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

@[cfg_block] def b_l100a20 : Block Op Label signature Reg.count 53 :=
  .terminate (.br ⟨.l100a20, RegMap.args (entryMap (live .l100a20)) 53⟩)

def bytes_l100a20 : List UInt8 :=
  [0xEB, 0xFE]

theorem code_l100a20 : ∀ x ∈ codeRange 0x100a20 bytes_l100a20, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xa20 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101dd0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101dd0 (pushR64Effect 0x101dd0 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[4, 14]
    (.letOp (n := 54) (.exec 0x101dd0 (PushPre 0x101dd0 2) (pushR64Effect 0x101dd0 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[4, 14]
    (.letOp (n := 55) (.out 0x101dd2 (pushR64Effect 0x101dd2 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[53, 3]
    (.letOp (n := 56) (.exec 0x101dd2 (PushPre 0x101dd2 1) (pushR64Effect 0x101dd2 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[53, 3]
    (.letOp (n := 57) (.out 0x101dd3 (subR64Imm32Effect 0x101dd3 4 0xe8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[55]
    (.letOp (n := 58) (.exec 0x101dd3 (fun s => s.RIP = 0x101dd3) (subR64Imm32Effect 0x101dd3 4 0xe8) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 59) (.out 0x101dda (movR64R64Effect 0x101dda 14 7) (EffectPart.reads (.reg (.gpr 14)) [.gpr 7] []) (.reg (.gpr 14))) #v[7]
    (.letOp (n := 60) (.exec 0x101dda (fun s => s.RIP = 0x101dda) (movR64R64Effect 0x101dda 14 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 61) (.out 0x101ddd (leaR64Effect 0x101ddd 7 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[57]
    (.letOp (n := 62) (.exec 0x101ddd (fun s => s.RIP = 0x101ddd) (leaR64Effect 0x101ddd 7 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[57]
    (.letOp (n := 63) (.out 0x101de5 (callEffect (fun _ => 0x106390) 0x101dea) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[57]
    (.letOp (n := 64) (.exec 0x101de5 (PushPre 0x101de5 5) (callEffect (fun _ => 0x106390) 0x101dea) (Reg.operands [.gpr 4] [])) #v[57]
    (.letOp (n := 65) (.const ⟨64, 0x101dea⟩) #v[]
    (.terminate (.call ⟨.l106390, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 59), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩ { target := .l101dea, kept := #v[], arity := rfl, guard := some (Fin.last 65) }))))))))))))))

def bytes_l101dd0 : List UInt8 :=
  [0x41, 0x56, 0x53, 0x48, 0x81, 0xEC, 0xE8, 0x00, 0x00, 0x00, 0x49, 0x89, 0xFE, 0x48, 0x8D, 0xBC,
    0x24, 0x88, 0x00, 0x00, 0x00, 0xE8, 0xA6, 0x45, 0x00, 0x00]

theorem code_l101dd0 : ∀ x ∈ codeRange 0x101dd0 bytes_l101dd0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1dd0 26 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101dea : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101dea (movR64M64Effect 0x101dea 3 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 54) (.exec 0x101dea (LoadPre 0x101dea (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x101dea + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x101dea 3 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x101df2 (cmpR64Imm8Effect 0x101df2 3 0x1) (EffectPart.reads (.flag .ZF) [.gpr 3] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x101df2 (fun s => s.RIP = 0x101df2) (cmpR64Imm8Effect 0x101df2 3 0x1) (Reg.operands [.gpr 3] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 4)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l101e62, RegMap.args [(1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l101df8, RegMap.args [(1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l101dea : List UInt8 :=
  [0x48, 0x8B, 0x9C, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x83, 0xFB, 0x01, 0x74, 0x6A]

theorem code_l101dea : ∀ x ∈ codeRange 0x101dea bytes_l101dea, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1dea 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101df8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101df8 (leaR64Effect 0x101df8 6 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 54) (.exec 0x101df8 (fun s => s.RIP = 0x101df8) (leaR64Effect 0x101df8 6 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x101e00 (leaR64Effect 0x101e00 7 (.sib 4 none 0 (.d8 0xf))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 56) (.exec 0x101e00 (fun s => s.RIP = 0x101e00) (leaR64Effect 0x101e00 7 (.sib 4 none 0 (.d8 0xf))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x101e05 (xorR32R32Effect 0x101e05 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[2, 2]
    (.letOp (n := 58) (.exec 0x101e05 (fun s => s.RIP = 0x101e05) (xorR32R32Effect 0x101e05 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 59) (.out 0x101e07 (callEffect (fun _ => 0x1215e0) 0x101e0c) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x101e07 (PushPre 0x101e07 5) (callEffect (fun _ => 0x1215e0) 0x101e0c) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x101e0c⟩) #v[]
    (.terminate (.call ⟨.l1215e0, RegMap.args [(2, 57), (3, 3), (4, 59), (5, 5), (6, 53), (7, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l101e0c, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l101df8 : List UInt8 :=
  [0x48, 0x8D, 0xB4, 0x24, 0x90, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x7C, 0x24, 0x0F, 0x31, 0xD2, 0xE8,
    0xD4, 0xF7, 0x01, 0x00]

theorem code_l101df8 : ∀ x ∈ codeRange 0x101df8 bytes_l101df8, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1df8 20 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101e0c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101e0c (movzxR32M8Effect 0x101e0c 5 1 (.sib 4 none 0 (.d8 0xf))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x101e0c (LoadPre 0x101e0c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x101e0c + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101e0c 5 1 (.sib 4 none 0 (.d8 0xf))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x101e11 (cmpR64Imm8Effect 0x101e11 1 0x6) (EffectPart.reads (.flag .CF) [.gpr 1] []) (.flag .CF)) #v[53]
    (.letOp (n := 56) (.exec 0x101e11 (fun s => s.RIP = 0x101e11) (cmpR64Imm8Effect 0x101e11 1 0x6) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 57) (.out 0x101e15 (atFlags (condHolds 2) (setccR8Effect 0x101e15 3 0)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 0))) #v[0, 55]
    (.letOp (n := 58) (.exec 0x101e15 (fun s => s.RIP = 0x101e15) (atFlags (condHolds 2) (setccR8Effect 0x101e15 3 0)) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[0, 55]
    (.letOp (n := 59) (.out 0x101e18 (movR8Imm8Effect 0x101e18 2 2 0x3d) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[2]
    (.letOp (n := 60) (.exec 0x101e18 (fun s => s.RIP = 0x101e18) (movR8Imm8Effect 0x101e18 2 2 0x3d) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 61) (.out 0x101e1a (shrR8ClEffect 0x101e1a 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[59, 53]
    (.letOp (n := 62) (.exec 0x101e1a (fun s => s.RIP = 0x101e1a) (shrR8ClEffect 0x101e1a 2 2) (Reg.operands [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[59, 53]
    (.letOp (n := 63) (.out 0x101e1c (testR8R8Effect 0x101e1c 2 0 2) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 2] []) (.flag .ZF)) #v[57, 61]
    (.letOp (n := 64) (.exec 0x101e1c (fun s => s.RIP = 0x101e1c) (testR8R8Effect 0x101e1c 2 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[57, 61]
    (.letOp (n := 65) (.pure (condOp 5)) #v[63]
    (.terminate (.condBr (Fin.last 65) ⟨.l101e4c, RegMap.args [(0, 57), (1, 53), (2, 61), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 63), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩ ⟨.l101e20, RegMap.args [(0, 57), (1, 53), (2, 61), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 63), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩))))))))))))))

def bytes_l101e0c : List UInt8 :=
  [0x0F, 0xB6, 0x4C, 0x24, 0x0F, 0x48, 0x83, 0xF9, 0x06, 0x0F, 0x92, 0xC0, 0xB2, 0x3D, 0xD2, 0xEA,
    0x84, 0xD0, 0x75, 0x2C]

theorem code_l101e0c : ∀ x ∈ codeRange 0x101e0c bytes_l101e0c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1e0c 20 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101e20 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x101e20 (StorePre 0x101e20 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x101e20 + BitVec.ofNat 64 8)) 4) (movM32Imm32Effect 0x101e20 8 (.sib 4 none 0 (.d8 0x50)) 0x3) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.out 0x101e28 (leaR64Effect 0x101e28 2 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 55) (.exec 0x101e28 (fun s => s.RIP = 0x101e28) (leaR64Effect 0x101e28 2 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x101e2d (movR32Imm32Effect 0x101e2d 5 6 0xb) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 57) (.exec 0x101e2d (fun s => s.RIP = 0x101e2d) (movR32Imm32Effect 0x101e2d 5 6 0xb) (Reg.operands [] [])) #v[]
    (.letOp (n := 58) (.out 0x101e32 (movR64Imm32Effect 0x101e32 7 0x202800) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 59) (.exec 0x101e32 (fun s => s.RIP = 0x101e32) (movR64Imm32Effect 0x101e32 7 0x202800) (Reg.operands [] [])) #v[]
    (.letOp (n := 60) (.out 0x101e39 (movR64Imm32Effect 0x101e39 1 0x2027e0) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 61) (.exec 0x101e39 (fun s => s.RIP = 0x101e39) (movR64Imm32Effect 0x101e39 1 0x2027e0) (Reg.operands [] [])) #v[]
    (.letOp (n := 62) (.out 0x101e40 (movR64Imm32Effect 0x101e40 8 0x202810) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 63) (.exec 0x101e40 (fun s => s.RIP = 0x101e40) (movR64Imm32Effect 0x101e40 8 0x202810) (Reg.operands [] [])) #v[]
    (.letOp (n := 64) (.out 0x101e47 (callEffect (fun _ => 0x1295a0) 0x101e4c) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 65) (.exec 0x101e47 (PushPre 0x101e47 5) (callEffect (fun _ => 0x1295a0) 0x101e4c) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.const ⟨64, 0x101e4c⟩) #v[]
    (.terminate (.call ⟨.l1295a0, RegMap.args [(1, 60), (2, 54), (4, 64), (5, 5), (6, 56), (7, 58), (8, 62)] 67⟩ { target := .l101e4c, kept := #v[], arity := rfl, guard := some (Fin.last 66) })))))))))))))))

def bytes_l101e20 : List UInt8 :=
  [0xC7, 0x44, 0x24, 0x50, 0x03, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x54, 0x24, 0x50, 0xBE, 0x0B, 0x00,
    0x00, 0x00, 0x48, 0xC7, 0xC7, 0x00, 0x28, 0x20, 0x00, 0x48, 0xC7, 0xC1, 0xE0, 0x27, 0x20, 0x00,
    0x49, 0xC7, 0xC0, 0x10, 0x28, 0x20, 0x00, 0xE8, 0x54, 0x77, 0x02, 0x00]

theorem code_l101e20 : ∀ x ∈ codeRange 0x101e20 bytes_l101e20, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1e20 44 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101e4c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101e4c (movR64M64Effect 0x101e4c 2 (.abs (some 1) 3 0x2022b8)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[1]
    (.letOp (n := 54) (.exec 0x101e4c (LoadPre 0x101e4c (fun s => AddrMode.addr (.abs (some 1) 3 0x2022b8) s (0x101e4c + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x101e4c 2 (.abs (some 1) 3 0x2022b8)) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 55) (.out 0x101e54 (leaR64Effect 0x101e54 6 (.sib 4 none 0 (.d8 0xf))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 56) (.exec 0x101e54 (fun s => s.RIP = 0x101e54) (leaR64Effect 0x101e54 6 (.sib 4 none 0 (.d8 0xf))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x101e59 (movR64R64Effect 0x101e59 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 58) (.exec 0x101e59 (fun s => s.RIP = 0x101e59) (movR64R64Effect 0x101e59 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 59) (.out 0x101e5c (callEffect (callMemPtr 0x101e5c (.rip 0x101f6e)) (0x101e5c + BitVec.ofNat 64 (callMemLen (.rip 0x101f6e)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x101e5c (GoesTo (CallMemPre 0x101e5c (.rip 0x101f6e)) (callEffect (callMemPtr 0x101e5c (.rip 0x101f6e)) (0x101e5c + BitVec.ofNat 64 (callMemLen (.rip 0x101f6e)))) 0x12a820) (callEffect (callMemPtr 0x101e5c (.rip 0x101f6e)) (0x101e5c + BitVec.ofNat 64 (callMemLen (.rip 0x101f6e)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x101e62⟩) #v[]
    (.terminate (.call ⟨.l12a820, RegMap.args [(1, 1), (2, 53), (3, 3), (4, 59), (5, 5), (6, 55), (7, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l101e62, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l101e4c : List UInt8 :=
  [0x48, 0x8B, 0x14, 0xCD, 0xB8, 0x22, 0x20, 0x00, 0x48, 0x8D, 0x74, 0x24, 0x0F, 0x4C, 0x89, 0xF7,
    0xFF, 0x15, 0x6E, 0x1F, 0x10, 0x00]

theorem code_l101e4c : ∀ x ∈ codeRange 0x101e4c bytes_l101e4c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1e4c 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101e62 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101e62 (movR32R32Effect 0x101e62 2 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 54) (.exec 0x101e62 (fun s => s.RIP = 0x101e62) (movR32R32Effect 0x101e62 2 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x101e64 (addR64Imm32Effect 0x101e64 4 0xe8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 56) (.exec 0x101e64 (fun s => s.RIP = 0x101e64) (addR64Imm32Effect 0x101e64 4 0xe8) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x101e6b (popR64Effect 0x101e6b 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[55]
    (.letOp (n := 58) (.out 0x101e6b (popR64Effect 0x101e6b 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[55]
    (.letOp (n := 59) (.exec 0x101e6b (PopPre 0x101e6b) (popR64Effect 0x101e6b 1 3) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 60) (.out 0x101e6c (popR64Effect 0x101e6c 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[58]
    (.letOp (n := 61) (.out 0x101e6c (popR64Effect 0x101e6c 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[58]
    (.letOp (n := 62) (.exec 0x101e6c (PopPre 0x101e6c) (popR64Effect 0x101e6c 2 14) (Reg.operands [.gpr 4] [])) #v[58]
    (.letOp (n := 63) (.out 0x101e6e (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[61]
    (.letOp (n := 64) (.out 0x101e6e (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 65) (.exec 0x101e6e (RetPre 0x101e6e) (retEffect) (Reg.operands [.gpr 4] [])) #v[61]
    (.terminate (.ret (RegMap.args [(0, 53), (1, 1), (2, 2), (3, 57), (4, 64), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 66) (some ⟨63, by decide⟩)))))))))))))))

def bytes_l101e62 : List UInt8 :=
  [0x89, 0xD8, 0x48, 0x81, 0xC4, 0xE8, 0x00, 0x00, 0x00, 0x5B, 0x41, 0x5E, 0xC3]

theorem code_l101e62 : ∀ x ∈ codeRange 0x101e62 bytes_l101e62, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1e62 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106390 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106390 (pushR64Effect 0x106390 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[4, 15]
    (.letOp (n := 54) (.exec 0x106390 (PushPre 0x106390 2) (pushR64Effect 0x106390 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[4, 15]
    (.letOp (n := 55) (.out 0x106392 (pushR64Effect 0x106392 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[53, 14]
    (.letOp (n := 56) (.exec 0x106392 (PushPre 0x106392 2) (pushR64Effect 0x106392 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 57) (.out 0x106394 (pushR64Effect 0x106394 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[55, 12]
    (.letOp (n := 58) (.exec 0x106394 (PushPre 0x106394 2) (pushR64Effect 0x106394 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[55, 12]
    (.letOp (n := 59) (.out 0x106396 (pushR64Effect 0x106396 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[57, 3]
    (.letOp (n := 60) (.exec 0x106396 (PushPre 0x106396 1) (pushR64Effect 0x106396 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[57, 3]
    (.letOp (n := 61) (.out 0x106397 (subR64Imm32Effect 0x106397 4 0x138) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 62) (.exec 0x106397 (fun s => s.RIP = 0x106397) (subR64Imm32Effect 0x106397 4 0x138) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 63) (.out 0x10639e (testR64R64Effect 0x10639e 2 2) (EffectPart.reads (.flag .ZF) [.gpr 2, .gpr 2] []) (.flag .ZF)) #v[2, 2]
    (.letOp (n := 64) (.exec 0x10639e (fun s => s.RIP = 0x10639e) (testR64R64Effect 0x10639e 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 65) (.pure (condOp 4)) #v[63]
    (.terminate (.condBr (Fin.last 65) ⟨.l106560, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 63), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩ ⟨.l1063a7, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 63), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩))))))))))))))

def bytes_l106390 : List UInt8 :=
  [0x41, 0x57, 0x41, 0x56, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0x38, 0x01, 0x00, 0x00, 0x48, 0x85,
    0xD2, 0x0F, 0x84, 0xB9, 0x01, 0x00, 0x00]

theorem code_l106390 : ∀ x ∈ codeRange 0x106390 bytes_l106390, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6390 23 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1063a7 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1063a7 (movzxR32M8Effect 0x1063a7 3 1 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[6]
    (.letOp (n := 54) (.exec 0x1063a7 (LoadPre 0x1063a7 (fun s => AddrMode.addr (.base 6 .none) s (0x1063a7 + BitVec.ofNat 64 3)) 1) (movzxR32M8Effect 0x1063a7 3 1 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 55) (.out 0x1063aa (cmpR64Imm8Effect 0x1063aa 1 0x6) (EffectPart.reads (.flag .CF) [.gpr 1] []) (.flag .CF)) #v[53]
    (.letOp (n := 56) (.exec 0x1063aa (fun s => s.RIP = 0x1063aa) (cmpR64Imm8Effect 0x1063aa 1 0x6) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 57) (.out 0x1063ae (atFlags (condHolds 2) (setccR8Effect 0x1063ae 3 0)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 0))) #v[0, 55]
    (.letOp (n := 58) (.exec 0x1063ae (fun s => s.RIP = 0x1063ae) (atFlags (condHolds 2) (setccR8Effect 0x1063ae 3 0)) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[0, 55]
    (.letOp (n := 59) (.out 0x1063b1 (movR8Imm8Effect 0x1063b1 3 8 0x3d) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[8]
    (.letOp (n := 60) (.exec 0x1063b1 (fun s => s.RIP = 0x1063b1) (movR8Imm8Effect 0x1063b1 3 8 0x3d) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 61) (.out 0x1063b4 (shrR8ClEffect 0x1063b4 3 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[59, 53]
    (.letOp (n := 62) (.exec 0x1063b4 (fun s => s.RIP = 0x1063b4) (shrR8ClEffect 0x1063b4 3 8) (Reg.operands [.gpr 8, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[59, 53]
    (.letOp (n := 63) (.out 0x1063b7 (andR8R8Effect 0x1063b7 3 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[61, 57]
    (.letOp (n := 64) (.exec 0x1063b7 (fun s => s.RIP = 0x1063b7) (andR8R8Effect 0x1063b7 3 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[61, 57]
    (.letOp (n := 65) (.out 0x1063ba (cmpR8Imm8Effect 0x1063ba 4 8 0x1) (EffectPart.reads (.flag .ZF) [.gpr 8] []) (.flag .ZF)) #v[63]
    (.letOp (n := 66) (.exec 0x1063ba (fun s => s.RIP = 0x1063ba) (cmpR8Imm8Effect 0x1063ba 4 8 0x1) (Reg.operands [.gpr 8] [])) #v[63]
    (.letOp (n := 67) (.pure (condOp 5)) #v[65]
    (.terminate (.condBr (Fin.last 67) ⟨.l106560, RegMap.args [(0, 57), (1, 53), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (19, 65), (22, 22), (39, 39), (50, 50), (51, 51)] 68⟩ ⟨.l1063c4, RegMap.args [(0, 57), (1, 53), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (19, 65), (22, 22), (39, 39), (50, 50), (51, 51)] 68⟩))))))))))))))))

def bytes_l1063a7 : List UInt8 :=
  [0x0F, 0xB6, 0x0E, 0x48, 0x83, 0xF9, 0x06, 0x0F, 0x92, 0xC0, 0x41, 0xB0, 0x3D, 0x41, 0xD2, 0xE8,
    0x41, 0x20, 0xC0, 0x41, 0x80, 0xF8, 0x01, 0x0F, 0x85, 0x9C, 0x01, 0x00, 0x00]

theorem code_l1063a7 : ∀ x ∈ codeRange 0x1063a7 bytes_l1063a7, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x63a7 29 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1063c4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1063c4 (cmpR64M64Effect 0x1063c4 2 (.abs (some 1) 3 0x202548)) (EffectPart.reads (.flag .ZF) [.gpr 2, .gpr 1] []) (.flag .ZF)) #v[2, 1]
    (.letOp (n := 54) (.exec 0x1063c4 (LoadPre 0x1063c4 (fun s => AddrMode.addr (.abs (some 1) 3 0x202548) s (0x1063c4 + BitVec.ofNat 64 8)) 8) (cmpR64M64Effect 0x1063c4 2 (.abs (some 1) 3 0x202548)) (Reg.operands [.gpr 2, .gpr 1] [])) #v[2, 1]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l106560, RegMap.args [(1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l1063d2, RegMap.args [(1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l1063c4 : List UInt8 :=
  [0x48, 0x3B, 0x14, 0xCD, 0x48, 0x25, 0x20, 0x00, 0x0F, 0x85, 0x8E, 0x01, 0x00, 0x00]

theorem code_l1063c4 : ∀ x ∈ codeRange 0x1063c4 bytes_l1063c4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x63c4 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1063d2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1063d2 (movR64R64Effect 0x1063d2 15 7) (EffectPart.reads (.reg (.gpr 15)) [.gpr 7] []) (.reg (.gpr 15))) #v[7]
    (.letOp (n := 54) (.exec 0x1063d2 (fun s => s.RIP = 0x1063d2) (movR64R64Effect 0x1063d2 15 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 55) (.out 0x1063d5 (movR32Imm32Effect 0x1063d5 5 1 0x41) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 56) (.exec 0x1063d5 (fun s => s.RIP = 0x1063d5) (movR32Imm32Effect 0x1063d5 5 1 0x41) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x1063da (subR64R64Effect 0x1063da 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[55, 2]
    (.letOp (n := 58) (.exec 0x1063da (fun s => s.RIP = 0x1063da) (subR64R64Effect 0x1063da 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[55, 2]
    (.letOp (n := 59) (.out 0x1063dd (xorR32R32Effect 0x1063dd 3 12 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 12] []) (.reg (.gpr 12))) #v[12, 12]
    (.letOp (n := 60) (.exec 0x1063dd (fun s => s.RIP = 0x1063dd) (xorR32R32Effect 0x1063dd 3 12 12) (Reg.operands [.gpr 12, .gpr 12] [])) #v[12, 12]
    (.letOp (n := 61) (.out 0x1063e0 (cmpR64Imm8Effect 0x1063e0 2 0x41) (EffectPart.reads (.flag .CF) [.gpr 2] []) (.flag .CF)) #v[2]
    (.letOp (n := 62) (.exec 0x1063e0 (fun s => s.RIP = 0x1063e0) (cmpR64Imm8Effect 0x1063e0 2 0x41) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 63) (.out 0x1063e4 (movR32Imm32Effect 0x1063e4 5 0 0x0) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 64) (.exec 0x1063e4 (fun s => s.RIP = 0x1063e4) (movR32Imm32Effect 0x1063e4 5 0 0x0) (Reg.operands [] [])) #v[]
    (.letOp (n := 65) (.out 0x1063e9 (atFlags (condHolds 2) (cmovR64R64Effect 0x1063e9 4 0 1)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 0))) #v[63, 57, 61]
    (.letOp (n := 66) (.exec 0x1063e9 (fun s => s.RIP = 0x1063e9) (atFlags (condHolds 2) (cmovR64R64Effect 0x1063e9 4 0 1)) (Reg.operands [.gpr 0, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[63, 57, 61]
    (.letOp (n := 67) (.out 0x1063ed (leaR64Effect 0x1063ed 7 (.sib 4 (some 2) 0 .none)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4, .gpr 2] []) (.reg (.gpr 7))) #v[4, 2]
    (.letOp (n := 68) (.exec 0x1063ed (fun s => s.RIP = 0x1063ed) (leaR64Effect 0x1063ed 7 (.sib 4 (some 2) 0 .none)) (Reg.operands [.gpr 4, .gpr 2] [])) #v[4, 2]
    (.letOp (n := 69) (.out 0x1063f1 (addR64Imm32Effect 0x1063f1 7 0xa0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[67]
    (.letOp (n := 70) (.exec 0x1063f1 (fun s => s.RIP = 0x1063f1) (addR64Imm32Effect 0x1063f1 7 0xa0) (Reg.operands [.gpr 7] [])) #v[67]
    (.letOp (n := 71) (.out 0x1063f8 (movR64R64Effect 0x1063f8 3 6) (EffectPart.reads (.reg (.gpr 3)) [.gpr 6] []) (.reg (.gpr 3))) #v[6]
    (.letOp (n := 72) (.exec 0x1063f8 (fun s => s.RIP = 0x1063f8) (movR64R64Effect 0x1063f8 3 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 73) (.out 0x1063fb (xorR32R32Effect 0x1063fb 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[6, 6]
    (.letOp (n := 74) (.exec 0x1063fb (fun s => s.RIP = 0x1063fb) (xorR32R32Effect 0x1063fb 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 75) (.out 0x1063fd (movR64R64Effect 0x1063fd 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[2]
    (.letOp (n := 76) (.exec 0x1063fd (fun s => s.RIP = 0x1063fd) (movR64R64Effect 0x1063fd 14 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 77) (.out 0x106400 (movR64R64Effect 0x106400 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0] []) (.reg (.gpr 2))) #v[65]
    (.letOp (n := 78) (.exec 0x106400 (fun s => s.RIP = 0x106400) (movR64R64Effect 0x106400 2 0) (Reg.operands [.gpr 0] [])) #v[65]
    (.letOp (n := 79) (.out 0x106403 (callEffect (callMemPtr 0x106403 (.rip 0xfda07)) (0x106403 + BitVec.ofNat 64 (callMemLen (.rip 0xfda07)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 80) (.exec 0x106403 (GoesTo (CallMemPre 0x106403 (.rip 0xfda07)) (callEffect (callMemPtr 0x106403 (.rip 0xfda07)) (0x106403 + BitVec.ofNat 64 (callMemLen (.rip 0xfda07)))) 0x12a700) (callEffect (callMemPtr 0x106403 (.rip 0xfda07)) (0x106403 + BitVec.ofNat 64 (callMemLen (.rip 0xfda07)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 81) (.const ⟨64, 0x106409⟩) #v[]
    (.terminate (.call ⟨.l12a700, RegMap.args [(0, 65), (1, 57), (2, 77), (3, 71), (4, 79), (5, 5), (6, 73), (7, 69), (9, 9), (10, 10), (11, 11), (12, 59), (13, 13), (14, 75), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 82⟩ { target := .l106409, kept := #v[], arity := rfl, guard := some (Fin.last 81) }))))))))))))))))))))))))))))))

def bytes_l1063d2 : List UInt8 :=
  [0x49, 0x89, 0xFF, 0xB9, 0x41, 0x00, 0x00, 0x00, 0x48, 0x29, 0xD1, 0x45, 0x31, 0xE4, 0x48, 0x83,
    0xFA, 0x41, 0xB8, 0x00, 0x00, 0x00, 0x00, 0x48, 0x0F, 0x42, 0xC1, 0x48, 0x8D, 0x3C, 0x14, 0x48,
    0x81, 0xC7, 0xA0, 0x00, 0x00, 0x00, 0x48, 0x89, 0xF3, 0x31, 0xF6, 0x49, 0x89, 0xD6, 0x48, 0x89,
    0xC2, 0xFF, 0x15, 0x07, 0xDA, 0x0F, 0x00]

theorem code_l1063d2 : ∀ x ∈ codeRange 0x1063d2 bytes_l1063d2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x63d2 55 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106409 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106409 (leaR64Effect 0x106409 7 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x106409 (fun s => s.RIP = 0x106409) (leaR64Effect 0x106409 7 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x106411 (movR64R64Effect 0x106411 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[3]
    (.letOp (n := 56) (.exec 0x106411 (fun s => s.RIP = 0x106411) (movR64R64Effect 0x106411 6 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 57) (.out 0x106414 (movR64R64Effect 0x106414 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14] []) (.reg (.gpr 2))) #v[14]
    (.letOp (n := 58) (.exec 0x106414 (fun s => s.RIP = 0x106414) (movR64R64Effect 0x106414 2 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 59) (.out 0x106417 (callEffect (callMemPtr 0x106417 (.rip 0xfd9b3)) (0x106417 + BitVec.ofNat 64 (callMemLen (.rip 0xfd9b3)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x106417 (GoesTo (CallMemPre 0x106417 (.rip 0xfd9b3)) (callEffect (callMemPtr 0x106417 (.rip 0xfd9b3)) (0x106417 + BitVec.ofNat 64 (callMemLen (.rip 0xfd9b3)))) 0x12a820) (callEffect (callMemPtr 0x106417 (.rip 0xfd9b3)) (0x106417 + BitVec.ofNat 64 (callMemLen (.rip 0xfd9b3)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x10641d⟩) #v[]
    (.terminate (.call ⟨.l12a820, RegMap.args [(2, 57), (3, 3), (4, 59), (5, 5), (6, 55), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l10641d, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l106409 : List UInt8 :=
  [0x48, 0x8D, 0xBC, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x48, 0x89, 0xDE, 0x4C, 0x89, 0xF2, 0xFF, 0x15,
    0xB3, 0xD9, 0x0F, 0x00]

theorem code_l106409 : ∀ x ∈ codeRange 0x106409 bytes_l106409, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6409 20 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10641d_1 : Block Op Label signature Reg.count 83 :=
  .letOp (n := 83) (.out 0x106499 (movR64M64Effect 0x106499 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 84) (.exec 0x106499 (LoadPre 0x106499 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x106499 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106499 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 85) (.out 0x10649e (movR64M64Effect 0x10649e 1 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 86) (.exec 0x10649e (LoadPre 0x10649e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10649e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10649e 1 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 87) (.exec 0x1064a3 (StorePre 0x1064a3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x1064a3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1064a3 0 (.sib 4 none 0 (.d8 0xf))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[83, 4]
    (.letOp (n := 88) (.exec 0x1064a8 (StorePre 0x1064a8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x17)) s (0x1064a8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1064a8 1 (.sib 4 none 0 (.d8 0x17))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[85, 4]
    (.letOp (n := 89) (.out 0x1064ad (movR64M64Effect 0x1064ad 0 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 90) (.exec 0x1064ad (LoadPre 0x1064ad (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1064ad + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1064ad 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 91) (.exec 0x1064b2 (StorePre 0x1064b2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1f)) s (0x1064b2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1064b2 0 (.sib 4 none 0 (.d8 0x1f))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[89, 4]
    (.letOp (n := 92) (.out 0x1064b7 (movR64M64Effect 0x1064b7 0 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 93) (.exec 0x1064b7 (LoadPre 0x1064b7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1064b7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1064b7 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 94) (.exec 0x1064bc (StorePre 0x1064bc 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x27)) s (0x1064bc + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1064bc 0 (.sib 4 none 0 (.d8 0x27))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[92, 4]
    (.letOp (n := 95) (.out 0x1064c1 (movR64M64Effect 0x1064c1 0 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 96) (.exec 0x1064c1 (LoadPre 0x1064c1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x1064c1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1064c1 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 97) (.exec 0x1064c6 (StorePre 0x1064c6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2f)) s (0x1064c6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1064c6 0 (.sib 4 none 0 (.d8 0x2f))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[95, 4]
    (.letOp (n := 98) (.out 0x1064cb (movR64M64Effect 0x1064cb 0 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 99) (.exec 0x1064cb (LoadPre 0x1064cb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x1064cb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1064cb 0 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 100) (.exec 0x1064d0 (StorePre 0x1064d0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x37)) s (0x1064d0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1064d0 0 (.sib 4 none 0 (.d8 0x37))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[98, 4]
    (.letOp (n := 101) (.out 0x1064d5 (movR64M64Effect 0x1064d5 0 (.sib 4 none 0 (.d8 0x76))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 102) (.exec 0x1064d5 (LoadPre 0x1064d5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x76)) s (0x1064d5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1064d5 0 (.sib 4 none 0 (.d8 0x76))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 103) (.exec 0x1064da (StorePre 0x1064da 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3d)) s (0x1064da + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1064da 0 (.sib 4 none 0 (.d8 0x3d))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[101, 4]
    (.letOp (n := 104) (.out 0x1064df (leaR64Effect 0x1064df 3 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 105) (.exec 0x1064df (fun s => s.RIP = 0x1064df) (leaR64Effect 0x1064df 3 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 106) (.out 0x1064e7 (leaR64Effect 0x1064e7 6 (.sib 4 none 0 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 107) (.exec 0x1064e7 (fun s => s.RIP = 0x1064e7) (leaR64Effect 0x1064e7 6 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 108) (.out 0x1064ec (movR64R64Effect 0x1064ec 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[104]
    (.letOp (n := 109) (.exec 0x1064ec (fun s => s.RIP = 0x1064ec) (movR64R64Effect 0x1064ec 7 3) (Reg.operands [.gpr 3] [])) #v[104]
    (.letOp (n := 110) (.out 0x1064ef (callEffect (fun _ => 0x121480) 0x1064f4) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 111) (.exec 0x1064ef (PushPre 0x1064ef 5) (callEffect (fun _ => 0x121480) 0x1064f4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 112) (.const ⟨64, 0x1064f4⟩) #v[]
    (.terminate (.call ⟨.l121480, RegMap.args [(0, 101), (1, 85), (3, 104), (4, 110), (5, 5), (6, 106), (7, 108), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 113⟩ { target := .l1064f4, kept := #v[], arity := rfl, guard := some (Fin.last 112) })))))))))))))))))))))))))))))))

def bytes_l10641d_1 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x8B, 0x4C, 0x24, 0x50, 0x48, 0x89, 0x44, 0x24, 0x0F, 0x48,
    0x89, 0x4C, 0x24, 0x17, 0x48, 0x8B, 0x44, 0x24, 0x58, 0x48, 0x89, 0x44, 0x24, 0x1F, 0x48, 0x8B,
    0x44, 0x24, 0x60, 0x48, 0x89, 0x44, 0x24, 0x27, 0x48, 0x8B, 0x44, 0x24, 0x68, 0x48, 0x89, 0x44,
    0x24, 0x2F, 0x48, 0x8B, 0x44, 0x24, 0x70, 0x48, 0x89, 0x44, 0x24, 0x37, 0x48, 0x8B, 0x44, 0x24,
    0x76, 0x48, 0x89, 0x44, 0x24, 0x3D, 0x48, 0x8D, 0x9C, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x48, 0x8D,
    0x74, 0x24, 0x04, 0x48, 0x89, 0xDF, 0xE8, 0x8C, 0xAF, 0x01, 0x00]

theorem code_l10641d_1 : ∀ x ∈ codeRange 0x106499 bytes_l10641d_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6499 91 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10641d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10641d (movR32M32LowEffect 0x10641d 0 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x10641d (LoadPre 0x10641d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x10641d + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x10641d 0 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x106424 (movR32M32LowEffect 0x106424 1 (.sib 4 none 0 (.d32 0xa3))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x106424 (LoadPre 0x106424 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa3)) s (0x106424 + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x106424 1 (.sib 4 none 0 (.d32 0xa3))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x10642b (StorePre 0x10642b 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x10642b + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x10642b 0 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 58) (.exec 0x10642f (StorePre 0x10642f 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x10642f + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x10642f 1 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 59) (.out 0x106433 (movR32M32LowEffect 0x106433 0 (.sib 4 none 0 (.d32 0xa7))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x106433 (LoadPre 0x106433 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa7)) s (0x106433 + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x106433 0 (.sib 4 none 0 (.d32 0xa7))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x10643a (movR64M64Effect 0x10643a 1 (.sib 4 none 0 (.d32 0xab))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 62) (.exec 0x10643a (LoadPre 0x10643a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xab)) s (0x10643a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10643a 1 (.sib 4 none 0 (.d32 0xab))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x106442 (StorePre 0x106442 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x106442 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x106442 1 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.out 0x106447 (movR64M64Effect 0x106447 1 (.sib 4 none 0 (.d32 0xb3))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x106447 (LoadPre 0x106447 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb3)) s (0x106447 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x106447 1 (.sib 4 none 0 (.d32 0xb3))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x10644f (StorePre 0x10644f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10644f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10644f 1 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.out 0x106454 (movR64M64Effect 0x106454 1 (.sib 4 none 0 (.d32 0xbb))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 68) (.exec 0x106454 (LoadPre 0x106454 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xbb)) s (0x106454 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x106454 1 (.sib 4 none 0 (.d32 0xbb))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.exec 0x10645c (StorePre 0x10645c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10645c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10645c 1 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[67, 4]
    (.letOp (n := 70) (.out 0x106461 (movR64M64Effect 0x106461 1 (.sib 4 none 0 (.d32 0xc3))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 71) (.exec 0x106461 (LoadPre 0x106461 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc3)) s (0x106461 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x106461 1 (.sib 4 none 0 (.d32 0xc3))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.exec 0x106469 (StorePre 0x106469 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x106469 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x106469 1 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[70, 4]
    (.letOp (n := 73) (.out 0x10646e (movR64M64Effect 0x10646e 1 (.sib 4 none 0 (.d32 0xcb))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 74) (.exec 0x10646e (LoadPre 0x10646e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xcb)) s (0x10646e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10646e 1 (.sib 4 none 0 (.d32 0xcb))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.exec 0x106476 (StorePre 0x106476 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x106476 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x106476 1 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[73, 4]
    (.letOp (n := 76) (.out 0x10647b (movR64M64Effect 0x10647b 1 (.sib 4 none 0 (.d32 0xd3))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 77) (.exec 0x10647b (LoadPre 0x10647b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd3)) s (0x10647b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10647b 1 (.sib 4 none 0 (.d32 0xd3))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 78) (.exec 0x106483 (StorePre 0x106483 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x106483 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x106483 1 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[76, 4]
    (.letOp (n := 79) (.out 0x106488 (movR64M64Effect 0x106488 1 (.sib 4 none 0 (.d32 0xd9))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 80) (.exec 0x106488 (LoadPre 0x106488 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd9)) s (0x106488 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x106488 1 (.sib 4 none 0 (.d32 0xd9))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 81) (.exec 0x106490 (StorePre 0x106490 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x76)) s (0x106490 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x106490 1 (.sib 4 none 0 (.d8 0x76))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[79, 4]
    (.letOp (n := 82) (.exec 0x106495 (StorePre 0x106495 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xb)) s (0x106495 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x106495 0 (.sib 4 none 0 (.d8 0xb))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (b_l10641d_1))))))))))))))))))))))))))))))

def bytes_l10641d : List UInt8 :=
  [0x8B, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x8B, 0x8C, 0x24, 0xA3, 0x00, 0x00, 0x00, 0x89, 0x44,
    0x24, 0x04, 0x89, 0x4C, 0x24, 0x07, 0x8B, 0x84, 0x24, 0xA7, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x8C,
    0x24, 0xAB, 0x00, 0x00, 0x00, 0x48, 0x89, 0x4C, 0x24, 0x48, 0x48, 0x8B, 0x8C, 0x24, 0xB3, 0x00,
    0x00, 0x00, 0x48, 0x89, 0x4C, 0x24, 0x50, 0x48, 0x8B, 0x8C, 0x24, 0xBB, 0x00, 0x00, 0x00, 0x48,
    0x89, 0x4C, 0x24, 0x58, 0x48, 0x8B, 0x8C, 0x24, 0xC3, 0x00, 0x00, 0x00, 0x48, 0x89, 0x4C, 0x24,
    0x60, 0x48, 0x8B, 0x8C, 0x24, 0xCB, 0x00, 0x00, 0x00, 0x48, 0x89, 0x4C, 0x24, 0x68, 0x48, 0x8B,
    0x8C, 0x24, 0xD3, 0x00, 0x00, 0x00, 0x48, 0x89, 0x4C, 0x24, 0x70, 0x48, 0x8B, 0x8C, 0x24, 0xD9,
    0x00, 0x00, 0x00, 0x48, 0x89, 0x4C, 0x24, 0x76, 0x89, 0x44, 0x24, 0x0B] ++ bytes_l10641d_1

theorem code_l10641d : ∀ x ∈ codeRange 0x10641d bytes_l10641d, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x641d 124 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10641d_1

@[cfg_block] def b_l1064f4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1064f4 (leaR64Effect 0x1064f4 7 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x1064f4 (fun s => s.RIP = 0x1064f4) (leaR64Effect 0x1064f4 7 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1064f9 (movR32Imm32Effect 0x1064f9 5 1 0xb) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 56) (.exec 0x1064f9 (fun s => s.RIP = 0x1064f9) (movR32Imm32Effect 0x1064f9 5 1 0xb) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x1064fe (movR64R64Effect 0x1064fe 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[3]
    (.letOp (n := 58) (.exec 0x1064fe (fun s => s.RIP = 0x1064fe) (movR64R64Effect 0x1064fe 6 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 59) (.out 0x106501 (repMovsqEffect 0x106501) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 6))) #v[57, 53, 55, 22]
    (.letOp (n := 60) (.exec 0x106501 (RepPre 0x106501 (RepMovsqPre 0x106501)) (repMovsqEffect 0x106501) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[57, 53, 55, 22]
    (.letOp (n := 61) (.out 0x106504 (movzxR32M8Effect 0x106504 5 0 (.sib 4 none 0 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 62) (.exec 0x106504 (LoadPre 0x106504 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x106504 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x106504 5 0 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x106509 (movzxR32R8Effect 0x106509 3 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[61]
    (.letOp (n := 64) (.exec 0x106509 (fun s => s.RIP = 0x106509) (movzxR32R8Effect 0x106509 3 1 0) (Reg.operands [.gpr 0] [])) #v[61]
    (.letOp (n := 65) (.out 0x10650c (leaR32Effect 0x10650c 3 2 (.base 1 (.d8 0xfe))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[63]
    (.letOp (n := 66) (.exec 0x10650c (fun s => s.RIP = 0x10650c) (leaR32Effect 0x10650c 3 2 (.base 1 (.d8 0xfe))) (Reg.operands [.gpr 1] [])) #v[63]
    (.letOp (n := 67) (.out 0x10650f (cmpR32Imm8Effect 0x10650f 3 2 0x4) (EffectPart.reads (.flag .CF) [.gpr 2] []) (.flag .CF)) #v[65]
    (.letOp (n := 68) (.exec 0x10650f (fun s => s.RIP = 0x10650f) (cmpR32Imm8Effect 0x10650f 3 2 0x4) (Reg.operands [.gpr 2] [])) #v[65]
    (.letOp (n := 69) (.pure (condOp 2)) #v[67]
    (.terminate (.condBr (Fin.last 69) ⟨.l106518, RegMap.args [(0, 61), (1, 63), (2, 65), (3, 3), (4, 4), (5, 5), (6, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (16, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 70⟩ ⟨.l106514, RegMap.args [(0, 61), (1, 63), (2, 65), (3, 3), (4, 4), (5, 5), (6, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (16, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 70⟩))))))))))))))))))

def bytes_l1064f4 : List UInt8 :=
  [0x48, 0x8D, 0x7C, 0x24, 0x48, 0xB9, 0x0B, 0x00, 0x00, 0x00, 0x48, 0x89, 0xDE, 0xF3, 0x48, 0xA5,
    0x0F, 0xB6, 0x44, 0x24, 0x04, 0x0F, 0xB6, 0xC8, 0x8D, 0x51, 0xFE, 0x83, 0xFA, 0x04, 0x72, 0x04]

theorem code_l1064f4 : ∀ x ∈ codeRange 0x1064f4 bytes_l1064f4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x64f4 32 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106514 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106514 (testR32R32Effect 0x106514 2 1 1) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 1] []) (.flag .ZF)) #v[1, 1]
    (.letOp (n := 54) (.exec 0x106514 (fun s => s.RIP = 0x106514) (testR32R32Effect 0x106514 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[1, 1]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l10657a, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l106518, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l106514 : List UInt8 :=
  [0x85, 0xC9, 0x75, 0x62]

theorem code_l106514 : ∀ x ∈ codeRange 0x106514 bytes_l106514, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6514 4 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106518 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106518 (movzxR32M8Effect 0x106518 8 1 (.sib 4 none 0 (.d32 0xf8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x106518 (LoadPre 0x106518 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x106518 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x106518 8 1 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x106520 (andR8Imm8Effect 0x106520 3 1 0x1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 56) (.exec 0x106520 (fun s => s.RIP = 0x106520) (andR8Imm8Effect 0x106520 3 1 0x1) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 57) (.out 0x106523 (testR8R8Effect 0x106523 2 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[0, 0]
    (.letOp (n := 58) (.exec 0x106523 (fun s => s.RIP = 0x106523) (testR8R8Effect 0x106523 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.letOp (n := 59) (.out 0x106525 (movzxR32R8Effect 0x106525 3 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[55]
    (.letOp (n := 60) (.exec 0x106525 (fun s => s.RIP = 0x106525) (movzxR32R8Effect 0x106525 3 0 1) (Reg.operands [.gpr 1] [])) #v[55]
    (.letOp (n := 61) (.out 0x106528 (atFlags (condHolds 4) (cmovR32R32Effect 0x106528 4 0 12)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 0))) #v[59, 12, 57]
    (.letOp (n := 62) (.exec 0x106528 (fun s => s.RIP = 0x106528) (atFlags (condHolds 4) (cmovR32R32Effect 0x106528 4 0 12)) (Reg.operands [.gpr 0, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[59, 12, 57]
    (.letOp (n := 63) (.exec 0x10652c (StorePre 0x10652c 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x10652c + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x10652c 7 0 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.out 0x106533 (leaR64Effect 0x106533 0 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 65) (.exec 0x106533 (fun s => s.RIP = 0x106533) (leaR64Effect 0x106533 0 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.out 0x10653b (cmpM8Imm8Effect 0x10653b 8 (.sib 4 none 0 (.d32 0xa0)) 0x0) (EffectPart.reads (.flag .ZF) [.gpr 4] []) (.flag .ZF)) #v[4]
    (.letOp (n := 67) (.exec 0x10653b (LoadPre 0x10653b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x10653b + BitVec.ofNat 64 8)) 1) (cmpM8Imm8Effect 0x10653b 8 (.sib 4 none 0 (.d32 0xa0)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.out 0x106543 (movR64R64Effect 0x106543 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[15]
    (.letOp (n := 69) (.exec 0x106543 (fun s => s.RIP = 0x106543) (movR64R64Effect 0x106543 7 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 70) (.pure (condOp 4)) #v[66]
    (.terminate (.condBr (Fin.last 70) ⟨.l106560, RegMap.args [(0, 64), (1, 55), (2, 2), (4, 4), (5, 5), (6, 6), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 66), (22, 22), (39, 39), (50, 50), (51, 51)] 71⟩ ⟨.l106548, RegMap.args [(0, 64), (1, 55), (2, 2), (4, 4), (5, 5), (6, 6), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 66), (22, 22), (39, 39), (50, 50), (51, 51)] 71⟩)))))))))))))))))))

def bytes_l106518 : List UInt8 :=
  [0x0F, 0xB6, 0x8C, 0x24, 0xF8, 0x00, 0x00, 0x00, 0x80, 0xE1, 0x01, 0x84, 0xC0, 0x0F, 0xB6, 0xC1,
    0x41, 0x0F, 0x44, 0xC4, 0x88, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x84, 0x24, 0xA0,
    0x00, 0x00, 0x00, 0x80, 0xBC, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xFF, 0x74, 0x18]

theorem code_l106518 : ∀ x ∈ codeRange 0x106518 bytes_l106518, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6518 48 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106548 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106548 (addR64Imm8Effect 0x106548 7 0x8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[7]
    (.letOp (n := 54) (.exec 0x106548 (fun s => s.RIP = 0x106548) (addR64Imm8Effect 0x106548 7 0x8) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 55) (.out 0x10654c (leaR64Effect 0x10654c 6 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 56) (.exec 0x10654c (fun s => s.RIP = 0x10654c) (leaR64Effect 0x10654c 6 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x106551 (movR32Imm32Effect 0x106551 5 1 0xb) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 58) (.exec 0x106551 (fun s => s.RIP = 0x106551) (movR32Imm32Effect 0x106551 5 1 0xb) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x106556 (repMovsqEffect 0x106556) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 6))) #v[55, 53, 57, 22]
    (.letOp (n := 60) (.out 0x106556 (repMovsqEffect 0x106556) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 1))) #v[55, 53, 57, 22]
    (.letOp (n := 61) (.exec 0x106556 (RepPre 0x106556 (RepMovsqPre 0x106556)) (repMovsqEffect 0x106556) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[55, 53, 57, 22]
    (.letOp (n := 62) (.out 0x106559 (movR64R64Effect 0x106559 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[15]
    (.letOp (n := 63) (.exec 0x106559 (fun s => s.RIP = 0x106559) (movR64R64Effect 0x106559 7 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 64) (.out 0x10655c (xorR32R32Effect 0x10655c 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[0, 0]
    (.letOp (n := 65) (.exec 0x10655c (fun s => s.RIP = 0x10655c) (xorR32R32Effect 0x10655c 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.terminate (.br ⟨.l106565, RegMap.args [(0, 64), (1, 60), (2, 2), (4, 4), (5, 5), (6, 59), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩))))))))))))))

def bytes_l106548 : List UInt8 :=
  [0x48, 0x83, 0xC7, 0x08, 0x48, 0x8D, 0x74, 0x24, 0x48, 0xB9, 0x0B, 0x00, 0x00, 0x00, 0xF3, 0x48,
    0xA5, 0x4C, 0x89, 0xFF, 0x31, 0xC0, 0xEB, 0x05]

theorem code_l106548 : ∀ x ∈ codeRange 0x106548 bytes_l106548, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6548 24 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106560 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106560 (movR32Imm32Effect 0x106560 5 0 0x1) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 54) (.exec 0x106560 (fun s => s.RIP = 0x106560) (movR32Imm32Effect 0x106560 5 0 0x1) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l106565, RegMap.args [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l106560 : List UInt8 :=
  [0xB8, 0x01, 0x00, 0x00, 0x00]

theorem code_l106560 : ∀ x ∈ codeRange 0x106560 bytes_l106560, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6560 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106565 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x106565 (StorePre 0x106565 3 (fun s => AddrMode.addr (.base 7 .none) s (0x106565 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x106565 0 (.base 7 .none)) (Reg.operands [.gpr 0, .gpr 7] [])) #v[0, 7]
    (.letOp (n := 54) (.out 0x106568 (movR64R64Effect 0x106568 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 55) (.exec 0x106568 (fun s => s.RIP = 0x106568) (movR64R64Effect 0x106568 0 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 56) (.out 0x10656b (addR64Imm32Effect 0x10656b 4 0x138) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 57) (.exec 0x10656b (fun s => s.RIP = 0x10656b) (addR64Imm32Effect 0x10656b 4 0x138) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.out 0x106572 (popR64Effect 0x106572 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[56]
    (.letOp (n := 59) (.out 0x106572 (popR64Effect 0x106572 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[56]
    (.letOp (n := 60) (.exec 0x106572 (PopPre 0x106572) (popR64Effect 0x106572 1 3) (Reg.operands [.gpr 4] [])) #v[56]
    (.letOp (n := 61) (.out 0x106573 (popR64Effect 0x106573 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[59]
    (.letOp (n := 62) (.out 0x106573 (popR64Effect 0x106573 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 63) (.exec 0x106573 (PopPre 0x106573) (popR64Effect 0x106573 2 12) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 64) (.out 0x106575 (popR64Effect 0x106575 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[62]
    (.letOp (n := 65) (.out 0x106575 (popR64Effect 0x106575 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[62]
    (.letOp (n := 66) (.exec 0x106575 (PopPre 0x106575) (popR64Effect 0x106575 2 14) (Reg.operands [.gpr 4] [])) #v[62]
    (.letOp (n := 67) (.out 0x106577 (popR64Effect 0x106577 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[65]
    (.letOp (n := 68) (.out 0x106577 (popR64Effect 0x106577 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 69) (.exec 0x106577 (PopPre 0x106577) (popR64Effect 0x106577 2 15) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 70) (.out 0x106579 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[68]
    (.letOp (n := 71) (.out 0x106579 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[68]
    (.letOp (n := 72) (.exec 0x106579 (RetPre 0x106579) (retEffect) (Reg.operands [.gpr 4] [])) #v[68]
    (.terminate (.ret (RegMap.args [(0, 54), (1, 1), (2, 2), (3, 58), (4, 71), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 13), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 73) (some ⟨70, by decide⟩))))))))))))))))))))))

def bytes_l106565 : List UInt8 :=
  [0x48, 0x89, 0x07, 0x48, 0x89, 0xF8, 0x48, 0x81, 0xC4, 0x38, 0x01, 0x00, 0x00, 0x5B, 0x41, 0x5C,
    0x41, 0x5E, 0x41, 0x5F, 0xC3]

theorem code_l106565 : ∀ x ∈ codeRange 0x106565 bytes_l106565, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6565 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10657a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x10657a (StorePre 0x10657a 11 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x10657a + BitVec.ofNat 64 11)) 4) (movM32Imm32Effect 0x10657a 11 (.sib 4 none 0 (.d32 0x100)) 0x3) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.out 0x106585 (leaR64Effect 0x106585 2 (.sib 4 none 0 (.d32 0x100))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 55) (.exec 0x106585 (fun s => s.RIP = 0x106585) (leaR64Effect 0x106585 2 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x10658d (movR32Imm32Effect 0x10658d 5 6 0xb) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 57) (.exec 0x10658d (fun s => s.RIP = 0x10658d) (movR32Imm32Effect 0x10658d 5 6 0xb) (Reg.operands [] [])) #v[]
    (.letOp (n := 58) (.out 0x106592 (movR64Imm32Effect 0x106592 7 0x202800) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 59) (.exec 0x106592 (fun s => s.RIP = 0x106592) (movR64Imm32Effect 0x106592 7 0x202800) (Reg.operands [] [])) #v[]
    (.letOp (n := 60) (.out 0x106599 (movR64Imm32Effect 0x106599 1 0x2027e0) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 61) (.exec 0x106599 (fun s => s.RIP = 0x106599) (movR64Imm32Effect 0x106599 1 0x2027e0) (Reg.operands [] [])) #v[]
    (.letOp (n := 62) (.out 0x1065a0 (movR64Imm32Effect 0x1065a0 8 0x202810) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 63) (.exec 0x1065a0 (fun s => s.RIP = 0x1065a0) (movR64Imm32Effect 0x1065a0 8 0x202810) (Reg.operands [] [])) #v[]
    (.letOp (n := 64) (.out 0x1065a7 (callEffect (fun _ => 0x1295a0) 0x1065ac) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 65) (.exec 0x1065a7 (PushPre 0x1065a7 5) (callEffect (fun _ => 0x1295a0) 0x1065ac) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.const ⟨64, 0x1065ac⟩) #v[]
    (.terminate (.call ⟨.l1295a0, RegMap.args [(1, 60), (2, 54), (4, 64), (5, 5), (6, 56), (7, 58), (8, 62)] 67⟩ { target := .l1065ac, kept := #v[], arity := rfl, guard := some (Fin.last 66) })))))))))))))))

def bytes_l10657a : List UInt8 :=
  [0xC7, 0x84, 0x24, 0x00, 0x01, 0x00, 0x00, 0x03, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x94, 0x24, 0x00,
    0x01, 0x00, 0x00, 0xBE, 0x0B, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC7, 0x00, 0x28, 0x20, 0x00, 0x48,
    0xC7, 0xC1, 0xE0, 0x27, 0x20, 0x00, 0x49, 0xC7, 0xC0, 0x10, 0x28, 0x20, 0x00, 0xE8, 0xF4, 0x2F,
    0x02, 0x00]

theorem code_l10657a : ∀ x ∈ codeRange 0x10657a bytes_l10657a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x657a 50 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1065ac : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1065ac (fun s => s.RIP = 0x1065ac) (fun _ => nopEffect 0x1065ac 4) (Reg.operands [] [])) #v[]
    (.letOp (n := 54) (.out 0x1065b0 (pushR64Effect 0x1065b0 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 55) (.exec 0x1065b0 (PushPre 0x1065b0 1) (pushR64Effect 0x1065b0 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 56) (.out 0x1065b1 (pushR64Effect 0x1065b1 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[54, 15]
    (.letOp (n := 57) (.exec 0x1065b1 (PushPre 0x1065b1 2) (pushR64Effect 0x1065b1 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[54, 15]
    (.letOp (n := 58) (.out 0x1065b3 (pushR64Effect 0x1065b3 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[56, 14]
    (.letOp (n := 59) (.exec 0x1065b3 (PushPre 0x1065b3 2) (pushR64Effect 0x1065b3 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[56, 14]
    (.letOp (n := 60) (.out 0x1065b5 (pushR64Effect 0x1065b5 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[58, 13]
    (.letOp (n := 61) (.exec 0x1065b5 (PushPre 0x1065b5 2) (pushR64Effect 0x1065b5 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[58, 13]
    (.letOp (n := 62) (.out 0x1065b7 (pushR64Effect 0x1065b7 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[60, 12]
    (.letOp (n := 63) (.exec 0x1065b7 (PushPre 0x1065b7 2) (pushR64Effect 0x1065b7 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[60, 12]
    (.letOp (n := 64) (.out 0x1065b9 (pushR64Effect 0x1065b9 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[62, 3]
    (.letOp (n := 65) (.exec 0x1065b9 (PushPre 0x1065b9 1) (pushR64Effect 0x1065b9 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[62, 3]
    (.letOp (n := 66) (.out 0x1065ba (subR64Imm8Effect 0x1065ba 4 0x18) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[64]
    (.letOp (n := 67) (.exec 0x1065ba (fun s => s.RIP = 0x1065ba) (subR64Imm8Effect 0x1065ba 4 0x18) (Reg.operands [.gpr 4] [])) #v[64]
    (.letOp (n := 68) (.out 0x1065be (cmpR32Imm32Effect 0x1065be 6 2 0x100) (EffectPart.reads (.flag .CF) [.gpr 2] []) (.flag .CF)) #v[2]
    (.letOp (n := 69) (.exec 0x1065be (fun s => s.RIP = 0x1065be) (cmpR32Imm32Effect 0x1065be 6 2 0x100) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 70) (.pure (condOp 3)) #v[68]
    (.terminate (.condBr (Fin.last 70) ⟨.l106764, RegMap.args [(2, 2), (3, 3), (4, 66), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (16, 68), (22, 22), (39, 39), (50, 50), (51, 51)] 71⟩ ⟨.l1065ca, RegMap.args [(2, 2), (3, 3), (4, 66), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (16, 68), (22, 22), (39, 39), (50, 50), (51, 51)] 71⟩)))))))))))))))))))

def bytes_l1065ac : List UInt8 :=
  [0x0F, 0x1F, 0x40, 0x00, 0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x83,
    0xEC, 0x18, 0x81, 0xFA, 0x00, 0x01, 0x00, 0x00, 0x0F, 0x83, 0x9A, 0x01, 0x00, 0x00]

theorem code_l1065ac : ∀ x ∈ codeRange 0x1065ac bytes_l1065ac, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x65ac 30 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1065ca_1 : Block Op Label signature Reg.count 86 :=
  .letOp (n := 86) (.exec 0x10661b (StorePre 0x10661b 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xb)) s (0x10661b + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10661b 4 1 (.sib 4 none 0 (.d8 0xb))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[84, 4]
    (.letOp (n := 87) (.out 0x10661f (movzxR32M8Effect 0x10661f 5 0 (.sib 4 none 0 (.d8 0xb))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 88) (.exec 0x10661f (LoadPre 0x10661f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xb)) s (0x10661f + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10661f 5 0 (.sib 4 none 0 (.d8 0xb))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 89) (.exec 0x106624 (StorePre 0x106624 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xb)) s (0x106624 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x106624 4 1 (.sib 4 none 0 (.d8 0xb))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[84, 4]
    (.letOp (n := 90) (.out 0x106628 (movzxR32M8Effect 0x106628 5 6 (.sib 4 none 0 (.d8 0xb))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 91) (.exec 0x106628 (LoadPre 0x106628 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xb)) s (0x106628 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x106628 5 6 (.sib 4 none 0 (.d8 0xb))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 92) (.exec 0x10662d (StorePre 0x10662d 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xd)) s (0x10662d + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10662d 4 1 (.sib 4 none 0 (.d8 0xd))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[84, 4]
    (.letOp (n := 93) (.out 0x106631 (movzxR32M8Effect 0x106631 6 8 (.sib 4 none 0 (.d8 0xd))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 94) (.exec 0x106631 (LoadPre 0x106631 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xd)) s (0x106631 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x106631 6 8 (.sib 4 none 0 (.d8 0xd))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 95) (.exec 0x106637 (StorePre 0x106637 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xd)) s (0x106637 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x106637 4 1 (.sib 4 none 0 (.d8 0xd))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[84, 4]
    (.letOp (n := 96) (.out 0x10663b (movzxR32M8Effect 0x10663b 6 11 (.sib 4 none 0 (.d8 0xd))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 97) (.exec 0x10663b (LoadPre 0x10663b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xd)) s (0x10663b + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x10663b 6 11 (.sib 4 none 0 (.d8 0xd))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 98) (.out 0x106641 (andR32Imm8Effect 0x106641 3 2 0x3f) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[2]
    (.letOp (n := 99) (.out 0x106641 (andR32Imm8Effect 0x106641 3 2 0x3f) (EffectPart.reads (.flag .ZF) [.gpr 2] []) (.flag .ZF)) #v[2]
    (.letOp (n := 100) (.exec 0x106641 (fun s => s.RIP = 0x106641) (andR32Imm8Effect 0x106641 3 2 0x3f) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 101) (.exec 0x106644 (StorePre 0x106644 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x106644 + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 5) (setccM8Effect 0x106644 5 (.sib 4 none 0 (.d8 0xe)))) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.ZF])) #v[4, 99]
    (.letOp (n := 102) (.out 0x106649 (atFlags (condHolds 5) (setccR8Effect 0x106649 4 7)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 7))) #v[7, 99]
    (.letOp (n := 103) (.exec 0x106649 (fun s => s.RIP = 0x106649) (atFlags (condHolds 5) (setccR8Effect 0x106649 4 7)) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[7, 99]
    (.letOp (n := 104) (.exec 0x10664d (fun s => s.RIP = 0x10664d) (leaR64Effect 0x10664d 1 (.sib 4 none 0 (.d8 0xe))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 105) (.out 0x106652 (movzxR32M8Effect 0x106652 5 1 (.sib 4 none 0 (.d8 0xe))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 106) (.exec 0x106652 (LoadPre 0x106652 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x106652 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x106652 5 1 (.sib 4 none 0 (.d8 0xe))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 107) (.out 0x106657 (negR32Effect 0x106657 2 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[105]
    (.letOp (n := 108) (.exec 0x106657 (fun s => s.RIP = 0x106657) (negR32Effect 0x106657 2 1) (Reg.operands [.gpr 1] [])) #v[105]
    (.letOp (n := 109) (.out 0x106659 (xorR32Imm8Effect 0x106659 3 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[98]
    (.letOp (n := 110) (.exec 0x106659 (fun s => s.RIP = 0x106659) (xorR32Imm8Effect 0x106659 3 2 0x1) (Reg.operands [.gpr 2] [])) #v[98]
    (.letOp (n := 111) (.out 0x10665c (andR32R32Effect 0x10665c 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[109, 107]
    (.letOp (n := 112) (.exec 0x10665c (fun s => s.RIP = 0x10665c) (andR32R32Effect 0x10665c 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[109, 107]
    (.letOp (n := 113) (.out 0x10665e (cmpR32Imm8Effect 0x10665e 3 2 0x1) (EffectPart.reads (.flag .ZF) [.gpr 2] []) (.flag .ZF)) #v[111]
    (.letOp (n := 114) (.exec 0x10665e (fun s => s.RIP = 0x10665e) (cmpR32Imm8Effect 0x10665e 3 2 0x1) (Reg.operands [.gpr 2] [])) #v[111]
    (.letOp (n := 115) (.pure (condOp 4)) #v[113]
    (.terminate (.condBr (Fin.last 115) ⟨.l10677c, RegMap.args [(0, 87), (1, 107), (2, 111), (3, 60), (4, 4), (5, 80), (6, 90), (7, 102), (8, 93), (9, 70), (10, 58), (11, 96), (12, 73), (13, 54), (14, 76), (15, 56), (19, 113), (22, 22), (39, 39), (50, 50), (51, 51)] 116⟩ ⟨.l106667, RegMap.args [(0, 87), (1, 107), (2, 111), (3, 60), (4, 4), (5, 80), (6, 90), (7, 102), (8, 93), (9, 70), (10, 58), (11, 96), (12, 73), (13, 54), (14, 76), (15, 56), (19, 113), (22, 22), (39, 39), (50, 50), (51, 51)] 116⟩)))))))))))))))))))))))))))))))

def bytes_l1065ca_1 : List UInt8 :=
  [0x88, 0x4C, 0x24, 0x0B, 0x0F, 0xB6, 0x44, 0x24, 0x0B, 0x88, 0x4C, 0x24, 0x0B, 0x0F, 0xB6, 0x74,
    0x24, 0x0B, 0x88, 0x4C, 0x24, 0x0D, 0x44, 0x0F, 0xB6, 0x44, 0x24, 0x0D, 0x88, 0x4C, 0x24, 0x0D,
    0x44, 0x0F, 0xB6, 0x5C, 0x24, 0x0D, 0x83, 0xE2, 0x3F, 0x0F, 0x95, 0x44, 0x24, 0x0E, 0x40, 0x0F,
    0x95, 0xC7, 0x48, 0x8D, 0x4C, 0x24, 0x0E, 0x0F, 0xB6, 0x4C, 0x24, 0x0E, 0xF7, 0xD9, 0x83, 0xF2,
    0x01, 0x21, 0xCA, 0x83, 0xFA, 0x01, 0x0F, 0x84, 0x15, 0x01, 0x00, 0x00]

theorem code_l1065ca_1 : ∀ x ∈ codeRange 0x10661b bytes_l1065ca_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x661b 76 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1065ca : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1065ca (StorePre 0x1065ca 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1065ca + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1065ca 7 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[7, 4]
    (.letOp (n := 54) (.out 0x1065cf (movR64M64Effect 0x1065cf 13 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 6] []) (.reg (.gpr 13))) #v[6]
    (.letOp (n := 55) (.exec 0x1065cf (LoadPre 0x1065cf (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x1065cf + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1065cf 13 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 56) (.out 0x1065d3 (movR64M64Effect 0x1065d3 15 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 6] []) (.reg (.gpr 15))) #v[6]
    (.letOp (n := 57) (.exec 0x1065d3 (LoadPre 0x1065d3 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x1065d3 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1065d3 15 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 58) (.out 0x1065d7 (movR64M64Effect 0x1065d7 10 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 6] []) (.reg (.gpr 10))) #v[6]
    (.letOp (n := 59) (.exec 0x1065d7 (LoadPre 0x1065d7 (fun s => AddrMode.addr (.base 6 .none) s (0x1065d7 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1065d7 10 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 60) (.out 0x1065da (movR64M64Effect 0x1065da 3 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 6] []) (.reg (.gpr 3))) #v[6]
    (.letOp (n := 61) (.exec 0x1065da (LoadPre 0x1065da (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x1065da + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1065da 3 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 62) (.out 0x1065de (movR32R32Effect 0x1065de 2 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 63) (.exec 0x1065de (fun s => s.RIP = 0x1065de) (movR32R32Effect 0x1065de 2 0 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 64) (.out 0x1065e0 (shrR8Effect 0x1065e0 3 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[62]
    (.letOp (n := 65) (.exec 0x1065e0 (fun s => s.RIP = 0x1065e0) (shrR8Effect 0x1065e0 3 0 6) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[62]
    (.letOp (n := 66) (.out 0x1065e3 (andAlImm8Effect 0x1065e3 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[64]
    (.letOp (n := 67) (.exec 0x1065e3 (fun s => s.RIP = 0x1065e3) (andAlImm8Effect 0x1065e3 0x1) (Reg.operands [.gpr 0] [])) #v[64]
    (.letOp (n := 68) (.exec 0x1065e5 (StorePre 0x1065e5 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xb)) s (0x1065e5 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1065e5 4 0 (.sib 4 none 0 (.d8 0xb))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[66, 4]
    (.letOp (n := 69) (.exec 0x1065e9 (fun s => s.RIP = 0x1065e9) (leaR64Effect 0x1065e9 6 (.sib 4 none 0 (.d8 0xb))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.out 0x1065ee (movzxR32M8Effect 0x1065ee 6 9 (.sib 4 none 0 (.d8 0xb))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 71) (.exec 0x1065ee (LoadPre 0x1065ee (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xb)) s (0x1065ee + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1065ee 6 9 (.sib 4 none 0 (.d8 0xb))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.exec 0x1065f4 (StorePre 0x1065f4 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xb)) s (0x1065f4 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1065f4 4 0 (.sib 4 none 0 (.d8 0xb))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[66, 4]
    (.letOp (n := 73) (.out 0x1065f8 (movzxR32M8Effect 0x1065f8 6 12 (.sib 4 none 0 (.d8 0xb))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 74) (.exec 0x1065f8 (LoadPre 0x1065f8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xb)) s (0x1065f8 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1065f8 6 12 (.sib 4 none 0 (.d8 0xb))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.exec 0x1065fe (StorePre 0x1065fe 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xb)) s (0x1065fe + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1065fe 4 0 (.sib 4 none 0 (.d8 0xb))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[66, 4]
    (.letOp (n := 76) (.out 0x106602 (movzxR32M8Effect 0x106602 6 14 (.sib 4 none 0 (.d8 0xb))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 77) (.exec 0x106602 (LoadPre 0x106602 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xb)) s (0x106602 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x106602 6 14 (.sib 4 none 0 (.d8 0xb))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 78) (.exec 0x106608 (StorePre 0x106608 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xd)) s (0x106608 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x106608 4 0 (.sib 4 none 0 (.d8 0xd))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[66, 4]
    (.letOp (n := 79) (.exec 0x10660c (fun s => s.RIP = 0x10660c) (leaR64Effect 0x10660c 11 (.sib 4 none 0 (.d8 0xd))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 80) (.out 0x106611 (movzxR32M8Effect 0x106611 5 5 (.sib 4 none 0 (.d8 0xd))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 81) (.exec 0x106611 (LoadPre 0x106611 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xd)) s (0x106611 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x106611 5 5 (.sib 4 none 0 (.d8 0xd))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 82) (.out 0x106616 (movR32R32Effect 0x106616 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2]
    (.letOp (n := 83) (.exec 0x106616 (fun s => s.RIP = 0x106616) (movR32R32Effect 0x106616 2 1 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 84) (.out 0x106618 (shrR32Effect 0x106618 3 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[82]
    (.letOp (n := 85) (.exec 0x106618 (fun s => s.RIP = 0x106618) (shrR32Effect 0x106618 3 1 7) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[82]
    (b_l1065ca_1)))))))))))))))))))))))))))))))))

def bytes_l1065ca : List UInt8 :=
  [0x48, 0x89, 0x7C, 0x24, 0x10, 0x4C, 0x8B, 0x6E, 0x18, 0x4C, 0x8B, 0x7E, 0x10, 0x4C, 0x8B, 0x16,
    0x48, 0x8B, 0x5E, 0x08, 0x89, 0xD0, 0xC0, 0xE8, 0x06, 0x24, 0x01, 0x88, 0x44, 0x24, 0x0B, 0x48,
    0x8D, 0x74, 0x24, 0x0B, 0x44, 0x0F, 0xB6, 0x4C, 0x24, 0x0B, 0x88, 0x44, 0x24, 0x0B, 0x44, 0x0F,
    0xB6, 0x64, 0x24, 0x0B, 0x88, 0x44, 0x24, 0x0B, 0x44, 0x0F, 0xB6, 0x74, 0x24, 0x0B, 0x88, 0x44,
    0x24, 0x0D, 0x4C, 0x8D, 0x5C, 0x24, 0x0D, 0x0F, 0xB6, 0x6C, 0x24, 0x0D, 0x89, 0xD1, 0xC1, 0xE9,
    0x07] ++ bytes_l1065ca_1

theorem code_l1065ca : ∀ x ∈ codeRange 0x1065ca bytes_l1065ca, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x65ca 81 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1065ca_1

@[cfg_block] def b_l106667_3 : Block Op Label signature Reg.count 168 :=
  .letOp (n := 168) (.out 0x10672e (xorR64R64Effect 0x10672e 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[159, 111]
    (.letOp (n := 169) (.exec 0x10672e (fun s => s.RIP = 0x10672e) (xorR64R64Effect 0x10672e 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[159, 111]
    (.letOp (n := 170) (.out 0x106731 (andR64R64Effect 0x106731 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[168, 166]
    (.letOp (n := 171) (.exec 0x106731 (fun s => s.RIP = 0x106731) (andR64R64Effect 0x106731 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[168, 166]
    (.letOp (n := 172) (.out 0x106734 (xorR64R64Effect 0x106734 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[170, 111]
    (.letOp (n := 173) (.exec 0x106734 (fun s => s.RIP = 0x106734) (xorR64R64Effect 0x106734 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[170, 111]
    (.letOp (n := 174) (.exec 0x106737 (StorePre 0x106737 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x106737 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x106737 5 7 (.sib 4 none 0 (.d8 0xf))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[7, 4]
    (.letOp (n := 175) (.exec 0x10673c (fun s => s.RIP = 0x10673c) (leaR64Effect 0x10673c 0 (.sib 4 none 0 (.d8 0xf))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 176) (.out 0x106741 (movR64M64Effect 0x106741 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 177) (.exec 0x106741 (LoadPre 0x106741 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x106741 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106741 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 178) (.exec 0x106746 (StorePre 0x106746 3 (fun s => AddrMode.addr (.base 0 .none) s (0x106746 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x106746 8 (.base 0 .none)) (Reg.operands [.gpr 8, .gpr 0] [])) #v[172, 176]
    (.letOp (n := 179) (.exec 0x106749 (StorePre 0x106749 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x106749 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x106749 11 (.base 0 (.d8 0x8))) (Reg.operands [.gpr 11, .gpr 0] [])) #v[161, 176]
    (.letOp (n := 180) (.exec 0x10674d (StorePre 0x10674d 4 (fun s => AddrMode.addr (.base 0 (.d8 0x10)) s (0x10674d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10674d 9 (.base 0 (.d8 0x10))) (Reg.operands [.gpr 9, .gpr 0] [])) #v[138, 176]
    (.letOp (n := 181) (.exec 0x106751 (StorePre 0x106751 4 (fun s => AddrMode.addr (.base 0 (.d8 0x18)) s (0x106751 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x106751 10 (.base 0 (.d8 0x18))) (Reg.operands [.gpr 10, .gpr 0] [])) #v[127, 176]
    (.letOp (n := 182) (.out 0x106755 (addR64Imm8Effect 0x106755 4 0x18) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 183) (.exec 0x106755 (fun s => s.RIP = 0x106755) (addR64Imm8Effect 0x106755 4 0x18) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 184) (.out 0x106759 (popR64Effect 0x106759 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[182]
    (.letOp (n := 185) (.out 0x106759 (popR64Effect 0x106759 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[182]
    (.letOp (n := 186) (.exec 0x106759 (PopPre 0x106759) (popR64Effect 0x106759 1 3) (Reg.operands [.gpr 4] [])) #v[182]
    (.letOp (n := 187) (.out 0x10675a (popR64Effect 0x10675a 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[185]
    (.letOp (n := 188) (.out 0x10675a (popR64Effect 0x10675a 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[185]
    (.letOp (n := 189) (.exec 0x10675a (PopPre 0x10675a) (popR64Effect 0x10675a 2 12) (Reg.operands [.gpr 4] [])) #v[185]
    (.letOp (n := 190) (.out 0x10675c (popR64Effect 0x10675c 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[188]
    (.letOp (n := 191) (.out 0x10675c (popR64Effect 0x10675c 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[188]
    (.letOp (n := 192) (.exec 0x10675c (PopPre 0x10675c) (popR64Effect 0x10675c 2 13) (Reg.operands [.gpr 4] [])) #v[188]
    (.letOp (n := 193) (.out 0x10675e (popR64Effect 0x10675e 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[191]
    (.letOp (n := 194) (.out 0x10675e (popR64Effect 0x10675e 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[191]
    (.letOp (n := 195) (.exec 0x10675e (PopPre 0x10675e) (popR64Effect 0x10675e 2 14) (Reg.operands [.gpr 4] [])) #v[191]
    (.letOp (n := 196) (.out 0x106760 (popR64Effect 0x106760 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[194]
    (.letOp (n := 197) (.out 0x106760 (popR64Effect 0x106760 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[194]
    (.letOp (n := 198) (.exec 0x106760 (PopPre 0x106760) (popR64Effect 0x106760 2 15) (Reg.operands [.gpr 4] [])) #v[194]
    (.letOp (n := 199) (.out 0x106762 (popR64Effect 0x106762 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[197]
    (.letOp (n := 200) (.out 0x106762 (popR64Effect 0x106762 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[197]
    (.letOp (n := 201) (.exec 0x106762 (PopPre 0x106762) (popR64Effect 0x106762 1 5) (Reg.operands [.gpr 4] [])) #v[197]
    (.letOp (n := 202) (.out 0x106763 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[200]
    (.letOp (n := 203) (.out 0x106763 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[200]
    (.letOp (n := 204) (.exec 0x106763 (RetPre 0x106763) (retEffect) (Reg.operands [.gpr 4] [])) #v[200]
    (.terminate (.ret (RegMap.args [(0, 176), (1, 166), (2, 103), (3, 184), (4, 203), (5, 199), (6, 87), (7, 7), (8, 172), (9, 138), (10, 127), (11, 161), (12, 187), (13, 190), (14, 193), (15, 196), (22, 22), (39, 39), (50, 50), (51, 51)] 205) (some ⟨202, by decide⟩)))))))))))))))))))))))))))))))))))))))

def bytes_l106667_3 : List UInt8 :=
  [0x49, 0x31, 0xC0, 0x49, 0x21, 0xC8, 0x49, 0x31, 0xC0, 0x40, 0x88, 0x7C, 0x24, 0x0F, 0x48, 0x8D,
    0x44, 0x24, 0x0F, 0x48, 0x8B, 0x44, 0x24, 0x10, 0x4C, 0x89, 0x00, 0x4C, 0x89, 0x58, 0x08, 0x4C,
    0x89, 0x48, 0x10, 0x4C, 0x89, 0x50, 0x18, 0x48, 0x83, 0xC4, 0x18, 0x5B, 0x41, 0x5C, 0x41, 0x5D,
    0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l106667_3 : ∀ x ∈ codeRange 0x10672e bytes_l106667_3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x672e 54 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106667_2 : Block Op Label signature Reg.count 130 :=
  .letOp (n := 130) (.out 0x1066e8 (movzxR32M8Effect 0x1066e8 5 1 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 131) (.exec 0x1066e8 (LoadPre 0x1066e8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x1066e8 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1066e8 5 1 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 132) (.out 0x1066ed (negR64Effect 0x1066ed 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[130]
    (.letOp (n := 133) (.exec 0x1066ed (fun s => s.RIP = 0x1066ed) (negR64Effect 0x1066ed 1) (Reg.operands [.gpr 1] [])) #v[130]
    (.letOp (n := 134) (.out 0x1066f0 (xorR64R64Effect 0x1066f0 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8] []) (.reg (.gpr 9))) #v[121, 71]
    (.letOp (n := 135) (.exec 0x1066f0 (fun s => s.RIP = 0x1066f0) (xorR64R64Effect 0x1066f0 9 8) (Reg.operands [.gpr 9, .gpr 8] [])) #v[121, 71]
    (.letOp (n := 136) (.out 0x1066f3 (andR64R64Effect 0x1066f3 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1] []) (.reg (.gpr 9))) #v[134, 132]
    (.letOp (n := 137) (.exec 0x1066f3 (fun s => s.RIP = 0x1066f3) (andR64R64Effect 0x1066f3 9 1) (Reg.operands [.gpr 9, .gpr 1] [])) #v[134, 132]
    (.letOp (n := 138) (.out 0x1066f6 (xorR64R64Effect 0x1066f6 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8] []) (.reg (.gpr 9))) #v[136, 71]
    (.letOp (n := 139) (.exec 0x1066f6 (fun s => s.RIP = 0x1066f6) (xorR64R64Effect 0x1066f6 9 8) (Reg.operands [.gpr 9, .gpr 8] [])) #v[136, 71]
    (.letOp (n := 140) (.out 0x1066f9 (movR64R64Effect 0x1066f9 11 6) (EffectPart.reads (.reg (.gpr 11)) [.gpr 6] []) (.reg (.gpr 11))) #v[87]
    (.letOp (n := 141) (.exec 0x1066f9 (fun s => s.RIP = 0x1066f9) (movR64R64Effect 0x1066f9 11 6) (Reg.operands [.gpr 6] [])) #v[87]
    (.letOp (n := 142) (.out 0x1066fc (movR32R32Effect 0x1066fc 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[103]
    (.letOp (n := 143) (.exec 0x1066fc (fun s => s.RIP = 0x1066fc) (movR32R32Effect 0x1066fc 2 1 2) (Reg.operands [.gpr 2] [])) #v[103]
    (.letOp (n := 144) (.out 0x1066fe (shrdR64R64ClEffect 0x1066fe 4 11 8) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 8, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[140, 71, 142]
    (.letOp (n := 145) (.exec 0x1066fe (fun s => s.RIP = 0x1066fe) (shrdR64R64ClEffect 0x1066fe 4 11 8) (Reg.operands [.gpr 11, .gpr 8, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[140, 71, 142]
    (.letOp (n := 146) (.exec 0x106702 (StorePre 0x106702 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x106702 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x106702 5 7 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[7, 4]
    (.letOp (n := 147) (.out 0x106707 (movzxR32M8Effect 0x106707 5 1 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 148) (.exec 0x106707 (LoadPre 0x106707 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x106707 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x106707 5 1 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 149) (.out 0x10670c (negR64Effect 0x10670c 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[147]
    (.letOp (n := 150) (.exec 0x10670c (fun s => s.RIP = 0x10670c) (negR64Effect 0x10670c 1) (Reg.operands [.gpr 1] [])) #v[147]
    (.letOp (n := 151) (.out 0x10670f (xorR64R64Effect 0x10670f 11 6) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 6] []) (.reg (.gpr 11))) #v[144, 87]
    (.letOp (n := 152) (.exec 0x10670f (fun s => s.RIP = 0x10670f) (xorR64R64Effect 0x10670f 11 6) (Reg.operands [.gpr 11, .gpr 6] [])) #v[144, 87]
    (.letOp (n := 153) (.out 0x106712 (andR64R64Effect 0x106712 11 1) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 1] []) (.reg (.gpr 11))) #v[151, 149]
    (.letOp (n := 154) (.exec 0x106712 (fun s => s.RIP = 0x106712) (andR64R64Effect 0x106712 11 1) (Reg.operands [.gpr 11, .gpr 1] [])) #v[151, 149]
    (.letOp (n := 155) (.out 0x106715 (movR64R64Effect 0x106715 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[111]
    (.letOp (n := 156) (.exec 0x106715 (fun s => s.RIP = 0x106715) (movR64R64Effect 0x106715 8 0) (Reg.operands [.gpr 0] [])) #v[111]
    (.letOp (n := 157) (.out 0x106718 (movR32R32Effect 0x106718 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[103]
    (.letOp (n := 158) (.exec 0x106718 (fun s => s.RIP = 0x106718) (movR32R32Effect 0x106718 2 1 2) (Reg.operands [.gpr 2] [])) #v[103]
    (.letOp (n := 159) (.out 0x10671a (shrdR64R64ClEffect 0x10671a 4 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[155, 87, 157]
    (.letOp (n := 160) (.exec 0x10671a (fun s => s.RIP = 0x10671a) (shrdR64R64ClEffect 0x10671a 4 8 6) (Reg.operands [.gpr 8, .gpr 6, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[155, 87, 157]
    (.letOp (n := 161) (.out 0x10671e (xorR64R64Effect 0x10671e 11 6) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 6] []) (.reg (.gpr 11))) #v[153, 87]
    (.letOp (n := 162) (.exec 0x10671e (fun s => s.RIP = 0x10671e) (xorR64R64Effect 0x10671e 11 6) (Reg.operands [.gpr 11, .gpr 6] [])) #v[153, 87]
    (.letOp (n := 163) (.exec 0x106721 (StorePre 0x106721 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x106721 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x106721 5 7 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[7, 4]
    (.letOp (n := 164) (.out 0x106726 (movzxR32M8Effect 0x106726 5 1 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 165) (.exec 0x106726 (LoadPre 0x106726 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x106726 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x106726 5 1 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 166) (.out 0x10672b (negR64Effect 0x10672b 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[164]
    (.letOp (n := 167) (.exec 0x10672b (fun s => s.RIP = 0x10672b) (negR64Effect 0x10672b 1) (Reg.operands [.gpr 1] [])) #v[164]
    (b_l106667_3))))))))))))))))))))))))))))))))))))))

def bytes_l106667_2 : List UInt8 :=
  [0x0F, 0xB6, 0x4C, 0x24, 0x0C, 0x48, 0xF7, 0xD9, 0x4D, 0x31, 0xC1, 0x49, 0x21, 0xC9, 0x4D, 0x31,
    0xC1, 0x49, 0x89, 0xF3, 0x89, 0xD1, 0x4D, 0x0F, 0xAD, 0xC3, 0x40, 0x88, 0x7C, 0x24, 0x0C, 0x0F,
    0xB6, 0x4C, 0x24, 0x0C, 0x48, 0xF7, 0xD9, 0x49, 0x31, 0xF3, 0x49, 0x21, 0xCB, 0x49, 0x89, 0xC0,
    0x89, 0xD1, 0x49, 0x0F, 0xAD, 0xF0, 0x49, 0x31, 0xF3, 0x40, 0x88, 0x7C, 0x24, 0x0C, 0x0F, 0xB6,
    0x4C, 0x24, 0x0C, 0x48, 0xF7, 0xD9] ++ bytes_l106667_3

theorem code_l106667_2 : ∀ x ∈ codeRange 0x1066e8 bytes_l106667_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x66e8 70 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l106667_3

@[cfg_block] def b_l106667_1 : Block Op Label signature Reg.count 93 :=
  .letOp (n := 93) (.out 0x1066a3 (andR64R64Effect 0x1066a3 9 3) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 3] []) (.reg (.gpr 9))) #v[91, 89]
    (.letOp (n := 94) (.exec 0x1066a3 (fun s => s.RIP = 0x1066a3) (andR64R64Effect 0x1066a3 9 3) (Reg.operands [.gpr 9, .gpr 3] [])) #v[91, 89]
    (.letOp (n := 95) (.out 0x1066a6 (xorR64R64Effect 0x1066a6 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[93, 10]
    (.letOp (n := 96) (.exec 0x1066a6 (fun s => s.RIP = 0x1066a6) (xorR64R64Effect 0x1066a6 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[93, 10]
    (.letOp (n := 97) (.out 0x1066a9 (xorR64R64Effect 0x1066a9 14 9) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 9] []) (.reg (.gpr 14))) #v[69, 95]
    (.letOp (n := 98) (.exec 0x1066a9 (fun s => s.RIP = 0x1066a9) (xorR64R64Effect 0x1066a9 14 9) (Reg.operands [.gpr 14, .gpr 9] [])) #v[69, 95]
    (.letOp (n := 99) (.out 0x1066ac (negR64Effect 0x1066ac 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 100) (.exec 0x1066ac (fun s => s.RIP = 0x1066ac) (negR64Effect 0x1066ac 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 101) (.out 0x1066af (andR64R64Effect 0x1066af 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[99, 97]
    (.letOp (n := 102) (.exec 0x1066af (fun s => s.RIP = 0x1066af) (andR64R64Effect 0x1066af 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[99, 97]
    (.letOp (n := 103) (.out 0x1066b2 (xorR8Imm8Effect 0x1066b2 3 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[2]
    (.letOp (n := 104) (.exec 0x1066b2 (fun s => s.RIP = 0x1066b2) (xorR8Imm8Effect 0x1066b2 3 2 0x1) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 105) (.out 0x1066b5 (movR64R64Effect 0x1066b5 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 11] []) (.reg (.gpr 10))) #v[59]
    (.letOp (n := 106) (.exec 0x1066b5 (fun s => s.RIP = 0x1066b5) (movR64R64Effect 0x1066b5 10 11) (Reg.operands [.gpr 11] [])) #v[59]
    (.letOp (n := 107) (.out 0x1066b8 (movR32R32Effect 0x1066b8 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[103]
    (.letOp (n := 108) (.exec 0x1066b8 (fun s => s.RIP = 0x1066b8) (movR32R32Effect 0x1066b8 2 1 2) (Reg.operands [.gpr 2] [])) #v[103]
    (.letOp (n := 109) (.out 0x1066ba (shrR64ClEffect 0x1066ba 3 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[105, 107]
    (.letOp (n := 110) (.exec 0x1066ba (fun s => s.RIP = 0x1066ba) (shrR64ClEffect 0x1066ba 3 10) (Reg.operands [.gpr 10, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[105, 107]
    (.letOp (n := 111) (.out 0x1066bd (xorR64R64Effect 0x1066bd 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[101, 95]
    (.letOp (n := 112) (.exec 0x1066bd (fun s => s.RIP = 0x1066bd) (xorR64R64Effect 0x1066bd 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[101, 95]
    (.letOp (n := 113) (.exec 0x1066c0 (StorePre 0x1066c0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x1066c0 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1066c0 5 7 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[7, 4]
    (.letOp (n := 114) (.exec 0x1066c5 (fun s => s.RIP = 0x1066c5) (leaR64Effect 0x1066c5 3 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 115) (.out 0x1066ca (movzxR32M8Effect 0x1066ca 6 14 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 116) (.exec 0x1066ca (LoadPre 0x1066ca (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x1066ca + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1066ca 6 14 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 117) (.out 0x1066d0 (negR64Effect 0x1066d0 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14] []) (.reg (.gpr 14))) #v[115]
    (.letOp (n := 118) (.exec 0x1066d0 (fun s => s.RIP = 0x1066d0) (negR64Effect 0x1066d0 14) (Reg.operands [.gpr 14] [])) #v[115]
    (.letOp (n := 119) (.out 0x1066d3 (movR64R64Effect 0x1066d3 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 8] []) (.reg (.gpr 9))) #v[71]
    (.letOp (n := 120) (.exec 0x1066d3 (fun s => s.RIP = 0x1066d3) (movR64R64Effect 0x1066d3 9 8) (Reg.operands [.gpr 8] [])) #v[71]
    (.letOp (n := 121) (.out 0x1066d6 (shrdR64R64ClEffect 0x1066d6 4 9 11) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 11, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[119, 59, 107]
    (.letOp (n := 122) (.exec 0x1066d6 (fun s => s.RIP = 0x1066d6) (shrdR64R64ClEffect 0x1066d6 4 9 11) (Reg.operands [.gpr 9, .gpr 11, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[119, 59, 107]
    (.letOp (n := 123) (.out 0x1066da (xorR64R64Effect 0x1066da 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 11] []) (.reg (.gpr 10))) #v[109, 59]
    (.letOp (n := 124) (.exec 0x1066da (fun s => s.RIP = 0x1066da) (xorR64R64Effect 0x1066da 10 11) (Reg.operands [.gpr 10, .gpr 11] [])) #v[109, 59]
    (.letOp (n := 125) (.out 0x1066dd (andR64R64Effect 0x1066dd 10 14) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 14] []) (.reg (.gpr 10))) #v[123, 117]
    (.letOp (n := 126) (.exec 0x1066dd (fun s => s.RIP = 0x1066dd) (andR64R64Effect 0x1066dd 10 14) (Reg.operands [.gpr 10, .gpr 14] [])) #v[123, 117]
    (.letOp (n := 127) (.out 0x1066e0 (xorR64R64Effect 0x1066e0 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 11] []) (.reg (.gpr 10))) #v[125, 59]
    (.letOp (n := 128) (.exec 0x1066e0 (fun s => s.RIP = 0x1066e0) (xorR64R64Effect 0x1066e0 10 11) (Reg.operands [.gpr 10, .gpr 11] [])) #v[125, 59]
    (.letOp (n := 129) (.exec 0x1066e3 (StorePre 0x1066e3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x1066e3 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1066e3 5 7 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[7, 4]
    (b_l106667_2)))))))))))))))))))))))))))))))))))))

def bytes_l106667_1 : List UInt8 :=
  [0x49, 0x21, 0xD9, 0x4D, 0x31, 0xD1, 0x4D, 0x31, 0xCE, 0x48, 0xF7, 0xD8, 0x4C, 0x21, 0xF0, 0x80,
    0xF2, 0x01, 0x4D, 0x89, 0xDA, 0x89, 0xD1, 0x49, 0xD3, 0xEA, 0x4C, 0x31, 0xC8, 0x40, 0x88, 0x7C,
    0x24, 0x0C, 0x48, 0x8D, 0x5C, 0x24, 0x0C, 0x44, 0x0F, 0xB6, 0x74, 0x24, 0x0C, 0x49, 0xF7, 0xDE,
    0x4D, 0x89, 0xC1, 0x4D, 0x0F, 0xAD, 0xD9, 0x4D, 0x31, 0xDA, 0x4D, 0x21, 0xF2, 0x4D, 0x31, 0xDA,
    0x40, 0x88, 0x7C, 0x24, 0x0C] ++ bytes_l106667_2

theorem code_l106667_1 : ∀ x ∈ codeRange 0x1066a3 bytes_l106667_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x66a3 69 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l106667_2

@[cfg_block] def b_l106667 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106667 (decR64Effect 0x106667 11) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[11]
    (.letOp (n := 54) (.exec 0x106667 (fun s => s.RIP = 0x106667) (decR64Effect 0x106667 11) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[11]
    (.letOp (n := 55) (.out 0x10666a (decR64Effect 0x10666a 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[5]
    (.letOp (n := 56) (.exec 0x10666a (fun s => s.RIP = 0x10666a) (decR64Effect 0x10666a 5) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5]
    (.letOp (n := 57) (.out 0x10666d (andR64R64Effect 0x10666d 5 13) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 13] []) (.reg (.gpr 5))) #v[55, 13]
    (.letOp (n := 58) (.exec 0x10666d (fun s => s.RIP = 0x10666d) (andR64R64Effect 0x10666d 5 13) (Reg.operands [.gpr 5, .gpr 13] [])) #v[55, 13]
    (.letOp (n := 59) (.out 0x106670 (andR64R64Effect 0x106670 11 5) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 5] []) (.reg (.gpr 11))) #v[53, 57]
    (.letOp (n := 60) (.exec 0x106670 (fun s => s.RIP = 0x106670) (andR64R64Effect 0x106670 11 5) (Reg.operands [.gpr 11, .gpr 5] [])) #v[53, 57]
    (.letOp (n := 61) (.out 0x106673 (decR64Effect 0x106673 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[8]
    (.letOp (n := 62) (.exec 0x106673 (fun s => s.RIP = 0x106673) (decR64Effect 0x106673 8) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[8]
    (.letOp (n := 63) (.out 0x106676 (xorR64R64Effect 0x106676 13 15) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 15] []) (.reg (.gpr 13))) #v[13, 15]
    (.letOp (n := 64) (.exec 0x106676 (fun s => s.RIP = 0x106676) (xorR64R64Effect 0x106676 13 15) (Reg.operands [.gpr 13, .gpr 15] [])) #v[13, 15]
    (.letOp (n := 65) (.out 0x106679 (negR64Effect 0x106679 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14] []) (.reg (.gpr 14))) #v[14]
    (.letOp (n := 66) (.exec 0x106679 (fun s => s.RIP = 0x106679) (negR64Effect 0x106679 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 67) (.out 0x10667c (andR64R64Effect 0x10667c 14 13) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 13] []) (.reg (.gpr 14))) #v[65, 63]
    (.letOp (n := 68) (.exec 0x10667c (fun s => s.RIP = 0x10667c) (andR64R64Effect 0x10667c 14 13) (Reg.operands [.gpr 14, .gpr 13] [])) #v[65, 63]
    (.letOp (n := 69) (.out 0x10667f (xorR64R64Effect 0x10667f 14 15) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 15] []) (.reg (.gpr 14))) #v[67, 15]
    (.letOp (n := 70) (.exec 0x10667f (fun s => s.RIP = 0x10667f) (xorR64R64Effect 0x10667f 14 15) (Reg.operands [.gpr 14, .gpr 15] [])) #v[67, 15]
    (.letOp (n := 71) (.out 0x106682 (andR64R64Effect 0x106682 8 14) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 14] []) (.reg (.gpr 8))) #v[61, 69]
    (.letOp (n := 72) (.exec 0x106682 (fun s => s.RIP = 0x106682) (andR64R64Effect 0x106682 8 14) (Reg.operands [.gpr 8, .gpr 14] [])) #v[61, 69]
    (.letOp (n := 73) (.out 0x106685 (xorR64R64Effect 0x106685 15 3) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 3] []) (.reg (.gpr 15))) #v[15, 3]
    (.letOp (n := 74) (.exec 0x106685 (fun s => s.RIP = 0x106685) (xorR64R64Effect 0x106685 15 3) (Reg.operands [.gpr 15, .gpr 3] [])) #v[15, 3]
    (.letOp (n := 75) (.out 0x106688 (negR64Effect 0x106688 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[12]
    (.letOp (n := 76) (.exec 0x106688 (fun s => s.RIP = 0x106688) (negR64Effect 0x106688 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 77) (.out 0x10668b (andR64R64Effect 0x10668b 12 15) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 15] []) (.reg (.gpr 12))) #v[75, 73]
    (.letOp (n := 78) (.exec 0x10668b (fun s => s.RIP = 0x10668b) (andR64R64Effect 0x10668b 12 15) (Reg.operands [.gpr 12, .gpr 15] [])) #v[75, 73]
    (.letOp (n := 79) (.out 0x10668e (xorR64R64Effect 0x10668e 12 3) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 3] []) (.reg (.gpr 12))) #v[77, 3]
    (.letOp (n := 80) (.exec 0x10668e (fun s => s.RIP = 0x10668e) (xorR64R64Effect 0x10668e 12 3) (Reg.operands [.gpr 12, .gpr 3] [])) #v[77, 3]
    (.letOp (n := 81) (.out 0x106691 (xorR64R64Effect 0x106691 5 12) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 12] []) (.reg (.gpr 5))) #v[57, 79]
    (.letOp (n := 82) (.exec 0x106691 (fun s => s.RIP = 0x106691) (xorR64R64Effect 0x106691 5 12) (Reg.operands [.gpr 5, .gpr 12] [])) #v[57, 79]
    (.letOp (n := 83) (.out 0x106694 (negR64Effect 0x106694 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[6]
    (.letOp (n := 84) (.exec 0x106694 (fun s => s.RIP = 0x106694) (negR64Effect 0x106694 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 85) (.out 0x106697 (andR64R64Effect 0x106697 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 5] []) (.reg (.gpr 6))) #v[83, 81]
    (.letOp (n := 86) (.exec 0x106697 (fun s => s.RIP = 0x106697) (andR64R64Effect 0x106697 6 5) (Reg.operands [.gpr 6, .gpr 5] [])) #v[83, 81]
    (.letOp (n := 87) (.out 0x10669a (xorR64R64Effect 0x10669a 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 12] []) (.reg (.gpr 6))) #v[85, 79]
    (.letOp (n := 88) (.exec 0x10669a (fun s => s.RIP = 0x10669a) (xorR64R64Effect 0x10669a 6 12) (Reg.operands [.gpr 6, .gpr 12] [])) #v[85, 79]
    (.letOp (n := 89) (.out 0x10669d (xorR64R64Effect 0x10669d 3 10) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 10] []) (.reg (.gpr 3))) #v[3, 10]
    (.letOp (n := 90) (.exec 0x10669d (fun s => s.RIP = 0x10669d) (xorR64R64Effect 0x10669d 3 10) (Reg.operands [.gpr 3, .gpr 10] [])) #v[3, 10]
    (.letOp (n := 91) (.out 0x1066a0 (negR64Effect 0x1066a0 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[9]
    (.letOp (n := 92) (.exec 0x1066a0 (fun s => s.RIP = 0x1066a0) (negR64Effect 0x1066a0 9) (Reg.operands [.gpr 9] [])) #v[9]
    (b_l106667_1))))))))))))))))))))))))))))))))))))))))

def bytes_l106667 : List UInt8 :=
  [0x49, 0xFF, 0xCB, 0x48, 0xFF, 0xCD, 0x4C, 0x21, 0xED, 0x49, 0x21, 0xEB, 0x49, 0xFF, 0xC8, 0x4D,
    0x31, 0xFD, 0x49, 0xF7, 0xDE, 0x4D, 0x21, 0xEE, 0x4D, 0x31, 0xFE, 0x4D, 0x21, 0xF0, 0x49, 0x31,
    0xDF, 0x49, 0xF7, 0xDC, 0x4D, 0x21, 0xFC, 0x49, 0x31, 0xDC, 0x4C, 0x31, 0xE5, 0x48, 0xF7, 0xDE,
    0x48, 0x21, 0xEE, 0x4C, 0x31, 0xE6, 0x4C, 0x31, 0xD3, 0x49, 0xF7, 0xD9] ++ bytes_l106667_1

theorem code_l106667 : ∀ x ∈ codeRange 0x106667 bytes_l106667, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x6667 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l106667_1

@[cfg_block] def b_l106764 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106764 (movR32Imm32Effect 0x106764 5 6 0x37) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 54) (.exec 0x106764 (fun s => s.RIP = 0x106764) (movR32Imm32Effect 0x106764 5 6 0x37) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x106769 (movR64Imm32Effect 0x106769 7 0x20249c) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 56) (.exec 0x106769 (fun s => s.RIP = 0x106769) (movR64Imm32Effect 0x106769 7 0x20249c) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x106770 (movR64Imm32Effect 0x106770 2 0x2024b8) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x106770 (fun s => s.RIP = 0x106770) (movR64Imm32Effect 0x106770 2 0x2024b8) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x106777 (callEffect (fun _ => 0x129770) 0x10677c) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x106777 (PushPre 0x106777 5) (callEffect (fun _ => 0x129770) 0x10677c) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x10677c⟩) #v[]
    (.terminate (.call ⟨.l129770, RegMap.args [(2, 57), (4, 59), (5, 5), (6, 53), (7, 55)] 62⟩ { target := .l10677c, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l106764 : List UInt8 :=
  [0xBE, 0x37, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC7, 0x9C, 0x24, 0x20, 0x00, 0x48, 0xC7, 0xC2, 0xB8,
    0x24, 0x20, 0x00, 0xE8, 0xF4, 0x2F, 0x02, 0x00]

theorem code_l106764 : ∀ x ∈ codeRange 0x106764 bytes_l106764, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6764 24 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10677c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10677c (movR32Imm32Effect 0x10677c 5 6 0x10) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 54) (.exec 0x10677c (fun s => s.RIP = 0x10677c) (movR32Imm32Effect 0x10677c 5 6 0x10) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x106781 (movR64Imm32Effect 0x106781 7 0x2024d0) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 56) (.exec 0x106781 (fun s => s.RIP = 0x106781) (movR64Imm32Effect 0x106781 7 0x2024d0) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x106788 (movR64Imm32Effect 0x106788 2 0x202500) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x106788 (fun s => s.RIP = 0x106788) (movR64Imm32Effect 0x106788 2 0x202500) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x10678f (callEffect (fun _ => 0x129560) 0x106794) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x10678f (PushPre 0x10678f 5) (callEffect (fun _ => 0x129560) 0x106794) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x106794⟩) #v[]
    (.terminate (.call ⟨.l129560, RegMap.args [(2, 57), (4, 59), (5, 5), (6, 53), (7, 55)] 62⟩ { target := .l106794, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l10677c : List UInt8 :=
  [0xBE, 0x10, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC7, 0xD0, 0x24, 0x20, 0x00, 0x48, 0xC7, 0xC2, 0x00,
    0x25, 0x20, 0x00, 0xE8, 0xCC, 0x2D, 0x02, 0x00]

theorem code_l10677c : ∀ x ∈ codeRange 0x10677c bytes_l10677c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x677c 24 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106794 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x106794 (fun s => s.RIP = 0x106794) (fun _ => nopEffect 0x106794 10) (Reg.operands [] [])) #v[]
    (.letOp (n := 54) (.exec 0x10679e (fun s => s.RIP = 0x10679e) (fun _ => nopEffect 0x10679e 2) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x1067a0 (movR64M64Effect 0x1067a0 7 (.base 7 .none)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[7]
    (.letOp (n := 56) (.exec 0x1067a0 (LoadPre 0x1067a0 (fun s => AddrMode.addr (.base 7 .none) s (0x1067a0 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1067a0 7 (.base 7 .none)) (Reg.operands [.gpr 7] [])) #v[7]
    (.terminate (.br ⟨.l127cd0, RegMap.args [(0, 0), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (14, 14), (15, 15)] 57⟩)))))

def bytes_l106794 : List UInt8 :=
  [0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00, 0x66, 0x90, 0x48, 0x8B, 0x3F, 0xE9,
    0x28, 0x15, 0x02, 0x00]

theorem code_l106794 : ∀ x ∈ codeRange 0x106794 bytes_l106794, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6794 20 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

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

end K256.Proofs.Sec1.LIR
