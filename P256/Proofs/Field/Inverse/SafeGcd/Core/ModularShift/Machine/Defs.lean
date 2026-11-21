import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine.Labels
import P256.Proofs.Common.CFG.EvalAttr
import P256.Proofs.Common.Lift.Generated.Footprints

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

@[cfg_block] def b_l116d00 : Block Op Label signature Reg.count 53 :=
  cutBlock 0x111220

def bytes_l116d00 : List UInt8 := [0x55]

theorem code_l116d00 : ∀ x ∈ codeRange 0x111220 bytes_l116d00, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x11220 1 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1171a0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1116c0 (pushR64Effect 0x1116c0 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x1116c0 (PushPre 0x1116c0 1) (pushR64Effect 0x1116c0 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x1116c1 (pushR64Effect 0x1116c1 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x1116c1 (PushPre 0x1116c1 2) (pushR64Effect 0x1116c1 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x1116c3 (pushR64Effect 0x1116c3 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x1116c3 (PushPre 0x1116c3 2) (pushR64Effect 0x1116c3 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x1116c5 (pushR64Effect 0x1116c5 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x1116c5 (PushPre 0x1116c5 2) (pushR64Effect 0x1116c5 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x1116c7 (pushR64Effect 0x1116c7 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x1116c7 (PushPre 0x1116c7 2) (pushR64Effect 0x1116c7 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x1116c9 (pushR64Effect 0x1116c9 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x1116c9 (PushPre 0x1116c9 1) (pushR64Effect 0x1116c9 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x1116ca (subR64Imm8Effect 0x1116ca 4 0x78) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x1116ca (fun s => s.RIP = 0x1116ca) (subR64Imm8Effect 0x1116ca 4 0x78) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x1116ce (movR32R32Effect 0x1116ce 3 5 9) (EffectPart.reads (.reg (.gpr 5)) [.gpr 9] []) (.reg (.gpr 5))) #v[9]
    (.letOp (n := 68) (.exec 0x1116ce (fun s => s.RIP = 0x1116ce) (movR32R32Effect 0x1116ce 3 5 9) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 69) (.out 0x1116d1 (movR64R64Effect 0x1116d1 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 70) (.exec 0x1116d1 (fun s => s.RIP = 0x1116d1) (movR64R64Effect 0x1116d1 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 71) (.out 0x1116d4 (leaR64Effect 0x1116d4 7 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[65]
    (.letOp (n := 72) (.exec 0x1116d4 (fun s => s.RIP = 0x1116d4) (leaR64Effect 0x1116d4 7 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 73) (.out 0x1116d9 (callEffect (fun _ => 0x111220) 0x1116de) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 74) (.exec 0x1116d9 (PushPre 0x1116d9 5) (callEffect (fun _ => 0x111220) 0x1116de) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 75) (.const ⟨64, 0x1116de⟩) #v[]
    (.terminate (.call ⟨.l116d00, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 69), (4, 73), (5, 67), (6, 6), (7, 71), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)] 76⟩ { target := .l1171be, kept := #v[], arity := rfl, guard := some (Fin.last 75) }))))))))))))))))))))))))

def bytes_l1171a0 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x83, 0xEC, 0x78, 0x44, 0x89,
    0xCD, 0x48, 0x89, 0xFB, 0x48, 0x8D, 0x7C, 0x24, 0x10, 0xE8, 0x42, 0xFB, 0xFF, 0xFF]

theorem code_l1171a0 : ∀ x ∈ codeRange 0x1116c0 bytes_l1171a0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x116c0 30 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1171be : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1116de (movR32Imm32Effect 0x1116de 5 1 0x40) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 54) (.exec 0x1116de (fun s => s.RIP = 0x1116de) (movR32Imm32Effect 0x1116de 5 1 0x40) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.exec 0x1116e3 (StorePre 0x1116e3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x1116e3 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x1116e3 5 (.sib 4 none 0 (.d8 0x44))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[5, 4]
    (.letOp (n := 56) (.out 0x1116e7 (subR32R32Effect 0x1116e7 2 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 5] []) (.reg (.gpr 1))) #v[53, 5]
    (.letOp (n := 57) (.exec 0x1116e7 (fun s => s.RIP = 0x1116e7) (subR32R32Effect 0x1116e7 2 1 5) (Reg.operands [.gpr 1, .gpr 5] [])) #v[53, 5]
    (.letOp (n := 58) (.out 0x1116e9 (cmpR32Imm8Effect 0x1116e9 3 1 0x40) (EffectPart.reads (.flag .CF) [.gpr 1] []) (.flag .CF)) #v[56]
    (.letOp (n := 59) (.exec 0x1116e9 (fun s => s.RIP = 0x1116e9) (cmpR32Imm8Effect 0x1116e9 3 1 0x40) (Reg.operands [.gpr 1] [])) #v[56]
    (.letOp (n := 60) (.pure (condOp 3)) #v[58]
    (.terminate (.condBr (Fin.last 60) ⟨.l117619, RegMap.args [(1, 56), (3, 3), (4, 4), (5, 5), (16, 58), (22, 22), (39, 39), (51, 51)] 61⟩ ⟨.l1171d2, RegMap.args [(1, 56), (3, 3), (4, 4), (5, 5), (16, 58), (22, 22), (39, 39), (51, 51)] 61⟩)))))))))

def bytes_l1171be : List UInt8 :=
  [0xB9, 0x40, 0x00, 0x00, 0x00, 0x89, 0x6C, 0x24, 0x44, 0x29, 0xE9, 0x83, 0xF9, 0x40, 0x0F, 0x83,
    0x47, 0x04, 0x00, 0x00]

theorem code_l1171be : ∀ x ∈ codeRange 0x1116de bytes_l1171be, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x116de 20 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1171d2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1116f2 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1116f2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x1116f2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1116f2 3 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[3, 4]
    (.letOp (n := 54) (.out 0x1116f7 (movR64M64Effect 0x1116f7 7 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 55) (.exec 0x1116f7 (LoadPre 0x1116f7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x1116f7 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1116f7 7 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x1116ff (movR64M64Effect 0x1116ff 6 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 57) (.exec 0x1116ff (LoadPre 0x1116ff (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1116ff + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1116ff 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.out 0x111704 (movR64M64Effect 0x111704 9 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 59) (.exec 0x111704 (LoadPre 0x111704 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x111704 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x111704 9 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.out 0x11170c (imulR64R64Effect 0x11170c 4 9 6) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 6] []) (.reg (.gpr 9))) #v[58, 56]
    (.letOp (n := 61) (.exec 0x11170c (fun s => s.RIP = 0x11170c) (imulR64R64Effect 0x11170c 4 9 6) (Reg.operands [.gpr 9, .gpr 6] [])) #v[58, 56]
    (.letOp (n := 62) (.out 0x111710 (shlR64ClEffect 0x111710 3 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[60, 1]
    (.letOp (n := 63) (.exec 0x111710 (fun s => s.RIP = 0x111710) (shlR64ClEffect 0x111710 3 9) (Reg.operands [.gpr 9, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[60, 1]
    (.letOp (n := 64) (.out 0x111713 (shrR64ClEffect 0x111713 3 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[62, 1]
    (.letOp (n := 65) (.exec 0x111713 (fun s => s.RIP = 0x111713) (shrR64ClEffect 0x111713 3 9) (Reg.operands [.gpr 9, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[62, 1]
    (.letOp (n := 66) (.out 0x111716 (movR64M64Effect 0x111716 8 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 67) (.exec 0x111716 (LoadPre 0x111716 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x111716 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111716 8 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.out 0x11171b (movR64M64Effect 0x11171b 3 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 69) (.exec 0x11171b (LoadPre 0x11171b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11171b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11171b 3 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.br ⟨.l117200, RegMap.args [(1, 1), (3, 68), (4, 4), (6, 56), (7, 54), (8, 66), (9, 64), (22, 22), (39, 39), (51, 51)] 70⟩))))))))))))))))))

def bytes_l1171d2 : List UInt8 :=
  [0x48, 0x89, 0x5C, 0x24, 0x70, 0x48, 0x8B, 0xBC, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x74,
    0x24, 0x10, 0x4C, 0x8B, 0x8C, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x4C, 0x0F, 0xAF, 0xCE, 0x49, 0xD3,
    0xE1, 0x49, 0xD3, 0xE9, 0x4C, 0x8B, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x5C, 0x24, 0x20]

theorem code_l1171d2 : ∀ x ∈ codeRange 0x1116f2 bytes_l1171d2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x116f2 46 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l117200 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x111720 (movR64M64Effect 0x111720 0 (.base 7 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 54) (.exec 0x111720 (LoadPre 0x111720 (fun s => AddrMode.addr (.base 7 .none) s (0x111720 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x111720 0 (.base 7 .none)) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 55) (.out 0x111723 (movR64M64Effect 0x111723 10 (.base 7 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 7] []) (.reg (.gpr 10))) #v[7]
    (.letOp (n := 56) (.exec 0x111723 (LoadPre 0x111723 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x111723 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x111723 10 (.base 7 (.d8 0x8))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 57) (.exec 0x111727 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111727 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x111727 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x111727 0 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 58) (.out 0x11172c (mulR64Effect 0x11172c 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[9, 53]
    (.letOp (n := 59) (.out 0x11172c (mulR64Effect 0x11172c 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[9, 53]
    (.letOp (n := 60) (.exec 0x11172c (fun s => s.RIP = 0x11172c) (mulR64Effect 0x11172c 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[9, 53]
    (.letOp (n := 61) (.out 0x11172f (movR64R64Effect 0x11172f 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[59]
    (.letOp (n := 62) (.exec 0x11172f (fun s => s.RIP = 0x11172f) (movR64R64Effect 0x11172f 15 2) (Reg.operands [.gpr 2] [])) #v[59]
    (.letOp (n := 63) (.out 0x111732 (movR64R64Effect 0x111732 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[58]
    (.letOp (n := 64) (.exec 0x111732 (fun s => s.RIP = 0x111732) (movR64R64Effect 0x111732 14 0) (Reg.operands [.gpr 0] [])) #v[58]
    (.letOp (n := 65) (.exec 0x111735 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111735 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x111735 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x111735 10 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 66) (.out 0x11173a (movR64R64Effect 0x11173a 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[55]
    (.letOp (n := 67) (.exec 0x11173a (fun s => s.RIP = 0x11173a) (movR64R64Effect 0x11173a 0 10) (Reg.operands [.gpr 10] [])) #v[55]
    (.letOp (n := 68) (.out 0x11173d (mulR64Effect 0x11173d 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[9, 66]
    (.letOp (n := 69) (.out 0x11173d (mulR64Effect 0x11173d 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[9, 66]
    (.letOp (n := 70) (.exec 0x11173d (fun s => s.RIP = 0x11173d) (mulR64Effect 0x11173d 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[9, 66]
    (.letOp (n := 71) (.out 0x111740 (movR64R64Effect 0x111740 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[68]
    (.letOp (n := 72) (.exec 0x111740 (fun s => s.RIP = 0x111740) (movR64R64Effect 0x111740 11 0) (Reg.operands [.gpr 0] [])) #v[68]
    (.letOp (n := 73) (.out 0x111743 (movR64R64Effect 0x111743 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 2] []) (.reg (.gpr 12))) #v[69]
    (.letOp (n := 74) (.exec 0x111743 (fun s => s.RIP = 0x111743) (movR64R64Effect 0x111743 12 2) (Reg.operands [.gpr 2] [])) #v[69]
    (.letOp (n := 75) (.out 0x111746 (movR64M64Effect 0x111746 0 (.base 7 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 76) (.exec 0x111746 (LoadPre 0x111746 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x111746 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x111746 0 (.base 7 (.d8 0x10))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 77) (.exec 0x11174a (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x11174a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x11174a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11174a 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[75, 4]
    (.letOp (n := 78) (.out 0x11174f (mulR64Effect 0x11174f 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[9, 75]
    (.letOp (n := 79) (.out 0x11174f (mulR64Effect 0x11174f 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[9, 75]
    (.letOp (n := 80) (.exec 0x11174f (fun s => s.RIP = 0x11174f) (mulR64Effect 0x11174f 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[9, 75]
    (.letOp (n := 81) (.out 0x111752 (movR64R64Effect 0x111752 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[78]
    (.letOp (n := 82) (.exec 0x111752 (fun s => s.RIP = 0x111752) (movR64R64Effect 0x111752 10 0) (Reg.operands [.gpr 0] [])) #v[78]
    (.letOp (n := 83) (.out 0x111755 (movR64R64Effect 0x111755 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[79]
    (.letOp (n := 84) (.exec 0x111755 (fun s => s.RIP = 0x111755) (movR64R64Effect 0x111755 13 2) (Reg.operands [.gpr 2] [])) #v[79]
    (.letOp (n := 85) (.out 0x111758 (movR64M64Effect 0x111758 0 (.base 7 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 86) (.exec 0x111758 (LoadPre 0x111758 (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x111758 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x111758 0 (.base 7 (.d8 0x18))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 87) (.exec 0x11175c (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x11175c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x11175c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11175c 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[85, 4]
    (.letOp (n := 88) (.out 0x111761 (mulR64Effect 0x111761 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[9, 85]
    (.letOp (n := 89) (.out 0x111761 (mulR64Effect 0x111761 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[9, 85]
    (.letOp (n := 90) (.exec 0x111761 (fun s => s.RIP = 0x111761) (mulR64Effect 0x111761 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[9, 85]
    (.terminate (.br ⟨.l117244, RegMap.args [(0, 88), (1, 1), (2, 89), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 81), (11, 71), (12, 73), (13, 83), (14, 63), (15, 61), (22, 22), (39, 39), (51, 51)] 91⟩)))))))))))))))))))))))))))))))))))))))

def bytes_l117200 : List UInt8 :=
  [0x48, 0x8B, 0x07, 0x4C, 0x8B, 0x57, 0x08, 0x48, 0x89, 0x44, 0x24, 0x50, 0x49, 0xF7, 0xE1, 0x49,
    0x89, 0xD7, 0x49, 0x89, 0xC6, 0x4C, 0x89, 0x54, 0x24, 0x58, 0x4C, 0x89, 0xD0, 0x49, 0xF7, 0xE1,
    0x49, 0x89, 0xC3, 0x49, 0x89, 0xD4, 0x48, 0x8B, 0x47, 0x10, 0x48, 0x89, 0x44, 0x24, 0x60, 0x49,
    0xF7, 0xE1, 0x49, 0x89, 0xC2, 0x49, 0x89, 0xD5, 0x48, 0x8B, 0x47, 0x18, 0x48, 0x89, 0x44, 0x24,
    0x68, 0x49, 0xF7, 0xE1]

theorem code_l117200 : ∀ x ∈ codeRange 0x111720 bytes_l117200, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x11720 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l117244 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x111764 (addR64R64Effect 0x111764 11 15) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 15] []) (.reg (.gpr 11))) #v[11, 15]
    (.letOp (n := 54) (.out 0x111764 (addR64R64Effect 0x111764 11 15) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 15] []) (.flag .CF)) #v[11, 15]
    (.letOp (n := 55) (.exec 0x111764 (fun s => s.RIP = 0x111764) (addR64R64Effect 0x111764 11 15) (Reg.operands [.gpr 11, .gpr 15] [])) #v[11, 15]
    (.letOp (n := 56) (.out 0x111767 (movR64M64Effect 0x111767 7 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 57) (.exec 0x111767 (LoadPre 0x111767 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x111767 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111767 7 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.out 0x11176c (atFlags StatusFlags.CF (adcR64R64Effect 0x11176c 10 12)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[10, 12, 54]
    (.letOp (n := 59) (.out 0x11176c (atFlags StatusFlags.CF (adcR64R64Effect 0x11176c 10 12)) (Reg.operands [.gpr 10, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[10, 12, 54]
    (.letOp (n := 60) (.exec 0x11176c (fun s => s.RIP = 0x11176c) (atFlags StatusFlags.CF (adcR64R64Effect 0x11176c 10 12)) (Reg.operands [.gpr 10, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[10, 12, 54]
    (.letOp (n := 61) (.out 0x11176f (atFlags StatusFlags.CF (adcR64R64Effect 0x11176f 0 13)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 0))) #v[0, 13, 59]
    (.letOp (n := 62) (.out 0x11176f (atFlags StatusFlags.CF (adcR64R64Effect 0x11176f 0 13)) (Reg.operands [.gpr 0, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[0, 13, 59]
    (.letOp (n := 63) (.exec 0x11176f (fun s => s.RIP = 0x11176f) (atFlags StatusFlags.CF (adcR64R64Effect 0x11176f 0 13)) (Reg.operands [.gpr 0, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[0, 13, 59]
    (.letOp (n := 64) (.out 0x111772 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x111772 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[2, 62]
    (.letOp (n := 65) (.exec 0x111772 (fun s => s.RIP = 0x111772) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x111772 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2, 62]
    (.terminate (.br ⟨.l117256, RegMap.args [(0, 61), (1, 1), (2, 64), (3, 3), (4, 4), (6, 6), (7, 56), (8, 8), (10, 58), (11, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)] 66⟩))))))))))))))

def bytes_l117244 : List UInt8 :=
  [0x4D, 0x01, 0xFB, 0x48, 0x8B, 0x7C, 0x24, 0x28, 0x4D, 0x11, 0xE2, 0x4C, 0x11, 0xE8, 0x48, 0x83,
    0xD2, 0x00]

theorem code_l117244 : ∀ x ∈ codeRange 0x111764 bytes_l117244, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x11764 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l117256 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x111776 (movR64R64Effect 0x111776 5 6) (EffectPart.reads (.reg (.gpr 5)) [.gpr 6] []) (.reg (.gpr 5))) #v[6]
    (.letOp (n := 54) (.exec 0x111776 (fun s => s.RIP = 0x111776) (movR64R64Effect 0x111776 5 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 55) (.out 0x111779 (subR64R64Effect 0x111779 5 14) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 14] []) (.reg (.gpr 5))) #v[53, 14]
    (.letOp (n := 56) (.exec 0x111779 (fun s => s.RIP = 0x111779) (subR64R64Effect 0x111779 5 14) (Reg.operands [.gpr 5, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 57) (.out 0x11177c (notR64Effect 0x11177c 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[6]
    (.letOp (n := 58) (.exec 0x11177c (fun s => s.RIP = 0x11177c) (notR64Effect 0x11177c 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 59) (.out 0x11177f (movR64R64Effect 0x11177f 15 14) (EffectPart.reads (.reg (.gpr 15)) [.gpr 14] []) (.reg (.gpr 15))) #v[14]
    (.letOp (n := 60) (.exec 0x11177f (fun s => s.RIP = 0x11177f) (movR64R64Effect 0x11177f 15 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 61) (.out 0x111782 (andR64R64Effect 0x111782 15 6) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 6] []) (.reg (.gpr 15))) #v[59, 57]
    (.letOp (n := 62) (.exec 0x111782 (fun s => s.RIP = 0x111782) (andR64R64Effect 0x111782 15 6) (Reg.operands [.gpr 15, .gpr 6] [])) #v[59, 57]
    (.letOp (n := 63) (.out 0x111785 (orR64R64Effect 0x111785 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 14] []) (.reg (.gpr 6))) #v[57, 14]
    (.letOp (n := 64) (.exec 0x111785 (fun s => s.RIP = 0x111785) (orR64R64Effect 0x111785 6 14) (Reg.operands [.gpr 6, .gpr 14] [])) #v[57, 14]
    (.letOp (n := 65) (.out 0x111788 (movR64M64Effect 0x111788 14 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 66) (.exec 0x111788 (LoadPre 0x111788 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x111788 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111788 14 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x11178d (andR64R64Effect 0x11178d 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 5] []) (.reg (.gpr 6))) #v[63, 55]
    (.letOp (n := 68) (.exec 0x11178d (fun s => s.RIP = 0x11178d) (andR64R64Effect 0x11178d 6 5) (Reg.operands [.gpr 6, .gpr 5] [])) #v[63, 55]
    (.letOp (n := 69) (.out 0x111790 (orR64R64Effect 0x111790 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 15] []) (.reg (.gpr 6))) #v[67, 61]
    (.letOp (n := 70) (.exec 0x111790 (fun s => s.RIP = 0x111790) (orR64R64Effect 0x111790 6 15) (Reg.operands [.gpr 6, .gpr 15] [])) #v[67, 61]
    (.letOp (n := 71) (.out 0x111793 (movzxR32M8Effect 0x111793 6 9 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 72) (.exec 0x111793 (LoadPre 0x111793 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x111793 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x111793 6 9 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.exec 0x111799 (StorePre 0x111799 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x111799 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x111799 5 9 (.sib 4 none 0 (.d8 0xf))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[71, 4]
    (.letOp (n := 74) (.out 0x11179e (shrR64Effect 0x11179e 4 6 63) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[69]
    (.letOp (n := 75) (.exec 0x11179e (fun s => s.RIP = 0x11179e) (shrR64Effect 0x11179e 4 6 63) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[69]
    (.letOp (n := 76) (.exec 0x1117a2 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1117a2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1117a2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1117a2 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[74, 4]
    (.terminate (.br ⟨.l117287, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (6, 74), (7, 7), (8, 8), (9, 71), (10, 10), (11, 11), (12, 12), (13, 13), (14, 65), (15, 61), (22, 22), (39, 39), (51, 51)] 77⟩)))))))))))))))))))))))))

def bytes_l117256 : List UInt8 :=
  [0x48, 0x89, 0xF5, 0x4C, 0x29, 0xF5, 0x48, 0xF7, 0xD6, 0x4D, 0x89, 0xF7, 0x49, 0x21, 0xF7, 0x4C,
    0x09, 0xF6, 0x4C, 0x8B, 0x74, 0x24, 0x30, 0x48, 0x21, 0xEE, 0x4C, 0x09, 0xFE, 0x44, 0x0F, 0xB6,
    0x4C, 0x24, 0x38, 0x44, 0x88, 0x4C, 0x24, 0x0F, 0x48, 0xC1, 0xEE, 0x3F, 0x48, 0x89, 0x74, 0x24,
    0x10]

theorem code_l117256 : ∀ x ∈ codeRange 0x111776 bytes_l117256, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x11776 49 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l117287 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1117a7 (fun s => s.RIP = 0x1117a7) (leaR64Effect 0x1117a7 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.out 0x1117ac (xorR32R32Effect 0x1117ac 3 12 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 12] []) (.reg (.gpr 12))) #v[12, 12]
    (.letOp (n := 55) (.exec 0x1117ac (fun s => s.RIP = 0x1117ac) (xorR32R32Effect 0x1117ac 3 12 12) (Reg.operands [.gpr 12, .gpr 12] [])) #v[12, 12]
    (.letOp (n := 56) (.out 0x1117af (subR64M64Effect 0x1117af 12 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 4] []) (.reg (.gpr 12))) #v[54, 4]
    (.letOp (n := 57) (.exec 0x1117af (LoadPre 0x1117af (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1117af + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x1117af 12 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[54, 4]
    (.letOp (n := 58) (.out 0x1117b4 (movR64R64Effect 0x1117b4 15 8) (EffectPart.reads (.reg (.gpr 15)) [.gpr 8] []) (.reg (.gpr 15))) #v[8]
    (.letOp (n := 59) (.exec 0x1117b4 (fun s => s.RIP = 0x1117b4) (movR64R64Effect 0x1117b4 15 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 60) (.out 0x1117b7 (subR64R64Effect 0x1117b7 15 11) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 11] []) (.reg (.gpr 15))) #v[58, 11]
    (.letOp (n := 61) (.exec 0x1117b7 (fun s => s.RIP = 0x1117b7) (subR64R64Effect 0x1117b7 15 11) (Reg.operands [.gpr 15, .gpr 11] [])) #v[58, 11]
    (.letOp (n := 62) (.out 0x1117ba (sarR64Effect 0x1117ba 4 12 63) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[56]
    (.letOp (n := 63) (.exec 0x1117ba (fun s => s.RIP = 0x1117ba) (sarR64Effect 0x1117ba 4 12 63) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[56]
    (.letOp (n := 64) (.out 0x1117be (addR64R64Effect 0x1117be 12 15) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 15] []) (.reg (.gpr 12))) #v[62, 60]
    (.letOp (n := 65) (.exec 0x1117be (fun s => s.RIP = 0x1117be) (addR64R64Effect 0x1117be 12 15) (Reg.operands [.gpr 12, .gpr 15] [])) #v[62, 60]
    (.letOp (n := 66) (.out 0x1117c1 (notR64Effect 0x1117c1 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[8]
    (.letOp (n := 67) (.exec 0x1117c1 (fun s => s.RIP = 0x1117c1) (notR64Effect 0x1117c1 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 68) (.out 0x1117c4 (movR64R64Effect 0x1117c4 15 11) (EffectPart.reads (.reg (.gpr 15)) [.gpr 11] []) (.reg (.gpr 15))) #v[11]
    (.letOp (n := 69) (.exec 0x1117c4 (fun s => s.RIP = 0x1117c4) (movR64R64Effect 0x1117c4 15 11) (Reg.operands [.gpr 11] [])) #v[11]
    (.letOp (n := 70) (.out 0x1117c7 (andR64R64Effect 0x1117c7 15 8) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 8] []) (.reg (.gpr 15))) #v[68, 66]
    (.letOp (n := 71) (.exec 0x1117c7 (fun s => s.RIP = 0x1117c7) (andR64R64Effect 0x1117c7 15 8) (Reg.operands [.gpr 15, .gpr 8] [])) #v[68, 66]
    (.letOp (n := 72) (.out 0x1117ca (orR64R64Effect 0x1117ca 8 11) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 11] []) (.reg (.gpr 8))) #v[66, 11]
    (.letOp (n := 73) (.exec 0x1117ca (fun s => s.RIP = 0x1117ca) (orR64R64Effect 0x1117ca 8 11) (Reg.operands [.gpr 8, .gpr 11] [])) #v[66, 11]
    (.letOp (n := 74) (.out 0x1117cd (andR64R64Effect 0x1117cd 8 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 12] []) (.reg (.gpr 8))) #v[72, 64]
    (.letOp (n := 75) (.exec 0x1117cd (fun s => s.RIP = 0x1117cd) (andR64R64Effect 0x1117cd 8 12) (Reg.operands [.gpr 8, .gpr 12] [])) #v[72, 64]
    (.letOp (n := 76) (.out 0x1117d0 (orR64R64Effect 0x1117d0 8 15) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 15] []) (.reg (.gpr 8))) #v[74, 70]
    (.letOp (n := 77) (.exec 0x1117d0 (fun s => s.RIP = 0x1117d0) (orR64R64Effect 0x1117d0 8 15) (Reg.operands [.gpr 8, .gpr 15] [])) #v[74, 70]
    (.letOp (n := 78) (.out 0x1117d3 (shrR64Effect 0x1117d3 4 8 63) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[76]
    (.letOp (n := 79) (.exec 0x1117d3 (fun s => s.RIP = 0x1117d3) (shrR64Effect 0x1117d3 4 8 63) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[76]
    (.terminate (.br ⟨.l1172b7, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 78), (10, 10), (11, 11), (12, 64), (13, 13), (14, 14), (15, 70), (22, 22), (39, 39), (51, 51)] 80⟩))))))))))))))))))))))))))))

def bytes_l117287 : List UInt8 :=
  [0x48, 0x8D, 0x74, 0x24, 0x10, 0x45, 0x31, 0xE4, 0x4C, 0x2B, 0x64, 0x24, 0x10, 0x4D, 0x89, 0xC7,
    0x4D, 0x29, 0xDF, 0x49, 0xC1, 0xFC, 0x3F, 0x4D, 0x01, 0xFC, 0x49, 0xF7, 0xD0, 0x4D, 0x89, 0xDF,
    0x4D, 0x21, 0xC7, 0x4D, 0x09, 0xD8, 0x4D, 0x21, 0xE0, 0x4D, 0x09, 0xF8, 0x49, 0xC1, 0xE8, 0x3F]

theorem code_l117287 : ∀ x ∈ codeRange 0x1117a7 bytes_l117287, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x117a7 48 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1172b7 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1117d7 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1117d7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1117d7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1117d7 8 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[8, 4]
    (.letOp (n := 54) (.out 0x1117dc (xorR32R32Effect 0x1117dc 3 11 11) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 11] []) (.reg (.gpr 11))) #v[11, 11]
    (.letOp (n := 55) (.exec 0x1117dc (fun s => s.RIP = 0x1117dc) (xorR32R32Effect 0x1117dc 3 11 11) (Reg.operands [.gpr 11, .gpr 11] [])) #v[11, 11]
    (.letOp (n := 56) (.out 0x1117df (subR64M64Effect 0x1117df 11 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 4] []) (.reg (.gpr 11))) #v[54, 4]
    (.letOp (n := 57) (.exec 0x1117df (LoadPre 0x1117df (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1117df + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x1117df 11 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[54, 4]
    (.letOp (n := 58) (.out 0x1117e4 (movR64R64Effect 0x1117e4 8 3) (EffectPart.reads (.reg (.gpr 8)) [.gpr 3] []) (.reg (.gpr 8))) #v[3]
    (.letOp (n := 59) (.exec 0x1117e4 (fun s => s.RIP = 0x1117e4) (movR64R64Effect 0x1117e4 8 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 60) (.out 0x1117e7 (subR64R64Effect 0x1117e7 8 10) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 10] []) (.reg (.gpr 8))) #v[58, 10]
    (.letOp (n := 61) (.exec 0x1117e7 (fun s => s.RIP = 0x1117e7) (subR64R64Effect 0x1117e7 8 10) (Reg.operands [.gpr 8, .gpr 10] [])) #v[58, 10]
    (.letOp (n := 62) (.out 0x1117ea (sarR64Effect 0x1117ea 4 11 63) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[56]
    (.letOp (n := 63) (.exec 0x1117ea (fun s => s.RIP = 0x1117ea) (sarR64Effect 0x1117ea 4 11 63) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[56]
    (.letOp (n := 64) (.out 0x1117ee (addR64R64Effect 0x1117ee 11 8) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 8] []) (.reg (.gpr 11))) #v[62, 60]
    (.letOp (n := 65) (.exec 0x1117ee (fun s => s.RIP = 0x1117ee) (addR64R64Effect 0x1117ee 11 8) (Reg.operands [.gpr 11, .gpr 8] [])) #v[62, 60]
    (.letOp (n := 66) (.out 0x1117f1 (notR64Effect 0x1117f1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[3]
    (.letOp (n := 67) (.exec 0x1117f1 (fun s => s.RIP = 0x1117f1) (notR64Effect 0x1117f1 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 68) (.out 0x1117f4 (movR64R64Effect 0x1117f4 8 10) (EffectPart.reads (.reg (.gpr 8)) [.gpr 10] []) (.reg (.gpr 8))) #v[10]
    (.letOp (n := 69) (.exec 0x1117f4 (fun s => s.RIP = 0x1117f4) (movR64R64Effect 0x1117f4 8 10) (Reg.operands [.gpr 10] [])) #v[10]
    (.letOp (n := 70) (.out 0x1117f7 (andR64R64Effect 0x1117f7 8 3) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 3] []) (.reg (.gpr 8))) #v[68, 66]
    (.letOp (n := 71) (.exec 0x1117f7 (fun s => s.RIP = 0x1117f7) (andR64R64Effect 0x1117f7 8 3) (Reg.operands [.gpr 8, .gpr 3] [])) #v[68, 66]
    (.letOp (n := 72) (.out 0x1117fa (orR64R64Effect 0x1117fa 3 10) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 10] []) (.reg (.gpr 3))) #v[66, 10]
    (.letOp (n := 73) (.exec 0x1117fa (fun s => s.RIP = 0x1117fa) (orR64R64Effect 0x1117fa 3 10) (Reg.operands [.gpr 3, .gpr 10] [])) #v[66, 10]
    (.letOp (n := 74) (.out 0x1117fd (andR64R64Effect 0x1117fd 3 11) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 11] []) (.reg (.gpr 3))) #v[72, 64]
    (.letOp (n := 75) (.exec 0x1117fd (fun s => s.RIP = 0x1117fd) (andR64R64Effect 0x1117fd 3 11) (Reg.operands [.gpr 3, .gpr 11] [])) #v[72, 64]
    (.letOp (n := 76) (.out 0x111800 (orR64R64Effect 0x111800 3 8) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 8] []) (.reg (.gpr 3))) #v[74, 70]
    (.letOp (n := 77) (.exec 0x111800 (fun s => s.RIP = 0x111800) (orR64R64Effect 0x111800 3 8) (Reg.operands [.gpr 3, .gpr 8] [])) #v[74, 70]
    (.letOp (n := 78) (.out 0x111803 (shrR64Effect 0x111803 4 3 63) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[76]
    (.letOp (n := 79) (.exec 0x111803 (fun s => s.RIP = 0x111803) (shrR64Effect 0x111803 4 3 63) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[76]
    (.terminate (.br ⟨.l1172e7, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 78), (4, 4), (5, 5), (7, 7), (8, 70), (10, 10), (11, 64), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (51, 51)] 80⟩))))))))))))))))))))))))))))

def bytes_l1172b7 : List UInt8 :=
  [0x4C, 0x89, 0x44, 0x24, 0x10, 0x45, 0x31, 0xDB, 0x4C, 0x2B, 0x5C, 0x24, 0x10, 0x49, 0x89, 0xD8,
    0x4D, 0x29, 0xD0, 0x49, 0xC1, 0xFB, 0x3F, 0x4D, 0x01, 0xC3, 0x48, 0xF7, 0xD3, 0x4D, 0x89, 0xD0,
    0x49, 0x21, 0xD8, 0x4C, 0x09, 0xD3, 0x4C, 0x21, 0xDB, 0x4C, 0x09, 0xC3, 0x48, 0xC1, 0xEB, 0x3F]

theorem code_l1172b7 : ∀ x ∈ codeRange 0x1117d7 bytes_l1172b7, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x117d7 48 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1172e7 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x111807 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111807 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x111807 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x111807 3 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[3, 4]
    (.letOp (n := 54) (.out 0x11180c (xorR32R32Effect 0x11180c 3 13 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 13] []) (.reg (.gpr 13))) #v[13, 13]
    (.letOp (n := 55) (.exec 0x11180c (fun s => s.RIP = 0x11180c) (xorR32R32Effect 0x11180c 3 13 13) (Reg.operands [.gpr 13, .gpr 13] [])) #v[13, 13]
    (.letOp (n := 56) (.out 0x11180f (subR64M64Effect 0x11180f 13 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 4] []) (.reg (.gpr 13))) #v[54, 4]
    (.letOp (n := 57) (.exec 0x11180f (LoadPre 0x11180f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11180f + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x11180f 13 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[54, 4]
    (.letOp (n := 58) (.out 0x111814 (movR64R64Effect 0x111814 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 7] []) (.reg (.gpr 8))) #v[7]
    (.letOp (n := 59) (.exec 0x111814 (fun s => s.RIP = 0x111814) (movR64R64Effect 0x111814 8 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 60) (.out 0x111817 (subR64R64Effect 0x111817 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[58, 0]
    (.letOp (n := 61) (.exec 0x111817 (fun s => s.RIP = 0x111817) (subR64R64Effect 0x111817 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[58, 0]
    (.letOp (n := 62) (.out 0x11181a (sarR64Effect 0x11181a 4 13 63) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[56]
    (.letOp (n := 63) (.exec 0x11181a (fun s => s.RIP = 0x11181a) (sarR64Effect 0x11181a 4 13 63) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[56]
    (.letOp (n := 64) (.out 0x11181e (addR64R64Effect 0x11181e 13 8) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 8] []) (.reg (.gpr 13))) #v[62, 60]
    (.letOp (n := 65) (.exec 0x11181e (fun s => s.RIP = 0x11181e) (addR64R64Effect 0x11181e 13 8) (Reg.operands [.gpr 13, .gpr 8] [])) #v[62, 60]
    (.letOp (n := 66) (.out 0x111821 (notR64Effect 0x111821 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[7]
    (.letOp (n := 67) (.exec 0x111821 (fun s => s.RIP = 0x111821) (notR64Effect 0x111821 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 68) (.out 0x111824 (movR64R64Effect 0x111824 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[0]
    (.letOp (n := 69) (.exec 0x111824 (fun s => s.RIP = 0x111824) (movR64R64Effect 0x111824 8 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 70) (.out 0x111827 (andR64R64Effect 0x111827 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 7] []) (.reg (.gpr 8))) #v[68, 66]
    (.letOp (n := 71) (.exec 0x111827 (fun s => s.RIP = 0x111827) (andR64R64Effect 0x111827 8 7) (Reg.operands [.gpr 8, .gpr 7] [])) #v[68, 66]
    (.letOp (n := 72) (.out 0x11182a (orR64R64Effect 0x11182a 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[66, 0]
    (.letOp (n := 73) (.exec 0x11182a (fun s => s.RIP = 0x11182a) (orR64R64Effect 0x11182a 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[66, 0]
    (.letOp (n := 74) (.out 0x11182d (xorR32R32Effect 0x11182d 3 10 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 10] []) (.reg (.gpr 10))) #v[10, 10]
    (.letOp (n := 75) (.exec 0x11182d (fun s => s.RIP = 0x11182d) (xorR32R32Effect 0x11182d 3 10 10) (Reg.operands [.gpr 10, .gpr 10] [])) #v[10, 10]
    (.letOp (n := 76) (.out 0x111830 (andR64R64Effect 0x111830 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 13] []) (.reg (.gpr 7))) #v[72, 64]
    (.letOp (n := 77) (.exec 0x111830 (fun s => s.RIP = 0x111830) (andR64R64Effect 0x111830 7 13) (Reg.operands [.gpr 7, .gpr 13] [])) #v[72, 64]
    (.letOp (n := 78) (.out 0x111833 (orR64R64Effect 0x111833 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 8] []) (.reg (.gpr 7))) #v[76, 70]
    (.letOp (n := 79) (.exec 0x111833 (fun s => s.RIP = 0x111833) (orR64R64Effect 0x111833 7 8) (Reg.operands [.gpr 7, .gpr 8] [])) #v[76, 70]
    (.letOp (n := 80) (.out 0x111836 (shrR64Effect 0x111836 4 7 63) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[78]
    (.letOp (n := 81) (.exec 0x111836 (fun s => s.RIP = 0x111836) (shrR64Effect 0x111836 4 7 63) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[78]
    (.terminate (.br ⟨.l11731a, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 80), (8, 70), (10, 74), (11, 11), (12, 12), (13, 64), (14, 14), (22, 22), (39, 39), (51, 51)] 82⟩))))))))))))))))))))))))))))))

def bytes_l1172e7 : List UInt8 :=
  [0x48, 0x89, 0x5C, 0x24, 0x10, 0x45, 0x31, 0xED, 0x4C, 0x2B, 0x6C, 0x24, 0x10, 0x49, 0x89, 0xF8,
    0x49, 0x29, 0xC0, 0x49, 0xC1, 0xFD, 0x3F, 0x4D, 0x01, 0xC5, 0x48, 0xF7, 0xD7, 0x49, 0x89, 0xC0,
    0x49, 0x21, 0xF8, 0x48, 0x09, 0xC7, 0x45, 0x31, 0xD2, 0x4C, 0x21, 0xEF, 0x4C, 0x09, 0xC7, 0x48,
    0xC1, 0xEF, 0x3F]

theorem code_l1172e7 : ∀ x ∈ codeRange 0x111807 bytes_l1172e7, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x11807 51 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11731a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x11183a (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x11183a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11183a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11183a 7 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[7, 4]
    (.letOp (n := 54) (.out 0x11183f (xorR32R32Effect 0x11183f 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[0, 0]
    (.letOp (n := 55) (.exec 0x11183f (fun s => s.RIP = 0x11183f) (xorR32R32Effect 0x11183f 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.letOp (n := 56) (.out 0x111841 (subR64M64Effect 0x111841 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[54, 4]
    (.letOp (n := 57) (.exec 0x111841 (LoadPre 0x111841 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x111841 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x111841 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[54, 4]
    (.letOp (n := 58) (.out 0x111846 (movR64R64Effect 0x111846 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 59) (.exec 0x111846 (fun s => s.RIP = 0x111846) (movR64R64Effect 0x111846 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 60) (.out 0x111849 (subR64R64Effect 0x111849 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[58, 2]
    (.letOp (n := 61) (.exec 0x111849 (fun s => s.RIP = 0x111849) (subR64R64Effect 0x111849 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[58, 2]
    (.letOp (n := 62) (.out 0x11184c (notR64Effect 0x11184c 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14] []) (.reg (.gpr 14))) #v[14]
    (.letOp (n := 63) (.exec 0x11184c (fun s => s.RIP = 0x11184c) (notR64Effect 0x11184c 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 64) (.out 0x11184f (movR64R64Effect 0x11184f 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[2]
    (.letOp (n := 65) (.exec 0x11184f (fun s => s.RIP = 0x11184f) (movR64R64Effect 0x11184f 7 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 66) (.out 0x111852 (andR64R64Effect 0x111852 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 14] []) (.reg (.gpr 7))) #v[64, 62]
    (.letOp (n := 67) (.exec 0x111852 (fun s => s.RIP = 0x111852) (andR64R64Effect 0x111852 7 14) (Reg.operands [.gpr 7, .gpr 14] [])) #v[64, 62]
    (.letOp (n := 68) (.out 0x111855 (orR64R64Effect 0x111855 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 2] []) (.reg (.gpr 14))) #v[62, 2]
    (.letOp (n := 69) (.exec 0x111855 (fun s => s.RIP = 0x111855) (orR64R64Effect 0x111855 14 2) (Reg.operands [.gpr 14, .gpr 2] [])) #v[62, 2]
    (.letOp (n := 70) (.out 0x111858 (sarR64Effect 0x111858 4 0 63) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[56]
    (.letOp (n := 71) (.exec 0x111858 (fun s => s.RIP = 0x111858) (sarR64Effect 0x111858 4 0 63) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[56]
    (.letOp (n := 72) (.out 0x11185c (addR64R64Effect 0x11185c 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[70, 60]
    (.letOp (n := 73) (.exec 0x11185c (fun s => s.RIP = 0x11185c) (addR64R64Effect 0x11185c 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[70, 60]
    (.letOp (n := 74) (.out 0x11185f (andR64R64Effect 0x11185f 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 0] []) (.reg (.gpr 14))) #v[68, 72]
    (.letOp (n := 75) (.exec 0x11185f (fun s => s.RIP = 0x11185f) (andR64R64Effect 0x11185f 14 0) (Reg.operands [.gpr 14, .gpr 0] [])) #v[68, 72]
    (.letOp (n := 76) (.out 0x111862 (orR64R64Effect 0x111862 14 7) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 7] []) (.reg (.gpr 14))) #v[74, 66]
    (.letOp (n := 77) (.exec 0x111862 (fun s => s.RIP = 0x111862) (orR64R64Effect 0x111862 14 7) (Reg.operands [.gpr 14, .gpr 7] [])) #v[74, 66]
    (.letOp (n := 78) (.out 0x111865 (shrR64Effect 0x111865 4 14 63) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[76]
    (.letOp (n := 79) (.exec 0x111865 (fun s => s.RIP = 0x111865) (shrR64Effect 0x111865 4 14 63) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[76]
    (.letOp (n := 80) (.exec 0x111869 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111869 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x111869 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x111869 14 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[78, 4]
    (.terminate (.br ⟨.l11734e, RegMap.args [(0, 72), (1, 1), (2, 2), (4, 4), (5, 5), (6, 60), (7, 66), (10, 10), (11, 11), (12, 12), (13, 13), (14, 78), (22, 22), (39, 39), (51, 51)] 81⟩)))))))))))))))))))))))))))))

def bytes_l11731a : List UInt8 :=
  [0x48, 0x89, 0x7C, 0x24, 0x10, 0x31, 0xC0, 0x48, 0x2B, 0x44, 0x24, 0x10, 0x4C, 0x89, 0xF6, 0x48,
    0x29, 0xD6, 0x49, 0xF7, 0xD6, 0x48, 0x89, 0xD7, 0x4C, 0x21, 0xF7, 0x49, 0x09, 0xD6, 0x48, 0xC1,
    0xF8, 0x3F, 0x48, 0x01, 0xF0, 0x49, 0x21, 0xC6, 0x49, 0x09, 0xFE, 0x49, 0xC1, 0xEE, 0x3F, 0x4C,
    0x89, 0x74, 0x24, 0x10]

theorem code_l11731a : ∀ x ∈ codeRange 0x11183a bytes_l11731a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1183a 52 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11734e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x11186e (fun s => s.RIP = 0x11186e) (leaR64Effect 0x11186e 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.exec 0x111873 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111873 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x111873 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x111873 5 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[5, 4]
    (.letOp (n := 55) (.out 0x111878 (movR64R64Effect 0x111878 3 5) (EffectPart.reads (.reg (.gpr 3)) [.gpr 5] []) (.reg (.gpr 3))) #v[5]
    (.letOp (n := 56) (.exec 0x111878 (fun s => s.RIP = 0x111878) (movR64R64Effect 0x111878 3 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 57) (.out 0x11187b (negR64Effect 0x11187b 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[55]
    (.letOp (n := 58) (.out 0x11187b (negR64Effect 0x11187b 3) (EffectPart.reads (.flag .CF) [.gpr 3] []) (.flag .CF)) #v[55]
    (.letOp (n := 59) (.exec 0x11187b (fun s => s.RIP = 0x11187b) (negR64Effect 0x11187b 3) (Reg.operands [.gpr 3] [])) #v[55]
    (.letOp (n := 60) (.out 0x11187e (movR32Imm32Effect 0x11187e 6 8 0x0) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 61) (.exec 0x11187e (fun s => s.RIP = 0x11187e) (movR32Imm32Effect 0x11187e 6 8 0x0) (Reg.operands [] [])) #v[]
    (.letOp (n := 62) (.out 0x111884 (atFlags StatusFlags.CF (sbbR64R64Effect 0x111884 8 12)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[60, 12, 58]
    (.letOp (n := 63) (.out 0x111884 (atFlags StatusFlags.CF (sbbR64R64Effect 0x111884 8 12)) (Reg.operands [.gpr 8, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[60, 12, 58]
    (.letOp (n := 64) (.exec 0x111884 (fun s => s.RIP = 0x111884) (atFlags StatusFlags.CF (sbbR64R64Effect 0x111884 8 12)) (Reg.operands [.gpr 8, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[60, 12, 58]
    (.letOp (n := 65) (.out 0x111887 (movR32Imm32Effect 0x111887 5 5 0x0) (EffectPart.reads (.reg (.gpr 5)) [] []) (.reg (.gpr 5))) #v[]
    (.letOp (n := 66) (.exec 0x111887 (fun s => s.RIP = 0x111887) (movR32Imm32Effect 0x111887 5 5 0x0) (Reg.operands [] [])) #v[]
    (.letOp (n := 67) (.out 0x11188c (atFlags StatusFlags.CF (sbbR64R64Effect 0x11188c 5 11)) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 5))) #v[65, 11, 63]
    (.letOp (n := 68) (.out 0x11188c (atFlags StatusFlags.CF (sbbR64R64Effect 0x11188c 5 11)) (Reg.operands [.gpr 5, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[65, 11, 63]
    (.letOp (n := 69) (.exec 0x11188c (fun s => s.RIP = 0x11188c) (atFlags StatusFlags.CF (sbbR64R64Effect 0x11188c 5 11)) (Reg.operands [.gpr 5, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[65, 11, 63]
    (.letOp (n := 70) (.out 0x11188f (atFlags StatusFlags.CF (sbbR64R64Effect 0x11188f 10 13)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[10, 13, 68]
    (.letOp (n := 71) (.out 0x11188f (atFlags StatusFlags.CF (sbbR64R64Effect 0x11188f 10 13)) (Reg.operands [.gpr 10, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[10, 13, 68]
    (.letOp (n := 72) (.exec 0x11188f (fun s => s.RIP = 0x11188f) (atFlags StatusFlags.CF (sbbR64R64Effect 0x11188f 10 13)) (Reg.operands [.gpr 10, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[10, 13, 68]
    (.letOp (n := 73) (.out 0x111892 (movR64M64Effect 0x111892 2 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 74) (.exec 0x111892 (LoadPre 0x111892 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x111892 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111892 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.exec 0x111897 (StorePre 0x111897 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x111897 + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 3) (setccM8Effect 0x111897 5 (.sib 4 none 0 (.d8 0x10)))) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[4, 71]
    (.letOp (n := 76) (.out 0x11189c (testR64R64Effect 0x11189c 2 2) (EffectPart.reads (.flag .ZF) [.gpr 2, .gpr 2] []) (.flag .ZF)) #v[73, 73]
    (.letOp (n := 77) (.exec 0x11189c (fun s => s.RIP = 0x11189c) (testR64R64Effect 0x11189c 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[73, 73]
    (.letOp (n := 78) (.exec 0x11189f (fun s => s.RIP = 0x11189f) (leaR64Effect 0x11189f 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.out 0x1118a4 (movzxR32M8Effect 0x1118a4 5 6 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 80) (.exec 0x1118a4 (LoadPre 0x1118a4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1118a4 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1118a4 5 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 81) (.exec 0x1118a9 (StorePre 0x1118a9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1118a9 + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 5) (setccM8Effect 0x1118a9 5 (.sib 4 none 0 (.d8 0x10)))) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.ZF])) #v[4, 76]
    (.letOp (n := 82) (.exec 0x1118ae (fun s => s.RIP = 0x1118ae) (leaR64Effect 0x1118ae 7 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.br ⟨.l117393, RegMap.args [(0, 0), (1, 1), (3, 57), (4, 4), (5, 67), (6, 79), (8, 62), (10, 70), (11, 11), (12, 12), (13, 13), (19, 76), (22, 22), (39, 39), (51, 51)] 83⟩)))))))))))))))))))))))))))))))

def bytes_l11734e : List UInt8 :=
  [0x48, 0x8D, 0x54, 0x24, 0x10, 0x48, 0x89, 0x6C, 0x24, 0x48, 0x48, 0x89, 0xEB, 0x48, 0xF7, 0xDB,
    0x41, 0xB8, 0x00, 0x00, 0x00, 0x00, 0x4D, 0x19, 0xE0, 0xBD, 0x00, 0x00, 0x00, 0x00, 0x4C, 0x19,
    0xDD, 0x4D, 0x19, 0xEA, 0x48, 0x8B, 0x54, 0x24, 0x10, 0x0F, 0x93, 0x44, 0x24, 0x10, 0x48, 0x85,
    0xD2, 0x48, 0x8D, 0x54, 0x24, 0x10, 0x0F, 0xB6, 0x74, 0x24, 0x10, 0x0F, 0x95, 0x44, 0x24, 0x10,
    0x48, 0x8D, 0x7C, 0x24, 0x10]

theorem code_l11734e : ∀ x ∈ codeRange 0x11186e bytes_l11734e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1186e 69 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l117393 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1118b3 (movzxR32M8Effect 0x1118b3 5 2 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 54) (.exec 0x1118b3 (LoadPre 0x1118b3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1118b3 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1118b3 5 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x1118b8 (StorePre 0x1118b8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1118b8 + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 5) (setccM8Effect 0x1118b8 5 (.sib 4 none 0 (.d8 0x10)))) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.ZF])) #v[4, 19]
    (.letOp (n := 56) (.out 0x1118bd (movzxR32M8Effect 0x1118bd 6 15 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 57) (.exec 0x1118bd (LoadPre 0x1118bd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1118bd + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1118bd 6 15 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x1118c3 (StorePre 0x1118c3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1118c3 + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 5) (setccM8Effect 0x1118c3 5 (.sib 4 none 0 (.d8 0x10)))) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.ZF])) #v[4, 19]
    (.letOp (n := 59) (.out 0x1118c8 (movzxR32M8Effect 0x1118c8 6 14 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 60) (.exec 0x1118c8 (LoadPre 0x1118c8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1118c8 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1118c8 6 14 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x1118ce (StorePre 0x1118ce 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1118ce + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 5) (setccM8Effect 0x1118ce 5 (.sib 4 none 0 (.d8 0x10)))) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.ZF])) #v[4, 19]
    (.letOp (n := 62) (.out 0x1118d3 (movzxR32M8Effect 0x1118d3 5 7 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 63) (.exec 0x1118d3 (LoadPre 0x1118d3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1118d3 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1118d3 5 7 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x1118d8 (StorePre 0x1118d8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1118d8 + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 5) (setccM8Effect 0x1118d8 5 (.sib 4 none 0 (.d8 0x10)))) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.ZF])) #v[4, 19]
    (.letOp (n := 65) (.out 0x1118dd (leaR64Effect 0x1118dd 9 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 66) (.exec 0x1118dd (fun s => s.RIP = 0x1118dd) (leaR64Effect 0x1118dd 9 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x1118e2 (atFlags (condHolds 5) (setccR8Effect 0x1118e2 4 9)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 9))) #v[65, 19]
    (.letOp (n := 68) (.exec 0x1118e2 (fun s => s.RIP = 0x1118e2) (atFlags (condHolds 5) (setccR8Effect 0x1118e2 4 9)) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[65, 19]
    (.letOp (n := 69) (.out 0x1118e6 (cmpMImm8Effect 0x1118e6 5 32 (.sib 4 none 0 (.d8 0x44)) 0x40) (EffectPart.reads (.flag .CF) [.gpr 4] []) (.flag .CF)) #v[4]
    (.letOp (n := 70) (.exec 0x1118e6 (LoadPre 0x1118e6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x1118e6 + BitVec.ofNat 64 5)) 4) (cmpMImm8Effect 0x1118e6 5 32 (.sib 4 none 0 (.d8 0x44)) 0x40) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.pure (condOp 3)) #v[69]
    (.terminate (.condBr (Fin.last 71) ⟨.l117619, RegMap.args [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 62), (8, 8), (9, 67), (10, 10), (11, 11), (12, 12), (13, 13), (14, 59), (15, 56), (16, 69), (22, 22), (39, 39), (51, 51)] 72⟩ ⟨.l1173d1, RegMap.args [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 62), (8, 8), (9, 67), (10, 10), (11, 11), (12, 12), (13, 13), (14, 59), (15, 56), (16, 69), (22, 22), (39, 39), (51, 51)] 72⟩))))))))))))))))))))

def bytes_l117393 : List UInt8 :=
  [0x0F, 0xB6, 0x54, 0x24, 0x10, 0x0F, 0x95, 0x44, 0x24, 0x10, 0x44, 0x0F, 0xB6, 0x7C, 0x24, 0x10,
    0x0F, 0x95, 0x44, 0x24, 0x10, 0x44, 0x0F, 0xB6, 0x74, 0x24, 0x10, 0x0F, 0x95, 0x44, 0x24, 0x10,
    0x0F, 0xB6, 0x7C, 0x24, 0x10, 0x0F, 0x95, 0x44, 0x24, 0x10, 0x4C, 0x8D, 0x4C, 0x24, 0x10, 0x41,
    0x0F, 0x95, 0xC1, 0x83, 0x7C, 0x24, 0x44, 0x40, 0x0F, 0x83, 0x48, 0x02, 0x00, 0x00]

theorem code_l117393 : ∀ x ∈ codeRange 0x1118b3 bytes_l117393, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x118b3 62 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1173d1 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1118f1 (StorePre 0x1118f1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x1118f1 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1118f1 5 9 (.sib 4 none 0 (.d8 0xe))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[9, 4]
    (.letOp (n := 54) (.out 0x1118f6 (cmpMImm8Effect 0x1118f6 5 32 (.sib 4 none 0 (.d8 0x44)) 0x0) (EffectPart.reads (.flag .ZF) [.gpr 4] []) (.flag .ZF)) #v[4]
    (.letOp (n := 55) (.exec 0x1118f6 (LoadPre 0x1118f6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x1118f6 + BitVec.ofNat 64 5)) 4) (cmpMImm8Effect 0x1118f6 5 32 (.sib 4 none 0 (.d8 0x44)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.pure (condOp 4)) #v[54]
    (.terminate (.condBr (Fin.last 56) ⟨.l117631, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 54), (22, 22), (39, 39), (51, 51)] 57⟩ ⟨.l1173e1, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 54), (22, 22), (39, 39), (51, 51)] 57⟩)))))

def bytes_l1173d1 : List UInt8 :=
  [0x44, 0x88, 0x4C, 0x24, 0x0E, 0x83, 0x7C, 0x24, 0x44, 0x00, 0x0F, 0x84, 0x50, 0x02, 0x00, 0x00]

theorem code_l1173d1 : ∀ x ∈ codeRange 0x1118f1 bytes_l1173d1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x118f1 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1173e1 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x111901 (xorR64R64Effect 0x111901 10 13) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 13] []) (.reg (.gpr 10))) #v[10, 13]
    (.letOp (n := 54) (.exec 0x111901 (fun s => s.RIP = 0x111901) (xorR64R64Effect 0x111901 10 13) (Reg.operands [.gpr 10, .gpr 13] [])) #v[10, 13]
    (.letOp (n := 55) (.out 0x111904 (negR64Effect 0x111904 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[7]
    (.letOp (n := 56) (.exec 0x111904 (fun s => s.RIP = 0x111904) (negR64Effect 0x111904 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 57) (.out 0x111907 (andR64R64Effect 0x111907 7 10) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 10] []) (.reg (.gpr 7))) #v[55, 53]
    (.letOp (n := 58) (.exec 0x111907 (fun s => s.RIP = 0x111907) (andR64R64Effect 0x111907 7 10) (Reg.operands [.gpr 7, .gpr 10] [])) #v[55, 53]
    (.letOp (n := 59) (.out 0x11190a (xorR64R64Effect 0x11190a 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 13] []) (.reg (.gpr 7))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x11190a (fun s => s.RIP = 0x11190a) (xorR64R64Effect 0x11190a 7 13) (Reg.operands [.gpr 7, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x11190d (xorR64R64Effect 0x11190d 5 11) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 11] []) (.reg (.gpr 5))) #v[5, 11]
    (.letOp (n := 62) (.exec 0x11190d (fun s => s.RIP = 0x11190d) (xorR64R64Effect 0x11190d 5 11) (Reg.operands [.gpr 5, .gpr 11] [])) #v[5, 11]
    (.letOp (n := 63) (.out 0x111910 (negR64Effect 0x111910 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14] []) (.reg (.gpr 14))) #v[14]
    (.letOp (n := 64) (.exec 0x111910 (fun s => s.RIP = 0x111910) (negR64Effect 0x111910 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 65) (.out 0x111913 (andR64R64Effect 0x111913 14 5) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 5] []) (.reg (.gpr 14))) #v[63, 61]
    (.letOp (n := 66) (.exec 0x111913 (fun s => s.RIP = 0x111913) (andR64R64Effect 0x111913 14 5) (Reg.operands [.gpr 14, .gpr 5] [])) #v[63, 61]
    (.letOp (n := 67) (.out 0x111916 (xorR64R64Effect 0x111916 14 11) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 11] []) (.reg (.gpr 14))) #v[65, 11]
    (.letOp (n := 68) (.exec 0x111916 (fun s => s.RIP = 0x111916) (xorR64R64Effect 0x111916 14 11) (Reg.operands [.gpr 14, .gpr 11] [])) #v[65, 11]
    (.letOp (n := 69) (.out 0x111919 (xorR64R64Effect 0x111919 8 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 12] []) (.reg (.gpr 8))) #v[8, 12]
    (.letOp (n := 70) (.exec 0x111919 (fun s => s.RIP = 0x111919) (xorR64R64Effect 0x111919 8 12) (Reg.operands [.gpr 8, .gpr 12] [])) #v[8, 12]
    (.letOp (n := 71) (.out 0x11191c (negR64Effect 0x11191c 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15] []) (.reg (.gpr 15))) #v[15]
    (.letOp (n := 72) (.exec 0x11191c (fun s => s.RIP = 0x11191c) (negR64Effect 0x11191c 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 73) (.out 0x11191f (andR64R64Effect 0x11191f 15 8) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 8] []) (.reg (.gpr 15))) #v[71, 69]
    (.letOp (n := 74) (.exec 0x11191f (fun s => s.RIP = 0x11191f) (andR64R64Effect 0x11191f 15 8) (Reg.operands [.gpr 15, .gpr 8] [])) #v[71, 69]
    (.letOp (n := 75) (.out 0x111922 (xorR64R64Effect 0x111922 15 12) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 12] []) (.reg (.gpr 15))) #v[73, 12]
    (.letOp (n := 76) (.exec 0x111922 (fun s => s.RIP = 0x111922) (xorR64R64Effect 0x111922 15 12) (Reg.operands [.gpr 15, .gpr 12] [])) #v[73, 12]
    (.terminate (.br ⟨.l117405, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 61), (6, 6), (7, 59), (8, 69), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 67), (15, 75), (22, 22), (39, 39), (51, 51)] 77⟩)))))))))))))))))))))))))

def bytes_l1173e1 : List UInt8 :=
  [0x4D, 0x31, 0xEA, 0x48, 0xF7, 0xDF, 0x4C, 0x21, 0xD7, 0x4C, 0x31, 0xEF, 0x4C, 0x31, 0xDD, 0x49,
    0xF7, 0xDE, 0x49, 0x21, 0xEE, 0x4D, 0x31, 0xDE, 0x4D, 0x31, 0xE0, 0x49, 0xF7, 0xDF, 0x4D, 0x21,
    0xC7, 0x4D, 0x31, 0xE7]

theorem code_l1173e1 : ∀ x ∈ codeRange 0x111901 bytes_l1173e1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x11901 36 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l117405 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x111925 (andR32Imm8Effect 0x111925 3 6 0x1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[6]
    (.letOp (n := 54) (.exec 0x111925 (fun s => s.RIP = 0x111925) (andR32Imm8Effect 0x111925 3 6 0x1) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 55) (.out 0x111928 (movR64R64Effect 0x111928 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[0]
    (.letOp (n := 56) (.exec 0x111928 (fun s => s.RIP = 0x111928) (movR64R64Effect 0x111928 8 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 57) (.out 0x11192b (notR64Effect 0x11192b 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[55]
    (.letOp (n := 58) (.exec 0x11192b (fun s => s.RIP = 0x11192b) (notR64Effect 0x11192b 8) (Reg.operands [.gpr 8] [])) #v[55]
    (.letOp (n := 59) (.out 0x11192e (addR64R64Effect 0x11192e 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6] []) (.reg (.gpr 8))) #v[57, 53]
    (.letOp (n := 60) (.exec 0x11192e (fun s => s.RIP = 0x11192e) (addR64R64Effect 0x11192e 8 6) (Reg.operands [.gpr 8, .gpr 6] [])) #v[57, 53]
    (.letOp (n := 61) (.out 0x111931 (xorR64R64Effect 0x111931 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[59, 0]
    (.letOp (n := 62) (.exec 0x111931 (fun s => s.RIP = 0x111931) (xorR64R64Effect 0x111931 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[59, 0]
    (.letOp (n := 63) (.out 0x111934 (movzxR32M8Effect 0x111934 6 13 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 64) (.exec 0x111934 (LoadPre 0x111934 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x111934 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x111934 6 13 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x11193a (negR64Effect 0x11193a 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[63]
    (.letOp (n := 66) (.exec 0x11193a (fun s => s.RIP = 0x11193a) (negR64Effect 0x11193a 13) (Reg.operands [.gpr 13] [])) #v[63]
    (.letOp (n := 67) (.out 0x11193d (andR64R64Effect 0x11193d 13 8) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 8] []) (.reg (.gpr 13))) #v[65, 61]
    (.letOp (n := 68) (.exec 0x11193d (fun s => s.RIP = 0x11193d) (andR64R64Effect 0x11193d 13 8) (Reg.operands [.gpr 13, .gpr 8] [])) #v[65, 61]
    (.letOp (n := 69) (.out 0x111940 (xorR64R64Effect 0x111940 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 0] []) (.reg (.gpr 13))) #v[67, 0]
    (.letOp (n := 70) (.exec 0x111940 (fun s => s.RIP = 0x111940) (xorR64R64Effect 0x111940 13 0) (Reg.operands [.gpr 13, .gpr 0] [])) #v[67, 0]
    (.terminate (.br ⟨.l117423, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 53), (7, 7), (8, 61), (9, 9), (13, 69), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)] 71⟩)))))))))))))))))))

def bytes_l117405 : List UInt8 :=
  [0x83, 0xE6, 0x01, 0x49, 0x89, 0xC0, 0x49, 0xF7, 0xD0, 0x49, 0x01, 0xF0, 0x49, 0x31, 0xC0, 0x44,
    0x0F, 0xB6, 0x6C, 0x24, 0x10, 0x49, 0xF7, 0xDD, 0x4D, 0x21, 0xC5, 0x49, 0x31, 0xC5]

theorem code_l117405 : ∀ x ∈ codeRange 0x111925 bytes_l117405, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x11925 30 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l117423 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x111943 (movR32R32Effect 0x111943 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[1]
    (.letOp (n := 54) (.exec 0x111943 (fun s => s.RIP = 0x111943) (movR32R32Effect 0x111943 2 0 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 55) (.out 0x111945 (movR64R64Effect 0x111945 10 13) (EffectPart.reads (.reg (.gpr 10)) [.gpr 13] []) (.reg (.gpr 10))) #v[13]
    (.letOp (n := 56) (.exec 0x111945 (fun s => s.RIP = 0x111945) (movR64R64Effect 0x111945 10 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 57) (.out 0x111948 (movR32R32Effect 0x111948 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 58) (.exec 0x111948 (fun s => s.RIP = 0x111948) (movR32R32Effect 0x111948 2 1 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 59) (.out 0x11194a (shlR64ClEffect 0x11194a 3 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[55, 57]
    (.letOp (n := 60) (.exec 0x11194a (fun s => s.RIP = 0x11194a) (shlR64ClEffect 0x11194a 3 10) (Reg.operands [.gpr 10, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[55, 57]
    (.letOp (n := 61) (.out 0x11194d (movR64M64Effect 0x11194d 6 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 62) (.exec 0x11194d (LoadPre 0x11194d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x11194d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11194d 6 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x111952 (xorR64R64Effect 0x111952 3 6) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 6] []) (.reg (.gpr 3))) #v[3, 61]
    (.letOp (n := 64) (.exec 0x111952 (fun s => s.RIP = 0x111952) (xorR64R64Effect 0x111952 3 6) (Reg.operands [.gpr 3, .gpr 6] [])) #v[3, 61]
    (.letOp (n := 65) (.out 0x111955 (negR64Effect 0x111955 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[2]
    (.letOp (n := 66) (.exec 0x111955 (fun s => s.RIP = 0x111955) (negR64Effect 0x111955 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 67) (.out 0x111958 (movR64R64Effect 0x111958 11 7) (EffectPart.reads (.reg (.gpr 11)) [.gpr 7] []) (.reg (.gpr 11))) #v[7]
    (.letOp (n := 68) (.exec 0x111958 (fun s => s.RIP = 0x111958) (movR64R64Effect 0x111958 11 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 69) (.out 0x11195b (movR32M32LowEffect 0x11195b 5 (.sib 4 none 0 (.d8 0x44))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 70) (.exec 0x11195b (LoadPre 0x11195b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x11195b + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x11195b 5 (.sib 4 none 0 (.d8 0x44))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.out 0x11195f (movR32R32Effect 0x11195f 2 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[69]
    (.letOp (n := 72) (.exec 0x11195f (fun s => s.RIP = 0x11195f) (movR32R32Effect 0x11195f 2 1 5) (Reg.operands [.gpr 5] [])) #v[69]
    (.letOp (n := 73) (.out 0x111961 (shrR64ClEffect 0x111961 3 11) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[67, 71]
    (.letOp (n := 74) (.exec 0x111961 (fun s => s.RIP = 0x111961) (shrR64ClEffect 0x111961 3 11) (Reg.operands [.gpr 11, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[67, 71]
    (.letOp (n := 75) (.out 0x111964 (movR32R32Effect 0x111964 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 76) (.exec 0x111964 (fun s => s.RIP = 0x111964) (movR32R32Effect 0x111964 2 1 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 77) (.out 0x111966 (shlR64ClEffect 0x111966 3 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[7, 75]
    (.letOp (n := 78) (.exec 0x111966 (fun s => s.RIP = 0x111966) (shlR64ClEffect 0x111966 3 7) (Reg.operands [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[7, 75]
    (.letOp (n := 79) (.out 0x111969 (movR64R64Effect 0x111969 12 14) (EffectPart.reads (.reg (.gpr 12)) [.gpr 14] []) (.reg (.gpr 12))) #v[14]
    (.letOp (n := 80) (.exec 0x111969 (fun s => s.RIP = 0x111969) (movR64R64Effect 0x111969 12 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 81) (.out 0x11196c (movR32R32Effect 0x11196c 2 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[69]
    (.letOp (n := 82) (.exec 0x11196c (fun s => s.RIP = 0x11196c) (movR32R32Effect 0x11196c 2 1 5) (Reg.operands [.gpr 5] [])) #v[69]
    (.letOp (n := 83) (.out 0x11196e (shrR64ClEffect 0x11196e 3 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[79, 81]
    (.letOp (n := 84) (.exec 0x11196e (fun s => s.RIP = 0x11196e) (shrR64ClEffect 0x11196e 3 12) (Reg.operands [.gpr 12, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[79, 81]
    (.letOp (n := 85) (.out 0x111971 (andR64R64Effect 0x111971 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 3] []) (.reg (.gpr 2))) #v[65, 63]
    (.letOp (n := 86) (.exec 0x111971 (fun s => s.RIP = 0x111971) (andR64R64Effect 0x111971 2 3) (Reg.operands [.gpr 2, .gpr 3] [])) #v[65, 63]
    (.letOp (n := 87) (.out 0x111974 (xorR64R64Effect 0x111974 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[85, 61]
    (.letOp (n := 88) (.exec 0x111974 (fun s => s.RIP = 0x111974) (xorR64R64Effect 0x111974 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[85, 61]
    (.terminate (.br ⟨.l117457, RegMap.args [(0, 53), (1, 81), (2, 87), (3, 63), (4, 4), (5, 69), (6, 61), (7, 77), (9, 9), (10, 59), (11, 73), (12, 83), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)] 89⟩)))))))))))))))))))))))))))))))))))))

def bytes_l117423 : List UInt8 :=
  [0x89, 0xC8, 0x4D, 0x89, 0xEA, 0x89, 0xC1, 0x49, 0xD3, 0xE2, 0x48, 0x8B, 0x74, 0x24, 0x48, 0x48,
    0x31, 0xF3, 0x48, 0xF7, 0xDA, 0x49, 0x89, 0xFB, 0x8B, 0x6C, 0x24, 0x44, 0x89, 0xE9, 0x49, 0xD3,
    0xEB, 0x89, 0xC1, 0x48, 0xD3, 0xE7, 0x4D, 0x89, 0xF4, 0x89, 0xE9, 0x49, 0xD3, 0xEC, 0x48, 0x21,
    0xDA, 0x48, 0x31, 0xF2]

theorem code_l117423 : ∀ x ∈ codeRange 0x111943 bytes_l117423, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x11943 52 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l117457 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x111977 (orR64R64Effect 0x111977 12 7) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 7] []) (.reg (.gpr 12))) #v[12, 7]
    (.letOp (n := 54) (.exec 0x111977 (fun s => s.RIP = 0x111977) (orR64R64Effect 0x111977 12 7) (Reg.operands [.gpr 12, .gpr 7] [])) #v[12, 7]
    (.letOp (n := 55) (.out 0x11197a (movR32R32Effect 0x11197a 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[0]
    (.letOp (n := 56) (.exec 0x11197a (fun s => s.RIP = 0x11197a) (movR32R32Effect 0x11197a 2 1 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 57) (.out 0x11197c (shlR64ClEffect 0x11197c 3 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[14, 55]
    (.letOp (n := 58) (.exec 0x11197c (fun s => s.RIP = 0x11197c) (shlR64ClEffect 0x11197c 3 14) (Reg.operands [.gpr 14, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[14, 55]
    (.letOp (n := 59) (.out 0x11197f (movR64R64Effect 0x11197f 3 15) (EffectPart.reads (.reg (.gpr 3)) [.gpr 15] []) (.reg (.gpr 3))) #v[15]
    (.letOp (n := 60) (.exec 0x11197f (fun s => s.RIP = 0x11197f) (movR64R64Effect 0x11197f 3 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 61) (.out 0x111982 (movR32R32Effect 0x111982 2 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[5]
    (.letOp (n := 62) (.exec 0x111982 (fun s => s.RIP = 0x111982) (movR32R32Effect 0x111982 2 1 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 63) (.out 0x111984 (shrR64ClEffect 0x111984 3 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[59, 61]
    (.letOp (n := 64) (.exec 0x111984 (fun s => s.RIP = 0x111984) (shrR64ClEffect 0x111984 3 3) (Reg.operands [.gpr 3, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[59, 61]
    (.letOp (n := 65) (.out 0x111987 (movR32R32Effect 0x111987 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[0]
    (.letOp (n := 66) (.exec 0x111987 (fun s => s.RIP = 0x111987) (movR32R32Effect 0x111987 2 1 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 67) (.out 0x111989 (shlR64ClEffect 0x111989 3 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[15, 65]
    (.letOp (n := 68) (.exec 0x111989 (fun s => s.RIP = 0x111989) (shlR64ClEffect 0x111989 3 15) (Reg.operands [.gpr 15, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[15, 65]
    (.letOp (n := 69) (.out 0x11198c (movR32R32Effect 0x11198c 2 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[5]
    (.letOp (n := 70) (.exec 0x11198c (fun s => s.RIP = 0x11198c) (movR32R32Effect 0x11198c 2 1 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 71) (.out 0x11198e (shrR64ClEffect 0x11198e 3 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[2, 69]
    (.letOp (n := 72) (.exec 0x11198e (fun s => s.RIP = 0x11198e) (shrR64ClEffect 0x11198e 3 2) (Reg.operands [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2, 69]
    (.letOp (n := 73) (.out 0x111991 (orR64R64Effect 0x111991 3 14) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 14] []) (.reg (.gpr 3))) #v[63, 57]
    (.letOp (n := 74) (.exec 0x111991 (fun s => s.RIP = 0x111991) (orR64R64Effect 0x111991 3 14) (Reg.operands [.gpr 3, .gpr 14] [])) #v[63, 57]
    (.letOp (n := 75) (.out 0x111994 (orR64R64Effect 0x111994 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 15] []) (.reg (.gpr 2))) #v[71, 67]
    (.letOp (n := 76) (.exec 0x111994 (fun s => s.RIP = 0x111994) (orR64R64Effect 0x111994 2 15) (Reg.operands [.gpr 2, .gpr 15] [])) #v[71, 67]
    (.terminate (.br ⟨.l117477, RegMap.args [(0, 0), (1, 69), (2, 75), (3, 73), (4, 4), (5, 5), (7, 7), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 57), (15, 67), (22, 22), (39, 39), (51, 51)] 77⟩)))))))))))))))))))))))))

def bytes_l117457 : List UInt8 :=
  [0x49, 0x09, 0xFC, 0x89, 0xC1, 0x49, 0xD3, 0xE6, 0x4C, 0x89, 0xFB, 0x89, 0xE9, 0x48, 0xD3, 0xEB,
    0x89, 0xC1, 0x49, 0xD3, 0xE7, 0x89, 0xE9, 0x48, 0xD3, 0xEA, 0x4C, 0x09, 0xF3, 0x4C, 0x09, 0xFA]

theorem code_l117457 : ∀ x ∈ codeRange 0x111977 bytes_l117457, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x11977 32 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l117477 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x111997 (movR64R64Effect 0x111997 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 54) (.exec 0x111997 (fun s => s.RIP = 0x111997) (movR64R64Effect 0x111997 0 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 55) (.out 0x11199a (movR64M64Effect 0x11199a 7 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 56) (.exec 0x11199a (LoadPre 0x11199a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x11199a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11199a 7 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x11199f (subR64R64Effect 0x11199f 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[53, 55]
    (.letOp (n := 58) (.exec 0x11199f (fun s => s.RIP = 0x11199f) (subR64R64Effect 0x11199f 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[53, 55]
    (.letOp (n := 59) (.out 0x1119a2 (movR64R64Effect 0x1119a2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2]
    (.letOp (n := 60) (.exec 0x1119a2 (fun s => s.RIP = 0x1119a2) (movR64R64Effect 0x1119a2 1 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 61) (.out 0x1119a5 (notR64Effect 0x1119a5 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[59]
    (.letOp (n := 62) (.exec 0x1119a5 (fun s => s.RIP = 0x1119a5) (notR64Effect 0x1119a5 1) (Reg.operands [.gpr 1] [])) #v[59]
    (.letOp (n := 63) (.out 0x1119a8 (movR64R64Effect 0x1119a8 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 7] []) (.reg (.gpr 6))) #v[55]
    (.letOp (n := 64) (.exec 0x1119a8 (fun s => s.RIP = 0x1119a8) (movR64R64Effect 0x1119a8 6 7) (Reg.operands [.gpr 7] [])) #v[55]
    (.letOp (n := 65) (.out 0x1119ab (andR64R64Effect 0x1119ab 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[63, 61]
    (.letOp (n := 66) (.exec 0x1119ab (fun s => s.RIP = 0x1119ab) (andR64R64Effect 0x1119ab 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[63, 61]
    (.letOp (n := 67) (.out 0x1119ae (orR64R64Effect 0x1119ae 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[61, 55]
    (.letOp (n := 68) (.exec 0x1119ae (fun s => s.RIP = 0x1119ae) (orR64R64Effect 0x1119ae 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[61, 55]
    (.letOp (n := 69) (.out 0x1119b1 (andR64R64Effect 0x1119b1 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[67, 57]
    (.letOp (n := 70) (.exec 0x1119b1 (fun s => s.RIP = 0x1119b1) (andR64R64Effect 0x1119b1 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[67, 57]
    (.letOp (n := 71) (.out 0x1119b4 (orR64R64Effect 0x1119b4 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[69, 65]
    (.letOp (n := 72) (.exec 0x1119b4 (fun s => s.RIP = 0x1119b4) (orR64R64Effect 0x1119b4 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[69, 65]
    (.letOp (n := 73) (.out 0x1119b7 (shrR64Effect 0x1119b7 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[71]
    (.letOp (n := 74) (.exec 0x1119b7 (fun s => s.RIP = 0x1119b7) (shrR64Effect 0x1119b7 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[71]
    (.letOp (n := 75) (.exec 0x1119bb (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1119bb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1119bb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1119bb 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[73, 4]
    (.terminate (.br ⟨.l1174a0, RegMap.args [(0, 57), (1, 73), (2, 2), (3, 3), (4, 4), (5, 5), (6, 65), (7, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (51, 51)] 76⟩))))))))))))))))))))))))

def bytes_l117477 : List UInt8 :=
  [0x48, 0x89, 0xD0, 0x48, 0x8B, 0x7C, 0x24, 0x50, 0x48, 0x29, 0xF8, 0x48, 0x89, 0xD1, 0x48, 0xF7,
    0xD1, 0x48, 0x89, 0xFE, 0x48, 0x21, 0xCE, 0x48, 0x09, 0xF9, 0x48, 0x21, 0xC1, 0x48, 0x09, 0xF1,
    0x48, 0xC1, 0xE9, 0x3F, 0x48, 0x89, 0x4C, 0x24, 0x10]

theorem code_l117477 : ∀ x ∈ codeRange 0x111997 bytes_l117477, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x11997 41 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1174a0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1119c0 (fun s => s.RIP = 0x1119c0) (leaR64Effect 0x1119c0 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.out 0x1119c5 (xorR32R32Effect 0x1119c5 3 9 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 9] []) (.reg (.gpr 9))) #v[9, 9]
    (.letOp (n := 55) (.exec 0x1119c5 (fun s => s.RIP = 0x1119c5) (xorR32R32Effect 0x1119c5 3 9 9) (Reg.operands [.gpr 9, .gpr 9] [])) #v[9, 9]
    (.letOp (n := 56) (.out 0x1119c8 (subR64M64Effect 0x1119c8 9 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 4] []) (.reg (.gpr 9))) #v[54, 4]
    (.letOp (n := 57) (.exec 0x1119c8 (LoadPre 0x1119c8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1119c8 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x1119c8 9 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[54, 4]
    (.letOp (n := 58) (.out 0x1119cd (movR64R64Effect 0x1119cd 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[3]
    (.letOp (n := 59) (.exec 0x1119cd (fun s => s.RIP = 0x1119cd) (movR64R64Effect 0x1119cd 6 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 60) (.out 0x1119d0 (movR64M64Effect 0x1119d0 8 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 61) (.exec 0x1119d0 (LoadPre 0x1119d0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1119d0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1119d0 8 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.out 0x1119d5 (subR64R64Effect 0x1119d5 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 8] []) (.reg (.gpr 6))) #v[58, 60]
    (.letOp (n := 63) (.exec 0x1119d5 (fun s => s.RIP = 0x1119d5) (subR64R64Effect 0x1119d5 6 8) (Reg.operands [.gpr 6, .gpr 8] [])) #v[58, 60]
    (.letOp (n := 64) (.out 0x1119d8 (sarR64Effect 0x1119d8 4 9 63) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[56]
    (.letOp (n := 65) (.exec 0x1119d8 (fun s => s.RIP = 0x1119d8) (sarR64Effect 0x1119d8 4 9 63) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[56]
    (.letOp (n := 66) (.out 0x1119dc (addR64R64Effect 0x1119dc 9 6) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 6] []) (.reg (.gpr 9))) #v[64, 62]
    (.letOp (n := 67) (.exec 0x1119dc (fun s => s.RIP = 0x1119dc) (addR64R64Effect 0x1119dc 9 6) (Reg.operands [.gpr 9, .gpr 6] [])) #v[64, 62]
    (.letOp (n := 68) (.out 0x1119df (movR64R64Effect 0x1119df 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[3]
    (.letOp (n := 69) (.exec 0x1119df (fun s => s.RIP = 0x1119df) (movR64R64Effect 0x1119df 6 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x1119e2 (notR64Effect 0x1119e2 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[68]
    (.letOp (n := 71) (.exec 0x1119e2 (fun s => s.RIP = 0x1119e2) (notR64Effect 0x1119e2 6) (Reg.operands [.gpr 6] [])) #v[68]
    (.letOp (n := 72) (.out 0x1119e5 (movR64R64Effect 0x1119e5 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 8] []) (.reg (.gpr 7))) #v[60]
    (.letOp (n := 73) (.exec 0x1119e5 (fun s => s.RIP = 0x1119e5) (movR64R64Effect 0x1119e5 7 8) (Reg.operands [.gpr 8] [])) #v[60]
    (.letOp (n := 74) (.out 0x1119e8 (andR64R64Effect 0x1119e8 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[72, 70]
    (.letOp (n := 75) (.exec 0x1119e8 (fun s => s.RIP = 0x1119e8) (andR64R64Effect 0x1119e8 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[72, 70]
    (.letOp (n := 76) (.out 0x1119eb (orR64R64Effect 0x1119eb 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 8] []) (.reg (.gpr 6))) #v[70, 60]
    (.letOp (n := 77) (.exec 0x1119eb (fun s => s.RIP = 0x1119eb) (orR64R64Effect 0x1119eb 6 8) (Reg.operands [.gpr 6, .gpr 8] [])) #v[70, 60]
    (.letOp (n := 78) (.out 0x1119ee (andR64R64Effect 0x1119ee 6 9) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 9] []) (.reg (.gpr 6))) #v[76, 66]
    (.letOp (n := 79) (.exec 0x1119ee (fun s => s.RIP = 0x1119ee) (andR64R64Effect 0x1119ee 6 9) (Reg.operands [.gpr 6, .gpr 9] [])) #v[76, 66]
    (.letOp (n := 80) (.out 0x1119f1 (orR64R64Effect 0x1119f1 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7] []) (.reg (.gpr 6))) #v[78, 74]
    (.letOp (n := 81) (.exec 0x1119f1 (fun s => s.RIP = 0x1119f1) (orR64R64Effect 0x1119f1 6 7) (Reg.operands [.gpr 6, .gpr 7] [])) #v[78, 74]
    (.letOp (n := 82) (.out 0x1119f4 (shrR64Effect 0x1119f4 4 6 63) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[80]
    (.letOp (n := 83) (.exec 0x1119f4 (fun s => s.RIP = 0x1119f4) (shrR64Effect 0x1119f4 4 6 63) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[80]
    (.terminate (.br ⟨.l1174d8, RegMap.args [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 82), (7, 74), (8, 60), (9, 66), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (51, 51)] 84⟩))))))))))))))))))))))))))))))))

def bytes_l1174a0 : List UInt8 :=
  [0x48, 0x8D, 0x4C, 0x24, 0x10, 0x45, 0x31, 0xC9, 0x4C, 0x2B, 0x4C, 0x24, 0x10, 0x48, 0x89, 0xDE,
    0x4C, 0x8B, 0x44, 0x24, 0x58, 0x4C, 0x29, 0xC6, 0x49, 0xC1, 0xF9, 0x3F, 0x49, 0x01, 0xF1, 0x48,
    0x89, 0xDE, 0x48, 0xF7, 0xD6, 0x4C, 0x89, 0xC7, 0x48, 0x21, 0xF7, 0x4C, 0x09, 0xC6, 0x4C, 0x21,
    0xCE, 0x48, 0x09, 0xFE, 0x48, 0xC1, 0xEE, 0x3F]

theorem code_l1174a0 : ∀ x ∈ codeRange 0x1119c0 bytes_l1174a0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x119c0 56 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1174d8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1119f8 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1119f8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1119f8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1119f8 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[6, 4]
    (.letOp (n := 54) (.out 0x1119fd (xorR32R32Effect 0x1119fd 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[6, 6]
    (.letOp (n := 55) (.exec 0x1119fd (fun s => s.RIP = 0x1119fd) (xorR32R32Effect 0x1119fd 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 56) (.out 0x1119ff (subR64M64Effect 0x1119ff 6 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 4] []) (.reg (.gpr 6))) #v[54, 4]
    (.letOp (n := 57) (.exec 0x1119ff (LoadPre 0x1119ff (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1119ff + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x1119ff 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[54, 4]
    (.letOp (n := 58) (.out 0x111a04 (movR64R64Effect 0x111a04 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[12]
    (.letOp (n := 59) (.exec 0x111a04 (fun s => s.RIP = 0x111a04) (movR64R64Effect 0x111a04 7 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 60) (.out 0x111a07 (movR64M64Effect 0x111a07 14 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 61) (.exec 0x111a07 (LoadPre 0x111a07 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x111a07 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111a07 14 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.out 0x111a0c (subR64R64Effect 0x111a0c 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 14] []) (.reg (.gpr 7))) #v[58, 60]
    (.letOp (n := 63) (.exec 0x111a0c (fun s => s.RIP = 0x111a0c) (subR64R64Effect 0x111a0c 7 14) (Reg.operands [.gpr 7, .gpr 14] [])) #v[58, 60]
    (.letOp (n := 64) (.out 0x111a0f (sarR64Effect 0x111a0f 4 6 63) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[56]
    (.letOp (n := 65) (.exec 0x111a0f (fun s => s.RIP = 0x111a0f) (sarR64Effect 0x111a0f 4 6 63) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[56]
    (.letOp (n := 66) (.out 0x111a13 (addR64R64Effect 0x111a13 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7] []) (.reg (.gpr 6))) #v[64, 62]
    (.letOp (n := 67) (.exec 0x111a13 (fun s => s.RIP = 0x111a13) (addR64R64Effect 0x111a13 6 7) (Reg.operands [.gpr 6, .gpr 7] [])) #v[64, 62]
    (.letOp (n := 68) (.out 0x111a16 (movR64R64Effect 0x111a16 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[12]
    (.letOp (n := 69) (.exec 0x111a16 (fun s => s.RIP = 0x111a16) (movR64R64Effect 0x111a16 7 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 70) (.out 0x111a19 (notR64Effect 0x111a19 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[68]
    (.letOp (n := 71) (.exec 0x111a19 (fun s => s.RIP = 0x111a19) (notR64Effect 0x111a19 7) (Reg.operands [.gpr 7] [])) #v[68]
    (.letOp (n := 72) (.out 0x111a1c (movR64R64Effect 0x111a1c 8 14) (EffectPart.reads (.reg (.gpr 8)) [.gpr 14] []) (.reg (.gpr 8))) #v[60]
    (.letOp (n := 73) (.exec 0x111a1c (fun s => s.RIP = 0x111a1c) (movR64R64Effect 0x111a1c 8 14) (Reg.operands [.gpr 14] [])) #v[60]
    (.letOp (n := 74) (.out 0x111a1f (andR64R64Effect 0x111a1f 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 7] []) (.reg (.gpr 8))) #v[72, 70]
    (.letOp (n := 75) (.exec 0x111a1f (fun s => s.RIP = 0x111a1f) (andR64R64Effect 0x111a1f 8 7) (Reg.operands [.gpr 8, .gpr 7] [])) #v[72, 70]
    (.letOp (n := 76) (.out 0x111a22 (orR64R64Effect 0x111a22 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 14] []) (.reg (.gpr 7))) #v[70, 60]
    (.letOp (n := 77) (.exec 0x111a22 (fun s => s.RIP = 0x111a22) (orR64R64Effect 0x111a22 7 14) (Reg.operands [.gpr 7, .gpr 14] [])) #v[70, 60]
    (.letOp (n := 78) (.out 0x111a25 (andR64R64Effect 0x111a25 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[76, 66]
    (.letOp (n := 79) (.exec 0x111a25 (fun s => s.RIP = 0x111a25) (andR64R64Effect 0x111a25 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[76, 66]
    (.letOp (n := 80) (.out 0x111a28 (orR64R64Effect 0x111a28 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 8] []) (.reg (.gpr 7))) #v[78, 74]
    (.letOp (n := 81) (.exec 0x111a28 (fun s => s.RIP = 0x111a28) (orR64R64Effect 0x111a28 7 8) (Reg.operands [.gpr 7, .gpr 8] [])) #v[78, 74]
    (.letOp (n := 82) (.out 0x111a2b (shrR64Effect 0x111a2b 4 7 63) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[80]
    (.letOp (n := 83) (.exec 0x111a2b (fun s => s.RIP = 0x111a2b) (shrR64Effect 0x111a2b 4 7 63) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[80]
    (.terminate (.br ⟨.l11750f, RegMap.args [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 66), (7, 82), (8, 74), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 60), (22, 22), (39, 39), (51, 51)] 84⟩))))))))))))))))))))))))))))))))

def bytes_l1174d8 : List UInt8 :=
  [0x48, 0x89, 0x74, 0x24, 0x10, 0x31, 0xF6, 0x48, 0x2B, 0x74, 0x24, 0x10, 0x4C, 0x89, 0xE7, 0x4C,
    0x8B, 0x74, 0x24, 0x60, 0x4C, 0x29, 0xF7, 0x48, 0xC1, 0xFE, 0x3F, 0x48, 0x01, 0xFE, 0x4C, 0x89,
    0xE7, 0x48, 0xF7, 0xD7, 0x4D, 0x89, 0xF0, 0x49, 0x21, 0xF8, 0x4C, 0x09, 0xF7, 0x48, 0x21, 0xF7,
    0x4C, 0x09, 0xC7, 0x48, 0xC1, 0xEF, 0x3F]

theorem code_l1174d8 : ∀ x ∈ codeRange 0x1119f8 bytes_l1174d8, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x119f8 55 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11750f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x111a2f (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111a2f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x111a2f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x111a2f 7 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[7, 4]
    (.letOp (n := 54) (.out 0x111a34 (xorR32R32Effect 0x111a34 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[7, 7]
    (.letOp (n := 55) (.exec 0x111a34 (fun s => s.RIP = 0x111a34) (xorR32R32Effect 0x111a34 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[7, 7]
    (.letOp (n := 56) (.out 0x111a36 (subR64M64Effect 0x111a36 7 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 4] []) (.reg (.gpr 7))) #v[54, 4]
    (.letOp (n := 57) (.exec 0x111a36 (LoadPre 0x111a36 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x111a36 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x111a36 7 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[54, 4]
    (.letOp (n := 58) (.out 0x111a3b (orR64R64Effect 0x111a3b 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 10] []) (.reg (.gpr 11))) #v[11, 10]
    (.letOp (n := 59) (.exec 0x111a3b (fun s => s.RIP = 0x111a3b) (orR64R64Effect 0x111a3b 11 10) (Reg.operands [.gpr 11, .gpr 10] [])) #v[11, 10]
    (.letOp (n := 60) (.out 0x111a3e (movR64R64Effect 0x111a3e 8 11) (EffectPart.reads (.reg (.gpr 8)) [.gpr 11] []) (.reg (.gpr 8))) #v[58]
    (.letOp (n := 61) (.exec 0x111a3e (fun s => s.RIP = 0x111a3e) (movR64R64Effect 0x111a3e 8 11) (Reg.operands [.gpr 11] [])) #v[58]
    (.letOp (n := 62) (.out 0x111a41 (movR64M64Effect 0x111a41 14 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 63) (.exec 0x111a41 (LoadPre 0x111a41 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x111a41 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111a41 14 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x111a46 (subR64R64Effect 0x111a46 8 14) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 14] []) (.reg (.gpr 8))) #v[60, 62]
    (.letOp (n := 65) (.exec 0x111a46 (fun s => s.RIP = 0x111a46) (subR64R64Effect 0x111a46 8 14) (Reg.operands [.gpr 8, .gpr 14] [])) #v[60, 62]
    (.letOp (n := 66) (.out 0x111a49 (sarR64Effect 0x111a49 4 7 63) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[56]
    (.letOp (n := 67) (.exec 0x111a49 (fun s => s.RIP = 0x111a49) (sarR64Effect 0x111a49 4 7 63) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[56]
    (.letOp (n := 68) (.out 0x111a4d (addR64R64Effect 0x111a4d 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 8] []) (.reg (.gpr 7))) #v[66, 64]
    (.letOp (n := 69) (.exec 0x111a4d (fun s => s.RIP = 0x111a4d) (addR64R64Effect 0x111a4d 7 8) (Reg.operands [.gpr 7, .gpr 8] [])) #v[66, 64]
    (.letOp (n := 70) (.out 0x111a50 (movR64R64Effect 0x111a50 8 11) (EffectPart.reads (.reg (.gpr 8)) [.gpr 11] []) (.reg (.gpr 8))) #v[58]
    (.letOp (n := 71) (.exec 0x111a50 (fun s => s.RIP = 0x111a50) (movR64R64Effect 0x111a50 8 11) (Reg.operands [.gpr 11] [])) #v[58]
    (.letOp (n := 72) (.out 0x111a53 (notR64Effect 0x111a53 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[70]
    (.letOp (n := 73) (.exec 0x111a53 (fun s => s.RIP = 0x111a53) (notR64Effect 0x111a53 8) (Reg.operands [.gpr 8] [])) #v[70]
    (.letOp (n := 74) (.out 0x111a56 (movR64R64Effect 0x111a56 10 14) (EffectPart.reads (.reg (.gpr 10)) [.gpr 14] []) (.reg (.gpr 10))) #v[62]
    (.letOp (n := 75) (.exec 0x111a56 (fun s => s.RIP = 0x111a56) (movR64R64Effect 0x111a56 10 14) (Reg.operands [.gpr 14] [])) #v[62]
    (.letOp (n := 76) (.out 0x111a59 (andR64R64Effect 0x111a59 10 8) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 8] []) (.reg (.gpr 10))) #v[74, 72]
    (.letOp (n := 77) (.exec 0x111a59 (fun s => s.RIP = 0x111a59) (andR64R64Effect 0x111a59 10 8) (Reg.operands [.gpr 10, .gpr 8] [])) #v[74, 72]
    (.letOp (n := 78) (.out 0x111a5c (orR64R64Effect 0x111a5c 8 14) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 14] []) (.reg (.gpr 8))) #v[72, 62]
    (.letOp (n := 79) (.exec 0x111a5c (fun s => s.RIP = 0x111a5c) (orR64R64Effect 0x111a5c 8 14) (Reg.operands [.gpr 8, .gpr 14] [])) #v[72, 62]
    (.letOp (n := 80) (.out 0x111a5f (andR64R64Effect 0x111a5f 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 7] []) (.reg (.gpr 8))) #v[78, 68]
    (.letOp (n := 81) (.exec 0x111a5f (fun s => s.RIP = 0x111a5f) (andR64R64Effect 0x111a5f 8 7) (Reg.operands [.gpr 8, .gpr 7] [])) #v[78, 68]
    (.letOp (n := 82) (.out 0x111a62 (orR64R64Effect 0x111a62 8 10) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 10] []) (.reg (.gpr 8))) #v[80, 76]
    (.letOp (n := 83) (.exec 0x111a62 (fun s => s.RIP = 0x111a62) (orR64R64Effect 0x111a62 8 10) (Reg.operands [.gpr 8, .gpr 10] [])) #v[80, 76]
    (.letOp (n := 84) (.out 0x111a65 (shrR64Effect 0x111a65 4 8 63) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[82]
    (.letOp (n := 85) (.exec 0x111a65 (fun s => s.RIP = 0x111a65) (shrR64Effect 0x111a65 4 8 63) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[82]
    (.letOp (n := 86) (.exec 0x111a69 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111a69 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x111a69 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x111a69 8 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[84, 4]
    (.terminate (.br ⟨.l11754e, RegMap.args [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 68), (8, 84), (9, 9), (10, 76), (11, 58), (12, 12), (13, 13), (14, 62), (22, 22), (39, 39), (51, 51)] 87⟩)))))))))))))))))))))))))))))))))))

def bytes_l11750f : List UInt8 :=
  [0x48, 0x89, 0x7C, 0x24, 0x10, 0x31, 0xFF, 0x48, 0x2B, 0x7C, 0x24, 0x10, 0x4D, 0x09, 0xD3, 0x4D,
    0x89, 0xD8, 0x4C, 0x8B, 0x74, 0x24, 0x68, 0x4D, 0x29, 0xF0, 0x48, 0xC1, 0xFF, 0x3F, 0x4C, 0x01,
    0xC7, 0x4D, 0x89, 0xD8, 0x49, 0xF7, 0xD0, 0x4D, 0x89, 0xF2, 0x4D, 0x21, 0xC2, 0x4D, 0x09, 0xF0,
    0x49, 0x21, 0xF8, 0x4D, 0x09, 0xD0, 0x49, 0xC1, 0xE8, 0x3F, 0x4C, 0x89, 0x44, 0x24, 0x10]

theorem code_l11750f : ∀ x ∈ codeRange 0x111a2f bytes_l11750f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x11a2f 63 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11754e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x111a6e (xorR32R32Effect 0x111a6e 3 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 8] []) (.reg (.gpr 8))) #v[8, 8]
    (.letOp (n := 54) (.exec 0x111a6e (fun s => s.RIP = 0x111a6e) (xorR32R32Effect 0x111a6e 3 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[8, 8]
    (.letOp (n := 55) (.out 0x111a71 (movR32R32Effect 0x111a71 2 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[5]
    (.letOp (n := 56) (.exec 0x111a71 (fun s => s.RIP = 0x111a71) (movR32R32Effect 0x111a71 2 1 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 57) (.out 0x111a73 (shrR64ClEffect 0x111a73 3 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[13, 55]
    (.letOp (n := 58) (.exec 0x111a73 (fun s => s.RIP = 0x111a73) (shrR64ClEffect 0x111a73 3 13) (Reg.operands [.gpr 13, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[13, 55]
    (.letOp (n := 59) (.out 0x111a76 (subR64M64Effect 0x111a76 8 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 4] []) (.reg (.gpr 8))) #v[53, 4]
    (.letOp (n := 60) (.exec 0x111a76 (LoadPre 0x111a76 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x111a76 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x111a76 8 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 61) (.out 0x111a7b (movzxR32M8Effect 0x111a7b 5 5 (.sib 4 none 0 (.d8 0xf))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 62) (.exec 0x111a7b (LoadPre 0x111a7b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x111a7b + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x111a7b 5 5 (.sib 4 none 0 (.d8 0xf))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x111a80 (xorR8M8Effect 0x111a80 5 5 (.sib 4 none 0 (.d8 0xe))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 4] []) (.reg (.gpr 5))) #v[61, 4]
    (.letOp (n := 64) (.exec 0x111a80 (LoadPre 0x111a80 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x111a80 + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x111a80 5 5 (.sib 4 none 0 (.d8 0xe))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 65) (.out 0x111a85 (testR64R64Effect 0x111a85 13 13) (EffectPart.reads (.flag .ZF) [.gpr 13, .gpr 13] []) (.flag .ZF)) #v[57, 57]
    (.letOp (n := 66) (.exec 0x111a85 (fun s => s.RIP = 0x111a85) (testR64R64Effect 0x111a85 13 13) (Reg.operands [.gpr 13, .gpr 13] [])) #v[57, 57]
    (.letOp (n := 67) (.out 0x111a88 (atFlags (condHolds 4) (setccR8Effect 0x111a88 3 1)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 1))) #v[55, 65]
    (.letOp (n := 68) (.exec 0x111a88 (fun s => s.RIP = 0x111a88) (atFlags (condHolds 4) (setccR8Effect 0x111a88 3 1)) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[55, 65]
    (.letOp (n := 69) (.out 0x111a8b (andR8R8Effect 0x111a8b 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8] []) (.reg (.gpr 1))) #v[67, 59]
    (.letOp (n := 70) (.exec 0x111a8b (fun s => s.RIP = 0x111a8b) (andR8R8Effect 0x111a8b 3 1 8) (Reg.operands [.gpr 1, .gpr 8] [])) #v[67, 59]
    (.letOp (n := 71) (.exec 0x111a8e (StorePre 0x111a8e 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x111a8e + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x111a8e 4 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[69, 4]
    (.letOp (n := 72) (.exec 0x111a92 (fun s => s.RIP = 0x111a92) (leaR64Effect 0x111a92 10 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.out 0x111a97 (movzxR32M8Effect 0x111a97 6 10 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 74) (.exec 0x111a97 (LoadPre 0x111a97 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x111a97 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x111a97 6 10 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.out 0x111a9d (decR64Effect 0x111a9d 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[73]
    (.letOp (n := 76) (.exec 0x111a9d (fun s => s.RIP = 0x111a9d) (decR64Effect 0x111a9d 10) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[73]
    (.letOp (n := 77) (.out 0x111aa0 (andR64R64Effect 0x111aa0 10 8) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 8] []) (.reg (.gpr 10))) #v[75, 59]
    (.letOp (n := 78) (.exec 0x111aa0 (fun s => s.RIP = 0x111aa0) (andR64R64Effect 0x111aa0 10 8) (Reg.operands [.gpr 10, .gpr 8] [])) #v[75, 59]
    (.letOp (n := 79) (.out 0x111aa3 (sarR64Effect 0x111aa3 4 10 63) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[77]
    (.letOp (n := 80) (.exec 0x111aa3 (fun s => s.RIP = 0x111aa3) (sarR64Effect 0x111aa3 4 10 63) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[77]
    (.letOp (n := 81) (.out 0x111aa7 (addR64R64Effect 0x111aa7 10 13) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 13] []) (.reg (.gpr 10))) #v[79, 57]
    (.letOp (n := 82) (.exec 0x111aa7 (fun s => s.RIP = 0x111aa7) (addR64R64Effect 0x111aa7 10 13) (Reg.operands [.gpr 10, .gpr 13] [])) #v[79, 57]
    (.letOp (n := 83) (.out 0x111aaa (shrR64Effect 0x111aaa 4 10 63) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[81]
    (.letOp (n := 84) (.exec 0x111aaa (fun s => s.RIP = 0x111aaa) (shrR64Effect 0x111aaa 4 10 63) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[81]
    (.terminate (.br ⟨.l11758e, RegMap.args [(0, 0), (1, 69), (2, 2), (3, 3), (4, 4), (5, 63), (6, 6), (7, 7), (8, 59), (9, 9), (10, 83), (11, 11), (12, 12), (13, 57), (22, 22), (39, 39), (51, 51)] 85⟩)))))))))))))))))))))))))))))))))

def bytes_l11754e : List UInt8 :=
  [0x45, 0x31, 0xC0, 0x89, 0xE9, 0x49, 0xD3, 0xED, 0x4C, 0x2B, 0x44, 0x24, 0x10, 0x0F, 0xB6, 0x6C,
    0x24, 0x0F, 0x40, 0x32, 0x6C, 0x24, 0x0E, 0x4D, 0x85, 0xED, 0x0F, 0x94, 0xC1, 0x44, 0x20, 0xC1,
    0x88, 0x4C, 0x24, 0x10, 0x4C, 0x8D, 0x54, 0x24, 0x10, 0x44, 0x0F, 0xB6, 0x54, 0x24, 0x10, 0x49,
    0xFF, 0xCA, 0x4D, 0x21, 0xC2, 0x49, 0xC1, 0xFA, 0x3F, 0x4D, 0x01, 0xEA, 0x49, 0xC1, 0xEA, 0x3F]

theorem code_l11754e : ∀ x ∈ codeRange 0x111a6e bytes_l11754e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x11a6e 64 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11758e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x111aae (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111aae 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x111aae + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x111aae 10 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[10, 4]
    (.letOp (n := 54) (.exec 0x111ab3 (fun s => s.RIP = 0x111ab3) (leaR64Effect 0x111ab3 8 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x111ab8 (StorePre 0x111ab8 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x111ab8 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x111ab8 4 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1, 4]
    (.letOp (n := 56) (.exec 0x111abc (fun s => s.RIP = 0x111abc) (leaR64Effect 0x111abc 10 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x111ac1 (movzxR32M8Effect 0x111ac1 6 8 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 58) (.exec 0x111ac1 (LoadPre 0x111ac1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x111ac1 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x111ac1 6 8 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x111ac7 (xorR64R64Effect 0x111ac7 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[2, 0]
    (.letOp (n := 60) (.exec 0x111ac7 (fun s => s.RIP = 0x111ac7) (xorR64R64Effect 0x111ac7 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[2, 0]
    (.letOp (n := 61) (.out 0x111aca (negR64Effect 0x111aca 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[57]
    (.letOp (n := 62) (.exec 0x111aca (fun s => s.RIP = 0x111aca) (negR64Effect 0x111aca 8) (Reg.operands [.gpr 8] [])) #v[57]
    (.letOp (n := 63) (.out 0x111acd (andR64R64Effect 0x111acd 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2] []) (.reg (.gpr 8))) #v[61, 59]
    (.letOp (n := 64) (.exec 0x111acd (fun s => s.RIP = 0x111acd) (andR64R64Effect 0x111acd 8 2) (Reg.operands [.gpr 8, .gpr 2] [])) #v[61, 59]
    (.letOp (n := 65) (.out 0x111ad0 (xorR64R64Effect 0x111ad0 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[63, 0]
    (.letOp (n := 66) (.exec 0x111ad0 (fun s => s.RIP = 0x111ad0) (xorR64R64Effect 0x111ad0 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[63, 0]
    (.letOp (n := 67) (.exec 0x111ad3 (StorePre 0x111ad3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x111ad3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x111ad3 4 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1, 4]
    (.letOp (n := 68) (.out 0x111ad7 (movzxR32M8Effect 0x111ad7 5 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 69) (.exec 0x111ad7 (LoadPre 0x111ad7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x111ad7 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x111ad7 5 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.out 0x111adc (xorR64R64Effect 0x111adc 3 9) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 9] []) (.reg (.gpr 3))) #v[3, 9]
    (.letOp (n := 71) (.exec 0x111adc (fun s => s.RIP = 0x111adc) (xorR64R64Effect 0x111adc 3 9) (Reg.operands [.gpr 3, .gpr 9] [])) #v[3, 9]
    (.letOp (n := 72) (.out 0x111adf (negR64Effect 0x111adf 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[68]
    (.letOp (n := 73) (.exec 0x111adf (fun s => s.RIP = 0x111adf) (negR64Effect 0x111adf 0) (Reg.operands [.gpr 0] [])) #v[68]
    (.letOp (n := 74) (.out 0x111ae2 (andR64R64Effect 0x111ae2 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[72, 70]
    (.letOp (n := 75) (.exec 0x111ae2 (fun s => s.RIP = 0x111ae2) (andR64R64Effect 0x111ae2 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[72, 70]
    (.letOp (n := 76) (.out 0x111ae5 (xorR64R64Effect 0x111ae5 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[74, 9]
    (.letOp (n := 77) (.exec 0x111ae5 (fun s => s.RIP = 0x111ae5) (xorR64R64Effect 0x111ae5 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[74, 9]
    (.terminate (.br ⟨.l1175c8, RegMap.args [(0, 76), (1, 1), (2, 59), (3, 70), (4, 4), (5, 5), (6, 6), (7, 7), (8, 65), (9, 9), (11, 11), (12, 12), (22, 22), (39, 39), (51, 51)] 78⟩))))))))))))))))))))))))))

def bytes_l11758e : List UInt8 :=
  [0x4C, 0x89, 0x54, 0x24, 0x10, 0x4C, 0x8D, 0x44, 0x24, 0x10, 0x88, 0x4C, 0x24, 0x10, 0x4C, 0x8D,
    0x54, 0x24, 0x10, 0x44, 0x0F, 0xB6, 0x44, 0x24, 0x10, 0x48, 0x31, 0xC2, 0x49, 0xF7, 0xD8, 0x49,
    0x21, 0xD0, 0x49, 0x31, 0xC0, 0x88, 0x4C, 0x24, 0x10, 0x0F, 0xB6, 0x44, 0x24, 0x10, 0x4C, 0x31,
    0xCB, 0x48, 0xF7, 0xD8, 0x48, 0x21, 0xD8, 0x4C, 0x31, 0xC8]

theorem code_l11758e : ∀ x ∈ codeRange 0x111aae bytes_l11758e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x11aae 58 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1175c8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x111ae8 (StorePre 0x111ae8 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x111ae8 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x111ae8 4 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1, 4]
    (.letOp (n := 54) (.out 0x111aec (movzxR32M8Effect 0x111aec 5 2 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 55) (.exec 0x111aec (LoadPre 0x111aec (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x111aec + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x111aec 5 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x111af1 (xorR64R64Effect 0x111af1 12 6) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 6] []) (.reg (.gpr 12))) #v[12, 6]
    (.letOp (n := 57) (.exec 0x111af1 (fun s => s.RIP = 0x111af1) (xorR64R64Effect 0x111af1 12 6) (Reg.operands [.gpr 12, .gpr 6] [])) #v[12, 6]
    (.letOp (n := 58) (.out 0x111af4 (negR64Effect 0x111af4 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[54]
    (.letOp (n := 59) (.exec 0x111af4 (fun s => s.RIP = 0x111af4) (negR64Effect 0x111af4 2) (Reg.operands [.gpr 2] [])) #v[54]
    (.letOp (n := 60) (.out 0x111af7 (andR64R64Effect 0x111af7 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 12] []) (.reg (.gpr 2))) #v[58, 56]
    (.letOp (n := 61) (.exec 0x111af7 (fun s => s.RIP = 0x111af7) (andR64R64Effect 0x111af7 2 12) (Reg.operands [.gpr 2, .gpr 12] [])) #v[58, 56]
    (.letOp (n := 62) (.out 0x111afa (xorR64R64Effect 0x111afa 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[60, 6]
    (.letOp (n := 63) (.exec 0x111afa (fun s => s.RIP = 0x111afa) (xorR64R64Effect 0x111afa 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[60, 6]
    (.letOp (n := 64) (.exec 0x111afd (StorePre 0x111afd 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x111afd + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x111afd 4 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1, 4]
    (.letOp (n := 65) (.out 0x111b01 (movzxR32M8Effect 0x111b01 5 1 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 66) (.exec 0x111b01 (LoadPre 0x111b01 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x111b01 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x111b01 5 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x111b06 (xorR64R64Effect 0x111b06 11 7) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 7] []) (.reg (.gpr 11))) #v[11, 7]
    (.letOp (n := 68) (.exec 0x111b06 (fun s => s.RIP = 0x111b06) (xorR64R64Effect 0x111b06 11 7) (Reg.operands [.gpr 11, .gpr 7] [])) #v[11, 7]
    (.letOp (n := 69) (.out 0x111b09 (negR64Effect 0x111b09 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 70) (.exec 0x111b09 (fun s => s.RIP = 0x111b09) (negR64Effect 0x111b09 1) (Reg.operands [.gpr 1] [])) #v[65]
    (.letOp (n := 71) (.out 0x111b0c (andR64R64Effect 0x111b0c 1 11) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 11] []) (.reg (.gpr 1))) #v[69, 67]
    (.letOp (n := 72) (.exec 0x111b0c (fun s => s.RIP = 0x111b0c) (andR64R64Effect 0x111b0c 1 11) (Reg.operands [.gpr 1, .gpr 11] [])) #v[69, 67]
    (.letOp (n := 73) (.out 0x111b0f (xorR64R64Effect 0x111b0f 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[71, 7]
    (.letOp (n := 74) (.exec 0x111b0f (fun s => s.RIP = 0x111b0f) (xorR64R64Effect 0x111b0f 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[71, 7]
    (.terminate (.br ⟨.l1175f2, RegMap.args [(0, 0), (1, 73), (2, 62), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (11, 67), (12, 56), (22, 22), (39, 39), (51, 51)] 75⟩)))))))))))))))))))))))

def bytes_l1175c8 : List UInt8 :=
  [0x88, 0x4C, 0x24, 0x10, 0x0F, 0xB6, 0x54, 0x24, 0x10, 0x49, 0x31, 0xF4, 0x48, 0xF7, 0xDA, 0x4C,
    0x21, 0xE2, 0x48, 0x31, 0xF2, 0x88, 0x4C, 0x24, 0x10, 0x0F, 0xB6, 0x4C, 0x24, 0x10, 0x49, 0x31,
    0xFB, 0x48, 0xF7, 0xD9, 0x4C, 0x21, 0xD9, 0x48, 0x31, 0xF9]

theorem code_l1175c8 : ∀ x ∈ codeRange 0x111ae8 bytes_l1175c8, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x11ae8 42 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1175f2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x111b12 (movR64M64Effect 0x111b12 6 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 54) (.exec 0x111b12 (LoadPre 0x111b12 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x111b12 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111b12 6 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x111b17 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111b17 3 (fun s => AddrMode.addr (.base 6 .none) s (0x111b17 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x111b17 8 (.base 6 .none)) (Reg.operands [.gpr 8, .gpr 6] [])) #v[8, 53]
    (.letOp (n := 56) (.exec 0x111b1a (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111b1a 4 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x111b1a + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x111b1a 0 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 6] [])) #v[0, 53]
    (.letOp (n := 57) (.exec 0x111b1e (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111b1e 4 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x111b1e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x111b1e 2 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 2, .gpr 6] [])) #v[2, 53]
    (.letOp (n := 58) (.exec 0x111b22 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111b22 4 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x111b22 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x111b22 1 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 1, .gpr 6] [])) #v[1, 53]
    (.letOp (n := 59) (.exec 0x111b26 (StorePre 0x111b26 4 (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x111b26 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x111b26 4 5 (.base 6 (.d8 0x20))) (Reg.operands [.gpr 5, .gpr 6] [])) #v[5, 53]
    (.letOp (n := 60) (.out 0x111b2a (addR64Imm8Effect 0x111b2a 4 0x78) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 61) (.exec 0x111b2a (fun s => s.RIP = 0x111b2a) (addR64Imm8Effect 0x111b2a 4 0x78) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.out 0x111b2e (popR64Effect 0x111b2e 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[60]
    (.letOp (n := 63) (.out 0x111b2e (popR64Effect 0x111b2e 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[60]
    (.letOp (n := 64) (.exec 0x111b2e (PopPre 0x111b2e) (popR64Effect 0x111b2e 1 3) (Reg.operands [.gpr 4] [])) #v[60]
    (.letOp (n := 65) (.out 0x111b2f (popR64Effect 0x111b2f 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[63]
    (.letOp (n := 66) (.out 0x111b2f (popR64Effect 0x111b2f 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 67) (.exec 0x111b2f (PopPre 0x111b2f) (popR64Effect 0x111b2f 2 12) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 68) (.out 0x111b31 (popR64Effect 0x111b31 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[66]
    (.letOp (n := 69) (.out 0x111b31 (popR64Effect 0x111b31 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[66]
    (.letOp (n := 70) (.exec 0x111b31 (PopPre 0x111b31) (popR64Effect 0x111b31 2 13) (Reg.operands [.gpr 4] [])) #v[66]
    (.letOp (n := 71) (.out 0x111b33 (popR64Effect 0x111b33 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[69]
    (.letOp (n := 72) (.out 0x111b33 (popR64Effect 0x111b33 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[69]
    (.letOp (n := 73) (.exec 0x111b33 (PopPre 0x111b33) (popR64Effect 0x111b33 2 14) (Reg.operands [.gpr 4] [])) #v[69]
    (.letOp (n := 74) (.out 0x111b35 (popR64Effect 0x111b35 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[72]
    (.letOp (n := 75) (.out 0x111b35 (popR64Effect 0x111b35 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[72]
    (.letOp (n := 76) (.exec 0x111b35 (PopPre 0x111b35) (popR64Effect 0x111b35 2 15) (Reg.operands [.gpr 4] [])) #v[72]
    (.letOp (n := 77) (.out 0x111b37 (popR64Effect 0x111b37 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[75]
    (.letOp (n := 78) (.out 0x111b37 (popR64Effect 0x111b37 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[75]
    (.letOp (n := 79) (.exec 0x111b37 (PopPre 0x111b37) (popR64Effect 0x111b37 1 5) (Reg.operands [.gpr 4] [])) #v[75]
    (.letOp (n := 80) (.out 0x111b38 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[78]
    (.letOp (n := 81) (.out 0x111b38 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[78]
    (.letOp (n := 82) (.exec 0x111b38 (RetPre 0x111b38) (retEffect) (Reg.operands [.gpr 4] [])) #v[78]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 2), (3, 62), (4, 81), (5, 77), (6, 53), (8, 8), (12, 65), (13, 68), (14, 71), (15, 74), (22, 22), (39, 39), (51, 51)] 83) (some ⟨80, by decide⟩))))))))))))))))))))))))))))))))

def bytes_l1175f2 : List UInt8 :=
  [0x48, 0x8B, 0x74, 0x24, 0x70, 0x4C, 0x89, 0x06, 0x48, 0x89, 0x46, 0x08, 0x48, 0x89, 0x56, 0x10,
    0x48, 0x89, 0x4E, 0x18, 0x40, 0x88, 0x6E, 0x20, 0x48, 0x83, 0xC4, 0x78, 0x5B, 0x41, 0x5C, 0x41,
    0x5D, 0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l1175f2 : ∀ x ∈ codeRange 0x111b12 bytes_l1175f2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x11b12 39 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l117619 : Block Op Label signature Reg.count 53 :=
  cutBlock 0x111b39

def bytes_l117619 : List UInt8 := [0xbe]

theorem code_l117619 : ∀ x ∈ codeRange 0x111b39 bytes_l117619, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x11b39 1 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l117631 : Block Op Label signature Reg.count 53 :=
  cutBlock 0x111b51

def bytes_l117631 : List UInt8 := [0xbf]

theorem code_l117631 : ∀ x ∈ codeRange 0x111b51 bytes_l117631, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x11b51 1 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl


end P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Machine
