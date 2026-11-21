import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Verifying.Core.Inverse.SafeGcd.Machine.Labels
import P256.Proofs.Common.CFG.EvalAttr
import P256.Proofs.Common.Lift.Generated.Footprints

namespace P256.Proofs.Verifying.Core.Inverse.SafeGcd.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

@[cfg_block] def b_l1170b0 : Block Op Label signature Reg.count 53 :=
  cutBlock 0x1115d0

def bytes_l1170b0 : List UInt8 :=
  [0x55]

theorem code_l1170b0 : ∀ x ∈ codeRange 0x1115d0 bytes_l1170b0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x115d0 1 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1171a0 : Block Op Label signature Reg.count 53 :=
  cutBlock 0x1116c0

def bytes_l1171a0 : List UInt8 :=
  [0x55]

theorem code_l1171a0 : ∀ x ∈ codeRange 0x1116c0 bytes_l1171a0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x116c0 1 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1141e0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x112190 (pushR64Effect 0x112190 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x112190 (PushPre 0x112190 1) (pushR64Effect 0x112190 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x112191 (pushR64Effect 0x112191 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x112191 (PushPre 0x112191 2) (pushR64Effect 0x112191 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x112193 (pushR64Effect 0x112193 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x112193 (PushPre 0x112193 2) (pushR64Effect 0x112193 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x112195 (pushR64Effect 0x112195 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x112195 (PushPre 0x112195 2) (pushR64Effect 0x112195 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x112197 (pushR64Effect 0x112197 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x112197 (PushPre 0x112197 2) (pushR64Effect 0x112197 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x112199 (pushR64Effect 0x112199 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x112199 (PushPre 0x112199 1) (pushR64Effect 0x112199 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x11219a (subR64Imm32Effect 0x11219a 4 0x158) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x11219a (fun s => s.RIP = 0x11219a) (subR64Imm32Effect 0x11219a 4 0x158) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.exec 0x1121a1 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1121a1 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x1121a1 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1121a1 1 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1, 65]
    (.letOp (n := 68) (.exec 0x1121a9 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1121a9 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x1121a9 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1121a9 7 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[7, 65]
    (.terminate (.br ⟨.l114201, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)] 69⟩)))))))))))))))))

def bytes_l1141e0 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0x58, 0x01, 0x00,
    0x00, 0x48, 0x89, 0x8C, 0x24, 0x28, 0x01, 0x00, 0x00, 0x48, 0x89, 0xBC, 0x24, 0x20, 0x01, 0x00,
    0x00]

theorem code_l1141e0 : ∀ x ∈ codeRange 0x112190 bytes_l1141e0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x12190 33 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l114201_1 : Block Op Label signature Reg.count 82 :=
  .letOp (n := 82) (.out 0x112216 (movR64M64Effect 0x112216 0 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 83) (.exec 0x112216 (LoadPre 0x112216 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x112216 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x112216 0 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 84) (.exec 0x11221a (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x11221a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x11221a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11221a 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[82, 4]
    (.letOp (n := 85) (.out 0x11221f (movR64M64Effect 0x11221f 0 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 86) (.exec 0x11221f (LoadPre 0x11221f (fun s => AddrMode.addr (.base 6 .none) s (0x11221f + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x11221f 0 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 87) (.out 0x112222 (movR64M64Effect 0x112222 1 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[6]
    (.letOp (n := 88) (.exec 0x112222 (LoadPre 0x112222 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x112222 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x112222 1 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 89) (.exec 0x112226 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112226 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x112226 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x112226 1 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[87, 4]
    (.letOp (n := 90) (.exec 0x11222b (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x11222b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11222b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11222b 0 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[85, 4]
    (.letOp (n := 91) (.exec 0x112230 (StorePre 0x112230 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x112230 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x112230 (.sib 4 none 0 (.d8 0x50)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.br ⟨.l114285, RegMap.args [(0, 85), (1, 87), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)] 92⟩)))))))))))

def bytes_l114201_1 : List UInt8 :=
  [0x48, 0x8B, 0x46, 0x10, 0x48, 0x89, 0x44, 0x24, 0x40, 0x48, 0x8B, 0x06, 0x48, 0x8B, 0x4E, 0x08,
    0x48, 0x89, 0x4C, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x30, 0xC6, 0x44, 0x24, 0x50, 0x00]

theorem code_l114201_1 : ∀ x ∈ codeRange 0x112216 bytes_l114201_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x12216 31 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l114201 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1121b1 (movR64M64Effect 0x1121b1 0 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 54) (.exec 0x1121b1 (LoadPre 0x1121b1 (fun s => AddrMode.addr (.base 6 .none) s (0x1121b1 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1121b1 0 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 55) (.exec 0x1121b4 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1121b4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x1121b4 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1121b4 0 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x1121bc (movR64M64Effect 0x1121bc 0 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 57) (.exec 0x1121bc (LoadPre 0x1121bc (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x1121bc + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1121bc 0 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 58) (.exec 0x1121c0 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1121c0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x1121c0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1121c0 0 (.sib 4 none 0 (.d32 0x118))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x1121c8 (movR64M64Effect 0x1121c8 0 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 60) (.exec 0x1121c8 (LoadPre 0x1121c8 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x1121c8 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1121c8 0 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 61) (.exec 0x1121cc (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1121cc 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x1121cc + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1121cc 0 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x1121d4 (movR64M64Effect 0x1121d4 0 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 63) (.exec 0x1121d4 (LoadPre 0x1121d4 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x1121d4 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1121d4 0 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 64) (.exec 0x1121d8 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1121d8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x1121d8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1121d8 0 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x1121e0 (movR64M64Effect 0x1121e0 0 (.base 2 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 66) (.exec 0x1121e0 (LoadPre 0x1121e0 (fun s => AddrMode.addr (.base 2 (.d8 0x18)) s (0x1121e0 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1121e0 0 (.base 2 (.d8 0x18))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 67) (.exec 0x1121e4 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1121e4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1121e4 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1121e4 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x1121e9 (movR64M64Effect 0x1121e9 0 (.base 2 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 69) (.exec 0x1121e9 (LoadPre 0x1121e9 (fun s => AddrMode.addr (.base 2 (.d8 0x10)) s (0x1121e9 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1121e9 0 (.base 2 (.d8 0x10))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 70) (.exec 0x1121ed (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1121ed 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1121ed + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1121ed 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[68, 4]
    (.letOp (n := 71) (.out 0x1121f2 (movR64M64Effect 0x1121f2 0 (.base 2 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 72) (.exec 0x1121f2 (LoadPre 0x1121f2 (fun s => AddrMode.addr (.base 2 .none) s (0x1121f2 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1121f2 0 (.base 2 .none)) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 73) (.exec 0x1121f5 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1121f5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1121f5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1121f5 2 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2, 4]
    (.letOp (n := 74) (.out 0x1121fa (movR64M64Effect 0x1121fa 1 (.base 2 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2]
    (.letOp (n := 75) (.exec 0x1121fa (LoadPre 0x1121fa (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x1121fa + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1121fa 1 (.base 2 (.d8 0x8))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 76) (.exec 0x1121fe (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1121fe 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1121fe + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1121fe 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[74, 4]
    (.letOp (n := 77) (.exec 0x112203 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112203 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x112203 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x112203 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[71, 4]
    (.letOp (n := 78) (.exec 0x112208 (StorePre 0x112208 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x112208 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x112208 (.sib 4 none 0 (.d8 0x28)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.out 0x11220d (movR64M64Effect 0x11220d 0 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 80) (.exec 0x11220d (LoadPre 0x11220d (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x11220d + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11220d 0 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 81) (.exec 0x112211 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112211 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x112211 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x112211 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[79, 4]
    (b_l114201_1)))))))))))))))))))))))))))))

def bytes_l114201 : List UInt8 :=
  [0x48, 0x8B, 0x06, 0x48, 0x89, 0x84, 0x24, 0x08, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x46, 0x08, 0x48,
    0x89, 0x84, 0x24, 0x18, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x46, 0x10, 0x48, 0x89, 0x84, 0x24, 0x00,
    0x01, 0x00, 0x00, 0x48, 0x8B, 0x46, 0x18, 0x48, 0x89, 0x84, 0x24, 0x10, 0x01, 0x00, 0x00, 0x48,
    0x8B, 0x42, 0x18, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x42, 0x10, 0x48, 0x89, 0x44, 0x24,
    0x18, 0x48, 0x8B, 0x02, 0x48, 0x89, 0x54, 0x24, 0x58, 0x48, 0x8B, 0x4A, 0x08, 0x48, 0x89, 0x4C,
    0x24, 0x10, 0x48, 0x89, 0x44, 0x24, 0x08, 0xC6, 0x44, 0x24, 0x28, 0x00, 0x48, 0x8B, 0x46, 0x18,
    0x48, 0x89, 0x44, 0x24, 0x48] ++ bytes_l114201_1

theorem code_l114201 : ∀ x ∈ codeRange 0x1121b1 bytes_l114201, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x121b1 101 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l114201_1

@[cfg_block] def b_l114285 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x112235 (StorePre 0x112235 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x112235 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x112235 (.sib 4 none 0 (.d32 0x80)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.exec 0x112241 (StorePre 0x112241 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x112241 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x112241 (.sib 4 none 0 (.d8 0x78)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x11224a (StorePre 0x11224a 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x11224a + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x11224a (.sib 4 none 0 (.d8 0x70)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.exec 0x112253 (StorePre 0x112253 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x112253 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x112253 (.sib 4 none 0 (.d8 0x68)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x11225c (StorePre 0x11225c 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x11225c + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x11225c (.sib 4 none 0 (.d8 0x60)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.out 0x112265 (movR64M64Effect 0x112265 0 (.base 8 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[8]
    (.letOp (n := 59) (.exec 0x112265 (LoadPre 0x112265 (fun s => AddrMode.addr (.base 8 (.d8 0x18)) s (0x112265 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x112265 0 (.base 8 (.d8 0x18))) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 60) (.exec 0x112269 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112269 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x112269 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x112269 0 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[58, 4]
    (.letOp (n := 61) (.out 0x112271 (movR64M64Effect 0x112271 0 (.base 8 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[8]
    (.letOp (n := 62) (.exec 0x112271 (LoadPre 0x112271 (fun s => AddrMode.addr (.base 8 (.d8 0x10)) s (0x112271 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x112271 0 (.base 8 (.d8 0x10))) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 63) (.exec 0x112275 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112275 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x112275 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x112275 0 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.out 0x11227d (movR64M64Effect 0x11227d 0 (.base 8 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[8]
    (.letOp (n := 65) (.exec 0x11227d (LoadPre 0x11227d (fun s => AddrMode.addr (.base 8 .none) s (0x11227d + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x11227d 0 (.base 8 .none)) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 66) (.out 0x112280 (movR64M64Effect 0x112280 1 (.base 8 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 8] []) (.reg (.gpr 1))) #v[8]
    (.letOp (n := 67) (.exec 0x112280 (LoadPre 0x112280 (fun s => AddrMode.addr (.base 8 (.d8 0x8)) s (0x112280 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x112280 1 (.base 8 (.d8 0x8))) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 68) (.exec 0x112284 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112284 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x112284 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x112284 1 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[66, 4]
    (.letOp (n := 69) (.exec 0x11228c (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x11228c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x11228c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11228c 0 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 70) (.exec 0x112294 (StorePre 0x112294 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x112294 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x112294 (.sib 4 none 0 (.d32 0xa8)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.br ⟨.l1142ec, RegMap.args [(0, 64), (1, 66), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)] 71⟩)))))))))))))))))))

def bytes_l114285 : List UInt8 :=
  [0x48, 0xC7, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24,
    0x78, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x70, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7,
    0x44, 0x24, 0x68, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x60, 0x00, 0x00, 0x00, 0x00,
    0x49, 0x8B, 0x40, 0x18, 0x48, 0x89, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x49, 0x8B, 0x40, 0x10,
    0x48, 0x89, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00, 0x49, 0x8B, 0x00, 0x49, 0x8B, 0x48, 0x08, 0x48,
    0x89, 0x8C, 0x24, 0x90, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, 0xC6,
    0x84, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x00]

theorem code_l114285 : ∀ x ∈ codeRange 0x112235 bytes_l114285, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x12235 103 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1142ec : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11229c (movR32Imm32Effect 0x11229c 6 12 0x1) (EffectPart.reads (.reg (.gpr 12)) [] []) (.reg (.gpr 12))) #v[]
    (.letOp (n := 54) (.exec 0x11229c (fun s => s.RIP = 0x11229c) (movR32Imm32Effect 0x11229c 6 12 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x1122a2 (movR32Imm32Effect 0x1122a2 5 6 0x24f) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 56) (.exec 0x1122a2 (fun s => s.RIP = 0x1122a2) (movR32Imm32Effect 0x1122a2 5 6 0x24f) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l11454e, RegMap.args [(3, 3), (4, 4), (5, 5), (6, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)] 57⟩)))))

def bytes_l1142ec : List UInt8 :=
  [0x41, 0xBC, 0x01, 0x00, 0x00, 0x00, 0xBE, 0x4F, 0x02, 0x00, 0x00, 0xE9, 0x52, 0x02, 0x00, 0x00]

theorem code_l1142ec : ∀ x ∈ codeRange 0x11229c bytes_l1142ec, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1229c 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l114300 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1122b0 (movR32Imm32Effect 0x1122b0 6 14 0x1) (EffectPart.reads (.reg (.gpr 14)) [] []) (.reg (.gpr 14))) #v[]
    (.letOp (n := 54) (.exec 0x1122b0 (fun s => s.RIP = 0x1122b0) (movR32Imm32Effect 0x1122b0 6 14 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x1122b6 (xorR32R32Effect 0x1122b6 3 13 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 13] []) (.reg (.gpr 13))) #v[13, 13]
    (.letOp (n := 56) (.exec 0x1122b6 (fun s => s.RIP = 0x1122b6) (xorR32R32Effect 0x1122b6 3 13 13) (Reg.operands [.gpr 13, .gpr 13] [])) #v[13, 13]
    (.letOp (n := 57) (.out 0x1122b9 (xorR32R32Effect 0x1122b9 3 15 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 15] []) (.reg (.gpr 15))) #v[15, 15]
    (.letOp (n := 58) (.exec 0x1122b9 (fun s => s.RIP = 0x1122b9) (xorR32R32Effect 0x1122b9 3 15 15) (Reg.operands [.gpr 15, .gpr 15] [])) #v[15, 15]
    (.letOp (n := 59) (.out 0x1122bc (movR32Imm32Effect 0x1122bc 5 3 0x1) (EffectPart.reads (.reg (.gpr 3)) [] []) (.reg (.gpr 3))) #v[]
    (.letOp (n := 60) (.exec 0x1122bc (fun s => s.RIP = 0x1122bc) (movR32Imm32Effect 0x1122bc 5 3 0x1) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l114311, RegMap.args [(3, 59), (4, 4), (9, 9), (10, 10), (11, 11), (12, 12), (13, 55), (14, 53), (15, 57), (22, 22), (39, 39), (51, 51)] 61⟩)))))))))

def bytes_l114300 : List UInt8 :=
  [0x41, 0xBE, 0x01, 0x00, 0x00, 0x00, 0x45, 0x31, 0xED, 0x45, 0x31, 0xFF, 0xBB, 0x01, 0x00, 0x00,
    0x00]

theorem code_l114300 : ∀ x ∈ codeRange 0x1122b0 bytes_l114300, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x122b0 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l114311 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1122c1 (movR64R64Effect 0x1122c1 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 54) (.exec 0x1122c1 (fun s => s.RIP = 0x1122c1) (movR64R64Effect 0x1122c1 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x1122c4 (shrR64Effect 0x1122c4 4 0 63) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x1122c4 (fun s => s.RIP = 0x1122c4) (shrR64Effect 0x1122c4 4 0 63) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 57) (.exec 0x1122c8 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1122c8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x138)) s (0x1122c8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1122c8 0 (.sib 4 none 0 (.d32 0x138))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 58) (.exec 0x1122d0 (StorePre 0x1122d0 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x1122d0 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1122d0 4 0 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 59) (.exec 0x1122d4 (fun s => s.RIP = 0x1122d4) (leaR64Effect 0x1122d4 1 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.out 0x1122d9 (movR64R64Effect 0x1122d9 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[15]
    (.letOp (n := 61) (.exec 0x1122d9 (fun s => s.RIP = 0x1122d9) (movR64R64Effect 0x1122d9 0 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 62) (.out 0x1122dc (shrR64Effect 0x1122dc 4 0 63) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[60]
    (.letOp (n := 63) (.exec 0x1122dc (fun s => s.RIP = 0x1122dc) (shrR64Effect 0x1122dc 4 0 63) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[60]
    (.letOp (n := 64) (.exec 0x1122e0 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1122e0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x1122e0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1122e0 0 (.sib 4 none 0 (.d32 0x140))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.exec 0x1122e8 (StorePre 0x1122e8 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x1122e8 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1122e8 4 0 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 66) (.out 0x1122ec (leaR64Effect 0x1122ec 7 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 67) (.exec 0x1122ec (fun s => s.RIP = 0x1122ec) (leaR64Effect 0x1122ec 7 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.out 0x1122f4 (leaR64Effect 0x1122f4 6 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 69) (.exec 0x1122f4 (fun s => s.RIP = 0x1122f4) (leaR64Effect 0x1122f4 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.out 0x1122f9 (leaR64Effect 0x1122f9 2 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 71) (.exec 0x1122f9 (fun s => s.RIP = 0x1122f9) (leaR64Effect 0x1122f9 2 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.out 0x1122fe (movR64R64Effect 0x1122fe 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 3] []) (.reg (.gpr 1))) #v[3]
    (.letOp (n := 73) (.exec 0x1122fe (fun s => s.RIP = 0x1122fe) (movR64R64Effect 0x1122fe 1 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 74) (.out 0x112301 (movR64R64Effect 0x112301 8 15) (EffectPart.reads (.reg (.gpr 8)) [.gpr 15] []) (.reg (.gpr 8))) #v[15]
    (.letOp (n := 75) (.exec 0x112301 (fun s => s.RIP = 0x112301) (movR64R64Effect 0x112301 8 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 76) (.out 0x112304 (movR32R32Effect 0x112304 3 5 9) (EffectPart.reads (.reg (.gpr 5)) [.gpr 9] []) (.reg (.gpr 5))) #v[9]
    (.letOp (n := 77) (.exec 0x112304 (fun s => s.RIP = 0x112304) (movR32R32Effect 0x112304 3 5 9) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 78) (.out 0x112307 (callEffect (fun _ => 0x1115d0) 0x11230c) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 79) (.exec 0x112307 (PushPre 0x112307 5) (callEffect (fun _ => 0x1115d0) 0x11230c) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 80) (.const ⟨64, 0x11230c⟩) #v[]
    (.terminate (.call ⟨.l1170b0, RegMap.args [(0, 62), (1, 72), (2, 70), (3, 3), (4, 78), (5, 76), (6, 68), (7, 66), (8, 74), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)] 81⟩ { target := .l11435c, kept := #v[], arity := rfl, guard := some (Fin.last 80) })))))))))))))))))))))))))))))

def bytes_l114311 : List UInt8 :=
  [0x48, 0x89, 0xD8, 0x48, 0xC1, 0xE8, 0x3F, 0x48, 0x89, 0x84, 0x24, 0x38, 0x01, 0x00, 0x00, 0x88,
    0x44, 0x24, 0x07, 0x48, 0x8D, 0x4C, 0x24, 0x07, 0x4C, 0x89, 0xF8, 0x48, 0xC1, 0xE8, 0x3F, 0x48,
    0x89, 0x84, 0x24, 0x40, 0x01, 0x00, 0x00, 0x88, 0x44, 0x24, 0x07, 0x48, 0x8D, 0xBC, 0x24, 0xB0,
    0x00, 0x00, 0x00, 0x48, 0x8D, 0x74, 0x24, 0x08, 0x48, 0x8D, 0x54, 0x24, 0x30, 0x48, 0x89, 0xD9,
    0x4D, 0x89, 0xF8, 0x44, 0x89, 0xCD, 0xE8, 0xC4, 0xF2, 0xFF, 0xFF]

theorem code_l114311 : ∀ x ∈ codeRange 0x1122c1 bytes_l114311, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x122c1 75 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11435c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11230c (movR64R64Effect 0x11230c 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[13]
    (.letOp (n := 54) (.exec 0x11230c (fun s => s.RIP = 0x11230c) (movR64R64Effect 0x11230c 0 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 55) (.out 0x11230f (shrR64Effect 0x11230f 4 0 63) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x11230f (fun s => s.RIP = 0x11230f) (shrR64Effect 0x11230f 4 0 63) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 57) (.exec 0x112313 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112313 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x148)) s (0x112313 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x112313 0 (.sib 4 none 0 (.d32 0x148))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 58) (.exec 0x11231b (StorePre 0x11231b 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x11231b + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x11231b 4 0 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 59) (.out 0x11231f (leaR64Effect 0x11231f 0 (.sib 4 none 0 (.d8 0x7))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x11231f (fun s => s.RIP = 0x11231f) (leaR64Effect 0x11231f 0 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x112324 (movR64R64Effect 0x112324 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[14]
    (.letOp (n := 62) (.exec 0x112324 (fun s => s.RIP = 0x112324) (movR64R64Effect 0x112324 1 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 63) (.out 0x112327 (shrR64Effect 0x112327 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[61]
    (.letOp (n := 64) (.exec 0x112327 (fun s => s.RIP = 0x112327) (shrR64Effect 0x112327 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[61]
    (.letOp (n := 65) (.exec 0x11232b (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x11232b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x11232b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11232b 1 (.sib 4 none 0 (.d32 0x130))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[63, 4]
    (.letOp (n := 66) (.exec 0x112333 (StorePre 0x112333 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x112333 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x112333 4 1 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[63, 4]
    (.letOp (n := 67) (.out 0x112337 (leaR64Effect 0x112337 7 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 68) (.exec 0x112337 (fun s => s.RIP = 0x112337) (leaR64Effect 0x112337 7 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.out 0x11233f (leaR64Effect 0x11233f 6 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 70) (.exec 0x11233f (fun s => s.RIP = 0x11233f) (leaR64Effect 0x11233f 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.out 0x112344 (leaR64Effect 0x112344 2 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 72) (.exec 0x112344 (fun s => s.RIP = 0x112344) (leaR64Effect 0x112344 2 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.out 0x112349 (movR64R64Effect 0x112349 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 13] []) (.reg (.gpr 1))) #v[13]
    (.letOp (n := 74) (.exec 0x112349 (fun s => s.RIP = 0x112349) (movR64R64Effect 0x112349 1 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 75) (.out 0x11234c (movR64R64Effect 0x11234c 8 14) (EffectPart.reads (.reg (.gpr 8)) [.gpr 14] []) (.reg (.gpr 8))) #v[14]
    (.letOp (n := 76) (.exec 0x11234c (fun s => s.RIP = 0x11234c) (movR64R64Effect 0x11234c 8 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 77) (.out 0x11234f (movR32R32Effect 0x11234f 3 9 5) (EffectPart.reads (.reg (.gpr 9)) [.gpr 5] []) (.reg (.gpr 9))) #v[5]
    (.letOp (n := 78) (.exec 0x11234f (fun s => s.RIP = 0x11234f) (movR32R32Effect 0x11234f 3 9 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 79) (.out 0x112352 (callEffect (fun _ => 0x1115d0) 0x112357) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 80) (.exec 0x112352 (PushPre 0x112352 5) (callEffect (fun _ => 0x1115d0) 0x112357) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 81) (.const ⟨64, 0x112357⟩) #v[]
    (.terminate (.call ⟨.l1170b0, RegMap.args [(0, 59), (1, 73), (2, 71), (3, 3), (4, 79), (5, 5), (6, 69), (7, 67), (8, 75), (9, 77), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)] 82⟩ { target := .l1143a7, kept := #v[], arity := rfl, guard := some (Fin.last 81) }))))))))))))))))))))))))))))))

def bytes_l11435c : List UInt8 :=
  [0x4C, 0x89, 0xE8, 0x48, 0xC1, 0xE8, 0x3F, 0x48, 0x89, 0x84, 0x24, 0x48, 0x01, 0x00, 0x00, 0x88,
    0x44, 0x24, 0x07, 0x48, 0x8D, 0x44, 0x24, 0x07, 0x4C, 0x89, 0xF1, 0x48, 0xC1, 0xE9, 0x3F, 0x48,
    0x89, 0x8C, 0x24, 0x30, 0x01, 0x00, 0x00, 0x88, 0x4C, 0x24, 0x07, 0x48, 0x8D, 0xBC, 0x24, 0xD8,
    0x00, 0x00, 0x00, 0x48, 0x8D, 0x74, 0x24, 0x08, 0x48, 0x8D, 0x54, 0x24, 0x30, 0x4C, 0x89, 0xE9,
    0x4D, 0x89, 0xF0, 0x41, 0x89, 0xE9, 0xE8, 0x79, 0xF2, 0xFF, 0xFF]

theorem code_l11435c : ∀ x ∈ codeRange 0x11230c bytes_l11435c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1230c 75 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1143a7_1 : Block Op Label signature Reg.count 84 :=
  .letOp (n := 84) (.exec 0x1123c7 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1123c7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1123c7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1123c7 0 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[82, 4]
    (.terminate (.br ⟨.l11441c, RegMap.args [(0, 82), (1, 72), (2, 68), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)] 85⟩))

def bytes_l1143a7_1 : List UInt8 :=
  [0x48, 0x89, 0x44, 0x24, 0x50]

theorem code_l1143a7_1 : ∀ x ∈ codeRange 0x1123c7 bytes_l1143a7_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x123c7 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1143a7 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x112357 (movR64M64Effect 0x112357 0 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x112357 (LoadPre 0x112357 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x112357 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x112357 0 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x11235f (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x11235f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11235f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11235f 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x112364 (movR64M64Effect 0x112364 0 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x112364 (LoadPre 0x112364 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x112364 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x112364 0 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x11236c (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x11236c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11236c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11236c 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x112371 (movR64M64Effect 0x112371 0 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x112371 (LoadPre 0x112371 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x112371 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x112371 0 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x112379 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112379 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x112379 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x112379 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x11237e (movR64M64Effect 0x11237e 0 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x11237e (LoadPre 0x11237e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x11237e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11237e 0 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x112386 (movR64M64Effect 0x112386 1 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x112386 (LoadPre 0x112386 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x112386 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x112386 1 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x11238e (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x11238e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11238e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11238e 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x112393 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112393 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x112393 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x112393 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x112398 (leaR64Effect 0x112398 2 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 69) (.exec 0x112398 (fun s => s.RIP = 0x112398) (leaR64Effect 0x112398 2 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.out 0x1123a0 (movR64M64Effect 0x1123a0 0 (.base 2 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[68]
    (.letOp (n := 71) (.exec 0x1123a0 (LoadPre 0x1123a0 (fun s => AddrMode.addr (.base 2 .none) s (0x1123a0 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1123a0 0 (.base 2 .none)) (Reg.operands [.gpr 2] [])) #v[68]
    (.letOp (n := 72) (.out 0x1123a3 (movR64M64Effect 0x1123a3 1 (.base 2 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[68]
    (.letOp (n := 73) (.exec 0x1123a3 (LoadPre 0x1123a3 (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x1123a3 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1123a3 1 (.base 2 (.d8 0x8))) (Reg.operands [.gpr 2] [])) #v[68]
    (.letOp (n := 74) (.exec 0x1123a7 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1123a7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1123a7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1123a7 0 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[70, 4]
    (.letOp (n := 75) (.exec 0x1123ac (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1123ac 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1123ac + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1123ac 1 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[72, 4]
    (.letOp (n := 76) (.out 0x1123b1 (movR64M64Effect 0x1123b1 0 (.base 2 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[68]
    (.letOp (n := 77) (.exec 0x1123b1 (LoadPre 0x1123b1 (fun s => AddrMode.addr (.base 2 (.d8 0x10)) s (0x1123b1 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1123b1 0 (.base 2 (.d8 0x10))) (Reg.operands [.gpr 2] [])) #v[68]
    (.letOp (n := 78) (.exec 0x1123b5 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1123b5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1123b5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1123b5 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[76, 4]
    (.letOp (n := 79) (.out 0x1123ba (movR64M64Effect 0x1123ba 0 (.base 2 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[68]
    (.letOp (n := 80) (.exec 0x1123ba (LoadPre 0x1123ba (fun s => AddrMode.addr (.base 2 (.d8 0x18)) s (0x1123ba + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1123ba 0 (.base 2 (.d8 0x18))) (Reg.operands [.gpr 2] [])) #v[68]
    (.letOp (n := 81) (.exec 0x1123be (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1123be 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1123be + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1123be 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[79, 4]
    (.letOp (n := 82) (.out 0x1123c3 (movR64M64Effect 0x1123c3 0 (.base 2 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[68]
    (.letOp (n := 83) (.exec 0x1123c3 (LoadPre 0x1123c3 (fun s => AddrMode.addr (.base 2 (.d8 0x20)) s (0x1123c3 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1123c3 0 (.base 2 (.d8 0x20))) (Reg.operands [.gpr 2] [])) #v[68]
    (b_l1143a7_1)))))))))))))))))))))))))))))))

def bytes_l1143a7 : List UInt8 :=
  [0x48, 0x8B, 0x84, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x28, 0x48, 0x8B, 0x84,
    0x24, 0xC8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x84, 0x24, 0xC0, 0x00,
    0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x48,
    0x8B, 0x8C, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x4C, 0x24, 0x10, 0x48, 0x89, 0x44, 0x24,
    0x08, 0x48, 0x8D, 0x94, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x02, 0x48, 0x8B, 0x4A, 0x08,
    0x48, 0x89, 0x44, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x38, 0x48, 0x8B, 0x42, 0x10, 0x48, 0x89,
    0x44, 0x24, 0x40, 0x48, 0x8B, 0x42, 0x18, 0x48, 0x89, 0x44, 0x24, 0x48, 0x48, 0x8B, 0x42, 0x20] ++ bytes_l1143a7_1

theorem code_l1143a7 : ∀ x ∈ codeRange 0x112357 bytes_l1143a7, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x12357 112 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1143a7_1

@[cfg_block] def b_l11441c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1123cc (movR64M64Effect 0x1123cc 0 (.sib 4 none 0 (.d32 0x138))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1123cc (LoadPre 0x1123cc (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x138)) s (0x1123cc + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1123cc 0 (.sib 4 none 0 (.d32 0x138))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x1123d4 (StorePre 0x1123d4 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x1123d4 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1123d4 4 0 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x1123d8 (leaR64Effect 0x1123d8 0 (.sib 4 none 0 (.d8 0x7))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x1123d8 (fun s => s.RIP = 0x1123d8) (leaR64Effect 0x1123d8 0 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.out 0x1123dd (movR64M64Effect 0x1123dd 1 (.sib 4 none 0 (.d32 0x140))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 59) (.exec 0x1123dd (LoadPre 0x1123dd (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x1123dd + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1123dd 1 (.sib 4 none 0 (.d32 0x140))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.exec 0x1123e5 (StorePre 0x1123e5 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x1123e5 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1123e5 4 1 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[58, 4]
    (.letOp (n := 61) (.out 0x1123e9 (leaR64Effect 0x1123e9 7 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 62) (.exec 0x1123e9 (fun s => s.RIP = 0x1123e9) (leaR64Effect 0x1123e9 7 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x1123f1 (leaR64Effect 0x1123f1 6 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 64) (.exec 0x1123f1 (fun s => s.RIP = 0x1123f1) (leaR64Effect 0x1123f1 6 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x1123f6 (leaR64Effect 0x1123f6 2 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 66) (.exec 0x1123f6 (fun s => s.RIP = 0x1123f6) (leaR64Effect 0x1123f6 2 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x1123fe (movR64R64Effect 0x1123fe 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 3] []) (.reg (.gpr 1))) #v[3]
    (.letOp (n := 68) (.exec 0x1123fe (fun s => s.RIP = 0x1123fe) (movR64R64Effect 0x1123fe 1 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 69) (.out 0x112401 (movR64R64Effect 0x112401 8 15) (EffectPart.reads (.reg (.gpr 8)) [.gpr 15] []) (.reg (.gpr 8))) #v[15]
    (.letOp (n := 70) (.exec 0x112401 (fun s => s.RIP = 0x112401) (movR64R64Effect 0x112401 8 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 71) (.out 0x112404 (movR32R32Effect 0x112404 3 9 5) (EffectPart.reads (.reg (.gpr 9)) [.gpr 5] []) (.reg (.gpr 9))) #v[5]
    (.letOp (n := 72) (.exec 0x112404 (fun s => s.RIP = 0x112404) (movR32R32Effect 0x112404 3 9 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 73) (.out 0x112407 (movR64M64Effect 0x112407 15 (.sib 4 none 0 (.d32 0x128))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 74) (.exec 0x112407 (LoadPre 0x112407 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x112407 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x112407 15 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.out 0x11240f (pushR64Effect 0x11240f 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[4, 73]
    (.letOp (n := 76) (.exec 0x11240f (PushPre 0x11240f 2) (pushR64Effect 0x11240f 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[4, 73]
    (.letOp (n := 77) (.out 0x112411 (movR64M64Effect 0x112411 3 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[75]
    (.letOp (n := 78) (.exec 0x112411 (LoadPre 0x112411 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x112411 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x112411 3 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[75]
    (.letOp (n := 79) (.out 0x112416 (pushR64Effect 0x112416 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[75, 77]
    (.letOp (n := 80) (.exec 0x112416 (PushPre 0x112416 1) (pushR64Effect 0x112416 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[75, 77]
    (.letOp (n := 81) (.out 0x112417 (callEffect (fun _ => 0x1116c0) 0x11241c) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[79]
    (.letOp (n := 82) (.exec 0x112417 (PushPre 0x112417 5) (callEffect (fun _ => 0x1116c0) 0x11241c) (Reg.operands [.gpr 4] [])) #v[79]
    (.letOp (n := 83) (.const ⟨64, 0x11241c⟩) #v[]
    (.terminate (.call ⟨.l1171a0, RegMap.args [(0, 56), (1, 67), (2, 65), (3, 77), (4, 81), (5, 5), (6, 63), (7, 61), (8, 69), (9, 71), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 73), (22, 22), (39, 39), (51, 51)] 84⟩ { target := .l11446c, kept := #v[], arity := rfl, guard := some (Fin.last 83) }))))))))))))))))))))))))))))))))

def bytes_l11441c : List UInt8 :=
  [0x48, 0x8B, 0x84, 0x24, 0x38, 0x01, 0x00, 0x00, 0x88, 0x44, 0x24, 0x07, 0x48, 0x8D, 0x44, 0x24,
    0x07, 0x48, 0x8B, 0x8C, 0x24, 0x40, 0x01, 0x00, 0x00, 0x88, 0x4C, 0x24, 0x07, 0x48, 0x8D, 0xBC,
    0x24, 0xB0, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x74, 0x24, 0x60, 0x48, 0x8D, 0x94, 0x24, 0x88, 0x00,
    0x00, 0x00, 0x48, 0x89, 0xD9, 0x4D, 0x89, 0xF8, 0x41, 0x89, 0xE9, 0x4C, 0x8B, 0xBC, 0x24, 0x28,
    0x01, 0x00, 0x00, 0x41, 0x57, 0x48, 0x8B, 0x5C, 0x24, 0x60, 0x53, 0xE8, 0xA4, 0xF2, 0xFF, 0xFF]

theorem code_l11441c : ∀ x ∈ codeRange 0x1123cc bytes_l11441c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x123cc 80 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11446c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11241c (addR64Imm8Effect 0x11241c 4 0x10) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 54) (.exec 0x11241c (fun s => s.RIP = 0x11241c) (addR64Imm8Effect 0x11241c 4 0x10) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x112420 (movR64M64Effect 0x112420 0 (.sib 4 none 0 (.d32 0x148))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x112420 (LoadPre 0x112420 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x148)) s (0x112420 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x112420 0 (.sib 4 none 0 (.d32 0x148))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 57) (.exec 0x112428 (StorePre 0x112428 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x112428 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x112428 4 0 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 53]
    (.letOp (n := 58) (.exec 0x11242c (fun s => s.RIP = 0x11242c) (leaR64Effect 0x11242c 1 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 59) (.out 0x112431 (movR64M64Effect 0x112431 0 (.sib 4 none 0 (.d32 0x130))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 60) (.exec 0x112431 (LoadPre 0x112431 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x112431 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x112431 0 (.sib 4 none 0 (.d32 0x130))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 61) (.exec 0x112439 (StorePre 0x112439 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x112439 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x112439 4 0 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 53]
    (.letOp (n := 62) (.out 0x11243d (leaR64Effect 0x11243d 7 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 63) (.exec 0x11243d (fun s => s.RIP = 0x11243d) (leaR64Effect 0x11243d 7 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 64) (.out 0x112445 (leaR64Effect 0x112445 6 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[53]
    (.letOp (n := 65) (.exec 0x112445 (fun s => s.RIP = 0x112445) (leaR64Effect 0x112445 6 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 66) (.out 0x11244a (leaR64Effect 0x11244a 2 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[53]
    (.letOp (n := 67) (.exec 0x11244a (fun s => s.RIP = 0x11244a) (leaR64Effect 0x11244a 2 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 68) (.out 0x112452 (movR64R64Effect 0x112452 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 13] []) (.reg (.gpr 1))) #v[13]
    (.letOp (n := 69) (.exec 0x112452 (fun s => s.RIP = 0x112452) (movR64R64Effect 0x112452 1 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 70) (.out 0x112455 (movR64R64Effect 0x112455 8 14) (EffectPart.reads (.reg (.gpr 8)) [.gpr 14] []) (.reg (.gpr 8))) #v[14]
    (.letOp (n := 71) (.exec 0x112455 (fun s => s.RIP = 0x112455) (movR64R64Effect 0x112455 8 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x112458 (movR32R32Effect 0x112458 3 9 5) (EffectPart.reads (.reg (.gpr 9)) [.gpr 5] []) (.reg (.gpr 9))) #v[5]
    (.letOp (n := 73) (.exec 0x112458 (fun s => s.RIP = 0x112458) (movR32R32Effect 0x112458 3 9 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 74) (.out 0x11245b (pushR64Effect 0x11245b 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 75) (.exec 0x11245b (PushPre 0x11245b 2) (pushR64Effect 0x11245b 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 76) (.out 0x11245d (pushR64Effect 0x11245d 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[74, 3]
    (.letOp (n := 77) (.exec 0x11245d (PushPre 0x11245d 1) (pushR64Effect 0x11245d 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[74, 3]
    (.letOp (n := 78) (.out 0x11245e (callEffect (fun _ => 0x1116c0) 0x112463) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[76]
    (.letOp (n := 79) (.exec 0x11245e (PushPre 0x11245e 5) (callEffect (fun _ => 0x1116c0) 0x112463) (Reg.operands [.gpr 4] [])) #v[76]
    (.letOp (n := 80) (.const ⟨64, 0x112463⟩) #v[]
    (.terminate (.call ⟨.l1171a0, RegMap.args [(0, 59), (1, 68), (2, 66), (3, 3), (4, 78), (5, 5), (6, 64), (7, 62), (8, 70), (9, 72), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)] 81⟩ { target := .l1144b3, kept := #v[], arity := rfl, guard := some (Fin.last 80) })))))))))))))))))))))))))))))

def bytes_l11446c : List UInt8 :=
  [0x48, 0x83, 0xC4, 0x10, 0x48, 0x8B, 0x84, 0x24, 0x48, 0x01, 0x00, 0x00, 0x88, 0x44, 0x24, 0x07,
    0x48, 0x8D, 0x4C, 0x24, 0x07, 0x48, 0x8B, 0x84, 0x24, 0x30, 0x01, 0x00, 0x00, 0x88, 0x44, 0x24,
    0x07, 0x48, 0x8D, 0xBC, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x74, 0x24, 0x60, 0x48, 0x8D,
    0x94, 0x24, 0x88, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xE9, 0x4D, 0x89, 0xF0, 0x41, 0x89, 0xE9, 0x41,
    0x57, 0x53, 0xE8, 0x5D, 0xF2, 0xFF, 0xFF]

theorem code_l11446c : ∀ x ∈ codeRange 0x11241c bytes_l11446c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1241c 71 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1144b3_1 : Block Op Label signature Reg.count 84 :=
  .letOp (n := 84) (.out 0x1124e2 (movR64M64Effect 0x1124e2 0 (.base 2 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[70]
    (.letOp (n := 85) (.exec 0x1124e2 (LoadPre 0x1124e2 (fun s => AddrMode.addr (.base 2 (.d8 0x20)) s (0x1124e2 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1124e2 0 (.base 2 (.d8 0x20))) (Reg.operands [.gpr 2] [])) #v[70]
    (.letOp (n := 86) (.exec 0x1124e6 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1124e6 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x1124e6 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1124e6 0 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[84, 53]
    (.terminate (.br ⟨.l11453e, RegMap.args [(0, 84), (1, 74), (2, 70), (3, 3), (4, 53), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)] 87⟩))))

def bytes_l1144b3_1 : List UInt8 :=
  [0x48, 0x8B, 0x42, 0x20, 0x48, 0x89, 0x84, 0x24, 0xA8, 0x00, 0x00, 0x00]

theorem code_l1144b3_1 : ∀ x ∈ codeRange 0x1124e2 bytes_l1144b3_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x124e2 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1144b3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x112463 (addR64Imm8Effect 0x112463 4 0x10) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 54) (.exec 0x112463 (fun s => s.RIP = 0x112463) (addR64Imm8Effect 0x112463 4 0x10) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x112467 (movR64M64Effect 0x112467 0 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x112467 (LoadPre 0x112467 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x112467 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x112467 0 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 57) (.exec 0x11246f (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x11246f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x11246f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11246f 0 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 53]
    (.letOp (n := 58) (.out 0x112477 (movR64M64Effect 0x112477 0 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 59) (.exec 0x112477 (LoadPre 0x112477 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x112477 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x112477 0 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 60) (.exec 0x11247f (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x11247f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x11247f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11247f 0 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[58, 53]
    (.letOp (n := 61) (.out 0x112484 (movR64M64Effect 0x112484 0 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 62) (.exec 0x112484 (LoadPre 0x112484 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x112484 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x112484 0 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 63) (.exec 0x11248c (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x11248c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x11248c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11248c 0 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[61, 53]
    (.letOp (n := 64) (.out 0x112491 (movR64M64Effect 0x112491 0 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 65) (.exec 0x112491 (LoadPre 0x112491 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x112491 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x112491 0 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 66) (.out 0x112499 (movR64M64Effect 0x112499 1 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 67) (.exec 0x112499 (LoadPre 0x112499 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x112499 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x112499 1 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 68) (.exec 0x1124a1 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1124a1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x1124a1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1124a1 1 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[66, 53]
    (.letOp (n := 69) (.exec 0x1124a6 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1124a6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1124a6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1124a6 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[64, 53]
    (.letOp (n := 70) (.out 0x1124ab (leaR64Effect 0x1124ab 2 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[53]
    (.letOp (n := 71) (.exec 0x1124ab (fun s => s.RIP = 0x1124ab) (leaR64Effect 0x1124ab 2 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 72) (.out 0x1124b3 (movR64M64Effect 0x1124b3 0 (.base 2 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[70]
    (.letOp (n := 73) (.exec 0x1124b3 (LoadPre 0x1124b3 (fun s => AddrMode.addr (.base 2 .none) s (0x1124b3 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1124b3 0 (.base 2 .none)) (Reg.operands [.gpr 2] [])) #v[70]
    (.letOp (n := 74) (.out 0x1124b6 (movR64M64Effect 0x1124b6 1 (.base 2 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[70]
    (.letOp (n := 75) (.exec 0x1124b6 (LoadPre 0x1124b6 (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x1124b6 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1124b6 1 (.base 2 (.d8 0x8))) (Reg.operands [.gpr 2] [])) #v[70]
    (.letOp (n := 76) (.exec 0x1124ba (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1124ba 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1124ba + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1124ba 0 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[72, 53]
    (.letOp (n := 77) (.exec 0x1124c2 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1124c2 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x1124c2 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1124c2 1 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[74, 53]
    (.letOp (n := 78) (.out 0x1124ca (movR64M64Effect 0x1124ca 0 (.base 2 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[70]
    (.letOp (n := 79) (.exec 0x1124ca (LoadPre 0x1124ca (fun s => AddrMode.addr (.base 2 (.d8 0x10)) s (0x1124ca + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1124ca 0 (.base 2 (.d8 0x10))) (Reg.operands [.gpr 2] [])) #v[70]
    (.letOp (n := 80) (.exec 0x1124ce (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1124ce 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x1124ce + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1124ce 0 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[78, 53]
    (.letOp (n := 81) (.out 0x1124d6 (movR64M64Effect 0x1124d6 0 (.base 2 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[70]
    (.letOp (n := 82) (.exec 0x1124d6 (LoadPre 0x1124d6 (fun s => AddrMode.addr (.base 2 (.d8 0x18)) s (0x1124d6 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1124d6 0 (.base 2 (.d8 0x18))) (Reg.operands [.gpr 2] [])) #v[70]
    (.letOp (n := 83) (.exec 0x1124da (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1124da 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x1124da + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1124da 0 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[81, 53]
    (b_l1144b3_1)))))))))))))))))))))))))))))))

def bytes_l1144b3 : List UInt8 :=
  [0x48, 0x83, 0xC4, 0x10, 0x48, 0x8B, 0x84, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24,
    0x80, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24,
    0x78, 0x48, 0x8B, 0x84, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x70, 0x48, 0x8B,
    0x84, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x8C, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x48, 0x89,
    0x4C, 0x24, 0x68, 0x48, 0x89, 0x44, 0x24, 0x60, 0x48, 0x8D, 0x94, 0x24, 0xD8, 0x00, 0x00, 0x00,
    0x48, 0x8B, 0x02, 0x48, 0x8B, 0x4A, 0x08, 0x48, 0x89, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48,
    0x89, 0x8C, 0x24, 0x90, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x42, 0x10, 0x48, 0x89, 0x84, 0x24, 0x98,
    0x00, 0x00, 0x00, 0x48, 0x8B, 0x42, 0x18, 0x48, 0x89, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00] ++ bytes_l1144b3_1

theorem code_l1144b3 : ∀ x ∈ codeRange 0x112463 bytes_l1144b3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x12463 127 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1144b3_1

@[cfg_block] def b_l11453e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1124ee (movR64M64Effect 0x1124ee 6 (.sib 4 none 0 (.d32 0x150))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 54) (.exec 0x1124ee (LoadPre 0x1124ee (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x150)) s (0x1124ee + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1124ee 6 (.sib 4 none 0 (.d32 0x150))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1124f6 (subR32R32Effect 0x1124f6 2 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 5] []) (.reg (.gpr 6))) #v[53, 5]
    (.letOp (n := 56) (.out 0x1124f6 (subR32R32Effect 0x1124f6 2 6 5) (EffectPart.reads (.flag .ZF) [.gpr 6, .gpr 5] []) (.flag .ZF)) #v[53, 5]
    (.letOp (n := 57) (.exec 0x1124f6 (fun s => s.RIP = 0x1124f6) (subR32R32Effect 0x1124f6 2 6 5) (Reg.operands [.gpr 6, .gpr 5] [])) #v[53, 5]
    (.letOp (n := 58) (.pure (condOp 4)) #v[56]
    (.terminate (.condBr (Fin.last 58) ⟨.l114698, RegMap.args [(3, 3), (4, 4), (5, 5), (6, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 56), (22, 22), (39, 39), (51, 51)] 59⟩ ⟨.l11454e, RegMap.args [(3, 3), (4, 4), (5, 5), (6, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 56), (22, 22), (39, 39), (51, 51)] 59⟩)))))))

def bytes_l11453e : List UInt8 :=
  [0x48, 0x8B, 0xB4, 0x24, 0x50, 0x01, 0x00, 0x00, 0x29, 0xEE, 0x0F, 0x84, 0x4A, 0x01, 0x00, 0x00]

theorem code_l11453e : ∀ x ∈ codeRange 0x1124ee bytes_l11453e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x124ee 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11454e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1124fe (movR64M64Effect 0x1124fe 2 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 54) (.exec 0x1124fe (LoadPre 0x1124fe (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1124fe + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1124fe 2 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x112503 (testR64R64Effect 0x112503 2 2) (EffectPart.reads (.flag .ZF) [.gpr 2, .gpr 2] []) (.flag .ZF)) #v[53, 53]
    (.letOp (n := 56) (.exec 0x112503 (fun s => s.RIP = 0x112503) (testR64R64Effect 0x112503 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[53, 53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l114574, RegMap.args [(2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 55), (22, 22), (39, 39), (51, 51)] 58⟩ ⟨.l114558, RegMap.args [(2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 55), (22, 22), (39, 39), (51, 51)] 58⟩))))))

def bytes_l11454e : List UInt8 :=
  [0x48, 0x8B, 0x54, 0x24, 0x30, 0x48, 0x85, 0xD2, 0x75, 0x1C]

theorem code_l11454e : ∀ x ∈ codeRange 0x1124fe bytes_l11454e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x124fe 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l114558 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x112508 (cmpMImm8Effect 0x112508 6 64 (.sib 4 none 0 (.d8 0x38)) 0x0) (EffectPart.reads (.flag .ZF) [.gpr 4] []) (.flag .ZF)) #v[4]
    (.letOp (n := 54) (.exec 0x112508 (LoadPre 0x112508 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x112508 + BitVec.ofNat 64 6)) 8) (cmpMImm8Effect 0x112508 6 64 (.sib 4 none 0 (.d8 0x38)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l114574, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 53), (22, 22), (39, 39), (51, 51)] 56⟩ ⟨.l114560, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 53), (22, 22), (39, 39), (51, 51)] 56⟩))))

def bytes_l114558 : List UInt8 :=
  [0x48, 0x83, 0x7C, 0x24, 0x38, 0x00, 0x75, 0x14]

theorem code_l114558 : ∀ x ∈ codeRange 0x112508 bytes_l114558, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x12508 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l114560 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x112510 (cmpMImm8Effect 0x112510 6 64 (.sib 4 none 0 (.d8 0x40)) 0x0) (EffectPart.reads (.flag .ZF) [.gpr 4] []) (.flag .ZF)) #v[4]
    (.letOp (n := 54) (.exec 0x112510 (LoadPre 0x112510 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x112510 + BitVec.ofNat 64 6)) 8) (cmpMImm8Effect 0x112510 6 64 (.sib 4 none 0 (.d8 0x40)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l114574, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 53), (22, 22), (39, 39), (51, 51)] 56⟩ ⟨.l114568, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 53), (22, 22), (39, 39), (51, 51)] 56⟩))))

def bytes_l114560 : List UInt8 :=
  [0x48, 0x83, 0x7C, 0x24, 0x40, 0x00, 0x75, 0x0C]

theorem code_l114560 : ∀ x ∈ codeRange 0x112510 bytes_l114560, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x12510 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l114568 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x112518 (cmpMImm8Effect 0x112518 6 64 (.sib 4 none 0 (.d8 0x48)) 0x0) (EffectPart.reads (.flag .ZF) [.gpr 4] []) (.flag .ZF)) #v[4]
    (.letOp (n := 54) (.exec 0x112518 (LoadPre 0x112518 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x112518 + BitVec.ofNat 64 6)) 8) (cmpMImm8Effect 0x112518 6 64 (.sib 4 none 0 (.d8 0x48)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l114698, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 53), (22, 22), (39, 39), (51, 51)] 56⟩ ⟨.l114574, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 53), (22, 22), (39, 39), (51, 51)] 56⟩))))

def bytes_l114568 : List UInt8 :=
  [0x48, 0x83, 0x7C, 0x24, 0x48, 0x00, 0x0F, 0x84, 0x24, 0x01, 0x00, 0x00]

theorem code_l114568 : ∀ x ∈ codeRange 0x112518 bytes_l114568, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x12518 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l114574 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x112524 (movR32R32Effect 0x112524 2 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 54) (.exec 0x112524 (fun s => s.RIP = 0x112524) (movR32R32Effect 0x112524 2 0 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 55) (.out 0x112526 (notR32Effect 0x112526 2 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x112526 (fun s => s.RIP = 0x112526) (notR32Effect 0x112526 2 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x112528 (leaR32Effect 0x112528 3 1 (.base 6 (.d8 0xc2))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[6]
    (.letOp (n := 58) (.exec 0x112528 (fun s => s.RIP = 0x112528) (leaR32Effect 0x112528 3 1 (.base 6 (.d8 0xc2))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 59) (.out 0x11252b (andR32R32Effect 0x11252b 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[57, 55]
    (.letOp (n := 60) (.exec 0x11252b (fun s => s.RIP = 0x11252b) (andR32R32Effect 0x11252b 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[57, 55]
    (.letOp (n := 61) (.out 0x11252d (shrR32Effect 0x11252d 3 1 31) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[59]
    (.letOp (n := 62) (.exec 0x11252d (fun s => s.RIP = 0x11252d) (shrR32Effect 0x11252d 3 1 31) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[59]
    (.letOp (n := 63) (.exec 0x112530 (StorePre 0x112530 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x112530 + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x112530 7 1 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.exec 0x112537 (fun s => s.RIP = 0x112537) (leaR64Effect 0x112537 7 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x11253f (movzxR32M8Effect 0x11253f 8 0 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 66) (.exec 0x11253f (LoadPre 0x11253f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x11253f + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x11253f 8 0 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x112547 (negR32Effect 0x112547 2 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 68) (.exec 0x112547 (fun s => s.RIP = 0x112547) (negR32Effect 0x112547 2 0) (Reg.operands [.gpr 0] [])) #v[65]
    (.letOp (n := 69) (.exec 0x112549 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112549 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x150)) s (0x112549 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x112549 6 (.sib 4 none 0 (.d32 0x150))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[6, 4]
    (.letOp (n := 70) (.out 0x112551 (movR32R32Effect 0x112551 3 9 6) (EffectPart.reads (.reg (.gpr 9)) [.gpr 6] []) (.reg (.gpr 9))) #v[6]
    (.letOp (n := 71) (.exec 0x112551 (fun s => s.RIP = 0x112551) (movR32R32Effect 0x112551 3 9 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 72) (.out 0x112554 (xorR32Imm8Effect 0x112554 4 9 0x3e) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[70]
    (.letOp (n := 73) (.exec 0x112554 (fun s => s.RIP = 0x112554) (xorR32Imm8Effect 0x112554 4 9 0x3e) (Reg.operands [.gpr 9] [])) #v[70]
    (.letOp (n := 74) (.out 0x112558 (andR32R32Effect 0x112558 3 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0] []) (.reg (.gpr 9))) #v[72, 67]
    (.letOp (n := 75) (.exec 0x112558 (fun s => s.RIP = 0x112558) (andR32R32Effect 0x112558 3 9 0) (Reg.operands [.gpr 9, .gpr 0] [])) #v[72, 67]
    (.letOp (n := 76) (.out 0x11255b (xorR32Imm8Effect 0x11255b 4 9 0x3e) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[74]
    (.letOp (n := 77) (.out 0x11255b (xorR32Imm8Effect 0x11255b 4 9 0x3e) (EffectPart.reads (.flag .ZF) [.gpr 9] []) (.flag .ZF)) #v[74]
    (.letOp (n := 78) (.exec 0x11255b (fun s => s.RIP = 0x11255b) (xorR32Imm8Effect 0x11255b 4 9 0x3e) (Reg.operands [.gpr 9] [])) #v[74]
    (.terminate (.br ⟨.l1145af, RegMap.args [(0, 67), (1, 61), (2, 2), (4, 4), (6, 6), (9, 76), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 77), (22, 22), (39, 39), (51, 51)] 79⟩)))))))))))))))))))))))))))

def bytes_l114574 : List UInt8 :=
  [0x89, 0xF0, 0xF7, 0xD0, 0x8D, 0x4E, 0xC2, 0x21, 0xC1, 0xC1, 0xE9, 0x1F, 0x88, 0x8C, 0x24, 0xB0,
    0x00, 0x00, 0x00, 0x48, 0x8D, 0xBC, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x0F, 0xB6, 0x84, 0x24, 0xB0,
    0x00, 0x00, 0x00, 0xF7, 0xD8, 0x48, 0x89, 0xB4, 0x24, 0x50, 0x01, 0x00, 0x00, 0x41, 0x89, 0xF1,
    0x41, 0x83, 0xF1, 0x3E, 0x41, 0x21, 0xC1, 0x41, 0x83, 0xF1, 0x3E]

theorem code_l114574 : ∀ x ∈ codeRange 0x112524 bytes_l114574, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x12524 59 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1145af : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11255f (movR64M64Effect 0x11255f 6 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 54) (.exec 0x11255f (LoadPre 0x11255f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11255f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11255f 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x112564 (movzxR32M8Effect 0x112564 5 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 56) (.exec 0x112564 (LoadPre 0x112564 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x112564 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x112564 5 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x112569 (StorePre 0x112569 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x112569 + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x112569 7 0 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 58) (.out 0x112570 (movzxR32M8Effect 0x112570 8 0 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 59) (.exec 0x112570 (LoadPre 0x112570 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x112570 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x112570 8 0 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.out 0x112578 (movzxR32M8Effect 0x112578 5 1 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 61) (.exec 0x112578 (LoadPre 0x112578 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x112578 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x112578 5 1 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.exec 0x11257d (StorePre 0x11257d 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x11257d + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x11257d 7 1 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[60, 4]
    (.letOp (n := 63) (.pure (condOp 4)) #v[19]
    (.terminate (.condBr (Fin.last 63) ⟨.l114300, RegMap.args [(0, 58), (1, 60), (2, 2), (4, 4), (6, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 19), (22, 22), (39, 39), (51, 51)] 64⟩ ⟨.l1145da, RegMap.args [(0, 58), (1, 60), (2, 2), (4, 4), (6, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 19), (22, 22), (39, 39), (51, 51)] 64⟩))))))))))))

def bytes_l1145af : List UInt8 :=
  [0x48, 0x8B, 0x74, 0x24, 0x08, 0x0F, 0xB6, 0x44, 0x24, 0x28, 0x88, 0x84, 0x24, 0xB0, 0x00, 0x00,
    0x00, 0x0F, 0xB6, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x0F, 0xB6, 0x4C, 0x24, 0x50, 0x88, 0x8C,
    0x24, 0xB0, 0x00, 0x00, 0x00, 0x0F, 0x84, 0x26, 0xFD, 0xFF, 0xFF]

theorem code_l1145af : ∀ x ∈ codeRange 0x11255f bytes_l1145af, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1255f 43 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1145da : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11258a (movzxR32M8Effect 0x11258a 8 1 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x11258a (LoadPre 0x11258a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x11258a + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x11258a 8 1 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.br ⟨.l1145e2, RegMap.args [(0, 0), (1, 53), (2, 2), (4, 4), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (15, 15), (22, 22), (39, 39), (51, 51)] 55⟩)))

def bytes_l1145da : List UInt8 :=
  [0x0F, 0xB6, 0x8C, 0x24, 0xB0, 0x00, 0x00, 0x00]

theorem code_l1145da : ∀ x ∈ codeRange 0x11258a bytes_l1145da, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1258a 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1145e2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x112592 (movR64Imm64Effect 0x112592 8 0x7fffffffffffffff) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 54) (.exec 0x112592 (fun s => s.RIP = 0x112592) (movR64Imm64Effect 0x112592 8 0x7fffffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x11259c (andR64R64Effect 0x11259c 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 8] []) (.reg (.gpr 2))) #v[2, 53]
    (.letOp (n := 56) (.exec 0x11259c (fun s => s.RIP = 0x11259c) (andR64R64Effect 0x11259c 2 8) (Reg.operands [.gpr 2, .gpr 8] [])) #v[2, 53]
    (.letOp (n := 57) (.out 0x11259f (movR64R64Effect 0x11259f 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[55]
    (.letOp (n := 58) (.exec 0x11259f (fun s => s.RIP = 0x11259f) (movR64R64Effect 0x11259f 7 2) (Reg.operands [.gpr 2] [])) #v[55]
    (.letOp (n := 59) (.out 0x1125a2 (negR64Effect 0x1125a2 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[57]
    (.letOp (n := 60) (.exec 0x1125a2 (fun s => s.RIP = 0x1125a2) (negR64Effect 0x1125a2 7) (Reg.operands [.gpr 7] [])) #v[57]
    (.letOp (n := 61) (.out 0x1125a5 (xorR64R64Effect 0x1125a5 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2] []) (.reg (.gpr 7))) #v[59, 55]
    (.letOp (n := 62) (.exec 0x1125a5 (fun s => s.RIP = 0x1125a5) (xorR64R64Effect 0x1125a5 7 2) (Reg.operands [.gpr 7, .gpr 2] [])) #v[59, 55]
    (.letOp (n := 63) (.out 0x1125a8 (negR64Effect 0x1125a8 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1]
    (.letOp (n := 64) (.exec 0x1125a8 (fun s => s.RIP = 0x1125a8) (negR64Effect 0x1125a8 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 65) (.out 0x1125ab (andR64R64Effect 0x1125ab 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[63, 61]
    (.letOp (n := 66) (.exec 0x1125ab (fun s => s.RIP = 0x1125ab) (andR64R64Effect 0x1125ab 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[63, 61]
    (.letOp (n := 67) (.out 0x1125ae (xorR64R64Effect 0x1125ae 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[65, 55]
    (.letOp (n := 68) (.exec 0x1125ae (fun s => s.RIP = 0x1125ae) (xorR64R64Effect 0x1125ae 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[65, 55]
    (.letOp (n := 69) (.out 0x1125b1 (andR64R64Effect 0x1125b1 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 8] []) (.reg (.gpr 6))) #v[6, 53]
    (.letOp (n := 70) (.exec 0x1125b1 (fun s => s.RIP = 0x1125b1) (andR64R64Effect 0x1125b1 6 8) (Reg.operands [.gpr 6, .gpr 8] [])) #v[6, 53]
    (.letOp (n := 71) (.out 0x1125b4 (movR64R64Effect 0x1125b4 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6] []) (.reg (.gpr 2))) #v[69]
    (.letOp (n := 72) (.exec 0x1125b4 (fun s => s.RIP = 0x1125b4) (movR64R64Effect 0x1125b4 2 6) (Reg.operands [.gpr 6] [])) #v[69]
    (.letOp (n := 73) (.out 0x1125b7 (negR64Effect 0x1125b7 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[71]
    (.letOp (n := 74) (.exec 0x1125b7 (fun s => s.RIP = 0x1125b7) (negR64Effect 0x1125b7 2) (Reg.operands [.gpr 2] [])) #v[71]
    (.letOp (n := 75) (.out 0x1125ba (xorR64R64Effect 0x1125ba 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[73, 69]
    (.letOp (n := 76) (.exec 0x1125ba (fun s => s.RIP = 0x1125ba) (xorR64R64Effect 0x1125ba 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[73, 69]
    (.letOp (n := 77) (.out 0x1125bd (negR64Effect 0x1125bd 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 78) (.exec 0x1125bd (fun s => s.RIP = 0x1125bd) (negR64Effect 0x1125bd 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 79) (.out 0x1125c0 (andR64R64Effect 0x1125c0 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[77, 75]
    (.letOp (n := 80) (.exec 0x1125c0 (fun s => s.RIP = 0x1125c0) (andR64R64Effect 0x1125c0 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[77, 75]
    (.letOp (n := 81) (.out 0x1125c3 (xorR64R64Effect 0x1125c3 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[79, 69]
    (.letOp (n := 82) (.exec 0x1125c3 (fun s => s.RIP = 0x1125c3) (xorR64R64Effect 0x1125c3 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[79, 69]
    (.terminate (.br ⟨.l114616, RegMap.args [(0, 81), (1, 67), (2, 75), (4, 4), (6, 69), (7, 61), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (15, 15), (22, 22), (39, 39), (51, 51)] 83⟩)))))))))))))))))))))))))))))))

def bytes_l1145e2 : List UInt8 :=
  [0x49, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F, 0x4C, 0x21, 0xC2, 0x48, 0x89, 0xD7,
    0x48, 0xF7, 0xDF, 0x48, 0x31, 0xD7, 0x48, 0xF7, 0xD9, 0x48, 0x21, 0xF9, 0x48, 0x31, 0xD1, 0x4C,
    0x21, 0xC6, 0x48, 0x89, 0xF2, 0x48, 0xF7, 0xDA, 0x48, 0x31, 0xF2, 0x48, 0xF7, 0xD8, 0x48, 0x21,
    0xD0, 0x48, 0x31, 0xF0]

theorem code_l1145e2 : ∀ x ∈ codeRange 0x112592 bytes_l1145e2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x12592 52 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l114616 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1125c6 (movR32Imm32Effect 0x1125c6 5 3 0x1) (EffectPart.reads (.reg (.gpr 3)) [] []) (.reg (.gpr 3))) #v[]
    (.letOp (n := 54) (.exec 0x1125c6 (fun s => s.RIP = 0x1125c6) (movR32Imm32Effect 0x1125c6 5 3 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x1125cb (movR32R32Effect 0x1125cb 3 2 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9] []) (.reg (.gpr 2))) #v[9]
    (.letOp (n := 56) (.exec 0x1125cb (fun s => s.RIP = 0x1125cb) (movR32R32Effect 0x1125cb 3 2 9) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 57) (.out 0x1125ce (xorR32R32Effect 0x1125ce 3 15 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 15] []) (.reg (.gpr 15))) #v[15, 15]
    (.letOp (n := 58) (.exec 0x1125ce (fun s => s.RIP = 0x1125ce) (xorR32R32Effect 0x1125ce 3 15 15) (Reg.operands [.gpr 15, .gpr 15] [])) #v[15, 15]
    (.letOp (n := 59) (.out 0x1125d1 (xorR32R32Effect 0x1125d1 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[6, 6]
    (.letOp (n := 60) (.exec 0x1125d1 (fun s => s.RIP = 0x1125d1) (xorR32R32Effect 0x1125d1 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 61) (.out 0x1125d3 (movR32Imm32Effect 0x1125d3 5 7 0x1) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 62) (.exec 0x1125d3 (fun s => s.RIP = 0x1125d3) (movR32Imm32Effect 0x1125d3 5 7 0x1) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l114675, RegMap.args [(0, 0), (1, 1), (2, 55), (3, 53), (4, 4), (6, 59), (7, 61), (9, 9), (10, 10), (11, 11), (12, 12), (15, 57), (22, 22), (39, 39), (51, 51)] 63⟩)))))))))))

def bytes_l114616 : List UInt8 :=
  [0xBB, 0x01, 0x00, 0x00, 0x00, 0x44, 0x89, 0xCA, 0x45, 0x31, 0xFF, 0x31, 0xF6, 0xBF, 0x01, 0x00,
    0x00, 0x00, 0xEB, 0x4B]

theorem code_l114616 : ∀ x ∈ codeRange 0x1125c6 bytes_l114616, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x125c6 20 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l114630 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1125e0 (testR64R64Effect 0x1125e0 12 12) (EffectPart.reads (.flag .ZF) [.gpr 12, .gpr 12] []) (.flag .ZF)) #v[12, 12]
    (.letOp (n := 54) (.out 0x1125e0 (testR64R64Effect 0x1125e0 12 12) (EffectPart.reads (.flag .SF) [.gpr 12, .gpr 12] []) (.flag .SF)) #v[12, 12]
    (.letOp (n := 55) (.out 0x1125e0 (testR64R64Effect 0x1125e0 12 12) (EffectPart.reads (.flag .OF) [.gpr 12, .gpr 12] []) (.flag .OF)) #v[12, 12]
    (.letOp (n := 56) (.exec 0x1125e0 (fun s => s.RIP = 0x1125e0) (testR64R64Effect 0x1125e0 12 12) (Reg.operands [.gpr 12, .gpr 12] [])) #v[12, 12]
    (.letOp (n := 57) (.pure (condOp 14)) #v[53, 54, 55]
    (.terminate (.condBr (Fin.last 57) ⟨.l114680, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (15, 15), (19, 53), (20, 54), (21, 55), (22, 22), (39, 39), (51, 51)] 58⟩ ⟨.l114635, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (15, 15), (19, 53), (20, 54), (21, 55), (22, 22), (39, 39), (51, 51)] 58⟩))))))

def bytes_l114630 : List UInt8 :=
  [0x4D, 0x85, 0xE4, 0x7E, 0x4B]

theorem code_l114630 : ∀ x ∈ codeRange 0x1125e0 bytes_l114630, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x125e0 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l114635 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1125e5 (movR64R64Effect 0x1125e5 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 1] []) (.reg (.gpr 8))) #v[1]
    (.letOp (n := 54) (.exec 0x1125e5 (fun s => s.RIP = 0x1125e5) (movR64R64Effect 0x1125e5 8 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 55) (.out 0x1125e8 (subR64R64Effect 0x1125e8 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[53, 0]
    (.letOp (n := 56) (.exec 0x1125e8 (fun s => s.RIP = 0x1125e8) (subR64R64Effect 0x1125e8 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[53, 0]
    (.letOp (n := 57) (.out 0x1125eb (movR32Imm32Effect 0x1125eb 5 0 0x2) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 58) (.exec 0x1125eb (fun s => s.RIP = 0x1125eb) (movR32Imm32Effect 0x1125eb 5 0 0x2) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x1125f0 (subR64R64Effect 0x1125f0 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 12] []) (.reg (.gpr 0))) #v[57, 12]
    (.letOp (n := 60) (.exec 0x1125f0 (fun s => s.RIP = 0x1125f0) (subR64R64Effect 0x1125f0 0 12) (Reg.operands [.gpr 0, .gpr 12] [])) #v[57, 12]
    (.letOp (n := 61) (.out 0x1125f3 (movR64R64Effect 0x1125f3 13 6) (EffectPart.reads (.reg (.gpr 13)) [.gpr 6] []) (.reg (.gpr 13))) #v[6]
    (.letOp (n := 62) (.exec 0x1125f3 (fun s => s.RIP = 0x1125f3) (movR64R64Effect 0x1125f3 13 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 63) (.out 0x1125f6 (subR64R64Effect 0x1125f6 13 3) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 3] []) (.reg (.gpr 13))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x1125f6 (fun s => s.RIP = 0x1125f6) (subR64R64Effect 0x1125f6 13 3) (Reg.operands [.gpr 13, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x1125f9 (movR64R64Effect 0x1125f9 14 7) (EffectPart.reads (.reg (.gpr 14)) [.gpr 7] []) (.reg (.gpr 14))) #v[7]
    (.letOp (n := 66) (.exec 0x1125f9 (fun s => s.RIP = 0x1125f9) (movR64R64Effect 0x1125f9 14 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 67) (.out 0x1125fc (subR64R64Effect 0x1125fc 14 15) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 15] []) (.reg (.gpr 14))) #v[65, 15]
    (.letOp (n := 68) (.exec 0x1125fc (fun s => s.RIP = 0x1125fc) (subR64R64Effect 0x1125fc 14 15) (Reg.operands [.gpr 14, .gpr 15] [])) #v[65, 15]
    (.letOp (n := 69) (.out 0x1125ff (movR64R64Effect 0x1125ff 15 7) (EffectPart.reads (.reg (.gpr 15)) [.gpr 7] []) (.reg (.gpr 15))) #v[7]
    (.letOp (n := 70) (.exec 0x1125ff (fun s => s.RIP = 0x1125ff) (movR64R64Effect 0x1125ff 15 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 71) (.out 0x112602 (movR64R64Effect 0x112602 3 6) (EffectPart.reads (.reg (.gpr 3)) [.gpr 6] []) (.reg (.gpr 3))) #v[6]
    (.letOp (n := 72) (.exec 0x112602 (fun s => s.RIP = 0x112602) (movR64R64Effect 0x112602 3 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 73) (.out 0x112605 (movR64R64Effect 0x112605 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[59]
    (.letOp (n := 74) (.exec 0x112605 (fun s => s.RIP = 0x112605) (movR64R64Effect 0x112605 12 0) (Reg.operands [.gpr 0] [])) #v[59]
    (.letOp (n := 75) (.out 0x112608 (movR64R64Effect 0x112608 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[1]
    (.letOp (n := 76) (.exec 0x112608 (fun s => s.RIP = 0x112608) (movR64R64Effect 0x112608 0 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.terminate (.br ⟨.l11465b, RegMap.args [(0, 75), (1, 1), (2, 2), (3, 71), (4, 4), (6, 6), (7, 7), (8, 55), (9, 9), (10, 10), (11, 11), (12, 73), (13, 63), (14, 67), (15, 69), (22, 22), (39, 39), (51, 51)] 77⟩)))))))))))))))))))))))))

def bytes_l114635 : List UInt8 :=
  [0x49, 0x89, 0xC8, 0x49, 0x29, 0xC0, 0xB8, 0x02, 0x00, 0x00, 0x00, 0x4C, 0x29, 0xE0, 0x49, 0x89,
    0xF5, 0x49, 0x29, 0xDD, 0x49, 0x89, 0xFE, 0x4D, 0x29, 0xFE, 0x49, 0x89, 0xFF, 0x48, 0x89, 0xF3,
    0x49, 0x89, 0xC4, 0x48, 0x89, 0xC8]

theorem code_l114635 : ∀ x ∈ codeRange 0x1125e5 bytes_l114635, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x125e5 38 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11465b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11260b (sarR64Effect 0x11260b 3 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[8]
    (.letOp (n := 54) (.exec 0x11260b (fun s => s.RIP = 0x11260b) (sarR64Effect 0x11260b 3 8 1) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[8]
    (.letOp (n := 55) (.out 0x11260e (addR64R64Effect 0x11260e 3 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 3] []) (.reg (.gpr 3))) #v[3, 3]
    (.letOp (n := 56) (.exec 0x11260e (fun s => s.RIP = 0x11260e) (addR64R64Effect 0x11260e 3 3) (Reg.operands [.gpr 3, .gpr 3] [])) #v[3, 3]
    (.letOp (n := 57) (.out 0x112611 (addR64R64Effect 0x112611 15 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 15] []) (.reg (.gpr 15))) #v[15, 15]
    (.letOp (n := 58) (.exec 0x112611 (fun s => s.RIP = 0x112611) (addR64R64Effect 0x112611 15 15) (Reg.operands [.gpr 15, .gpr 15] [])) #v[15, 15]
    (.letOp (n := 59) (.out 0x112614 (movR64R64Effect 0x112614 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 8] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 60) (.exec 0x112614 (fun s => s.RIP = 0x112614) (movR64R64Effect 0x112614 1 8) (Reg.operands [.gpr 8] [])) #v[53]
    (.letOp (n := 61) (.out 0x112617 (movR64R64Effect 0x112617 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 13] []) (.reg (.gpr 6))) #v[13]
    (.letOp (n := 62) (.exec 0x112617 (fun s => s.RIP = 0x112617) (movR64R64Effect 0x112617 6 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 63) (.out 0x11261a (movR64R64Effect 0x11261a 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 64) (.exec 0x11261a (fun s => s.RIP = 0x11261a) (movR64R64Effect 0x11261a 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 65) (.out 0x11261d (decR32Effect 0x11261d 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[2]
    (.letOp (n := 66) (.out 0x11261d (decR32Effect 0x11261d 2 2) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.flag .ZF)) #v[2]
    (.letOp (n := 67) (.exec 0x11261d (fun s => s.RIP = 0x11261d) (decR32Effect 0x11261d 2 2) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2]
    (.letOp (n := 68) (.pure (condOp 4)) #v[66]
    (.terminate (.condBr (Fin.last 68) ⟨.l114311, RegMap.args [(0, 0), (1, 59), (2, 65), (3, 55), (4, 4), (6, 61), (7, 63), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 57), (19, 66), (22, 22), (39, 39), (51, 51)] 69⟩ ⟨.l114675, RegMap.args [(0, 0), (1, 59), (2, 65), (3, 55), (4, 4), (6, 61), (7, 63), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 57), (19, 66), (22, 22), (39, 39), (51, 51)] 69⟩)))))))))))))))))

def bytes_l11465b : List UInt8 :=
  [0x49, 0xD1, 0xF8, 0x48, 0x01, 0xDB, 0x4D, 0x01, 0xFF, 0x4C, 0x89, 0xC1, 0x4C, 0x89, 0xEE, 0x4C,
    0x89, 0xF7, 0xFF, 0xCA, 0x0F, 0x84, 0x9C, 0xFC, 0xFF, 0xFF]

theorem code_l11465b : ∀ x ∈ codeRange 0x11260b bytes_l11465b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1260b 26 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l114675 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x112625 (testR8Imm8LowEffect 0x112625 1 0x1) (EffectPart.reads (.flag .ZF) [.gpr 1] []) (.flag .ZF)) #v[1]
    (.letOp (n := 54) (.exec 0x112625 (fun s => s.RIP = 0x112625) (testR8Imm8LowEffect 0x112625 1 0x1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l114630, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (15, 15), (19, 53), (22, 22), (39, 39), (51, 51)] 56⟩ ⟨.l11467a, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (15, 15), (19, 53), (22, 22), (39, 39), (51, 51)] 56⟩))))

def bytes_l114675 : List UInt8 :=
  [0xF6, 0xC1, 0x01, 0x75, 0xB6]

theorem code_l114675 : ∀ x ∈ codeRange 0x112625 bytes_l114675, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x12625 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11467a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11262a (addR64Imm8Effect 0x11262a 12 0x2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[12]
    (.letOp (n := 54) (.exec 0x11262a (fun s => s.RIP = 0x11262a) (addR64Imm8Effect 0x11262a 12 0x2) (Reg.operands [.gpr 12] [])) #v[12]
    (.terminate (.br ⟨.l11468d, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 53), (15, 15), (22, 22), (39, 39), (51, 51)] 55⟩)))

def bytes_l11467a : List UInt8 :=
  [0x49, 0x83, 0xC4, 0x02, 0xEB, 0x0D]

theorem code_l11467a : ∀ x ∈ codeRange 0x11262a bytes_l11467a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1262a 6 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l114680 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x112630 (addR64R64Effect 0x112630 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1, 0]
    (.letOp (n := 54) (.exec 0x112630 (fun s => s.RIP = 0x112630) (addR64R64Effect 0x112630 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1, 0]
    (.letOp (n := 55) (.out 0x112633 (addR64Imm8Effect 0x112633 12 0x2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[12]
    (.letOp (n := 56) (.exec 0x112633 (fun s => s.RIP = 0x112633) (addR64Imm8Effect 0x112633 12 0x2) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 57) (.out 0x112637 (addR64R64Effect 0x112637 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 3] []) (.reg (.gpr 6))) #v[6, 3]
    (.letOp (n := 58) (.exec 0x112637 (fun s => s.RIP = 0x112637) (addR64R64Effect 0x112637 6 3) (Reg.operands [.gpr 6, .gpr 3] [])) #v[6, 3]
    (.letOp (n := 59) (.out 0x11263a (addR64R64Effect 0x11263a 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 15] []) (.reg (.gpr 7))) #v[7, 15]
    (.letOp (n := 60) (.exec 0x11263a (fun s => s.RIP = 0x11263a) (addR64R64Effect 0x11263a 7 15) (Reg.operands [.gpr 7, .gpr 15] [])) #v[7, 15]
    (.terminate (.br ⟨.l11468d, RegMap.args [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 59), (9, 9), (10, 10), (11, 11), (12, 55), (15, 15), (22, 22), (39, 39), (51, 51)] 61⟩)))))))))

def bytes_l114680 : List UInt8 :=
  [0x48, 0x01, 0xC1, 0x49, 0x83, 0xC4, 0x02, 0x48, 0x01, 0xDE, 0x4C, 0x01, 0xFF]

theorem code_l114680 : ∀ x ∈ codeRange 0x112630 bytes_l114680, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x12630 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11468d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11263d (movR64R64Effect 0x11263d 14 7) (EffectPart.reads (.reg (.gpr 14)) [.gpr 7] []) (.reg (.gpr 14))) #v[7]
    (.letOp (n := 54) (.exec 0x11263d (fun s => s.RIP = 0x11263d) (movR64R64Effect 0x11263d 14 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 55) (.out 0x112640 (movR64R64Effect 0x112640 13 6) (EffectPart.reads (.reg (.gpr 13)) [.gpr 6] []) (.reg (.gpr 13))) #v[6]
    (.letOp (n := 56) (.exec 0x112640 (fun s => s.RIP = 0x112640) (movR64R64Effect 0x112640 13 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 57) (.out 0x112643 (movR64R64Effect 0x112643 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 1] []) (.reg (.gpr 8))) #v[1]
    (.letOp (n := 58) (.exec 0x112643 (fun s => s.RIP = 0x112643) (movR64R64Effect 0x112643 8 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.terminate (.br ⟨.l11465b, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 55), (14, 53), (15, 15), (22, 22), (39, 39), (51, 51)] 59⟩)))))))

def bytes_l11468d : List UInt8 :=
  [0x49, 0x89, 0xFE, 0x49, 0x89, 0xF5, 0x49, 0x89, 0xC8, 0xEB, 0xC3]

theorem code_l11468d : ∀ x ∈ codeRange 0x11263d bytes_l11468d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1263d 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l114698 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x112648 (movR64M64Effect 0x112648 0 (.sib 4 none 0 (.d32 0x118))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x112648 (LoadPre 0x112648 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x112648 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x112648 0 (.sib 4 none 0 (.d32 0x118))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x112650 (orR64M64Effect 0x112650 0 (.sib 4 none 0 (.d32 0x108))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[53, 4]
    (.letOp (n := 56) (.exec 0x112650 (LoadPre 0x112650 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x112650 + BitVec.ofNat 64 8)) 8) (orR64M64Effect 0x112650 0 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 57) (.out 0x112658 (orR64M64Effect 0x112658 0 (.sib 4 none 0 (.d32 0x100))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[55, 4]
    (.letOp (n := 58) (.exec 0x112658 (LoadPre 0x112658 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x112658 + BitVec.ofNat 64 8)) 8) (orR64M64Effect 0x112658 0 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 59) (.out 0x112660 (orR64M64Effect 0x112660 0 (.sib 4 none 0 (.d32 0x110))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[57, 4]
    (.letOp (n := 60) (.out 0x112660 (orR64M64Effect 0x112660 0 (.sib 4 none 0 (.d32 0x110))) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 4] []) (.flag .ZF)) #v[57, 4]
    (.letOp (n := 61) (.exec 0x112660 (LoadPre 0x112660 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x112660 + BitVec.ofNat 64 8)) 8) (orR64M64Effect 0x112660 0 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 62) (.out 0x112668 (atFlags (condHolds 5) (setccR8Effect 0x112668 3 3)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 3))) #v[3, 60]
    (.letOp (n := 63) (.exec 0x112668 (fun s => s.RIP = 0x112668) (atFlags (condHolds 5) (setccR8Effect 0x112668 3 3)) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[3, 60]
    (.letOp (n := 64) (.out 0x11266b (movR32M32LowEffect 0x11266b 2 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 65) (.exec 0x11266b (LoadPre 0x11266b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11266b + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x11266b 2 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.out 0x11266f (leaR64Effect 0x11266f 6 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 67) (.exec 0x11266f (fun s => s.RIP = 0x11266f) (leaR64Effect 0x11266f 6 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.out 0x112674 (movR64M64Effect 0x112674 14 (.sib 4 none 0 (.d32 0x120))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 69) (.exec 0x112674 (LoadPre 0x112674 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x112674 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x112674 14 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.out 0x11267c (movR64R64Effect 0x11267c 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[68]
    (.letOp (n := 71) (.exec 0x11267c (fun s => s.RIP = 0x11267c) (movR64R64Effect 0x11267c 7 14) (Reg.operands [.gpr 14] [])) #v[68]
    (.letOp (n := 72) (.out 0x11267f (movR64M64Effect 0x11267f 1 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 73) (.exec 0x11267f (LoadPre 0x11267f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x11267f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11267f 1 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.out 0x112684 (callEffect (fun _ => 0x1126c0) 0x112689) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 75) (.exec 0x112684 (PushPre 0x112684 5) (callEffect (fun _ => 0x1126c0) 0x112689) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 76) (.const ⟨64, 0x112689⟩) #v[]
    (.terminate (.call ⟨.l1181a0, RegMap.args [(0, 59), (1, 72), (2, 64), (3, 62), (4, 74), (5, 5), (6, 66), (7, 70), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 68), (15, 15), (19, 60), (22, 22), (39, 39), (51, 51)] 77⟩ { target := .l1146d9, kept := #v[], arity := rfl, guard := some (Fin.last 76) })))))))))))))))))))))))))

def bytes_l114698 : List UInt8 :=
  [0x48, 0x8B, 0x84, 0x24, 0x18, 0x01, 0x00, 0x00, 0x48, 0x0B, 0x84, 0x24, 0x08, 0x01, 0x00, 0x00,
    0x48, 0x0B, 0x84, 0x24, 0x00, 0x01, 0x00, 0x00, 0x48, 0x0B, 0x84, 0x24, 0x10, 0x01, 0x00, 0x00,
    0x0F, 0x95, 0xC3, 0x8B, 0x54, 0x24, 0x28, 0x48, 0x8D, 0x74, 0x24, 0x60, 0x4C, 0x8B, 0xB4, 0x24,
    0x20, 0x01, 0x00, 0x00, 0x4C, 0x89, 0xF7, 0x48, 0x8B, 0x4C, 0x24, 0x58, 0xE8, 0x37, 0x00, 0x00,
    0x00]

theorem code_l114698 : ∀ x ∈ codeRange 0x112648 bytes_l114698, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x12648 65 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1146d9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x112689 (movR64M64Effect 0x112689 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x112689 (LoadPre 0x112689 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x112689 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x112689 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x11268e (xorR64Imm8Effect 0x11268e 0 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x11268e (fun s => s.RIP = 0x11268e) (xorR64Imm8Effect 0x11268e 0 0x1) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x112692 (orR64M64Effect 0x112692 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[55, 4]
    (.letOp (n := 58) (.exec 0x112692 (LoadPre 0x112692 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x112692 + BitVec.ofNat 64 5)) 8) (orR64M64Effect 0x112692 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 59) (.out 0x112697 (orR64M64Effect 0x112697 0 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[57, 4]
    (.letOp (n := 60) (.exec 0x112697 (LoadPre 0x112697 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x112697 + BitVec.ofNat 64 5)) 8) (orR64M64Effect 0x112697 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 61) (.out 0x11269c (orR64M64Effect 0x11269c 0 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[59, 4]
    (.letOp (n := 62) (.out 0x11269c (orR64M64Effect 0x11269c 0 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 4] []) (.flag .ZF)) #v[59, 4]
    (.letOp (n := 63) (.exec 0x11269c (LoadPre 0x11269c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11269c + BitVec.ofNat 64 5)) 8) (orR64M64Effect 0x11269c 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 64) (.out 0x1126a1 (atFlags (condHolds 4) (setccR8Effect 0x1126a1 3 0)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 0))) #v[61, 62]
    (.letOp (n := 65) (.exec 0x1126a1 (fun s => s.RIP = 0x1126a1) (atFlags (condHolds 4) (setccR8Effect 0x1126a1 3 0)) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[61, 62]
    (.letOp (n := 66) (.out 0x1126a4 (andR8R8Effect 0x1126a4 2 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[64, 3]
    (.letOp (n := 67) (.exec 0x1126a4 (fun s => s.RIP = 0x1126a4) (andR8R8Effect 0x1126a4 2 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[64, 3]
    (.letOp (n := 68) (.exec 0x1126a6 (StorePre 0x1126a6 4 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x1126a6 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1126a6 4 0 (.base 14 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 14] [])) #v[66, 14]
    (.letOp (n := 69) (.out 0x1126aa (addR64Imm32Effect 0x1126aa 4 0x158) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 70) (.exec 0x1126aa (fun s => s.RIP = 0x1126aa) (addR64Imm32Effect 0x1126aa 4 0x158) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.out 0x1126b1 (popR64Effect 0x1126b1 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[69]
    (.letOp (n := 72) (.out 0x1126b1 (popR64Effect 0x1126b1 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[69]
    (.letOp (n := 73) (.exec 0x1126b1 (PopPre 0x1126b1) (popR64Effect 0x1126b1 1 3) (Reg.operands [.gpr 4] [])) #v[69]
    (.letOp (n := 74) (.out 0x1126b2 (popR64Effect 0x1126b2 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[72]
    (.letOp (n := 75) (.out 0x1126b2 (popR64Effect 0x1126b2 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[72]
    (.letOp (n := 76) (.exec 0x1126b2 (PopPre 0x1126b2) (popR64Effect 0x1126b2 2 12) (Reg.operands [.gpr 4] [])) #v[72]
    (.letOp (n := 77) (.out 0x1126b4 (popR64Effect 0x1126b4 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[75]
    (.letOp (n := 78) (.out 0x1126b4 (popR64Effect 0x1126b4 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[75]
    (.letOp (n := 79) (.exec 0x1126b4 (PopPre 0x1126b4) (popR64Effect 0x1126b4 2 13) (Reg.operands [.gpr 4] [])) #v[75]
    (.letOp (n := 80) (.out 0x1126b6 (popR64Effect 0x1126b6 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[78]
    (.letOp (n := 81) (.out 0x1126b6 (popR64Effect 0x1126b6 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[78]
    (.letOp (n := 82) (.exec 0x1126b6 (PopPre 0x1126b6) (popR64Effect 0x1126b6 2 14) (Reg.operands [.gpr 4] [])) #v[78]
    (.letOp (n := 83) (.out 0x1126b8 (popR64Effect 0x1126b8 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[81]
    (.letOp (n := 84) (.out 0x1126b8 (popR64Effect 0x1126b8 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[81]
    (.letOp (n := 85) (.exec 0x1126b8 (PopPre 0x1126b8) (popR64Effect 0x1126b8 2 15) (Reg.operands [.gpr 4] [])) #v[81]
    (.letOp (n := 86) (.out 0x1126ba (popR64Effect 0x1126ba 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[84]
    (.letOp (n := 87) (.out 0x1126ba (popR64Effect 0x1126ba 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[84]
    (.letOp (n := 88) (.exec 0x1126ba (PopPre 0x1126ba) (popR64Effect 0x1126ba 1 5) (Reg.operands [.gpr 4] [])) #v[84]
    (.letOp (n := 89) (.out 0x1126bb (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[87]
    (.letOp (n := 90) (.out 0x1126bb (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[87]
    (.letOp (n := 91) (.exec 0x1126bb (RetPre 0x1126bb) (retEffect) (Reg.operands [.gpr 4] [])) #v[87]
    (.terminate (.ret (RegMap.args [(0, 66), (2, 2), (3, 71), (4, 90), (5, 86), (8, 8), (9, 9), (10, 10), (11, 11), (12, 74), (13, 77), (14, 80), (15, 83), (22, 22), (39, 39), (51, 51)] 92) (some ⟨89, by decide⟩)))))))))))))))))))))))))))))))))))))))))

def bytes_l1146d9 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x08, 0x48, 0x83, 0xF0, 0x01, 0x48, 0x0B, 0x44, 0x24, 0x10, 0x48, 0x0B,
    0x44, 0x24, 0x18, 0x48, 0x0B, 0x44, 0x24, 0x20, 0x0F, 0x94, 0xC0, 0x20, 0xD8, 0x41, 0x88, 0x46,
    0x20, 0x48, 0x81, 0xC4, 0x58, 0x01, 0x00, 0x00, 0x5B, 0x41, 0x5C, 0x41, 0x5D,
    0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l1146d9 : ∀ x ∈ codeRange 0x112689 bytes_l1146d9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x12689 51 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1181a0 : Block Op Label signature Reg.count 53 :=
  cutBlock 0x1126c0

def bytes_l1181a0 : List UInt8 :=
  [0x41, 0x57]

theorem code_l1181a0 : ∀ x ∈ codeRange 0x1126c0 bytes_l1181a0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x126c0 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

end P256.Proofs.Verifying.Core.Inverse.SafeGcd.Machine
