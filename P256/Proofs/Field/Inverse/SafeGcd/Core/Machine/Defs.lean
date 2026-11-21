import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.Machine.Labels
import P256.Proofs.Common.CFG.EvalAttr
import P256.Proofs.Common.Lift.Generated.Footprints

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.Machine

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

@[cfg_block] def b_l117650 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x111b70 (pushR64Effect 0x111b70 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x111b70 (PushPre 0x111b70 1) (pushR64Effect 0x111b70 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x111b71 (pushR64Effect 0x111b71 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x111b71 (PushPre 0x111b71 2) (pushR64Effect 0x111b71 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x111b73 (pushR64Effect 0x111b73 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x111b73 (PushPre 0x111b73 2) (pushR64Effect 0x111b73 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x111b75 (pushR64Effect 0x111b75 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x111b75 (PushPre 0x111b75 2) (pushR64Effect 0x111b75 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x111b77 (pushR64Effect 0x111b77 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x111b77 (PushPre 0x111b77 2) (pushR64Effect 0x111b77 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x111b79 (pushR64Effect 0x111b79 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x111b79 (PushPre 0x111b79 1) (pushR64Effect 0x111b79 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x111b7a (subR64Imm32Effect 0x111b7a 4 0x158) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x111b7a (fun s => s.RIP = 0x111b7a) (subR64Imm32Effect 0x111b7a 4 0x158) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.exec 0x111b81 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111b81 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x111b81 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111b81 1 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1, 65]
    (.letOp (n := 68) (.exec 0x111b89 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111b89 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x111b89 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111b89 7 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[7, 65]
    (.terminate (.br ⟨.l117671, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)] 69⟩)))))))))))))))))

def bytes_l117650 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0x58, 0x01, 0x00,
    0x00, 0x48, 0x89, 0x8C, 0x24, 0x28, 0x01, 0x00, 0x00, 0x48, 0x89, 0xBC, 0x24, 0x20, 0x01, 0x00,
    0x00]

theorem code_l117650 : ∀ x ∈ codeRange 0x111b70 bytes_l117650, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x11b70 33 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l117671 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x111b91 (movR64Imm64Effect 0x111b91 9 0x7fffffffffffffff) (EffectPart.reads (.reg (.gpr 9)) [] []) (.reg (.gpr 9))) #v[]
    (.letOp (n := 54) (.exec 0x111b91 (fun s => s.RIP = 0x111b91) (movR64Imm64Effect 0x111b91 9 0x7fffffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x111b9b (movR64M64Effect 0x111b9b 0 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 56) (.exec 0x111b9b (LoadPre 0x111b9b (fun s => AddrMode.addr (.base 6 .none) s (0x111b9b + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x111b9b 0 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 57) (.exec 0x111b9e (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111b9e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x111b9e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111b9e 0 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 58) (.out 0x111ba6 (movR64M64Effect 0x111ba6 0 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 59) (.exec 0x111ba6 (LoadPre 0x111ba6 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x111ba6 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x111ba6 0 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 60) (.exec 0x111baa (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111baa 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x111baa + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111baa 0 (.sib 4 none 0 (.d32 0x118))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[58, 4]
    (.letOp (n := 61) (.out 0x111bb2 (movR64M64Effect 0x111bb2 0 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 62) (.exec 0x111bb2 (LoadPre 0x111bb2 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x111bb2 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x111bb2 0 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 63) (.exec 0x111bb6 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111bb6 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x111bb6 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111bb6 0 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.out 0x111bbe (movR64M64Effect 0x111bbe 0 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 65) (.exec 0x111bbe (LoadPre 0x111bbe (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x111bbe + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x111bbe 0 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 66) (.exec 0x111bc2 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111bc2 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x111bc2 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111bc2 0 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.out 0x111bca (movR64M64Effect 0x111bca 0 (.base 2 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 68) (.exec 0x111bca (LoadPre 0x111bca (fun s => AddrMode.addr (.base 2 (.d8 0x18)) s (0x111bca + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x111bca 0 (.base 2 (.d8 0x18))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 69) (.exec 0x111bce (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111bce 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x111bce + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x111bce 0 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[67, 4]
    (.letOp (n := 70) (.out 0x111bd3 (movR64M64Effect 0x111bd3 0 (.base 2 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 71) (.exec 0x111bd3 (LoadPre 0x111bd3 (fun s => AddrMode.addr (.base 2 (.d8 0x10)) s (0x111bd3 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x111bd3 0 (.base 2 (.d8 0x10))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 72) (.exec 0x111bd7 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111bd7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x111bd7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x111bd7 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[70, 4]
    (.letOp (n := 73) (.out 0x111bdc (movR64M64Effect 0x111bdc 0 (.base 2 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 74) (.exec 0x111bdc (LoadPre 0x111bdc (fun s => AddrMode.addr (.base 2 .none) s (0x111bdc + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x111bdc 0 (.base 2 .none)) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 75) (.exec 0x111bdf (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111bdf 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x111bdf + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111bdf 2 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2, 4]
    (.letOp (n := 76) (.out 0x111be7 (movR64M64Effect 0x111be7 1 (.base 2 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2]
    (.letOp (n := 77) (.exec 0x111be7 (LoadPre 0x111be7 (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x111be7 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x111be7 1 (.base 2 (.d8 0x8))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 78) (.exec 0x111beb (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111beb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x111beb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x111beb 1 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[76, 4]
    (.letOp (n := 79) (.exec 0x111bf0 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111bf0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x111bf0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x111bf0 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[73, 4]
    (.letOp (n := 80) (.exec 0x111bf5 (StorePre 0x111bf5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x111bf5 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x111bf5 (.sib 4 none 0 (.d8 0x78)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.br ⟨.l1176da, RegMap.args [(0, 73), (1, 76), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 53), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (51, 51)] 81⟩)))))))))))))))))))))))))))))

def bytes_l117671 : List UInt8 :=
  [0x49, 0xB9, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F, 0x48, 0x8B, 0x06, 0x48, 0x89, 0x84,
    0x24, 0x08, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x46, 0x08, 0x48, 0x89, 0x84, 0x24, 0x18, 0x01, 0x00,
    0x00, 0x48, 0x8B, 0x46, 0x10, 0x48, 0x89, 0x84, 0x24, 0x00, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x46,
    0x18, 0x48, 0x89, 0x84, 0x24, 0x10, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x42, 0x18, 0x48, 0x89, 0x44,
    0x24, 0x70, 0x48, 0x8B, 0x42, 0x10, 0x48, 0x89, 0x44, 0x24, 0x68, 0x48, 0x8B, 0x02, 0x48, 0x89,
    0x94, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x4A, 0x08, 0x48, 0x89, 0x4C, 0x24, 0x60, 0x48,
    0x89, 0x44, 0x24, 0x58, 0xC6, 0x44, 0x24, 0x78, 0x00]

theorem code_l117671 : ∀ x ∈ codeRange 0x111b91 bytes_l117671, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x11b91 105 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1176da : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x111bfa (movR64M64Effect 0x111bfa 0 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 54) (.exec 0x111bfa (LoadPre 0x111bfa (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x111bfa + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x111bfa 0 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 55) (.exec 0x111bfe (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111bfe 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x111bfe + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111bfe 0 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x111c06 (movR64M64Effect 0x111c06 0 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 57) (.exec 0x111c06 (LoadPre 0x111c06 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x111c06 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x111c06 0 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 58) (.exec 0x111c0a (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111c0a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x111c0a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111c0a 0 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x111c12 (movR64M64Effect 0x111c12 0 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 60) (.exec 0x111c12 (LoadPre 0x111c12 (fun s => AddrMode.addr (.base 6 .none) s (0x111c12 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x111c12 0 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 61) (.out 0x111c15 (movR64M64Effect 0x111c15 1 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[6]
    (.letOp (n := 62) (.exec 0x111c15 (LoadPre 0x111c15 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x111c15 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x111c15 1 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 63) (.exec 0x111c19 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111c19 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x111c19 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111c19 1 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.exec 0x111c21 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111c21 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x111c21 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111c21 0 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 65) (.exec 0x111c29 (StorePre 0x111c29 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x111c29 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x111c29 (.sib 4 none 0 (.d32 0xa8)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x111c31 (StorePre 0x111c31 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x111c31 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x111c31 (.sib 4 none 0 (.d32 0xd0)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x111c3d (StorePre 0x111c3d 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x111c3d + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x111c3d (.sib 4 none 0 (.d32 0xc8)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.exec 0x111c49 (StorePre 0x111c49 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x111c49 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x111c49 (.sib 4 none 0 (.d32 0xc0)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.exec 0x111c55 (StorePre 0x111c55 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x111c55 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x111c55 (.sib 4 none 0 (.d32 0xb8)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.exec 0x111c61 (StorePre 0x111c61 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x111c61 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x111c61 (.sib 4 none 0 (.d32 0xb0)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.br ⟨.l11774d, RegMap.args [(0, 59), (1, 61), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (51, 51)] 71⟩)))))))))))))))))))

def bytes_l1176da : List UInt8 :=
  [0x48, 0x8B, 0x46, 0x18, 0x48, 0x89, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x46, 0x10,
    0x48, 0x89, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x06, 0x48, 0x8B, 0x4E, 0x08, 0x48,
    0x89, 0x8C, 0x24, 0x90, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, 0xC6,
    0x84, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48,
    0xC7, 0x84, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0xB8,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00]

theorem code_l1176da : ∀ x ∈ codeRange 0x111bfa bytes_l1176da, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x11bfa 115 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11774d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x111c6d (movR64M64Effect 0x111c6d 0 (.base 8 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[8]
    (.letOp (n := 54) (.exec 0x111c6d (LoadPre 0x111c6d (fun s => AddrMode.addr (.base 8 (.d8 0x18)) s (0x111c6d + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x111c6d 0 (.base 8 (.d8 0x18))) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 55) (.exec 0x111c71 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111c71 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x111c71 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111c71 0 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x111c79 (movR64M64Effect 0x111c79 0 (.base 8 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[8]
    (.letOp (n := 57) (.exec 0x111c79 (LoadPre 0x111c79 (fun s => AddrMode.addr (.base 8 (.d8 0x10)) s (0x111c79 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x111c79 0 (.base 8 (.d8 0x10))) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 58) (.exec 0x111c7d (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111c7d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x111c7d + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111c7d 0 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x111c85 (movR64M64Effect 0x111c85 0 (.base 8 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[8]
    (.letOp (n := 60) (.exec 0x111c85 (LoadPre 0x111c85 (fun s => AddrMode.addr (.base 8 .none) s (0x111c85 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x111c85 0 (.base 8 .none)) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 61) (.out 0x111c88 (movR64M64Effect 0x111c88 1 (.base 8 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 8] []) (.reg (.gpr 1))) #v[8]
    (.letOp (n := 62) (.exec 0x111c88 (LoadPre 0x111c88 (fun s => AddrMode.addr (.base 8 (.d8 0x8)) s (0x111c88 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x111c88 1 (.base 8 (.d8 0x8))) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 63) (.exec 0x111c8c (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111c8c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x111c8c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111c8c 1 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.exec 0x111c94 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111c94 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x111c94 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111c94 0 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 65) (.exec 0x111c9c (StorePre 0x111c9c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x111c9c + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x111c9c (.sib 4 none 0 (.d32 0xf8)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.br ⟨.l117784, RegMap.args [(0, 59), (1, 61), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (51, 51)] 66⟩))))))))))))))

def bytes_l11774d : List UInt8 :=
  [0x49, 0x8B, 0x40, 0x18, 0x48, 0x89, 0x84, 0x24, 0xF0, 0x00, 0x00, 0x00, 0x49, 0x8B, 0x40, 0x10,
    0x48, 0x89, 0x84, 0x24, 0xE8, 0x00, 0x00, 0x00, 0x49, 0x8B, 0x00, 0x49, 0x8B, 0x48, 0x08, 0x48,
    0x89, 0x8C, 0x24, 0xE0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0xD8, 0x00, 0x00, 0x00, 0xC6,
    0x84, 0x24, 0xF8, 0x00, 0x00, 0x00, 0x00]

theorem code_l11774d : ∀ x ∈ codeRange 0x111c6d bytes_l11774d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x11c6d 55 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l117784 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x111ca4 (movR32Imm32Effect 0x111ca4 5 5 0x1) (EffectPart.reads (.reg (.gpr 5)) [] []) (.reg (.gpr 5))) #v[]
    (.letOp (n := 54) (.exec 0x111ca4 (fun s => s.RIP = 0x111ca4) (movR32Imm32Effect 0x111ca4 5 5 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x111ca9 (movR32Imm32Effect 0x111ca9 5 2 0x24f) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 56) (.exec 0x111ca9 (fun s => s.RIP = 0x111ca9) (movR32Imm32Effect 0x111ca9 5 2 0x24f) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x111cae (leaR64Effect 0x111cae 13 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 58) (.exec 0x111cae (fun s => s.RIP = 0x111cae) (leaR64Effect 0x111cae 13 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.br ⟨.l1179fa, RegMap.args [(2, 55), (3, 3), (4, 4), (5, 53), (9, 9), (10, 10), (11, 11), (13, 57), (14, 14), (22, 22), (39, 39), (51, 51)] 59⟩)))))))

def bytes_l117784 : List UInt8 :=
  [0xBD, 0x01, 0x00, 0x00, 0x00, 0xBA, 0x4F, 0x02, 0x00, 0x00, 0x4C, 0x8D, 0x6C, 0x24, 0x08, 0xE9,
    0x62, 0x02, 0x00, 0x00]

theorem code_l117784 : ∀ x ∈ codeRange 0x111ca4 bytes_l117784, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x11ca4 20 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1177a0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x111cc0 (movR32Imm32Effect 0x111cc0 6 12 0x1) (EffectPart.reads (.reg (.gpr 12)) [] []) (.reg (.gpr 12))) #v[]
    (.letOp (n := 54) (.exec 0x111cc0 (fun s => s.RIP = 0x111cc0) (movR32Imm32Effect 0x111cc0 6 12 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x111cc6 (xorR32R32Effect 0x111cc6 3 14 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 14] []) (.reg (.gpr 14))) #v[14, 14]
    (.letOp (n := 56) (.exec 0x111cc6 (fun s => s.RIP = 0x111cc6) (xorR32R32Effect 0x111cc6 3 14 14) (Reg.operands [.gpr 14, .gpr 14] [])) #v[14, 14]
    (.letOp (n := 57) (.out 0x111cc9 (xorR32R32Effect 0x111cc9 2 3 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 3] []) (.reg (.gpr 3))) #v[3, 3]
    (.letOp (n := 58) (.exec 0x111cc9 (fun s => s.RIP = 0x111cc9) (xorR32R32Effect 0x111cc9 2 3 3) (Reg.operands [.gpr 3, .gpr 3] [])) #v[3, 3]
    (.letOp (n := 59) (.out 0x111ccb (movR32Imm32Effect 0x111ccb 6 15 0x1) (EffectPart.reads (.reg (.gpr 15)) [] []) (.reg (.gpr 15))) #v[]
    (.letOp (n := 60) (.exec 0x111ccb (fun s => s.RIP = 0x111ccb) (movR32Imm32Effect 0x111ccb 6 15 0x1) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l1177b1, RegMap.args [(3, 57), (4, 4), (5, 5), (10, 10), (11, 11), (12, 53), (13, 13), (14, 55), (15, 59), (22, 22), (39, 39), (51, 51)] 61⟩)))))))))

def bytes_l1177a0 : List UInt8 :=
  [0x41, 0xBC, 0x01, 0x00, 0x00, 0x00, 0x45, 0x31, 0xF6, 0x31, 0xDB, 0x41, 0xBF, 0x01, 0x00, 0x00,
    0x00]

theorem code_l1177a0 : ∀ x ∈ codeRange 0x111cc0 bytes_l1177a0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x11cc0 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1177b1 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x111cd1 (movR64R64Effect 0x111cd1 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[15]
    (.letOp (n := 54) (.exec 0x111cd1 (fun s => s.RIP = 0x111cd1) (movR64R64Effect 0x111cd1 0 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.out 0x111cd4 (shrR64Effect 0x111cd4 4 0 63) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x111cd4 (fun s => s.RIP = 0x111cd4) (shrR64Effect 0x111cd4 4 0 63) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 57) (.exec 0x111cd8 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111cd8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x148)) s (0x111cd8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111cd8 0 (.sib 4 none 0 (.d32 0x148))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 58) (.exec 0x111ce0 (StorePre 0x111ce0 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3)) s (0x111ce0 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x111ce0 4 0 (.sib 4 none 0 (.d8 0x3))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 59) (.exec 0x111ce4 (fun s => s.RIP = 0x111ce4) (leaR64Effect 0x111ce4 1 (.sib 4 none 0 (.d8 0x3))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.out 0x111ce9 (movR64R64Effect 0x111ce9 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 61) (.exec 0x111ce9 (fun s => s.RIP = 0x111ce9) (movR64R64Effect 0x111ce9 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 62) (.out 0x111cec (shrR64Effect 0x111cec 4 0 63) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[60]
    (.letOp (n := 63) (.exec 0x111cec (fun s => s.RIP = 0x111cec) (shrR64Effect 0x111cec 4 0 63) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[60]
    (.letOp (n := 64) (.exec 0x111cf0 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111cf0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x138)) s (0x111cf0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111cf0 0 (.sib 4 none 0 (.d32 0x138))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.exec 0x111cf8 (StorePre 0x111cf8 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3)) s (0x111cf8 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x111cf8 4 0 (.sib 4 none 0 (.d8 0x3))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 66) (.out 0x111cfc (movR64R64Effect 0x111cfc 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 13] []) (.reg (.gpr 7))) #v[13]
    (.letOp (n := 67) (.exec 0x111cfc (fun s => s.RIP = 0x111cfc) (movR64R64Effect 0x111cfc 7 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 68) (.out 0x111cff (leaR64Effect 0x111cff 6 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 69) (.exec 0x111cff (fun s => s.RIP = 0x111cff) (leaR64Effect 0x111cff 6 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.out 0x111d04 (leaR64Effect 0x111d04 2 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 71) (.exec 0x111d04 (fun s => s.RIP = 0x111d04) (leaR64Effect 0x111d04 2 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.out 0x111d0c (movR64R64Effect 0x111d0c 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 15] []) (.reg (.gpr 1))) #v[15]
    (.letOp (n := 73) (.exec 0x111d0c (fun s => s.RIP = 0x111d0c) (movR64R64Effect 0x111d0c 1 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 74) (.out 0x111d0f (movR64R64Effect 0x111d0f 8 3) (EffectPart.reads (.reg (.gpr 8)) [.gpr 3] []) (.reg (.gpr 8))) #v[3]
    (.letOp (n := 75) (.exec 0x111d0f (fun s => s.RIP = 0x111d0f) (movR64R64Effect 0x111d0f 8 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 76) (.out 0x111d12 (movR32M32Effect 0x111d12 9 (.sib 4 none 0 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 77) (.exec 0x111d12 (LoadPre 0x111d12 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x111d12 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x111d12 9 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 78) (.out 0x111d17 (callEffect (fun _ => 0x1115d0) 0x111d1c) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 79) (.exec 0x111d17 (PushPre 0x111d17 5) (callEffect (fun _ => 0x1115d0) 0x111d1c) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 80) (.const ⟨64, 0x111d1c⟩) #v[]
    (.terminate (.call ⟨.l1170b0, RegMap.args [(0, 62), (1, 72), (2, 70), (3, 3), (4, 78), (5, 5), (6, 68), (7, 66), (8, 74), (9, 76), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)] 81⟩ { target := .l1177fc, kept := #v[], arity := rfl, guard := some (Fin.last 80) })))))))))))))))))))))))))))))

def bytes_l1177b1 : List UInt8 :=
  [0x4C, 0x89, 0xF8, 0x48, 0xC1, 0xE8, 0x3F, 0x48, 0x89, 0x84, 0x24, 0x48, 0x01, 0x00, 0x00, 0x88,
    0x44, 0x24, 0x03, 0x48, 0x8D, 0x4C, 0x24, 0x03, 0x48, 0x89, 0xD8, 0x48, 0xC1, 0xE8, 0x3F, 0x48,
    0x89, 0x84, 0x24, 0x38, 0x01, 0x00, 0x00, 0x88, 0x44, 0x24, 0x03, 0x4C, 0x89, 0xEF, 0x48, 0x8D,
    0x74, 0x24, 0x58, 0x48, 0x8D, 0x94, 0x24, 0x88, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF9, 0x49, 0x89,
    0xD8, 0x44, 0x8B, 0x4C, 0x24, 0x04, 0xE8, 0xB4, 0xF8, 0xFF, 0xFF]

theorem code_l1177b1 : ∀ x ∈ codeRange 0x111cd1 bytes_l1177b1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x11cd1 75 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1177fc : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x111d1c (movR64R64Effect 0x111d1c 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[14]
    (.letOp (n := 54) (.exec 0x111d1c (fun s => s.RIP = 0x111d1c) (movR64R64Effect 0x111d1c 0 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 55) (.out 0x111d1f (shrR64Effect 0x111d1f 4 0 63) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x111d1f (fun s => s.RIP = 0x111d1f) (shrR64Effect 0x111d1f 4 0 63) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 57) (.exec 0x111d23 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111d23 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x111d23 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111d23 0 (.sib 4 none 0 (.d32 0x140))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 58) (.exec 0x111d2b (StorePre 0x111d2b 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3)) s (0x111d2b + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x111d2b 4 0 (.sib 4 none 0 (.d8 0x3))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 59) (.exec 0x111d2f (fun s => s.RIP = 0x111d2f) (leaR64Effect 0x111d2f 1 (.sib 4 none 0 (.d8 0x3))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.out 0x111d34 (movR64R64Effect 0x111d34 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[12]
    (.letOp (n := 61) (.exec 0x111d34 (fun s => s.RIP = 0x111d34) (movR64R64Effect 0x111d34 0 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 62) (.out 0x111d37 (shrR64Effect 0x111d37 4 0 63) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[60]
    (.letOp (n := 63) (.exec 0x111d37 (fun s => s.RIP = 0x111d37) (shrR64Effect 0x111d37 4 0 63) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[60]
    (.letOp (n := 64) (.exec 0x111d3b (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111d3b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x111d3b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111d3b 0 (.sib 4 none 0 (.d32 0x130))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.exec 0x111d43 (StorePre 0x111d43 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3)) s (0x111d43 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x111d43 4 0 (.sib 4 none 0 (.d8 0x3))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 66) (.out 0x111d47 (leaR64Effect 0x111d47 7 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 67) (.exec 0x111d47 (fun s => s.RIP = 0x111d47) (leaR64Effect 0x111d47 7 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.out 0x111d4c (leaR64Effect 0x111d4c 6 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 69) (.exec 0x111d4c (fun s => s.RIP = 0x111d4c) (leaR64Effect 0x111d4c 6 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.out 0x111d51 (leaR64Effect 0x111d51 2 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 71) (.exec 0x111d51 (fun s => s.RIP = 0x111d51) (leaR64Effect 0x111d51 2 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.out 0x111d59 (movR64R64Effect 0x111d59 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[14]
    (.letOp (n := 73) (.exec 0x111d59 (fun s => s.RIP = 0x111d59) (movR64R64Effect 0x111d59 1 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 74) (.out 0x111d5c (movR64R64Effect 0x111d5c 8 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 12] []) (.reg (.gpr 8))) #v[12]
    (.letOp (n := 75) (.exec 0x111d5c (fun s => s.RIP = 0x111d5c) (movR64R64Effect 0x111d5c 8 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 76) (.out 0x111d5f (movR32M32Effect 0x111d5f 9 (.sib 4 none 0 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 77) (.exec 0x111d5f (LoadPre 0x111d5f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x111d5f + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x111d5f 9 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 78) (.out 0x111d64 (callEffect (fun _ => 0x1115d0) 0x111d69) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 79) (.exec 0x111d64 (PushPre 0x111d64 5) (callEffect (fun _ => 0x1115d0) 0x111d69) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 80) (.const ⟨64, 0x111d69⟩) #v[]
    (.terminate (.call ⟨.l1170b0, RegMap.args [(0, 62), (1, 72), (2, 70), (3, 3), (4, 78), (5, 5), (6, 68), (7, 66), (8, 74), (9, 76), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)] 81⟩ { target := .l117849, kept := #v[], arity := rfl, guard := some (Fin.last 80) })))))))))))))))))))))))))))))

def bytes_l1177fc : List UInt8 :=
  [0x4C, 0x89, 0xF0, 0x48, 0xC1, 0xE8, 0x3F, 0x48, 0x89, 0x84, 0x24, 0x40, 0x01, 0x00, 0x00, 0x88,
    0x44, 0x24, 0x03, 0x48, 0x8D, 0x4C, 0x24, 0x03, 0x4C, 0x89, 0xE0, 0x48, 0xC1, 0xE8, 0x3F, 0x48,
    0x89, 0x84, 0x24, 0x30, 0x01, 0x00, 0x00, 0x88, 0x44, 0x24, 0x03, 0x48, 0x8D, 0x7C, 0x24, 0x30,
    0x48, 0x8D, 0x74, 0x24, 0x58, 0x48, 0x8D, 0x94, 0x24, 0x88, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF1,
    0x4D, 0x89, 0xE0, 0x44, 0x8B, 0x4C, 0x24, 0x04, 0xE8, 0x67, 0xF8, 0xFF, 0xFF]

theorem code_l1177fc : ∀ x ∈ codeRange 0x111d1c bytes_l1177fc, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x11d1c 77 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l117849_1 : Block Op Label signature Reg.count 84 :=
  .letOp (n := 84) (.exec 0x111dd3 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111dd3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x111dd3 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111dd3 0 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[82, 4]
    (.terminate (.br ⟨.l1178bb, RegMap.args [(0, 82), (1, 72), (2, 68), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)] 85⟩))

def bytes_l117849_1 : List UInt8 :=
  [0x48, 0x89, 0x84, 0x24, 0xA8, 0x00, 0x00, 0x00]

theorem code_l117849_1 : ∀ x ∈ codeRange 0x111dd3 bytes_l117849_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x11dd3 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l117849 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x111d69 (movR64M64Effect 0x111d69 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x111d69 (LoadPre 0x111d69 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x111d69 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111d69 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x111d6e (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111d6e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x111d6e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x111d6e 0 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x111d73 (movR64M64Effect 0x111d73 0 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x111d73 (LoadPre 0x111d73 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x111d73 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111d73 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x111d78 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111d78 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x111d78 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x111d78 0 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x111d7d (movR64M64Effect 0x111d7d 0 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x111d7d (LoadPre 0x111d7d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x111d7d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111d7d 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x111d82 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111d82 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x111d82 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x111d82 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x111d87 (movR64M64Effect 0x111d87 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x111d87 (LoadPre 0x111d87 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x111d87 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111d87 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x111d8c (movR64M64Effect 0x111d8c 1 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x111d8c (LoadPre 0x111d8c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x111d8c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111d8c 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x111d91 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111d91 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x111d91 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x111d91 1 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x111d96 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111d96 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x111d96 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x111d96 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x111d9b (leaR64Effect 0x111d9b 2 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 69) (.exec 0x111d9b (fun s => s.RIP = 0x111d9b) (leaR64Effect 0x111d9b 2 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.out 0x111da0 (movR64M64Effect 0x111da0 0 (.base 2 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[68]
    (.letOp (n := 71) (.exec 0x111da0 (LoadPre 0x111da0 (fun s => AddrMode.addr (.base 2 .none) s (0x111da0 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x111da0 0 (.base 2 .none)) (Reg.operands [.gpr 2] [])) #v[68]
    (.letOp (n := 72) (.out 0x111da3 (movR64M64Effect 0x111da3 1 (.base 2 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[68]
    (.letOp (n := 73) (.exec 0x111da3 (LoadPre 0x111da3 (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x111da3 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x111da3 1 (.base 2 (.d8 0x8))) (Reg.operands [.gpr 2] [])) #v[68]
    (.letOp (n := 74) (.exec 0x111da7 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111da7 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x111da7 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111da7 0 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[70, 4]
    (.letOp (n := 75) (.exec 0x111daf (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111daf 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x111daf + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111daf 1 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[72, 4]
    (.letOp (n := 76) (.out 0x111db7 (movR64M64Effect 0x111db7 0 (.base 2 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[68]
    (.letOp (n := 77) (.exec 0x111db7 (LoadPre 0x111db7 (fun s => AddrMode.addr (.base 2 (.d8 0x10)) s (0x111db7 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x111db7 0 (.base 2 (.d8 0x10))) (Reg.operands [.gpr 2] [])) #v[68]
    (.letOp (n := 78) (.exec 0x111dbb (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111dbb 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x111dbb + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111dbb 0 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[76, 4]
    (.letOp (n := 79) (.out 0x111dc3 (movR64M64Effect 0x111dc3 0 (.base 2 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[68]
    (.letOp (n := 80) (.exec 0x111dc3 (LoadPre 0x111dc3 (fun s => AddrMode.addr (.base 2 (.d8 0x18)) s (0x111dc3 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x111dc3 0 (.base 2 (.d8 0x18))) (Reg.operands [.gpr 2] [])) #v[68]
    (.letOp (n := 81) (.exec 0x111dc7 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111dc7 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x111dc7 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111dc7 0 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[79, 4]
    (.letOp (n := 82) (.out 0x111dcf (movR64M64Effect 0x111dcf 0 (.base 2 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[68]
    (.letOp (n := 83) (.exec 0x111dcf (LoadPre 0x111dcf (fun s => AddrMode.addr (.base 2 (.d8 0x20)) s (0x111dcf + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x111dcf 0 (.base 2 (.d8 0x20))) (Reg.operands [.gpr 2] [])) #v[68]
    (b_l117849_1)))))))))))))))))))))))))))))))

def bytes_l117849 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x28, 0x48, 0x89, 0x44, 0x24, 0x78, 0x48, 0x8B, 0x44, 0x24, 0x20, 0x48,
    0x89, 0x44, 0x24, 0x70, 0x48, 0x8B, 0x44, 0x24, 0x18, 0x48, 0x89, 0x44, 0x24, 0x68, 0x48, 0x8B,
    0x44, 0x24, 0x08, 0x48, 0x8B, 0x4C, 0x24, 0x10, 0x48, 0x89, 0x4C, 0x24, 0x60, 0x48, 0x89, 0x44,
    0x24, 0x58, 0x48, 0x8D, 0x54, 0x24, 0x30, 0x48, 0x8B, 0x02, 0x48, 0x8B, 0x4A, 0x08, 0x48, 0x89,
    0x84, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x89, 0x8C, 0x24, 0x90, 0x00, 0x00, 0x00, 0x48, 0x8B,
    0x42, 0x10, 0x48, 0x89, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x42, 0x18, 0x48, 0x89,
    0x84, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x42, 0x20] ++ bytes_l117849_1

theorem code_l117849 : ∀ x ∈ codeRange 0x111d69 bytes_l117849, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x11d69 106 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l117849_1

@[cfg_block] def b_l1178bb : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x111ddb (movR64M64Effect 0x111ddb 0 (.sib 4 none 0 (.d32 0x148))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x111ddb (LoadPre 0x111ddb (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x148)) s (0x111ddb + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x111ddb 0 (.sib 4 none 0 (.d32 0x148))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x111de3 (StorePre 0x111de3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3)) s (0x111de3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x111de3 4 0 (.sib 4 none 0 (.d8 0x3))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x111de7 (leaR64Effect 0x111de7 0 (.sib 4 none 0 (.d8 0x3))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x111de7 (fun s => s.RIP = 0x111de7) (leaR64Effect 0x111de7 0 (.sib 4 none 0 (.d8 0x3))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.out 0x111dec (movR64M64Effect 0x111dec 1 (.sib 4 none 0 (.d32 0x138))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 59) (.exec 0x111dec (LoadPre 0x111dec (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x138)) s (0x111dec + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x111dec 1 (.sib 4 none 0 (.d32 0x138))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.exec 0x111df4 (StorePre 0x111df4 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3)) s (0x111df4 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x111df4 4 1 (.sib 4 none 0 (.d8 0x3))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[58, 4]
    (.letOp (n := 61) (.out 0x111df8 (movR64R64Effect 0x111df8 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 13] []) (.reg (.gpr 7))) #v[13]
    (.letOp (n := 62) (.exec 0x111df8 (fun s => s.RIP = 0x111df8) (movR64R64Effect 0x111df8 7 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 63) (.out 0x111dfb (leaR64Effect 0x111dfb 6 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 64) (.exec 0x111dfb (fun s => s.RIP = 0x111dfb) (leaR64Effect 0x111dfb 6 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x111e03 (leaR64Effect 0x111e03 2 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 66) (.exec 0x111e03 (fun s => s.RIP = 0x111e03) (leaR64Effect 0x111e03 2 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x111e0b (movR64R64Effect 0x111e0b 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 15] []) (.reg (.gpr 1))) #v[15]
    (.letOp (n := 68) (.exec 0x111e0b (fun s => s.RIP = 0x111e0b) (movR64R64Effect 0x111e0b 1 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 69) (.out 0x111e0e (movR64R64Effect 0x111e0e 8 3) (EffectPart.reads (.reg (.gpr 8)) [.gpr 3] []) (.reg (.gpr 8))) #v[3]
    (.letOp (n := 70) (.exec 0x111e0e (fun s => s.RIP = 0x111e0e) (movR64R64Effect 0x111e0e 8 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 71) (.out 0x111e11 (movR32M32Effect 0x111e11 9 (.sib 4 none 0 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 72) (.exec 0x111e11 (LoadPre 0x111e11 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x111e11 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x111e11 9 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.out 0x111e16 (movR64M64Effect 0x111e16 15 (.sib 4 none 0 (.d32 0x128))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 74) (.exec 0x111e16 (LoadPre 0x111e16 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x111e16 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x111e16 15 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.out 0x111e1e (pushR64Effect 0x111e1e 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[4, 73]
    (.letOp (n := 76) (.exec 0x111e1e (PushPre 0x111e1e 2) (pushR64Effect 0x111e1e 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[4, 73]
    (.letOp (n := 77) (.out 0x111e20 (movR64M64Effect 0x111e20 3 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[75]
    (.letOp (n := 78) (.exec 0x111e20 (LoadPre 0x111e20 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x111e20 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x111e20 3 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[75]
    (.letOp (n := 79) (.out 0x111e28 (pushR64Effect 0x111e28 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[75, 77]
    (.letOp (n := 80) (.exec 0x111e28 (PushPre 0x111e28 1) (pushR64Effect 0x111e28 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[75, 77]
    (.letOp (n := 81) (.out 0x111e29 (callEffect (fun _ => 0x1116c0) 0x111e2e) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[79]
    (.letOp (n := 82) (.exec 0x111e29 (PushPre 0x111e29 5) (callEffect (fun _ => 0x1116c0) 0x111e2e) (Reg.operands [.gpr 4] [])) #v[79]
    (.letOp (n := 83) (.const ⟨64, 0x111e2e⟩) #v[]
    (.terminate (.call ⟨.l1171a0, RegMap.args [(0, 56), (1, 67), (2, 65), (3, 77), (4, 81), (5, 5), (6, 63), (7, 61), (8, 69), (9, 71), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 73), (22, 22), (39, 39), (51, 51)] 84⟩ { target := .l11790e, kept := #v[], arity := rfl, guard := some (Fin.last 83) }))))))))))))))))))))))))))))))))

def bytes_l1178bb : List UInt8 :=
  [0x48, 0x8B, 0x84, 0x24, 0x48, 0x01, 0x00, 0x00, 0x88, 0x44, 0x24, 0x03, 0x48, 0x8D, 0x44, 0x24,
    0x03, 0x48, 0x8B, 0x8C, 0x24, 0x38, 0x01, 0x00, 0x00, 0x88, 0x4C, 0x24, 0x03, 0x4C, 0x89, 0xEF,
    0x48, 0x8D, 0xB4, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x94, 0x24, 0xD8, 0x00, 0x00, 0x00,
    0x4C, 0x89, 0xF9, 0x49, 0x89, 0xD8, 0x44, 0x8B, 0x4C, 0x24, 0x04, 0x4C, 0x8B, 0xBC, 0x24, 0x28,
    0x01, 0x00, 0x00, 0x41, 0x57, 0x48, 0x8B, 0x9C, 0x24, 0x88, 0x00, 0x00, 0x00, 0x53, 0xE8, 0x92,
    0xF8, 0xFF, 0xFF]

theorem code_l1178bb : ∀ x ∈ codeRange 0x111ddb bytes_l1178bb, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x11ddb 83 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11790e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x111e2e (addR64Imm8Effect 0x111e2e 4 0x10) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 54) (.exec 0x111e2e (fun s => s.RIP = 0x111e2e) (addR64Imm8Effect 0x111e2e 4 0x10) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x111e32 (movR64M64Effect 0x111e32 0 (.sib 4 none 0 (.d32 0x140))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x111e32 (LoadPre 0x111e32 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x111e32 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x111e32 0 (.sib 4 none 0 (.d32 0x140))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 57) (.exec 0x111e3a (StorePre 0x111e3a 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3)) s (0x111e3a + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x111e3a 4 0 (.sib 4 none 0 (.d8 0x3))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 53]
    (.letOp (n := 58) (.exec 0x111e3e (fun s => s.RIP = 0x111e3e) (leaR64Effect 0x111e3e 1 (.sib 4 none 0 (.d8 0x3))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 59) (.out 0x111e43 (movR64M64Effect 0x111e43 0 (.sib 4 none 0 (.d32 0x130))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 60) (.exec 0x111e43 (LoadPre 0x111e43 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x111e43 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x111e43 0 (.sib 4 none 0 (.d32 0x130))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 61) (.exec 0x111e4b (StorePre 0x111e4b 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3)) s (0x111e4b + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x111e4b 4 0 (.sib 4 none 0 (.d8 0x3))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 53]
    (.letOp (n := 62) (.out 0x111e4f (leaR64Effect 0x111e4f 7 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 63) (.exec 0x111e4f (fun s => s.RIP = 0x111e4f) (leaR64Effect 0x111e4f 7 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 64) (.out 0x111e54 (leaR64Effect 0x111e54 6 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[53]
    (.letOp (n := 65) (.exec 0x111e54 (fun s => s.RIP = 0x111e54) (leaR64Effect 0x111e54 6 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 66) (.out 0x111e5c (leaR64Effect 0x111e5c 2 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[53]
    (.letOp (n := 67) (.exec 0x111e5c (fun s => s.RIP = 0x111e5c) (leaR64Effect 0x111e5c 2 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 68) (.out 0x111e64 (movR64R64Effect 0x111e64 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[14]
    (.letOp (n := 69) (.exec 0x111e64 (fun s => s.RIP = 0x111e64) (movR64R64Effect 0x111e64 1 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 70) (.out 0x111e67 (movR64R64Effect 0x111e67 8 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 12] []) (.reg (.gpr 8))) #v[12]
    (.letOp (n := 71) (.exec 0x111e67 (fun s => s.RIP = 0x111e67) (movR64R64Effect 0x111e67 8 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 72) (.out 0x111e6a (movR32M32Effect 0x111e6a 14 (.sib 4 none 0 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[53]
    (.letOp (n := 73) (.exec 0x111e6a (LoadPre 0x111e6a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x111e6a + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x111e6a 14 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 74) (.out 0x111e6f (movR32R32Effect 0x111e6f 3 9 14) (EffectPart.reads (.reg (.gpr 9)) [.gpr 14] []) (.reg (.gpr 9))) #v[72]
    (.letOp (n := 75) (.exec 0x111e6f (fun s => s.RIP = 0x111e6f) (movR32R32Effect 0x111e6f 3 9 14) (Reg.operands [.gpr 14] [])) #v[72]
    (.letOp (n := 76) (.out 0x111e72 (pushR64Effect 0x111e72 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 77) (.exec 0x111e72 (PushPre 0x111e72 2) (pushR64Effect 0x111e72 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 78) (.out 0x111e74 (pushR64Effect 0x111e74 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[76, 3]
    (.letOp (n := 79) (.exec 0x111e74 (PushPre 0x111e74 1) (pushR64Effect 0x111e74 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[76, 3]
    (.letOp (n := 80) (.out 0x111e75 (callEffect (fun _ => 0x1116c0) 0x111e7a) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[78]
    (.letOp (n := 81) (.exec 0x111e75 (PushPre 0x111e75 5) (callEffect (fun _ => 0x1116c0) 0x111e7a) (Reg.operands [.gpr 4] [])) #v[78]
    (.letOp (n := 82) (.const ⟨64, 0x111e7a⟩) #v[]
    (.terminate (.call ⟨.l1171a0, RegMap.args [(0, 59), (1, 68), (2, 66), (3, 3), (4, 80), (5, 5), (6, 64), (7, 62), (8, 70), (9, 74), (10, 10), (11, 11), (12, 12), (13, 13), (14, 72), (15, 15), (22, 22), (39, 39), (51, 51)] 83⟩ { target := .l11795a, kept := #v[], arity := rfl, guard := some (Fin.last 82) })))))))))))))))))))))))))))))))

def bytes_l11790e : List UInt8 :=
  [0x48, 0x83, 0xC4, 0x10, 0x48, 0x8B, 0x84, 0x24, 0x40, 0x01, 0x00, 0x00, 0x88, 0x44, 0x24, 0x03,
    0x48, 0x8D, 0x4C, 0x24, 0x03, 0x48, 0x8B, 0x84, 0x24, 0x30, 0x01, 0x00, 0x00, 0x88, 0x44, 0x24,
    0x03, 0x48, 0x8D, 0x7C, 0x24, 0x30, 0x48, 0x8D, 0xB4, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x48, 0x8D,
    0x94, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF1, 0x4D, 0x89, 0xE0, 0x44, 0x8B, 0x74, 0x24,
    0x04, 0x45, 0x89, 0xF1, 0x41, 0x57, 0x53, 0xE8, 0x46, 0xF8, 0xFF, 0xFF]

theorem code_l11790e : ∀ x ∈ codeRange 0x111e2e bytes_l11790e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x11e2e 76 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11795a_1 : Block Op Label signature Reg.count 84 :=
  .letOp (n := 84) (.out 0x111ef3 (movR64M64Effect 0x111ef3 0 (.base 2 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[70]
    (.letOp (n := 85) (.exec 0x111ef3 (LoadPre 0x111ef3 (fun s => AddrMode.addr (.base 2 (.d8 0x20)) s (0x111ef3 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x111ef3 0 (.base 2 (.d8 0x20))) (Reg.operands [.gpr 2] [])) #v[70]
    (.letOp (n := 86) (.exec 0x111ef7 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111ef7 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x111ef7 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111ef7 0 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[84, 53]
    (.terminate (.br ⟨.l1179df, RegMap.args [(0, 84), (1, 74), (2, 70), (3, 3), (4, 53), (5, 5), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)] 87⟩))))

def bytes_l11795a_1 : List UInt8 :=
  [0x48, 0x8B, 0x42, 0x20, 0x48, 0x89, 0x84, 0x24, 0xF8, 0x00, 0x00, 0x00]

theorem code_l11795a_1 : ∀ x ∈ codeRange 0x111ef3 bytes_l11795a_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x11ef3 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11795a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x111e7a (addR64Imm8Effect 0x111e7a 4 0x10) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 54) (.exec 0x111e7a (fun s => s.RIP = 0x111e7a) (addR64Imm8Effect 0x111e7a 4 0x10) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x111e7e (movR64M64Effect 0x111e7e 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x111e7e (LoadPre 0x111e7e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x111e7e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111e7e 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 57) (.exec 0x111e83 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111e83 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x111e83 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111e83 0 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 53]
    (.letOp (n := 58) (.out 0x111e8b (movR64M64Effect 0x111e8b 0 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 59) (.exec 0x111e8b (LoadPre 0x111e8b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x111e8b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111e8b 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 60) (.exec 0x111e90 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111e90 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x111e90 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111e90 0 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[58, 53]
    (.letOp (n := 61) (.out 0x111e98 (movR64M64Effect 0x111e98 0 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 62) (.exec 0x111e98 (LoadPre 0x111e98 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x111e98 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111e98 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 63) (.exec 0x111e9d (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111e9d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x111e9d + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111e9d 0 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[61, 53]
    (.letOp (n := 64) (.out 0x111ea5 (movR64M64Effect 0x111ea5 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 65) (.exec 0x111ea5 (LoadPre 0x111ea5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x111ea5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111ea5 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 66) (.out 0x111eaa (movR64M64Effect 0x111eaa 1 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 67) (.exec 0x111eaa (LoadPre 0x111eaa (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x111eaa + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111eaa 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 68) (.exec 0x111eaf (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111eaf 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x111eaf + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111eaf 1 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[66, 53]
    (.letOp (n := 69) (.exec 0x111eb7 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111eb7 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x111eb7 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111eb7 0 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[64, 53]
    (.letOp (n := 70) (.out 0x111ebf (leaR64Effect 0x111ebf 2 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[53]
    (.letOp (n := 71) (.exec 0x111ebf (fun s => s.RIP = 0x111ebf) (leaR64Effect 0x111ebf 2 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 72) (.out 0x111ec4 (movR64M64Effect 0x111ec4 0 (.base 2 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[70]
    (.letOp (n := 73) (.exec 0x111ec4 (LoadPre 0x111ec4 (fun s => AddrMode.addr (.base 2 .none) s (0x111ec4 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x111ec4 0 (.base 2 .none)) (Reg.operands [.gpr 2] [])) #v[70]
    (.letOp (n := 74) (.out 0x111ec7 (movR64M64Effect 0x111ec7 1 (.base 2 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[70]
    (.letOp (n := 75) (.exec 0x111ec7 (LoadPre 0x111ec7 (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x111ec7 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x111ec7 1 (.base 2 (.d8 0x8))) (Reg.operands [.gpr 2] [])) #v[70]
    (.letOp (n := 76) (.exec 0x111ecb (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111ecb 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x111ecb + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111ecb 0 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[72, 53]
    (.letOp (n := 77) (.exec 0x111ed3 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111ed3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x111ed3 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111ed3 1 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[74, 53]
    (.letOp (n := 78) (.out 0x111edb (movR64M64Effect 0x111edb 0 (.base 2 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[70]
    (.letOp (n := 79) (.exec 0x111edb (LoadPre 0x111edb (fun s => AddrMode.addr (.base 2 (.d8 0x10)) s (0x111edb + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x111edb 0 (.base 2 (.d8 0x10))) (Reg.operands [.gpr 2] [])) #v[70]
    (.letOp (n := 80) (.exec 0x111edf (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111edf 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x111edf + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111edf 0 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[78, 53]
    (.letOp (n := 81) (.out 0x111ee7 (movR64M64Effect 0x111ee7 0 (.base 2 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[70]
    (.letOp (n := 82) (.exec 0x111ee7 (LoadPre 0x111ee7 (fun s => AddrMode.addr (.base 2 (.d8 0x18)) s (0x111ee7 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x111ee7 0 (.base 2 (.d8 0x18))) (Reg.operands [.gpr 2] [])) #v[70]
    (.letOp (n := 83) (.exec 0x111eeb (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111eeb 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x111eeb + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111eeb 0 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[81, 53]
    (b_l11795a_1)))))))))))))))))))))))))))))))

def bytes_l11795a : List UInt8 :=
  [0x48, 0x83, 0xC4, 0x10, 0x48, 0x8B, 0x44, 0x24, 0x28, 0x48, 0x89, 0x84, 0x24, 0xD0, 0x00, 0x00,
    0x00, 0x48, 0x8B, 0x44, 0x24, 0x20, 0x48, 0x89, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x48, 0x8B,
    0x44, 0x24, 0x18, 0x48, 0x89, 0x84, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x08,
    0x48, 0x8B, 0x4C, 0x24, 0x10, 0x48, 0x89, 0x8C, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84,
    0x24, 0xB0, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x54, 0x24, 0x30, 0x48, 0x8B, 0x02, 0x48, 0x8B, 0x4A,
    0x08, 0x48, 0x89, 0x84, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x8C, 0x24, 0xE0, 0x00, 0x00,
    0x00, 0x48, 0x8B, 0x42, 0x10, 0x48, 0x89, 0x84, 0x24, 0xE8, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x42,
    0x18, 0x48, 0x89, 0x84, 0x24, 0xF0, 0x00, 0x00, 0x00] ++ bytes_l11795a_1

theorem code_l11795a : ∀ x ∈ codeRange 0x111e7a bytes_l11795a, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x11e7a 121 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11795a_1

@[cfg_block] def b_l1179df : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x111eff (movR64M64Effect 0x111eff 2 (.sib 4 none 0 (.d32 0x150))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 54) (.exec 0x111eff (LoadPre 0x111eff (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x150)) s (0x111eff + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x111eff 2 (.sib 4 none 0 (.d32 0x150))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x111f07 (subR32R32Effect 0x111f07 3 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 14] []) (.reg (.gpr 2))) #v[53, 14]
    (.letOp (n := 56) (.out 0x111f07 (subR32R32Effect 0x111f07 3 2 14) (EffectPart.reads (.flag .ZF) [.gpr 2, .gpr 14] []) (.flag .ZF)) #v[53, 14]
    (.letOp (n := 57) (.exec 0x111f07 (fun s => s.RIP = 0x111f07) (subR32R32Effect 0x111f07 3 2 14) (Reg.operands [.gpr 2, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 58) (.out 0x111f0a (movR64Imm64Effect 0x111f0a 9 0x7fffffffffffffff) (EffectPart.reads (.reg (.gpr 9)) [] []) (.reg (.gpr 9))) #v[]
    (.letOp (n := 59) (.exec 0x111f0a (fun s => s.RIP = 0x111f0a) (movR64Imm64Effect 0x111f0a 9 0x7fffffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 60) (.pure (condOp 4)) #v[56]
    (.terminate (.condBr (Fin.last 60) ⟨.l117be8, RegMap.args [(2, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 58), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 56), (22, 22), (39, 39), (51, 51)] 61⟩ ⟨.l1179fa, RegMap.args [(2, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 58), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 56), (22, 22), (39, 39), (51, 51)] 61⟩)))))))))

def bytes_l1179df : List UInt8 :=
  [0x48, 0x8B, 0x94, 0x24, 0x50, 0x01, 0x00, 0x00, 0x44, 0x29, 0xF2, 0x49, 0xB9, 0xFF, 0xFF, 0xFF,
    0xFF, 0xFF, 0xFF, 0xFF, 0x7F, 0x0F, 0x84, 0xEE, 0x01, 0x00, 0x00]

theorem code_l1179df : ∀ x ∈ codeRange 0x111eff bytes_l1179df, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x11eff 27 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1179fa_1 : Block Op Label signature Reg.count 90 :=
  .letOp (n := 90) (.exec 0x111f6e (StorePre 0x111f6e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x111f6e + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x111f6e 8 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[75, 4]
    (.letOp (n := 91) (.pure (condOp 4)) #v[76]
    (.terminate (.condBr (Fin.last 91) ⟨.l1177a0, RegMap.args [(0, 87), (1, 78), (2, 83), (3, 3), (4, 4), (5, 5), (6, 85), (8, 75), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (19, 76), (22, 22), (39, 39), (51, 51)] 92⟩ ⟨.l117a59, RegMap.args [(0, 87), (1, 78), (2, 83), (3, 3), (4, 4), (5, 5), (6, 85), (8, 75), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (19, 76), (22, 22), (39, 39), (51, 51)] 92⟩)))

def bytes_l1179fa_1 : List UInt8 :=
  [0x44, 0x89, 0x44, 0x24, 0x04, 0x0F, 0x84, 0x47, 0xFD, 0xFF, 0xFF]

theorem code_l1179fa_1 : ∀ x ∈ codeRange 0x111f6e bytes_l1179fa_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x11f6e 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1179fa : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x111f1a (movR32R32Effect 0x111f1a 2 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 54) (.exec 0x111f1a (fun s => s.RIP = 0x111f1a) (movR32R32Effect 0x111f1a 2 0 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 55) (.out 0x111f1c (notR32Effect 0x111f1c 2 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x111f1c (fun s => s.RIP = 0x111f1c) (notR32Effect 0x111f1c 2 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x111f1e (leaR32Effect 0x111f1e 3 1 (.base 2 (.d8 0xc2))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2]
    (.letOp (n := 58) (.exec 0x111f1e (fun s => s.RIP = 0x111f1e) (leaR32Effect 0x111f1e 3 1 (.base 2 (.d8 0xc2))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 59) (.out 0x111f21 (andR32R32Effect 0x111f21 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[57, 55]
    (.letOp (n := 60) (.exec 0x111f21 (fun s => s.RIP = 0x111f21) (andR32R32Effect 0x111f21 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[57, 55]
    (.letOp (n := 61) (.out 0x111f23 (shrR32Effect 0x111f23 3 1 31) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[59]
    (.letOp (n := 62) (.exec 0x111f23 (fun s => s.RIP = 0x111f23) (shrR32Effect 0x111f23 3 1 31) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[59]
    (.letOp (n := 63) (.exec 0x111f26 (StorePre 0x111f26 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x111f26 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x111f26 4 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.out 0x111f2a (movzxR32M8Effect 0x111f2a 5 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 65) (.exec 0x111f2a (LoadPre 0x111f2a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x111f2a + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x111f2a 5 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.out 0x111f2f (negR32Effect 0x111f2f 2 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[64]
    (.letOp (n := 67) (.exec 0x111f2f (fun s => s.RIP = 0x111f2f) (negR32Effect 0x111f2f 2 0) (Reg.operands [.gpr 0] [])) #v[64]
    (.letOp (n := 68) (.exec 0x111f31 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111f31 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x150)) s (0x111f31 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111f31 2 (.sib 4 none 0 (.d32 0x150))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2, 4]
    (.letOp (n := 69) (.out 0x111f39 (movR32R32Effect 0x111f39 3 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[2]
    (.letOp (n := 70) (.exec 0x111f39 (fun s => s.RIP = 0x111f39) (movR32R32Effect 0x111f39 3 8 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 71) (.out 0x111f3c (xorR32Imm8Effect 0x111f3c 4 8 0x3e) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[69]
    (.letOp (n := 72) (.exec 0x111f3c (fun s => s.RIP = 0x111f3c) (xorR32Imm8Effect 0x111f3c 4 8 0x3e) (Reg.operands [.gpr 8] [])) #v[69]
    (.letOp (n := 73) (.out 0x111f40 (andR32R32Effect 0x111f40 3 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[71, 66]
    (.letOp (n := 74) (.exec 0x111f40 (fun s => s.RIP = 0x111f40) (andR32R32Effect 0x111f40 3 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[71, 66]
    (.letOp (n := 75) (.out 0x111f43 (xorR32Imm8Effect 0x111f43 4 8 0x3e) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[73]
    (.letOp (n := 76) (.out 0x111f43 (xorR32Imm8Effect 0x111f43 4 8 0x3e) (EffectPart.reads (.flag .ZF) [.gpr 8] []) (.flag .ZF)) #v[73]
    (.letOp (n := 77) (.exec 0x111f43 (fun s => s.RIP = 0x111f43) (xorR32Imm8Effect 0x111f43 4 8 0x3e) (Reg.operands [.gpr 8] [])) #v[73]
    (.letOp (n := 78) (.out 0x111f47 (movR64M64Effect 0x111f47 1 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 79) (.exec 0x111f47 (LoadPre 0x111f47 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x111f47 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111f47 1 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 80) (.out 0x111f4c (movzxR32M8Effect 0x111f4c 5 0 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 81) (.exec 0x111f4c (LoadPre 0x111f4c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x111f4c + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x111f4c 5 0 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 82) (.exec 0x111f51 (StorePre 0x111f51 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x111f51 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x111f51 4 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[80, 4]
    (.letOp (n := 83) (.out 0x111f55 (movzxR32M8Effect 0x111f55 5 2 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 84) (.exec 0x111f55 (LoadPre 0x111f55 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x111f55 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x111f55 5 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 85) (.out 0x111f5a (movR64M64Effect 0x111f5a 6 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 86) (.exec 0x111f5a (LoadPre 0x111f5a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x111f5a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x111f5a 6 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 87) (.out 0x111f62 (movzxR32M8Effect 0x111f62 8 0 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 88) (.exec 0x111f62 (LoadPre 0x111f62 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x111f62 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x111f62 8 0 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 89) (.exec 0x111f6a (StorePre 0x111f6a 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x111f6a + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x111f6a 4 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[87, 4]
    (b_l1179fa_1)))))))))))))))))))))))))))))))))))))

def bytes_l1179fa : List UInt8 :=
  [0x89, 0xD0, 0xF7, 0xD0, 0x8D, 0x4A, 0xC2, 0x21, 0xC1, 0xC1, 0xE9, 0x1F, 0x88, 0x4C, 0x24, 0x08,
    0x0F, 0xB6, 0x44, 0x24, 0x08, 0xF7, 0xD8, 0x48, 0x89, 0x94, 0x24, 0x50, 0x01, 0x00, 0x00, 0x41,
    0x89, 0xD0, 0x41, 0x83, 0xF0, 0x3E, 0x41, 0x21, 0xC0, 0x41, 0x83, 0xF0, 0x3E, 0x48, 0x8B, 0x4C,
    0x24, 0x58, 0x0F, 0xB6, 0x44, 0x24, 0x78, 0x88, 0x44, 0x24, 0x08, 0x0F, 0xB6, 0x54, 0x24, 0x08,
    0x48, 0x8B, 0xB4, 0x24, 0x88, 0x00, 0x00, 0x00, 0x0F, 0xB6, 0x84, 0x24, 0xA8, 0x00, 0x00, 0x00,
    0x88, 0x44, 0x24, 0x08] ++ bytes_l1179fa_1

theorem code_l1179fa : ∀ x ∈ codeRange 0x111f1a bytes_l1179fa, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x11f1a 84 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1179fa_1

@[cfg_block] def b_l117a59_1 : Block Op Label signature Reg.count 93 :=
  .letOp (n := 93) (.exec 0x111fbb (fun s => s.RIP = 0x111fbb) (fun _ => nopEffect 0x111fbb 5) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l117aa0, RegMap.args [(0, 67), (1, 85), (2, 81), (4, 4), (5, 5), (6, 87), (7, 83), (8, 8), (9, 9), (12, 91), (13, 13), (14, 89), (22, 22), (39, 39), (51, 51)] 94⟩))

def bytes_l117a59_1 : List UInt8 :=
  [0x0F, 0x1F, 0x44, 0x00, 0x00]

theorem code_l117a59_1 : ∀ x ∈ codeRange 0x111fbb bytes_l117a59_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x11fbb 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l117a59 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x111f79 (movzxR32M8Effect 0x111f79 5 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x111f79 (LoadPre 0x111f79 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x111f79 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x111f79 5 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x111f7e (andR64R64Effect 0x111f7e 6 9) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 9] []) (.reg (.gpr 6))) #v[6, 9]
    (.letOp (n := 56) (.exec 0x111f7e (fun s => s.RIP = 0x111f7e) (andR64R64Effect 0x111f7e 6 9) (Reg.operands [.gpr 6, .gpr 9] [])) #v[6, 9]
    (.letOp (n := 57) (.out 0x111f81 (movR64R64Effect 0x111f81 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[55]
    (.letOp (n := 58) (.exec 0x111f81 (fun s => s.RIP = 0x111f81) (movR64R64Effect 0x111f81 7 6) (Reg.operands [.gpr 6] [])) #v[55]
    (.letOp (n := 59) (.out 0x111f84 (negR64Effect 0x111f84 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[57]
    (.letOp (n := 60) (.exec 0x111f84 (fun s => s.RIP = 0x111f84) (negR64Effect 0x111f84 7) (Reg.operands [.gpr 7] [])) #v[57]
    (.letOp (n := 61) (.out 0x111f87 (xorR64R64Effect 0x111f87 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[59, 55]
    (.letOp (n := 62) (.exec 0x111f87 (fun s => s.RIP = 0x111f87) (xorR64R64Effect 0x111f87 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[59, 55]
    (.letOp (n := 63) (.out 0x111f8a (negR64Effect 0x111f8a 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 64) (.exec 0x111f8a (fun s => s.RIP = 0x111f8a) (negR64Effect 0x111f8a 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 65) (.out 0x111f8d (andR64R64Effect 0x111f8d 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[63, 61]
    (.letOp (n := 66) (.exec 0x111f8d (fun s => s.RIP = 0x111f8d) (andR64R64Effect 0x111f8d 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[63, 61]
    (.letOp (n := 67) (.out 0x111f90 (xorR64R64Effect 0x111f90 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[65, 55]
    (.letOp (n := 68) (.exec 0x111f90 (fun s => s.RIP = 0x111f90) (xorR64R64Effect 0x111f90 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[65, 55]
    (.letOp (n := 69) (.out 0x111f93 (andR64R64Effect 0x111f93 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 9] []) (.reg (.gpr 1))) #v[1, 9]
    (.letOp (n := 70) (.exec 0x111f93 (fun s => s.RIP = 0x111f93) (andR64R64Effect 0x111f93 1 9) (Reg.operands [.gpr 1, .gpr 9] [])) #v[1, 9]
    (.letOp (n := 71) (.out 0x111f96 (movR64R64Effect 0x111f96 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 1] []) (.reg (.gpr 6))) #v[69]
    (.letOp (n := 72) (.exec 0x111f96 (fun s => s.RIP = 0x111f96) (movR64R64Effect 0x111f96 6 1) (Reg.operands [.gpr 1] [])) #v[69]
    (.letOp (n := 73) (.out 0x111f99 (negR64Effect 0x111f99 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[71]
    (.letOp (n := 74) (.exec 0x111f99 (fun s => s.RIP = 0x111f99) (negR64Effect 0x111f99 6) (Reg.operands [.gpr 6] [])) #v[71]
    (.letOp (n := 75) (.out 0x111f9c (xorR64R64Effect 0x111f9c 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[73, 69]
    (.letOp (n := 76) (.exec 0x111f9c (fun s => s.RIP = 0x111f9c) (xorR64R64Effect 0x111f9c 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[73, 69]
    (.letOp (n := 77) (.out 0x111f9f (negR64Effect 0x111f9f 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[2]
    (.letOp (n := 78) (.exec 0x111f9f (fun s => s.RIP = 0x111f9f) (negR64Effect 0x111f9f 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 79) (.out 0x111fa2 (andR64R64Effect 0x111fa2 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[77, 75]
    (.letOp (n := 80) (.exec 0x111fa2 (fun s => s.RIP = 0x111fa2) (andR64R64Effect 0x111fa2 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[77, 75]
    (.letOp (n := 81) (.out 0x111fa5 (xorR64R64Effect 0x111fa5 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[79, 69]
    (.letOp (n := 82) (.exec 0x111fa5 (fun s => s.RIP = 0x111fa5) (xorR64R64Effect 0x111fa5 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[79, 69]
    (.letOp (n := 83) (.out 0x111fa8 (movR32Imm32Effect 0x111fa8 5 7 0x1) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 84) (.exec 0x111fa8 (fun s => s.RIP = 0x111fa8) (movR32Imm32Effect 0x111fa8 5 7 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 85) (.out 0x111fad (movR32R32Effect 0x111fad 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 8] []) (.reg (.gpr 1))) #v[8]
    (.letOp (n := 86) (.exec 0x111fad (fun s => s.RIP = 0x111fad) (movR32R32Effect 0x111fad 3 1 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 87) (.out 0x111fb0 (xorR32R32Effect 0x111fb0 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[75, 75]
    (.letOp (n := 88) (.exec 0x111fb0 (fun s => s.RIP = 0x111fb0) (xorR32R32Effect 0x111fb0 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[75, 75]
    (.letOp (n := 89) (.out 0x111fb2 (xorR32R32Effect 0x111fb2 3 14 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 14] []) (.reg (.gpr 14))) #v[14, 14]
    (.letOp (n := 90) (.exec 0x111fb2 (fun s => s.RIP = 0x111fb2) (xorR32R32Effect 0x111fb2 3 14 14) (Reg.operands [.gpr 14, .gpr 14] [])) #v[14, 14]
    (.letOp (n := 91) (.out 0x111fb5 (movR32Imm32Effect 0x111fb5 6 12 0x1) (EffectPart.reads (.reg (.gpr 12)) [] []) (.reg (.gpr 12))) #v[]
    (.letOp (n := 92) (.exec 0x111fb5 (fun s => s.RIP = 0x111fb5) (movR32Imm32Effect 0x111fb5 6 12 0x1) (Reg.operands [] [])) #v[]
    (b_l117a59_1))))))))))))))))))))))))))))))))))))))))

def bytes_l117a59 : List UInt8 :=
  [0x0F, 0xB6, 0x44, 0x24, 0x08, 0x4C, 0x21, 0xCE, 0x48, 0x89, 0xF7, 0x48, 0xF7, 0xDF, 0x48, 0x31,
    0xF7, 0x48, 0xF7, 0xD8, 0x48, 0x21, 0xF8, 0x48, 0x31, 0xF0, 0x4C, 0x21, 0xC9, 0x48, 0x89, 0xCE,
    0x48, 0xF7, 0xDE, 0x48, 0x31, 0xCE, 0x48, 0xF7, 0xDA, 0x48, 0x21, 0xF2, 0x48, 0x31, 0xCA, 0xBF,
    0x01, 0x00, 0x00, 0x00, 0x44, 0x89, 0xC1, 0x31, 0xF6, 0x45, 0x31, 0xF6, 0x41, 0xBC, 0x01, 0x00,
    0x00, 0x00] ++ bytes_l117a59_1

theorem code_l117a59 : ∀ x ∈ codeRange 0x111f79 bytes_l117a59, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x11f79 66 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l117a59_1

@[cfg_block] def b_l117aa0_1 : Block Op Label signature Reg.count 91 :=
  .letOp (n := 91) (.out 0x11200f (movzxR32M8Effect 0x11200f 6 15 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 92) (.exec 0x11200f (LoadPre 0x11200f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11200f + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x11200f 6 15 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 93) (.out 0x112015 (negR64Effect 0x112015 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15] []) (.reg (.gpr 15))) #v[91]
    (.letOp (n := 94) (.exec 0x112015 (fun s => s.RIP = 0x112015) (negR64Effect 0x112015 15) (Reg.operands [.gpr 15] [])) #v[91]
    (.letOp (n := 95) (.out 0x112018 (xorR64R64Effect 0x112018 2 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 5] []) (.reg (.gpr 2))) #v[86, 88]
    (.letOp (n := 96) (.exec 0x112018 (fun s => s.RIP = 0x112018) (xorR64R64Effect 0x112018 2 5) (Reg.operands [.gpr 2, .gpr 5] [])) #v[86, 88]
    (.letOp (n := 97) (.out 0x11201b (andR64R64Effect 0x11201b 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 15] []) (.reg (.gpr 2))) #v[95, 93]
    (.letOp (n := 98) (.exec 0x11201b (fun s => s.RIP = 0x11201b) (andR64R64Effect 0x11201b 2 15) (Reg.operands [.gpr 2, .gpr 15] [])) #v[95, 93]
    (.letOp (n := 99) (.out 0x11201e (xorR64R64Effect 0x11201e 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 2] []) (.reg (.gpr 5))) #v[88, 97]
    (.letOp (n := 100) (.exec 0x11201e (fun s => s.RIP = 0x11201e) (xorR64R64Effect 0x11201e 5 2) (Reg.operands [.gpr 5, .gpr 2] [])) #v[88, 97]
    (.terminate (.br ⟨.l117b01, RegMap.args [(0, 0), (1, 1), (2, 97), (3, 78), (4, 4), (5, 99), (6, 6), (7, 7), (8, 71), (9, 67), (10, 82), (11, 53), (12, 12), (13, 13), (14, 14), (15, 93), (22, 22), (39, 39), (51, 51)] 101⟩)))))))))))

def bytes_l117aa0_1 : List UInt8 :=
  [0x44, 0x0F, 0xB6, 0x7C, 0x24, 0x08, 0x49, 0xF7, 0xDF, 0x48, 0x31, 0xEA, 0x4C, 0x21, 0xFA, 0x48,
    0x31, 0xD5]

theorem code_l117aa0_1 : ∀ x ∈ codeRange 0x11200f bytes_l117aa0_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1200f 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l117aa0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x111fc0 (movR64R64Effect 0x111fc0 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[2]
    (.letOp (n := 54) (.exec 0x111fc0 (fun s => s.RIP = 0x111fc0) (movR64R64Effect 0x111fc0 11 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 55) (.out 0x111fc3 (movR64Imm64Effect 0x111fc3 2 0x7fffffffffffffff) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 56) (.exec 0x111fc3 (fun s => s.RIP = 0x111fc3) (movR64Imm64Effect 0x111fc3 2 0x7fffffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x111fcd (leaR64Effect 0x111fcd 9 (.base 2 (.d8 0x1))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[55]
    (.letOp (n := 58) (.exec 0x111fcd (fun s => s.RIP = 0x111fcd) (leaR64Effect 0x111fcd 9 (.base 2 (.d8 0x1))) (Reg.operands [.gpr 2] [])) #v[55]
    (.letOp (n := 59) (.out 0x111fd1 (movR64R64Effect 0x111fd1 2 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5] []) (.reg (.gpr 2))) #v[5]
    (.letOp (n := 60) (.exec 0x111fd1 (fun s => s.RIP = 0x111fd1) (movR64R64Effect 0x111fd1 2 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 61) (.out 0x111fd4 (xorR64R64Effect 0x111fd4 2 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 9] []) (.reg (.gpr 2))) #v[59, 57]
    (.letOp (n := 62) (.exec 0x111fd4 (fun s => s.RIP = 0x111fd4) (xorR64R64Effect 0x111fd4 2 9) (Reg.operands [.gpr 2, .gpr 9] [])) #v[59, 57]
    (.letOp (n := 63) (.out 0x111fd7 (subR64R64Effect 0x111fd7 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2] []) (.reg (.gpr 9))) #v[57, 61]
    (.letOp (n := 64) (.exec 0x111fd7 (fun s => s.RIP = 0x111fd7) (subR64R64Effect 0x111fd7 9 2) (Reg.operands [.gpr 9, .gpr 2] [])) #v[57, 61]
    (.letOp (n := 65) (.out 0x111fda (andR64R64Effect 0x111fda 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2] []) (.reg (.gpr 9))) #v[63, 61]
    (.letOp (n := 66) (.exec 0x111fda (fun s => s.RIP = 0x111fda) (andR64R64Effect 0x111fda 9 2) (Reg.operands [.gpr 9, .gpr 2] [])) #v[63, 61]
    (.letOp (n := 67) (.out 0x111fdd (shrR64Effect 0x111fdd 4 9 63) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[65]
    (.letOp (n := 68) (.exec 0x111fdd (fun s => s.RIP = 0x111fdd) (shrR64Effect 0x111fdd 4 9 63) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[65]
    (.letOp (n := 69) (.out 0x111fe1 (movR32R32Effect 0x111fe1 3 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[0]
    (.letOp (n := 70) (.exec 0x111fe1 (fun s => s.RIP = 0x111fe1) (movR32R32Effect 0x111fe1 3 8 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 71) (.out 0x111fe4 (andR8Imm8Effect 0x111fe4 4 8 0x1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[69]
    (.letOp (n := 72) (.exec 0x111fe4 (fun s => s.RIP = 0x111fe4) (andR8Imm8Effect 0x111fe4 4 8 0x1) (Reg.operands [.gpr 8] [])) #v[69]
    (.letOp (n := 73) (.exec 0x111fe8 (StorePre 0x111fe8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x111fe8 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x111fe8 5 8 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[71, 4]
    (.letOp (n := 74) (.out 0x111fed (movzxR32M8Effect 0x111fed 5 3 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 75) (.exec 0x111fed (LoadPre 0x111fed (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x111fed + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x111fed 5 3 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 76) (.out 0x111ff2 (negR64Effect 0x111ff2 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[74]
    (.letOp (n := 77) (.exec 0x111ff2 (fun s => s.RIP = 0x111ff2) (negR64Effect 0x111ff2 3) (Reg.operands [.gpr 3] [])) #v[74]
    (.letOp (n := 78) (.out 0x111ff5 (andR64R64Effect 0x111ff5 3 11) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 11] []) (.reg (.gpr 3))) #v[76, 53]
    (.letOp (n := 79) (.exec 0x111ff5 (fun s => s.RIP = 0x111ff5) (andR64R64Effect 0x111ff5 3 11) (Reg.operands [.gpr 3, .gpr 11] [])) #v[76, 53]
    (.letOp (n := 80) (.out 0x111ff8 (movR32R32Effect 0x111ff8 3 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 9] []) (.reg (.gpr 10))) #v[67]
    (.letOp (n := 81) (.exec 0x111ff8 (fun s => s.RIP = 0x111ff8) (movR32R32Effect 0x111ff8 3 10 9) (Reg.operands [.gpr 9] [])) #v[67]
    (.letOp (n := 82) (.out 0x111ffb (andR8R8Effect 0x111ffb 3 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0] []) (.reg (.gpr 10))) #v[80, 0]
    (.letOp (n := 83) (.exec 0x111ffb (fun s => s.RIP = 0x111ffb) (andR8R8Effect 0x111ffb 3 10 0) (Reg.operands [.gpr 10, .gpr 0] [])) #v[80, 0]
    (.letOp (n := 84) (.out 0x111ffe (movR32Imm32Effect 0x111ffe 5 2 0x2) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 85) (.exec 0x111ffe (fun s => s.RIP = 0x111ffe) (movR32Imm32Effect 0x111ffe 5 2 0x2) (Reg.operands [] [])) #v[]
    (.letOp (n := 86) (.out 0x112003 (subR64R64Effect 0x112003 2 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 5] []) (.reg (.gpr 2))) #v[84, 5]
    (.letOp (n := 87) (.exec 0x112003 (fun s => s.RIP = 0x112003) (subR64R64Effect 0x112003 2 5) (Reg.operands [.gpr 2, .gpr 5] [])) #v[84, 5]
    (.letOp (n := 88) (.out 0x112006 (addR64Imm8Effect 0x112006 5 0x2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5] []) (.reg (.gpr 5))) #v[5]
    (.letOp (n := 89) (.exec 0x112006 (fun s => s.RIP = 0x112006) (addR64Imm8Effect 0x112006 5 0x2) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 90) (.exec 0x11200a (StorePre 0x11200a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11200a + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11200a 5 10 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[82, 4]
    (b_l117aa0_1))))))))))))))))))))))))))))))))))))))

def bytes_l117aa0 : List UInt8 :=
  [0x49, 0x89, 0xD3, 0x48, 0xBA, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F, 0x4C, 0x8D, 0x4A,
    0x01, 0x48, 0x89, 0xEA, 0x4C, 0x31, 0xCA, 0x49, 0x29, 0xD1, 0x49, 0x21, 0xD1, 0x49, 0xC1, 0xE9,
    0x3F, 0x41, 0x89, 0xC0, 0x41, 0x80, 0xE0, 0x01, 0x44, 0x88, 0x44, 0x24, 0x08, 0x0F, 0xB6, 0x5C,
    0x24, 0x08, 0x48, 0xF7, 0xDB, 0x4C, 0x21, 0xDB, 0x45, 0x89, 0xCA, 0x41, 0x20, 0xC2, 0xBA, 0x02,
    0x00, 0x00, 0x00, 0x48, 0x29, 0xEA, 0x48, 0x83, 0xC5, 0x02, 0x44, 0x88, 0x54, 0x24, 0x08] ++ bytes_l117aa0_1

theorem code_l117aa0 : ∀ x ∈ codeRange 0x111fc0 bytes_l117aa0, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x11fc0 79 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l117aa0_1

@[cfg_block] def b_l117b01 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x112021 (StorePre 0x112021 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x112021 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x112021 5 10 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[10, 4]
    (.letOp (n := 54) (.out 0x112026 (movzxR32M8Effect 0x112026 6 15 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 55) (.exec 0x112026 (LoadPre 0x112026 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x112026 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x112026 6 15 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x11202c (negR64Effect 0x11202c 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15] []) (.reg (.gpr 15))) #v[54]
    (.letOp (n := 57) (.exec 0x11202c (fun s => s.RIP = 0x11202c) (negR64Effect 0x11202c 15) (Reg.operands [.gpr 15] [])) #v[54]
    (.letOp (n := 58) (.out 0x11202f (movR64R64Effect 0x11202f 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0] []) (.reg (.gpr 2))) #v[0]
    (.letOp (n := 59) (.exec 0x11202f (fun s => s.RIP = 0x11202f) (movR64R64Effect 0x11202f 2 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 60) (.out 0x112032 (xorR64R64Effect 0x112032 2 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 11] []) (.reg (.gpr 2))) #v[58, 11]
    (.letOp (n := 61) (.exec 0x112032 (fun s => s.RIP = 0x112032) (xorR64R64Effect 0x112032 2 11) (Reg.operands [.gpr 2, .gpr 11] [])) #v[58, 11]
    (.letOp (n := 62) (.out 0x112035 (andR64R64Effect 0x112035 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 15] []) (.reg (.gpr 2))) #v[60, 56]
    (.letOp (n := 63) (.exec 0x112035 (fun s => s.RIP = 0x112035) (andR64R64Effect 0x112035 2 15) (Reg.operands [.gpr 2, .gpr 15] [])) #v[60, 56]
    (.letOp (n := 64) (.out 0x112038 (xorR64R64Effect 0x112038 2 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 11] []) (.reg (.gpr 2))) #v[62, 11]
    (.letOp (n := 65) (.exec 0x112038 (fun s => s.RIP = 0x112038) (xorR64R64Effect 0x112038 2 11) (Reg.operands [.gpr 2, .gpr 11] [])) #v[62, 11]
    (.letOp (n := 66) (.out 0x11203b (leaR64Effect 0x11203b 11 (.sib 3 (some 0) 0 .none)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 3, .gpr 0] []) (.reg (.gpr 11))) #v[3, 0]
    (.letOp (n := 67) (.exec 0x11203b (fun s => s.RIP = 0x11203b) (leaR64Effect 0x11203b 11 (.sib 3 (some 0) 0 .none)) (Reg.operands [.gpr 3, .gpr 0] [])) #v[3, 0]
    (.letOp (n := 68) (.out 0x11203f (subR64R64Effect 0x11203f 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[0, 3]
    (.letOp (n := 69) (.exec 0x11203f (fun s => s.RIP = 0x11203f) (subR64R64Effect 0x11203f 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (.letOp (n := 70) (.exec 0x112042 (StorePre 0x112042 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x112042 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x112042 5 10 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[10, 4]
    (.letOp (n := 71) (.out 0x112047 (movzxR32M8Effect 0x112047 5 3 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 72) (.exec 0x112047 (LoadPre 0x112047 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x112047 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x112047 5 3 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.out 0x11204c (negR64Effect 0x11204c 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[71]
    (.letOp (n := 74) (.exec 0x11204c (fun s => s.RIP = 0x11204c) (negR64Effect 0x11204c 3) (Reg.operands [.gpr 3] [])) #v[71]
    (.letOp (n := 75) (.out 0x11204f (xorR64R64Effect 0x11204f 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[68, 66]
    (.letOp (n := 76) (.exec 0x11204f (fun s => s.RIP = 0x11204f) (xorR64R64Effect 0x11204f 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[68, 66]
    (.letOp (n := 77) (.out 0x112052 (andR64R64Effect 0x112052 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[75, 73]
    (.letOp (n := 78) (.exec 0x112052 (fun s => s.RIP = 0x112052) (andR64R64Effect 0x112052 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[75, 73]
    (.letOp (n := 79) (.out 0x112055 (xorR64R64Effect 0x112055 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[77, 66]
    (.letOp (n := 80) (.exec 0x112055 (fun s => s.RIP = 0x112055) (xorR64R64Effect 0x112055 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[77, 66]
    (.letOp (n := 81) (.exec 0x112058 (StorePre 0x112058 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x112058 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x112058 5 10 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[10, 4]
    (.letOp (n := 82) (.out 0x11205d (movzxR32M8Effect 0x11205d 6 11 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 83) (.exec 0x11205d (LoadPre 0x11205d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11205d + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x11205d 6 11 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 84) (.out 0x112063 (negR64Effect 0x112063 11) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11] []) (.reg (.gpr 11))) #v[82]
    (.letOp (n := 85) (.exec 0x112063 (fun s => s.RIP = 0x112063) (negR64Effect 0x112063 11) (Reg.operands [.gpr 11] [])) #v[82]
    (.terminate (.br ⟨.l117b46, RegMap.args [(0, 79), (1, 1), (2, 64), (3, 73), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 84), (12, 12), (13, 13), (14, 14), (15, 56), (22, 22), (39, 39), (51, 51)] 86⟩))))))))))))))))))))))))))))))))))

def bytes_l117b01 : List UInt8 :=
  [0x44, 0x88, 0x54, 0x24, 0x08, 0x44, 0x0F, 0xB6, 0x7C, 0x24, 0x08, 0x49, 0xF7, 0xDF, 0x48, 0x89,
    0xC2, 0x4C, 0x31, 0xDA, 0x4C, 0x21, 0xFA, 0x4C, 0x31, 0xDA, 0x4C, 0x8D, 0x1C, 0x03, 0x48, 0x29,
    0xD8, 0x44, 0x88, 0x54, 0x24, 0x08, 0x0F, 0xB6, 0x5C, 0x24, 0x08, 0x48, 0xF7, 0xDB, 0x4C, 0x31,
    0xD8, 0x48, 0x21, 0xD8, 0x4C, 0x31, 0xD8, 0x44, 0x88, 0x54, 0x24, 0x08, 0x44, 0x0F, 0xB6, 0x5C,
    0x24, 0x08, 0x49, 0xF7, 0xDB]

theorem code_l117b01 : ∀ x ∈ codeRange 0x112021 bytes_l117b01, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x12021 69 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l117b46 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x112066 (movR64R64Effect 0x112066 15 14) (EffectPart.reads (.reg (.gpr 15)) [.gpr 14] []) (.reg (.gpr 15))) #v[14]
    (.letOp (n := 54) (.exec 0x112066 (fun s => s.RIP = 0x112066) (movR64R64Effect 0x112066 15 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 55) (.out 0x112069 (xorR64R64Effect 0x112069 15 7) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 7] []) (.reg (.gpr 15))) #v[53, 7]
    (.letOp (n := 56) (.exec 0x112069 (fun s => s.RIP = 0x112069) (xorR64R64Effect 0x112069 15 7) (Reg.operands [.gpr 15, .gpr 7] [])) #v[53, 7]
    (.letOp (n := 57) (.out 0x11206c (andR64R64Effect 0x11206c 15 11) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 11] []) (.reg (.gpr 15))) #v[55, 11]
    (.letOp (n := 58) (.exec 0x11206c (fun s => s.RIP = 0x11206c) (andR64R64Effect 0x11206c 15 11) (Reg.operands [.gpr 15, .gpr 11] [])) #v[55, 11]
    (.letOp (n := 59) (.exec 0x11206f (StorePre 0x11206f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11206f + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11206f 5 10 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[10, 4]
    (.letOp (n := 60) (.out 0x112074 (movzxR32M8Effect 0x112074 6 10 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 61) (.exec 0x112074 (LoadPre 0x112074 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x112074 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x112074 6 10 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.out 0x11207a (negR64Effect 0x11207a 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[60]
    (.letOp (n := 63) (.exec 0x11207a (fun s => s.RIP = 0x11207a) (negR64Effect 0x11207a 10) (Reg.operands [.gpr 10] [])) #v[60]
    (.letOp (n := 64) (.out 0x11207d (movR64R64Effect 0x11207d 3 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 12] []) (.reg (.gpr 3))) #v[12]
    (.letOp (n := 65) (.exec 0x11207d (fun s => s.RIP = 0x11207d) (movR64R64Effect 0x11207d 3 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 66) (.out 0x112080 (xorR64R64Effect 0x112080 3 6) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 6] []) (.reg (.gpr 3))) #v[64, 6]
    (.letOp (n := 67) (.exec 0x112080 (fun s => s.RIP = 0x112080) (xorR64R64Effect 0x112080 3 6) (Reg.operands [.gpr 3, .gpr 6] [])) #v[64, 6]
    (.letOp (n := 68) (.out 0x112083 (andR64R64Effect 0x112083 3 10) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 10] []) (.reg (.gpr 3))) #v[66, 62]
    (.letOp (n := 69) (.exec 0x112083 (fun s => s.RIP = 0x112083) (andR64R64Effect 0x112083 3 10) (Reg.operands [.gpr 3, .gpr 10] [])) #v[66, 62]
    (.letOp (n := 70) (.out 0x112086 (movR64R64Effect 0x112086 10 7) (EffectPart.reads (.reg (.gpr 10)) [.gpr 7] []) (.reg (.gpr 10))) #v[7]
    (.letOp (n := 71) (.exec 0x112086 (fun s => s.RIP = 0x112086) (movR64R64Effect 0x112086 10 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 72) (.out 0x112089 (negR64Effect 0x112089 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[70]
    (.letOp (n := 73) (.exec 0x112089 (fun s => s.RIP = 0x112089) (negR64Effect 0x112089 10) (Reg.operands [.gpr 10] [])) #v[70]
    (.letOp (n := 74) (.exec 0x11208c (StorePre 0x11208c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11208c + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11208c 5 9 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[9, 4]
    (.letOp (n := 75) (.out 0x112091 (movzxR32M8Effect 0x112091 6 11 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 76) (.exec 0x112091 (LoadPre 0x112091 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x112091 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x112091 6 11 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 77) (.out 0x112097 (negR64Effect 0x112097 11) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11] []) (.reg (.gpr 11))) #v[75]
    (.letOp (n := 78) (.exec 0x112097 (fun s => s.RIP = 0x112097) (negR64Effect 0x112097 11) (Reg.operands [.gpr 11] [])) #v[75]
    (.letOp (n := 79) (.out 0x11209a (xorR64R64Effect 0x11209a 10 7) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 7] []) (.reg (.gpr 10))) #v[72, 7]
    (.letOp (n := 80) (.exec 0x11209a (fun s => s.RIP = 0x11209a) (xorR64R64Effect 0x11209a 10 7) (Reg.operands [.gpr 10, .gpr 7] [])) #v[72, 7]
    (.letOp (n := 81) (.out 0x11209d (andR64R64Effect 0x11209d 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 11] []) (.reg (.gpr 10))) #v[79, 77]
    (.letOp (n := 82) (.exec 0x11209d (fun s => s.RIP = 0x11209d) (andR64R64Effect 0x11209d 10 11) (Reg.operands [.gpr 10, .gpr 11] [])) #v[79, 77]
    (.letOp (n := 83) (.out 0x1120a0 (xorR64R64Effect 0x1120a0 15 7) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 7] []) (.reg (.gpr 15))) #v[57, 7]
    (.letOp (n := 84) (.exec 0x1120a0 (fun s => s.RIP = 0x1120a0) (xorR64R64Effect 0x1120a0 15 7) (Reg.operands [.gpr 15, .gpr 7] [])) #v[57, 7]
    (.terminate (.br ⟨.l117b83, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 68), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 81), (11, 77), (12, 12), (13, 13), (14, 14), (15, 83), (22, 22), (39, 39), (51, 51)] 85⟩)))))))))))))))))))))))))))))))))

def bytes_l117b46 : List UInt8 :=
  [0x4D, 0x89, 0xF7, 0x49, 0x31, 0xFF, 0x4D, 0x21, 0xDF, 0x44, 0x88, 0x54, 0x24, 0x08, 0x44, 0x0F,
    0xB6, 0x54, 0x24, 0x08, 0x49, 0xF7, 0xDA, 0x4C, 0x89, 0xE3, 0x48, 0x31, 0xF3, 0x4C, 0x21, 0xD3,
    0x49, 0x89, 0xFA, 0x49, 0xF7, 0xDA, 0x44, 0x88, 0x4C, 0x24, 0x08, 0x44, 0x0F, 0xB6, 0x5C, 0x24,
    0x08, 0x49, 0xF7, 0xDB, 0x49, 0x31, 0xFA, 0x4D, 0x21, 0xDA, 0x49, 0x31, 0xFF]

theorem code_l117b46 : ∀ x ∈ codeRange 0x112066 bytes_l117b46, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x12066 61 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l117b83 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1120a3 (xorR64R64Effect 0x1120a3 10 7) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 7] []) (.reg (.gpr 10))) #v[10, 7]
    (.letOp (n := 54) (.exec 0x1120a3 (fun s => s.RIP = 0x1120a3) (xorR64R64Effect 0x1120a3 10 7) (Reg.operands [.gpr 10, .gpr 7] [])) #v[10, 7]
    (.letOp (n := 55) (.exec 0x1120a6 (StorePre 0x1120a6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1120a6 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1120a6 5 8 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[8, 4]
    (.letOp (n := 56) (.out 0x1120ab (movzxR32M8Effect 0x1120ab 5 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 57) (.exec 0x1120ab (LoadPre 0x1120ab (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1120ab + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1120ab 5 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.out 0x1120b0 (negR64Effect 0x1120b0 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[56]
    (.letOp (n := 59) (.exec 0x1120b0 (fun s => s.RIP = 0x1120b0) (negR64Effect 0x1120b0 7) (Reg.operands [.gpr 7] [])) #v[56]
    (.letOp (n := 60) (.out 0x1120b3 (andR64R64Effect 0x1120b3 7 10) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 10] []) (.reg (.gpr 7))) #v[58, 53]
    (.letOp (n := 61) (.exec 0x1120b3 (fun s => s.RIP = 0x1120b3) (andR64R64Effect 0x1120b3 7 10) (Reg.operands [.gpr 7, .gpr 10] [])) #v[58, 53]
    (.letOp (n := 62) (.out 0x1120b6 (addR64R64Effect 0x1120b6 14 7) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 7] []) (.reg (.gpr 14))) #v[14, 60]
    (.letOp (n := 63) (.exec 0x1120b6 (fun s => s.RIP = 0x1120b6) (addR64R64Effect 0x1120b6 14 7) (Reg.operands [.gpr 14, .gpr 7] [])) #v[14, 60]
    (.letOp (n := 64) (.out 0x1120b9 (movR64R64Effect 0x1120b9 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[6]
    (.letOp (n := 65) (.exec 0x1120b9 (fun s => s.RIP = 0x1120b9) (movR64R64Effect 0x1120b9 7 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 66) (.out 0x1120bc (negR64Effect 0x1120bc 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[64]
    (.letOp (n := 67) (.exec 0x1120bc (fun s => s.RIP = 0x1120bc) (negR64Effect 0x1120bc 7) (Reg.operands [.gpr 7] [])) #v[64]
    (.letOp (n := 68) (.exec 0x1120bf (StorePre 0x1120bf 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1120bf + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1120bf 5 9 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[9, 4]
    (.letOp (n := 69) (.out 0x1120c4 (movzxR32M8Effect 0x1120c4 6 9 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 70) (.exec 0x1120c4 (LoadPre 0x1120c4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1120c4 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1120c4 6 9 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.out 0x1120ca (negR64Effect 0x1120ca 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[69]
    (.letOp (n := 72) (.exec 0x1120ca (fun s => s.RIP = 0x1120ca) (negR64Effect 0x1120ca 9) (Reg.operands [.gpr 9] [])) #v[69]
    (.letOp (n := 73) (.out 0x1120cd (xorR64R64Effect 0x1120cd 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[66, 6]
    (.letOp (n := 74) (.exec 0x1120cd (fun s => s.RIP = 0x1120cd) (xorR64R64Effect 0x1120cd 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[66, 6]
    (.letOp (n := 75) (.out 0x1120d0 (andR64R64Effect 0x1120d0 7 9) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 9] []) (.reg (.gpr 7))) #v[73, 71]
    (.letOp (n := 76) (.exec 0x1120d0 (fun s => s.RIP = 0x1120d0) (andR64R64Effect 0x1120d0 7 9) (Reg.operands [.gpr 7, .gpr 9] [])) #v[73, 71]
    (.letOp (n := 77) (.out 0x1120d3 (xorR64R64Effect 0x1120d3 3 6) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 6] []) (.reg (.gpr 3))) #v[3, 6]
    (.letOp (n := 78) (.exec 0x1120d3 (fun s => s.RIP = 0x1120d3) (xorR64R64Effect 0x1120d3 3 6) (Reg.operands [.gpr 3, .gpr 6] [])) #v[3, 6]
    (.letOp (n := 79) (.out 0x1120d6 (xorR64R64Effect 0x1120d6 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[75, 6]
    (.letOp (n := 80) (.exec 0x1120d6 (fun s => s.RIP = 0x1120d6) (xorR64R64Effect 0x1120d6 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[75, 6]
    (.letOp (n := 81) (.out 0x1120d9 (sarR64Effect 0x1120d9 3 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 82) (.exec 0x1120d9 (fun s => s.RIP = 0x1120d9) (sarR64Effect 0x1120d9 3 0 1) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[0]
    (.letOp (n := 83) (.out 0x1120dc (addR64R64Effect 0x1120dc 15 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 15] []) (.reg (.gpr 15))) #v[15, 15]
    (.letOp (n := 84) (.exec 0x1120dc (fun s => s.RIP = 0x1120dc) (addR64R64Effect 0x1120dc 15 15) (Reg.operands [.gpr 15, .gpr 15] [])) #v[15, 15]
    (.letOp (n := 85) (.out 0x1120df (addR64R64Effect 0x1120df 3 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 3] []) (.reg (.gpr 3))) #v[77, 77]
    (.letOp (n := 86) (.exec 0x1120df (fun s => s.RIP = 0x1120df) (addR64R64Effect 0x1120df 3 3) (Reg.operands [.gpr 3, .gpr 3] [])) #v[77, 77]
    (.terminate (.br ⟨.l117bc2, RegMap.args [(0, 81), (1, 1), (2, 2), (3, 85), (4, 4), (5, 5), (6, 6), (7, 79), (8, 8), (9, 71), (10, 53), (11, 11), (12, 12), (13, 13), (14, 62), (15, 83), (22, 22), (39, 39), (51, 51)] 87⟩)))))))))))))))))))))))))))))))))))

def bytes_l117b83 : List UInt8 :=
  [0x49, 0x31, 0xFA, 0x44, 0x88, 0x44, 0x24, 0x08, 0x0F, 0xB6, 0x7C, 0x24, 0x08, 0x48, 0xF7, 0xDF,
    0x4C, 0x21, 0xD7, 0x49, 0x01, 0xFE, 0x48, 0x89, 0xF7, 0x48, 0xF7, 0xDF, 0x44, 0x88, 0x4C, 0x24,
    0x08, 0x44, 0x0F, 0xB6, 0x4C, 0x24, 0x08, 0x49, 0xF7, 0xD9, 0x48, 0x31, 0xF7, 0x4C, 0x21, 0xCF,
    0x48, 0x31, 0xF3, 0x48, 0x31, 0xF7, 0x48, 0xD1, 0xF8, 0x4D, 0x01, 0xFF, 0x48, 0x01, 0xDB]

theorem code_l117b83 : ∀ x ∈ codeRange 0x1120a3 bytes_l117b83, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x120a3 63 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l117bc2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1120e2 (StorePre 0x1120e2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1120e2 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1120e2 5 8 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[8, 4]
    (.letOp (n := 54) (.out 0x1120e7 (movzxR32M8Effect 0x1120e7 5 6 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 55) (.exec 0x1120e7 (LoadPre 0x1120e7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1120e7 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1120e7 5 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x1120ec (negR64Effect 0x1120ec 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[54]
    (.letOp (n := 57) (.exec 0x1120ec (fun s => s.RIP = 0x1120ec) (negR64Effect 0x1120ec 6) (Reg.operands [.gpr 6] [])) #v[54]
    (.letOp (n := 58) (.out 0x1120ef (andR64R64Effect 0x1120ef 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7] []) (.reg (.gpr 6))) #v[56, 7]
    (.letOp (n := 59) (.exec 0x1120ef (fun s => s.RIP = 0x1120ef) (andR64R64Effect 0x1120ef 6 7) (Reg.operands [.gpr 6, .gpr 7] [])) #v[56, 7]
    (.letOp (n := 60) (.out 0x1120f2 (addR64R64Effect 0x1120f2 12 6) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 6] []) (.reg (.gpr 12))) #v[12, 58]
    (.letOp (n := 61) (.exec 0x1120f2 (fun s => s.RIP = 0x1120f2) (addR64R64Effect 0x1120f2 12 6) (Reg.operands [.gpr 12, .gpr 6] [])) #v[12, 58]
    (.letOp (n := 62) (.out 0x1120f5 (movR64R64Effect 0x1120f5 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[15]
    (.letOp (n := 63) (.exec 0x1120f5 (fun s => s.RIP = 0x1120f5) (movR64R64Effect 0x1120f5 7 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 64) (.out 0x1120f8 (movR64R64Effect 0x1120f8 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[3]
    (.letOp (n := 65) (.exec 0x1120f8 (fun s => s.RIP = 0x1120f8) (movR64R64Effect 0x1120f8 6 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.terminate (.br ⟨.l117bdb, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 64), (7, 62), (8, 8), (10, 10), (11, 11), (12, 60), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)] 66⟩))))))))))))))

def bytes_l117bc2 : List UInt8 :=
  [0x44, 0x88, 0x44, 0x24, 0x08, 0x0F, 0xB6, 0x74, 0x24, 0x08, 0x48, 0xF7, 0xDE, 0x48, 0x21, 0xFE,
    0x49, 0x01, 0xF4, 0x4C, 0x89, 0xFF, 0x48, 0x89, 0xDE]

theorem code_l117bc2 : ∀ x ∈ codeRange 0x1120e2 bytes_l117bc2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x120e2 25 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l117bdb : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1120fb (decR32Effect 0x1120fb 2 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1]
    (.letOp (n := 54) (.out 0x1120fb (decR32Effect 0x1120fb 2 1) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.flag .ZF)) #v[1]
    (.letOp (n := 55) (.exec 0x1120fb (fun s => s.RIP = 0x1120fb) (decR32Effect 0x1120fb 2 1) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1]
    (.letOp (n := 56) (.pure (condOp 5)) #v[54]
    (.terminate (.condBr (Fin.last 56) ⟨.l117aa0, RegMap.args [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 54), (22, 22), (39, 39), (51, 51)] 57⟩ ⟨.l117be3, RegMap.args [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 54), (22, 22), (39, 39), (51, 51)] 57⟩)))))

def bytes_l117bdb : List UInt8 :=
  [0xFF, 0xC9, 0x0F, 0x85, 0xBD, 0xFE, 0xFF, 0xFF]

theorem code_l117bdb : ∀ x ∈ codeRange 0x1120fb bytes_l117bdb, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x120fb 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l117be3 : Block Op Label signature Reg.count 53 :=
  .terminate (.br ⟨.l1177b1, RegMap.args (entryMap (live .l117be3)) 53⟩)

def bytes_l117be3 : List UInt8 :=
  [0xE9, 0xC9, 0xFB, 0xFF, 0xFF]

theorem code_l117be3 : ∀ x ∈ codeRange 0x112103 bytes_l117be3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x12103 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l117be8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x112108 (movR64M64Effect 0x112108 0 (.sib 4 none 0 (.d32 0x118))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x112108 (LoadPre 0x112108 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x112108 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x112108 0 (.sib 4 none 0 (.d32 0x118))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x112110 (orR64M64Effect 0x112110 0 (.sib 4 none 0 (.d32 0x108))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[53, 4]
    (.letOp (n := 56) (.exec 0x112110 (LoadPre 0x112110 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x112110 + BitVec.ofNat 64 8)) 8) (orR64M64Effect 0x112110 0 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 57) (.out 0x112118 (orR64M64Effect 0x112118 0 (.sib 4 none 0 (.d32 0x100))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[55, 4]
    (.letOp (n := 58) (.exec 0x112118 (LoadPre 0x112118 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x112118 + BitVec.ofNat 64 8)) 8) (orR64M64Effect 0x112118 0 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 59) (.out 0x112120 (orR64M64Effect 0x112120 0 (.sib 4 none 0 (.d32 0x110))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[57, 4]
    (.letOp (n := 60) (.out 0x112120 (orR64M64Effect 0x112120 0 (.sib 4 none 0 (.d32 0x110))) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 4] []) (.flag .ZF)) #v[57, 4]
    (.letOp (n := 61) (.exec 0x112120 (LoadPre 0x112120 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x112120 + BitVec.ofNat 64 8)) 8) (orR64M64Effect 0x112120 0 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 62) (.out 0x112128 (atFlags (condHolds 5) (setccR8Effect 0x112128 3 3)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 3))) #v[3, 60]
    (.letOp (n := 63) (.exec 0x112128 (fun s => s.RIP = 0x112128) (atFlags (condHolds 5) (setccR8Effect 0x112128 3 3)) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[3, 60]
    (.letOp (n := 64) (.out 0x11212b (movR32M32LowEffect 0x11212b 2 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 65) (.exec 0x11212b (LoadPre 0x11212b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x11212b + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x11212b 2 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.out 0x11212f (leaR64Effect 0x11212f 6 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 67) (.exec 0x11212f (fun s => s.RIP = 0x11212f) (leaR64Effect 0x11212f 6 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.out 0x112137 (movR64M64Effect 0x112137 14 (.sib 4 none 0 (.d32 0x120))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 69) (.exec 0x112137 (LoadPre 0x112137 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x112137 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x112137 14 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.out 0x11213f (movR64R64Effect 0x11213f 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[68]
    (.letOp (n := 71) (.exec 0x11213f (fun s => s.RIP = 0x11213f) (movR64R64Effect 0x11213f 7 14) (Reg.operands [.gpr 14] [])) #v[68]
    (.letOp (n := 72) (.out 0x112142 (movR64M64Effect 0x112142 1 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 73) (.exec 0x112142 (LoadPre 0x112142 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x112142 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x112142 1 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.out 0x11214a (callEffect (fun _ => 0x1126c0) 0x11214f) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 75) (.exec 0x11214a (PushPre 0x11214a 5) (callEffect (fun _ => 0x1126c0) 0x11214f) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 76) (.const ⟨64, 0x11214f⟩) #v[]
    (.terminate (.call ⟨.l1181a0, RegMap.args [(0, 59), (1, 72), (2, 64), (3, 62), (4, 74), (5, 5), (6, 66), (7, 70), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 68), (15, 15), (19, 60), (22, 22), (39, 39), (51, 51)] 77⟩ { target := .l117c2f, kept := #v[], arity := rfl, guard := some (Fin.last 76) })))))))))))))))))))))))))

def bytes_l117be8 : List UInt8 :=
  [0x48, 0x8B, 0x84, 0x24, 0x18, 0x01, 0x00, 0x00, 0x48, 0x0B, 0x84, 0x24, 0x08, 0x01, 0x00, 0x00,
    0x48, 0x0B, 0x84, 0x24, 0x00, 0x01, 0x00, 0x00, 0x48, 0x0B, 0x84, 0x24, 0x10, 0x01, 0x00, 0x00,
    0x0F, 0x95, 0xC3, 0x8B, 0x54, 0x24, 0x78, 0x48, 0x8D, 0xB4, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x4C,
    0x8B, 0xB4, 0x24, 0x20, 0x01, 0x00, 0x00, 0x4C, 0x89, 0xF7, 0x48, 0x8B, 0x8C, 0x24, 0x80, 0x00,
    0x00, 0x00, 0xE8, 0x71, 0x05, 0x00, 0x00]

theorem code_l117be8 : ∀ x ∈ codeRange 0x112108 bytes_l117be8, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x12108 71 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l117c2f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11214f (movR64M64Effect 0x11214f 0 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x11214f (LoadPre 0x11214f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x11214f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11214f 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x112154 (xorR64Imm8Effect 0x112154 0 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x112154 (fun s => s.RIP = 0x112154) (xorR64Imm8Effect 0x112154 0 0x1) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x112158 (orR64M64Effect 0x112158 0 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[55, 4]
    (.letOp (n := 58) (.exec 0x112158 (LoadPre 0x112158 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x112158 + BitVec.ofNat 64 5)) 8) (orR64M64Effect 0x112158 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 59) (.out 0x11215d (orR64M64Effect 0x11215d 0 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[57, 4]
    (.letOp (n := 60) (.exec 0x11215d (LoadPre 0x11215d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x11215d + BitVec.ofNat 64 5)) 8) (orR64M64Effect 0x11215d 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 61) (.out 0x112162 (orR64M64Effect 0x112162 0 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[59, 4]
    (.letOp (n := 62) (.out 0x112162 (orR64M64Effect 0x112162 0 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 4] []) (.flag .ZF)) #v[59, 4]
    (.letOp (n := 63) (.exec 0x112162 (LoadPre 0x112162 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x112162 + BitVec.ofNat 64 5)) 8) (orR64M64Effect 0x112162 0 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 64) (.out 0x112167 (atFlags (condHolds 4) (setccR8Effect 0x112167 3 0)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 0))) #v[61, 62]
    (.letOp (n := 65) (.exec 0x112167 (fun s => s.RIP = 0x112167) (atFlags (condHolds 4) (setccR8Effect 0x112167 3 0)) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[61, 62]
    (.letOp (n := 66) (.out 0x11216a (andR8R8Effect 0x11216a 2 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[64, 3]
    (.letOp (n := 67) (.exec 0x11216a (fun s => s.RIP = 0x11216a) (andR8R8Effect 0x11216a 2 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[64, 3]
    (.letOp (n := 68) (.exec 0x11216c (StorePre 0x11216c 4 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x11216c + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x11216c 4 0 (.base 14 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 14] [])) #v[66, 14]
    (.letOp (n := 69) (.out 0x112170 (addR64Imm32Effect 0x112170 4 0x158) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 70) (.exec 0x112170 (fun s => s.RIP = 0x112170) (addR64Imm32Effect 0x112170 4 0x158) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.out 0x112177 (popR64Effect 0x112177 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[69]
    (.letOp (n := 72) (.out 0x112177 (popR64Effect 0x112177 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[69]
    (.letOp (n := 73) (.exec 0x112177 (PopPre 0x112177) (popR64Effect 0x112177 1 3) (Reg.operands [.gpr 4] [])) #v[69]
    (.letOp (n := 74) (.out 0x112178 (popR64Effect 0x112178 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[72]
    (.letOp (n := 75) (.out 0x112178 (popR64Effect 0x112178 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[72]
    (.letOp (n := 76) (.exec 0x112178 (PopPre 0x112178) (popR64Effect 0x112178 2 12) (Reg.operands [.gpr 4] [])) #v[72]
    (.letOp (n := 77) (.out 0x11217a (popR64Effect 0x11217a 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[75]
    (.letOp (n := 78) (.out 0x11217a (popR64Effect 0x11217a 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[75]
    (.letOp (n := 79) (.exec 0x11217a (PopPre 0x11217a) (popR64Effect 0x11217a 2 13) (Reg.operands [.gpr 4] [])) #v[75]
    (.letOp (n := 80) (.out 0x11217c (popR64Effect 0x11217c 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[78]
    (.letOp (n := 81) (.out 0x11217c (popR64Effect 0x11217c 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[78]
    (.letOp (n := 82) (.exec 0x11217c (PopPre 0x11217c) (popR64Effect 0x11217c 2 14) (Reg.operands [.gpr 4] [])) #v[78]
    (.letOp (n := 83) (.out 0x11217e (popR64Effect 0x11217e 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[81]
    (.letOp (n := 84) (.out 0x11217e (popR64Effect 0x11217e 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[81]
    (.letOp (n := 85) (.exec 0x11217e (PopPre 0x11217e) (popR64Effect 0x11217e 2 15) (Reg.operands [.gpr 4] [])) #v[81]
    (.letOp (n := 86) (.out 0x112180 (popR64Effect 0x112180 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[84]
    (.letOp (n := 87) (.out 0x112180 (popR64Effect 0x112180 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[84]
    (.letOp (n := 88) (.exec 0x112180 (PopPre 0x112180) (popR64Effect 0x112180 1 5) (Reg.operands [.gpr 4] [])) #v[84]
    (.letOp (n := 89) (.out 0x112181 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[87]
    (.letOp (n := 90) (.out 0x112181 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[87]
    (.letOp (n := 91) (.exec 0x112181 (RetPre 0x112181) (retEffect) (Reg.operands [.gpr 4] [])) #v[87]
    (.terminate (.ret (RegMap.args [(0, 66), (2, 2), (3, 71), (4, 90), (5, 86), (8, 8), (10, 10), (11, 11), (12, 74), (13, 77), (14, 80), (15, 83), (22, 22), (39, 39), (51, 51)] 92) (some ⟨89, by decide⟩)))))))))))))))))))))))))))))))))))))))))

def bytes_l117c2f : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x58, 0x48, 0x83, 0xF0, 0x01, 0x48, 0x0B, 0x44, 0x24, 0x60, 0x48, 0x0B,
    0x44, 0x24, 0x68, 0x48, 0x0B, 0x44, 0x24, 0x70, 0x0F, 0x94, 0xC0, 0x20, 0xD8, 0x41, 0x88, 0x46,
    0x20, 0x48, 0x81, 0xC4, 0x58, 0x01, 0x00, 0x00, 0x5B, 0x41, 0x5C, 0x41, 0x5D,
    0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l117c2f : ∀ x ∈ codeRange 0x11214f bytes_l117c2f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1214f 51 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1181a0 : Block Op Label signature Reg.count 53 :=
  cutBlock 0x1126c0

def bytes_l1181a0 : List UInt8 :=
  [0x41, 0x57]

theorem code_l1181a0 : ∀ x ∈ codeRange 0x1126c0 bytes_l1181a0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x126c0 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

end P256.Proofs.Field.Inverse.SafeGcd.Core.Machine
