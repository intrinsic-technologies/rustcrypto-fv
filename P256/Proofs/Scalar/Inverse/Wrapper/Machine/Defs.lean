import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Scalar.Inverse.Wrapper.Machine.Labels
import P256.Proofs.Common.CFG.EvalAttr
import P256.Proofs.Common.Lift.Generated.Footprints

namespace P256.Proofs.Scalar.Inverse.Wrapper.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

@[cfg_block] def b_l118910 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x112e30 (pushR64Effect 0x112e30 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[4, 3]
    (.letOp (n := 54) (.exec 0x112e30 (PushPre 0x112e30 1) (pushR64Effect 0x112e30 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[4, 3]
    (.letOp (n := 55) (.out 0x112e31 (subR64Imm8Effect 0x112e31 4 0x30) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[53]
    (.letOp (n := 56) (.exec 0x112e31 (fun s => s.RIP = 0x112e31) (subR64Imm8Effect 0x112e31 4 0x30) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 57) (.out 0x112e35 (movR64R64Effect 0x112e35 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 58) (.exec 0x112e35 (fun s => s.RIP = 0x112e35) (movR64R64Effect 0x112e35 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 59) (.out 0x112e38 (leaR64Effect 0x112e38 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[55]
    (.letOp (n := 60) (.exec 0x112e38 (fun s => s.RIP = 0x112e38) (leaR64Effect 0x112e38 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 61) (.out 0x112e3d (movR64Imm64Effect 0x112e3d 1 0x332e375511ff43b1) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 62) (.exec 0x112e3d (fun s => s.RIP = 0x112e3d) (movR64Imm64Effect 0x112e3d 1 0x332e375511ff43b1) (Reg.operands [] [])) #v[]
    (.letOp (n := 63) (.out 0x112e47 (movR64Imm32Effect 0x112e47 2 0x2025e0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 64) (.exec 0x112e47 (fun s => s.RIP = 0x112e47) (movR64Imm32Effect 0x112e47 2 0x2025e0) (Reg.operands [] [])) #v[]
    (.letOp (n := 65) (.out 0x112e4e (movR64Imm32Effect 0x112e4e 8 0x2025c0) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 66) (.exec 0x112e4e (fun s => s.RIP = 0x112e4e) (movR64Imm32Effect 0x112e4e 8 0x2025c0) (Reg.operands [] [])) #v[]
    (.letOp (n := 67) (.out 0x112e55 (callEffect (fun _ => 0x111b70) 0x112e5a) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[55]
    (.letOp (n := 68) (.exec 0x112e55 (PushPre 0x112e55 5) (callEffect (fun _ => 0x111b70) 0x112e5a) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 69) (.const ⟨64, 0x112e5a⟩) #v[]
    (.terminate (.call ⟨.l117650, RegMap.args [(0, 0), (1, 61), (2, 63), (3, 57), (4, 67), (5, 5), (6, 6), (7, 59), (8, 65), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)] 70⟩ { target := .l11893a, kept := #v[], arity := rfl, guard := some (Fin.last 69) }))))))))))))))))))

def bytes_l118910 : List UInt8 :=
  [0x53, 0x48, 0x83, 0xEC, 0x30, 0x48, 0x89, 0xFB, 0x48, 0x8D, 0x7C, 0x24, 0x08, 0x48, 0xB9, 0xB1, 0x43, 0xFF, 0x11, 0x55, 0x37, 0x2E, 0x33, 0x48, 0xc7, 0xc2, 0xe0, 0x25, 0x20, 0x00, 0x49, 0xc7, 0xc0, 0xc0, 0x25, 0x20, 0x00, 0xE8, 0x16, 0xED, 0xFF, 0xFF]

theorem code_l118910 : ∀ x ∈ codeRange 0x112e30 bytes_l118910, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x12e30 42 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11893a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x112e5a (movR64M64Effect 0x112e5a 0 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x112e5a (LoadPre 0x112e5a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x112e5a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x112e5a 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x112e5f (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112e5f 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x112e5f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x112e5f 0 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[53, 3]
    (.letOp (n := 56) (.out 0x112e63 (movR64M64Effect 0x112e63 0 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x112e63 (LoadPre 0x112e63 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x112e63 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x112e63 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x112e68 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112e68 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x112e68 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x112e68 0 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[56, 3]
    (.letOp (n := 59) (.out 0x112e6c (movR64M64Effect 0x112e6c 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x112e6c (LoadPre 0x112e6c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x112e6c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x112e6c 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x112e71 (movR64M64Effect 0x112e71 1 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 62) (.exec 0x112e71 (LoadPre 0x112e71 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x112e71 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x112e71 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x112e76 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112e76 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x112e76 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x112e76 1 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 64) (.exec 0x112e7a (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112e7a 3 (fun s => AddrMode.addr (.base 3 .none) s (0x112e7a + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x112e7a 0 (.base 3 .none)) (Reg.operands [.gpr 0, .gpr 3] [])) #v[59, 3]
    (.letOp (n := 65) (.out 0x112e7d (movR32M32LowEffect 0x112e7d 7 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 66) (.exec 0x112e7d (LoadPre 0x112e7d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x112e7d + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x112e7d 7 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x112e81 (callEffect (fun _ => 0x119070) 0x112e86) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 68) (.exec 0x112e81 (PushPre 0x112e81 5) (callEffect (fun _ => 0x119070) 0x112e86) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.const ⟨64, 0x112e86⟩) #v[]
    (.terminate (.call ⟨.l126f60, RegMap.args [(0, 59), (1, 61), (2, 2), (3, 3), (4, 67), (5, 5), (7, 65), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)] 70⟩ { target := .l118966, kept := #v[], arity := rfl, guard := some (Fin.last 69) }))))))))))))))))))

def bytes_l11893a : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x20, 0x48, 0x89, 0x43, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x18, 0x48, 0x89, 0x43, 0x10, 0x48, 0x8B, 0x44, 0x24, 0x08, 0x48, 0x8B, 0x4C, 0x24, 0x10, 0x48, 0x89, 0x4B, 0x08, 0x48, 0x89, 0x03, 0x8B, 0x7C, 0x24, 0x28, 0xe8, 0xea, 0x61, 0x00, 0x00]

theorem code_l11893a : ∀ x ∈ codeRange 0x112e5a bytes_l11893a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x12e5a 44 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l118966 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x112e86 (StorePre 0x112e86 3 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x112e86 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x112e86 3 0 (.base 3 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (.letOp (n := 54) (.out 0x112e89 (movR64R64Effect 0x112e89 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 55) (.exec 0x112e89 (fun s => s.RIP = 0x112e89) (movR64R64Effect 0x112e89 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 56) (.out 0x112e8c (addR64Imm8Effect 0x112e8c 4 0x30) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 57) (.exec 0x112e8c (fun s => s.RIP = 0x112e8c) (addR64Imm8Effect 0x112e8c 4 0x30) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.out 0x112e90 (popR64Effect 0x112e90 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[56]
    (.letOp (n := 59) (.out 0x112e90 (popR64Effect 0x112e90 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[56]
    (.letOp (n := 60) (.exec 0x112e90 (PopPre 0x112e90) (popR64Effect 0x112e90 1 3) (Reg.operands [.gpr 4] [])) #v[56]
    (.letOp (n := 61) (.out 0x112e91 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[59]
    (.letOp (n := 62) (.out 0x112e91 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 63) (.exec 0x112e91 (RetPre 0x112e91) (retEffect) (Reg.operands [.gpr 4] [])) #v[59]
    (.terminate (.ret (RegMap.args [(0, 54), (2, 2), (3, 58), (4, 62), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)] 64) (some ⟨61, by decide⟩)))))))))))))

def bytes_l118966 : List UInt8 :=
  [0x88, 0x43, 0x20, 0x48, 0x89, 0xD8, 0x48, 0x83, 0xC4, 0x30, 0x5B, 0xC3]

theorem code_l118966 : ∀ x ∈ codeRange 0x112e86 bytes_l118966, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x12e86 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l117650 : Block Op Label signature Reg.count 53 :=
  cutBlock 0x111b70

def bytes_l117650 : List UInt8 :=
  [0x55]

theorem code_l117650 : ∀ x ∈ codeRange 0x111b70 bytes_l117650, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x11b70 1 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126f60 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x119070 (subR64Imm8Effect 0x119070 4 0x1) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 54) (.exec 0x119070 (fun s => s.RIP = 0x119070) (subR64Imm8Effect 0x119070 4 0x1) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x119074 (StorePre 0x119074 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x119074 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x119074 4 7 (.sib 4 none 0 .none)) (Reg.operands [.gpr 7, .gpr 4] [])) #v[7, 53]
    (.letOp (n := 56) (.out 0x119078 (movzxR32M8Effect 0x119078 4 0 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 57) (.exec 0x119078 (LoadPre 0x119078 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x119078 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x119078 4 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 58) (.out 0x11907c (addR64Imm8Effect 0x11907c 4 0x1) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[53]
    (.letOp (n := 59) (.exec 0x11907c (fun s => s.RIP = 0x11907c) (addR64Imm8Effect 0x11907c 4 0x1) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 60) (.out 0x119080 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[58]
    (.letOp (n := 61) (.out 0x119080 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[58]
    (.letOp (n := 62) (.exec 0x119080 (RetPre 0x119080) (retEffect) (Reg.operands [.gpr 4] [])) #v[58]
    (.terminate (.ret (RegMap.args [(0, 56), (2, 2), (3, 3), (4, 61), (5, 5), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)] 63) (some ⟨60, by decide⟩))))))))))))

def bytes_l126f60 : List UInt8 :=
  [0x48, 0x83, 0xEC, 0x01, 0x40, 0x88, 0x3C, 0x24, 0x0F, 0xB6, 0x04, 0x24, 0x48, 0x83, 0xC4, 0x01, 0xC3]

theorem code_l126f60 : ∀ x ∈ codeRange 0x119070 bytes_l126f60, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x19070 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

end P256.Proofs.Scalar.Inverse.Wrapper.Machine
