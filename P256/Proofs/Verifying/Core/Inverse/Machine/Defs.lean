import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Verifying.Core.Inverse.Machine.Labels
import P256.Proofs.Common.CFG.EvalAttr
import P256.Proofs.Common.Lift.Generated.Footprints

namespace P256.Proofs.Verifying.Core.Inverse.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

@[cfg_block] def b_l115020 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x112fd0 (pushR64Effect 0x112fd0 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[4, 3]
    (.letOp (n := 54) (.exec 0x112fd0 (PushPre 0x112fd0 1) (pushR64Effect 0x112fd0 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[4, 3]
    (.letOp (n := 55) (.out 0x112fd1 (subR64Imm8Effect 0x112fd1 4 0x30) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[53]
    (.letOp (n := 56) (.exec 0x112fd1 (fun s => s.RIP = 0x112fd1) (subR64Imm8Effect 0x112fd1 4 0x30) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 57) (.out 0x112fd5 (movR64R64Effect 0x112fd5 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 58) (.exec 0x112fd5 (fun s => s.RIP = 0x112fd5) (movR64R64Effect 0x112fd5 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 59) (.out 0x112fd8 (leaR64Effect 0x112fd8 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[55]
    (.letOp (n := 60) (.exec 0x112fd8 (fun s => s.RIP = 0x112fd8) (leaR64Effect 0x112fd8 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 61) (.out 0x112fdd (movR64Imm64Effect 0x112fdd 1 0x332e375511ff43b1) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 62) (.exec 0x112fdd (fun s => s.RIP = 0x112fdd) (movR64Imm64Effect 0x112fdd 1 0x332e375511ff43b1) (Reg.operands [] [])) #v[]
    (.letOp (n := 63) (.out 0x112fe7 (movR64Imm32Effect 0x112fe7 2 0x2025e0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 64) (.exec 0x112fe7 (fun s => s.RIP = 0x112fe7) (movR64Imm32Effect 0x112fe7 2 0x2025e0) (Reg.operands [] [])) #v[]
    (.letOp (n := 65) (.out 0x112fee (movR64Imm32Effect 0x112fee 8 0x2025c0) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 66) (.exec 0x112fee (fun s => s.RIP = 0x112fee) (movR64Imm32Effect 0x112fee 8 0x2025c0) (Reg.operands [] [])) #v[]
    (.letOp (n := 67) (.out 0x112ff5 (callEffect (fun _ => 0x112190) 0x112ffa) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[55]
    (.letOp (n := 68) (.exec 0x112ff5 (PushPre 0x112ff5 5) (callEffect (fun _ => 0x112190) 0x112ffa) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 69) (.const ⟨64, 0x112ffa⟩) #v[]
    (.terminate (.call ⟨.l1141e0, RegMap.args [(0, 0), (1, 61), (2, 63), (3, 57), (4, 67), (5, 5), (6, 6), (7, 59), (8, 65), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)] 70⟩ { target := .l11504a, kept := #v[], arity := rfl, guard := some (Fin.last 69) }))))))))))))))))))

def bytes_l115020 : List UInt8 :=
  [0x53, 0x48, 0x83, 0xec, 0x30, 0x48, 0x89, 0xfb, 0x48, 0x8d, 0x7c, 0x24, 0x8, 0x48, 0xb9, 0xb1, 0x43, 0xff, 0x11, 0x55, 0x37, 0x2e, 0x33, 0x48, 0xc7, 0xc2, 0xe0, 0x25, 0x20, 0x0, 0x49, 0xc7, 0xc0, 0xc0, 0x25, 0x20, 0x0, 0xe8, 0x96, 0xf1, 0xff, 0xff]

theorem code_l115020 : ∀ x ∈ codeRange 0x112fd0 bytes_l115020, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x12fd0 42 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11504a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x112ffa (movR64M64Effect 0x112ffa 0 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x112ffa (LoadPre 0x112ffa (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x112ffa + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x112ffa 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x112fff (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112fff 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x112fff + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x112fff 0 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[53, 3]
    (.letOp (n := 56) (.out 0x113003 (movR64M64Effect 0x113003 0 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x113003 (LoadPre 0x113003 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x113003 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x113003 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x113008 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x113008 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x113008 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x113008 0 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[56, 3]
    (.letOp (n := 59) (.out 0x11300c (movR64M64Effect 0x11300c 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x11300c (LoadPre 0x11300c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11300c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11300c 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x113011 (movR64M64Effect 0x113011 1 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 62) (.exec 0x113011 (LoadPre 0x113011 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x113011 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x113011 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x113016 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x113016 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x113016 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x113016 1 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 64) (.exec 0x11301a (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x11301a 3 (fun s => AddrMode.addr (.base 3 .none) s (0x11301a + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x11301a 0 (.base 3 .none)) (Reg.operands [.gpr 0, .gpr 3] [])) #v[59, 3]
    (.letOp (n := 65) (.out 0x11301d (movR32M32LowEffect 0x11301d 7 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 66) (.exec 0x11301d (LoadPre 0x11301d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11301d + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x11301d 7 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x113021 (callEffect (fun _ => 0x119070) 0x113026) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 68) (.exec 0x113021 (PushPre 0x113021 5) (callEffect (fun _ => 0x119070) 0x113026) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.const ⟨64, 0x113026⟩) #v[]
    (.terminate (.call ⟨.l1234c0, RegMap.args [(0, 59), (1, 61), (2, 2), (3, 3), (4, 67), (5, 5), (7, 65), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)] 70⟩ { target := .l115076, kept := #v[], arity := rfl, guard := some (Fin.last 69) }))))))))))))))))))

def bytes_l11504a : List UInt8 :=
  [0x48, 0x8b, 0x44, 0x24, 0x20, 0x48, 0x89, 0x43, 0x18, 0x48, 0x8b, 0x44, 0x24, 0x18, 0x48, 0x89, 0x43, 0x10, 0x48, 0x8b, 0x44, 0x24, 0x8, 0x48, 0x8b, 0x4c, 0x24, 0x10, 0x48, 0x89, 0x4b, 0x8, 0x48, 0x89, 0x3, 0x8b, 0x7c, 0x24, 0x28, 0xe8, 0x4a, 0x60, 0x0, 0x0]

theorem code_l11504a : ∀ x ∈ codeRange 0x112ffa bytes_l11504a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x12ffa 44 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l115076 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x113026 (StorePre 0x113026 3 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x113026 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x113026 3 0 (.base 3 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (.letOp (n := 54) (.out 0x113029 (movR64R64Effect 0x113029 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 55) (.exec 0x113029 (fun s => s.RIP = 0x113029) (movR64R64Effect 0x113029 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 56) (.out 0x11302c (addR64Imm8Effect 0x11302c 4 0x30) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 57) (.exec 0x11302c (fun s => s.RIP = 0x11302c) (addR64Imm8Effect 0x11302c 4 0x30) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.out 0x113030 (popR64Effect 0x113030 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[56]
    (.letOp (n := 59) (.out 0x113030 (popR64Effect 0x113030 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[56]
    (.letOp (n := 60) (.exec 0x113030 (PopPre 0x113030) (popR64Effect 0x113030 1 3) (Reg.operands [.gpr 4] [])) #v[56]
    (.letOp (n := 61) (.out 0x113031 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[59]
    (.letOp (n := 62) (.out 0x113031 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 63) (.exec 0x113031 (RetPre 0x113031) (retEffect) (Reg.operands [.gpr 4] [])) #v[59]
    (.terminate (.ret (RegMap.args [(0, 54), (2, 2), (3, 58), (4, 62), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)] 64) (some ⟨61, by decide⟩)))))))))))))

def bytes_l115076 : List UInt8 :=
  [0x88, 0x43, 0x20, 0x48, 0x89, 0xd8, 0x48, 0x83, 0xc4, 0x30, 0x5b, 0xc3]

theorem code_l115076 : ∀ x ∈ codeRange 0x113026 bytes_l115076, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x13026 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1141e0 : Block Op Label signature Reg.count 53 :=
  cutBlock 0x112190

def bytes_l1141e0 : List UInt8 :=
  [0x55]

theorem code_l1141e0 : ∀ x ∈ codeRange 0x112190 bytes_l1141e0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x12190 1 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1234c0 : Block Op Label signature Reg.count 53 :=
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

def bytes_l1234c0 : List UInt8 :=
  [0x48, 0x83, 0xec, 0x1, 0x40, 0x88, 0x3c, 0x24, 0xf, 0xb6, 0x4, 0x24, 0x48, 0x83, 0xc4, 0x1, 0xc3]

theorem code_l1234c0 : ∀ x ∈ codeRange 0x119070 bytes_l1234c0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x19070 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

end P256.Proofs.Verifying.Core.Inverse.Machine
