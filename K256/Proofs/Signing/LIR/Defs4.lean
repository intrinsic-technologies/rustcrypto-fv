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

@[cfg_block] def b_l106eed : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x106eed (StorePre 0x106eed 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x106eed + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x106eed 14 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[14, 4]
    (.letOp (n := 54) (.exec 0x106ef2 (StorePre 0x106ef2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x106ef2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x106ef2 15 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[15, 4]
    (.letOp (n := 55) (.exec 0x106ef7 (StorePre 0x106ef7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x106ef7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x106ef7 12 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[12, 4]
    (.letOp (n := 56) (.exec 0x106efc (StorePre 0x106efc 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x106efc + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x106efc 13 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[13, 4]
    (.letOp (n := 57) (.exec 0x106f01 (StorePre 0x106f01 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x106f01 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x106f01 (.sib 4 none 0 (.d8 0x18)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x106f0a (StorePre 0x106f0a 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x106f0a + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x106f0a (.sib 4 none 0 (.d8 0x10)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.exec 0x106f13 (StorePre 0x106f13 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x106f13 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x106f13 (.sib 4 none 0 (.d8 0x8)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.exec 0x106f1c (StorePre 0x106f1c 8 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x106f1c + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x106f1c (.sib 4 none 0 .none) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x106f24 (leaR64Effect 0x106f24 7 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 62) (.exec 0x106f24 (fun s => s.RIP = 0x106f24) (leaR64Effect 0x106f24 7 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x106f29 (movR64R64Effect 0x106f29 2 4) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 64) (.exec 0x106f29 (fun s => s.RIP = 0x106f29) (movR64R64Effect 0x106f29 2 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x106f2c (movR32Imm32Effect 0x106f2c 5 6 0x4) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 66) (.exec 0x106f2c (fun s => s.RIP = 0x106f2c) (movR32Imm32Effect 0x106f2c 5 6 0x4) (Reg.operands [] [])) #v[]
    (.letOp (n := 67) (.out 0x106f31 (movR32Imm32Effect 0x106f31 5 1 0x4) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 68) (.exec 0x106f31 (fun s => s.RIP = 0x106f31) (movR32Imm32Effect 0x106f31 5 1 0x4) (Reg.operands [] [])) #v[]
    (.letOp (n := 69) (.out 0x106f36 (callEffect (fun _ => 0x127f50) 0x106f3b) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 70) (.exec 0x106f36 (PushPre 0x106f36 5) (callEffect (fun _ => 0x127f50) 0x106f3b) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.const ⟨64, 0x106f3b⟩) #v[]
    (.terminate (.call ⟨.l127f50, RegMap.args [(0, 0), (1, 67), (2, 63), (3, 3), (4, 69), (5, 5), (6, 65), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩ { target := .l106f3b, kept := #v[], arity := rfl, guard := some (Fin.last 71) }))))))))))))))))))))

def bytes_l106eed : List UInt8 :=
  [0x4C, 0x89, 0x74, 0x24, 0x28, 0x4C, 0x89, 0x7C, 0x24, 0x30, 0x4C, 0x89, 0x64, 0x24, 0x38, 0x4C,
    0x89, 0x6C, 0x24, 0x40, 0x48, 0xC7, 0x44, 0x24, 0x18, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44,
    0x24, 0x10, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00, 0x48,
    0xC7, 0x04, 0x24, 0x00, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x7C, 0x24, 0x28, 0x48, 0x89, 0xE2, 0xBE,
    0x04, 0x00, 0x00, 0x00, 0xB9, 0x04, 0x00, 0x00, 0x00, 0xE8, 0x15, 0x10, 0x02, 0x00]

theorem code_l106eed : ∀ x ∈ codeRange 0x106eed bytes_l106eed, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6eed 78 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106f3b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106f3b (andAlImm8Effect 0x106f3b 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 54) (.exec 0x106f3b (fun s => s.RIP = 0x106f3b) (andAlImm8Effect 0x106f3b 0x1) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x106f3d (movzxR32R8Effect 0x106f3d 3 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 56) (.exec 0x106f3d (fun s => s.RIP = 0x106f3d) (movzxR32R8Effect 0x106f3d 3 7 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x106f40 (callEffect (fun _ => 0x127d50) 0x106f45) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x106f40 (PushPre 0x106f40 5) (callEffect (fun _ => 0x127d50) 0x106f45) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x106f45⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ { target := .l106f45, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l106f3b : List UInt8 :=
  [0x24, 0x01, 0x0F, 0xB6, 0xF8, 0xE8, 0x0B, 0x0E, 0x02, 0x00]

theorem code_l106f3b : ∀ x ∈ codeRange 0x106f3b bytes_l106f3b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6f3b 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106f45 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106f45 (testR8R8Effect 0x106f45 2 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[0, 0]
    (.letOp (n := 54) (.exec 0x106f45 (fun s => s.RIP = 0x106f45) (testR8R8Effect 0x106f45 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l106f5b, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l106f49, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l106f45 : List UInt8 :=
  [0x84, 0xC0, 0x75, 0x12]

theorem code_l106f45 : ∀ x ∈ codeRange 0x106f45 bytes_l106f45, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6f45 4 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106f49 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x106f49 (StorePre 0x106f49 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x106f49 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x106f49 14 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 14, .gpr 3] [])) #v[14, 3]
    (.letOp (n := 54) (.exec 0x106f4d (StorePre 0x106f4d 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x106f4d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x106f4d 15 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 15, .gpr 3] [])) #v[15, 3]
    (.letOp (n := 55) (.exec 0x106f51 (StorePre 0x106f51 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x106f51 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x106f51 12 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 12, .gpr 3] [])) #v[12, 3]
    (.letOp (n := 56) (.exec 0x106f55 (StorePre 0x106f55 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x106f55 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x106f55 13 (.base 3 (.d8 0x20))) (Reg.operands [.gpr 13, .gpr 3] [])) #v[13, 3]
    (.letOp (n := 57) (.out 0x106f59 (xorR32R32Effect 0x106f59 2 5 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 5] []) (.reg (.gpr 5))) #v[5, 5]
    (.letOp (n := 58) (.exec 0x106f59 (fun s => s.RIP = 0x106f59) (xorR32R32Effect 0x106f59 2 5 5) (Reg.operands [.gpr 5, .gpr 5] [])) #v[5, 5]
    (.terminate (.br ⟨.l106f5b, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 57), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l106f49 : List UInt8 :=
  [0x4C, 0x89, 0x73, 0x08, 0x4C, 0x89, 0x7B, 0x10, 0x4C, 0x89, 0x63, 0x18, 0x4C, 0x89, 0x6B, 0x20,
    0x31, 0xED]

theorem code_l106f49 : ∀ x ∈ codeRange 0x106f49 bytes_l106f49, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6f49 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106f5b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x106f5b (StorePre 0x106f5b 3 (fun s => AddrMode.addr (.base 3 .none) s (0x106f5b + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x106f5b 5 (.base 3 .none)) (Reg.operands [.gpr 5, .gpr 3] [])) #v[5, 3]
    (.letOp (n := 54) (.out 0x106f5e (movR64R64Effect 0x106f5e 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 55) (.exec 0x106f5e (fun s => s.RIP = 0x106f5e) (movR64R64Effect 0x106f5e 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 56) (.out 0x106f61 (addR64Imm8Effect 0x106f61 4 0x48) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 57) (.exec 0x106f61 (fun s => s.RIP = 0x106f61) (addR64Imm8Effect 0x106f61 4 0x48) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.out 0x106f65 (popR64Effect 0x106f65 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[56]
    (.letOp (n := 59) (.out 0x106f65 (popR64Effect 0x106f65 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[56]
    (.letOp (n := 60) (.exec 0x106f65 (PopPre 0x106f65) (popR64Effect 0x106f65 1 3) (Reg.operands [.gpr 4] [])) #v[56]
    (.letOp (n := 61) (.out 0x106f66 (popR64Effect 0x106f66 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[59]
    (.letOp (n := 62) (.out 0x106f66 (popR64Effect 0x106f66 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 63) (.exec 0x106f66 (PopPre 0x106f66) (popR64Effect 0x106f66 2 12) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 64) (.out 0x106f68 (popR64Effect 0x106f68 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[62]
    (.letOp (n := 65) (.out 0x106f68 (popR64Effect 0x106f68 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[62]
    (.letOp (n := 66) (.exec 0x106f68 (PopPre 0x106f68) (popR64Effect 0x106f68 2 13) (Reg.operands [.gpr 4] [])) #v[62]
    (.letOp (n := 67) (.out 0x106f6a (popR64Effect 0x106f6a 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[65]
    (.letOp (n := 68) (.out 0x106f6a (popR64Effect 0x106f6a 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 69) (.exec 0x106f6a (PopPre 0x106f6a) (popR64Effect 0x106f6a 2 14) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 70) (.out 0x106f6c (popR64Effect 0x106f6c 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[68]
    (.letOp (n := 71) (.out 0x106f6c (popR64Effect 0x106f6c 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[68]
    (.letOp (n := 72) (.exec 0x106f6c (PopPre 0x106f6c) (popR64Effect 0x106f6c 2 15) (Reg.operands [.gpr 4] [])) #v[68]
    (.letOp (n := 73) (.out 0x106f6e (popR64Effect 0x106f6e 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[71]
    (.letOp (n := 74) (.out 0x106f6e (popR64Effect 0x106f6e 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[71]
    (.letOp (n := 75) (.exec 0x106f6e (PopPre 0x106f6e) (popR64Effect 0x106f6e 1 5) (Reg.operands [.gpr 4] [])) #v[71]
    (.letOp (n := 76) (.out 0x106f6f (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[74]
    (.letOp (n := 77) (.out 0x106f6f (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[74]
    (.letOp (n := 78) (.exec 0x106f6f (RetPre 0x106f6f) (retEffect) (Reg.operands [.gpr 4] [])) #v[74]
    (.terminate (.ret (RegMap.args [(0, 54), (1, 1), (2, 2), (3, 58), (4, 77), (5, 73), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 64), (14, 67), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)] 79) (some ⟨76, by decide⟩))))))))))))))))))))))))))))

def bytes_l106f5b : List UInt8 :=
  [0x48, 0x89, 0x2B, 0x48, 0x89, 0xD8, 0x48, 0x83, 0xC4, 0x48, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41,
    0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l106f5b : ∀ x ∈ codeRange 0x106f5b bytes_l106f5b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6f5b 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106f70 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x106f70 (StorePre 0x106f70 8 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x106f70 + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x106f70 (.sib 4 none 0 .none) 0x202498) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.exec 0x106f78 (StorePre 0x106f78 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x106f78 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x106f78 (.sib 4 none 0 (.d8 0x8)) 0x12a190) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x106f81 (leaR64Effect 0x106f81 0 (.sib 4 none 0 (.d8 0x24))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 56) (.exec 0x106f81 (fun s => s.RIP = 0x106f81) (leaR64Effect 0x106f81 0 (.sib 4 none 0 (.d8 0x24))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x106f86 (StorePre 0x106f86 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x106f86 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x106f86 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 58) (.exec 0x106f8b (StorePre 0x106f8b 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x106f8b + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x106f8b (.sib 4 none 0 (.d8 0x18)) 0x12a190) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x106f94 (movR64R64Effect 0x106f94 6 4) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 60) (.exec 0x106f94 (fun s => s.RIP = 0x106f94) (movR64R64Effect 0x106f94 6 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x106f97 (movR64Imm32Effect 0x106f97 7 0x20028f) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 62) (.exec 0x106f97 (fun s => s.RIP = 0x106f97) (movR64Imm32Effect 0x106f97 7 0x20028f) (Reg.operands [] [])) #v[]
    (.letOp (n := 63) (.out 0x106f9e (movR64Imm32Effect 0x106f9e 2 0x202518) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 64) (.exec 0x106f9e (fun s => s.RIP = 0x106f9e) (movR64Imm32Effect 0x106f9e 2 0x202518) (Reg.operands [] [])) #v[]
    (.letOp (n := 65) (.out 0x106fa5 (callEffect (fun _ => 0x129770) 0x106faa) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 66) (.exec 0x106fa5 (PushPre 0x106fa5 5) (callEffect (fun _ => 0x129770) 0x106faa) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.const ⟨64, 0x106faa⟩) #v[]
    (.terminate (.call ⟨.l129770, RegMap.args [(0, 55), (2, 63), (4, 65), (5, 5), (6, 59), (7, 61)] 68⟩ { target := .l106faa, kept := #v[], arity := rfl, guard := some (Fin.last 67) }))))))))))))))))

def bytes_l106f70 : List UInt8 :=
  [0x48, 0xC7, 0x04, 0x24, 0x98, 0x24, 0x20, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x08, 0x90, 0xA1, 0x12,
    0x00, 0x48, 0x8D, 0x44, 0x24, 0x24, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0xC7, 0x44, 0x24, 0x18,
    0x90, 0xA1, 0x12, 0x00, 0x48, 0x89, 0xE6, 0x48, 0xC7, 0xC7, 0x8F, 0x02, 0x20, 0x00, 0x48, 0xC7,
    0xC2, 0x18, 0x25, 0x20, 0x00, 0xE8, 0xC6, 0x27, 0x02, 0x00]

theorem code_l106f70 : ∀ x ∈ codeRange 0x106f70 bytes_l106f70, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6f70 58 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106faa : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x106faa (fun s => s.RIP = 0x106faa) (fun _ => nopEffect 0x106faa 6) (Reg.operands [] [])) #v[]
    (.letOp (n := 54) (.out 0x106fb0 (pushR64Effect 0x106fb0 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 55) (.exec 0x106fb0 (PushPre 0x106fb0 1) (pushR64Effect 0x106fb0 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 56) (.out 0x106fb1 (pushR64Effect 0x106fb1 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[54, 15]
    (.letOp (n := 57) (.exec 0x106fb1 (PushPre 0x106fb1 2) (pushR64Effect 0x106fb1 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[54, 15]
    (.letOp (n := 58) (.out 0x106fb3 (pushR64Effect 0x106fb3 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[56, 14]
    (.letOp (n := 59) (.exec 0x106fb3 (PushPre 0x106fb3 2) (pushR64Effect 0x106fb3 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[56, 14]
    (.letOp (n := 60) (.out 0x106fb5 (pushR64Effect 0x106fb5 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[58, 13]
    (.letOp (n := 61) (.exec 0x106fb5 (PushPre 0x106fb5 2) (pushR64Effect 0x106fb5 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[58, 13]
    (.letOp (n := 62) (.out 0x106fb7 (pushR64Effect 0x106fb7 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[60, 12]
    (.letOp (n := 63) (.exec 0x106fb7 (PushPre 0x106fb7 2) (pushR64Effect 0x106fb7 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[60, 12]
    (.letOp (n := 64) (.out 0x106fb9 (pushR64Effect 0x106fb9 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[62, 3]
    (.letOp (n := 65) (.exec 0x106fb9 (PushPre 0x106fb9 1) (pushR64Effect 0x106fb9 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[62, 3]
    (.letOp (n := 66) (.out 0x106fba (subR64Imm32Effect 0x106fba 4 0x1d8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[64]
    (.letOp (n := 67) (.exec 0x106fba (fun s => s.RIP = 0x106fba) (subR64Imm32Effect 0x106fba 4 0x1d8) (Reg.operands [.gpr 4] [])) #v[64]
    (.letOp (n := 68) (.out 0x106fc1 (movR64R64Effect 0x106fc1 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 69) (.exec 0x106fc1 (fun s => s.RIP = 0x106fc1) (movR64R64Effect 0x106fc1 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 70) (.out 0x106fc4 (leaR64Effect 0x106fc4 5 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[66]
    (.letOp (n := 71) (.exec 0x106fc4 (fun s => s.RIP = 0x106fc4) (leaR64Effect 0x106fc4 5 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[66]
    (.letOp (n := 72) (.out 0x106fcc (movR64R64Effect 0x106fcc 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[70]
    (.letOp (n := 73) (.exec 0x106fcc (fun s => s.RIP = 0x106fcc) (movR64R64Effect 0x106fcc 7 5) (Reg.operands [.gpr 5] [])) #v[70]
    (.letOp (n := 74) (.out 0x106fcf (callEffect (fun _ => 0x125790) 0x106fd4) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[66]
    (.letOp (n := 75) (.exec 0x106fcf (PushPre 0x106fcf 5) (callEffect (fun _ => 0x125790) 0x106fd4) (Reg.operands [.gpr 4] [])) #v[66]
    (.letOp (n := 76) (.const ⟨64, 0x106fd4⟩) #v[]
    (.terminate (.call ⟨.l125790, RegMap.args [(2, 2), (3, 68), (4, 74), (5, 70), (6, 6), (7, 72), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 77⟩ { target := .l106fd4, kept := #v[], arity := rfl, guard := some (Fin.last 76) })))))))))))))))))))))))))

def bytes_l106faa : List UInt8 :=
  [0x66, 0x0F, 0x1F, 0x44, 0x00, 0x00, 0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53,
    0x48, 0x81, 0xEC, 0xD8, 0x01, 0x00, 0x00, 0x48, 0x89, 0xFB, 0x48, 0x8D, 0xAC, 0x24, 0x88, 0x00,
    0x00, 0x00, 0x48, 0x89, 0xEF, 0xE8, 0xBC, 0xE7, 0x01, 0x00]

theorem code_l106faa : ∀ x ∈ codeRange 0x106faa bytes_l106faa, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6faa 42 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106fd4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106fd4 (movR64M64Effect 0x106fd4 12 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 54) (.exec 0x106fd4 (LoadPre 0x106fd4 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x106fd4 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x106fd4 12 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x106fdc (movR64M64Effect 0x106fdc 13 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 56) (.exec 0x106fdc (LoadPre 0x106fdc (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x106fdc + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x106fdc 13 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x106fe4 (movR64M64Effect 0x106fe4 15 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 58) (.exec 0x106fe4 (LoadPre 0x106fe4 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x106fe4 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x106fe4 15 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x106fec (movR64M64Effect 0x106fec 14 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 60) (.exec 0x106fec (LoadPre 0x106fec (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x106fec + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x106fec 14 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x106ff4 (movzxR32M8Effect 0x106ff4 8 0 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 62) (.exec 0x106ff4 (LoadPre 0x106ff4 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x106ff4 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x106ff4 8 0 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x106ffc (cmpMImm8Effect 0x106ffc 8 32 (.sib 4 none 0 (.d32 0x88)) 0x1) (EffectPart.reads (.flag .ZF) [.gpr 4] []) (.flag .ZF)) #v[4]
    (.letOp (n := 64) (.exec 0x106ffc (LoadPre 0x106ffc (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x106ffc + BitVec.ofNat 64 8)) 4) (cmpMImm8Effect 0x106ffc 8 32 (.sib 4 none 0 (.d32 0x88)) 0x1) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.pure (condOp 5)) #v[63]
    (.terminate (.condBr (Fin.last 65) ⟨.l107052, RegMap.args [(0, 61), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 55), (14, 59), (15, 57), (19, 63), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩ ⟨.l107006, RegMap.args [(0, 61), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 55), (14, 59), (15, 57), (19, 63), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩))))))))))))))

def bytes_l106fd4 : List UInt8 :=
  [0x4C, 0x8B, 0xA4, 0x24, 0x90, 0x00, 0x00, 0x00, 0x4C, 0x8B, 0xAC, 0x24, 0x98, 0x00, 0x00, 0x00,
    0x4C, 0x8B, 0xBC, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x4C, 0x8B, 0xB4, 0x24, 0xA8, 0x00, 0x00, 0x00,
    0x0F, 0xB6, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x83, 0xBC, 0x24, 0x88, 0x00, 0x00, 0x00, 0x01,
    0x75, 0x4C]

theorem code_l106fd4 : ∀ x ∈ codeRange 0x106fd4 bytes_l106fd4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6fd4 50 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l107006 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x107006 (movR64M64Effect 0x107006 1 (.base 5 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[5]
    (.letOp (n := 54) (.exec 0x107006 (LoadPre 0x107006 (fun s => AddrMode.addr (.base 5 (.d8 0x38)) s (0x107006 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x107006 1 (.base 5 (.d8 0x38))) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 55) (.exec 0x10700a (StorePre 0x10700a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3f)) s (0x10700a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10700a 1 (.sib 4 none 0 (.d8 0x3f))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x10700f (movR64M64Effect 0x10700f 1 (.base 5 (.d8 0x29))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[5]
    (.letOp (n := 57) (.exec 0x10700f (LoadPre 0x10700f (fun s => AddrMode.addr (.base 5 (.d8 0x29)) s (0x10700f + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10700f 1 (.base 5 (.d8 0x29))) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 58) (.out 0x107013 (movR64M64Effect 0x107013 2 (.base 5 (.d8 0x31))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5] []) (.reg (.gpr 2))) #v[5]
    (.letOp (n := 59) (.exec 0x107013 (LoadPre 0x107013 (fun s => AddrMode.addr (.base 5 (.d8 0x31)) s (0x107013 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x107013 2 (.base 5 (.d8 0x31))) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 60) (.exec 0x107017 (StorePre 0x107017 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x107017 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107017 2 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[58, 4]
    (.letOp (n := 61) (.exec 0x10701c (StorePre 0x10701c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10701c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10701c 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 62) (.out 0x107021 (movR64M64Effect 0x107021 2 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 63) (.exec 0x107021 (LoadPre 0x107021 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x107021 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107021 2 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x107026 (movR64M64Effect 0x107026 6 (.sib 4 none 0 (.d8 0x3f))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 65) (.exec 0x107026 (LoadPre 0x107026 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3f)) s (0x107026 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107026 6 (.sib 4 none 0 (.d8 0x3f))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x10702b (StorePre 0x10702b 4 (fun s => AddrMode.addr (.base 3 (.d8 0x38)) s (0x10702b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10702b 6 (.base 3 (.d8 0x38))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[64, 3]
    (.letOp (n := 67) (.exec 0x10702f (StorePre 0x10702f 4 (fun s => AddrMode.addr (.base 3 (.d8 0x31)) s (0x10702f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10702f 2 (.base 3 (.d8 0x31))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[62, 3]
    (.letOp (n := 68) (.exec 0x107033 (StorePre 0x107033 4 (fun s => AddrMode.addr (.base 3 (.d8 0x29)) s (0x107033 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x107033 1 (.base 3 (.d8 0x29))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[56, 3]
    (.letOp (n := 69) (.exec 0x107037 (StorePre 0x107037 3 (fun s => AddrMode.addr (.base 3 .none) s (0x107037 + BitVec.ofNat 64 3)) 1) (movM8Imm8Effect 0x107037 (.base 3 .none) 0xff) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.exec 0x10703a (StorePre 0x10703a 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x10703a + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10703a 12 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 12, .gpr 3] [])) #v[12, 3]
    (.letOp (n := 71) (.exec 0x10703e (StorePre 0x10703e 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x10703e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10703e 13 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 13, .gpr 3] [])) #v[13, 3]
    (.letOp (n := 72) (.exec 0x107042 (StorePre 0x107042 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x107042 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x107042 15 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 15, .gpr 3] [])) #v[15, 3]
    (.letOp (n := 73) (.exec 0x107046 (StorePre 0x107046 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x107046 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x107046 14 (.base 3 (.d8 0x20))) (Reg.operands [.gpr 14, .gpr 3] [])) #v[14, 3]
    (.letOp (n := 74) (.exec 0x10704a (StorePre 0x10704a 3 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x10704a + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10704a 3 0 (.base 3 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (.terminate (.br ⟨.l10768b, RegMap.args [(0, 0), (1, 56), (2, 62), (3, 3), (4, 4), (5, 5), (6, 64), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩)))))))))))))))))))))))

def bytes_l107006 : List UInt8 :=
  [0x48, 0x8B, 0x4D, 0x38, 0x48, 0x89, 0x4C, 0x24, 0x3F, 0x48, 0x8B, 0x4D, 0x29, 0x48, 0x8B, 0x55,
    0x31, 0x48, 0x89, 0x54, 0x24, 0x38, 0x48, 0x89, 0x4C, 0x24, 0x30, 0x48, 0x8B, 0x54, 0x24, 0x38,
    0x48, 0x8B, 0x74, 0x24, 0x3F, 0x48, 0x89, 0x73, 0x38, 0x48, 0x89, 0x53, 0x31, 0x48, 0x89, 0x4B,
    0x29, 0xC6, 0x03, 0xFF, 0x4C, 0x89, 0x63, 0x08, 0x4C, 0x89, 0x6B, 0x10, 0x4C, 0x89, 0x7B, 0x18,
    0x4C, 0x89, 0x73, 0x20, 0x88, 0x43, 0x28, 0xE9, 0x39, 0x06, 0x00, 0x00]

theorem code_l107006 : ∀ x ∈ codeRange 0x107006 bytes_l107006, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x7006 76 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l107052 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x107052 (movR64M64Effect 0x107052 1 (.base 5 (.d8 0x49))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[5]
    (.letOp (n := 54) (.exec 0x107052 (LoadPre 0x107052 (fun s => AddrMode.addr (.base 5 (.d8 0x49)) s (0x107052 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x107052 1 (.base 5 (.d8 0x49))) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 55) (.exec 0x107056 (StorePre 0x107056 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x107056 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107056 1 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x10705b (movR64M64Effect 0x10705b 2 (.base 5 (.d8 0x41))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5] []) (.reg (.gpr 2))) #v[5]
    (.letOp (n := 57) (.exec 0x10705b (LoadPre 0x10705b (fun s => AddrMode.addr (.base 5 (.d8 0x41)) s (0x10705b + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10705b 2 (.base 5 (.d8 0x41))) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 58) (.out 0x10705f (movR64M64Effect 0x10705f 6 (.base 5 (.d8 0x39))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[5]
    (.letOp (n := 59) (.exec 0x10705f (LoadPre 0x10705f (fun s => AddrMode.addr (.base 5 (.d8 0x39)) s (0x10705f + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10705f 6 (.base 5 (.d8 0x39))) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 60) (.out 0x107063 (movR64M64Effect 0x107063 7 (.base 5 (.d8 0x29))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[5]
    (.letOp (n := 61) (.exec 0x107063 (LoadPre 0x107063 (fun s => AddrMode.addr (.base 5 (.d8 0x29)) s (0x107063 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x107063 7 (.base 5 (.d8 0x29))) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 62) (.out 0x107067 (movR64M64Effect 0x107067 8 (.base 5 (.d8 0x31))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 5] []) (.reg (.gpr 8))) #v[5]
    (.letOp (n := 63) (.exec 0x107067 (LoadPre 0x107067 (fun s => AddrMode.addr (.base 5 (.d8 0x31)) s (0x107067 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x107067 8 (.base 5 (.d8 0x31))) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 64) (.exec 0x10706b (StorePre 0x10706b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x168)) s (0x10706b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10706b 7 (.sib 4 none 0 (.d32 0x168))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[60, 4]
    (.letOp (n := 65) (.exec 0x107073 (StorePre 0x107073 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x170)) s (0x107073 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107073 8 (.sib 4 none 0 (.d32 0x170))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 66) (.exec 0x10707b (StorePre 0x10707b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x178)) s (0x10707b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10707b 6 (.sib 4 none 0 (.d32 0x178))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[58, 4]
    (.letOp (n := 67) (.exec 0x107083 (StorePre 0x107083 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x180)) s (0x107083 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107083 2 (.sib 4 none 0 (.d32 0x180))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 68) (.exec 0x10708b (StorePre 0x10708b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x188)) s (0x10708b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10708b 1 (.sib 4 none 0 (.d32 0x188))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 69) (.out 0x107093 (cmpAlImm8Effect 0x107093 0x1) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[0]
    (.letOp (n := 70) (.exec 0x107093 (fun s => s.RIP = 0x107093) (cmpAlImm8Effect 0x107093 0x1) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 71) (.pure (condOp 5)) #v[69]
    (.terminate (.condBr (Fin.last 71) ⟨.l107110, RegMap.args [(0, 0), (1, 53), (2, 56), (3, 3), (4, 4), (5, 5), (6, 58), (7, 60), (8, 62), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩ ⟨.l107097, RegMap.args [(0, 0), (1, 53), (2, 56), (3, 3), (4, 4), (5, 5), (6, 58), (7, 60), (8, 62), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩))))))))))))))))))))

def bytes_l107052 : List UInt8 :=
  [0x48, 0x8B, 0x4D, 0x49, 0x48, 0x89, 0x4C, 0x24, 0x50, 0x48, 0x8B, 0x55, 0x41, 0x48, 0x8B, 0x75,
    0x39, 0x48, 0x8B, 0x7D, 0x29, 0x4C, 0x8B, 0x45, 0x31, 0x48, 0x89, 0xBC, 0x24, 0x68, 0x01, 0x00,
    0x00, 0x4C, 0x89, 0x84, 0x24, 0x70, 0x01, 0x00, 0x00, 0x48, 0x89, 0xB4, 0x24, 0x78, 0x01, 0x00,
    0x00, 0x48, 0x89, 0x94, 0x24, 0x80, 0x01, 0x00, 0x00, 0x48, 0x89, 0x8C, 0x24, 0x88, 0x01, 0x00,
    0x00, 0x3C, 0x01, 0x75, 0x79]

theorem code_l107052 : ∀ x ∈ codeRange 0x107052 bytes_l107052, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x7052 69 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l107097 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x107097 (movR64M64Effect 0x107097 0 (.sib 4 none 0 (.d32 0x188))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x107097 (LoadPre 0x107097 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x188)) s (0x107097 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107097 0 (.sib 4 none 0 (.d32 0x188))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x10709f (StorePre 0x10709f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x10709f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10709f 0 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x1070a7 (movR64M64Effect 0x1070a7 0 (.sib 4 none 0 (.d32 0x180))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x1070a7 (LoadPre 0x1070a7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x180)) s (0x1070a7 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1070a7 0 (.sib 4 none 0 (.d32 0x180))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x1070af (StorePre 0x1070af 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x1070af + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1070af 0 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x1070b7 (movR64M64Effect 0x1070b7 0 (.sib 4 none 0 (.d32 0x178))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x1070b7 (LoadPre 0x1070b7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x178)) s (0x1070b7 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1070b7 0 (.sib 4 none 0 (.d32 0x178))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x1070bf (StorePre 0x1070bf 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x1070bf + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1070bf 0 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x1070c7 (movR64M64Effect 0x1070c7 0 (.sib 4 none 0 (.d32 0x168))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x1070c7 (LoadPre 0x1070c7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x168)) s (0x1070c7 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1070c7 0 (.sib 4 none 0 (.d32 0x168))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x1070cf (movR64M64Effect 0x1070cf 1 (.sib 4 none 0 (.d32 0x170))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x1070cf (LoadPre 0x1070cf (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x170)) s (0x1070cf + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1070cf 1 (.sib 4 none 0 (.d32 0x170))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x1070d7 (StorePre 0x1070d7 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x1070d7 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1070d7 1 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x1070df (StorePre 0x1070df 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1070df + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1070df 0 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x1070e7 (cmpAlImm8Effect 0x1070e7 0x5) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[62]
    (.letOp (n := 69) (.exec 0x1070e7 (fun s => s.RIP = 0x1070e7) (cmpAlImm8Effect 0x1070e7 0x5) (Reg.operands [.gpr 0] [])) #v[62]
    (.letOp (n := 70) (.pure (condOp 5)) #v[68]
    (.terminate (.condBr (Fin.last 70) ⟨.l107109, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 68), (22, 22), (39, 39), (50, 50), (51, 51)] 71⟩ ⟨.l1070eb, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 68), (22, 22), (39, 39), (50, 50), (51, 51)] 71⟩)))))))))))))))))))

def bytes_l107097 : List UInt8 :=
  [0x48, 0x8B, 0x84, 0x24, 0x88, 0x01, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0xA8, 0x00, 0x00, 0x00,
    0x48, 0x8B, 0x84, 0x24, 0x80, 0x01, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00,
    0x48, 0x8B, 0x84, 0x24, 0x78, 0x01, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00,
    0x48, 0x8B, 0x84, 0x24, 0x68, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x8C, 0x24, 0x70, 0x01, 0x00, 0x00,
    0x48, 0x89, 0x8C, 0x24, 0x90, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00,
    0x3C, 0x05, 0x75, 0x1E]

theorem code_l107097 : ∀ x ∈ codeRange 0x107097 bytes_l107097, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x7097 84 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1070eb : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1070eb (leaR64Effect 0x1070eb 6 (.sib 4 none 0 (.d32 0x89))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 54) (.exec 0x1070eb (fun s => s.RIP = 0x1070eb) (leaR64Effect 0x1070eb 6 (.sib 4 none 0 (.d32 0x89))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1070f3 (movR32Imm32Effect 0x1070f3 5 2 0x27) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 56) (.exec 0x1070f3 (fun s => s.RIP = 0x1070f3) (movR32Imm32Effect 0x1070f3 5 2 0x27) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x1070f8 (movR64Imm32Effect 0x1070f8 7 0x2028b9) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 58) (.exec 0x1070f8 (fun s => s.RIP = 0x1070f8) (movR64Imm32Effect 0x1070f8 7 0x2028b9) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x1070ff (callEffect (callMemPtr 0x1070ff (.rip 0xfccfb)) (0x1070ff + BitVec.ofNat 64 (callMemLen (.rip 0xfccfb)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x1070ff (GoesTo (CallMemPre 0x1070ff (.rip 0xfccfb)) (callEffect (callMemPtr 0x1070ff (.rip 0xfccfb)) (0x1070ff + BitVec.ofNat 64 (callMemLen (.rip 0xfccfb)))) 0x12a750) (callEffect (callMemPtr 0x1070ff (.rip 0xfccfb)) (0x1070ff + BitVec.ofNat 64 (callMemLen (.rip 0xfccfb)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x107105⟩) #v[]
    (.terminate (.call ⟨.l12a750, RegMap.args [(2, 55), (3, 3), (4, 59), (5, 5), (6, 53), (7, 57), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l107105, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l1070eb : List UInt8 :=
  [0x48, 0x8D, 0xB4, 0x24, 0x89, 0x00, 0x00, 0x00, 0xBA, 0x27, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC7,
    0xB9, 0x28, 0x20, 0x00, 0xFF, 0x15, 0xFB, 0xCC, 0x0F, 0x00]

theorem code_l1070eb : ∀ x ∈ codeRange 0x1070eb bytes_l1070eb, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x70eb 26 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l107105 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x107105 (testR32R32Effect 0x107105 2 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[0, 0]
    (.letOp (n := 54) (.exec 0x107105 (fun s => s.RIP = 0x107105) (testR32R32Effect 0x107105 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l107110, RegMap.args [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l107109, RegMap.args [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l107105 : List UInt8 :=
  [0x85, 0xC0, 0x74, 0x07]

theorem code_l107105 : ∀ x ∈ codeRange 0x107105 bytes_l107105, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x7105 4 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l107109 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x107109 (movR8Imm8Effect 0x107109 2 0 0x5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 54) (.exec 0x107109 (fun s => s.RIP = 0x107109) (movR8Imm8Effect 0x107109 2 0 0x5) (Reg.operands [.gpr 0] [])) #v[0]
    (.terminate (.br ⟨.l107623, RegMap.args [(0, 53), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l107109 : List UInt8 :=
  [0xB0, 0x05, 0xE9, 0x13, 0x05, 0x00, 0x00]

theorem code_l107109 : ∀ x ∈ codeRange 0x107109 bytes_l107109, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x7109 7 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l107110 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x107110 (cmpR64Imm8Effect 0x107110 13 0x20) (EffectPart.reads (.flag .ZF) [.gpr 13] []) (.flag .ZF)) #v[13]
    (.letOp (n := 54) (.exec 0x107110 (fun s => s.RIP = 0x107110) (cmpR64Imm8Effect 0x107110 13 0x20) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l107139, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l107116, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l107110 : List UInt8 :=
  [0x49, 0x83, 0xFD, 0x20, 0x75, 0x23]

theorem code_l107110 : ∀ x ∈ codeRange 0x107110 bytes_l107110, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x7110 6 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l107116 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x107116 (leaR64Effect 0x107116 7 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x107116 (fun s => s.RIP = 0x107116) (leaR64Effect 0x107116 7 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10711e (movR64R64Effect 0x10711e 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 12] []) (.reg (.gpr 6))) #v[12]
    (.letOp (n := 56) (.exec 0x10711e (fun s => s.RIP = 0x10711e) (movR64R64Effect 0x10711e 6 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 57) (.out 0x107121 (callEffect (fun _ => 0x106dd0) 0x107126) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x107121 (PushPre 0x107121 5) (callEffect (fun _ => 0x106dd0) 0x107126) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x107126⟩) #v[]
    (.terminate (.call ⟨.l106dd0, RegMap.args [(3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ { target := .l107126, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l107116 : List UInt8 :=
  [0x48, 0x8D, 0xBC, 0x24, 0x88, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xE6, 0xE8, 0xAA, 0xFC, 0xFF, 0xFF]

theorem code_l107116 : ∀ x ∈ codeRange 0x107116 bytes_l107116, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x7116 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l107126 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x107126 (cmpM8Imm8Effect 0x107126 8 (.sib 4 none 0 (.d32 0x88)) 0x0) (EffectPart.reads (.flag .ZF) [.gpr 4] []) (.flag .ZF)) #v[4]
    (.letOp (n := 54) (.exec 0x107126 (LoadPre 0x107126 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x107126 + BitVec.ofNat 64 8)) 1) (cmpM8Imm8Effect 0x107126 8 (.sib 4 none 0 (.d32 0x88)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l10724d, RegMap.args [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l107134, RegMap.args [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l107126 : List UInt8 :=
  [0x80, 0xBC, 0x24, 0x88, 0x00, 0x00, 0x00, 0x00, 0x0F, 0x84, 0x19, 0x01, 0x00, 0x00]

theorem code_l107126 : ∀ x ∈ codeRange 0x107126 bytes_l107126, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x7126 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l107134 : Block Op Label signature Reg.count 53 :=
  .terminate (.br ⟨.l107535, RegMap.args (entryMap (live .l107134)) 53⟩)

def bytes_l107134 : List UInt8 :=
  [0xE9, 0xFC, 0x03, 0x00, 0x00]

theorem code_l107134 : ∀ x ∈ codeRange 0x107134 bytes_l107134, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x7134 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l107139 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x107139 (movR64Imm64Effect 0x107139 0 0x7ffffffffffffff8) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 54) (.exec 0x107139 (fun s => s.RIP = 0x107139) (movR64Imm64Effect 0x107139 0 0x7ffffffffffffff8) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x107143 (andR64R64Effect 0x107143 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 13] []) (.reg (.gpr 0))) #v[53, 13]
    (.letOp (n := 56) (.exec 0x107143 (fun s => s.RIP = 0x107143) (andR64R64Effect 0x107143 0 13) (Reg.operands [.gpr 0, .gpr 13] [])) #v[53, 13]
    (.letOp (n := 57) (.out 0x107146 (cmpR64Imm8Effect 0x107146 0 0x18) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[55]
    (.letOp (n := 58) (.exec 0x107146 (fun s => s.RIP = 0x107146) (cmpR64Imm8Effect 0x107146 0 0x18) (Reg.operands [.gpr 0] [])) #v[55]
    (.letOp (n := 59) (.pure (condOp 5)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l10751b, RegMap.args [(0, 55), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l107150, RegMap.args [(0, 55), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l107139 : List UInt8 :=
  [0x48, 0xB8, 0xF8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F, 0x4C, 0x21, 0xE8, 0x48, 0x83, 0xF8,
    0x18, 0x0F, 0x85, 0xCB, 0x03, 0x00, 0x00]

theorem code_l107139 : ∀ x ∈ codeRange 0x107139 bytes_l107139, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x7139 23 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l107150 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x107150 (StorePre 0x107150 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x107150 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x107150 (.sib 4 none 0 (.d8 0x48)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.exec 0x107159 (StorePre 0x107159 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x107159 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x107159 (.sib 4 none 0 (.d8 0x40)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x107162 (StorePre 0x107162 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x107162 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x107162 (.sib 4 none 0 (.d8 0x38)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.exec 0x10716b (StorePre 0x10716b 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10716b + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10716b (.sib 4 none 0 (.d8 0x30)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x107174 (leaR64Effect 0x107174 5 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 58) (.exec 0x107174 (fun s => s.RIP = 0x107174) (leaR64Effect 0x107174 5 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x107179 (movR64R64Effect 0x107179 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[57]
    (.letOp (n := 60) (.exec 0x107179 (fun s => s.RIP = 0x107179) (movR64R64Effect 0x107179 7 5) (Reg.operands [.gpr 5] [])) #v[57]
    (.letOp (n := 61) (.out 0x10717c (subR64R64Effect 0x10717c 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 13] []) (.reg (.gpr 7))) #v[59, 13]
    (.letOp (n := 62) (.exec 0x10717c (fun s => s.RIP = 0x10717c) (subR64R64Effect 0x10717c 7 13) (Reg.operands [.gpr 7, .gpr 13] [])) #v[59, 13]
    (.letOp (n := 63) (.out 0x10717f (addR64Imm8Effect 0x10717f 7 0x20) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[61]
    (.letOp (n := 64) (.exec 0x10717f (fun s => s.RIP = 0x10717f) (addR64Imm8Effect 0x10717f 7 0x20) (Reg.operands [.gpr 7] [])) #v[61]
    (.letOp (n := 65) (.out 0x107183 (movR64R64Effect 0x107183 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 12] []) (.reg (.gpr 6))) #v[12]
    (.letOp (n := 66) (.exec 0x107183 (fun s => s.RIP = 0x107183) (movR64R64Effect 0x107183 6 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 67) (.out 0x107186 (movR64R64Effect 0x107186 2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13] []) (.reg (.gpr 2))) #v[13]
    (.letOp (n := 68) (.exec 0x107186 (fun s => s.RIP = 0x107186) (movR64R64Effect 0x107186 2 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 69) (.out 0x107189 (callEffect (callMemPtr 0x107189 (.rip 0xfcc41)) (0x107189 + BitVec.ofNat 64 (callMemLen (.rip 0xfcc41)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 70) (.exec 0x107189 (GoesTo (CallMemPre 0x107189 (.rip 0xfcc41)) (callEffect (callMemPtr 0x107189 (.rip 0xfcc41)) (0x107189 + BitVec.ofNat 64 (callMemLen (.rip 0xfcc41)))) 0x12a820) (callEffect (callMemPtr 0x107189 (.rip 0xfcc41)) (0x107189 + BitVec.ofNat 64 (callMemLen (.rip 0xfcc41)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.const ⟨64, 0x10718f⟩) #v[]
    (.terminate (.call ⟨.l12a820, RegMap.args [(2, 67), (3, 3), (4, 69), (5, 57), (6, 65), (7, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩ { target := .l10718f, kept := #v[], arity := rfl, guard := some (Fin.last 71) }))))))))))))))))))))

def bytes_l107150 : List UInt8 :=
  [0x48, 0xC7, 0x44, 0x24, 0x48, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x40, 0x00, 0x00,
    0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x38, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x30,
    0x00, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x6C, 0x24, 0x30, 0x48, 0x89, 0xEF, 0x4C, 0x29, 0xEF, 0x48,
    0x83, 0xC7, 0x20, 0x4C, 0x89, 0xE6, 0x4C, 0x89, 0xEA, 0xFF, 0x15, 0x41, 0xCC, 0x0F, 0x00]

theorem code_l107150 : ∀ x ∈ codeRange 0x107150 bytes_l107150, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x7150 63 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10718f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10718f (leaR64Effect 0x10718f 7 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x10718f (fun s => s.RIP = 0x10718f) (leaR64Effect 0x10718f 7 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x107197 (movR64R64Effect 0x107197 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[5]
    (.letOp (n := 56) (.exec 0x107197 (fun s => s.RIP = 0x107197) (movR64R64Effect 0x107197 6 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 57) (.out 0x10719a (callEffect (fun _ => 0x106dd0) 0x10719f) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x10719a (PushPre 0x10719a 5) (callEffect (fun _ => 0x106dd0) 0x10719f) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x10719f⟩) #v[]
    (.terminate (.call ⟨.l106dd0, RegMap.args [(3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ { target := .l10719f, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l10718f : List UInt8 :=
  [0x48, 0x8D, 0xBC, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x89, 0xEE, 0xE8, 0x31, 0xFC, 0xFF, 0xFF]

theorem code_l10718f : ∀ x ∈ codeRange 0x10718f bytes_l10718f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x718f 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10719f_1 : Block Op Label signature Reg.count 73 :=
  .letOp (n := 73) (.exec 0x107203 (StorePre 0x107203 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x107203 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x107203 (.sib 4 none 0 (.d8 0x44)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.exec 0x107208 (StorePre 0x107208 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x45)) s (0x107208 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x107208 (.sib 4 none 0 (.d8 0x45)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.exec 0x10720d (StorePre 0x10720d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x46)) s (0x10720d + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x10720d (.sib 4 none 0 (.d8 0x46)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 76) (.exec 0x107212 (StorePre 0x107212 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x47)) s (0x107212 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x107212 (.sib 4 none 0 (.d8 0x47)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 77) (.exec 0x107217 (StorePre 0x107217 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x107217 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x107217 (.sib 4 none 0 (.d8 0x48)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 78) (.exec 0x10721c (StorePre 0x10721c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x49)) s (0x10721c + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x10721c (.sib 4 none 0 (.d8 0x49)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.exec 0x107221 (StorePre 0x107221 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4a)) s (0x107221 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x107221 (.sib 4 none 0 (.d8 0x4a)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 80) (.exec 0x107226 (StorePre 0x107226 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4b)) s (0x107226 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x107226 (.sib 4 none 0 (.d8 0x4b)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 81) (.exec 0x10722b (StorePre 0x10722b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4c)) s (0x10722b + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x10722b (.sib 4 none 0 (.d8 0x4c)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 82) (.exec 0x107230 (StorePre 0x107230 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4d)) s (0x107230 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x107230 (.sib 4 none 0 (.d8 0x4d)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 83) (.exec 0x107235 (StorePre 0x107235 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4e)) s (0x107235 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x107235 (.sib 4 none 0 (.d8 0x4e)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 84) (.exec 0x10723a (StorePre 0x10723a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4f)) s (0x10723a + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x10723a (.sib 4 none 0 (.d8 0x4f)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 85) (.out 0x10723f (cmpM8Imm8Effect 0x10723f 8 (.sib 4 none 0 (.d32 0x88)) 0x0) (EffectPart.reads (.flag .ZF) [.gpr 4] []) (.flag .ZF)) #v[4]
    (.letOp (n := 86) (.exec 0x10723f (LoadPre 0x10723f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10723f + BitVec.ofNat 64 8)) 1) (cmpM8Imm8Effect 0x10723f 8 (.sib 4 none 0 (.d32 0x88)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 87) (.pure (condOp 5)) #v[85]
    (.terminate (.condBr (Fin.last 87) ⟨.l107535, RegMap.args [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 85), (22, 22), (39, 39), (50, 50), (51, 51)] 88⟩ ⟨.l10724d, RegMap.args [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 85), (22, 22), (39, 39), (50, 50), (51, 51)] 88⟩))))))))))))))))

def bytes_l10719f_1 : List UInt8 :=
  [0xC6, 0x44, 0x24, 0x44, 0x00, 0xC6, 0x44, 0x24, 0x45, 0x00, 0xC6, 0x44, 0x24, 0x46, 0x00, 0xC6,
    0x44, 0x24, 0x47, 0x00, 0xC6, 0x44, 0x24, 0x48, 0x00, 0xC6, 0x44, 0x24, 0x49, 0x00, 0xC6, 0x44,
    0x24, 0x4A, 0x00, 0xC6, 0x44, 0x24, 0x4B, 0x00, 0xC6, 0x44, 0x24, 0x4C, 0x00, 0xC6, 0x44, 0x24,
    0x4D, 0x00, 0xC6, 0x44, 0x24, 0x4E, 0x00, 0xC6, 0x44, 0x24, 0x4F, 0x00, 0x80, 0xBC, 0x24, 0x88,
    0x00, 0x00, 0x00, 0x00, 0x0F, 0x85, 0xE8, 0x02, 0x00, 0x00]

theorem code_l10719f_1 : ∀ x ∈ codeRange 0x107203 bytes_l10719f_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x7203 74 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10719f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x10719f (StorePre 0x10719f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10719f + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x10719f (.sib 4 none 0 (.d8 0x30)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.exec 0x1071a4 (StorePre 0x1071a4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x31)) s (0x1071a4 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x1071a4 (.sib 4 none 0 (.d8 0x31)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x1071a9 (StorePre 0x1071a9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x32)) s (0x1071a9 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x1071a9 (.sib 4 none 0 (.d8 0x32)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.exec 0x1071ae (StorePre 0x1071ae 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x33)) s (0x1071ae + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x1071ae (.sib 4 none 0 (.d8 0x33)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x1071b3 (StorePre 0x1071b3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x1071b3 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x1071b3 (.sib 4 none 0 (.d8 0x34)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x1071b8 (StorePre 0x1071b8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x35)) s (0x1071b8 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x1071b8 (.sib 4 none 0 (.d8 0x35)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.exec 0x1071bd (StorePre 0x1071bd 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x36)) s (0x1071bd + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x1071bd (.sib 4 none 0 (.d8 0x36)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.exec 0x1071c2 (StorePre 0x1071c2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x37)) s (0x1071c2 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x1071c2 (.sib 4 none 0 (.d8 0x37)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x1071c7 (StorePre 0x1071c7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1071c7 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x1071c7 (.sib 4 none 0 (.d8 0x38)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.exec 0x1071cc (StorePre 0x1071cc 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x39)) s (0x1071cc + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x1071cc (.sib 4 none 0 (.d8 0x39)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x1071d1 (StorePre 0x1071d1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3a)) s (0x1071d1 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x1071d1 (.sib 4 none 0 (.d8 0x3a)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x1071d6 (StorePre 0x1071d6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3b)) s (0x1071d6 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x1071d6 (.sib 4 none 0 (.d8 0x3b)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.exec 0x1071db (StorePre 0x1071db 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x1071db + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x1071db (.sib 4 none 0 (.d8 0x3c)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x1071e0 (StorePre 0x1071e0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3d)) s (0x1071e0 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x1071e0 (.sib 4 none 0 (.d8 0x3d)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x1071e5 (StorePre 0x1071e5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3e)) s (0x1071e5 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x1071e5 (.sib 4 none 0 (.d8 0x3e)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.exec 0x1071ea (StorePre 0x1071ea 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3f)) s (0x1071ea + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x1071ea (.sib 4 none 0 (.d8 0x3f)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.exec 0x1071ef (StorePre 0x1071ef 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1071ef + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x1071ef (.sib 4 none 0 (.d8 0x40)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.exec 0x1071f4 (StorePre 0x1071f4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x41)) s (0x1071f4 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x1071f4 (.sib 4 none 0 (.d8 0x41)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.exec 0x1071f9 (StorePre 0x1071f9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x42)) s (0x1071f9 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x1071f9 (.sib 4 none 0 (.d8 0x42)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.exec 0x1071fe (StorePre 0x1071fe 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x43)) s (0x1071fe + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x1071fe (.sib 4 none 0 (.d8 0x43)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l10719f_1))))))))))))))))))))

def bytes_l10719f : List UInt8 :=
  [0xC6, 0x44, 0x24, 0x30, 0x00, 0xC6, 0x44, 0x24, 0x31, 0x00, 0xC6, 0x44, 0x24, 0x32, 0x00, 0xC6,
    0x44, 0x24, 0x33, 0x00, 0xC6, 0x44, 0x24, 0x34, 0x00, 0xC6, 0x44, 0x24, 0x35, 0x00, 0xC6, 0x44,
    0x24, 0x36, 0x00, 0xC6, 0x44, 0x24, 0x37, 0x00, 0xC6, 0x44, 0x24, 0x38, 0x00, 0xC6, 0x44, 0x24,
    0x39, 0x00, 0xC6, 0x44, 0x24, 0x3A, 0x00, 0xC6, 0x44, 0x24, 0x3B, 0x00, 0xC6, 0x44, 0x24, 0x3C,
    0x00, 0xC6, 0x44, 0x24, 0x3D, 0x00, 0xC6, 0x44, 0x24, 0x3E, 0x00, 0xC6, 0x44, 0x24, 0x3F, 0x00,
    0xC6, 0x44, 0x24, 0x40, 0x00, 0xC6, 0x44, 0x24, 0x41, 0x00, 0xC6, 0x44, 0x24, 0x42, 0x00, 0xC6,
    0x44, 0x24, 0x43, 0x00] ++ bytes_l10719f_1

theorem code_l10719f : ∀ x ∈ codeRange 0x10719f bytes_l10719f, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x719f 100 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10719f_1

@[cfg_block] def b_l10724d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10724d (movzxR32M8Effect 0x10724d 8 5 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 54) (.exec 0x10724d (LoadPre 0x10724d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x10724d + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x10724d 8 5 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x107255 (movzxR32M16Effect 0x107255 8 0 (.sib 4 none 0 (.d32 0x91))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 56) (.exec 0x107255 (LoadPre 0x107255 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x91)) s (0x107255 + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x107255 8 0 (.sib 4 none 0 (.d32 0x91))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x10725d (StorePre 0x10725d 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10725d + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x10725d 4 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 58) (.out 0x107261 (movzxR32M8Effect 0x107261 8 0 (.sib 4 none 0 (.d32 0x93))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 59) (.exec 0x107261 (LoadPre 0x107261 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x93)) s (0x107261 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107261 8 0 (.sib 4 none 0 (.d32 0x93))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.exec 0x107269 (StorePre 0x107269 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2)) s (0x107269 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x107269 4 0 (.sib 4 none 0 (.d8 0x2))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[58, 4]
    (.letOp (n := 61) (.out 0x10726d (movzxR32M8Effect 0x10726d 9 12 (.sib 4 none 0 (.d32 0x94))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 62) (.exec 0x10726d (LoadPre 0x10726d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x94)) s (0x10726d + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x10726d 9 12 (.sib 4 none 0 (.d32 0x94))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x107276 (movR64M64Effect 0x107276 0 (.sib 4 none 0 (.d32 0x95))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 64) (.exec 0x107276 (LoadPre 0x107276 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x95)) s (0x107276 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107276 0 (.sib 4 none 0 (.d32 0x95))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.exec 0x10727e (StorePre 0x10727e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10727e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10727e 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[63, 4]
    (.letOp (n := 66) (.out 0x107283 (movR64M64Effect 0x107283 0 (.sib 4 none 0 (.d32 0x9d))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 67) (.exec 0x107283 (LoadPre 0x107283 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9d)) s (0x107283 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107283 0 (.sib 4 none 0 (.d32 0x9d))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.exec 0x10728b (StorePre 0x10728b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10728b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10728b 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[66, 4]
    (.letOp (n := 69) (.out 0x107290 (movR64M64Effect 0x107290 0 (.sib 4 none 0 (.d32 0xa5))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 70) (.exec 0x107290 (LoadPre 0x107290 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa5)) s (0x107290 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107290 0 (.sib 4 none 0 (.d32 0xa5))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.exec 0x107298 (StorePre 0x107298 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x107298 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107298 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[69, 4]
    (.letOp (n := 72) (.out 0x10729d (movR32M32LowEffect 0x10729d 0 (.sib 4 none 0 (.d32 0xac))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 73) (.exec 0x10729d (LoadPre 0x10729d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xac)) s (0x10729d + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x10729d 0 (.sib 4 none 0 (.d32 0xac))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.exec 0x1072a4 (StorePre 0x1072a4 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x27)) s (0x1072a4 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x1072a4 0 (.sib 4 none 0 (.d8 0x27))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[72, 4]
    (.letOp (n := 75) (.out 0x1072a8 (testR64R64Effect 0x1072a8 15 15) (EffectPart.reads (.flag .ZF) [.gpr 15, .gpr 15] []) (.flag .ZF)) #v[15, 15]
    (.letOp (n := 76) (.exec 0x1072a8 (fun s => s.RIP = 0x1072a8) (testR64R64Effect 0x1072a8 15 15) (Reg.operands [.gpr 15, .gpr 15] [])) #v[15, 15]
    (.letOp (n := 77) (.pure (condOp 4)) #v[75]
    (.terminate (.condBr (Fin.last 77) ⟨.l1076a0, RegMap.args [(0, 72), (2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 13), (14, 14), (15, 15), (19, 75), (22, 22), (39, 39), (50, 50), (51, 51)] 78⟩ ⟨.l1072b1, RegMap.args [(0, 72), (2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 13), (14, 14), (15, 15), (19, 75), (22, 22), (39, 39), (50, 50), (51, 51)] 78⟩))))))))))))))))))))))))))

def bytes_l10724d : List UInt8 :=
  [0x0F, 0xB6, 0xAC, 0x24, 0x90, 0x00, 0x00, 0x00, 0x0F, 0xB7, 0x84, 0x24, 0x91, 0x00, 0x00, 0x00,
    0x66, 0x89, 0x04, 0x24, 0x0F, 0xB6, 0x84, 0x24, 0x93, 0x00, 0x00, 0x00, 0x88, 0x44, 0x24, 0x02,
    0x44, 0x0F, 0xB6, 0xA4, 0x24, 0x94, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x84, 0x24, 0x95, 0x00, 0x00,
    0x00, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B, 0x84, 0x24, 0x9D, 0x00, 0x00, 0x00, 0x48, 0x89,
    0x44, 0x24, 0x18, 0x48, 0x8B, 0x84, 0x24, 0xA5, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x20,
    0x8B, 0x84, 0x24, 0xAC, 0x00, 0x00, 0x00, 0x89, 0x44, 0x24, 0x27, 0x4D, 0x85, 0xFF, 0x0F, 0x84,
    0xEF, 0x03, 0x00, 0x00]

theorem code_l10724d : ∀ x ∈ codeRange 0x10724d bytes_l10724d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x724d 100 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1072b1 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1072b1 (testR64R64Effect 0x1072b1 14 14) (EffectPart.reads (.flag .ZF) [.gpr 14, .gpr 14] []) (.flag .ZF)) #v[14, 14]
    (.letOp (n := 54) (.exec 0x1072b1 (fun s => s.RIP = 0x1072b1) (testR64R64Effect 0x1072b1 14 14) (Reg.operands [.gpr 14, .gpr 14] [])) #v[14, 14]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l10756c, RegMap.args [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l1072ba, RegMap.args [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l1072b1 : List UInt8 :=
  [0x4D, 0x85, 0xF6, 0x0F, 0x84, 0xB2, 0x02, 0x00, 0x00]

theorem code_l1072b1 : ∀ x ∈ codeRange 0x1072b1 bytes_l1072b1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x72b1 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1072ba : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1072ba (movzxR32M8Effect 0x1072ba 4 1 (.base 15 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 15] []) (.reg (.gpr 1))) #v[15]
    (.letOp (n := 54) (.exec 0x1072ba (LoadPre 0x1072ba (fun s => AddrMode.addr (.base 15 .none) s (0x1072ba + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x1072ba 4 1 (.base 15 .none)) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.out 0x1072be (cmpR64Imm8Effect 0x1072be 1 0x6) (EffectPart.reads (.flag .CF) [.gpr 1] []) (.flag .CF)) #v[53]
    (.letOp (n := 56) (.exec 0x1072be (fun s => s.RIP = 0x1072be) (cmpR64Imm8Effect 0x1072be 1 0x6) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 57) (.out 0x1072c2 (atFlags (condHolds 2) (setccR8Effect 0x1072c2 3 0)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 0))) #v[0, 55]
    (.letOp (n := 58) (.exec 0x1072c2 (fun s => s.RIP = 0x1072c2) (atFlags (condHolds 2) (setccR8Effect 0x1072c2 3 0)) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[0, 55]
    (.letOp (n := 59) (.out 0x1072c5 (movR8Imm8Effect 0x1072c5 2 2 0x3d) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[2]
    (.letOp (n := 60) (.exec 0x1072c5 (fun s => s.RIP = 0x1072c5) (movR8Imm8Effect 0x1072c5 2 2 0x3d) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 61) (.out 0x1072c7 (shrR8ClEffect 0x1072c7 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[59, 53]
    (.letOp (n := 62) (.exec 0x1072c7 (fun s => s.RIP = 0x1072c7) (shrR8ClEffect 0x1072c7 2 2) (Reg.operands [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[59, 53]
    (.letOp (n := 63) (.out 0x1072c9 (andR8R8Effect 0x1072c9 2 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[61, 57]
    (.letOp (n := 64) (.exec 0x1072c9 (fun s => s.RIP = 0x1072c9) (andR8R8Effect 0x1072c9 2 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[61, 57]
    (.letOp (n := 65) (.out 0x1072cb (cmpR8Imm8Effect 0x1072cb 3 2 0x1) (EffectPart.reads (.flag .ZF) [.gpr 2] []) (.flag .ZF)) #v[63]
    (.letOp (n := 66) (.exec 0x1072cb (fun s => s.RIP = 0x1072cb) (cmpR8Imm8Effect 0x1072cb 3 2 0x1) (Reg.operands [.gpr 2] [])) #v[63]
    (.letOp (n := 67) (.pure (condOp 5)) #v[65]
    (.terminate (.condBr (Fin.last 67) ⟨.l10756c, RegMap.args [(0, 57), (1, 53), (2, 63), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 65), (22, 22), (39, 39), (50, 50), (51, 51)] 68⟩ ⟨.l1072d4, RegMap.args [(0, 57), (1, 53), (2, 63), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 65), (22, 22), (39, 39), (50, 50), (51, 51)] 68⟩))))))))))))))))

def bytes_l1072ba : List UInt8 :=
  [0x41, 0x0F, 0xB6, 0x0F, 0x48, 0x83, 0xF9, 0x06, 0x0F, 0x92, 0xC0, 0xB2, 0x3D, 0xD2, 0xEA, 0x20,
    0xC2, 0x80, 0xFA, 0x01, 0x0F, 0x85, 0x98, 0x02, 0x00, 0x00]

theorem code_l1072ba : ∀ x ∈ codeRange 0x1072ba bytes_l1072ba, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x72ba 26 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1072d4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1072d4 (cmpR64M64Effect 0x1072d4 14 (.abs (some 1) 3 0x202ad8)) (EffectPart.reads (.flag .ZF) [.gpr 14, .gpr 1] []) (.flag .ZF)) #v[14, 1]
    (.letOp (n := 54) (.exec 0x1072d4 (LoadPre 0x1072d4 (fun s => AddrMode.addr (.abs (some 1) 3 0x202ad8) s (0x1072d4 + BitVec.ofNat 64 8)) 8) (cmpR64M64Effect 0x1072d4 14 (.abs (some 1) 3 0x202ad8)) (Reg.operands [.gpr 14, .gpr 1] [])) #v[14, 1]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l10756c, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l1072e2, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l1072d4 : List UInt8 :=
  [0x4C, 0x3B, 0x34, 0xCD, 0xD8, 0x2A, 0x20, 0x00, 0x0F, 0x85, 0x8A, 0x02, 0x00, 0x00]

theorem code_l1072d4 : ∀ x ∈ codeRange 0x1072d4 bytes_l1072d4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x72d4 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1072e2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1072e2 (movR32Imm32Effect 0x1072e2 5 0 0x41) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 54) (.exec 0x1072e2 (fun s => s.RIP = 0x1072e2) (movR32Imm32Effect 0x1072e2 5 0 0x41) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x1072e7 (subR64R64Effect 0x1072e7 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[53, 14]
    (.letOp (n := 56) (.exec 0x1072e7 (fun s => s.RIP = 0x1072e7) (subR64R64Effect 0x1072e7 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 57) (.out 0x1072ea (xorR32R32Effect 0x1072ea 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[2, 2]
    (.letOp (n := 58) (.exec 0x1072ea (fun s => s.RIP = 0x1072ea) (xorR32R32Effect 0x1072ea 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 59) (.out 0x1072ec (cmpR64Imm8Effect 0x1072ec 14 0x41) (EffectPart.reads (.flag .CF) [.gpr 14] []) (.flag .CF)) #v[14]
    (.letOp (n := 60) (.exec 0x1072ec (fun s => s.RIP = 0x1072ec) (cmpR64Imm8Effect 0x1072ec 14 0x41) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 61) (.out 0x1072f0 (atFlags (condHolds 2) (cmovR64R64Effect 0x1072f0 4 2 0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[57, 55, 59]
    (.letOp (n := 62) (.exec 0x1072f0 (fun s => s.RIP = 0x1072f0) (atFlags (condHolds 2) (cmovR64R64Effect 0x1072f0 4 2 0)) (Reg.operands [.gpr 2, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[57, 55, 59]
    (.letOp (n := 63) (.out 0x1072f4 (leaR64Effect 0x1072f4 7 (.sib 4 (some 14) 0 .none)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4, .gpr 14] []) (.reg (.gpr 7))) #v[4, 14]
    (.letOp (n := 64) (.exec 0x1072f4 (fun s => s.RIP = 0x1072f4) (leaR64Effect 0x1072f4 7 (.sib 4 (some 14) 0 .none)) (Reg.operands [.gpr 4, .gpr 14] [])) #v[4, 14]
    (.letOp (n := 65) (.out 0x1072f8 (addR64Imm32Effect 0x1072f8 7 0x88) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[63]
    (.letOp (n := 66) (.exec 0x1072f8 (fun s => s.RIP = 0x1072f8) (addR64Imm32Effect 0x1072f8 7 0x88) (Reg.operands [.gpr 7] [])) #v[63]
    (.letOp (n := 67) (.out 0x1072ff (xorR32R32Effect 0x1072ff 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[6, 6]
    (.letOp (n := 68) (.exec 0x1072ff (fun s => s.RIP = 0x1072ff) (xorR32R32Effect 0x1072ff 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 69) (.out 0x107301 (callEffect (callMemPtr 0x107301 (.rip 0xfcb09)) (0x107301 + BitVec.ofNat 64 (callMemLen (.rip 0xfcb09)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 70) (.exec 0x107301 (GoesTo (CallMemPre 0x107301 (.rip 0xfcb09)) (callEffect (callMemPtr 0x107301 (.rip 0xfcb09)) (0x107301 + BitVec.ofNat 64 (callMemLen (.rip 0xfcb09)))) 0x12a700) (callEffect (callMemPtr 0x107301 (.rip 0xfcb09)) (0x107301 + BitVec.ofNat 64 (callMemLen (.rip 0xfcb09)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.const ⟨64, 0x107307⟩) #v[]
    (.terminate (.call ⟨.l12a700, RegMap.args [(0, 55), (2, 61), (3, 3), (4, 69), (5, 5), (6, 67), (7, 65), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩ { target := .l107307, kept := #v[], arity := rfl, guard := some (Fin.last 71) }))))))))))))))))))))

def bytes_l1072e2 : List UInt8 :=
  [0xB8, 0x41, 0x00, 0x00, 0x00, 0x4C, 0x29, 0xF0, 0x31, 0xD2, 0x49, 0x83, 0xFE, 0x41, 0x48, 0x0F,
    0x42, 0xD0, 0x4A, 0x8D, 0x3C, 0x34, 0x48, 0x81, 0xC7, 0x88, 0x00, 0x00, 0x00, 0x31, 0xF6, 0xFF,
    0x15, 0x09, 0xCB, 0x0F, 0x00]

theorem code_l1072e2 : ∀ x ∈ codeRange 0x1072e2 bytes_l1072e2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x72e2 37 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l107307 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x107307 (leaR64Effect 0x107307 7 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x107307 (fun s => s.RIP = 0x107307) (leaR64Effect 0x107307 7 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10730f (movR64R64Effect 0x10730f 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 56) (.exec 0x10730f (fun s => s.RIP = 0x10730f) (movR64R64Effect 0x10730f 6 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 57) (.out 0x107312 (movR64R64Effect 0x107312 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14] []) (.reg (.gpr 2))) #v[14]
    (.letOp (n := 58) (.exec 0x107312 (fun s => s.RIP = 0x107312) (movR64R64Effect 0x107312 2 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 59) (.out 0x107315 (callEffect (callMemPtr 0x107315 (.rip 0xfcab5)) (0x107315 + BitVec.ofNat 64 (callMemLen (.rip 0xfcab5)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x107315 (GoesTo (CallMemPre 0x107315 (.rip 0xfcab5)) (callEffect (callMemPtr 0x107315 (.rip 0xfcab5)) (0x107315 + BitVec.ofNat 64 (callMemLen (.rip 0xfcab5)))) 0x12a820) (callEffect (callMemPtr 0x107315 (.rip 0xfcab5)) (0x107315 + BitVec.ofNat 64 (callMemLen (.rip 0xfcab5)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x10731b⟩) #v[]
    (.terminate (.call ⟨.l12a820, RegMap.args [(2, 57), (3, 3), (4, 59), (5, 5), (6, 55), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l10731b, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l107307 : List UInt8 :=
  [0x48, 0x8D, 0xBC, 0x24, 0x88, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xFE, 0x4C, 0x89, 0xF2, 0xFF, 0x15,
    0xB5, 0xCA, 0x0F, 0x00]

theorem code_l107307 : ∀ x ∈ codeRange 0x107307 bytes_l107307, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x7307 20 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10731b_2 : Block Op Label signature Reg.count 109 :=
  .letOp (n := 109) (.out 0x107436 (movR64M64Effect 0x107436 1 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 110) (.exec 0x107436 (LoadPre 0x107436 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x107436 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107436 1 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 111) (.exec 0x10743b (StorePre 0x10743b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x105)) s (0x10743b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10743b 0 (.sib 4 none 0 (.d32 0x105))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[107, 4]
    (.letOp (n := 112) (.exec 0x107443 (StorePre 0x107443 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x10d)) s (0x107443 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107443 1 (.sib 4 none 0 (.d32 0x10d))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[109, 4]
    (.letOp (n := 113) (.out 0x10744b (movR64M64Effect 0x10744b 0 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 114) (.exec 0x10744b (LoadPre 0x10744b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10744b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10744b 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 115) (.exec 0x107450 (StorePre 0x107450 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x115)) s (0x107450 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107450 0 (.sib 4 none 0 (.d32 0x115))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[113, 4]
    (.letOp (n := 116) (.out 0x107458 (movR32M32LowEffect 0x107458 0 (.sib 4 none 0 (.d8 0x27))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 117) (.exec 0x107458 (LoadPre 0x107458 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x27)) s (0x107458 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x107458 0 (.sib 4 none 0 (.d8 0x27))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 118) (.exec 0x10745c (StorePre 0x10745c 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x11c)) s (0x10745c + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x10745c 0 (.sib 4 none 0 (.d32 0x11c))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[116, 4]
    (.letOp (n := 119) (.out 0x107463 (leaR64Effect 0x107463 14 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 120) (.exec 0x107463 (fun s => s.RIP = 0x107463) (leaR64Effect 0x107463 14 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 121) (.out 0x10746b (leaR64Effect 0x10746b 6 (.sib 4 none 0 (.d32 0x100))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 122) (.exec 0x10746b (fun s => s.RIP = 0x10746b) (leaR64Effect 0x10746b 6 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 123) (.out 0x107473 (movR64R64Effect 0x107473 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[119]
    (.letOp (n := 124) (.exec 0x107473 (fun s => s.RIP = 0x107473) (movR64R64Effect 0x107473 7 14) (Reg.operands [.gpr 14] [])) #v[119]
    (.letOp (n := 125) (.out 0x107476 (callEffect (fun _ => 0x10ee80) 0x10747b) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 126) (.exec 0x107476 (PushPre 0x107476 5) (callEffect (fun _ => 0x10ee80) 0x10747b) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 127) (.const ⟨64, 0x10747b⟩) #v[]
    (.terminate (.call ⟨.l10ee80, RegMap.args [(0, 116), (1, 109), (2, 69), (3, 3), (4, 125), (5, 5), (6, 121), (7, 123), (8, 78), (9, 81), (10, 84), (11, 87), (12, 12), (13, 13), (14, 119), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 128⟩ { target := .l10747b, kept := #v[], arity := rfl, guard := some (Fin.last 127) }))))))))))))))))))))

def bytes_l10731b_2 : List UInt8 :=
  [0x48, 0x8B, 0x4C, 0x24, 0x18, 0x48, 0x89, 0x84, 0x24, 0x05, 0x01, 0x00, 0x00, 0x48, 0x89, 0x8C,
    0x24, 0x0D, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x20, 0x48, 0x89, 0x84, 0x24, 0x15, 0x01,
    0x00, 0x00, 0x8B, 0x44, 0x24, 0x27, 0x89, 0x84, 0x24, 0x1C, 0x01, 0x00, 0x00, 0x4C, 0x8D, 0xB4,
    0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x8D, 0xB4, 0x24, 0x00, 0x01, 0x00, 0x00, 0x4C, 0x89, 0xF7,
    0xE8, 0x05, 0x7A, 0x00, 0x00]

theorem code_l10731b_2 : ∀ x ∈ codeRange 0x107436 bytes_l10731b_2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x7436 69 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10731b_1 : Block Op Label signature Reg.count 84 :=
  .letOp (n := 84) (.out 0x1073a1 (movzxR32M16Effect 0x1073a1 9 10 (.sib 4 none 0 (.d32 0xc7))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 85) (.exec 0x1073a1 (LoadPre 0x1073a1 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc7)) s (0x1073a1 + BitVec.ofNat 64 9)) 2) (movzxR32M16Effect 0x1073a1 9 10 (.sib 4 none 0 (.d32 0xc7))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 86) (.exec 0x1073aa (StorePre 0x1073aa 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x198)) s (0x1073aa + BitVec.ofNat 64 9)) 2) (movM16R16Effect 0x1073aa 9 10 (.sib 4 none 0 (.d32 0x198))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[84, 4]
    (.letOp (n := 87) (.out 0x1073b3 (movR64M64Effect 0x1073b3 11 (.sib 4 none 0 (.d32 0xbf))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 88) (.exec 0x1073b3 (LoadPre 0x1073b3 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xbf)) s (0x1073b3 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1073b3 11 (.sib 4 none 0 (.d32 0xbf))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 89) (.exec 0x1073bb (StorePre 0x1073bb 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x190)) s (0x1073bb + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1073bb 11 (.sib 4 none 0 (.d32 0x190))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[87, 4]
    (.letOp (n := 90) (.exec 0x1073c3 (StorePre 0x1073c3 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x12b)) s (0x1073c3 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x1073c3 0 (.sib 4 none 0 (.d32 0x12b))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 91) (.exec 0x1073ca (StorePre 0x1073ca 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x12f)) s (0x1073ca + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x1073ca 7 1 (.sib 4 none 0 (.d32 0x12f))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 92) (.exec 0x1073d1 (StorePre 0x1073d1 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x157)) s (0x1073d1 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x1073d1 2 (.sib 4 none 0 (.d32 0x157))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[69, 4]
    (.letOp (n := 93) (.exec 0x1073d8 (StorePre 0x1073d8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x14f)) s (0x1073d8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1073d8 6 (.sib 4 none 0 (.d32 0x14f))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[72, 4]
    (.letOp (n := 94) (.exec 0x1073e0 (StorePre 0x1073e0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x147)) s (0x1073e0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1073e0 7 (.sib 4 none 0 (.d32 0x147))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[75, 4]
    (.letOp (n := 95) (.exec 0x1073e8 (StorePre 0x1073e8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x13f)) s (0x1073e8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1073e8 8 (.sib 4 none 0 (.d32 0x13f))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[78, 4]
    (.letOp (n := 96) (.exec 0x1073f0 (StorePre 0x1073f0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x137)) s (0x1073f0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1073f0 9 (.sib 4 none 0 (.d32 0x137))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[81, 4]
    (.letOp (n := 97) (.exec 0x1073f8 (StorePre 0x1073f8 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x163)) s (0x1073f8 + BitVec.ofNat 64 9)) 2) (movM16R16Effect 0x1073f8 9 10 (.sib 4 none 0 (.d32 0x163))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[84, 4]
    (.letOp (n := 98) (.exec 0x107401 (StorePre 0x107401 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x15b)) s (0x107401 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107401 11 (.sib 4 none 0 (.d32 0x15b))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[87, 4]
    (.letOp (n := 99) (.exec 0x107409 (StorePre 0x107409 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x107409 + BitVec.ofNat 64 8)) 1) (movM8R8Effect 0x107409 8 5 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[5, 4]
    (.letOp (n := 100) (.out 0x107411 (movzxR32M16Effect 0x107411 4 0 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 101) (.exec 0x107411 (LoadPre 0x107411 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x107411 + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x107411 4 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 102) (.exec 0x107415 (StorePre 0x107415 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x101)) s (0x107415 + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x107415 8 0 (.sib 4 none 0 (.d32 0x101))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[100, 4]
    (.letOp (n := 103) (.out 0x10741d (movzxR32M8Effect 0x10741d 5 0 (.sib 4 none 0 (.d8 0x2))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 104) (.exec 0x10741d (LoadPre 0x10741d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2)) s (0x10741d + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10741d 5 0 (.sib 4 none 0 (.d8 0x2))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 105) (.exec 0x107422 (StorePre 0x107422 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x103)) s (0x107422 + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x107422 7 0 (.sib 4 none 0 (.d32 0x103))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[103, 4]
    (.letOp (n := 106) (.exec 0x107429 (StorePre 0x107429 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x104)) s (0x107429 + BitVec.ofNat 64 8)) 1) (movM8R8Effect 0x107429 8 12 (.sib 4 none 0 (.d32 0x104))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[12, 4]
    (.letOp (n := 107) (.out 0x107431 (movR64M64Effect 0x107431 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 108) (.exec 0x107431 (LoadPre 0x107431 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x107431 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107431 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l10731b_2)))))))))))))))))))))))))

def bytes_l10731b_1 : List UInt8 :=
  [0x44, 0x0F, 0xB7, 0x94, 0x24, 0xC7, 0x00, 0x00, 0x00, 0x66, 0x44, 0x89, 0x94, 0x24, 0x98, 0x01,
    0x00, 0x00, 0x4C, 0x8B, 0x9C, 0x24, 0xBF, 0x00, 0x00, 0x00, 0x4C, 0x89, 0x9C, 0x24, 0x90, 0x01,
    0x00, 0x00, 0x89, 0x84, 0x24, 0x2B, 0x01, 0x00, 0x00, 0x88, 0x8C, 0x24, 0x2F, 0x01, 0x00, 0x00,
    0x89, 0x94, 0x24, 0x57, 0x01, 0x00, 0x00, 0x48, 0x89, 0xB4, 0x24, 0x4F, 0x01, 0x00, 0x00, 0x48,
    0x89, 0xBC, 0x24, 0x47, 0x01, 0x00, 0x00, 0x4C, 0x89, 0x84, 0x24, 0x3F, 0x01, 0x00, 0x00, 0x4C,
    0x89, 0x8C, 0x24, 0x37, 0x01, 0x00, 0x00, 0x66, 0x44, 0x89, 0x94, 0x24, 0x63, 0x01, 0x00, 0x00,
    0x4C, 0x89, 0x9C, 0x24, 0x5B, 0x01, 0x00, 0x00, 0x40, 0x88, 0xAC, 0x24, 0x00, 0x01, 0x00, 0x00,
    0x0F, 0xB7, 0x04, 0x24, 0x66, 0x89, 0x84, 0x24, 0x01, 0x01, 0x00, 0x00, 0x0F, 0xB6, 0x44, 0x24,
    0x02, 0x88, 0x84, 0x24, 0x03, 0x01, 0x00, 0x00, 0x44, 0x88, 0xA4, 0x24, 0x04, 0x01, 0x00, 0x00,
    0x48, 0x8B, 0x44, 0x24, 0x10] ++ bytes_l10731b_2

theorem code_l10731b_1 : ∀ x ∈ codeRange 0x1073a1 bytes_l10731b_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x73a1 149 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10731b_2

@[cfg_block] def b_l10731b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10731b (movR32M32LowEffect 0x10731b 0 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x10731b (LoadPre 0x10731b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10731b + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x10731b 0 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x107322 (movR32M32LowEffect 0x107322 1 (.sib 4 none 0 (.d32 0x8b))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x107322 (LoadPre 0x107322 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x8b)) s (0x107322 + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x107322 1 (.sib 4 none 0 (.d32 0x8b))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x107329 (StorePre 0x107329 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x124)) s (0x107329 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x107329 0 (.sib 4 none 0 (.d32 0x124))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 58) (.exec 0x107330 (StorePre 0x107330 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x127)) s (0x107330 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x107330 1 (.sib 4 none 0 (.d32 0x127))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 59) (.out 0x107337 (movR32M32LowEffect 0x107337 0 (.sib 4 none 0 (.d32 0x8f))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x107337 (LoadPre 0x107337 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x8f)) s (0x107337 + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x107337 0 (.sib 4 none 0 (.d32 0x8f))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x10733e (movzxR32M8Effect 0x10733e 8 1 (.sib 4 none 0 (.d32 0x93))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 62) (.exec 0x10733e (LoadPre 0x10733e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x93)) s (0x10733e + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x10733e 8 1 (.sib 4 none 0 (.d32 0x93))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x107346 (movR32M32LowEffect 0x107346 2 (.sib 4 none 0 (.d32 0x94))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 64) (.exec 0x107346 (LoadPre 0x107346 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x94)) s (0x107346 + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x107346 2 (.sib 4 none 0 (.d32 0x94))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.exec 0x10734d (StorePre 0x10734d 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x10734d + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x10734d 2 (.sib 4 none 0 (.d32 0x130))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[63, 4]
    (.letOp (n := 66) (.out 0x107354 (movR32M32LowEffect 0x107354 2 (.sib 4 none 0 (.d32 0x97))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 67) (.exec 0x107354 (LoadPre 0x107354 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x97)) s (0x107354 + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x107354 2 (.sib 4 none 0 (.d32 0x97))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.exec 0x10735b (StorePre 0x10735b 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x133)) s (0x10735b + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x10735b 2 (.sib 4 none 0 (.d32 0x133))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[66, 4]
    (.letOp (n := 69) (.out 0x107362 (movR32M32LowEffect 0x107362 2 (.sib 4 none 0 (.d32 0xbb))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 70) (.exec 0x107362 (LoadPre 0x107362 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xbb)) s (0x107362 + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x107362 2 (.sib 4 none 0 (.d32 0xbb))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.exec 0x107369 (StorePre 0x107369 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x107369 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x107369 2 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[69, 4]
    (.letOp (n := 72) (.out 0x10736d (movR64M64Effect 0x10736d 6 (.sib 4 none 0 (.d32 0xb3))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 73) (.exec 0x10736d (LoadPre 0x10736d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb3)) s (0x10736d + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10736d 6 (.sib 4 none 0 (.d32 0xb3))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.exec 0x107375 (StorePre 0x107375 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x107375 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107375 6 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[72, 4]
    (.letOp (n := 75) (.out 0x10737a (movR64M64Effect 0x10737a 7 (.sib 4 none 0 (.d32 0xab))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 76) (.exec 0x10737a (LoadPre 0x10737a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xab)) s (0x10737a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10737a 7 (.sib 4 none 0 (.d32 0xab))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 77) (.exec 0x107382 (StorePre 0x107382 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x107382 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107382 7 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[75, 4]
    (.letOp (n := 78) (.out 0x107387 (movR64M64Effect 0x107387 8 (.sib 4 none 0 (.d32 0xa3))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 79) (.exec 0x107387 (LoadPre 0x107387 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa3)) s (0x107387 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107387 8 (.sib 4 none 0 (.d32 0xa3))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 80) (.exec 0x10738f (StorePre 0x10738f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10738f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10738f 8 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[78, 4]
    (.letOp (n := 81) (.out 0x107394 (movR64M64Effect 0x107394 9 (.sib 4 none 0 (.d32 0x9b))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 82) (.exec 0x107394 (LoadPre 0x107394 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9b)) s (0x107394 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107394 9 (.sib 4 none 0 (.d32 0x9b))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 83) (.exec 0x10739c (StorePre 0x10739c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10739c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10739c 9 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[81, 4]
    (b_l10731b_1)))))))))))))))))))))))))))))))

def bytes_l10731b : List UInt8 :=
  [0x8B, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, 0x8B, 0x8C, 0x24, 0x8B, 0x00, 0x00, 0x00, 0x89, 0x84,
    0x24, 0x24, 0x01, 0x00, 0x00, 0x89, 0x8C, 0x24, 0x27, 0x01, 0x00, 0x00, 0x8B, 0x84, 0x24, 0x8F,
    0x00, 0x00, 0x00, 0x0F, 0xB6, 0x8C, 0x24, 0x93, 0x00, 0x00, 0x00, 0x8B, 0x94, 0x24, 0x94, 0x00,
    0x00, 0x00, 0x89, 0x94, 0x24, 0x30, 0x01, 0x00, 0x00, 0x8B, 0x94, 0x24, 0x97, 0x00, 0x00, 0x00,
    0x89, 0x94, 0x24, 0x33, 0x01, 0x00, 0x00, 0x8B, 0x94, 0x24, 0xBB, 0x00, 0x00, 0x00, 0x89, 0x54,
    0x24, 0x50, 0x48, 0x8B, 0xB4, 0x24, 0xB3, 0x00, 0x00, 0x00, 0x48, 0x89, 0x74, 0x24, 0x48, 0x48,
    0x8B, 0xBC, 0x24, 0xAB, 0x00, 0x00, 0x00, 0x48, 0x89, 0x7C, 0x24, 0x40, 0x4C, 0x8B, 0x84, 0x24,
    0xA3, 0x00, 0x00, 0x00, 0x4C, 0x89, 0x44, 0x24, 0x38, 0x4C, 0x8B, 0x8C, 0x24, 0x9B, 0x00, 0x00,
    0x00, 0x4C, 0x89, 0x4C, 0x24, 0x30] ++ bytes_l10731b_1

theorem code_l10731b : ∀ x ∈ codeRange 0x10731b bytes_l10731b, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x731b 134 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10731b_1

@[cfg_block] def b_l10747b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10747b (leaR64Effect 0x10747b 7 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x10747b (fun s => s.RIP = 0x10747b) (leaR64Effect 0x10747b 7 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x107480 (movR64R64Effect 0x107480 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 56) (.exec 0x107480 (fun s => s.RIP = 0x107480) (movR64R64Effect 0x107480 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x107483 (callEffect (fun _ => 0x10fe50) 0x107488) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x107483 (PushPre 0x107483 5) (callEffect (fun _ => 0x10fe50) 0x107488) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x107488⟩) #v[]
    (.terminate (.call ⟨.l10fe50, RegMap.args [(3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ { target := .l107488, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l10747b : List UInt8 :=
  [0x48, 0x8D, 0x7C, 0x24, 0x30, 0x4C, 0x89, 0xF6, 0xE8, 0xC8, 0x89, 0x00, 0x00]

theorem code_l10747b : ∀ x ∈ codeRange 0x10747b bytes_l10747b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x747b 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l107488 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x107488 (movzxR32M8Effect 0x107488 9 14 (.sib 4 none 0 (.d32 0x124))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 54) (.exec 0x107488 (LoadPre 0x107488 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x124)) s (0x107488 + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x107488 9 14 (.sib 4 none 0 (.d32 0x124))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x107491 (leaR32Effect 0x107491 4 0 (.base 14 (.d8 0xfe))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x107491 (fun s => s.RIP = 0x107491) (leaR32Effect 0x107491 4 0 (.base 14 (.d8 0xfe))) (Reg.operands [.gpr 14] [])) #v[53]
    (.letOp (n := 57) (.out 0x107495 (cmpR32Imm8Effect 0x107495 3 0 0x4) (EffectPart.reads (.flag .CF) [.gpr 0] []) (.flag .CF)) #v[55]
    (.letOp (n := 58) (.exec 0x107495 (fun s => s.RIP = 0x107495) (cmpR32Imm8Effect 0x107495 3 0 0x4) (Reg.operands [.gpr 0] [])) #v[55]
    (.letOp (n := 59) (.pure (condOp 2)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l10749f, RegMap.args [(0, 55), (2, 2), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (16, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l10749a, RegMap.args [(0, 55), (2, 2), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (16, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l107488 : List UInt8 :=
  [0x44, 0x0F, 0xB6, 0xB4, 0x24, 0x24, 0x01, 0x00, 0x00, 0x41, 0x8D, 0x46, 0xFE, 0x83, 0xF8, 0x04,
    0x72, 0x05]

theorem code_l107488 : ∀ x ∈ codeRange 0x107488 bytes_l107488, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x7488 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10749a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10749a (testR32R32Effect 0x10749a 3 14 14) (EffectPart.reads (.flag .ZF) [.gpr 14, .gpr 14] []) (.flag .ZF)) #v[14, 14]
    (.letOp (n := 54) (.exec 0x10749a (fun s => s.RIP = 0x10749a) (testR32R32Effect 0x10749a 3 14 14) (Reg.operands [.gpr 14, .gpr 14] [])) #v[14, 14]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l1074e9, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l10749f, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l10749a : List UInt8 :=
  [0x45, 0x85, 0xF6, 0x75, 0x4A]

theorem code_l10749a : ∀ x ∈ codeRange 0x10749a bytes_l10749a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x749a 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10749f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10749f (movR32R32Effect 0x10749f 3 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[14]
    (.letOp (n := 54) (.exec 0x10749f (fun s => s.RIP = 0x10749f) (movR32R32Effect 0x10749f 3 0 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 55) (.out 0x1074a2 (andAlImm8Effect 0x1074a2 0xfe) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x1074a2 (fun s => s.RIP = 0x1074a2) (andAlImm8Effect 0x1074a2 0xfe) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x1074a4 (xorR32R32Effect 0x1074a4 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[2, 2]
    (.letOp (n := 58) (.exec 0x1074a4 (fun s => s.RIP = 0x1074a4) (xorR32R32Effect 0x1074a4 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 59) (.out 0x1074a6 (cmpAlImm8Effect 0x1074a6 0x2) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[55]
    (.letOp (n := 60) (.exec 0x1074a6 (fun s => s.RIP = 0x1074a6) (cmpAlImm8Effect 0x1074a6 0x2) (Reg.operands [.gpr 0] [])) #v[55]
    (.letOp (n := 61) (.out 0x1074a8 (atFlags (condHolds 4) (setccR8Effect 0x1074a8 3 2)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 2))) #v[57, 59]
    (.letOp (n := 62) (.exec 0x1074a8 (fun s => s.RIP = 0x1074a8) (atFlags (condHolds 4) (setccR8Effect 0x1074a8 3 2)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[57, 59]
    (.letOp (n := 63) (.out 0x1074ab (leaR64Effect 0x1074ab 7 (.sib 4 none 0 (.d32 0x190))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 64) (.exec 0x1074ab (fun s => s.RIP = 0x1074ab) (leaR64Effect 0x1074ab 7 (.sib 4 none 0 (.d32 0x190))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x1074b3 (leaR64Effect 0x1074b3 6 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 66) (.exec 0x1074b3 (fun s => s.RIP = 0x1074b3) (leaR64Effect 0x1074b3 6 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x1074b8 (callEffect (fun _ => 0x1215e0) 0x1074bd) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 68) (.exec 0x1074b8 (PushPre 0x1074b8 5) (callEffect (fun _ => 0x1215e0) 0x1074bd) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.const ⟨64, 0x1074bd⟩) #v[]
    (.terminate (.call ⟨.l1215e0, RegMap.args [(0, 55), (2, 61), (3, 3), (4, 67), (5, 5), (6, 65), (7, 63), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 70⟩ { target := .l1074bd, kept := #v[], arity := rfl, guard := some (Fin.last 69) }))))))))))))))))))

def bytes_l10749f : List UInt8 :=
  [0x44, 0x89, 0xF0, 0x24, 0xFE, 0x31, 0xD2, 0x3C, 0x02, 0x0F, 0x94, 0xC2, 0x48, 0x8D, 0xBC, 0x24,
    0x90, 0x01, 0x00, 0x00, 0x48, 0x8D, 0x74, 0x24, 0x30, 0xE8, 0x23, 0xA1, 0x01, 0x00]

theorem code_l10749f : ∀ x ∈ codeRange 0x10749f bytes_l10749f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x749f 30 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1074bd : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1074bd (cmpR8Imm8Effect 0x1074bd 4 14 0x6) (EffectPart.reads (.flag .CF) [.gpr 14] []) (.flag .CF)) #v[14]
    (.letOp (n := 54) (.exec 0x1074bd (fun s => s.RIP = 0x1074bd) (cmpR8Imm8Effect 0x1074bd 4 14 0x6) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 55) (.out 0x1074c1 (atFlags (condHolds 2) (setccR8Effect 0x1074c1 3 2)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[2, 53]
    (.letOp (n := 56) (.exec 0x1074c1 (fun s => s.RIP = 0x1074c1) (atFlags (condHolds 2) (setccR8Effect 0x1074c1 3 2)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2, 53]
    (.letOp (n := 57) (.out 0x1074c4 (movR8Imm8Effect 0x1074c4 2 0 0x3d) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 58) (.exec 0x1074c4 (fun s => s.RIP = 0x1074c4) (movR8Imm8Effect 0x1074c4 2 0 0x3d) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 59) (.out 0x1074c6 (movR8Imm8Effect 0x1074c6 3 6 0x3d) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[6]
    (.letOp (n := 60) (.exec 0x1074c6 (fun s => s.RIP = 0x1074c6) (movR8Imm8Effect 0x1074c6 3 6 0x3d) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 61) (.out 0x1074c9 (movR32R32Effect 0x1074c9 3 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[14]
    (.letOp (n := 62) (.exec 0x1074c9 (fun s => s.RIP = 0x1074c9) (movR32R32Effect 0x1074c9 3 1 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 63) (.out 0x1074cc (shrR8ClEffect 0x1074cc 3 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[59, 61]
    (.letOp (n := 64) (.exec 0x1074cc (fun s => s.RIP = 0x1074cc) (shrR8ClEffect 0x1074cc 3 6) (Reg.operands [.gpr 6, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[59, 61]
    (.letOp (n := 65) (.out 0x1074cf (testR8R8Effect 0x1074cf 3 2 6) (EffectPart.reads (.flag .ZF) [.gpr 2, .gpr 6] []) (.flag .ZF)) #v[55, 63]
    (.letOp (n := 66) (.exec 0x1074cf (fun s => s.RIP = 0x1074cf) (testR8R8Effect 0x1074cf 3 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[55, 63]
    (.letOp (n := 67) (.pure (condOp 4)) #v[65]
    (.terminate (.condBr (Fin.last 67) ⟨.l1074e9, RegMap.args [(0, 57), (1, 61), (2, 55), (3, 3), (4, 4), (5, 5), (6, 63), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 65), (22, 22), (39, 39), (50, 50), (51, 51)] 68⟩ ⟨.l1074d4, RegMap.args [(0, 57), (1, 61), (2, 55), (3, 3), (4, 4), (5, 5), (6, 63), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 65), (22, 22), (39, 39), (50, 50), (51, 51)] 68⟩))))))))))))))))

def bytes_l1074bd : List UInt8 :=
  [0x41, 0x80, 0xFE, 0x06, 0x0F, 0x92, 0xC2, 0xB0, 0x3D, 0x40, 0xB6, 0x3D, 0x44, 0x89, 0xF1, 0x40,
    0xD2, 0xEE, 0x40, 0x84, 0xF2, 0x74, 0x15]

theorem code_l1074bd : ∀ x ∈ codeRange 0x1074bd bytes_l1074bd, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x74bd 23 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1074d4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1074d4 (movzxR32M8Effect 0x1074d4 8 1 (.sib 4 none 0 (.d32 0x190))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x1074d4 (LoadPre 0x1074d4 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x190)) s (0x1074d4 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1074d4 8 1 (.sib 4 none 0 (.d32 0x190))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1074dc (cmpR64Imm8Effect 0x1074dc 1 0x6) (EffectPart.reads (.flag .CF) [.gpr 1] []) (.flag .CF)) #v[53]
    (.letOp (n := 56) (.exec 0x1074dc (fun s => s.RIP = 0x1074dc) (cmpR64Imm8Effect 0x1074dc 1 0x6) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 57) (.out 0x1074e0 (atFlags (condHolds 2) (setccR8Effect 0x1074e0 3 2)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[2, 55]
    (.letOp (n := 58) (.exec 0x1074e0 (fun s => s.RIP = 0x1074e0) (atFlags (condHolds 2) (setccR8Effect 0x1074e0 3 2)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2, 55]
    (.letOp (n := 59) (.out 0x1074e3 (shrR8ClEffect 0x1074e3 2 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[0, 53]
    (.letOp (n := 60) (.exec 0x1074e3 (fun s => s.RIP = 0x1074e3) (shrR8ClEffect 0x1074e3 2 0) (Reg.operands [.gpr 0, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[0, 53]
    (.letOp (n := 61) (.out 0x1074e5 (testR8R8Effect 0x1074e5 2 2 0) (EffectPart.reads (.flag .ZF) [.gpr 2, .gpr 0] []) (.flag .ZF)) #v[57, 59]
    (.letOp (n := 62) (.exec 0x1074e5 (fun s => s.RIP = 0x1074e5) (testR8R8Effect 0x1074e5 2 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[57, 59]
    (.letOp (n := 63) (.pure (condOp 5)) #v[61]
    (.terminate (.condBr (Fin.last 63) ⟨.l10753c, RegMap.args [(0, 59), (1, 53), (2, 57), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 61), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ ⟨.l1074e9, RegMap.args [(0, 59), (1, 53), (2, 57), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 61), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩))))))))))))

def bytes_l1074d4 : List UInt8 :=
  [0x0F, 0xB6, 0x8C, 0x24, 0x90, 0x01, 0x00, 0x00, 0x48, 0x83, 0xF9, 0x06, 0x0F, 0x92, 0xC2, 0xD2,
    0xE8, 0x84, 0xC2, 0x75, 0x53]

theorem code_l1074d4 : ∀ x ∈ codeRange 0x1074d4 bytes_l1074d4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x74d4 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1074e9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1074e9 (StorePre 0x1074e9 11 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1074e9 + BitVec.ofNat 64 11)) 4) (movM32Imm32Effect 0x1074e9 11 (.sib 4 none 0 (.d32 0x88)) 0x3) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.out 0x1074f4 (leaR64Effect 0x1074f4 2 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 55) (.exec 0x1074f4 (fun s => s.RIP = 0x1074f4) (leaR64Effect 0x1074f4 2 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x1074fc (movR32Imm32Effect 0x1074fc 5 6 0xb) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 57) (.exec 0x1074fc (fun s => s.RIP = 0x1074fc) (movR32Imm32Effect 0x1074fc 5 6 0xb) (Reg.operands [] [])) #v[]
    (.letOp (n := 58) (.out 0x107501 (movR64Imm32Effect 0x107501 7 0x202800) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 59) (.exec 0x107501 (fun s => s.RIP = 0x107501) (movR64Imm32Effect 0x107501 7 0x202800) (Reg.operands [] [])) #v[]
    (.letOp (n := 60) (.out 0x107508 (movR64Imm32Effect 0x107508 1 0x2027e0) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 61) (.exec 0x107508 (fun s => s.RIP = 0x107508) (movR64Imm32Effect 0x107508 1 0x2027e0) (Reg.operands [] [])) #v[]
    (.letOp (n := 62) (.out 0x10750f (movR64Imm32Effect 0x10750f 8 0x202810) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 63) (.exec 0x10750f (fun s => s.RIP = 0x10750f) (movR64Imm32Effect 0x10750f 8 0x202810) (Reg.operands [] [])) #v[]
    (.letOp (n := 64) (.out 0x107516 (callEffect (fun _ => 0x1295a0) 0x10751b) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 65) (.exec 0x107516 (PushPre 0x107516 5) (callEffect (fun _ => 0x1295a0) 0x10751b) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.const ⟨64, 0x10751b⟩) #v[]
    (.terminate (.call ⟨.l1295a0, RegMap.args [(1, 60), (2, 54), (4, 64), (5, 5), (6, 56), (7, 58), (8, 62)] 67⟩ { target := .l10751b, kept := #v[], arity := rfl, guard := some (Fin.last 66) })))))))))))))))

def bytes_l1074e9 : List UInt8 :=
  [0xC7, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, 0x03, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x94, 0x24, 0x88,
    0x00, 0x00, 0x00, 0xBE, 0x0B, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC7, 0x00, 0x28, 0x20, 0x00, 0x48,
    0xC7, 0xC1, 0xE0, 0x27, 0x20, 0x00, 0x49, 0xC7, 0xC0, 0x10, 0x28, 0x20, 0x00, 0xE8, 0x85, 0x20,
    0x02, 0x00]

theorem code_l1074e9 : ∀ x ∈ codeRange 0x1074e9 bytes_l1074e9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x74e9 50 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10751b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x10751b (StorePre 0x10751b 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10751b + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x10751b (.sib 4 none 0 (.d32 0x88)) 0x1) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.out 0x107527 (cmpM8Imm8Effect 0x107527 8 (.sib 4 none 0 (.d32 0x88)) 0x0) (EffectPart.reads (.flag .ZF) [.gpr 4] []) (.flag .ZF)) #v[4]
    (.letOp (n := 55) (.exec 0x107527 (LoadPre 0x107527 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x107527 + BitVec.ofNat 64 8)) 1) (cmpM8Imm8Effect 0x107527 8 (.sib 4 none 0 (.d32 0x88)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.pure (condOp 4)) #v[54]
    (.terminate (.condBr (Fin.last 56) ⟨.l10724d, RegMap.args [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩ ⟨.l107535, RegMap.args [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l10751b : List UInt8 :=
  [0x48, 0xC7, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x80, 0xBC, 0x24, 0x88,
    0x00, 0x00, 0x00, 0x00, 0x0F, 0x84, 0x18, 0xFD, 0xFF, 0xFF]

theorem code_l10751b : ∀ x ∈ codeRange 0x10751b bytes_l10751b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x751b 26 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l107535 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x107535 (movR8Imm8Effect 0x107535 2 0 0x3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 54) (.exec 0x107535 (fun s => s.RIP = 0x107535) (movR8Imm8Effect 0x107535 2 0 0x3) (Reg.operands [.gpr 0] [])) #v[0]
    (.terminate (.br ⟨.l107623, RegMap.args [(0, 53), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l107535 : List UInt8 :=
  [0xB0, 0x03, 0xE9, 0xE7, 0x00, 0x00, 0x00]

theorem code_l107535 : ∀ x ∈ codeRange 0x107535 bytes_l107535, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x7535 7 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10753c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10753c (movR64M64Effect 0x10753c 2 (.abs (some 14) 3 0x202ad8)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14] []) (.reg (.gpr 2))) #v[14]
    (.letOp (n := 54) (.exec 0x10753c (LoadPre 0x10753c (fun s => AddrMode.addr (.abs (some 14) 3 0x202ad8) s (0x10753c + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10753c 2 (.abs (some 14) 3 0x202ad8)) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 55) (.out 0x107544 (cmpR64M64Effect 0x107544 2 (.abs (some 1) 3 0x202ad8)) (EffectPart.reads (.flag .ZF) [.gpr 2, .gpr 1] []) (.flag .ZF)) #v[53, 1]
    (.letOp (n := 56) (.exec 0x107544 (LoadPre 0x107544 (fun s => AddrMode.addr (.abs (some 1) 3 0x202ad8) s (0x107544 + BitVec.ofNat 64 8)) 8) (cmpR64M64Effect 0x107544 2 (.abs (some 1) 3 0x202ad8)) (Reg.operands [.gpr 2, .gpr 1] [])) #v[53, 1]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l10756c, RegMap.args [(1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l10754e, RegMap.args [(1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l10753c : List UInt8 :=
  [0x4A, 0x8B, 0x14, 0xF5, 0xD8, 0x2A, 0x20, 0x00, 0x48, 0x3B, 0x14, 0xCD, 0xD8, 0x2A, 0x20, 0x00,
    0x75, 0x1E]

theorem code_l10753c : ∀ x ∈ codeRange 0x10753c bytes_l10753c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x753c 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10754e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10754e (leaR64Effect 0x10754e 7 (.sib 4 none 0 (.d32 0x124))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x10754e (fun s => s.RIP = 0x10754e) (leaR64Effect 0x10754e 7 (.sib 4 none 0 (.d32 0x124))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x107556 (leaR64Effect 0x107556 6 (.sib 4 none 0 (.d32 0x190))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 56) (.exec 0x107556 (fun s => s.RIP = 0x107556) (leaR64Effect 0x107556 6 (.sib 4 none 0 (.d32 0x190))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x10755e (callEffect (callMemPtr 0x10755e (.rip 0xfc89c)) (0x10755e + BitVec.ofNat 64 (callMemLen (.rip 0xfc89c)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x10755e (GoesTo (CallMemPre 0x10755e (.rip 0xfc89c)) (callEffect (callMemPtr 0x10755e (.rip 0xfc89c)) (0x10755e + BitVec.ofNat 64 (callMemLen (.rip 0xfc89c)))) 0x12a750) (callEffect (callMemPtr 0x10755e (.rip 0xfc89c)) (0x10755e + BitVec.ofNat 64 (callMemLen (.rip 0xfc89c)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x107564⟩) #v[]
    (.terminate (.call ⟨.l12a750, RegMap.args [(2, 2), (3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ { target := .l107564, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l10754e : List UInt8 :=
  [0x48, 0x8D, 0xBC, 0x24, 0x24, 0x01, 0x00, 0x00, 0x48, 0x8D, 0xB4, 0x24, 0x90, 0x01, 0x00, 0x00,
    0xFF, 0x15, 0x9C, 0xC8, 0x0F, 0x00]

theorem code_l10754e : ∀ x ∈ codeRange 0x10754e bytes_l10754e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x754e 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l107564 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x107564 (testR32R32Effect 0x107564 2 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[0, 0]
    (.letOp (n := 54) (.exec 0x107564 (fun s => s.RIP = 0x107564) (testR32R32Effect 0x107564 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l1076a0, RegMap.args [(0, 0), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l10756c, RegMap.args [(0, 0), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l107564 : List UInt8 :=
  [0x85, 0xC0, 0x0F, 0x84, 0x34, 0x01, 0x00, 0x00]

theorem code_l107564 : ∀ x ∈ codeRange 0x107564 bytes_l107564, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x7564 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10756c_1 : Block Op Label signature Reg.count 79 :=
  .letOp (n := 79) (.out 0x1075fa (movR64M64Effect 0x1075fa 0 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 80) (.exec 0x1075fa (LoadPre 0x1075fa (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x1075fa + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1075fa 0 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 81) (.exec 0x107602 (StorePre 0x107602 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x107602 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107602 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[79, 4]
    (.letOp (n := 82) (.out 0x107607 (movR64M64Effect 0x107607 0 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 83) (.exec 0x107607 (LoadPre 0x107607 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x107607 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107607 0 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 84) (.exec 0x10760f (StorePre 0x10760f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10760f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10760f 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[82, 4]
    (.letOp (n := 85) (.out 0x107614 (movR64M64Effect 0x107614 0 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 86) (.exec 0x107614 (LoadPre 0x107614 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x107614 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107614 0 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 87) (.exec 0x10761c (StorePre 0x10761c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10761c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10761c 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[85, 4]
    (.letOp (n := 88) (.out 0x107621 (movR8Imm8Effect 0x107621 2 0 0x2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[85]
    (.letOp (n := 89) (.exec 0x107621 (fun s => s.RIP = 0x107621) (movR8Imm8Effect 0x107621 2 0 0x2) (Reg.operands [.gpr 0] [])) #v[85]
    (.terminate (.br ⟨.l107623, RegMap.args [(0, 88), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 90⟩))))))))))))

def bytes_l10756c_1 : List UInt8 :=
  [0x48, 0x8B, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x84,
    0x24, 0x90, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x84, 0x24, 0x88, 0x00,
    0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x10, 0xB0, 0x02]

theorem code_l10756c_1 : ∀ x ∈ codeRange 0x1075fa bytes_l10756c_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x75fa 41 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10756c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x10756c (StorePre 0x10756c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x190)) s (0x10756c + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x10756c (.sib 4 none 0 (.d32 0x190)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.exec 0x107574 (StorePre 0x107574 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x32)) s (0x107574 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x107574 (.sib 4 none 0 (.d8 0x32)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x107579 (StorePre 0x107579 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x107579 + BitVec.ofNat 64 7)) 2) (movM16Imm16Effect 0x107579 (.sib 4 none 0 (.d8 0x30)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.exec 0x107580 (StorePre 0x107580 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x124)) s (0x107580 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x107580 (.sib 4 none 0 (.d32 0x124)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x107588 (StorePre 0x107588 11 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9f)) s (0x107588 + BitVec.ofNat 64 11)) 4) (movM32Imm32Effect 0x107588 11 (.sib 4 none 0 (.d32 0x9f)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x107593 (StorePre 0x107593 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x107593 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x107593 (.sib 4 none 0 (.d32 0x98)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.exec 0x10759f (StorePre 0x10759f 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x10759f + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x10759f (.sib 4 none 0 (.d32 0x90)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.exec 0x1075ab (StorePre 0x1075ab 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1075ab + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1075ab (.sib 4 none 0 (.d32 0x88)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x1075b7 (movzxR32M8Effect 0x1075b7 8 0 (.sib 4 none 0 (.d32 0x190))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 62) (.exec 0x1075b7 (LoadPre 0x1075b7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x190)) s (0x1075b7 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1075b7 8 0 (.sib 4 none 0 (.d32 0x190))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x1075bf (StorePre 0x1075bf 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1075bf + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1075bf 4 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.out 0x1075c3 (movzxR32M8Effect 0x1075c3 5 0 (.sib 4 none 0 (.d8 0x32))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 65) (.exec 0x1075c3 (LoadPre 0x1075c3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x32)) s (0x1075c3 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1075c3 5 0 (.sib 4 none 0 (.d8 0x32))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x1075c8 (StorePre 0x1075c8 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2)) s (0x1075c8 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1075c8 4 0 (.sib 4 none 0 (.d8 0x2))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.out 0x1075cc (movzxR32M16Effect 0x1075cc 5 0 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 68) (.exec 0x1075cc (LoadPre 0x1075cc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1075cc + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x1075cc 5 0 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.exec 0x1075d1 (StorePre 0x1075d1 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1075d1 + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x1075d1 4 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[67, 4]
    (.letOp (n := 70) (.out 0x1075d5 (movzxR32M8Effect 0x1075d5 8 0 (.sib 4 none 0 (.d32 0x124))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 71) (.exec 0x1075d5 (LoadPre 0x1075d5 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x124)) s (0x1075d5 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1075d5 8 0 (.sib 4 none 0 (.d32 0x124))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.exec 0x1075dd (StorePre 0x1075dd 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x1075dd + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1075dd 4 0 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[70, 4]
    (.letOp (n := 73) (.out 0x1075e1 (movzxR32M8Effect 0x1075e1 8 0 (.sib 4 none 0 (.d32 0xa2))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 74) (.exec 0x1075e1 (LoadPre 0x1075e1 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa2)) s (0x1075e1 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1075e1 8 0 (.sib 4 none 0 (.d32 0xa2))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.exec 0x1075e9 (StorePre 0x1075e9 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2a)) s (0x1075e9 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1075e9 4 0 (.sib 4 none 0 (.d8 0x2a))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[73, 4]
    (.letOp (n := 76) (.out 0x1075ed (movzxR32M16Effect 0x1075ed 8 0 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 77) (.exec 0x1075ed (LoadPre 0x1075ed (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x1075ed + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x1075ed 8 0 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 78) (.exec 0x1075f5 (StorePre 0x1075f5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1075f5 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1075f5 5 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[76, 4]
    (b_l10756c_1))))))))))))))))))))))))))

def bytes_l10756c : List UInt8 :=
  [0xC6, 0x84, 0x24, 0x90, 0x01, 0x00, 0x00, 0x00, 0xC6, 0x44, 0x24, 0x32, 0x00, 0x66, 0xC7, 0x44,
    0x24, 0x30, 0x00, 0x00, 0xC6, 0x84, 0x24, 0x24, 0x01, 0x00, 0x00, 0x00, 0xC7, 0x84, 0x24, 0x9F,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48,
    0xC7, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x0F, 0xB6, 0x84, 0x24, 0x90,
    0x01, 0x00, 0x00, 0x88, 0x44, 0x24, 0x08, 0x0F, 0xB6, 0x44, 0x24, 0x32, 0x88, 0x44, 0x24, 0x02,
    0x0F, 0xB7, 0x44, 0x24, 0x30, 0x66, 0x89, 0x04, 0x24, 0x0F, 0xB6, 0x84, 0x24, 0x24, 0x01, 0x00,
    0x00, 0x88, 0x44, 0x24, 0x0C, 0x0F, 0xB6, 0x84, 0x24, 0xA2, 0x00, 0x00, 0x00, 0x88, 0x44, 0x24,
    0x2A, 0x0F, 0xB7, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x66, 0x89, 0x44, 0x24, 0x28] ++ bytes_l10756c_1

theorem code_l10756c : ∀ x ∈ codeRange 0x10756c bytes_l10756c, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x756c 142 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10756c_1

@[cfg_block] def b_l107623 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x107623 (movzxR32M8Effect 0x107623 5 1 (.sib 4 none 0 (.d8 0x6))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x107623 (LoadPre 0x107623 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6)) s (0x107623 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x107623 5 1 (.sib 4 none 0 (.d8 0x6))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x107628 (StorePre 0x107628 3 (fun s => AddrMode.addr (.base 3 (.d8 0x13)) s (0x107628 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x107628 3 1 (.base 3 (.d8 0x13))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[53, 3]
    (.letOp (n := 56) (.out 0x10762b (movzxR32M16Effect 0x10762b 5 1 (.sib 4 none 0 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 57) (.exec 0x10762b (LoadPre 0x10762b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x10762b + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x10762b 5 1 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x107630 (StorePre 0x107630 4 (fun s => AddrMode.addr (.base 3 (.d8 0x11)) s (0x107630 + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x107630 4 1 (.base 3 (.d8 0x11))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[56, 3]
    (.letOp (n := 59) (.out 0x107634 (movR64M64Effect 0x107634 1 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 60) (.exec 0x107634 (LoadPre 0x107634 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x107634 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107634 1 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x10763c (movR64M64Effect 0x10763c 2 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 62) (.exec 0x10763c (LoadPre 0x10763c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x10763c + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10763c 2 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x107644 (StorePre 0x107644 4 (fun s => AddrMode.addr (.base 3 (.d8 0x15)) s (0x107644 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x107644 1 (.base 3 (.d8 0x15))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[59, 3]
    (.letOp (n := 64) (.exec 0x107648 (StorePre 0x107648 4 (fun s => AddrMode.addr (.base 3 (.d8 0x1d)) s (0x107648 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x107648 2 (.base 3 (.d8 0x1d))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x10764c (movR64M64Effect 0x10764c 1 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 66) (.exec 0x10764c (LoadPre 0x10764c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x10764c + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10764c 1 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x107654 (StorePre 0x107654 4 (fun s => AddrMode.addr (.base 3 (.d8 0x25)) s (0x107654 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x107654 1 (.base 3 (.d8 0x25))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[65, 3]
    (.letOp (n := 68) (.out 0x107658 (movR64M64Effect 0x107658 1 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 69) (.exec 0x107658 (LoadPre 0x107658 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x107658 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107658 1 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.exec 0x107660 (StorePre 0x107660 4 (fun s => AddrMode.addr (.base 3 (.d8 0x2d)) s (0x107660 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x107660 1 (.base 3 (.d8 0x2d))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[68, 3]
    (.letOp (n := 71) (.out 0x107664 (movR64M64Effect 0x107664 1 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 72) (.exec 0x107664 (LoadPre 0x107664 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x107664 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107664 1 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.exec 0x10766c (StorePre 0x10766c 4 (fun s => AddrMode.addr (.base 3 (.d8 0x35)) s (0x10766c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10766c 1 (.base 3 (.d8 0x35))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[71, 3]
    (.letOp (n := 74) (.out 0x107670 (movR32M32LowEffect 0x107670 1 (.sib 4 none 0 (.d32 0xaf))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 75) (.exec 0x107670 (LoadPre 0x107670 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xaf)) s (0x107670 + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x107670 1 (.sib 4 none 0 (.d32 0xaf))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 76) (.exec 0x107677 (StorePre 0x107677 3 (fun s => AddrMode.addr (.base 3 (.d8 0x3c)) s (0x107677 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x107677 1 (.base 3 (.d8 0x3c))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[74, 3]
    (.letOp (n := 77) (.exec 0x10767a (StorePre 0x10767a 3 (fun s => AddrMode.addr (.base 3 .none) s (0x10767a + BitVec.ofNat 64 3)) 1) (movM8Imm8Effect 0x10767a (.base 3 .none) 0xff) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 78) (.exec 0x10767d (StorePre 0x10767d 7 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x10767d + BitVec.ofNat 64 7)) 4) (movM32Imm32Effect 0x10767d 7 (.base 3 (.d8 0x8)) 0x0) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 79) (.exec 0x107684 (StorePre 0x107684 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x107684 + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x107684 (.base 3 (.d8 0x10)) 0x15) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 80) (.exec 0x107688 (StorePre 0x107688 3 (fun s => AddrMode.addr (.base 3 (.d8 0x14)) s (0x107688 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x107688 3 0 (.base 3 (.d8 0x14))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (.terminate (.br ⟨.l10768b, RegMap.args [(0, 0), (1, 74), (2, 61), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 81⟩)))))))))))))))))))))))))))))

def bytes_l107623 : List UInt8 :=
  [0x0F, 0xB6, 0x4C, 0x24, 0x06, 0x88, 0x4B, 0x13, 0x0F, 0xB7, 0x4C, 0x24, 0x04, 0x66, 0x89, 0x4B,
    0x11, 0x48, 0x8B, 0x8C, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x94, 0x24, 0x90, 0x00, 0x00,
    0x00, 0x48, 0x89, 0x4B, 0x15, 0x48, 0x89, 0x53, 0x1D, 0x48, 0x8B, 0x8C, 0x24, 0x98, 0x00, 0x00,
    0x00, 0x48, 0x89, 0x4B, 0x25, 0x48, 0x8B, 0x8C, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x4B,
    0x2D, 0x48, 0x8B, 0x8C, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x4B, 0x35, 0x8B, 0x8C, 0x24,
    0xAF, 0x00, 0x00, 0x00, 0x89, 0x4B, 0x3C, 0xC6, 0x03, 0xFF, 0xC7, 0x43, 0x08, 0x00, 0x00, 0x00,
    0x00, 0xC6, 0x43, 0x10, 0x15, 0x88, 0x43, 0x14]

theorem code_l107623 : ∀ x ∈ codeRange 0x107623 bytes_l107623, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x7623 104 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10768b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10768b (movR64R64Effect 0x10768b 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 54) (.exec 0x10768b (fun s => s.RIP = 0x10768b) (movR64R64Effect 0x10768b 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x10768e (addR64Imm32Effect 0x10768e 4 0x1d8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 56) (.exec 0x10768e (fun s => s.RIP = 0x10768e) (addR64Imm32Effect 0x10768e 4 0x1d8) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x107695 (popR64Effect 0x107695 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[55]
    (.letOp (n := 58) (.out 0x107695 (popR64Effect 0x107695 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[55]
    (.letOp (n := 59) (.exec 0x107695 (PopPre 0x107695) (popR64Effect 0x107695 1 3) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 60) (.out 0x107696 (popR64Effect 0x107696 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[58]
    (.letOp (n := 61) (.out 0x107696 (popR64Effect 0x107696 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[58]
    (.letOp (n := 62) (.exec 0x107696 (PopPre 0x107696) (popR64Effect 0x107696 2 12) (Reg.operands [.gpr 4] [])) #v[58]
    (.letOp (n := 63) (.out 0x107698 (popR64Effect 0x107698 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[61]
    (.letOp (n := 64) (.out 0x107698 (popR64Effect 0x107698 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 65) (.exec 0x107698 (PopPre 0x107698) (popR64Effect 0x107698 2 13) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 66) (.out 0x10769a (popR64Effect 0x10769a 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[64]
    (.letOp (n := 67) (.out 0x10769a (popR64Effect 0x10769a 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[64]
    (.letOp (n := 68) (.exec 0x10769a (PopPre 0x10769a) (popR64Effect 0x10769a 2 14) (Reg.operands [.gpr 4] [])) #v[64]
    (.letOp (n := 69) (.out 0x10769c (popR64Effect 0x10769c 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[67]
    (.letOp (n := 70) (.out 0x10769c (popR64Effect 0x10769c 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[67]
    (.letOp (n := 71) (.exec 0x10769c (PopPre 0x10769c) (popR64Effect 0x10769c 2 15) (Reg.operands [.gpr 4] [])) #v[67]
    (.letOp (n := 72) (.out 0x10769e (popR64Effect 0x10769e 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[70]
    (.letOp (n := 73) (.out 0x10769e (popR64Effect 0x10769e 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[70]
    (.letOp (n := 74) (.exec 0x10769e (PopPre 0x10769e) (popR64Effect 0x10769e 1 5) (Reg.operands [.gpr 4] [])) #v[70]
    (.letOp (n := 75) (.out 0x10769f (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[73]
    (.letOp (n := 76) (.out 0x10769f (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[73]
    (.letOp (n := 77) (.exec 0x10769f (RetPre 0x10769f) (retEffect) (Reg.operands [.gpr 4] [])) #v[73]
    (.terminate (.ret (RegMap.args [(0, 53), (1, 1), (2, 2), (3, 57), (4, 76), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 78) (some ⟨75, by decide⟩)))))))))))))))))))))))))))

def bytes_l10768b : List UInt8 :=
  [0x48, 0x89, 0xD8, 0x48, 0x81, 0xC4, 0xD8, 0x01, 0x00, 0x00, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41,
    0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l10768b : ∀ x ∈ codeRange 0x10768b bytes_l10768b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x768b 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1076a0_1 : Block Op Label signature Reg.count 82 :=
  .letOp (n := 82) (.exec 0x10770b (StorePre 0x10770b 4 (fun s => AddrMode.addr (.base 3 (.d8 0x9)) s (0x10770b + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x10770b 4 0 (.base 3 (.d8 0x9))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[80, 3]
    (.letOp (n := 83) (.out 0x10770f (movzxR32M8Effect 0x10770f 5 0 (.sib 4 none 0 (.d8 0x6))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 84) (.exec 0x10770f (LoadPre 0x10770f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6)) s (0x10770f + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10770f 5 0 (.sib 4 none 0 (.d8 0x6))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 85) (.exec 0x107714 (StorePre 0x107714 3 (fun s => AddrMode.addr (.base 3 (.d8 0xb)) s (0x107714 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x107714 3 0 (.base 3 (.d8 0xb))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[83, 3]
    (.letOp (n := 86) (.exec 0x107717 (StorePre 0x107717 4 (fun s => AddrMode.addr (.base 3 (.d8 0xc)) s (0x107717 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x107717 4 12 (.base 3 (.d8 0xc))) (Reg.operands [.gpr 12, .gpr 3] [])) #v[12, 3]
    (.letOp (n := 87) (.exec 0x10771b (StorePre 0x10771b 3 (fun s => AddrMode.addr (.base 3 .none) s (0x10771b + BitVec.ofNat 64 3)) 1) (movM8Imm8Effect 0x10771b (.base 3 .none) 0xfe) (Reg.operands [.gpr 3] [])) #v[3]
    (.terminate (.br ⟨.l10768b, RegMap.args [(0, 83), (1, 67), (2, 74), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)] 88⟩)))))))

def bytes_l1076a0_1 : List UInt8 :=
  [0x66, 0x89, 0x43, 0x09, 0x0F, 0xB6, 0x44, 0x24, 0x06, 0x88, 0x43, 0x0B, 0x44, 0x88, 0x63, 0x0C,
    0xC6, 0x03, 0xFE, 0xE9, 0x68, 0xFF, 0xFF, 0xFF]

theorem code_l1076a0_1 : ∀ x ∈ codeRange 0x10770b bytes_l1076a0_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x770b 24 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1076a0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1076a0 (movzxR32M8Effect 0x1076a0 5 0 (.sib 4 none 0 (.d8 0x2))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1076a0 (LoadPre 0x1076a0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2)) s (0x1076a0 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1076a0 5 0 (.sib 4 none 0 (.d8 0x2))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x1076a5 (StorePre 0x1076a5 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6)) s (0x1076a5 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1076a5 4 0 (.sib 4 none 0 (.d8 0x6))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x1076a9 (movzxR32M16Effect 0x1076a9 4 0 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x1076a9 (LoadPre 0x1076a9 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1076a9 + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x1076a9 4 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x1076ad (StorePre 0x1076ad 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x1076ad + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1076ad 5 0 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x1076b2 (movR32M32LowEffect 0x1076b2 0 (.sib 4 none 0 (.d8 0x27))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x1076b2 (LoadPre 0x1076b2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x27)) s (0x1076b2 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1076b2 0 (.sib 4 none 0 (.d8 0x27))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x1076b6 (StorePre 0x1076b6 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9f)) s (0x1076b6 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x1076b6 0 (.sib 4 none 0 (.d32 0x9f))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x1076bd (movR64M64Effect 0x1076bd 0 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x1076bd (LoadPre 0x1076bd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1076bd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1076bd 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x1076c2 (StorePre 0x1076c2 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x1076c2 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1076c2 0 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x1076ca (movR64M64Effect 0x1076ca 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 66) (.exec 0x1076ca (LoadPre 0x1076ca (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1076ca + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1076ca 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x1076cf (movR64M64Effect 0x1076cf 1 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 68) (.exec 0x1076cf (LoadPre 0x1076cf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1076cf + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1076cf 1 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.exec 0x1076d4 (StorePre 0x1076d4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1076d4 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1076d4 0 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 70) (.exec 0x1076dc (StorePre 0x1076dc 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x1076dc + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1076dc 1 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[67, 4]
    (.letOp (n := 71) (.out 0x1076e4 (movR32M32LowEffect 0x1076e4 2 (.sib 4 none 0 (.d32 0x9f))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 72) (.exec 0x1076e4 (LoadPre 0x1076e4 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9f)) s (0x1076e4 + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x1076e4 2 (.sib 4 none 0 (.d32 0x9f))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.exec 0x1076eb (StorePre 0x1076eb 3 (fun s => AddrMode.addr (.base 3 (.d8 0x24)) s (0x1076eb + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x1076eb 2 (.base 3 (.d8 0x24))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[71, 3]
    (.letOp (n := 74) (.out 0x1076ee (movR64M64Effect 0x1076ee 2 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 75) (.exec 0x1076ee (LoadPre 0x1076ee (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x1076ee + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1076ee 2 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 76) (.exec 0x1076f6 (StorePre 0x1076f6 4 (fun s => AddrMode.addr (.base 3 (.d8 0x1d)) s (0x1076f6 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1076f6 2 (.base 3 (.d8 0x1d))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[74, 3]
    (.letOp (n := 77) (.exec 0x1076fa (StorePre 0x1076fa 4 (fun s => AddrMode.addr (.base 3 (.d8 0x15)) s (0x1076fa + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1076fa 1 (.base 3 (.d8 0x15))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[67, 3]
    (.letOp (n := 78) (.exec 0x1076fe (StorePre 0x1076fe 4 (fun s => AddrMode.addr (.base 3 (.d8 0xd)) s (0x1076fe + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1076fe 0 (.base 3 (.d8 0xd))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[65, 3]
    (.letOp (n := 79) (.exec 0x107702 (StorePre 0x107702 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x107702 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x107702 4 5 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 5, .gpr 3] [])) #v[5, 3]
    (.letOp (n := 80) (.out 0x107706 (movzxR32M16Effect 0x107706 5 0 (.sib 4 none 0 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 81) (.exec 0x107706 (LoadPre 0x107706 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x107706 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x107706 5 0 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l1076a0_1)))))))))))))))))))))))))))))

def bytes_l1076a0 : List UInt8 :=
  [0x0F, 0xB6, 0x44, 0x24, 0x02, 0x88, 0x44, 0x24, 0x06, 0x0F, 0xB7, 0x04, 0x24, 0x66, 0x89, 0x44,
    0x24, 0x04, 0x8B, 0x44, 0x24, 0x27, 0x89, 0x84, 0x24, 0x9F, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x44,
    0x24, 0x20, 0x48, 0x89, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x10, 0x48,
    0x8B, 0x4C, 0x24, 0x18, 0x48, 0x89, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x89, 0x8C, 0x24,
    0x90, 0x00, 0x00, 0x00, 0x8B, 0x94, 0x24, 0x9F, 0x00, 0x00, 0x00, 0x89, 0x53, 0x24, 0x48, 0x8B,
    0x94, 0x24, 0x98, 0x00, 0x00, 0x00, 0x48, 0x89, 0x53, 0x1D, 0x48, 0x89, 0x4B, 0x15, 0x48, 0x89,
    0x43, 0x0D, 0x40, 0x88, 0x6B, 0x08, 0x0F, 0xB7, 0x44, 0x24, 0x04] ++ bytes_l1076a0_1

theorem code_l1076a0 : ∀ x ∈ codeRange 0x1076a0 bytes_l1076a0, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x76a0 107 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1076a0_1

@[cfg_block] def b_l107730 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x107730 (pushR64Effect 0x107730 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x107730 (PushPre 0x107730 1) (pushR64Effect 0x107730 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x107731 (pushR64Effect 0x107731 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x107731 (PushPre 0x107731 2) (pushR64Effect 0x107731 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x107733 (pushR64Effect 0x107733 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x107733 (PushPre 0x107733 2) (pushR64Effect 0x107733 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x107735 (pushR64Effect 0x107735 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x107735 (PushPre 0x107735 2) (pushR64Effect 0x107735 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x107737 (pushR64Effect 0x107737 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x107737 (PushPre 0x107737 2) (pushR64Effect 0x107737 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x107739 (pushR64Effect 0x107739 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x107739 (PushPre 0x107739 1) (pushR64Effect 0x107739 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x10773a (subR64Imm8Effect 0x10773a 4 0x68) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x10773a (fun s => s.RIP = 0x10773a) (subR64Imm8Effect 0x10773a 4 0x68) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x10773e (movR64R64Effect 0x10773e 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 68) (.exec 0x10773e (fun s => s.RIP = 0x10773e) (movR64R64Effect 0x10773e 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 69) (.out 0x107741 (movR32Imm32Effect 0x107741 6 14 0x1) (EffectPart.reads (.reg (.gpr 14)) [] []) (.reg (.gpr 14))) #v[]
    (.letOp (n := 70) (.exec 0x107741 (fun s => s.RIP = 0x107741) (movR32Imm32Effect 0x107741 6 14 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 71) (.out 0x107747 (cmpR64Imm8Effect 0x107747 2 0x20) (EffectPart.reads (.flag .ZF) [.gpr 2] []) (.flag .ZF)) #v[2]
    (.letOp (n := 72) (.exec 0x107747 (fun s => s.RIP = 0x107747) (cmpR64Imm8Effect 0x107747 2 0x20) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 73) (.pure (condOp 5)) #v[71]
    (.terminate (.condBr (Fin.last 73) ⟨.l107897, RegMap.args [(1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 69), (15, 15), (19, 71), (22, 22), (39, 39), (50, 50), (51, 51)] 74⟩ ⟨.l107751, RegMap.args [(1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 69), (15, 15), (19, 71), (22, 22), (39, 39), (50, 50), (51, 51)] 74⟩))))))))))))))))))))))

def bytes_l107730 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x83, 0xEC, 0x68, 0x48, 0x89,
    0xFB, 0x41, 0xBE, 0x01, 0x00, 0x00, 0x00, 0x48, 0x83, 0xFA, 0x20, 0x0F, 0x85, 0x46, 0x01, 0x00,
    0x00]

theorem code_l107730 : ∀ x ∈ codeRange 0x107730 bytes_l107730, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x7730 33 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l107751 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x107751 (movR64M64Effect 0x107751 0 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 54) (.exec 0x107751 (LoadPre 0x107751 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x107751 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x107751 0 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 55) (.exec 0x107755 (StorePre 0x107755 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x107755 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107755 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x10775a (movR64M64Effect 0x10775a 0 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 57) (.exec 0x10775a (LoadPre 0x10775a (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x10775a + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10775a 0 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 58) (.exec 0x10775e (StorePre 0x10775e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10775e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10775e 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x107763 (movR64M64Effect 0x107763 0 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 60) (.exec 0x107763 (LoadPre 0x107763 (fun s => AddrMode.addr (.base 6 .none) s (0x107763 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x107763 0 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 61) (.out 0x107766 (movR64M64Effect 0x107766 1 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[6]
    (.letOp (n := 62) (.exec 0x107766 (LoadPre 0x107766 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x107766 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x107766 1 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 63) (.exec 0x10776a (StorePre 0x10776a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10776a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10776a 1 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.exec 0x10776f (StorePre 0x10776f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10776f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10776f 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 65) (.exec 0x107774 (StorePre 0x107774 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x107774 + BitVec.ofNat 64 8)) 4) (movM32Imm32Effect 0x107774 8 (.sib 4 none 0 (.d8 0x4)) 0x100) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x10777c (StorePre 0x10777c 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10777c + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10777c (.sib 4 none 0 (.d8 0x40)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x107785 (StorePre 0x107785 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x107785 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x107785 (.sib 4 none 0 (.d8 0x38)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.exec 0x10778e (StorePre 0x10778e 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10778e + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10778e (.sib 4 none 0 (.d8 0x30)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.exec 0x107797 (StorePre 0x107797 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x107797 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x107797 (.sib 4 none 0 (.d8 0x28)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.out 0x1077a0 (leaR64Effect 0x1077a0 7 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 71) (.exec 0x1077a0 (fun s => s.RIP = 0x1077a0) (leaR64Effect 0x1077a0 7 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.out 0x1077a5 (leaR64Effect 0x1077a5 2 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 73) (.exec 0x1077a5 (fun s => s.RIP = 0x1077a5) (leaR64Effect 0x1077a5 2 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.out 0x1077aa (movR32Imm32Effect 0x1077aa 5 6 0x20) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 75) (.exec 0x1077aa (fun s => s.RIP = 0x1077aa) (movR32Imm32Effect 0x1077aa 5 6 0x20) (Reg.operands [] [])) #v[]
    (.letOp (n := 76) (.out 0x1077af (movR32Imm32Effect 0x1077af 5 1 0x4) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 77) (.exec 0x1077af (fun s => s.RIP = 0x1077af) (movR32Imm32Effect 0x1077af 5 1 0x4) (Reg.operands [] [])) #v[]
    (.letOp (n := 78) (.out 0x1077b4 (movR32Imm32Effect 0x1077b4 6 8 0x100) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 79) (.exec 0x1077b4 (fun s => s.RIP = 0x1077b4) (movR32Imm32Effect 0x1077b4 6 8 0x100) (Reg.operands [] [])) #v[]
    (.letOp (n := 80) (.out 0x1077ba (callEffect (fun _ => 0x127d70) 0x1077bf) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 81) (.exec 0x1077ba (PushPre 0x1077ba 5) (callEffect (fun _ => 0x127d70) 0x1077bf) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 82) (.const ⟨64, 0x1077bf⟩) #v[]
    (.terminate (.call ⟨.l127d70, RegMap.args [(0, 59), (1, 76), (2, 72), (3, 3), (4, 80), (5, 5), (6, 74), (7, 70), (8, 78), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 83⟩ { target := .l1077bf, kept := #v[], arity := rfl, guard := some (Fin.last 82) })))))))))))))))))))))))))))))))

def bytes_l107751 : List UInt8 :=
  [0x48, 0x8B, 0x46, 0x18, 0x48, 0x89, 0x44, 0x24, 0x60, 0x48, 0x8B, 0x46, 0x10, 0x48, 0x89, 0x44,
    0x24, 0x58, 0x48, 0x8B, 0x06, 0x48, 0x8B, 0x4E, 0x08, 0x48, 0x89, 0x4C, 0x24, 0x50, 0x48, 0x89,
    0x44, 0x24, 0x48, 0xC7, 0x44, 0x24, 0x04, 0x00, 0x01, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x40,
    0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x38, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44,
    0x24, 0x30, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x28, 0x00, 0x00, 0x00, 0x00, 0x48,
    0x8D, 0x7C, 0x24, 0x48, 0x48, 0x8D, 0x54, 0x24, 0x28, 0xBE, 0x20, 0x00, 0x00, 0x00, 0xB9, 0x04,
    0x00, 0x00, 0x00, 0x41, 0xB8, 0x00, 0x01, 0x00, 0x00, 0xE8, 0xB1, 0x05, 0x02, 0x00]

theorem code_l107751 : ∀ x ∈ codeRange 0x107751 bytes_l107751, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x7751 110 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1077bf : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1077bf (cmpAlImm8Effect 0x1077bf 0xff) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[0]
    (.letOp (n := 54) (.exec 0x1077bf (fun s => s.RIP = 0x1077bf) (cmpAlImm8Effect 0x1077bf 0xff) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l1078ac, RegMap.args [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l1077c7, RegMap.args [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l1077bf : List UInt8 :=
  [0x3C, 0xFF, 0x0F, 0x85, 0xE5, 0x00, 0x00, 0x00]

theorem code_l1077bf : ∀ x ∈ codeRange 0x1077bf bytes_l1077bf, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x77bf 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1077c7_2 : Block Op Label signature Reg.count 129 :=
  .letOp (n := 129) (.out 0x107868 (shrR64Effect 0x107868 4 2 63) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[127]
    (.letOp (n := 130) (.exec 0x107868 (fun s => s.RIP = 0x107868) (shrR64Effect 0x107868 4 2 63) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[127]
    (.letOp (n := 131) (.exec 0x10786c (StorePre 0x10786c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10786c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10786c 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[129, 4]
    (.letOp (n := 132) (.out 0x107871 (movzxR32M8Effect 0x107871 5 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 133) (.exec 0x107871 (LoadPre 0x107871 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x107871 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x107871 5 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 134) (.out 0x107876 (andAlImm8Effect 0x107876 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[132]
    (.letOp (n := 135) (.exec 0x107876 (fun s => s.RIP = 0x107876) (andAlImm8Effect 0x107876 0x1) (Reg.operands [.gpr 0] [])) #v[132]
    (.letOp (n := 136) (.out 0x107878 (movzxR32R8Effect 0x107878 3 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[134]
    (.letOp (n := 137) (.exec 0x107878 (fun s => s.RIP = 0x107878) (movzxR32R8Effect 0x107878 3 7 0) (Reg.operands [.gpr 0] [])) #v[134]
    (.letOp (n := 138) (.out 0x10787b (callEffect (fun _ => 0x127d50) 0x107880) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 139) (.exec 0x10787b (PushPre 0x10787b 5) (callEffect (fun _ => 0x127d50) 0x107880) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 140) (.const ⟨64, 0x107880⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(0, 134), (1, 121), (2, 129), (3, 3), (4, 138), (5, 59), (6, 87), (7, 136), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 57), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 141⟩ { target := .l107880, kept := #v[], arity := rfl, guard := some (Fin.last 140) })))))))))))))

def bytes_l1077c7_2 : List UInt8 :=
  [0x48, 0xC1, 0xEA, 0x3F, 0x48, 0x89, 0x54, 0x24, 0x08, 0x0F, 0xB6, 0x44, 0x24, 0x08, 0x24, 0x01,
    0x0F, 0xB6, 0xF8, 0xE8, 0xD0, 0x04, 0x02, 0x00]

theorem code_l1077c7_2 : ∀ x ∈ codeRange 0x107868 bytes_l1077c7_2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x7868 24 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1077c7_1 : Block Op Label signature Reg.count 91 :=
  .letOp (n := 91) (.out 0x10781f (notR64Effect 0x10781f 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[89]
    (.letOp (n := 92) (.exec 0x10781f (fun s => s.RIP = 0x10781f) (notR64Effect 0x10781f 2) (Reg.operands [.gpr 2] [])) #v[89]
    (.letOp (n := 93) (.out 0x107822 (orR64R64Effect 0x107822 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[91, 87]
    (.letOp (n := 94) (.exec 0x107822 (fun s => s.RIP = 0x107822) (orR64R64Effect 0x107822 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[91, 87]
    (.letOp (n := 95) (.out 0x107825 (shrR64Effect 0x107825 4 2 63) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[93]
    (.letOp (n := 96) (.exec 0x107825 (fun s => s.RIP = 0x107825) (shrR64Effect 0x107825 4 2 63) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[93]
    (.letOp (n := 97) (.exec 0x107829 (StorePre 0x107829 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x107829 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107829 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[95, 4]
    (.letOp (n := 98) (.out 0x10782e (subR64M64Effect 0x10782e 1 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 4] []) (.reg (.gpr 1))) #v[75, 4]
    (.letOp (n := 99) (.exec 0x10782e (LoadPre 0x10782e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10782e + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x10782e 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[75, 4]
    (.letOp (n := 100) (.out 0x107833 (sarR64Effect 0x107833 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[98]
    (.letOp (n := 101) (.exec 0x107833 (fun s => s.RIP = 0x107833) (sarR64Effect 0x107833 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[98]
    (.letOp (n := 102) (.out 0x107837 (movR64R64Effect 0x107837 2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13] []) (.reg (.gpr 2))) #v[57]
    (.letOp (n := 103) (.exec 0x107837 (fun s => s.RIP = 0x107837) (movR64R64Effect 0x107837 2 13) (Reg.operands [.gpr 13] [])) #v[57]
    (.letOp (n := 104) (.out 0x10783a (notR64Effect 0x10783a 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[102]
    (.letOp (n := 105) (.exec 0x10783a (fun s => s.RIP = 0x10783a) (notR64Effect 0x10783a 2) (Reg.operands [.gpr 2] [])) #v[102]
    (.letOp (n := 106) (.out 0x10783d (addR64R64Effect 0x10783d 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 13] []) (.reg (.gpr 1))) #v[100, 57]
    (.letOp (n := 107) (.exec 0x10783d (fun s => s.RIP = 0x10783d) (addR64R64Effect 0x10783d 1 13) (Reg.operands [.gpr 1, .gpr 13] [])) #v[100, 57]
    (.letOp (n := 108) (.out 0x107840 (addR64Imm8Effect 0x107840 1 0x2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[106]
    (.letOp (n := 109) (.exec 0x107840 (fun s => s.RIP = 0x107840) (addR64Imm8Effect 0x107840 1 0x2) (Reg.operands [.gpr 1] [])) #v[106]
    (.letOp (n := 110) (.out 0x107844 (orR64R64Effect 0x107844 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[108, 104]
    (.letOp (n := 111) (.exec 0x107844 (fun s => s.RIP = 0x107844) (orR64R64Effect 0x107844 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[108, 104]
    (.letOp (n := 112) (.out 0x107847 (shrR64Effect 0x107847 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[110]
    (.letOp (n := 113) (.exec 0x107847 (fun s => s.RIP = 0x107847) (shrR64Effect 0x107847 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[110]
    (.letOp (n := 114) (.exec 0x10784b (StorePre 0x10784b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10784b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10784b 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[112, 4]
    (.letOp (n := 115) (.out 0x107850 (movR64M64Effect 0x107850 1 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 116) (.exec 0x107850 (LoadPre 0x107850 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x107850 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107850 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 117) (.out 0x107855 (decR64Effect 0x107855 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[115]
    (.letOp (n := 118) (.exec 0x107855 (fun s => s.RIP = 0x107855) (decR64Effect 0x107855 1) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[115]
    (.letOp (n := 119) (.out 0x107858 (shrR64Effect 0x107858 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[117]
    (.letOp (n := 120) (.exec 0x107858 (fun s => s.RIP = 0x107858) (shrR64Effect 0x107858 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[117]
    (.letOp (n := 121) (.out 0x10785c (addR64R64Effect 0x10785c 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 5] []) (.reg (.gpr 1))) #v[119, 59]
    (.letOp (n := 122) (.exec 0x10785c (fun s => s.RIP = 0x10785c) (addR64R64Effect 0x10785c 1 5) (Reg.operands [.gpr 1, .gpr 5] [])) #v[119, 59]
    (.letOp (n := 123) (.out 0x10785f (movR64R64Effect 0x10785f 2 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5] []) (.reg (.gpr 2))) #v[59]
    (.letOp (n := 124) (.exec 0x10785f (fun s => s.RIP = 0x10785f) (movR64R64Effect 0x10785f 2 5) (Reg.operands [.gpr 5] [])) #v[59]
    (.letOp (n := 125) (.out 0x107862 (notR64Effect 0x107862 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[123]
    (.letOp (n := 126) (.exec 0x107862 (fun s => s.RIP = 0x107862) (notR64Effect 0x107862 2) (Reg.operands [.gpr 2] [])) #v[123]
    (.letOp (n := 127) (.out 0x107865 (orR64R64Effect 0x107865 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[125, 121]
    (.letOp (n := 128) (.exec 0x107865 (fun s => s.RIP = 0x107865) (orR64R64Effect 0x107865 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[125, 121]
    (b_l1077c7_2))))))))))))))))))))))))))))))))))))))

def bytes_l1077c7_1 : List UInt8 :=
  [0x48, 0xF7, 0xD2, 0x48, 0x09, 0xF2, 0x48, 0xC1, 0xEA, 0x3F, 0x48, 0x89, 0x54, 0x24, 0x08, 0x48,
    0x2B, 0x4C, 0x24, 0x08, 0x48, 0xC1, 0xF9, 0x3F, 0x4C, 0x89, 0xEA, 0x48, 0xF7, 0xD2, 0x4C, 0x01,
    0xE9, 0x48, 0x83, 0xC1, 0x02, 0x48, 0x09, 0xD1, 0x48, 0xC1, 0xE9, 0x3F, 0x48, 0x89, 0x4C, 0x24,
    0x08, 0x48, 0x8B, 0x4C, 0x24, 0x08, 0x48, 0xFF, 0xC9, 0x48, 0xC1, 0xE9, 0x3F, 0x48, 0x01, 0xE9,
    0x48, 0x89, 0xEA, 0x48, 0xF7, 0xD2, 0x48, 0x09, 0xCA] ++ bytes_l1077c7_2

theorem code_l1077c7_1 : ∀ x ∈ codeRange 0x10781f bytes_l1077c7_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x781f 73 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1077c7_2

@[cfg_block] def b_l1077c7 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1077c7 (movR64M64Effect 0x1077c7 15 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 54) (.exec 0x1077c7 (LoadPre 0x1077c7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1077c7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1077c7 15 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1077cc (movR64M64Effect 0x1077cc 12 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 56) (.exec 0x1077cc (LoadPre 0x1077cc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1077cc + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1077cc 12 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1077d1 (movR64M64Effect 0x1077d1 13 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 58) (.exec 0x1077d1 (LoadPre 0x1077d1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1077d1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1077d1 13 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x1077d6 (movR64M64Effect 0x1077d6 5 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 60) (.exec 0x1077d6 (LoadPre 0x1077d6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1077d6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1077d6 5 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x1077db (movR64Imm64Effect 0x1077db 0 0x402da1732fc9bebf) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 62) (.exec 0x1077db (fun s => s.RIP = 0x1077db) (movR64Imm64Effect 0x1077db 0 0x402da1732fc9bebf) (Reg.operands [] [])) #v[]
    (.letOp (n := 63) (.out 0x1077e5 (addR64R64Effect 0x1077e5 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 15] []) (.reg (.gpr 0))) #v[61, 53]
    (.letOp (n := 64) (.exec 0x1077e5 (fun s => s.RIP = 0x1077e5) (addR64R64Effect 0x1077e5 0 15) (Reg.operands [.gpr 0, .gpr 15] [])) #v[61, 53]
    (.letOp (n := 65) (.out 0x1077e8 (movR64R64Effect 0x1077e8 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 15] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 66) (.exec 0x1077e8 (fun s => s.RIP = 0x1077e8) (movR64R64Effect 0x1077e8 1 15) (Reg.operands [.gpr 15] [])) #v[53]
    (.letOp (n := 67) (.out 0x1077eb (notR64Effect 0x1077eb 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 68) (.exec 0x1077eb (fun s => s.RIP = 0x1077eb) (notR64Effect 0x1077eb 1) (Reg.operands [.gpr 1] [])) #v[65]
    (.letOp (n := 69) (.out 0x1077ee (orR64R64Effect 0x1077ee 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[67, 63]
    (.letOp (n := 70) (.exec 0x1077ee (fun s => s.RIP = 0x1077ee) (orR64R64Effect 0x1077ee 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[67, 63]
    (.letOp (n := 71) (.out 0x1077f1 (shrR64Effect 0x1077f1 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[69]
    (.letOp (n := 72) (.exec 0x1077f1 (fun s => s.RIP = 0x1077f1) (shrR64Effect 0x1077f1 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[69]
    (.letOp (n := 73) (.exec 0x1077f5 (StorePre 0x1077f5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1077f5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1077f5 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[71, 4]
    (.letOp (n := 74) (.exec 0x1077fa (fun s => s.RIP = 0x1077fa) (leaR64Effect 0x1077fa 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.out 0x1077ff (xorR32R32Effect 0x1077ff 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[71, 71]
    (.letOp (n := 76) (.exec 0x1077ff (fun s => s.RIP = 0x1077ff) (xorR32R32Effect 0x1077ff 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[71, 71]
    (.letOp (n := 77) (.out 0x107801 (xorR32R32Effect 0x107801 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[2, 2]
    (.letOp (n := 78) (.exec 0x107801 (fun s => s.RIP = 0x107801) (xorR32R32Effect 0x107801 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 79) (.out 0x107803 (subR64M64Effect 0x107803 2 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 4] []) (.reg (.gpr 2))) #v[77, 4]
    (.letOp (n := 80) (.exec 0x107803 (LoadPre 0x107803 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x107803 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x107803 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[77, 4]
    (.letOp (n := 81) (.out 0x107808 (sarR64Effect 0x107808 4 2 63) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[79]
    (.letOp (n := 82) (.exec 0x107808 (fun s => s.RIP = 0x107808) (sarR64Effect 0x107808 4 2 63) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[79]
    (.letOp (n := 83) (.out 0x10780c (movR64Imm64Effect 0x10780c 6 0x4551231950b75fc5) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 84) (.exec 0x10780c (fun s => s.RIP = 0x10780c) (movR64Imm64Effect 0x10780c 6 0x4551231950b75fc5) (Reg.operands [] [])) #v[]
    (.letOp (n := 85) (.out 0x107816 (addR64R64Effect 0x107816 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 12] []) (.reg (.gpr 6))) #v[83, 55]
    (.letOp (n := 86) (.exec 0x107816 (fun s => s.RIP = 0x107816) (addR64R64Effect 0x107816 6 12) (Reg.operands [.gpr 6, .gpr 12] [])) #v[83, 55]
    (.letOp (n := 87) (.out 0x107819 (addR64R64Effect 0x107819 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[85, 81]
    (.letOp (n := 88) (.exec 0x107819 (fun s => s.RIP = 0x107819) (addR64R64Effect 0x107819 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[85, 81]
    (.letOp (n := 89) (.out 0x10781c (movR64R64Effect 0x10781c 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12] []) (.reg (.gpr 2))) #v[55]
    (.letOp (n := 90) (.exec 0x10781c (fun s => s.RIP = 0x10781c) (movR64R64Effect 0x10781c 2 12) (Reg.operands [.gpr 12] [])) #v[55]
    (b_l1077c7_1))))))))))))))))))))))))))))))))))))))

def bytes_l1077c7 : List UInt8 :=
  [0x4C, 0x8B, 0x7C, 0x24, 0x28, 0x4C, 0x8B, 0x64, 0x24, 0x30, 0x4C, 0x8B, 0x6C, 0x24, 0x38, 0x48,
    0x8B, 0x6C, 0x24, 0x40, 0x48, 0xB8, 0xBF, 0xBE, 0xC9, 0x2F, 0x73, 0xA1, 0x2D, 0x40, 0x4C, 0x01,
    0xF8, 0x4C, 0x89, 0xF9, 0x48, 0xF7, 0xD1, 0x48, 0x09, 0xC1, 0x48, 0xC1, 0xE9, 0x3F, 0x48, 0x89,
    0x4C, 0x24, 0x08, 0x48, 0x8D, 0x44, 0x24, 0x08, 0x31, 0xC9, 0x31, 0xD2, 0x48, 0x2B, 0x54, 0x24,
    0x08, 0x48, 0xC1, 0xFA, 0x3F, 0x48, 0xBE, 0xC5, 0x5F, 0xB7, 0x50, 0x19, 0x23, 0x51, 0x45, 0x4C,
    0x01, 0xE6, 0x48, 0x01, 0xD6, 0x4C, 0x89, 0xE2] ++ bytes_l1077c7_1

theorem code_l1077c7 : ∀ x ∈ codeRange 0x1077c7 bytes_l1077c7, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x77c7 88 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1077c7_1

@[cfg_block] def b_l107880 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x107880 (cmpAlImm8Effect 0x107880 0x1) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[0]
    (.letOp (n := 54) (.exec 0x107880 (fun s => s.RIP = 0x107880) (cmpAlImm8Effect 0x107880 0x1) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l107897, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l107884, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l107880 : List UInt8 :=
  [0x3C, 0x01, 0x75, 0x13]

theorem code_l107880 : ∀ x ∈ codeRange 0x107880 bytes_l107880, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x7880 4 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l107884 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x107884 (StorePre 0x107884 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x107884 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x107884 15 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 15, .gpr 3] [])) #v[15, 3]
    (.letOp (n := 54) (.exec 0x107888 (StorePre 0x107888 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x107888 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x107888 12 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 12, .gpr 3] [])) #v[12, 3]
    (.letOp (n := 55) (.exec 0x10788c (StorePre 0x10788c 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x10788c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10788c 13 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 13, .gpr 3] [])) #v[13, 3]
    (.letOp (n := 56) (.exec 0x107890 (StorePre 0x107890 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x107890 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x107890 5 (.base 3 (.d8 0x20))) (Reg.operands [.gpr 5, .gpr 3] [])) #v[5, 3]
    (.letOp (n := 57) (.out 0x107894 (xorR32R32Effect 0x107894 3 14 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 14] []) (.reg (.gpr 14))) #v[14, 14]
    (.letOp (n := 58) (.exec 0x107894 (fun s => s.RIP = 0x107894) (xorR32R32Effect 0x107894 3 14 14) (Reg.operands [.gpr 14, .gpr 14] [])) #v[14, 14]
    (.terminate (.br ⟨.l107897, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 57), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l107884 : List UInt8 :=
  [0x4C, 0x89, 0x7B, 0x08, 0x4C, 0x89, 0x63, 0x10, 0x4C, 0x89, 0x6B, 0x18, 0x48, 0x89, 0x6B, 0x20,
    0x45, 0x31, 0xF6]

theorem code_l107884 : ∀ x ∈ codeRange 0x107884 bytes_l107884, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x7884 19 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l107897 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x107897 (StorePre 0x107897 3 (fun s => AddrMode.addr (.base 3 .none) s (0x107897 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x107897 14 (.base 3 .none)) (Reg.operands [.gpr 14, .gpr 3] [])) #v[14, 3]
    (.letOp (n := 54) (.out 0x10789a (movR64R64Effect 0x10789a 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 55) (.exec 0x10789a (fun s => s.RIP = 0x10789a) (movR64R64Effect 0x10789a 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 56) (.out 0x10789d (addR64Imm8Effect 0x10789d 4 0x68) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 57) (.exec 0x10789d (fun s => s.RIP = 0x10789d) (addR64Imm8Effect 0x10789d 4 0x68) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.out 0x1078a1 (popR64Effect 0x1078a1 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[56]
    (.letOp (n := 59) (.out 0x1078a1 (popR64Effect 0x1078a1 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[56]
    (.letOp (n := 60) (.exec 0x1078a1 (PopPre 0x1078a1) (popR64Effect 0x1078a1 1 3) (Reg.operands [.gpr 4] [])) #v[56]
    (.letOp (n := 61) (.out 0x1078a2 (popR64Effect 0x1078a2 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[59]
    (.letOp (n := 62) (.out 0x1078a2 (popR64Effect 0x1078a2 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 63) (.exec 0x1078a2 (PopPre 0x1078a2) (popR64Effect 0x1078a2 2 12) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 64) (.out 0x1078a4 (popR64Effect 0x1078a4 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[62]
    (.letOp (n := 65) (.out 0x1078a4 (popR64Effect 0x1078a4 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[62]
    (.letOp (n := 66) (.exec 0x1078a4 (PopPre 0x1078a4) (popR64Effect 0x1078a4 2 13) (Reg.operands [.gpr 4] [])) #v[62]
    (.letOp (n := 67) (.out 0x1078a6 (popR64Effect 0x1078a6 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[65]
    (.letOp (n := 68) (.out 0x1078a6 (popR64Effect 0x1078a6 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 69) (.exec 0x1078a6 (PopPre 0x1078a6) (popR64Effect 0x1078a6 2 14) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 70) (.out 0x1078a8 (popR64Effect 0x1078a8 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[68]
    (.letOp (n := 71) (.out 0x1078a8 (popR64Effect 0x1078a8 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[68]
    (.letOp (n := 72) (.exec 0x1078a8 (PopPre 0x1078a8) (popR64Effect 0x1078a8 2 15) (Reg.operands [.gpr 4] [])) #v[68]
    (.letOp (n := 73) (.out 0x1078aa (popR64Effect 0x1078aa 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[71]
    (.letOp (n := 74) (.out 0x1078aa (popR64Effect 0x1078aa 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[71]
    (.letOp (n := 75) (.exec 0x1078aa (PopPre 0x1078aa) (popR64Effect 0x1078aa 1 5) (Reg.operands [.gpr 4] [])) #v[71]
    (.letOp (n := 76) (.out 0x1078ab (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[74]
    (.letOp (n := 77) (.out 0x1078ab (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[74]
    (.letOp (n := 78) (.exec 0x1078ab (RetPre 0x1078ab) (retEffect) (Reg.operands [.gpr 4] [])) #v[74]
    (.terminate (.ret (RegMap.args [(0, 54), (1, 1), (2, 2), (3, 58), (4, 77), (5, 73), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 64), (14, 67), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)] 79) (some ⟨76, by decide⟩))))))))))))))))))))))))))))

def bytes_l107897 : List UInt8 :=
  [0x4C, 0x89, 0x33, 0x48, 0x89, 0xD8, 0x48, 0x83, 0xC4, 0x68, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41,
    0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l107897 : ∀ x ∈ codeRange 0x107897 bytes_l107897, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x7897 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1078ac : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1078ac (StorePre 0x1078ac 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1078ac + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1078ac (.sib 4 none 0 (.d8 0x8)) 0x202498) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.exec 0x1078b5 (StorePre 0x1078b5 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1078b5 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1078b5 (.sib 4 none 0 (.d8 0x10)) 0x12a190) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1078be (leaR64Effect 0x1078be 0 (.sib 4 none 0 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 56) (.exec 0x1078be (fun s => s.RIP = 0x1078be) (leaR64Effect 0x1078be 0 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x1078c3 (StorePre 0x1078c3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1078c3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1078c3 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 58) (.exec 0x1078c8 (StorePre 0x1078c8 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1078c8 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1078c8 (.sib 4 none 0 (.d8 0x20)) 0x12a190) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x1078d1 (leaR64Effect 0x1078d1 6 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 60) (.exec 0x1078d1 (fun s => s.RIP = 0x1078d1) (leaR64Effect 0x1078d1 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x1078d6 (movR64Imm32Effect 0x1078d6 7 0x20028f) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 62) (.exec 0x1078d6 (fun s => s.RIP = 0x1078d6) (movR64Imm32Effect 0x1078d6 7 0x20028f) (Reg.operands [] [])) #v[]
    (.letOp (n := 63) (.out 0x1078dd (movR64Imm32Effect 0x1078dd 2 0x202518) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 64) (.exec 0x1078dd (fun s => s.RIP = 0x1078dd) (movR64Imm32Effect 0x1078dd 2 0x202518) (Reg.operands [] [])) #v[]
    (.letOp (n := 65) (.out 0x1078e4 (callEffect (fun _ => 0x129770) 0x1078e9) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 66) (.exec 0x1078e4 (PushPre 0x1078e4 5) (callEffect (fun _ => 0x129770) 0x1078e9) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.const ⟨64, 0x1078e9⟩) #v[]
    (.terminate (.call ⟨.l129770, RegMap.args [(0, 55), (2, 63), (4, 65), (5, 5), (6, 59), (7, 61)] 68⟩ { target := .l1078e9, kept := #v[], arity := rfl, guard := some (Fin.last 67) }))))))))))))))))

def bytes_l1078ac : List UInt8 :=
  [0x48, 0xC7, 0x44, 0x24, 0x08, 0x98, 0x24, 0x20, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x10, 0x90, 0xA1,
    0x12, 0x00, 0x48, 0x8D, 0x44, 0x24, 0x04, 0x48, 0x89, 0x44, 0x24, 0x18, 0x48, 0xC7, 0x44, 0x24,
    0x20, 0x90, 0xA1, 0x12, 0x00, 0x48, 0x8D, 0x74, 0x24, 0x08, 0x48, 0xC7, 0xC7, 0x8F, 0x02, 0x20,
    0x00, 0x48, 0xC7, 0xC2, 0x18, 0x25, 0x20, 0x00, 0xE8, 0x87, 0x1E, 0x02, 0x00]

theorem code_l1078ac : ∀ x ∈ codeRange 0x1078ac bytes_l1078ac, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x78ac 61 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1078e9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1078e9 (fun s => s.RIP = 0x1078e9) (fun _ => nopEffect 0x1078e9 7) (Reg.operands [] [])) #v[]
    (.letOp (n := 54) (.out 0x1078f0 (subR64Imm8Effect 0x1078f0 4 0x18) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 55) (.exec 0x1078f0 (fun s => s.RIP = 0x1078f0) (subR64Imm8Effect 0x1078f0 4 0x18) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x1078f4 (movR64M64Effect 0x1078f4 0 (.base 7 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 57) (.exec 0x1078f4 (LoadPre 0x1078f4 (fun s => AddrMode.addr (.base 7 .none) s (0x1078f4 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1078f4 0 (.base 7 .none)) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 58) (.out 0x1078f7 (movR64M64Effect 0x1078f7 7 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[6]
    (.letOp (n := 59) (.exec 0x1078f7 (LoadPre 0x1078f7 (fun s => AddrMode.addr (.base 6 .none) s (0x1078f7 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1078f7 7 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 60) (.out 0x1078fa (movR64M64Effect 0x1078fa 6 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[6]
    (.letOp (n := 61) (.exec 0x1078fa (LoadPre 0x1078fa (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x1078fa + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1078fa 6 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 62) (.exec 0x1078fe (StorePre 0x1078fe 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1078fe + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1078fe 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 54]
    (.letOp (n := 63) (.out 0x107902 (movR64R64Effect 0x107902 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[54]
    (.letOp (n := 64) (.exec 0x107902 (fun s => s.RIP = 0x107902) (movR64R64Effect 0x107902 0 4) (Reg.operands [.gpr 4] [])) #v[54]
    (.letOp (n := 65) (.exec 0x107905 (StorePre 0x107905 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x107905 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107905 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[63, 54]
    (.letOp (n := 66) (.exec 0x10790a (StorePre 0x10790a 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10790a + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10790a (.sib 4 none 0 (.d8 0x10)) 0x1079c0) (Reg.operands [.gpr 4] [])) #v[54]
    (.letOp (n := 67) (.out 0x107913 (leaR64Effect 0x107913 1 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[54]
    (.letOp (n := 68) (.exec 0x107913 (fun s => s.RIP = 0x107913) (leaR64Effect 0x107913 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[54]
    (.letOp (n := 69) (.out 0x107918 (movR64Imm32Effect 0x107918 2 0x200413) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 70) (.exec 0x107918 (fun s => s.RIP = 0x107918) (movR64Imm32Effect 0x107918 2 0x200413) (Reg.operands [] [])) #v[]
    (.letOp (n := 71) (.out 0x10791f (callEffect (fun _ => 0x1293a0) 0x107924) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[54]
    (.letOp (n := 72) (.exec 0x10791f (PushPre 0x10791f 5) (callEffect (fun _ => 0x1293a0) 0x107924) (Reg.operands [.gpr 4] [])) #v[54]
    (.letOp (n := 73) (.const ⟨64, 0x107924⟩) #v[]
    (.terminate (.call ⟨.l1293a0, RegMap.args [(0, 63), (1, 67), (2, 69), (3, 3), (4, 71), (5, 5), (6, 60), (7, 58), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 74⟩ { target := .l107924, kept := #v[], arity := rfl, guard := some (Fin.last 73) }))))))))))))))))))))))

def bytes_l1078e9 : List UInt8 :=
  [0x0F, 0x1F, 0x80, 0x00, 0x00, 0x00, 0x00, 0x48, 0x83, 0xEC, 0x18, 0x48, 0x8B, 0x07, 0x48, 0x8B,
    0x3E, 0x48, 0x8B, 0x76, 0x08, 0x48, 0x89, 0x04, 0x24, 0x48, 0x89, 0xE0, 0x48, 0x89, 0x44, 0x24,
    0x08, 0x48, 0xC7, 0x44, 0x24, 0x10, 0xC0, 0x79, 0x10, 0x00, 0x48, 0x8D, 0x4C, 0x24, 0x08, 0x48,
    0xC7, 0xC2, 0x13, 0x04, 0x20, 0x00, 0xE8, 0x7C, 0x1A, 0x02, 0x00]

theorem code_l1078e9 : ∀ x ∈ codeRange 0x1078e9 bytes_l1078e9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x78e9 59 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l107924 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x107924 (addR64Imm8Effect 0x107924 4 0x18) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 54) (.exec 0x107924 (fun s => s.RIP = 0x107924) (addR64Imm8Effect 0x107924 4 0x18) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x107928 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[53]
    (.letOp (n := 56) (.out 0x107928 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[53]
    (.letOp (n := 57) (.exec 0x107928 (RetPre 0x107928) (retEffect) (Reg.operands [.gpr 4] [])) #v[53]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 56), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 58) (some ⟨55, by decide⟩)))))))

def bytes_l107924 : List UInt8 :=
  [0x48, 0x83, 0xC4, 0x18, 0xC3]

theorem code_l107924 : ∀ x ∈ codeRange 0x107924 bytes_l107924, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x7924 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l107a50_1 : Block Op Label signature Reg.count 87 :=
  .letOp (n := 87) (.out 0x107acb (movR32Imm32Effect 0x107acb 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 88) (.exec 0x107acb (fun s => s.RIP = 0x107acb) (movR32Imm32Effect 0x107acb 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 89) (.out 0x107ad0 (movR64R64Effect 0x107ad0 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[71]
    (.letOp (n := 90) (.exec 0x107ad0 (fun s => s.RIP = 0x107ad0) (movR64R64Effect 0x107ad0 7 14) (Reg.operands [.gpr 14] [])) #v[71]
    (.letOp (n := 91) (.out 0x107ad3 (movR64R64Effect 0x107ad3 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[69]
    (.letOp (n := 92) (.exec 0x107ad3 (fun s => s.RIP = 0x107ad3) (movR64R64Effect 0x107ad3 6 15) (Reg.operands [.gpr 15] [])) #v[69]
    (.letOp (n := 93) (.out 0x107ad6 (callEffect (fun _ => 0x1218e0) 0x107adb) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 94) (.exec 0x107ad6 (PushPre 0x107ad6 5) (callEffect (fun _ => 0x1218e0) 0x107adb) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 95) (.const ⟨64, 0x107adb⟩) #v[]
    (.terminate (.call ⟨.l1218e0, RegMap.args [(0, 82), (1, 1), (2, 87), (3, 67), (4, 93), (5, 5), (6, 91), (7, 89), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 71), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 96⟩ { target := .l107adb, kept := #v[], arity := rfl, guard := some (Fin.last 95) }))))))))))

def bytes_l107a50_1 : List UInt8 :=
  [0xBA, 0x01, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF7, 0x4C, 0x89, 0xFE, 0xE8, 0x05, 0x9E, 0x01, 0x00]

theorem code_l107a50_1 : ∀ x ∈ codeRange 0x107acb bytes_l107a50_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x7acb 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l107a50 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x107a50 (pushR64Effect 0x107a50 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x107a50 (PushPre 0x107a50 1) (pushR64Effect 0x107a50 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x107a51 (pushR64Effect 0x107a51 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x107a51 (PushPre 0x107a51 2) (pushR64Effect 0x107a51 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x107a53 (pushR64Effect 0x107a53 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x107a53 (PushPre 0x107a53 2) (pushR64Effect 0x107a53 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x107a55 (pushR64Effect 0x107a55 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x107a55 (PushPre 0x107a55 2) (pushR64Effect 0x107a55 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x107a57 (pushR64Effect 0x107a57 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x107a57 (PushPre 0x107a57 2) (pushR64Effect 0x107a57 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x107a59 (pushR64Effect 0x107a59 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x107a59 (PushPre 0x107a59 1) (pushR64Effect 0x107a59 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x107a5a (subR64Imm32Effect 0x107a5a 4 0x138) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x107a5a (fun s => s.RIP = 0x107a5a) (subR64Imm32Effect 0x107a5a 4 0x138) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x107a61 (movR64R64Effect 0x107a61 3 6) (EffectPart.reads (.reg (.gpr 3)) [.gpr 6] []) (.reg (.gpr 3))) #v[6]
    (.letOp (n := 68) (.exec 0x107a61 (fun s => s.RIP = 0x107a61) (movR64R64Effect 0x107a61 3 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 69) (.out 0x107a64 (movR64R64Effect 0x107a64 15 7) (EffectPart.reads (.reg (.gpr 15)) [.gpr 7] []) (.reg (.gpr 15))) #v[7]
    (.letOp (n := 70) (.exec 0x107a64 (fun s => s.RIP = 0x107a64) (movR64R64Effect 0x107a64 15 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 71) (.out 0x107a67 (leaR64Effect 0x107a67 14 (.sib 4 none 0 (.d32 0x110))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[65]
    (.letOp (n := 72) (.exec 0x107a67 (fun s => s.RIP = 0x107a67) (leaR64Effect 0x107a67 14 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 73) (.out 0x107a6f (movR64Imm64Effect 0x107a6f 0 0x5be0cd191f83d9ab) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 74) (.exec 0x107a6f (fun s => s.RIP = 0x107a6f) (movR64Imm64Effect 0x107a6f 0 0x5be0cd191f83d9ab) (Reg.operands [] [])) #v[]
    (.letOp (n := 75) (.exec 0x107a79 (StorePre 0x107a79 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x107a79 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107a79 0 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[73, 65]
    (.letOp (n := 76) (.out 0x107a81 (movR64Imm64Effect 0x107a81 0 0x9b05688c510e527f) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 77) (.exec 0x107a81 (fun s => s.RIP = 0x107a81) (movR64Imm64Effect 0x107a81 0 0x9b05688c510e527f) (Reg.operands [] [])) #v[]
    (.letOp (n := 78) (.exec 0x107a8b (StorePre 0x107a8b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x107a8b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107a8b 0 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[76, 65]
    (.letOp (n := 79) (.out 0x107a93 (movR64Imm64Effect 0x107a93 0 0xa54ff53a3c6ef372) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 80) (.exec 0x107a93 (fun s => s.RIP = 0x107a93) (movR64Imm64Effect 0x107a93 0 0xa54ff53a3c6ef372) (Reg.operands [] [])) #v[]
    (.letOp (n := 81) (.exec 0x107a9d (StorePre 0x107a9d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x107a9d + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107a9d 0 (.sib 4 none 0 (.d32 0x118))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[79, 65]
    (.letOp (n := 82) (.out 0x107aa5 (movR64Imm64Effect 0x107aa5 0 0xbb67ae856a09e667) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 83) (.exec 0x107aa5 (fun s => s.RIP = 0x107aa5) (movR64Imm64Effect 0x107aa5 0 0xbb67ae856a09e667) (Reg.operands [] [])) #v[]
    (.letOp (n := 84) (.exec 0x107aaf (StorePre 0x107aaf 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x107aaf + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107aaf 0 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[82, 65]
    (.letOp (n := 85) (.exec 0x107ab7 (StorePre 0x107ab7 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x10f)) s (0x107ab7 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x107ab7 (.sib 4 none 0 (.d32 0x10f)) 0x0) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 86) (.exec 0x107abf (StorePre 0x107abf 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x107abf + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x107abf (.sib 4 none 0 (.d32 0x130)) 0x1) (Reg.operands [.gpr 4] [])) #v[65]
    (b_l107a50_1))))))))))))))))))))))))))))))))))

def bytes_l107a50 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0x38, 0x01, 0x00,
    0x00, 0x48, 0x89, 0xF3, 0x49, 0x89, 0xFF, 0x4C, 0x8D, 0xB4, 0x24, 0x10, 0x01, 0x00, 0x00, 0x48,
    0xB8, 0xAB, 0xD9, 0x83, 0x1F, 0x19, 0xCD, 0xE0, 0x5B, 0x48, 0x89, 0x84, 0x24, 0x28, 0x01, 0x00,
    0x00, 0x48, 0xB8, 0x7F, 0x52, 0x0E, 0x51, 0x8C, 0x68, 0x05, 0x9B, 0x48, 0x89, 0x84, 0x24, 0x20,
    0x01, 0x00, 0x00, 0x48, 0xB8, 0x72, 0xF3, 0x6E, 0x3C, 0x3A, 0xF5, 0x4F, 0xA5, 0x48, 0x89, 0x84,
    0x24, 0x18, 0x01, 0x00, 0x00, 0x48, 0xB8, 0x67, 0xE6, 0x09, 0x6A, 0x85, 0xAE, 0x67, 0xBB, 0x48,
    0x89, 0x84, 0x24, 0x10, 0x01, 0x00, 0x00, 0xC6, 0x84, 0x24, 0x0F, 0x01, 0x00, 0x00, 0x00, 0x48,
    0xC7, 0x84, 0x24, 0x30, 0x01, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00] ++ bytes_l107a50_1

theorem code_l107a50 : ∀ x ∈ codeRange 0x107a50 bytes_l107a50, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x7a50 123 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l107a50_1

@[cfg_block] def b_l107adb : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x107adb (StorePre 0x107adb 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x10f)) s (0x107adb + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x107adb (.sib 4 none 0 (.d32 0x10f)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.out 0x107ae3 (addR64Imm8Effect 0x107ae3 15 0x40) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15] []) (.reg (.gpr 15))) #v[15]
    (.letOp (n := 55) (.exec 0x107ae3 (fun s => s.RIP = 0x107ae3) (addR64Imm8Effect 0x107ae3 15 0x40) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 56) (.out 0x107ae7 (leaR64Effect 0x107ae7 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 57) (.exec 0x107ae7 (fun s => s.RIP = 0x107ae7) (leaR64Effect 0x107ae7 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.out 0x107aec (movR32Imm32Effect 0x107aec 5 1 0xd) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 59) (.exec 0x107aec (fun s => s.RIP = 0x107aec) (movR32Imm32Effect 0x107aec 5 1 0xd) (Reg.operands [] [])) #v[]
    (.letOp (n := 60) (.out 0x107af1 (movR64R64Effect 0x107af1 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[54]
    (.letOp (n := 61) (.exec 0x107af1 (fun s => s.RIP = 0x107af1) (movR64R64Effect 0x107af1 6 15) (Reg.operands [.gpr 15] [])) #v[54]
    (.letOp (n := 62) (.out 0x107af4 (repMovsqEffect 0x107af4) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 6))) #v[60, 56, 58, 22]
    (.letOp (n := 63) (.exec 0x107af4 (RepPre 0x107af4 (RepMovsqPre 0x107af4)) (repMovsqEffect 0x107af4) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[60, 56, 58, 22]
    (.letOp (n := 64) (.out 0x107af7 (leaR64Effect 0x107af7 15 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 65) (.exec 0x107af7 (fun s => s.RIP = 0x107af7) (leaR64Effect 0x107af7 15 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.out 0x107afc (movzxR32M8Effect 0x107afc 6 13 (.sib 4 none 0 (.d8 0x47))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 67) (.exec 0x107afc (LoadPre 0x107afc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x47)) s (0x107afc + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x107afc 6 13 (.sib 4 none 0 (.d8 0x47))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.out 0x107b02 (movR64M64Effect 0x107b02 5 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 69) (.exec 0x107b02 (LoadPre 0x107b02 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x107b02 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107b02 5 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.out 0x107b07 (movR64R64Effect 0x107b07 12 13) (EffectPart.reads (.reg (.gpr 12)) [.gpr 13] []) (.reg (.gpr 12))) #v[66]
    (.letOp (n := 71) (.exec 0x107b07 (fun s => s.RIP = 0x107b07) (movR64R64Effect 0x107b07 12 13) (Reg.operands [.gpr 13] [])) #v[66]
    (.letOp (n := 72) (.out 0x107b0a (xorR64Imm8Effect 0x107b0a 12 0x3f) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[70]
    (.letOp (n := 73) (.exec 0x107b0a (fun s => s.RIP = 0x107b0a) (xorR64Imm8Effect 0x107b0a 12 0x3f) (Reg.operands [.gpr 12] [])) #v[70]
    (.letOp (n := 74) (.exec 0x107b0e (StorePre 0x107b0e 6 (fun s => AddrMode.addr (.sib 4 (some 13) 0 (.d8 0x8)) s (0x107b0e + BitVec.ofNat 64 6)) 1) (movM8Imm8RexEffect 0x107b0e (.sib 4 (some 13) 0 (.d8 0x8)) 0x80) (Reg.operands [.gpr 4, .gpr 13] [])) #v[4, 66]
    (.letOp (n := 75) (.out 0x107b14 (leaR64Effect 0x107b14 7 (.sib 4 (some 13) 0 .none)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4, .gpr 13] []) (.reg (.gpr 7))) #v[4, 66]
    (.letOp (n := 76) (.exec 0x107b14 (fun s => s.RIP = 0x107b14) (leaR64Effect 0x107b14 7 (.sib 4 (some 13) 0 .none)) (Reg.operands [.gpr 4, .gpr 13] [])) #v[4, 66]
    (.letOp (n := 77) (.out 0x107b18 (addR64Imm8Effect 0x107b18 7 0x9) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[75]
    (.letOp (n := 78) (.exec 0x107b18 (fun s => s.RIP = 0x107b18) (addR64Imm8Effect 0x107b18 7 0x9) (Reg.operands [.gpr 7] [])) #v[75]
    (.letOp (n := 79) (.out 0x107b1c (xorR32R32Effect 0x107b1c 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[62, 62]
    (.letOp (n := 80) (.exec 0x107b1c (fun s => s.RIP = 0x107b1c) (xorR32R32Effect 0x107b1c 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[62, 62]
    (.letOp (n := 81) (.out 0x107b1e (movR64R64Effect 0x107b1e 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12] []) (.reg (.gpr 2))) #v[72]
    (.letOp (n := 82) (.exec 0x107b1e (fun s => s.RIP = 0x107b1e) (movR64R64Effect 0x107b1e 2 12) (Reg.operands [.gpr 12] [])) #v[72]
    (.letOp (n := 83) (.out 0x107b21 (callEffect (callMemPtr 0x107b21 (.rip 0xfc2e9)) (0x107b21 + BitVec.ofNat 64 (callMemLen (.rip 0xfc2e9)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 84) (.exec 0x107b21 (GoesTo (CallMemPre 0x107b21 (.rip 0xfc2e9)) (callEffect (callMemPtr 0x107b21 (.rip 0xfc2e9)) (0x107b21 + BitVec.ofNat 64 (callMemLen (.rip 0xfc2e9)))) 0x12a700) (callEffect (callMemPtr 0x107b21 (.rip 0xfc2e9)) (0x107b21 + BitVec.ofNat 64 (callMemLen (.rip 0xfc2e9)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 85) (.const ⟨64, 0x107b27⟩) #v[]
    (.terminate (.call ⟨.l12a700, RegMap.args [(2, 81), (3, 3), (4, 83), (5, 68), (6, 79), (7, 77), (9, 9), (10, 10), (11, 11), (12, 72), (13, 66), (14, 14), (15, 64), (22, 22), (39, 39), (50, 50), (51, 51)] 86⟩ { target := .l107b27, kept := #v[], arity := rfl, guard := some (Fin.last 85) }))))))))))))))))))))))))))))))))))

def bytes_l107adb : List UInt8 :=
  [0xC6, 0x84, 0x24, 0x0F, 0x01, 0x00, 0x00, 0x00, 0x49, 0x83, 0xC7, 0x40, 0x48, 0x8D, 0x7C, 0x24,
    0x08, 0xB9, 0x0D, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xFE, 0xF3, 0x48, 0xA5, 0x4C, 0x8D, 0x7C, 0x24,
    0x48, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x47, 0x48, 0x8B, 0x6C, 0x24, 0x68, 0x4D, 0x89, 0xEC, 0x49,
    0x83, 0xF4, 0x3F, 0x42, 0xC6, 0x44, 0x2C, 0x08, 0x80, 0x4A, 0x8D, 0x3C, 0x2C, 0x48, 0x83, 0xC7,
    0x09, 0x31, 0xF6, 0x4C, 0x89, 0xE2, 0xFF, 0x15, 0xE9, 0xC2, 0x0F, 0x00]

theorem code_l107adb : ∀ x ∈ codeRange 0x107adb bytes_l107adb, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x7adb 76 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l107b27 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x107b27 (cmpR64Imm8Effect 0x107b27 12 0x7) (EffectPart.reads (.flag .CF) [.gpr 12] []) (.flag .CF)) #v[12]
    (.letOp (n := 54) (.out 0x107b27 (cmpR64Imm8Effect 0x107b27 12 0x7) (EffectPart.reads (.flag .ZF) [.gpr 12] []) (.flag .ZF)) #v[12]
    (.letOp (n := 55) (.exec 0x107b27 (fun s => s.RIP = 0x107b27) (cmpR64Imm8Effect 0x107b27 12 0x7) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 56) (.pure (condOp 7)) #v[53, 54]
    (.terminate (.condBr (Fin.last 56) ⟨.l107be4, RegMap.args [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩ ⟨.l107b31, RegMap.args [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l107b27 : List UInt8 :=
  [0x49, 0x83, 0xFC, 0x07, 0x0F, 0x87, 0xB3, 0x00, 0x00, 0x00]

theorem code_l107b27 : ∀ x ∈ codeRange 0x107b27 bytes_l107b27, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x7b27 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l107b31 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x107b31 (movR64M64Effect 0x107b31 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x107b31 (LoadPre 0x107b31 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x107b31 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107b31 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x107b36 (StorePre 0x107b36 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x107b36 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107b36 0 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x107b3e (movR64M64Effect 0x107b3e 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x107b3e (LoadPre 0x107b3e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x107b3e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107b3e 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x107b43 (StorePre 0x107b43 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x107b43 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107b43 0 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x107b4b (movR64M64Effect 0x107b4b 0 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x107b4b (LoadPre 0x107b4b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x107b4b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107b4b 0 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x107b50 (StorePre 0x107b50 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x107b50 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107b50 0 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x107b58 (movR64M64Effect 0x107b58 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x107b58 (LoadPre 0x107b58 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x107b58 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107b58 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x107b5d (StorePre 0x107b5d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x107b5d + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107b5d 0 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x107b65 (movR64M64Effect 0x107b65 0 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 66) (.exec 0x107b65 (LoadPre 0x107b65 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x107b65 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107b65 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x107b6a (StorePre 0x107b6a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x107b6a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107b6a 0 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x107b72 (movR64M64Effect 0x107b72 0 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 69) (.exec 0x107b72 (LoadPre 0x107b72 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x107b72 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107b72 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.exec 0x107b77 (StorePre 0x107b77 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x107b77 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107b77 0 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[68, 4]
    (.letOp (n := 71) (.out 0x107b7f (movR64M64Effect 0x107b7f 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 72) (.exec 0x107b7f (LoadPre 0x107b7f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x107b7f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107b7f 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.out 0x107b84 (movR64M64Effect 0x107b84 1 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 74) (.exec 0x107b84 (LoadPre 0x107b84 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x107b84 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107b84 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.exec 0x107b89 (StorePre 0x107b89 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x107b89 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107b89 1 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[73, 4]
    (.letOp (n := 76) (.exec 0x107b8e (StorePre 0x107b8e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x107b8e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107b8e 0 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[71, 4]
    (.letOp (n := 77) (.out 0x107b93 (leaR64Effect 0x107b93 6 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 78) (.exec 0x107b93 (fun s => s.RIP = 0x107b93) (leaR64Effect 0x107b93 6 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.out 0x107b98 (movR32Imm32Effect 0x107b98 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 80) (.exec 0x107b98 (fun s => s.RIP = 0x107b98) (movR32Imm32Effect 0x107b98 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 81) (.out 0x107b9d (movR64R64Effect 0x107b9d 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[15]
    (.letOp (n := 82) (.exec 0x107b9d (fun s => s.RIP = 0x107b9d) (movR64R64Effect 0x107b9d 7 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 83) (.out 0x107ba0 (callEffect (fun _ => 0x1218e0) 0x107ba5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 84) (.exec 0x107ba0 (PushPre 0x107ba0 5) (callEffect (fun _ => 0x1218e0) 0x107ba5) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 85) (.const ⟨64, 0x107ba5⟩) #v[]
    (.terminate (.call ⟨.l1218e0, RegMap.args [(0, 71), (1, 73), (2, 79), (3, 3), (4, 83), (5, 5), (6, 77), (7, 81), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 86⟩ { target := .l107ba5, kept := #v[], arity := rfl, guard := some (Fin.last 85) }))))))))))))))))))))))))))))))))))

def bytes_l107b31 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x40, 0x48, 0x89, 0x84, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x44,
    0x24, 0x38, 0x48, 0x89, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x30, 0x48,
    0x89, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x28, 0x48, 0x89, 0x84, 0x24,
    0x90, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x20, 0x48, 0x89, 0x84, 0x24, 0x88, 0x00, 0x00,
    0x00, 0x48, 0x8B, 0x44, 0x24, 0x18, 0x48, 0x89, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0x8B,
    0x44, 0x24, 0x08, 0x48, 0x8B, 0x4C, 0x24, 0x10, 0x48, 0x89, 0x4C, 0x24, 0x78, 0x48, 0x89, 0x44,
    0x24, 0x70, 0x48, 0x8D, 0x74, 0x24, 0x70, 0xBA, 0x01, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xFF, 0xE8,
    0x3B, 0x9D, 0x01, 0x00]

theorem code_l107b31 : ∀ x ∈ codeRange 0x107b31 bytes_l107b31, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x7b31 116 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l107ba5 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x107ba5 (StorePre 0x107ba5 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x107ba5 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x107ba5 (.sib 4 none 0 (.d8 0x8)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.exec 0x107bae (StorePre 0x107bae 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x107bae + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x107bae (.sib 4 none 0 (.d8 0x10)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x107bb7 (StorePre 0x107bb7 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x107bb7 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x107bb7 (.sib 4 none 0 (.d8 0x18)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.exec 0x107bc0 (StorePre 0x107bc0 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x107bc0 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x107bc0 (.sib 4 none 0 (.d8 0x20)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x107bc9 (StorePre 0x107bc9 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x107bc9 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x107bc9 (.sib 4 none 0 (.d8 0x28)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x107bd2 (StorePre 0x107bd2 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x107bd2 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x107bd2 (.sib 4 none 0 (.d8 0x30)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.exec 0x107bdb (StorePre 0x107bdb 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x107bdb + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x107bdb (.sib 4 none 0 (.d8 0x38)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.br ⟨.l107be4, RegMap.args [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l107ba5 : List UInt8 :=
  [0x48, 0xC7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x10, 0x00, 0x00,
    0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x18, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x20,
    0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x28, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44,
    0x24, 0x30, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x38, 0x00, 0x00, 0x00, 0x00]

theorem code_l107ba5 : ∀ x ∈ codeRange 0x107ba5 bytes_l107ba5, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x7ba5 63 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l107be4_1 : Block Op Label signature Reg.count 84 :=
  .letOp (n := 84) (.out 0x107c54 (leaR64Effect 0x107c54 6 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 85) (.exec 0x107c54 (fun s => s.RIP = 0x107c54) (leaR64Effect 0x107c54 6 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 86) (.out 0x107c59 (movR32Imm32Effect 0x107c59 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 87) (.exec 0x107c59 (fun s => s.RIP = 0x107c59) (movR32Imm32Effect 0x107c59 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 88) (.out 0x107c5e (movR64R64Effect 0x107c5e 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[15]
    (.letOp (n := 89) (.exec 0x107c5e (fun s => s.RIP = 0x107c5e) (movR64R64Effect 0x107c5e 7 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 90) (.out 0x107c61 (callEffect (fun _ => 0x1218e0) 0x107c66) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 91) (.exec 0x107c61 (PushPre 0x107c61 5) (callEffect (fun _ => 0x1218e0) 0x107c66) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 92) (.const ⟨64, 0x107c66⟩) #v[]
    (.terminate (.call ⟨.l1218e0, RegMap.args [(0, 78), (1, 80), (2, 86), (3, 3), (4, 90), (5, 53), (6, 84), (7, 88), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 93⟩ { target := .l107c66, kept := #v[], arity := rfl, guard := some (Fin.last 92) }))))))))))

def bytes_l107be4_1 : List UInt8 :=
  [0x48, 0x8D, 0x74, 0x24, 0x70, 0xBA, 0x01, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xFF, 0xE8, 0x7A, 0x9C,
    0x01, 0x00]

theorem code_l107be4_1 : ∀ x ∈ codeRange 0x107c54 bytes_l107be4_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x7c54 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l107be4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x107be4 (shlR64Effect 0x107be4 4 5 9) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[5]
    (.letOp (n := 54) (.exec 0x107be4 (fun s => s.RIP = 0x107be4) (shlR64Effect 0x107be4 4 5 9) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5]
    (.letOp (n := 55) (.out 0x107be8 (shlR32Effect 0x107be8 4 13 3) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[13]
    (.letOp (n := 56) (.exec 0x107be8 (fun s => s.RIP = 0x107be8) (shlR32Effect 0x107be8 4 13 3) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[13]
    (.letOp (n := 57) (.out 0x107bec (orR64R64Effect 0x107bec 13 5) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 5] []) (.reg (.gpr 13))) #v[55, 53]
    (.letOp (n := 58) (.exec 0x107bec (fun s => s.RIP = 0x107bec) (orR64R64Effect 0x107bec 13 5) (Reg.operands [.gpr 13, .gpr 5] [])) #v[55, 53]
    (.letOp (n := 59) (.out 0x107bef (bswapR64Effect 0x107bef 3 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[57]
    (.letOp (n := 60) (.exec 0x107bef (fun s => s.RIP = 0x107bef) (bswapR64Effect 0x107bef 3 13) (Reg.operands [.gpr 13] [])) #v[57]
    (.letOp (n := 61) (.exec 0x107bf2 (StorePre 0x107bf2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x107bf2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107bf2 13 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.exec 0x107bf7 (StorePre 0x107bf7 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x107bf7 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107bf7 13 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 63) (.out 0x107bff (movR64M64Effect 0x107bff 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 64) (.exec 0x107bff (LoadPre 0x107bff (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x107bff + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107bff 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.exec 0x107c04 (StorePre 0x107c04 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x107c04 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107c04 0 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[63, 4]
    (.letOp (n := 66) (.out 0x107c0c (movR64M64Effect 0x107c0c 0 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 67) (.exec 0x107c0c (LoadPre 0x107c0c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x107c0c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107c0c 0 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.exec 0x107c11 (StorePre 0x107c11 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x107c11 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107c11 0 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[66, 4]
    (.letOp (n := 69) (.out 0x107c19 (movR64M64Effect 0x107c19 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 70) (.exec 0x107c19 (LoadPre 0x107c19 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x107c19 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107c19 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.exec 0x107c1e (StorePre 0x107c1e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x107c1e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107c1e 0 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[69, 4]
    (.letOp (n := 72) (.out 0x107c26 (movR64M64Effect 0x107c26 0 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 73) (.exec 0x107c26 (LoadPre 0x107c26 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x107c26 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107c26 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.exec 0x107c2b (StorePre 0x107c2b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x107c2b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107c2b 0 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[72, 4]
    (.letOp (n := 75) (.out 0x107c33 (movR64M64Effect 0x107c33 0 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 76) (.exec 0x107c33 (LoadPre 0x107c33 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x107c33 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107c33 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 77) (.exec 0x107c38 (StorePre 0x107c38 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x107c38 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107c38 0 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[75, 4]
    (.letOp (n := 78) (.out 0x107c40 (movR64M64Effect 0x107c40 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 79) (.exec 0x107c40 (LoadPre 0x107c40 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x107c40 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107c40 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 80) (.out 0x107c45 (movR64M64Effect 0x107c45 1 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 81) (.exec 0x107c45 (LoadPre 0x107c45 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x107c45 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107c45 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 82) (.exec 0x107c4a (StorePre 0x107c4a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x107c4a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107c4a 1 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[80, 4]
    (.letOp (n := 83) (.exec 0x107c4f (StorePre 0x107c4f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x107c4f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107c4f 0 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[78, 4]
    (b_l107be4_1)))))))))))))))))))))))))))))))

def bytes_l107be4 : List UInt8 :=
  [0x48, 0xC1, 0xE5, 0x09, 0x41, 0xC1, 0xE5, 0x03, 0x49, 0x09, 0xED, 0x49, 0x0F, 0xCD, 0x4C, 0x89,
    0x6C, 0x24, 0x40, 0x4C, 0x89, 0xAC, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x38,
    0x48, 0x89, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x30, 0x48, 0x89, 0x84,
    0x24, 0x98, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x28, 0x48, 0x89, 0x84, 0x24, 0x90, 0x00,
    0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x20, 0x48, 0x89, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48,
    0x8B, 0x44, 0x24, 0x18, 0x48, 0x89, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24,
    0x08, 0x48, 0x8B, 0x4C, 0x24, 0x10, 0x48, 0x89, 0x4C, 0x24, 0x78, 0x48, 0x89, 0x44, 0x24, 0x70] ++ bytes_l107be4_1

theorem code_l107be4 : ∀ x ∈ codeRange 0x107be4 bytes_l107be4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x7be4 112 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l107be4_1

@[cfg_block] def b_l107c66_1 : Block Op Label signature Reg.count 89 :=
  .letOp (n := 89) (.exec 0x107cb8 (StorePre 0x107cb8 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x107cb8 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x107cb8 7 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[71, 4]
    (.letOp (n := 90) (.exec 0x107cbf (StorePre 0x107cbf 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc4)) s (0x107cbf + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x107cbf 8 (.sib 4 none 0 (.d32 0xc4))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[75, 4]
    (.letOp (n := 91) (.exec 0x107cc7 (StorePre 0x107cc7 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x107cc7 + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x107cc7 9 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[79, 4]
    (.letOp (n := 92) (.exec 0x107ccf (StorePre 0x107ccf 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xcc)) s (0x107ccf + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x107ccf 10 (.sib 4 none 0 (.d32 0xcc))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[83, 4]
    (.letOp (n := 93) (.out 0x107cd7 (movzxR32M8Effect 0x107cd7 9 15 (.sib 4 none 0 (.d32 0x10f))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 94) (.exec 0x107cd7 (LoadPre 0x107cd7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x10f)) s (0x107cd7 + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x107cd7 9 15 (.sib 4 none 0 (.d32 0x10f))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 95) (.out 0x107ce0 (cmpR64Imm8Effect 0x107ce0 15 0x1f) (EffectPart.reads (.flag .CF) [.gpr 15] []) (.flag .CF)) #v[93]
    (.letOp (n := 96) (.out 0x107ce0 (cmpR64Imm8Effect 0x107ce0 15 0x1f) (EffectPart.reads (.flag .ZF) [.gpr 15] []) (.flag .ZF)) #v[93]
    (.letOp (n := 97) (.exec 0x107ce0 (fun s => s.RIP = 0x107ce0) (cmpR64Imm8Effect 0x107ce0 15 0x1f) (Reg.operands [.gpr 15] [])) #v[93]
    (.letOp (n := 98) (.pure (condOp 7)) #v[95, 96]
    (.terminate (.condBr (Fin.last 98) ⟨.l107d34, RegMap.args [(0, 57), (1, 59), (2, 63), (3, 3), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (12, 12), (14, 14), (15, 93), (16, 95), (19, 96), (22, 22), (39, 39), (50, 50), (51, 51)] 99⟩ ⟨.l107ce6, RegMap.args [(0, 57), (1, 59), (2, 63), (3, 3), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (12, 12), (14, 14), (15, 93), (16, 95), (19, 96), (22, 22), (39, 39), (50, 50), (51, 51)] 99⟩)))))))))))

def bytes_l107c66_1 : List UInt8 :=
  [0x89, 0xBC, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x44, 0x89, 0x84, 0x24, 0xC4, 0x00, 0x00, 0x00, 0x44,
    0x89, 0x8C, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x44, 0x89, 0x94, 0x24, 0xCC, 0x00, 0x00, 0x00, 0x44,
    0x0F, 0xB6, 0xBC, 0x24, 0x0F, 0x01, 0x00, 0x00, 0x49, 0x83, 0xFF, 0x1F, 0x77, 0x4E]

theorem code_l107c66_1 : ∀ x ∈ codeRange 0x107cb8 bytes_l107c66_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x7cb8 46 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l107c66 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x107c66 (movR32M32LowEffect 0x107c66 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x107c66 (LoadPre 0x107c66 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x107c66 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x107c66 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x107c6a (movR32M32LowEffect 0x107c6a 1 (.sib 4 none 0 (.d8 0x4c))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x107c6a (LoadPre 0x107c6a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4c)) s (0x107c6a + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x107c6a 1 (.sib 4 none 0 (.d8 0x4c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x107c6e (bswapR32Effect 0x107c6e 2 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 58) (.exec 0x107c6e (fun s => s.RIP = 0x107c6e) (bswapR32Effect 0x107c6e 2 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 59) (.out 0x107c70 (bswapR32Effect 0x107c70 2 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[55]
    (.letOp (n := 60) (.exec 0x107c70 (fun s => s.RIP = 0x107c70) (bswapR32Effect 0x107c70 2 1) (Reg.operands [.gpr 1] [])) #v[55]
    (.letOp (n := 61) (.out 0x107c72 (movR32M32LowEffect 0x107c72 2 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 62) (.exec 0x107c72 (LoadPre 0x107c72 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x107c72 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x107c72 2 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x107c76 (bswapR32Effect 0x107c76 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[61]
    (.letOp (n := 64) (.exec 0x107c76 (fun s => s.RIP = 0x107c76) (bswapR32Effect 0x107c76 2 2) (Reg.operands [.gpr 2] [])) #v[61]
    (.letOp (n := 65) (.out 0x107c78 (movR32M32LowEffect 0x107c78 6 (.sib 4 none 0 (.d8 0x54))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 66) (.exec 0x107c78 (LoadPre 0x107c78 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x54)) s (0x107c78 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x107c78 6 (.sib 4 none 0 (.d8 0x54))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x107c7c (bswapR32Effect 0x107c7c 2 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[65]
    (.letOp (n := 68) (.exec 0x107c7c (fun s => s.RIP = 0x107c7c) (bswapR32Effect 0x107c7c 2 6) (Reg.operands [.gpr 6] [])) #v[65]
    (.letOp (n := 69) (.out 0x107c7e (movR32M32LowEffect 0x107c7e 7 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 70) (.exec 0x107c7e (LoadPre 0x107c7e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x107c7e + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x107c7e 7 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.out 0x107c82 (bswapR32Effect 0x107c82 2 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[69]
    (.letOp (n := 72) (.exec 0x107c82 (fun s => s.RIP = 0x107c82) (bswapR32Effect 0x107c82 2 7) (Reg.operands [.gpr 7] [])) #v[69]
    (.letOp (n := 73) (.out 0x107c84 (movR32M32Effect 0x107c84 8 (.sib 4 none 0 (.d8 0x5c))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 74) (.exec 0x107c84 (LoadPre 0x107c84 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5c)) s (0x107c84 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x107c84 8 (.sib 4 none 0 (.d8 0x5c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.out 0x107c89 (bswapR32Effect 0x107c89 3 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[73]
    (.letOp (n := 76) (.exec 0x107c89 (fun s => s.RIP = 0x107c89) (bswapR32Effect 0x107c89 3 8) (Reg.operands [.gpr 8] [])) #v[73]
    (.letOp (n := 77) (.out 0x107c8c (movR32M32Effect 0x107c8c 9 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 78) (.exec 0x107c8c (LoadPre 0x107c8c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x107c8c + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x107c8c 9 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.out 0x107c91 (bswapR32Effect 0x107c91 3 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[77]
    (.letOp (n := 80) (.exec 0x107c91 (fun s => s.RIP = 0x107c91) (bswapR32Effect 0x107c91 3 9) (Reg.operands [.gpr 9] [])) #v[77]
    (.letOp (n := 81) (.out 0x107c94 (movR32M32Effect 0x107c94 10 (.sib 4 none 0 (.d8 0x64))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 82) (.exec 0x107c94 (LoadPre 0x107c94 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x64)) s (0x107c94 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x107c94 10 (.sib 4 none 0 (.d8 0x64))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 83) (.out 0x107c99 (bswapR32Effect 0x107c99 3 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[81]
    (.letOp (n := 84) (.exec 0x107c99 (fun s => s.RIP = 0x107c99) (bswapR32Effect 0x107c99 3 10) (Reg.operands [.gpr 10] [])) #v[81]
    (.letOp (n := 85) (.exec 0x107c9c (StorePre 0x107c9c 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x107c9c + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x107c9c 0 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 86) (.exec 0x107ca3 (StorePre 0x107ca3 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb4)) s (0x107ca3 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x107ca3 1 (.sib 4 none 0 (.d32 0xb4))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 87) (.exec 0x107caa (StorePre 0x107caa 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x107caa + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x107caa 2 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[63, 4]
    (.letOp (n := 88) (.exec 0x107cb1 (StorePre 0x107cb1 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xbc)) s (0x107cb1 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x107cb1 6 (.sib 4 none 0 (.d32 0xbc))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[67, 4]
    (b_l107c66_1))))))))))))))))))))))))))))))))))))

def bytes_l107c66 : List UInt8 :=
  [0x8B, 0x44, 0x24, 0x48, 0x8B, 0x4C, 0x24, 0x4C, 0x0F, 0xC8, 0x0F, 0xC9, 0x8B, 0x54, 0x24, 0x50,
    0x0F, 0xCA, 0x8B, 0x74, 0x24, 0x54, 0x0F, 0xCE, 0x8B, 0x7C, 0x24, 0x58, 0x0F, 0xCF, 0x44, 0x8B,
    0x44, 0x24, 0x5C, 0x41, 0x0F, 0xC8, 0x44, 0x8B, 0x4C, 0x24, 0x60, 0x41, 0x0F, 0xC9, 0x44, 0x8B,
    0x54, 0x24, 0x64, 0x41, 0x0F, 0xCA, 0x89, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x89, 0x8C, 0x24,
    0xB4, 0x00, 0x00, 0x00, 0x89, 0x94, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x89, 0xB4, 0x24, 0xBC, 0x00,
    0x00, 0x00] ++ bytes_l107c66_1

theorem code_l107c66 : ∀ x ∈ codeRange 0x107c66 bytes_l107c66, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x7c66 82 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l107c66_1

@[cfg_block] def b_l107ce6 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x107ce6 (movR64M64Effect 0x107ce6 0 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x107ce6 (LoadPre 0x107ce6 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x107ce6 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107ce6 0 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x107cee (StorePre 0x107cee 8 (fun s => AddrMode.addr (.sib 4 (some 15) 0 (.d32 0xe8)) s (0x107cee + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107cee 0 (.sib 4 (some 15) 0 (.d32 0xe8))) (Reg.operands [.gpr 0, .gpr 4, .gpr 15] [])) #v[53, 4, 15]
    (.letOp (n := 56) (.out 0x107cf6 (movR64M64Effect 0x107cf6 0 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x107cf6 (LoadPre 0x107cf6 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x107cf6 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107cf6 0 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x107cfe (StorePre 0x107cfe 8 (fun s => AddrMode.addr (.sib 4 (some 15) 0 (.d32 0xe0)) s (0x107cfe + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107cfe 0 (.sib 4 (some 15) 0 (.d32 0xe0))) (Reg.operands [.gpr 0, .gpr 4, .gpr 15] [])) #v[56, 4, 15]
    (.letOp (n := 59) (.out 0x107d06 (movR64M64Effect 0x107d06 0 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x107d06 (LoadPre 0x107d06 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x107d06 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107d06 0 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x107d0e (movR64M64Effect 0x107d0e 1 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 62) (.exec 0x107d0e (LoadPre 0x107d0e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x107d0e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107d0e 1 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x107d16 (StorePre 0x107d16 8 (fun s => AddrMode.addr (.sib 4 (some 15) 0 (.d32 0xd8)) s (0x107d16 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107d16 1 (.sib 4 (some 15) 0 (.d32 0xd8))) (Reg.operands [.gpr 1, .gpr 4, .gpr 15] [])) #v[61, 4, 15]
    (.letOp (n := 64) (.exec 0x107d1e (StorePre 0x107d1e 8 (fun s => AddrMode.addr (.sib 4 (some 15) 0 (.d32 0xd0)) s (0x107d1e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107d1e 0 (.sib 4 (some 15) 0 (.d32 0xd0))) (Reg.operands [.gpr 0, .gpr 4, .gpr 15] [])) #v[59, 4, 15]
    (.letOp (n := 65) (.out 0x107d26 (orR8Imm8Effect 0x107d26 4 15 0x20) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15] []) (.reg (.gpr 15))) #v[15]
    (.letOp (n := 66) (.exec 0x107d26 (fun s => s.RIP = 0x107d26) (orR8Imm8Effect 0x107d26 4 15 0x20) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 67) (.exec 0x107d2a (StorePre 0x107d2a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x10f)) s (0x107d2a + BitVec.ofNat 64 8)) 1) (movM8R8Effect 0x107d2a 8 15 (.sib 4 none 0 (.d32 0x10f))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[65, 4]
    (.terminate (.br ⟨.l107da7, RegMap.args [(0, 59), (1, 61), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)] 68⟩))))))))))))))))

def bytes_l107ce6 : List UInt8 :=
  [0x48, 0x8B, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x4A, 0x89, 0x84, 0x3C, 0xE8, 0x00, 0x00, 0x00,
    0x48, 0x8B, 0x84, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x4A, 0x89, 0x84, 0x3C, 0xE0, 0x00, 0x00, 0x00,
    0x48, 0x8B, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x8C, 0x24, 0xB8, 0x00, 0x00, 0x00,
    0x4A, 0x89, 0x8C, 0x3C, 0xD8, 0x00, 0x00, 0x00, 0x4A, 0x89, 0x84, 0x3C, 0xD0, 0x00, 0x00, 0x00,
    0x41, 0x80, 0xCF, 0x20, 0x44, 0x88, 0xBC, 0x24, 0x0F, 0x01, 0x00, 0x00, 0xEB, 0x73]

theorem code_l107ce6 : ∀ x ∈ codeRange 0x107ce6 bytes_l107ce6, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x7ce6 78 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l107d34 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x107d34 (movR32Imm32Effect 0x107d34 5 2 0x40) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 54) (.exec 0x107d34 (fun s => s.RIP = 0x107d34) (movR32Imm32Effect 0x107d34 5 2 0x40) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x107d39 (subR64R64Effect 0x107d39 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 15] []) (.reg (.gpr 2))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x107d39 (fun s => s.RIP = 0x107d39) (subR64R64Effect 0x107d39 2 15) (Reg.operands [.gpr 2, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x107d3c (leaR64Effect 0x107d3c 13 (.sib 4 (some 2) 0 .none)) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4, .gpr 2] []) (.reg (.gpr 13))) #v[4, 55]
    (.letOp (n := 58) (.exec 0x107d3c (fun s => s.RIP = 0x107d3c) (leaR64Effect 0x107d3c 13 (.sib 4 (some 2) 0 .none)) (Reg.operands [.gpr 4, .gpr 2] [])) #v[4, 55]
    (.letOp (n := 59) (.out 0x107d40 (addR64Imm32Effect 0x107d40 13 0xb0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[57]
    (.letOp (n := 60) (.exec 0x107d40 (fun s => s.RIP = 0x107d40) (addR64Imm32Effect 0x107d40 13 0xb0) (Reg.operands [.gpr 13] [])) #v[57]
    (.letOp (n := 61) (.out 0x107d47 (leaR64Effect 0x107d47 7 (.sib 4 (some 15) 0 .none)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4, .gpr 15] []) (.reg (.gpr 7))) #v[4, 15]
    (.letOp (n := 62) (.exec 0x107d47 (fun s => s.RIP = 0x107d47) (leaR64Effect 0x107d47 7 (.sib 4 (some 15) 0 .none)) (Reg.operands [.gpr 4, .gpr 15] [])) #v[4, 15]
    (.letOp (n := 63) (.out 0x107d4b (addR64Imm32Effect 0x107d4b 7 0xd0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[61]
    (.letOp (n := 64) (.exec 0x107d4b (fun s => s.RIP = 0x107d4b) (addR64Imm32Effect 0x107d4b 7 0xd0) (Reg.operands [.gpr 7] [])) #v[61]
    (.letOp (n := 65) (.out 0x107d52 (addR64Imm8Effect 0x107d52 15 0xe0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15] []) (.reg (.gpr 15))) #v[15]
    (.letOp (n := 66) (.exec 0x107d52 (fun s => s.RIP = 0x107d52) (addR64Imm8Effect 0x107d52 15 0xe0) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 67) (.out 0x107d56 (leaR64Effect 0x107d56 6 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 68) (.exec 0x107d56 (fun s => s.RIP = 0x107d56) (leaR64Effect 0x107d56 6 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.out 0x107d5e (leaR64Effect 0x107d5e 5 (.rip 0x22abb)) (EffectPart.reads (.reg (.gpr 5)) [] []) (.reg (.gpr 5))) #v[]
    (.letOp (n := 70) (.exec 0x107d5e (fun s => s.RIP = 0x107d5e) (leaR64Effect 0x107d5e 5 (.rip 0x22abb)) (Reg.operands [] [])) #v[]
    (.letOp (n := 71) (.out 0x107d65 (callEffect (fun s => (Operand.reg 5 : Operand 64).read s) 0x107d67) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 69]
    (.letOp (n := 72) (.exec 0x107d65 (GoesTo (CallPre 0x107d65 2 (fun s => (Operand.reg 5 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 5 : Operand 64).read s) 0x107d67) 0x12a820) (callEffect (fun s => (Operand.reg 5 : Operand 64).read s) 0x107d67) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 69]
    (.letOp (n := 73) (.const ⟨64, 0x107d67⟩) #v[]
    (.terminate (.call ⟨.l12a820, RegMap.args [(2, 55), (3, 3), (4, 71), (5, 69), (6, 67), (7, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 14), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)] 74⟩ { target := .l107d67, kept := #v[], arity := rfl, guard := some (Fin.last 73) }))))))))))))))))))))))

def bytes_l107d34 : List UInt8 :=
  [0xBA, 0x40, 0x00, 0x00, 0x00, 0x4C, 0x29, 0xFA, 0x4C, 0x8D, 0x2C, 0x14, 0x49, 0x81, 0xC5, 0xB0,
    0x00, 0x00, 0x00, 0x4A, 0x8D, 0x3C, 0x3C, 0x48, 0x81, 0xC7, 0xD0, 0x00, 0x00, 0x00, 0x49, 0x83,
    0xC7, 0xE0, 0x48, 0x8D, 0xB4, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x2D, 0xBB, 0x2A, 0x02,
    0x00, 0xFF, 0xD5]

theorem code_l107d34 : ∀ x ∈ codeRange 0x107d34 bytes_l107d34, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x7d34 51 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l107d67 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x107d67 (StorePre 0x107d67 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x107d67 + BitVec.ofNat 64 8)) 8) (incMEffect 0x107d67 8 64 (.sib 4 none 0 (.d32 0x130))) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [])) #v[4]
    (.letOp (n := 54) (.out 0x107d6f (leaR64Effect 0x107d6f 12 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 55) (.exec 0x107d6f (fun s => s.RIP = 0x107d6f) (leaR64Effect 0x107d6f 12 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x107d77 (movR32Imm32Effect 0x107d77 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 57) (.exec 0x107d77 (fun s => s.RIP = 0x107d77) (movR32Imm32Effect 0x107d77 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 58) (.out 0x107d7c (movR64R64Effect 0x107d7c 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 59) (.exec 0x107d7c (fun s => s.RIP = 0x107d7c) (movR64R64Effect 0x107d7c 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 60) (.out 0x107d7f (movR64R64Effect 0x107d7f 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 12] []) (.reg (.gpr 6))) #v[54]
    (.letOp (n := 61) (.exec 0x107d7f (fun s => s.RIP = 0x107d7f) (movR64R64Effect 0x107d7f 6 12) (Reg.operands [.gpr 12] [])) #v[54]
    (.letOp (n := 62) (.out 0x107d82 (callEffect (fun _ => 0x1218e0) 0x107d87) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 63) (.exec 0x107d82 (PushPre 0x107d82 5) (callEffect (fun _ => 0x1218e0) 0x107d87) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.const ⟨64, 0x107d87⟩) #v[]
    (.terminate (.call ⟨.l1218e0, RegMap.args [(0, 0), (1, 1), (2, 56), (3, 3), (4, 62), (5, 5), (6, 60), (7, 58), (8, 8), (9, 9), (10, 10), (11, 11), (12, 54), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 65⟩ { target := .l107d87, kept := #v[], arity := rfl, guard := some (Fin.last 64) })))))))))))))

def bytes_l107d67 : List UInt8 :=
  [0x48, 0xFF, 0x84, 0x24, 0x30, 0x01, 0x00, 0x00, 0x4C, 0x8D, 0xA4, 0x24, 0xD0, 0x00, 0x00, 0x00,
    0xBA, 0x01, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF7, 0x4C, 0x89, 0xE6, 0xE8, 0x59, 0x9B, 0x01, 0x00]

theorem code_l107d67 : ∀ x ∈ codeRange 0x107d67 bytes_l107d67, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x7d67 32 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l107d87 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x107d87 (movR64Imm64Effect 0x107d87 6 0x7fffffffffffffc0) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 54) (.exec 0x107d87 (fun s => s.RIP = 0x107d87) (movR64Imm64Effect 0x107d87 6 0x7fffffffffffffc0) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x107d91 (andR64R64Effect 0x107d91 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 15] []) (.reg (.gpr 6))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x107d91 (fun s => s.RIP = 0x107d91) (andR64R64Effect 0x107d91 6 15) (Reg.operands [.gpr 6, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x107d94 (addR64R64Effect 0x107d94 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 13] []) (.reg (.gpr 6))) #v[55, 13]
    (.letOp (n := 58) (.exec 0x107d94 (fun s => s.RIP = 0x107d94) (addR64R64Effect 0x107d94 6 13) (Reg.operands [.gpr 6, .gpr 13] [])) #v[55, 13]
    (.letOp (n := 59) (.exec 0x107d97 (StorePre 0x107d97 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x10f)) s (0x107d97 + BitVec.ofNat 64 8)) 1) (movM8R8Effect 0x107d97 8 15 (.sib 4 none 0 (.d32 0x10f))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[15, 4]
    (.letOp (n := 60) (.out 0x107d9f (movR64R64Effect 0x107d9f 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[12]
    (.letOp (n := 61) (.exec 0x107d9f (fun s => s.RIP = 0x107d9f) (movR64R64Effect 0x107d9f 7 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 62) (.out 0x107da2 (movR64R64Effect 0x107da2 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15] []) (.reg (.gpr 2))) #v[15]
    (.letOp (n := 63) (.exec 0x107da2 (fun s => s.RIP = 0x107da2) (movR64R64Effect 0x107da2 2 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 64) (.out 0x107da5 (callEffect (fun s => (Operand.reg 5 : Operand 64).read s) 0x107da7) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 65) (.exec 0x107da5 (GoesTo (CallPre 0x107da5 2 (fun s => (Operand.reg 5 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 5 : Operand 64).read s) 0x107da7) 0x12a820) (callEffect (fun s => (Operand.reg 5 : Operand 64).read s) 0x107da7) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 66) (.const ⟨64, 0x107da7⟩) #v[]
    (.terminate (.call ⟨.l12a820, RegMap.args [(2, 62), (3, 3), (4, 64), (5, 5), (6, 57), (7, 60), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩ { target := .l107da7, kept := #v[], arity := rfl, guard := some (Fin.last 66) })))))))))))))))

def bytes_l107d87 : List UInt8 :=
  [0x48, 0xBE, 0xC0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F, 0x4C, 0x21, 0xFE, 0x4C, 0x01, 0xEE,
    0x44, 0x88, 0xBC, 0x24, 0x0F, 0x01, 0x00, 0x00, 0x4C, 0x89, 0xE7, 0x4C, 0x89, 0xFA, 0xFF, 0xD5]

theorem code_l107d87 : ∀ x ∈ codeRange 0x107d87 bytes_l107d87, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x7d87 32 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l107da7 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x107da7 (leaR64Effect 0x107da7 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x107da7 (fun s => s.RIP = 0x107da7) (leaR64Effect 0x107da7 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x107dac (leaR64Effect 0x107dac 6 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 56) (.exec 0x107dac (fun s => s.RIP = 0x107dac) (leaR64Effect 0x107dac 6 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x107db4 (movR32Imm32Effect 0x107db4 5 1 0xd) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 58) (.exec 0x107db4 (fun s => s.RIP = 0x107db4) (movR32Imm32Effect 0x107db4 5 1 0xd) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x107db9 (repMovsqEffect 0x107db9) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 6))) #v[55, 53, 57, 22]
    (.letOp (n := 60) (.exec 0x107db9 (RepPre 0x107db9 (RepMovsqPre 0x107db9)) (repMovsqEffect 0x107db9) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[55, 53, 57, 22]
    (.letOp (n := 61) (.out 0x107dbc (leaR64Effect 0x107dbc 14 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 62) (.exec 0x107dbc (fun s => s.RIP = 0x107dbc) (leaR64Effect 0x107dbc 14 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x107dc1 (movzxR32M8Effect 0x107dc1 6 12 (.sib 4 none 0 (.d8 0x47))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 64) (.exec 0x107dc1 (LoadPre 0x107dc1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x47)) s (0x107dc1 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x107dc1 6 12 (.sib 4 none 0 (.d8 0x47))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x107dc7 (movR64M64Effect 0x107dc7 13 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 66) (.exec 0x107dc7 (LoadPre 0x107dc7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x107dc7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107dc7 13 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x107dcc (movR64R64Effect 0x107dcc 15 12) (EffectPart.reads (.reg (.gpr 15)) [.gpr 12] []) (.reg (.gpr 15))) #v[63]
    (.letOp (n := 68) (.exec 0x107dcc (fun s => s.RIP = 0x107dcc) (movR64R64Effect 0x107dcc 15 12) (Reg.operands [.gpr 12] [])) #v[63]
    (.letOp (n := 69) (.out 0x107dcf (xorR64Imm8Effect 0x107dcf 15 0x3f) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15] []) (.reg (.gpr 15))) #v[67]
    (.letOp (n := 70) (.exec 0x107dcf (fun s => s.RIP = 0x107dcf) (xorR64Imm8Effect 0x107dcf 15 0x3f) (Reg.operands [.gpr 15] [])) #v[67]
    (.letOp (n := 71) (.exec 0x107dd3 (StorePre 0x107dd3 6 (fun s => AddrMode.addr (.sib 4 (some 12) 0 (.d8 0x8)) s (0x107dd3 + BitVec.ofNat 64 6)) 1) (movM8Imm8RexEffect 0x107dd3 (.sib 4 (some 12) 0 (.d8 0x8)) 0x80) (Reg.operands [.gpr 4, .gpr 12] [])) #v[4, 63]
    (.letOp (n := 72) (.out 0x107dd9 (leaR64Effect 0x107dd9 7 (.sib 4 (some 12) 0 .none)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4, .gpr 12] []) (.reg (.gpr 7))) #v[4, 63]
    (.letOp (n := 73) (.exec 0x107dd9 (fun s => s.RIP = 0x107dd9) (leaR64Effect 0x107dd9 7 (.sib 4 (some 12) 0 .none)) (Reg.operands [.gpr 4, .gpr 12] [])) #v[4, 63]
    (.letOp (n := 74) (.out 0x107ddd (addR64Imm8Effect 0x107ddd 7 0x9) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[72]
    (.letOp (n := 75) (.exec 0x107ddd (fun s => s.RIP = 0x107ddd) (addR64Imm8Effect 0x107ddd 7 0x9) (Reg.operands [.gpr 7] [])) #v[72]
    (.letOp (n := 76) (.out 0x107de1 (xorR32R32Effect 0x107de1 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[59, 59]
    (.letOp (n := 77) (.exec 0x107de1 (fun s => s.RIP = 0x107de1) (xorR32R32Effect 0x107de1 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[59, 59]
    (.letOp (n := 78) (.out 0x107de3 (movR64R64Effect 0x107de3 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15] []) (.reg (.gpr 2))) #v[69]
    (.letOp (n := 79) (.exec 0x107de3 (fun s => s.RIP = 0x107de3) (movR64R64Effect 0x107de3 2 15) (Reg.operands [.gpr 15] [])) #v[69]
    (.letOp (n := 80) (.out 0x107de6 (callEffect (callMemPtr 0x107de6 (.rip 0xfc024)) (0x107de6 + BitVec.ofNat 64 (callMemLen (.rip 0xfc024)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 81) (.exec 0x107de6 (GoesTo (CallMemPre 0x107de6 (.rip 0xfc024)) (callEffect (callMemPtr 0x107de6 (.rip 0xfc024)) (0x107de6 + BitVec.ofNat 64 (callMemLen (.rip 0xfc024)))) 0x12a700) (callEffect (callMemPtr 0x107de6 (.rip 0xfc024)) (0x107de6 + BitVec.ofNat 64 (callMemLen (.rip 0xfc024)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 82) (.const ⟨64, 0x107dec⟩) #v[]
    (.terminate (.call ⟨.l12a700, RegMap.args [(2, 78), (3, 3), (4, 80), (5, 5), (6, 76), (7, 74), (9, 9), (10, 10), (11, 11), (12, 63), (13, 65), (14, 61), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 83⟩ { target := .l107dec, kept := #v[], arity := rfl, guard := some (Fin.last 82) })))))))))))))))))))))))))))))))

def bytes_l107da7 : List UInt8 :=
  [0x48, 0x8D, 0x7C, 0x24, 0x08, 0x48, 0x8D, 0xB4, 0x24, 0xD0, 0x00, 0x00, 0x00, 0xB9, 0x0D, 0x00,
    0x00, 0x00, 0xF3, 0x48, 0xA5, 0x4C, 0x8D, 0x74, 0x24, 0x48, 0x44, 0x0F, 0xB6, 0x64, 0x24, 0x47,
    0x4C, 0x8B, 0x6C, 0x24, 0x68, 0x4D, 0x89, 0xE7, 0x49, 0x83, 0xF7, 0x3F, 0x42, 0xC6, 0x44, 0x24,
    0x08, 0x80, 0x4A, 0x8D, 0x3C, 0x24, 0x48, 0x83, 0xC7, 0x09, 0x31, 0xF6, 0x4C, 0x89, 0xFA, 0xFF,
    0x15, 0x24, 0xC0, 0x0F, 0x00]

theorem code_l107da7 : ∀ x ∈ codeRange 0x107da7 bytes_l107da7, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x7da7 69 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l107dec : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x107dec (cmpR64Imm8Effect 0x107dec 15 0x7) (EffectPart.reads (.flag .CF) [.gpr 15] []) (.flag .CF)) #v[15]
    (.letOp (n := 54) (.out 0x107dec (cmpR64Imm8Effect 0x107dec 15 0x7) (EffectPart.reads (.flag .ZF) [.gpr 15] []) (.flag .ZF)) #v[15]
    (.letOp (n := 55) (.exec 0x107dec (fun s => s.RIP = 0x107dec) (cmpR64Imm8Effect 0x107dec 15 0x7) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 56) (.pure (condOp 7)) #v[53, 54]
    (.terminate (.condBr (Fin.last 56) ⟨.l107ea9, RegMap.args [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩ ⟨.l107df6, RegMap.args [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l107dec : List UInt8 :=
  [0x49, 0x83, 0xFF, 0x07, 0x0F, 0x87, 0xB3, 0x00, 0x00, 0x00]

theorem code_l107dec : ∀ x ∈ codeRange 0x107dec bytes_l107dec, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x7dec 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l107df6 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x107df6 (movR64M64Effect 0x107df6 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x107df6 (LoadPre 0x107df6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x107df6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107df6 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x107dfb (StorePre 0x107dfb 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x107dfb + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107dfb 0 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x107e03 (movR64M64Effect 0x107e03 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x107e03 (LoadPre 0x107e03 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x107e03 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107e03 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x107e08 (StorePre 0x107e08 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x107e08 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107e08 0 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x107e10 (movR64M64Effect 0x107e10 0 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x107e10 (LoadPre 0x107e10 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x107e10 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107e10 0 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x107e15 (StorePre 0x107e15 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x107e15 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107e15 0 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x107e1d (movR64M64Effect 0x107e1d 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x107e1d (LoadPre 0x107e1d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x107e1d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107e1d 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x107e22 (StorePre 0x107e22 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x107e22 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107e22 0 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x107e2a (movR64M64Effect 0x107e2a 0 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 66) (.exec 0x107e2a (LoadPre 0x107e2a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x107e2a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107e2a 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x107e2f (StorePre 0x107e2f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x107e2f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107e2f 0 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x107e37 (movR64M64Effect 0x107e37 0 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 69) (.exec 0x107e37 (LoadPre 0x107e37 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x107e37 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107e37 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.exec 0x107e3c (StorePre 0x107e3c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x107e3c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107e3c 0 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[68, 4]
    (.letOp (n := 71) (.out 0x107e44 (movR64M64Effect 0x107e44 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 72) (.exec 0x107e44 (LoadPre 0x107e44 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x107e44 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107e44 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.out 0x107e49 (movR64M64Effect 0x107e49 1 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 74) (.exec 0x107e49 (LoadPre 0x107e49 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x107e49 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107e49 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.exec 0x107e4e (StorePre 0x107e4e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x107e4e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107e4e 1 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[73, 4]
    (.letOp (n := 76) (.exec 0x107e53 (StorePre 0x107e53 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x107e53 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107e53 0 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[71, 4]
    (.letOp (n := 77) (.out 0x107e58 (leaR64Effect 0x107e58 6 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 78) (.exec 0x107e58 (fun s => s.RIP = 0x107e58) (leaR64Effect 0x107e58 6 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.out 0x107e5d (movR32Imm32Effect 0x107e5d 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 80) (.exec 0x107e5d (fun s => s.RIP = 0x107e5d) (movR32Imm32Effect 0x107e5d 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 81) (.out 0x107e62 (movR64R64Effect 0x107e62 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 82) (.exec 0x107e62 (fun s => s.RIP = 0x107e62) (movR64R64Effect 0x107e62 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 83) (.out 0x107e65 (callEffect (fun _ => 0x1218e0) 0x107e6a) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 84) (.exec 0x107e65 (PushPre 0x107e65 5) (callEffect (fun _ => 0x1218e0) 0x107e6a) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 85) (.const ⟨64, 0x107e6a⟩) #v[]
    (.terminate (.call ⟨.l1218e0, RegMap.args [(0, 71), (1, 73), (2, 79), (3, 3), (4, 83), (5, 5), (6, 77), (7, 81), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 86⟩ { target := .l107e6a, kept := #v[], arity := rfl, guard := some (Fin.last 85) }))))))))))))))))))))))))))))))))))

def bytes_l107df6 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x40, 0x48, 0x89, 0x84, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x44,
    0x24, 0x38, 0x48, 0x89, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x30, 0x48,
    0x89, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x28, 0x48, 0x89, 0x84, 0x24,
    0x90, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x20, 0x48, 0x89, 0x84, 0x24, 0x88, 0x00, 0x00,
    0x00, 0x48, 0x8B, 0x44, 0x24, 0x18, 0x48, 0x89, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0x8B,
    0x44, 0x24, 0x08, 0x48, 0x8B, 0x4C, 0x24, 0x10, 0x48, 0x89, 0x4C, 0x24, 0x78, 0x48, 0x89, 0x44,
    0x24, 0x70, 0x48, 0x8D, 0x74, 0x24, 0x70, 0xBA, 0x01, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF7, 0xE8,
    0x76, 0x9A, 0x01, 0x00]

theorem code_l107df6 : ∀ x ∈ codeRange 0x107df6 bytes_l107df6, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x7df6 116 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l107e6a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x107e6a (StorePre 0x107e6a 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x107e6a + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x107e6a (.sib 4 none 0 (.d8 0x8)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.exec 0x107e73 (StorePre 0x107e73 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x107e73 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x107e73 (.sib 4 none 0 (.d8 0x10)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x107e7c (StorePre 0x107e7c 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x107e7c + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x107e7c (.sib 4 none 0 (.d8 0x18)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.exec 0x107e85 (StorePre 0x107e85 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x107e85 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x107e85 (.sib 4 none 0 (.d8 0x20)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x107e8e (StorePre 0x107e8e 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x107e8e + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x107e8e (.sib 4 none 0 (.d8 0x28)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x107e97 (StorePre 0x107e97 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x107e97 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x107e97 (.sib 4 none 0 (.d8 0x30)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.exec 0x107ea0 (StorePre 0x107ea0 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x107ea0 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x107ea0 (.sib 4 none 0 (.d8 0x38)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.br ⟨.l107ea9, RegMap.args [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l107e6a : List UInt8 :=
  [0x48, 0xC7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x10, 0x00, 0x00,
    0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x18, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x20,
    0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x28, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44,
    0x24, 0x30, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x38, 0x00, 0x00, 0x00, 0x00]

theorem code_l107e6a : ∀ x ∈ codeRange 0x107e6a bytes_l107e6a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x7e6a 63 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l107ea9_1 : Block Op Label signature Reg.count 84 :=
  .letOp (n := 84) (.out 0x107f19 (leaR64Effect 0x107f19 6 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 85) (.exec 0x107f19 (fun s => s.RIP = 0x107f19) (leaR64Effect 0x107f19 6 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 86) (.out 0x107f1e (movR32Imm32Effect 0x107f1e 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 87) (.exec 0x107f1e (fun s => s.RIP = 0x107f1e) (movR32Imm32Effect 0x107f1e 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 88) (.out 0x107f23 (movR64R64Effect 0x107f23 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 89) (.exec 0x107f23 (fun s => s.RIP = 0x107f23) (movR64R64Effect 0x107f23 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 90) (.out 0x107f26 (callEffect (fun _ => 0x1218e0) 0x107f2b) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 91) (.exec 0x107f26 (PushPre 0x107f26 5) (callEffect (fun _ => 0x1218e0) 0x107f2b) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 92) (.const ⟨64, 0x107f2b⟩) #v[]
    (.terminate (.call ⟨.l1218e0, RegMap.args [(0, 78), (1, 80), (2, 86), (3, 3), (4, 90), (5, 5), (6, 84), (7, 88), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 93⟩ { target := .l107f2b, kept := #v[], arity := rfl, guard := some (Fin.last 92) }))))))))))

def bytes_l107ea9_1 : List UInt8 :=
  [0x48, 0x8D, 0x74, 0x24, 0x70, 0xBA, 0x01, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF7, 0xE8, 0xB5, 0x99,
    0x01, 0x00]

theorem code_l107ea9_1 : ∀ x ∈ codeRange 0x107f19 bytes_l107ea9_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x7f19 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l107ea9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x107ea9 (shlR64Effect 0x107ea9 4 13 9) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[13]
    (.letOp (n := 54) (.exec 0x107ea9 (fun s => s.RIP = 0x107ea9) (shlR64Effect 0x107ea9 4 13 9) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[13]
    (.letOp (n := 55) (.out 0x107ead (shlR32Effect 0x107ead 4 12 3) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[12]
    (.letOp (n := 56) (.exec 0x107ead (fun s => s.RIP = 0x107ead) (shlR32Effect 0x107ead 4 12 3) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[12]
    (.letOp (n := 57) (.out 0x107eb1 (orR64R64Effect 0x107eb1 12 13) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 13] []) (.reg (.gpr 12))) #v[55, 53]
    (.letOp (n := 58) (.exec 0x107eb1 (fun s => s.RIP = 0x107eb1) (orR64R64Effect 0x107eb1 12 13) (Reg.operands [.gpr 12, .gpr 13] [])) #v[55, 53]
    (.letOp (n := 59) (.out 0x107eb4 (bswapR64Effect 0x107eb4 3 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[57]
    (.letOp (n := 60) (.exec 0x107eb4 (fun s => s.RIP = 0x107eb4) (bswapR64Effect 0x107eb4 3 12) (Reg.operands [.gpr 12] [])) #v[57]
    (.letOp (n := 61) (.exec 0x107eb7 (StorePre 0x107eb7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x107eb7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107eb7 12 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.exec 0x107ebc (StorePre 0x107ebc 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x107ebc + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107ebc 12 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 63) (.out 0x107ec4 (movR64M64Effect 0x107ec4 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 64) (.exec 0x107ec4 (LoadPre 0x107ec4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x107ec4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107ec4 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.exec 0x107ec9 (StorePre 0x107ec9 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x107ec9 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107ec9 0 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[63, 4]
    (.letOp (n := 66) (.out 0x107ed1 (movR64M64Effect 0x107ed1 0 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 67) (.exec 0x107ed1 (LoadPre 0x107ed1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x107ed1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107ed1 0 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.exec 0x107ed6 (StorePre 0x107ed6 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x107ed6 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107ed6 0 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[66, 4]
    (.letOp (n := 69) (.out 0x107ede (movR64M64Effect 0x107ede 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 70) (.exec 0x107ede (LoadPre 0x107ede (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x107ede + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107ede 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.exec 0x107ee3 (StorePre 0x107ee3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x107ee3 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107ee3 0 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[69, 4]
    (.letOp (n := 72) (.out 0x107eeb (movR64M64Effect 0x107eeb 0 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 73) (.exec 0x107eeb (LoadPre 0x107eeb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x107eeb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107eeb 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.exec 0x107ef0 (StorePre 0x107ef0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x107ef0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107ef0 0 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[72, 4]
    (.letOp (n := 75) (.out 0x107ef8 (movR64M64Effect 0x107ef8 0 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 76) (.exec 0x107ef8 (LoadPre 0x107ef8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x107ef8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107ef8 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 77) (.exec 0x107efd (StorePre 0x107efd 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x107efd + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107efd 0 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[75, 4]
    (.letOp (n := 78) (.out 0x107f05 (movR64M64Effect 0x107f05 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 79) (.exec 0x107f05 (LoadPre 0x107f05 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x107f05 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107f05 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 80) (.out 0x107f0a (movR64M64Effect 0x107f0a 1 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 81) (.exec 0x107f0a (LoadPre 0x107f0a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x107f0a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107f0a 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 82) (.exec 0x107f0f (StorePre 0x107f0f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x107f0f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107f0f 1 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[80, 4]
    (.letOp (n := 83) (.exec 0x107f14 (StorePre 0x107f14 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x107f14 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107f14 0 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[78, 4]
    (b_l107ea9_1)))))))))))))))))))))))))))))))

def bytes_l107ea9 : List UInt8 :=
  [0x49, 0xC1, 0xE5, 0x09, 0x41, 0xC1, 0xE4, 0x03, 0x4D, 0x09, 0xEC, 0x49, 0x0F, 0xCC, 0x4C, 0x89,
    0x64, 0x24, 0x40, 0x4C, 0x89, 0xA4, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x38,
    0x48, 0x89, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x30, 0x48, 0x89, 0x84,
    0x24, 0x98, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x28, 0x48, 0x89, 0x84, 0x24, 0x90, 0x00,
    0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x20, 0x48, 0x89, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48,
    0x8B, 0x44, 0x24, 0x18, 0x48, 0x89, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24,
    0x08, 0x48, 0x8B, 0x4C, 0x24, 0x10, 0x48, 0x89, 0x4C, 0x24, 0x78, 0x48, 0x89, 0x44, 0x24, 0x70] ++ bytes_l107ea9_1

theorem code_l107ea9 : ∀ x ∈ codeRange 0x107ea9 bytes_l107ea9, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x7ea9 112 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l107ea9_1

@[cfg_block] def b_l107f2b_1 : Block Op Label signature Reg.count 89 :=
  .letOp (n := 89) (.exec 0x107f6c (StorePre 0x107f6c 3 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x107f6c + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x107f6c 7 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[71, 3]
    (.letOp (n := 90) (.exec 0x107f6f (StorePre 0x107f6f 4 (fun s => AddrMode.addr (.base 3 (.d8 0x14)) s (0x107f6f + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x107f6f 8 (.base 3 (.d8 0x14))) (Reg.operands [.gpr 8, .gpr 3] [])) #v[75, 3]
    (.letOp (n := 91) (.exec 0x107f73 (StorePre 0x107f73 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x107f73 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x107f73 9 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 9, .gpr 3] [])) #v[79, 3]
    (.letOp (n := 92) (.exec 0x107f77 (StorePre 0x107f77 4 (fun s => AddrMode.addr (.base 3 (.d8 0x1c)) s (0x107f77 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x107f77 10 (.base 3 (.d8 0x1c))) (Reg.operands [.gpr 10, .gpr 3] [])) #v[83, 3]
    (.letOp (n := 93) (.out 0x107f7b (addR64Imm32Effect 0x107f7b 4 0x138) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 94) (.exec 0x107f7b (fun s => s.RIP = 0x107f7b) (addR64Imm32Effect 0x107f7b 4 0x138) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 95) (.out 0x107f82 (popR64Effect 0x107f82 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[93]
    (.letOp (n := 96) (.out 0x107f82 (popR64Effect 0x107f82 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[93]
    (.letOp (n := 97) (.exec 0x107f82 (PopPre 0x107f82) (popR64Effect 0x107f82 1 3) (Reg.operands [.gpr 4] [])) #v[93]
    (.letOp (n := 98) (.out 0x107f83 (popR64Effect 0x107f83 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[96]
    (.letOp (n := 99) (.out 0x107f83 (popR64Effect 0x107f83 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[96]
    (.letOp (n := 100) (.exec 0x107f83 (PopPre 0x107f83) (popR64Effect 0x107f83 2 12) (Reg.operands [.gpr 4] [])) #v[96]
    (.letOp (n := 101) (.out 0x107f85 (popR64Effect 0x107f85 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[99]
    (.letOp (n := 102) (.out 0x107f85 (popR64Effect 0x107f85 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[99]
    (.letOp (n := 103) (.exec 0x107f85 (PopPre 0x107f85) (popR64Effect 0x107f85 2 13) (Reg.operands [.gpr 4] [])) #v[99]
    (.letOp (n := 104) (.out 0x107f87 (popR64Effect 0x107f87 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[102]
    (.letOp (n := 105) (.out 0x107f87 (popR64Effect 0x107f87 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[102]
    (.letOp (n := 106) (.exec 0x107f87 (PopPre 0x107f87) (popR64Effect 0x107f87 2 14) (Reg.operands [.gpr 4] [])) #v[102]
    (.letOp (n := 107) (.out 0x107f89 (popR64Effect 0x107f89 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[105]
    (.letOp (n := 108) (.out 0x107f89 (popR64Effect 0x107f89 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[105]
    (.letOp (n := 109) (.exec 0x107f89 (PopPre 0x107f89) (popR64Effect 0x107f89 2 15) (Reg.operands [.gpr 4] [])) #v[105]
    (.letOp (n := 110) (.out 0x107f8b (popR64Effect 0x107f8b 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[108]
    (.letOp (n := 111) (.out 0x107f8b (popR64Effect 0x107f8b 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[108]
    (.letOp (n := 112) (.exec 0x107f8b (PopPre 0x107f8b) (popR64Effect 0x107f8b 1 5) (Reg.operands [.gpr 4] [])) #v[108]
    (.letOp (n := 113) (.out 0x107f8c (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[111]
    (.letOp (n := 114) (.out 0x107f8c (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[111]
    (.letOp (n := 115) (.exec 0x107f8c (RetPre 0x107f8c) (retEffect) (Reg.operands [.gpr 4] [])) #v[111]
    (.terminate (.ret (RegMap.args [(0, 57), (1, 59), (2, 63), (3, 95), (4, 114), (5, 110), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (12, 98), (13, 101), (14, 104), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)] 116) (some ⟨113, by decide⟩)))))))))))))))))))))))))))))

def bytes_l107f2b_1 : List UInt8 :=
  [0x89, 0x7B, 0x10, 0x44, 0x89, 0x43, 0x14, 0x44, 0x89, 0x4B, 0x18, 0x44, 0x89, 0x53, 0x1C, 0x48,
    0x81, 0xC4, 0x38, 0x01, 0x00, 0x00, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F, 0x5D,
    0xC3]

theorem code_l107f2b_1 : ∀ x ∈ codeRange 0x107f6c bytes_l107f2b_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x7f6c 33 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l107f2b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x107f2b (movR32M32LowEffect 0x107f2b 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x107f2b (LoadPre 0x107f2b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x107f2b + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x107f2b 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x107f2f (movR32M32LowEffect 0x107f2f 1 (.sib 4 none 0 (.d8 0x4c))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x107f2f (LoadPre 0x107f2f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4c)) s (0x107f2f + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x107f2f 1 (.sib 4 none 0 (.d8 0x4c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x107f33 (bswapR32Effect 0x107f33 2 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 58) (.exec 0x107f33 (fun s => s.RIP = 0x107f33) (bswapR32Effect 0x107f33 2 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 59) (.out 0x107f35 (bswapR32Effect 0x107f35 2 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[55]
    (.letOp (n := 60) (.exec 0x107f35 (fun s => s.RIP = 0x107f35) (bswapR32Effect 0x107f35 2 1) (Reg.operands [.gpr 1] [])) #v[55]
    (.letOp (n := 61) (.out 0x107f37 (movR32M32LowEffect 0x107f37 2 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 62) (.exec 0x107f37 (LoadPre 0x107f37 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x107f37 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x107f37 2 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x107f3b (bswapR32Effect 0x107f3b 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[61]
    (.letOp (n := 64) (.exec 0x107f3b (fun s => s.RIP = 0x107f3b) (bswapR32Effect 0x107f3b 2 2) (Reg.operands [.gpr 2] [])) #v[61]
    (.letOp (n := 65) (.out 0x107f3d (movR32M32LowEffect 0x107f3d 6 (.sib 4 none 0 (.d8 0x54))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 66) (.exec 0x107f3d (LoadPre 0x107f3d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x54)) s (0x107f3d + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x107f3d 6 (.sib 4 none 0 (.d8 0x54))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x107f41 (bswapR32Effect 0x107f41 2 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[65]
    (.letOp (n := 68) (.exec 0x107f41 (fun s => s.RIP = 0x107f41) (bswapR32Effect 0x107f41 2 6) (Reg.operands [.gpr 6] [])) #v[65]
    (.letOp (n := 69) (.out 0x107f43 (movR32M32LowEffect 0x107f43 7 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 70) (.exec 0x107f43 (LoadPre 0x107f43 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x107f43 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x107f43 7 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.out 0x107f47 (bswapR32Effect 0x107f47 2 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[69]
    (.letOp (n := 72) (.exec 0x107f47 (fun s => s.RIP = 0x107f47) (bswapR32Effect 0x107f47 2 7) (Reg.operands [.gpr 7] [])) #v[69]
    (.letOp (n := 73) (.out 0x107f49 (movR32M32Effect 0x107f49 8 (.sib 4 none 0 (.d8 0x5c))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 74) (.exec 0x107f49 (LoadPre 0x107f49 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5c)) s (0x107f49 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x107f49 8 (.sib 4 none 0 (.d8 0x5c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.out 0x107f4e (bswapR32Effect 0x107f4e 3 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[73]
    (.letOp (n := 76) (.exec 0x107f4e (fun s => s.RIP = 0x107f4e) (bswapR32Effect 0x107f4e 3 8) (Reg.operands [.gpr 8] [])) #v[73]
    (.letOp (n := 77) (.out 0x107f51 (movR32M32Effect 0x107f51 9 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 78) (.exec 0x107f51 (LoadPre 0x107f51 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x107f51 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x107f51 9 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.out 0x107f56 (bswapR32Effect 0x107f56 3 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[77]
    (.letOp (n := 80) (.exec 0x107f56 (fun s => s.RIP = 0x107f56) (bswapR32Effect 0x107f56 3 9) (Reg.operands [.gpr 9] [])) #v[77]
    (.letOp (n := 81) (.out 0x107f59 (movR32M32Effect 0x107f59 10 (.sib 4 none 0 (.d8 0x64))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 82) (.exec 0x107f59 (LoadPre 0x107f59 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x64)) s (0x107f59 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x107f59 10 (.sib 4 none 0 (.d8 0x64))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 83) (.out 0x107f5e (bswapR32Effect 0x107f5e 3 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[81]
    (.letOp (n := 84) (.exec 0x107f5e (fun s => s.RIP = 0x107f5e) (bswapR32Effect 0x107f5e 3 10) (Reg.operands [.gpr 10] [])) #v[81]
    (.letOp (n := 85) (.exec 0x107f61 (StorePre 0x107f61 2 (fun s => AddrMode.addr (.base 3 .none) s (0x107f61 + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x107f61 0 (.base 3 .none)) (Reg.operands [.gpr 0, .gpr 3] [])) #v[57, 3]
    (.letOp (n := 86) (.exec 0x107f63 (StorePre 0x107f63 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x107f63 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x107f63 1 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[59, 3]
    (.letOp (n := 87) (.exec 0x107f66 (StorePre 0x107f66 3 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x107f66 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x107f66 2 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[63, 3]
    (.letOp (n := 88) (.exec 0x107f69 (StorePre 0x107f69 3 (fun s => AddrMode.addr (.base 3 (.d8 0xc)) s (0x107f69 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x107f69 6 (.base 3 (.d8 0xc))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[67, 3]
    (b_l107f2b_1))))))))))))))))))))))))))))))))))))

def bytes_l107f2b : List UInt8 :=
  [0x8B, 0x44, 0x24, 0x48, 0x8B, 0x4C, 0x24, 0x4C, 0x0F, 0xC8, 0x0F, 0xC9, 0x8B, 0x54, 0x24, 0x50,
    0x0F, 0xCA, 0x8B, 0x74, 0x24, 0x54, 0x0F, 0xCE, 0x8B, 0x7C, 0x24, 0x58, 0x0F, 0xCF, 0x44, 0x8B,
    0x44, 0x24, 0x5C, 0x41, 0x0F, 0xC8, 0x44, 0x8B, 0x4C, 0x24, 0x60, 0x41, 0x0F, 0xC9, 0x44, 0x8B,
    0x54, 0x24, 0x64, 0x41, 0x0F, 0xCA, 0x89, 0x03, 0x89, 0x4B, 0x04, 0x89, 0x53, 0x08, 0x89, 0x73,
    0x0C] ++ bytes_l107f2b_1

theorem code_l107f2b : ∀ x ∈ codeRange 0x107f2b bytes_l107f2b, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x7f2b 65 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l107f2b_1

@[cfg_block] def b_l108380 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x108380 (pushR64Effect 0x108380 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[4, 3]
    (.letOp (n := 54) (.exec 0x108380 (PushPre 0x108380 1) (pushR64Effect 0x108380 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[4, 3]
    (.letOp (n := 55) (.out 0x108381 (subR64Imm8Effect 0x108381 4 0x50) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[53]
    (.letOp (n := 56) (.exec 0x108381 (fun s => s.RIP = 0x108381) (subR64Imm8Effect 0x108381 4 0x50) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 57) (.out 0x108385 (movR64R64Effect 0x108385 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 58) (.exec 0x108385 (fun s => s.RIP = 0x108385) (movR64R64Effect 0x108385 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 59) (.out 0x108388 (movR64Imm64Effect 0x108388 0 0xbfd25e8cd0364141) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 60) (.exec 0x108388 (fun s => s.RIP = 0x108388) (movR64Imm64Effect 0x108388 0 0xbfd25e8cd0364141) (Reg.operands [] [])) #v[]
    (.letOp (n := 61) (.exec 0x108392 (StorePre 0x108392 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x108392 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108392 0 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 55]
    (.letOp (n := 62) (.out 0x108397 (movR64Imm64Effect 0x108397 0 0xbaaedce6af48a03b) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 63) (.exec 0x108397 (fun s => s.RIP = 0x108397) (movR64Imm64Effect 0x108397 0 0xbaaedce6af48a03b) (Reg.operands [] [])) #v[]
    (.letOp (n := 64) (.exec 0x1083a1 (StorePre 0x1083a1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1083a1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1083a1 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 55]
    (.letOp (n := 65) (.exec 0x1083a6 (StorePre 0x1083a6 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1083a6 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1083a6 (.sib 4 none 0 (.d8 0x40)) 0xfffffffe) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 66) (.exec 0x1083af (StorePre 0x1083af 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1083af + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1083af (.sib 4 none 0 (.d8 0x48)) 0xffffffff) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 67) (.out 0x1083b8 (leaR64Effect 0x1083b8 7 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[55]
    (.letOp (n := 68) (.exec 0x1083b8 (fun s => s.RIP = 0x1083b8) (leaR64Effect 0x1083b8 7 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 69) (.out 0x1083bd (leaR64Effect 0x1083bd 6 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[55]
    (.letOp (n := 70) (.exec 0x1083bd (fun s => s.RIP = 0x1083bd) (leaR64Effect 0x1083bd 6 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 71) (.out 0x1083c2 (movR32Imm32Effect 0x1083c2 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 72) (.exec 0x1083c2 (fun s => s.RIP = 0x1083c2) (movR32Imm32Effect 0x1083c2 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 73) (.exec 0x1083c7 (fun s => s.RIP = 0x1083c7) (movR64Imm32Effect 0x1083c7 1 0x202868) (Reg.operands [] [])) #v[]
    (.letOp (n := 74) (.out 0x1083ce (callEffect (fun _ => 0x1065b0) 0x1083d3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[55]
    (.letOp (n := 75) (.exec 0x1083ce (PushPre 0x1083ce 5) (callEffect (fun _ => 0x1065b0) 0x1083d3) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 76) (.const ⟨64, 0x1083d3⟩) #v[]
    (.terminate (.call ⟨.l1065b0, RegMap.args [(0, 62), (2, 71), (3, 57), (4, 74), (5, 5), (6, 69), (7, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 77⟩ { target := .l1083d3, kept := #v[], arity := rfl, guard := some (Fin.last 76) })))))))))))))))))))))))))

def bytes_l108380 : List UInt8 :=
  [0x53, 0x48, 0x83, 0xEC, 0x50, 0x48, 0x89, 0xFB, 0x48, 0xB8, 0x41, 0x41, 0x36, 0xD0, 0x8C, 0x5E,
    0xD2, 0xBF, 0x48, 0x89, 0x44, 0x24, 0x30, 0x48, 0xB8, 0x3B, 0xA0, 0x48, 0xAF, 0xE6, 0xDC, 0xAE,
    0xBA, 0x48, 0x89, 0x44, 0x24, 0x38, 0x48, 0xC7, 0x44, 0x24, 0x40, 0xFE, 0xFF, 0xFF, 0xFF, 0x48,
    0xC7, 0x44, 0x24, 0x48, 0xFF, 0xFF, 0xFF, 0xFF, 0x48, 0x8D, 0x7C, 0x24, 0x10, 0x48, 0x8D, 0x74,
    0x24, 0x30, 0xBA, 0x01, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC1, 0x68, 0x28, 0x20, 0x00, 0xE8, 0xDD,
    0xE1, 0xFF, 0xFF]

theorem code_l108380 : ∀ x ∈ codeRange 0x108380 bytes_l108380, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x8380 83 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1083d3_3 : Block Op Label signature Reg.count 168 :=
  .letOp (n := 168) (.out 0x1084a7 (movzxR32R8Effect 0x1084a7 3 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[166]
    (.letOp (n := 169) (.exec 0x1084a7 (fun s => s.RIP = 0x1084a7) (movzxR32R8Effect 0x1084a7 3 7 0) (Reg.operands [.gpr 0] [])) #v[166]
    (.letOp (n := 170) (.out 0x1084aa (callEffect (fun _ => 0x127d50) 0x1084af) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 171) (.exec 0x1084aa (PushPre 0x1084aa 5) (callEffect (fun _ => 0x127d50) 0x1084af) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 172) (.const ⟨64, 0x1084af⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(0, 166), (1, 147), (2, 161), (3, 3), (4, 170), (5, 5), (6, 141), (7, 168), (8, 126), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 173⟩ { target := .l1084af, kept := #v[], arity := rfl, guard := some (Fin.last 172) }))))))

def bytes_l1083d3_3 : List UInt8 :=
  [0x0F, 0xB6, 0xF8, 0xE8, 0xA1, 0xF8, 0x01, 0x00]

theorem code_l1083d3_3 : ∀ x ∈ codeRange 0x1084a7 bytes_l1083d3_3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x84a7 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1083d3_2 : Block Op Label signature Reg.count 130 :=
  .letOp (n := 130) (.out 0x10845e (andR64R64Effect 0x10845e 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[128, 120]
    (.letOp (n := 131) (.exec 0x10845e (fun s => s.RIP = 0x10845e) (andR64R64Effect 0x10845e 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[128, 120]
    (.letOp (n := 132) (.out 0x108461 (orR64R64Effect 0x108461 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 8] []) (.reg (.gpr 6))) #v[130, 126]
    (.letOp (n := 133) (.exec 0x108461 (fun s => s.RIP = 0x108461) (orR64R64Effect 0x108461 6 8) (Reg.operands [.gpr 6, .gpr 8] [])) #v[130, 126]
    (.letOp (n := 134) (.out 0x108464 (shrR64Effect 0x108464 4 6 63) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[132]
    (.letOp (n := 135) (.exec 0x108464 (fun s => s.RIP = 0x108464) (shrR64Effect 0x108464 4 6 63) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[132]
    (.letOp (n := 136) (.exec 0x108468 (StorePre 0x108468 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x108468 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108468 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[134, 4]
    (.letOp (n := 137) (.out 0x10846d (subR64M64Effect 0x10846d 1 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 4] []) (.reg (.gpr 1))) #v[77, 4]
    (.letOp (n := 138) (.exec 0x10846d (LoadPre 0x10846d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10846d + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x10846d 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[77, 4]
    (.letOp (n := 139) (.out 0x108472 (movR64M64Effect 0x108472 2 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 140) (.exec 0x108472 (LoadPre 0x108472 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x108472 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x108472 2 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 141) (.out 0x108477 (movR64M64Effect 0x108477 6 (.base 3 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[3]
    (.letOp (n := 142) (.exec 0x108477 (LoadPre 0x108477 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x108477 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x108477 6 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 143) (.out 0x10847b (sarR64Effect 0x10847b 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[137]
    (.letOp (n := 144) (.exec 0x10847b (fun s => s.RIP = 0x10847b) (sarR64Effect 0x10847b 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[137]
    (.letOp (n := 145) (.out 0x10847f (addR64R64Effect 0x10847f 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[143, 139]
    (.letOp (n := 146) (.exec 0x10847f (fun s => s.RIP = 0x10847f) (addR64R64Effect 0x10847f 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[143, 139]
    (.letOp (n := 147) (.out 0x108482 (subR64R64Effect 0x108482 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[145, 141]
    (.letOp (n := 148) (.exec 0x108482 (fun s => s.RIP = 0x108482) (subR64R64Effect 0x108482 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[145, 141]
    (.letOp (n := 149) (.out 0x108485 (notR64Effect 0x108485 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[139]
    (.letOp (n := 150) (.exec 0x108485 (fun s => s.RIP = 0x108485) (notR64Effect 0x108485 2) (Reg.operands [.gpr 2] [])) #v[139]
    (.letOp (n := 151) (.out 0x108488 (movR64R64Effect 0x108488 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[141]
    (.letOp (n := 152) (.exec 0x108488 (fun s => s.RIP = 0x108488) (movR64R64Effect 0x108488 7 6) (Reg.operands [.gpr 6] [])) #v[141]
    (.letOp (n := 153) (.out 0x10848b (andR64R64Effect 0x10848b 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2] []) (.reg (.gpr 7))) #v[151, 149]
    (.letOp (n := 154) (.exec 0x10848b (fun s => s.RIP = 0x10848b) (andR64R64Effect 0x10848b 7 2) (Reg.operands [.gpr 7, .gpr 2] [])) #v[151, 149]
    (.letOp (n := 155) (.out 0x10848e (orR64R64Effect 0x10848e 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[149, 141]
    (.letOp (n := 156) (.exec 0x10848e (fun s => s.RIP = 0x10848e) (orR64R64Effect 0x10848e 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[149, 141]
    (.letOp (n := 157) (.out 0x108491 (andR64R64Effect 0x108491 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[155, 147]
    (.letOp (n := 158) (.exec 0x108491 (fun s => s.RIP = 0x108491) (andR64R64Effect 0x108491 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[155, 147]
    (.letOp (n := 159) (.out 0x108494 (orR64R64Effect 0x108494 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 7] []) (.reg (.gpr 2))) #v[157, 153]
    (.letOp (n := 160) (.exec 0x108494 (fun s => s.RIP = 0x108494) (orR64R64Effect 0x108494 2 7) (Reg.operands [.gpr 2, .gpr 7] [])) #v[157, 153]
    (.letOp (n := 161) (.out 0x108497 (shrR64Effect 0x108497 4 2 63) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[159]
    (.letOp (n := 162) (.exec 0x108497 (fun s => s.RIP = 0x108497) (shrR64Effect 0x108497 4 2 63) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[159]
    (.letOp (n := 163) (.exec 0x10849b (StorePre 0x10849b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10849b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10849b 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[161, 4]
    (.letOp (n := 164) (.out 0x1084a0 (movzxR32M8Effect 0x1084a0 5 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 165) (.exec 0x1084a0 (LoadPre 0x1084a0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1084a0 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1084a0 5 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 166) (.out 0x1084a5 (andAlImm8Effect 0x1084a5 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[164]
    (.letOp (n := 167) (.exec 0x1084a5 (fun s => s.RIP = 0x1084a5) (andAlImm8Effect 0x1084a5 0x1) (Reg.operands [.gpr 0] [])) #v[164]
    (b_l1083d3_3))))))))))))))))))))))))))))))))))))))

def bytes_l1083d3_2 : List UInt8 :=
  [0x48, 0x21, 0xD6, 0x4C, 0x09, 0xC6, 0x48, 0xC1, 0xEE, 0x3F, 0x48, 0x89, 0x74, 0x24, 0x08, 0x48,
    0x2B, 0x4C, 0x24, 0x08, 0x48, 0x8B, 0x54, 0x24, 0x28, 0x48, 0x8B, 0x73, 0x18, 0x48, 0xC1, 0xF9,
    0x3F, 0x48, 0x01, 0xD1, 0x48, 0x29, 0xF1, 0x48, 0xF7, 0xD2, 0x48, 0x89, 0xF7, 0x48, 0x21, 0xD7,
    0x48, 0x09, 0xF2, 0x48, 0x21, 0xCA, 0x48, 0x09, 0xFA, 0x48, 0xC1, 0xEA, 0x3F, 0x48, 0x89, 0x54,
    0x24, 0x08, 0x0F, 0xB6, 0x44, 0x24, 0x08, 0x24, 0x01] ++ bytes_l1083d3_3

theorem code_l1083d3_2 : ∀ x ∈ codeRange 0x10845e bytes_l1083d3_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x845e 73 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1083d3_3

@[cfg_block] def b_l1083d3_1 : Block Op Label signature Reg.count 91 :=
  .letOp (n := 91) (.out 0x10841a (subR64R64Effect 0x10841a 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 7] []) (.reg (.gpr 2))) #v[89, 85]
    (.letOp (n := 92) (.exec 0x10841a (fun s => s.RIP = 0x10841a) (subR64R64Effect 0x10841a 2 7) (Reg.operands [.gpr 2, .gpr 7] [])) #v[89, 85]
    (.letOp (n := 93) (.out 0x10841d (notR64Effect 0x10841d 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[83]
    (.letOp (n := 94) (.exec 0x10841d (fun s => s.RIP = 0x10841d) (notR64Effect 0x10841d 6) (Reg.operands [.gpr 6] [])) #v[83]
    (.letOp (n := 95) (.out 0x108420 (movR64R64Effect 0x108420 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 7] []) (.reg (.gpr 8))) #v[85]
    (.letOp (n := 96) (.exec 0x108420 (fun s => s.RIP = 0x108420) (movR64R64Effect 0x108420 8 7) (Reg.operands [.gpr 7] [])) #v[85]
    (.letOp (n := 97) (.out 0x108423 (andR64R64Effect 0x108423 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6] []) (.reg (.gpr 8))) #v[95, 93]
    (.letOp (n := 98) (.exec 0x108423 (fun s => s.RIP = 0x108423) (andR64R64Effect 0x108423 8 6) (Reg.operands [.gpr 8, .gpr 6] [])) #v[95, 93]
    (.letOp (n := 99) (.out 0x108426 (orR64R64Effect 0x108426 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7] []) (.reg (.gpr 6))) #v[93, 85]
    (.letOp (n := 100) (.exec 0x108426 (fun s => s.RIP = 0x108426) (orR64R64Effect 0x108426 6 7) (Reg.operands [.gpr 6, .gpr 7] [])) #v[93, 85]
    (.letOp (n := 101) (.out 0x108429 (andR64R64Effect 0x108429 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[99, 91]
    (.letOp (n := 102) (.exec 0x108429 (fun s => s.RIP = 0x108429) (andR64R64Effect 0x108429 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[99, 91]
    (.letOp (n := 103) (.out 0x10842c (orR64R64Effect 0x10842c 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 8] []) (.reg (.gpr 6))) #v[101, 97]
    (.letOp (n := 104) (.exec 0x10842c (fun s => s.RIP = 0x10842c) (orR64R64Effect 0x10842c 6 8) (Reg.operands [.gpr 6, .gpr 8] [])) #v[101, 97]
    (.letOp (n := 105) (.out 0x10842f (shrR64Effect 0x10842f 4 6 63) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[103]
    (.letOp (n := 106) (.exec 0x10842f (fun s => s.RIP = 0x10842f) (shrR64Effect 0x10842f 4 6 63) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[103]
    (.letOp (n := 107) (.exec 0x108433 (StorePre 0x108433 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x108433 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108433 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[105, 4]
    (.letOp (n := 108) (.out 0x108438 (xorR32R32Effect 0x108438 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[91, 91]
    (.letOp (n := 109) (.exec 0x108438 (fun s => s.RIP = 0x108438) (xorR32R32Effect 0x108438 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[91, 91]
    (.letOp (n := 110) (.out 0x10843a (subR64M64Effect 0x10843a 2 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 4] []) (.reg (.gpr 2))) #v[108, 4]
    (.letOp (n := 111) (.exec 0x10843a (LoadPre 0x10843a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10843a + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x10843a 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[108, 4]
    (.letOp (n := 112) (.out 0x10843f (movR64M64Effect 0x10843f 6 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 113) (.exec 0x10843f (LoadPre 0x10843f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10843f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10843f 6 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 114) (.out 0x108444 (movR64M64Effect 0x108444 7 (.base 3 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 115) (.exec 0x108444 (LoadPre 0x108444 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x108444 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x108444 7 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 116) (.out 0x108448 (sarR64Effect 0x108448 4 2 63) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[110]
    (.letOp (n := 117) (.exec 0x108448 (fun s => s.RIP = 0x108448) (sarR64Effect 0x108448 4 2 63) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[110]
    (.letOp (n := 118) (.out 0x10844c (addR64R64Effect 0x10844c 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[116, 112]
    (.letOp (n := 119) (.exec 0x10844c (fun s => s.RIP = 0x10844c) (addR64R64Effect 0x10844c 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[116, 112]
    (.letOp (n := 120) (.out 0x10844f (subR64R64Effect 0x10844f 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 7] []) (.reg (.gpr 2))) #v[118, 114]
    (.letOp (n := 121) (.exec 0x10844f (fun s => s.RIP = 0x10844f) (subR64R64Effect 0x10844f 2 7) (Reg.operands [.gpr 2, .gpr 7] [])) #v[118, 114]
    (.letOp (n := 122) (.out 0x108452 (notR64Effect 0x108452 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[112]
    (.letOp (n := 123) (.exec 0x108452 (fun s => s.RIP = 0x108452) (notR64Effect 0x108452 6) (Reg.operands [.gpr 6] [])) #v[112]
    (.letOp (n := 124) (.out 0x108455 (movR64R64Effect 0x108455 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 7] []) (.reg (.gpr 8))) #v[114]
    (.letOp (n := 125) (.exec 0x108455 (fun s => s.RIP = 0x108455) (movR64R64Effect 0x108455 8 7) (Reg.operands [.gpr 7] [])) #v[114]
    (.letOp (n := 126) (.out 0x108458 (andR64R64Effect 0x108458 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6] []) (.reg (.gpr 8))) #v[124, 122]
    (.letOp (n := 127) (.exec 0x108458 (fun s => s.RIP = 0x108458) (andR64R64Effect 0x108458 8 6) (Reg.operands [.gpr 8, .gpr 6] [])) #v[124, 122]
    (.letOp (n := 128) (.out 0x10845b (orR64R64Effect 0x10845b 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7] []) (.reg (.gpr 6))) #v[122, 114]
    (.letOp (n := 129) (.exec 0x10845b (fun s => s.RIP = 0x10845b) (orR64R64Effect 0x10845b 6 7) (Reg.operands [.gpr 6, .gpr 7] [])) #v[122, 114]
    (b_l1083d3_2)))))))))))))))))))))))))))))))))))))))

def bytes_l1083d3_1 : List UInt8 :=
  [0x48, 0x29, 0xFA, 0x48, 0xF7, 0xD6, 0x49, 0x89, 0xF8, 0x49, 0x21, 0xF0, 0x48, 0x09, 0xFE, 0x48,
    0x21, 0xD6, 0x4C, 0x09, 0xC6, 0x48, 0xC1, 0xEE, 0x3F, 0x48, 0x89, 0x74, 0x24, 0x08, 0x31, 0xD2,
    0x48, 0x2B, 0x54, 0x24, 0x08, 0x48, 0x8B, 0x74, 0x24, 0x20, 0x48, 0x8B, 0x7B, 0x10, 0x48, 0xC1,
    0xFA, 0x3F, 0x48, 0x01, 0xF2, 0x48, 0x29, 0xFA, 0x48, 0xF7, 0xD6, 0x49, 0x89, 0xF8, 0x49, 0x21,
    0xF0, 0x48, 0x09, 0xFE] ++ bytes_l1083d3_2

theorem code_l1083d3_1 : ∀ x ∈ codeRange 0x10841a bytes_l1083d3_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x841a 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1083d3_2

@[cfg_block] def b_l1083d3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1083d3 (movR64M64Effect 0x1083d3 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1083d3 (LoadPre 0x1083d3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1083d3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1083d3 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1083d8 (movR64M64Effect 0x1083d8 1 (.base 3 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 3] []) (.reg (.gpr 1))) #v[3]
    (.letOp (n := 56) (.exec 0x1083d8 (LoadPre 0x1083d8 (fun s => AddrMode.addr (.base 3 .none) s (0x1083d8 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1083d8 1 (.base 3 .none)) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 57) (.out 0x1083db (movR64R64Effect 0x1083db 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0] []) (.reg (.gpr 2))) #v[53]
    (.letOp (n := 58) (.exec 0x1083db (fun s => s.RIP = 0x1083db) (movR64R64Effect 0x1083db 2 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 59) (.out 0x1083de (subR64R64Effect 0x1083de 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[57, 55]
    (.letOp (n := 60) (.exec 0x1083de (fun s => s.RIP = 0x1083de) (subR64R64Effect 0x1083de 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[57, 55]
    (.letOp (n := 61) (.out 0x1083e1 (notR64Effect 0x1083e1 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 62) (.exec 0x1083e1 (fun s => s.RIP = 0x1083e1) (notR64Effect 0x1083e1 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 63) (.out 0x1083e4 (movR64R64Effect 0x1083e4 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 1] []) (.reg (.gpr 6))) #v[55]
    (.letOp (n := 64) (.exec 0x1083e4 (fun s => s.RIP = 0x1083e4) (movR64R64Effect 0x1083e4 6 1) (Reg.operands [.gpr 1] [])) #v[55]
    (.letOp (n := 65) (.out 0x1083e7 (andR64R64Effect 0x1083e7 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[63, 61]
    (.letOp (n := 66) (.exec 0x1083e7 (fun s => s.RIP = 0x1083e7) (andR64R64Effect 0x1083e7 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[63, 61]
    (.letOp (n := 67) (.out 0x1083ea (orR64R64Effect 0x1083ea 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[61, 55]
    (.letOp (n := 68) (.exec 0x1083ea (fun s => s.RIP = 0x1083ea) (orR64R64Effect 0x1083ea 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[61, 55]
    (.letOp (n := 69) (.out 0x1083ed (andR64R64Effect 0x1083ed 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[67, 59]
    (.letOp (n := 70) (.exec 0x1083ed (fun s => s.RIP = 0x1083ed) (andR64R64Effect 0x1083ed 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[67, 59]
    (.letOp (n := 71) (.out 0x1083f0 (orR64R64Effect 0x1083f0 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[69, 65]
    (.letOp (n := 72) (.exec 0x1083f0 (fun s => s.RIP = 0x1083f0) (orR64R64Effect 0x1083f0 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[69, 65]
    (.letOp (n := 73) (.out 0x1083f3 (shrR64Effect 0x1083f3 4 0 63) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[71]
    (.letOp (n := 74) (.exec 0x1083f3 (fun s => s.RIP = 0x1083f3) (shrR64Effect 0x1083f3 4 0 63) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[71]
    (.letOp (n := 75) (.exec 0x1083f7 (StorePre 0x1083f7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1083f7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1083f7 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[73, 4]
    (.letOp (n := 76) (.exec 0x1083fc (fun s => s.RIP = 0x1083fc) (leaR64Effect 0x1083fc 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 77) (.out 0x108401 (xorR32R32Effect 0x108401 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[55, 55]
    (.letOp (n := 78) (.exec 0x108401 (fun s => s.RIP = 0x108401) (xorR32R32Effect 0x108401 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[55, 55]
    (.letOp (n := 79) (.out 0x108403 (xorR32R32Effect 0x108403 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[59, 59]
    (.letOp (n := 80) (.exec 0x108403 (fun s => s.RIP = 0x108403) (xorR32R32Effect 0x108403 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[59, 59]
    (.letOp (n := 81) (.out 0x108405 (subR64M64Effect 0x108405 2 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 4] []) (.reg (.gpr 2))) #v[79, 4]
    (.letOp (n := 82) (.exec 0x108405 (LoadPre 0x108405 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x108405 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x108405 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[79, 4]
    (.letOp (n := 83) (.out 0x10840a (movR64M64Effect 0x10840a 6 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 84) (.exec 0x10840a (LoadPre 0x10840a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10840a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10840a 6 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 85) (.out 0x10840f (movR64M64Effect 0x10840f 7 (.base 3 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 86) (.exec 0x10840f (LoadPre 0x10840f (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x10840f + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10840f 7 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 87) (.out 0x108413 (sarR64Effect 0x108413 4 2 63) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[81]
    (.letOp (n := 88) (.exec 0x108413 (fun s => s.RIP = 0x108413) (sarR64Effect 0x108413 4 2 63) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[81]
    (.letOp (n := 89) (.out 0x108417 (addR64R64Effect 0x108417 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[87, 83]
    (.letOp (n := 90) (.exec 0x108417 (fun s => s.RIP = 0x108417) (addR64R64Effect 0x108417 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[87, 83]
    (b_l1083d3_1))))))))))))))))))))))))))))))))))))))

def bytes_l1083d3 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x10, 0x48, 0x8B, 0x0B, 0x48, 0x89, 0xC2, 0x48, 0x29, 0xCA, 0x48, 0xF7,
    0xD0, 0x48, 0x89, 0xCE, 0x48, 0x21, 0xC6, 0x48, 0x09, 0xC8, 0x48, 0x21, 0xD0, 0x48, 0x09, 0xF0,
    0x48, 0xC1, 0xE8, 0x3F, 0x48, 0x89, 0x44, 0x24, 0x08, 0x48, 0x8D, 0x44, 0x24, 0x08, 0x31, 0xC9,
    0x31, 0xD2, 0x48, 0x2B, 0x54, 0x24, 0x08, 0x48, 0x8B, 0x74, 0x24, 0x18, 0x48, 0x8B, 0x7B, 0x08,
    0x48, 0xC1, 0xFA, 0x3F, 0x48, 0x01, 0xF2] ++ bytes_l1083d3_1

theorem code_l1083d3 : ∀ x ∈ codeRange 0x1083d3 bytes_l1083d3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x83d3 71 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1083d3_1

@[cfg_block] def b_l1084af : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1084af (addR64Imm8Effect 0x1084af 4 0x50) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 54) (.exec 0x1084af (fun s => s.RIP = 0x1084af) (addR64Imm8Effect 0x1084af 4 0x50) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1084b3 (popR64Effect 0x1084b3 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[53]
    (.letOp (n := 56) (.out 0x1084b3 (popR64Effect 0x1084b3 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[53]
    (.letOp (n := 57) (.exec 0x1084b3 (PopPre 0x1084b3) (popR64Effect 0x1084b3 1 3) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 58) (.out 0x1084b4 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[56]
    (.letOp (n := 59) (.out 0x1084b4 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[56]
    (.letOp (n := 60) (.exec 0x1084b4 (RetPre 0x1084b4) (retEffect) (Reg.operands [.gpr 4] [])) #v[56]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 2), (3, 55), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 61) (some ⟨58, by decide⟩))))))))))

def bytes_l1084af : List UInt8 :=
  [0x48, 0x83, 0xC4, 0x50, 0x5B, 0xC3]

theorem code_l1084af : ∀ x ∈ codeRange 0x1084af bytes_l1084af, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x84af 6 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1084c0 : Block Op Label signature Reg.count 53 :=
  .terminate (.br ⟨.l1286b0, RegMap.args (entryMap (live .l1084c0)) 53⟩)

def bytes_l1084c0 : List UInt8 :=
  [0xE9, 0xEB, 0x01, 0x02, 0x00]

theorem code_l1084c0 : ∀ x ∈ codeRange 0x1084c0 bytes_l1084c0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x84c0 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1084d0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1084d0 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[4]
    (.letOp (n := 54) (.out 0x1084d0 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 55) (.exec 0x1084d0 (RetPre 0x1084d0) (retEffect) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 54), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 56) (some ⟨53, by decide⟩)))))

def bytes_l1084d0 : List UInt8 :=
  [0xC3]

theorem code_l1084d0 : ∀ x ∈ codeRange 0x1084d0 bytes_l1084d0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x84d0 1 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

def b_l1084e0_13 : Block Op Label signature Reg.count 554 :=
  .letOp (n := 554) (.out 0x10885c (andR8M8Effect 0x10885c 4 1 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 4] []) (.reg (.gpr 1))) #v[552, 65]
    (.letOp (n := 555) (.exec 0x10885c (LoadPre 0x10885c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10885c + BitVec.ofNat 64 4)) 1) (andR8M8Effect 0x10885c 4 1 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[552, 65]
    (.letOp (n := 556) (.exec 0x108860 (StorePre 0x108860 3 (fun s => AddrMode.addr (.base 7 .none) s (0x108860 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x108860 6 (.base 7 .none)) (Reg.operands [.gpr 6, .gpr 7] [])) #v[501, 7]
    (.letOp (n := 557) (.exec 0x108863 (StorePre 0x108863 4 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x108863 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x108863 0 (.base 7 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 7] [])) #v[512, 7]
    (.letOp (n := 558) (.exec 0x108867 (StorePre 0x108867 4 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x108867 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x108867 8 (.base 7 (.d8 0x10))) (Reg.operands [.gpr 8, .gpr 7] [])) #v[523, 7]
    (.letOp (n := 559) (.exec 0x10886b (StorePre 0x10886b 4 (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x10886b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10886b 9 (.base 7 (.d8 0x18))) (Reg.operands [.gpr 9, .gpr 7] [])) #v[534, 7]
    (.letOp (n := 560) (.exec 0x10886f (StorePre 0x10886f 4 (fun s => AddrMode.addr (.base 7 (.d8 0x20)) s (0x10886f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10886f 10 (.base 7 (.d8 0x20))) (Reg.operands [.gpr 10, .gpr 7] [])) #v[546, 7]
    (.letOp (n := 561) (.out 0x108873 (movR64R64Effect 0x108873 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[550]
    (.letOp (n := 562) (.exec 0x108873 (fun s => s.RIP = 0x108873) (movR64R64Effect 0x108873 0 2) (Reg.operands [.gpr 2] [])) #v[550]
    (.letOp (n := 563) (.out 0x108876 (orR8R8Effect 0x108876 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[561, 554]
    (.letOp (n := 564) (.exec 0x108876 (fun s => s.RIP = 0x108876) (orR8R8Effect 0x108876 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[561, 554]
    (.letOp (n := 565) (.exec 0x108878 (StorePre 0x108878 3 (fun s => AddrMode.addr (.base 7 (.d8 0x28)) s (0x108878 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x108878 3 0 (.base 7 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 7] [])) #v[563, 7]
    (.letOp (n := 566) (.out 0x10887b (addR64Imm8Effect 0x10887b 4 0x40) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 567) (.exec 0x10887b (fun s => s.RIP = 0x10887b) (addR64Imm8Effect 0x10887b 4 0x40) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 568) (.out 0x10887f (popR64Effect 0x10887f 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[566]
    (.letOp (n := 569) (.out 0x10887f (popR64Effect 0x10887f 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[566]
    (.letOp (n := 570) (.exec 0x10887f (PopPre 0x10887f) (popR64Effect 0x10887f 1 3) (Reg.operands [.gpr 4] [])) #v[566]
    (.letOp (n := 571) (.out 0x108880 (popR64Effect 0x108880 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[569]
    (.letOp (n := 572) (.out 0x108880 (popR64Effect 0x108880 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[569]
    (.letOp (n := 573) (.exec 0x108880 (PopPre 0x108880) (popR64Effect 0x108880 2 12) (Reg.operands [.gpr 4] [])) #v[569]
    (.letOp (n := 574) (.out 0x108882 (popR64Effect 0x108882 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[572]
    (.letOp (n := 575) (.out 0x108882 (popR64Effect 0x108882 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[572]
    (.letOp (n := 576) (.exec 0x108882 (PopPre 0x108882) (popR64Effect 0x108882 2 13) (Reg.operands [.gpr 4] [])) #v[572]
    (.letOp (n := 577) (.out 0x108884 (popR64Effect 0x108884 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[575]
    (.letOp (n := 578) (.out 0x108884 (popR64Effect 0x108884 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[575]
    (.letOp (n := 579) (.exec 0x108884 (PopPre 0x108884) (popR64Effect 0x108884 2 14) (Reg.operands [.gpr 4] [])) #v[575]
    (.letOp (n := 580) (.out 0x108886 (popR64Effect 0x108886 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[578]
    (.letOp (n := 581) (.out 0x108886 (popR64Effect 0x108886 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[578]
    (.letOp (n := 582) (.exec 0x108886 (PopPre 0x108886) (popR64Effect 0x108886 2 15) (Reg.operands [.gpr 4] [])) #v[578]
    (.letOp (n := 583) (.out 0x108888 (popR64Effect 0x108888 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[581]
    (.letOp (n := 584) (.out 0x108888 (popR64Effect 0x108888 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[581]
    (.letOp (n := 585) (.exec 0x108888 (PopPre 0x108888) (popR64Effect 0x108888 1 5) (Reg.operands [.gpr 4] [])) #v[581]
    (.letOp (n := 586) (.out 0x108889 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[584]
    (.letOp (n := 587) (.out 0x108889 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[584]
    (.letOp (n := 588) (.exec 0x108889 (RetPre 0x108889) (retEffect) (Reg.operands [.gpr 4] [])) #v[584]
    (.terminate (.ret (RegMap.args [(0, 563), (1, 554), (2, 550), (3, 568), (4, 587), (5, 583), (6, 501), (7, 7), (8, 523), (9, 534), (10, 546), (11, 517), (12, 571), (13, 574), (14, 577), (15, 580), (22, 22), (39, 39), (50, 50), (51, 51)] 589) (some ⟨586, by decide⟩)))))))))))))))))))))))))))))))))))))

def bytes_l1084e0_13 : List UInt8 :=
  [0x22, 0x4C, 0x24, 0x20, 0x48, 0x89, 0x37, 0x48, 0x89, 0x47, 0x08, 0x4C, 0x89, 0x47, 0x10, 0x4C,
    0x89, 0x4F, 0x18, 0x4C, 0x89, 0x57, 0x20, 0x48, 0x89, 0xD0, 0x08, 0xC8, 0x88, 0x47, 0x28, 0x48,
    0x83, 0xC4, 0x40, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l1084e0_13 : ∀ x ∈ codeRange 0x10885c bytes_l1084e0_13, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x885c 46 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

def b_l1084e0_12 : Block Op Label signature Reg.count 517 :=
  .letOp (n := 517) (.out 0x10881b (xorR64R64Effect 0x10881b 11 9) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 9] []) (.reg (.gpr 11))) #v[473, 357]
    (.letOp (n := 518) (.exec 0x10881b (fun s => s.RIP = 0x10881b) (xorR64R64Effect 0x10881b 11 9) (Reg.operands [.gpr 11, .gpr 9] [])) #v[473, 357]
    (.letOp (n := 519) (.out 0x10881e (negR64Effect 0x10881e 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[515]
    (.letOp (n := 520) (.exec 0x10881e (fun s => s.RIP = 0x10881e) (negR64Effect 0x10881e 8) (Reg.operands [.gpr 8] [])) #v[515]
    (.letOp (n := 521) (.out 0x108821 (andR64R64Effect 0x108821 8 11) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 11] []) (.reg (.gpr 8))) #v[519, 517]
    (.letOp (n := 522) (.exec 0x108821 (fun s => s.RIP = 0x108821) (andR64R64Effect 0x108821 8 11) (Reg.operands [.gpr 8, .gpr 11] [])) #v[519, 517]
    (.letOp (n := 523) (.out 0x108824 (xorR64R64Effect 0x108824 8 9) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 9] []) (.reg (.gpr 8))) #v[521, 357]
    (.letOp (n := 524) (.exec 0x108824 (fun s => s.RIP = 0x108824) (xorR64R64Effect 0x108824 8 9) (Reg.operands [.gpr 8, .gpr 9] [])) #v[521, 357]
    (.letOp (n := 525) (.exec 0x108827 (StorePre 0x108827 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108827 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x108827 3 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 1, .gpr 4] [])) #v[459, 65]
    (.letOp (n := 526) (.out 0x10882a (movzxR32M8Effect 0x10882a 5 9 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[65]
    (.letOp (n := 527) (.exec 0x10882a (LoadPre 0x10882a (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10882a + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10882a 5 9 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 528) (.out 0x10882f (xorR64R64Effect 0x10882f 13 10) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 10] []) (.reg (.gpr 13))) #v[476, 384]
    (.letOp (n := 529) (.exec 0x10882f (fun s => s.RIP = 0x10882f) (xorR64R64Effect 0x10882f 13 10) (Reg.operands [.gpr 13, .gpr 10] [])) #v[476, 384]
    (.letOp (n := 530) (.out 0x108832 (negR64Effect 0x108832 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[526]
    (.letOp (n := 531) (.exec 0x108832 (fun s => s.RIP = 0x108832) (negR64Effect 0x108832 9) (Reg.operands [.gpr 9] [])) #v[526]
    (.letOp (n := 532) (.out 0x108835 (andR64R64Effect 0x108835 9 13) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 13] []) (.reg (.gpr 9))) #v[530, 528]
    (.letOp (n := 533) (.exec 0x108835 (fun s => s.RIP = 0x108835) (andR64R64Effect 0x108835 9 13) (Reg.operands [.gpr 9, .gpr 13] [])) #v[530, 528]
    (.letOp (n := 534) (.out 0x108838 (xorR64R64Effect 0x108838 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[532, 384]
    (.letOp (n := 535) (.exec 0x108838 (fun s => s.RIP = 0x108838) (xorR64R64Effect 0x108838 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[532, 384]
    (.letOp (n := 536) (.exec 0x10883b (StorePre 0x10883b 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10883b + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10883b 3 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 1, .gpr 4] [])) #v[459, 65]
    (.letOp (n := 537) (.exec 0x10883e (fun s => s.RIP = 0x10883e) (movR64R64Effect 0x10883e 10 4) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 538) (.out 0x108841 (movzxR32M8Effect 0x108841 5 10 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[65]
    (.letOp (n := 539) (.exec 0x108841 (LoadPre 0x108841 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108841 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x108841 5 10 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 540) (.out 0x108846 (xorR64R64Effect 0x108846 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 3] []) (.reg (.gpr 2))) #v[489, 439]
    (.letOp (n := 541) (.exec 0x108846 (fun s => s.RIP = 0x108846) (xorR64R64Effect 0x108846 2 3) (Reg.operands [.gpr 2, .gpr 3] [])) #v[489, 439]
    (.letOp (n := 542) (.out 0x108849 (negR64Effect 0x108849 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[538]
    (.letOp (n := 543) (.exec 0x108849 (fun s => s.RIP = 0x108849) (negR64Effect 0x108849 10) (Reg.operands [.gpr 10] [])) #v[538]
    (.letOp (n := 544) (.out 0x10884c (andR64R64Effect 0x10884c 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2] []) (.reg (.gpr 10))) #v[542, 540]
    (.letOp (n := 545) (.exec 0x10884c (fun s => s.RIP = 0x10884c) (andR64R64Effect 0x10884c 10 2) (Reg.operands [.gpr 10, .gpr 2] [])) #v[542, 540]
    (.letOp (n := 546) (.out 0x10884f (xorR64R64Effect 0x10884f 10 3) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 3] []) (.reg (.gpr 10))) #v[544, 439]
    (.letOp (n := 547) (.exec 0x10884f (fun s => s.RIP = 0x10884f) (xorR64R64Effect 0x10884f 10 3) (Reg.operands [.gpr 10, .gpr 3] [])) #v[544, 439]
    (.letOp (n := 548) (.out 0x108852 (movR64M64Effect 0x108852 2 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[65]
    (.letOp (n := 549) (.exec 0x108852 (LoadPre 0x108852 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x108852 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x108852 2 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 550) (.out 0x108857 (andR8R8Effect 0x108857 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[548, 459]
    (.letOp (n := 551) (.exec 0x108857 (fun s => s.RIP = 0x108857) (andR8R8Effect 0x108857 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[548, 459]
    (.letOp (n := 552) (.out 0x108859 (xorR8Imm8Effect 0x108859 3 1 0x1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[459]
    (.letOp (n := 553) (.exec 0x108859 (fun s => s.RIP = 0x108859) (xorR8Imm8Effect 0x108859 3 1 0x1) (Reg.operands [.gpr 1] [])) #v[459]
    (b_l1084e0_13)))))))))))))))))))))))))))))))))))))

def bytes_l1084e0_12 : List UInt8 :=
  [0x4D, 0x31, 0xCB, 0x49, 0xF7, 0xD8, 0x4D, 0x21, 0xD8, 0x4D, 0x31, 0xC8, 0x88, 0x0C, 0x24, 0x44,
    0x0F, 0xB6, 0x0C, 0x24, 0x4D, 0x31, 0xD5, 0x49, 0xF7, 0xD9, 0x4D, 0x21, 0xE9, 0x4D, 0x31, 0xD1,
    0x88, 0x0C, 0x24, 0x49, 0x89, 0xE2, 0x44, 0x0F, 0xB6, 0x14, 0x24, 0x48, 0x31, 0xDA, 0x49, 0xF7,
    0xDA, 0x49, 0x21, 0xD2, 0x49, 0x31, 0xDA, 0x48, 0x8B, 0x54, 0x24, 0x18, 0x20, 0xCA, 0x80, 0xF1,
    0x01] ++ bytes_l1084e0_13

theorem code_l1084e0_12 : ∀ x ∈ codeRange 0x10881b bytes_l1084e0_12, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x881b 65 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1084e0_13

def b_l1084e0_11 : Block Op Label signature Reg.count 483 :=
  .letOp (n := 483) (.exec 0x1087d9 (StorePre 0x1087d9 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1087d9 + BitVec.ofNat 64 4)) 1) (atFlags (condHolds 3) (setccM8Effect 0x1087d9 4 (.sib 4 none 0 .none))) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[65, 477]
    (.letOp (n := 484) (.exec 0x1087dd (fun s => s.RIP = 0x1087dd) (movR64R64Effect 0x1087dd 2 4) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 485) (.out 0x1087e0 (movzxR32M8Effect 0x1087e0 4 2 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[65]
    (.letOp (n := 486) (.exec 0x1087e0 (LoadPre 0x1087e0 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1087e0 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x1087e0 4 2 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 487) (.out 0x1087e4 (andR32Imm8Effect 0x1087e4 3 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[485]
    (.letOp (n := 488) (.exec 0x1087e4 (fun s => s.RIP = 0x1087e4) (andR32Imm8Effect 0x1087e4 3 2 0x1) (Reg.operands [.gpr 2] [])) #v[485]
    (.letOp (n := 489) (.out 0x1087e7 (addR64R64Effect 0x1087e7 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[487, 481]
    (.letOp (n := 490) (.exec 0x1087e7 (fun s => s.RIP = 0x1087e7) (addR64R64Effect 0x1087e7 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[487, 481]
    (.letOp (n := 491) (.exec 0x1087ea (StorePre 0x1087ea 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1087ea + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x1087ea 3 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 1, .gpr 4] [])) #v[459, 65]
    (.letOp (n := 492) (.exec 0x1087ed (fun s => s.RIP = 0x1087ed) (movR64R64Effect 0x1087ed 15 4) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 493) (.out 0x1087f0 (xorR64R64Effect 0x1087f0 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 0] []) (.reg (.gpr 12))) #v[463, 300]
    (.letOp (n := 494) (.exec 0x1087f0 (fun s => s.RIP = 0x1087f0) (xorR64R64Effect 0x1087f0 12 0) (Reg.operands [.gpr 12, .gpr 0] [])) #v[463, 300]
    (.letOp (n := 495) (.out 0x1087f3 (movzxR32M8Effect 0x1087f3 4 6 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[65]
    (.letOp (n := 496) (.exec 0x1087f3 (LoadPre 0x1087f3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1087f3 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x1087f3 4 6 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 497) (.out 0x1087f7 (negR64Effect 0x1087f7 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[495]
    (.letOp (n := 498) (.exec 0x1087f7 (fun s => s.RIP = 0x1087f7) (negR64Effect 0x1087f7 6) (Reg.operands [.gpr 6] [])) #v[495]
    (.letOp (n := 499) (.out 0x1087fa (andR64R64Effect 0x1087fa 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 12] []) (.reg (.gpr 6))) #v[497, 493]
    (.letOp (n := 500) (.exec 0x1087fa (fun s => s.RIP = 0x1087fa) (andR64R64Effect 0x1087fa 6 12) (Reg.operands [.gpr 6, .gpr 12] [])) #v[497, 493]
    (.letOp (n := 501) (.out 0x1087fd (xorR64R64Effect 0x1087fd 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[499, 300]
    (.letOp (n := 502) (.exec 0x1087fd (fun s => s.RIP = 0x1087fd) (xorR64R64Effect 0x1087fd 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[499, 300]
    (.letOp (n := 503) (.exec 0x108800 (StorePre 0x108800 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108800 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x108800 3 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 1, .gpr 4] [])) #v[459, 65]
    (.letOp (n := 504) (.out 0x108803 (movzxR32M8Effect 0x108803 4 0 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 505) (.exec 0x108803 (LoadPre 0x108803 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108803 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x108803 4 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 506) (.out 0x108807 (xorR64R64Effect 0x108807 14 8) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 8] []) (.reg (.gpr 14))) #v[468, 330]
    (.letOp (n := 507) (.exec 0x108807 (fun s => s.RIP = 0x108807) (xorR64R64Effect 0x108807 14 8) (Reg.operands [.gpr 14, .gpr 8] [])) #v[468, 330]
    (.letOp (n := 508) (.out 0x10880a (negR64Effect 0x10880a 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[504]
    (.letOp (n := 509) (.exec 0x10880a (fun s => s.RIP = 0x10880a) (negR64Effect 0x10880a 0) (Reg.operands [.gpr 0] [])) #v[504]
    (.letOp (n := 510) (.out 0x10880d (andR64R64Effect 0x10880d 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[508, 506]
    (.letOp (n := 511) (.exec 0x10880d (fun s => s.RIP = 0x10880d) (andR64R64Effect 0x10880d 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[508, 506]
    (.letOp (n := 512) (.out 0x108810 (xorR64R64Effect 0x108810 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 8] []) (.reg (.gpr 0))) #v[510, 330]
    (.letOp (n := 513) (.exec 0x108810 (fun s => s.RIP = 0x108810) (xorR64R64Effect 0x108810 0 8) (Reg.operands [.gpr 0, .gpr 8] [])) #v[510, 330]
    (.letOp (n := 514) (.exec 0x108813 (StorePre 0x108813 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108813 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x108813 3 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 1, .gpr 4] [])) #v[459, 65]
    (.letOp (n := 515) (.out 0x108816 (movzxR32M8Effect 0x108816 5 8 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[65]
    (.letOp (n := 516) (.exec 0x108816 (LoadPre 0x108816 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108816 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x108816 5 8 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (b_l1084e0_12))))))))))))))))))))))))))))))))))

def bytes_l1084e0_11 : List UInt8 :=
  [0x0F, 0x93, 0x04, 0x24, 0x48, 0x89, 0xE2, 0x0F, 0xB6, 0x14, 0x24, 0x83, 0xE2, 0x01, 0x48, 0x01,
    0xF2, 0x88, 0x0C, 0x24, 0x49, 0x89, 0xE7, 0x49, 0x31, 0xC4, 0x0F, 0xB6, 0x34, 0x24, 0x48, 0xF7,
    0xDE, 0x4C, 0x21, 0xE6, 0x48, 0x31, 0xC6, 0x88, 0x0C, 0x24, 0x0F, 0xB6, 0x04, 0x24, 0x4D, 0x31,
    0xC6, 0x48, 0xF7, 0xD8, 0x4C, 0x21, 0xF0, 0x4C, 0x31, 0xC0, 0x88, 0x0C, 0x24, 0x44, 0x0F, 0xB6,
    0x04, 0x24] ++ bytes_l1084e0_12

theorem code_l1084e0_11 : ∀ x ∈ codeRange 0x1087d9 bytes_l1084e0_11, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x87d9 66 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1084e0_12

def b_l1084e0_10 : Block Op Label signature Reg.count 441 :=
  .letOp (n := 441) (.out 0x10878d (andR64R64Effect 0x10878d 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 3] []) (.reg (.gpr 1))) #v[435, 439]
    (.letOp (n := 442) (.exec 0x10878d (fun s => s.RIP = 0x10878d) (andR64R64Effect 0x10878d 1 3) (Reg.operands [.gpr 1, .gpr 3] [])) #v[435, 439]
    (.letOp (n := 443) (.out 0x108790 (orR64R64Effect 0x108790 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[441, 433]
    (.letOp (n := 444) (.exec 0x108790 (fun s => s.RIP = 0x108790) (orR64R64Effect 0x108790 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[441, 433]
    (.letOp (n := 445) (.out 0x108793 (shrR64Effect 0x108793 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[443]
    (.letOp (n := 446) (.exec 0x108793 (fun s => s.RIP = 0x108793) (shrR64Effect 0x108793 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[443]
    (.letOp (n := 447) (.exec 0x108797 (StorePre 0x108797 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108797 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x108797 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 1, .gpr 4] [])) #v[445, 65]
    (.letOp (n := 448) (.exec 0x10879b (fun s => s.RIP = 0x10879b) (movR64R64Effect 0x10879b 1 4) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 449) (.out 0x10879e (movzxR32M8Effect 0x10879e 5 1 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 450) (.exec 0x10879e (LoadPre 0x10879e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10879e + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10879e 5 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 451) (.out 0x1087a3 (andR8Imm8Effect 0x1087a3 3 1 0x1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[449]
    (.letOp (n := 452) (.exec 0x1087a3 (fun s => s.RIP = 0x1087a3) (andR8Imm8Effect 0x1087a3 3 1 0x1) (Reg.operands [.gpr 1] [])) #v[449]
    (.letOp (n := 453) (.out 0x1087a6 (cmpMImm8Effect 0x1087a6 5 64 (.sib 4 none 0 .none) 0x0) (EffectPart.reads (.flag .ZF) [.gpr 4] []) (.flag .ZF)) #v[65]
    (.letOp (n := 454) (.exec 0x1087a6 (LoadPre 0x1087a6 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1087a6 + BitVec.ofNat 64 5)) 8) (cmpMImm8Effect 0x1087a6 5 64 (.sib 4 none 0 .none) 0x0) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 455) (.out 0x1087ab (movzxR32R8Effect 0x1087ab 3 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[451]
    (.letOp (n := 456) (.exec 0x1087ab (fun s => s.RIP = 0x1087ab) (movzxR32R8Effect 0x1087ab 3 1 1) (Reg.operands [.gpr 1] [])) #v[451]
    (.letOp (n := 457) (.out 0x1087ae (movR32Imm32Effect 0x1087ae 6 13 0x0) (EffectPart.reads (.reg (.gpr 13)) [] []) (.reg (.gpr 13))) #v[]
    (.letOp (n := 458) (.exec 0x1087ae (fun s => s.RIP = 0x1087ae) (movR32Imm32Effect 0x1087ae 6 13 0x0) (Reg.operands [] [])) #v[]
    (.letOp (n := 459) (.out 0x1087b4 (atFlags (condHolds 4) (cmovR32R32Effect 0x1087b4 4 1 13)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 1))) #v[455, 457, 453]
    (.letOp (n := 460) (.exec 0x1087b4 (fun s => s.RIP = 0x1087b4) (atFlags (condHolds 4) (cmovR32R32Effect 0x1087b4 4 1 13)) (Reg.operands [.gpr 1, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[455, 457, 453]
    (.letOp (n := 461) (.out 0x1087b8 (movR64R64Effect 0x1087b8 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[300]
    (.letOp (n := 462) (.exec 0x1087b8 (fun s => s.RIP = 0x1087b8) (movR64R64Effect 0x1087b8 12 0) (Reg.operands [.gpr 0] [])) #v[300]
    (.letOp (n := 463) (.out 0x1087bb (negR64Effect 0x1087bb 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[461]
    (.letOp (n := 464) (.out 0x1087bb (negR64Effect 0x1087bb 12) (EffectPart.reads (.flag .CF) [.gpr 12] []) (.flag .CF)) #v[461]
    (.letOp (n := 465) (.exec 0x1087bb (fun s => s.RIP = 0x1087bb) (negR64Effect 0x1087bb 12) (Reg.operands [.gpr 12] [])) #v[461]
    (.letOp (n := 466) (.out 0x1087be (movR32Imm32Effect 0x1087be 6 14 0x0) (EffectPart.reads (.reg (.gpr 14)) [] []) (.reg (.gpr 14))) #v[]
    (.letOp (n := 467) (.exec 0x1087be (fun s => s.RIP = 0x1087be) (movR32Imm32Effect 0x1087be 6 14 0x0) (Reg.operands [] [])) #v[]
    (.letOp (n := 468) (.out 0x1087c4 (atFlags StatusFlags.CF (sbbR64R64Effect 0x1087c4 14 8)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[466, 330, 464]
    (.letOp (n := 469) (.out 0x1087c4 (atFlags StatusFlags.CF (sbbR64R64Effect 0x1087c4 14 8)) (Reg.operands [.gpr 14, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[466, 330, 464]
    (.letOp (n := 470) (.exec 0x1087c4 (fun s => s.RIP = 0x1087c4) (atFlags StatusFlags.CF (sbbR64R64Effect 0x1087c4 14 8)) (Reg.operands [.gpr 14, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[466, 330, 464]
    (.letOp (n := 471) (.out 0x1087c7 (movR32Imm32Effect 0x1087c7 6 11 0x0) (EffectPart.reads (.reg (.gpr 11)) [] []) (.reg (.gpr 11))) #v[]
    (.letOp (n := 472) (.exec 0x1087c7 (fun s => s.RIP = 0x1087c7) (movR32Imm32Effect 0x1087c7 6 11 0x0) (Reg.operands [] [])) #v[]
    (.letOp (n := 473) (.out 0x1087cd (atFlags StatusFlags.CF (sbbR64R64Effect 0x1087cd 11 9)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[471, 357, 469]
    (.letOp (n := 474) (.out 0x1087cd (atFlags StatusFlags.CF (sbbR64R64Effect 0x1087cd 11 9)) (Reg.operands [.gpr 11, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[471, 357, 469]
    (.letOp (n := 475) (.exec 0x1087cd (fun s => s.RIP = 0x1087cd) (atFlags StatusFlags.CF (sbbR64R64Effect 0x1087cd 11 9)) (Reg.operands [.gpr 11, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[471, 357, 469]
    (.letOp (n := 476) (.out 0x1087d0 (atFlags StatusFlags.CF (sbbR64R64Effect 0x1087d0 13 10)) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 13))) #v[457, 384, 474]
    (.letOp (n := 477) (.out 0x1087d0 (atFlags StatusFlags.CF (sbbR64R64Effect 0x1087d0 13 10)) (Reg.operands [.gpr 13, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[457, 384, 474]
    (.letOp (n := 478) (.exec 0x1087d0 (fun s => s.RIP = 0x1087d0) (atFlags StatusFlags.CF (sbbR64R64Effect 0x1087d0 13 10)) (Reg.operands [.gpr 13, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[457, 384, 474]
    (.letOp (n := 479) (.out 0x1087d3 (movR64R64Effect 0x1087d3 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[439]
    (.letOp (n := 480) (.exec 0x1087d3 (fun s => s.RIP = 0x1087d3) (movR64R64Effect 0x1087d3 6 3) (Reg.operands [.gpr 3] [])) #v[439]
    (.letOp (n := 481) (.out 0x1087d6 (notR64Effect 0x1087d6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[479]
    (.letOp (n := 482) (.exec 0x1087d6 (fun s => s.RIP = 0x1087d6) (notR64Effect 0x1087d6 6) (Reg.operands [.gpr 6] [])) #v[479]
    (b_l1084e0_11))))))))))))))))))))))))))))))))))))))))))

def bytes_l1084e0_10 : List UInt8 :=
  [0x48, 0x21, 0xD9, 0x48, 0x09, 0xF1, 0x48, 0xC1, 0xE9, 0x3F, 0x48, 0x89, 0x0C, 0x24, 0x48, 0x89,
    0xE1, 0x0F, 0xB6, 0x4C, 0x24, 0x10, 0x80, 0xE1, 0x01, 0x48, 0x83, 0x3C, 0x24, 0x00, 0x0F, 0xB6,
    0xC9, 0x41, 0xBD, 0x00, 0x00, 0x00, 0x00, 0x41, 0x0F, 0x44, 0xCD, 0x49, 0x89, 0xC4, 0x49, 0xF7,
    0xDC, 0x41, 0xBE, 0x00, 0x00, 0x00, 0x00, 0x4D, 0x19, 0xC6, 0x41, 0xBB, 0x00, 0x00, 0x00, 0x00,
    0x4D, 0x19, 0xCB, 0x4D, 0x19, 0xD5, 0x48, 0x89, 0xDE, 0x48, 0xF7, 0xD6] ++ bytes_l1084e0_11

theorem code_l1084e0_10 : ∀ x ∈ codeRange 0x10878d bytes_l1084e0_10, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x878d 76 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1084e0_11

def b_l1084e0_9 : Block Op Label signature Reg.count 401 :=
  .letOp (n := 401) (.out 0x10874b (xorR32R32Effect 0x10874b 2 3 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 3] []) (.reg (.gpr 3))) #v[398, 398]
    (.letOp (n := 402) (.exec 0x10874b (fun s => s.RIP = 0x10874b) (xorR32R32Effect 0x10874b 2 3 3) (Reg.operands [.gpr 3, .gpr 3] [])) #v[398, 398]
    (.letOp (n := 403) (.out 0x10874d (subR64M64Effect 0x10874d 3 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 4] []) (.reg (.gpr 3))) #v[401, 65]
    (.letOp (n := 404) (.exec 0x10874d (LoadPre 0x10874d (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10874d + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x10874d 3 (.sib 4 none 0 .none)) (Reg.operands [.gpr 3, .gpr 4] [])) #v[401, 65]
    (.letOp (n := 405) (.out 0x108751 (movR64M64Effect 0x108751 11 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[65]
    (.letOp (n := 406) (.exec 0x108751 (LoadPre 0x108751 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x108751 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x108751 11 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 407) (.out 0x108756 (andR32Imm8Effect 0x108756 4 11 0x1) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11] []) (.reg (.gpr 11))) #v[405]
    (.letOp (n := 408) (.exec 0x108756 (fun s => s.RIP = 0x108756) (andR32Imm8Effect 0x108756 4 11 0x1) (Reg.operands [.gpr 11] [])) #v[405]
    (.letOp (n := 409) (.out 0x10875a (movR64M64Effect 0x10875a 6 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[65]
    (.letOp (n := 410) (.exec 0x10875a (LoadPre 0x10875a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10875a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10875a 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 411) (.out 0x10875f (movR64R64Effect 0x10875f 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6] []) (.reg (.gpr 2))) #v[409]
    (.letOp (n := 412) (.exec 0x10875f (fun s => s.RIP = 0x10875f) (movR64R64Effect 0x10875f 2 6) (Reg.operands [.gpr 6] [])) #v[409]
    (.letOp (n := 413) (.out 0x108762 (notR64Effect 0x108762 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[411]
    (.letOp (n := 414) (.exec 0x108762 (fun s => s.RIP = 0x108762) (notR64Effect 0x108762 2) (Reg.operands [.gpr 2] [])) #v[411]
    (.letOp (n := 415) (.out 0x108765 (addR64R64Effect 0x108765 2 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 11] []) (.reg (.gpr 2))) #v[413, 407]
    (.letOp (n := 416) (.exec 0x108765 (fun s => s.RIP = 0x108765) (addR64R64Effect 0x108765 2 11) (Reg.operands [.gpr 2, .gpr 11] [])) #v[413, 407]
    (.letOp (n := 417) (.out 0x108768 (xorR64R64Effect 0x108768 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[415, 409]
    (.letOp (n := 418) (.exec 0x108768 (fun s => s.RIP = 0x108768) (xorR64R64Effect 0x108768 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[415, 409]
    (.letOp (n := 419) (.out 0x10876b (negR64Effect 0x10876b 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14] []) (.reg (.gpr 14))) #v[316]
    (.letOp (n := 420) (.exec 0x10876b (fun s => s.RIP = 0x10876b) (negR64Effect 0x10876b 14) (Reg.operands [.gpr 14] [])) #v[316]
    (.letOp (n := 421) (.out 0x10876e (andR64R64Effect 0x10876e 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 2] []) (.reg (.gpr 14))) #v[419, 417]
    (.letOp (n := 422) (.exec 0x10876e (fun s => s.RIP = 0x10876e) (andR64R64Effect 0x10876e 14 2) (Reg.operands [.gpr 14, .gpr 2] [])) #v[419, 417]
    (.letOp (n := 423) (.out 0x108771 (xorR64R64Effect 0x108771 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 6] []) (.reg (.gpr 14))) #v[421, 409]
    (.letOp (n := 424) (.exec 0x108771 (fun s => s.RIP = 0x108771) (xorR64R64Effect 0x108771 14 6) (Reg.operands [.gpr 14, .gpr 6] [])) #v[421, 409]
    (.letOp (n := 425) (.out 0x108774 (movR64R64Effect 0x108774 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[156]
    (.letOp (n := 426) (.exec 0x108774 (fun s => s.RIP = 0x108774) (movR64R64Effect 0x108774 2 1) (Reg.operands [.gpr 1] [])) #v[156]
    (.letOp (n := 427) (.out 0x108777 (subR64R64Effect 0x108777 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 14] []) (.reg (.gpr 2))) #v[425, 423]
    (.letOp (n := 428) (.exec 0x108777 (fun s => s.RIP = 0x108777) (subR64R64Effect 0x108777 2 14) (Reg.operands [.gpr 2, .gpr 14] [])) #v[425, 423]
    (.letOp (n := 429) (.out 0x10877a (notR64Effect 0x10877a 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[156]
    (.letOp (n := 430) (.exec 0x10877a (fun s => s.RIP = 0x10877a) (notR64Effect 0x10877a 1) (Reg.operands [.gpr 1] [])) #v[156]
    (.letOp (n := 431) (.out 0x10877d (movR64R64Effect 0x10877d 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[423]
    (.letOp (n := 432) (.exec 0x10877d (fun s => s.RIP = 0x10877d) (movR64R64Effect 0x10877d 6 14) (Reg.operands [.gpr 14] [])) #v[423]
    (.letOp (n := 433) (.out 0x108780 (andR64R64Effect 0x108780 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[431, 429]
    (.letOp (n := 434) (.exec 0x108780 (fun s => s.RIP = 0x108780) (andR64R64Effect 0x108780 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[431, 429]
    (.letOp (n := 435) (.out 0x108783 (orR64R64Effect 0x108783 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 14] []) (.reg (.gpr 1))) #v[429, 423]
    (.letOp (n := 436) (.exec 0x108783 (fun s => s.RIP = 0x108783) (orR64R64Effect 0x108783 1 14) (Reg.operands [.gpr 1, .gpr 14] [])) #v[429, 423]
    (.letOp (n := 437) (.out 0x108786 (sarR64Effect 0x108786 4 3 63) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[403]
    (.letOp (n := 438) (.exec 0x108786 (fun s => s.RIP = 0x108786) (sarR64Effect 0x108786 4 3 63) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[403]
    (.letOp (n := 439) (.out 0x10878a (addR64R64Effect 0x10878a 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 2] []) (.reg (.gpr 3))) #v[437, 427]
    (.letOp (n := 440) (.exec 0x10878a (fun s => s.RIP = 0x10878a) (addR64R64Effect 0x10878a 3 2) (Reg.operands [.gpr 3, .gpr 2] [])) #v[437, 427]
    (b_l1084e0_10))))))))))))))))))))))))))))))))))))))))

def bytes_l1084e0_9 : List UInt8 :=
  [0x31, 0xDB, 0x48, 0x2B, 0x1C, 0x24, 0x4C, 0x8B, 0x5C, 0x24, 0x38, 0x41, 0x83, 0xE3, 0x01, 0x48,
    0x8B, 0x74, 0x24, 0x08, 0x48, 0x89, 0xF2, 0x48, 0xF7, 0xD2, 0x4C, 0x01, 0xDA, 0x48, 0x31, 0xF2,
    0x49, 0xF7, 0xDE, 0x49, 0x21, 0xD6, 0x49, 0x31, 0xF6, 0x48, 0x89, 0xCA, 0x4C, 0x29, 0xF2, 0x48,
    0xF7, 0xD1, 0x4C, 0x89, 0xF6, 0x48, 0x21, 0xCE, 0x4C, 0x09, 0xF1, 0x48, 0xC1, 0xFB, 0x3F, 0x48,
    0x01, 0xD3] ++ bytes_l1084e0_10

theorem code_l1084e0_9 : ∀ x ∈ codeRange 0x10874b bytes_l1084e0_9, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x874b 66 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1084e0_10

def b_l1084e0_8 : Block Op Label signature Reg.count 363 :=
  .letOp (n := 363) (.out 0x108709 (andR64R64Effect 0x108709 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 12] []) (.reg (.gpr 2))) #v[361, 359]
    (.letOp (n := 364) (.exec 0x108709 (fun s => s.RIP = 0x108709) (andR64R64Effect 0x108709 2 12) (Reg.operands [.gpr 2, .gpr 12] [])) #v[361, 359]
    (.letOp (n := 365) (.out 0x10870c (orR64R64Effect 0x10870c 12 5) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 5] []) (.reg (.gpr 12))) #v[359, 283]
    (.letOp (n := 366) (.exec 0x10870c (fun s => s.RIP = 0x10870c) (orR64R64Effect 0x10870c 12 5) (Reg.operands [.gpr 12, .gpr 5] [])) #v[359, 283]
    (.letOp (n := 367) (.out 0x10870f (andR64R64Effect 0x10870f 12 9) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 9] []) (.reg (.gpr 12))) #v[365, 357]
    (.letOp (n := 368) (.exec 0x10870f (fun s => s.RIP = 0x10870f) (andR64R64Effect 0x10870f 12 9) (Reg.operands [.gpr 12, .gpr 9] [])) #v[365, 357]
    (.letOp (n := 369) (.out 0x108712 (orR64R64Effect 0x108712 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 2] []) (.reg (.gpr 12))) #v[367, 363]
    (.letOp (n := 370) (.exec 0x108712 (fun s => s.RIP = 0x108712) (orR64R64Effect 0x108712 12 2) (Reg.operands [.gpr 12, .gpr 2] [])) #v[367, 363]
    (.letOp (n := 371) (.out 0x108715 (shrR64Effect 0x108715 4 12 63) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[369]
    (.letOp (n := 372) (.exec 0x108715 (fun s => s.RIP = 0x108715) (shrR64Effect 0x108715 4 12 63) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[369]
    (.letOp (n := 373) (.exec 0x108719 (StorePre 0x108719 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108719 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x108719 12 (.sib 4 none 0 .none)) (Reg.operands [.gpr 12, .gpr 4] [])) #v[371, 65]
    (.letOp (n := 374) (.out 0x10871d (xorR32R32Effect 0x10871d 3 10 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 10] []) (.reg (.gpr 10))) #v[314, 314]
    (.letOp (n := 375) (.exec 0x10871d (fun s => s.RIP = 0x10871d) (xorR32R32Effect 0x10871d 3 10 10) (Reg.operands [.gpr 10, .gpr 10] [])) #v[314, 314]
    (.letOp (n := 376) (.out 0x108720 (subR64M64Effect 0x108720 10 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 4] []) (.reg (.gpr 10))) #v[374, 65]
    (.letOp (n := 377) (.exec 0x108720 (LoadPre 0x108720 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108720 + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x108720 10 (.sib 4 none 0 .none)) (Reg.operands [.gpr 10, .gpr 4] [])) #v[374, 65]
    (.letOp (n := 378) (.out 0x108724 (movR64R64Effect 0x108724 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3] []) (.reg (.gpr 2))) #v[153]
    (.letOp (n := 379) (.exec 0x108724 (fun s => s.RIP = 0x108724) (movR64R64Effect 0x108724 2 3) (Reg.operands [.gpr 3] [])) #v[153]
    (.letOp (n := 380) (.out 0x108727 (subR64R64Effect 0x108727 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 15] []) (.reg (.gpr 2))) #v[378, 294]
    (.letOp (n := 381) (.exec 0x108727 (fun s => s.RIP = 0x108727) (subR64R64Effect 0x108727 2 15) (Reg.operands [.gpr 2, .gpr 15] [])) #v[378, 294]
    (.letOp (n := 382) (.out 0x10872a (sarR64Effect 0x10872a 4 10 63) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[376]
    (.letOp (n := 383) (.exec 0x10872a (fun s => s.RIP = 0x10872a) (sarR64Effect 0x10872a 4 10 63) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[376]
    (.letOp (n := 384) (.out 0x10872e (addR64R64Effect 0x10872e 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2] []) (.reg (.gpr 10))) #v[382, 380]
    (.letOp (n := 385) (.exec 0x10872e (fun s => s.RIP = 0x10872e) (addR64R64Effect 0x10872e 10 2) (Reg.operands [.gpr 10, .gpr 2] [])) #v[382, 380]
    (.letOp (n := 386) (.out 0x108731 (notR64Effect 0x108731 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[153]
    (.letOp (n := 387) (.exec 0x108731 (fun s => s.RIP = 0x108731) (notR64Effect 0x108731 3) (Reg.operands [.gpr 3] [])) #v[153]
    (.letOp (n := 388) (.out 0x108734 (movR64R64Effect 0x108734 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15] []) (.reg (.gpr 2))) #v[294]
    (.letOp (n := 389) (.exec 0x108734 (fun s => s.RIP = 0x108734) (movR64R64Effect 0x108734 2 15) (Reg.operands [.gpr 15] [])) #v[294]
    (.letOp (n := 390) (.out 0x108737 (andR64R64Effect 0x108737 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 3] []) (.reg (.gpr 2))) #v[388, 386]
    (.letOp (n := 391) (.exec 0x108737 (fun s => s.RIP = 0x108737) (andR64R64Effect 0x108737 2 3) (Reg.operands [.gpr 2, .gpr 3] [])) #v[388, 386]
    (.letOp (n := 392) (.out 0x10873a (orR64R64Effect 0x10873a 3 15) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 15] []) (.reg (.gpr 3))) #v[386, 294]
    (.letOp (n := 393) (.exec 0x10873a (fun s => s.RIP = 0x10873a) (orR64R64Effect 0x10873a 3 15) (Reg.operands [.gpr 3, .gpr 15] [])) #v[386, 294]
    (.letOp (n := 394) (.out 0x10873d (andR64R64Effect 0x10873d 3 10) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 10] []) (.reg (.gpr 3))) #v[392, 384]
    (.letOp (n := 395) (.exec 0x10873d (fun s => s.RIP = 0x10873d) (andR64R64Effect 0x10873d 3 10) (Reg.operands [.gpr 3, .gpr 10] [])) #v[392, 384]
    (.letOp (n := 396) (.out 0x108740 (orR64R64Effect 0x108740 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 2] []) (.reg (.gpr 3))) #v[394, 390]
    (.letOp (n := 397) (.exec 0x108740 (fun s => s.RIP = 0x108740) (orR64R64Effect 0x108740 3 2) (Reg.operands [.gpr 3, .gpr 2] [])) #v[394, 390]
    (.letOp (n := 398) (.out 0x108743 (shrR64Effect 0x108743 4 3 63) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[396]
    (.letOp (n := 399) (.exec 0x108743 (fun s => s.RIP = 0x108743) (shrR64Effect 0x108743 4 3 63) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[396]
    (.letOp (n := 400) (.exec 0x108747 (StorePre 0x108747 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108747 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x108747 3 (.sib 4 none 0 .none)) (Reg.operands [.gpr 3, .gpr 4] [])) #v[398, 65]
    (b_l1084e0_9))))))))))))))))))))))))))))))))))))))

def bytes_l1084e0_8 : List UInt8 :=
  [0x4C, 0x21, 0xE2, 0x49, 0x09, 0xEC, 0x4D, 0x21, 0xCC, 0x49, 0x09, 0xD4, 0x49, 0xC1, 0xEC, 0x3F,
    0x4C, 0x89, 0x24, 0x24, 0x45, 0x31, 0xD2, 0x4C, 0x2B, 0x14, 0x24, 0x48, 0x89, 0xDA, 0x4C, 0x29,
    0xFA, 0x49, 0xC1, 0xFA, 0x3F, 0x49, 0x01, 0xD2, 0x48, 0xF7, 0xD3, 0x4C, 0x89, 0xFA, 0x48, 0x21,
    0xDA, 0x4C, 0x09, 0xFB, 0x4C, 0x21, 0xD3, 0x48, 0x09, 0xD3, 0x48, 0xC1, 0xEB, 0x3F, 0x48, 0x89,
    0x1C, 0x24] ++ bytes_l1084e0_9

theorem code_l1084e0_8 : ∀ x ∈ codeRange 0x108709 bytes_l1084e0_8, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x8709 66 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1084e0_9

def b_l1084e0_7 : Block Op Label signature Reg.count 324 :=
  .letOp (n := 324) (.out 0x1086c8 (movR64R64Effect 0x1086c8 2 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9] []) (.reg (.gpr 2))) #v[147]
    (.letOp (n := 325) (.exec 0x1086c8 (fun s => s.RIP = 0x1086c8) (movR64R64Effect 0x1086c8 2 9) (Reg.operands [.gpr 9] [])) #v[147]
    (.letOp (n := 326) (.out 0x1086cb (subR64R64Effect 0x1086cb 2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 13] []) (.reg (.gpr 2))) #v[324, 269]
    (.letOp (n := 327) (.exec 0x1086cb (fun s => s.RIP = 0x1086cb) (subR64R64Effect 0x1086cb 2 13) (Reg.operands [.gpr 2, .gpr 13] [])) #v[324, 269]
    (.letOp (n := 328) (.out 0x1086ce (sarR64Effect 0x1086ce 4 8 63) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[322]
    (.letOp (n := 329) (.exec 0x1086ce (fun s => s.RIP = 0x1086ce) (sarR64Effect 0x1086ce 4 8 63) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[322]
    (.letOp (n := 330) (.out 0x1086d2 (addR64R64Effect 0x1086d2 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2] []) (.reg (.gpr 8))) #v[328, 326]
    (.letOp (n := 331) (.exec 0x1086d2 (fun s => s.RIP = 0x1086d2) (addR64R64Effect 0x1086d2 8 2) (Reg.operands [.gpr 8, .gpr 2] [])) #v[328, 326]
    (.letOp (n := 332) (.out 0x1086d5 (notR64Effect 0x1086d5 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[147]
    (.letOp (n := 333) (.exec 0x1086d5 (fun s => s.RIP = 0x1086d5) (notR64Effect 0x1086d5 9) (Reg.operands [.gpr 9] [])) #v[147]
    (.letOp (n := 334) (.out 0x1086d8 (movR64R64Effect 0x1086d8 2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13] []) (.reg (.gpr 2))) #v[269]
    (.letOp (n := 335) (.exec 0x1086d8 (fun s => s.RIP = 0x1086d8) (movR64R64Effect 0x1086d8 2 13) (Reg.operands [.gpr 13] [])) #v[269]
    (.letOp (n := 336) (.out 0x1086db (andR64R64Effect 0x1086db 2 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 9] []) (.reg (.gpr 2))) #v[334, 332]
    (.letOp (n := 337) (.exec 0x1086db (fun s => s.RIP = 0x1086db) (andR64R64Effect 0x1086db 2 9) (Reg.operands [.gpr 2, .gpr 9] [])) #v[334, 332]
    (.letOp (n := 338) (.out 0x1086de (orR64R64Effect 0x1086de 9 13) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 13] []) (.reg (.gpr 9))) #v[332, 269]
    (.letOp (n := 339) (.exec 0x1086de (fun s => s.RIP = 0x1086de) (orR64R64Effect 0x1086de 9 13) (Reg.operands [.gpr 9, .gpr 13] [])) #v[332, 269]
    (.letOp (n := 340) (.out 0x1086e1 (andR64R64Effect 0x1086e1 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8] []) (.reg (.gpr 9))) #v[338, 330]
    (.letOp (n := 341) (.exec 0x1086e1 (fun s => s.RIP = 0x1086e1) (andR64R64Effect 0x1086e1 9 8) (Reg.operands [.gpr 9, .gpr 8] [])) #v[338, 330]
    (.letOp (n := 342) (.out 0x1086e4 (orR64R64Effect 0x1086e4 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2] []) (.reg (.gpr 9))) #v[340, 336]
    (.letOp (n := 343) (.exec 0x1086e4 (fun s => s.RIP = 0x1086e4) (orR64R64Effect 0x1086e4 9 2) (Reg.operands [.gpr 9, .gpr 2] [])) #v[340, 336]
    (.letOp (n := 344) (.out 0x1086e7 (shrR64Effect 0x1086e7 4 9 63) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[342]
    (.letOp (n := 345) (.exec 0x1086e7 (fun s => s.RIP = 0x1086e7) (shrR64Effect 0x1086e7 4 9 63) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[342]
    (.letOp (n := 346) (.exec 0x1086eb (StorePre 0x1086eb 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1086eb + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1086eb 9 (.sib 4 none 0 .none)) (Reg.operands [.gpr 9, .gpr 4] [])) #v[344, 65]
    (.letOp (n := 347) (.out 0x1086ef (xorR32R32Effect 0x1086ef 3 9 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 9] []) (.reg (.gpr 9))) #v[344, 344]
    (.letOp (n := 348) (.exec 0x1086ef (fun s => s.RIP = 0x1086ef) (xorR32R32Effect 0x1086ef 3 9 9) (Reg.operands [.gpr 9, .gpr 9] [])) #v[344, 344]
    (.letOp (n := 349) (.out 0x1086f2 (subR64M64Effect 0x1086f2 9 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 4] []) (.reg (.gpr 9))) #v[347, 65]
    (.letOp (n := 350) (.exec 0x1086f2 (LoadPre 0x1086f2 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1086f2 + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x1086f2 9 (.sib 4 none 0 .none)) (Reg.operands [.gpr 9, .gpr 4] [])) #v[347, 65]
    (.letOp (n := 351) (.out 0x1086f6 (movR64R64Effect 0x1086f6 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12] []) (.reg (.gpr 2))) #v[150]
    (.letOp (n := 352) (.exec 0x1086f6 (fun s => s.RIP = 0x1086f6) (movR64R64Effect 0x1086f6 2 12) (Reg.operands [.gpr 12] [])) #v[150]
    (.letOp (n := 353) (.out 0x1086f9 (subR64R64Effect 0x1086f9 2 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 5] []) (.reg (.gpr 2))) #v[351, 283]
    (.letOp (n := 354) (.exec 0x1086f9 (fun s => s.RIP = 0x1086f9) (subR64R64Effect 0x1086f9 2 5) (Reg.operands [.gpr 2, .gpr 5] [])) #v[351, 283]
    (.letOp (n := 355) (.out 0x1086fc (sarR64Effect 0x1086fc 4 9 63) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[349]
    (.letOp (n := 356) (.exec 0x1086fc (fun s => s.RIP = 0x1086fc) (sarR64Effect 0x1086fc 4 9 63) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[349]
    (.letOp (n := 357) (.out 0x108700 (addR64R64Effect 0x108700 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2] []) (.reg (.gpr 9))) #v[355, 353]
    (.letOp (n := 358) (.exec 0x108700 (fun s => s.RIP = 0x108700) (addR64R64Effect 0x108700 9 2) (Reg.operands [.gpr 9, .gpr 2] [])) #v[355, 353]
    (.letOp (n := 359) (.out 0x108703 (notR64Effect 0x108703 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[150]
    (.letOp (n := 360) (.exec 0x108703 (fun s => s.RIP = 0x108703) (notR64Effect 0x108703 12) (Reg.operands [.gpr 12] [])) #v[150]
    (.letOp (n := 361) (.out 0x108706 (movR64R64Effect 0x108706 2 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5] []) (.reg (.gpr 2))) #v[283]
    (.letOp (n := 362) (.exec 0x108706 (fun s => s.RIP = 0x108706) (movR64R64Effect 0x108706 2 5) (Reg.operands [.gpr 5] [])) #v[283]
    (b_l1084e0_8)))))))))))))))))))))))))))))))))))))))

def bytes_l1084e0_7 : List UInt8 :=
  [0x4C, 0x89, 0xCA, 0x4C, 0x29, 0xEA, 0x49, 0xC1, 0xF8, 0x3F, 0x49, 0x01, 0xD0, 0x49, 0xF7, 0xD1,
    0x4C, 0x89, 0xEA, 0x4C, 0x21, 0xCA, 0x4D, 0x09, 0xE9, 0x4D, 0x21, 0xC1, 0x49, 0x09, 0xD1, 0x49,
    0xC1, 0xE9, 0x3F, 0x4C, 0x89, 0x0C, 0x24, 0x45, 0x31, 0xC9, 0x4C, 0x2B, 0x0C, 0x24, 0x4C, 0x89,
    0xE2, 0x48, 0x29, 0xEA, 0x49, 0xC1, 0xF9, 0x3F, 0x49, 0x01, 0xD1, 0x49, 0xF7, 0xD4, 0x48, 0x89,
    0xEA] ++ bytes_l1084e0_8

theorem code_l1084e0_7 : ∀ x ∈ codeRange 0x1086c8 bytes_l1084e0_7, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x86c8 65 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1084e0_8

def b_l1084e0_6 : Block Op Label signature Reg.count 288 :=
  .letOp (n := 288) (.out 0x108684 (movzxR32M8Effect 0x108684 5 15 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[65]
    (.letOp (n := 289) (.exec 0x108684 (LoadPre 0x108684 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108684 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x108684 5 15 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 290) (.out 0x108689 (negR64Effect 0x108689 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15] []) (.reg (.gpr 15))) #v[288]
    (.letOp (n := 291) (.exec 0x108689 (fun s => s.RIP = 0x108689) (negR64Effect 0x108689 15) (Reg.operands [.gpr 15] [])) #v[288]
    (.letOp (n := 292) (.out 0x10868c (andR64R64Effect 0x10868c 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 2] []) (.reg (.gpr 15))) #v[290, 286]
    (.letOp (n := 293) (.exec 0x10868c (fun s => s.RIP = 0x10868c) (andR64R64Effect 0x10868c 15 2) (Reg.operands [.gpr 15, .gpr 2] [])) #v[290, 286]
    (.letOp (n := 294) (.out 0x10868f (xorR64R64Effect 0x10868f 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 0] []) (.reg (.gpr 15))) #v[292, 201]
    (.letOp (n := 295) (.exec 0x10868f (fun s => s.RIP = 0x10868f) (xorR64R64Effect 0x10868f 15 0) (Reg.operands [.gpr 15, .gpr 0] [])) #v[292, 201]
    (.letOp (n := 296) (.exec 0x108692 (StorePre 0x108692 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108692 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108692 4 11 (.sib 4 none 0 .none)) (Reg.operands [.gpr 11, .gpr 4] [])) #v[217, 65]
    (.letOp (n := 297) (.exec 0x108696 (fun s => s.RIP = 0x108696) (movR64R64Effect 0x108696 0 4) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 298) (.out 0x108699 (movR64R64Effect 0x108699 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[102]
    (.letOp (n := 299) (.exec 0x108699 (fun s => s.RIP = 0x108699) (movR64R64Effect 0x108699 0 10) (Reg.operands [.gpr 10] [])) #v[102]
    (.letOp (n := 300) (.out 0x10869c (subR64R64Effect 0x10869c 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[298, 256]
    (.letOp (n := 301) (.exec 0x10869c (fun s => s.RIP = 0x10869c) (subR64R64Effect 0x10869c 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[298, 256]
    (.letOp (n := 302) (.out 0x10869f (notR64Effect 0x10869f 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[102]
    (.letOp (n := 303) (.exec 0x10869f (fun s => s.RIP = 0x10869f) (notR64Effect 0x10869f 10) (Reg.operands [.gpr 10] [])) #v[102]
    (.letOp (n := 304) (.out 0x1086a2 (movR64R64Effect 0x1086a2 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6] []) (.reg (.gpr 2))) #v[256]
    (.letOp (n := 305) (.exec 0x1086a2 (fun s => s.RIP = 0x1086a2) (movR64R64Effect 0x1086a2 2 6) (Reg.operands [.gpr 6] [])) #v[256]
    (.letOp (n := 306) (.out 0x1086a5 (andR64R64Effect 0x1086a5 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 10] []) (.reg (.gpr 2))) #v[304, 302]
    (.letOp (n := 307) (.exec 0x1086a5 (fun s => s.RIP = 0x1086a5) (andR64R64Effect 0x1086a5 2 10) (Reg.operands [.gpr 2, .gpr 10] [])) #v[304, 302]
    (.letOp (n := 308) (.out 0x1086a8 (orR64R64Effect 0x1086a8 10 6) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 6] []) (.reg (.gpr 10))) #v[302, 256]
    (.letOp (n := 309) (.exec 0x1086a8 (fun s => s.RIP = 0x1086a8) (orR64R64Effect 0x1086a8 10 6) (Reg.operands [.gpr 10, .gpr 6] [])) #v[302, 256]
    (.letOp (n := 310) (.out 0x1086ab (andR64R64Effect 0x1086ab 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0] []) (.reg (.gpr 10))) #v[308, 300]
    (.letOp (n := 311) (.exec 0x1086ab (fun s => s.RIP = 0x1086ab) (andR64R64Effect 0x1086ab 10 0) (Reg.operands [.gpr 10, .gpr 0] [])) #v[308, 300]
    (.letOp (n := 312) (.out 0x1086ae (orR64R64Effect 0x1086ae 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2] []) (.reg (.gpr 10))) #v[310, 306]
    (.letOp (n := 313) (.exec 0x1086ae (fun s => s.RIP = 0x1086ae) (orR64R64Effect 0x1086ae 10 2) (Reg.operands [.gpr 10, .gpr 2] [])) #v[310, 306]
    (.letOp (n := 314) (.out 0x1086b1 (shrR64Effect 0x1086b1 4 10 63) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[312]
    (.letOp (n := 315) (.exec 0x1086b1 (fun s => s.RIP = 0x1086b1) (shrR64Effect 0x1086b1 4 10 63) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[312]
    (.letOp (n := 316) (.out 0x1086b5 (movzxR32M8Effect 0x1086b5 5 14 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[65]
    (.letOp (n := 317) (.exec 0x1086b5 (LoadPre 0x1086b5 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1086b5 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1086b5 5 14 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 318) (.exec 0x1086ba (StorePre 0x1086ba 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1086ba + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1086ba 10 (.sib 4 none 0 .none)) (Reg.operands [.gpr 10, .gpr 4] [])) #v[314, 65]
    (.letOp (n := 319) (.exec 0x1086be (fun s => s.RIP = 0x1086be) (movR64R64Effect 0x1086be 11 4) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 320) (.out 0x1086c1 (xorR32R32Effect 0x1086c1 3 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 8] []) (.reg (.gpr 8))) #v[275, 275]
    (.letOp (n := 321) (.exec 0x1086c1 (fun s => s.RIP = 0x1086c1) (xorR32R32Effect 0x1086c1 3 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[275, 275]
    (.letOp (n := 322) (.out 0x1086c4 (subR64M64Effect 0x1086c4 8 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 4] []) (.reg (.gpr 8))) #v[320, 65]
    (.letOp (n := 323) (.exec 0x1086c4 (LoadPre 0x1086c4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1086c4 + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x1086c4 8 (.sib 4 none 0 .none)) (Reg.operands [.gpr 8, .gpr 4] [])) #v[320, 65]
    (b_l1084e0_7))))))))))))))))))))))))))))))))))))

def bytes_l1084e0_6 : List UInt8 :=
  [0x44, 0x0F, 0xB6, 0x3C, 0x24, 0x49, 0xF7, 0xDF, 0x49, 0x21, 0xD7, 0x49, 0x31, 0xC7, 0x44, 0x88,
    0x1C, 0x24, 0x48, 0x89, 0xE0, 0x4C, 0x89, 0xD0, 0x48, 0x29, 0xF0, 0x49, 0xF7, 0xD2, 0x48, 0x89,
    0xF2, 0x4C, 0x21, 0xD2, 0x49, 0x09, 0xF2, 0x49, 0x21, 0xC2, 0x49, 0x09, 0xD2, 0x49, 0xC1, 0xEA,
    0x3F, 0x44, 0x0F, 0xB6, 0x34, 0x24, 0x4C, 0x89, 0x14, 0x24, 0x49, 0x89, 0xE3, 0x45, 0x31, 0xC0,
    0x4C, 0x2B, 0x04, 0x24] ++ bytes_l1084e0_7

theorem code_l1084e0_6 : ∀ x ∈ codeRange 0x108684 bytes_l1084e0_6, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x8684 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1084e0_7

def b_l1084e0_5 : Block Op Label signature Reg.count 252 :=
  .letOp (n := 252) (.out 0x108640 (negR64Effect 0x108640 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[250]
    (.letOp (n := 253) (.exec 0x108640 (fun s => s.RIP = 0x108640) (negR64Effect 0x108640 6) (Reg.operands [.gpr 6] [])) #v[250]
    (.letOp (n := 254) (.out 0x108643 (andR64R64Effect 0x108643 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 13] []) (.reg (.gpr 6))) #v[252, 248]
    (.letOp (n := 255) (.exec 0x108643 (fun s => s.RIP = 0x108643) (andR64R64Effect 0x108643 6 13) (Reg.operands [.gpr 6, .gpr 13] [])) #v[252, 248]
    (.letOp (n := 256) (.out 0x108646 (xorR64R64Effect 0x108646 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 14] []) (.reg (.gpr 6))) #v[254, 219]
    (.letOp (n := 257) (.exec 0x108646 (fun s => s.RIP = 0x108646) (xorR64R64Effect 0x108646 6 14) (Reg.operands [.gpr 6, .gpr 14] [])) #v[254, 219]
    (.letOp (n := 258) (.exec 0x108649 (StorePre 0x108649 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108649 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108649 4 11 (.sib 4 none 0 .none)) (Reg.operands [.gpr 11, .gpr 4] [])) #v[217, 65]
    (.letOp (n := 259) (.out 0x10864d (movR64R64Effect 0x10864d 14 4) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[65]
    (.letOp (n := 260) (.exec 0x10864d (fun s => s.RIP = 0x10864d) (movR64R64Effect 0x10864d 14 4) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 261) (.out 0x108650 (xorR64R64Effect 0x108650 5 15) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 15] []) (.reg (.gpr 5))) #v[228, 192]
    (.letOp (n := 262) (.exec 0x108650 (fun s => s.RIP = 0x108650) (xorR64R64Effect 0x108650 5 15) (Reg.operands [.gpr 5, .gpr 15] [])) #v[228, 192]
    (.letOp (n := 263) (.out 0x108653 (movzxR32M8Effect 0x108653 5 13 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[65]
    (.letOp (n := 264) (.exec 0x108653 (LoadPre 0x108653 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108653 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x108653 5 13 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 265) (.out 0x108658 (negR64Effect 0x108658 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[263]
    (.letOp (n := 266) (.exec 0x108658 (fun s => s.RIP = 0x108658) (negR64Effect 0x108658 13) (Reg.operands [.gpr 13] [])) #v[263]
    (.letOp (n := 267) (.out 0x10865b (andR64R64Effect 0x10865b 13 5) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 5] []) (.reg (.gpr 13))) #v[265, 261]
    (.letOp (n := 268) (.exec 0x10865b (fun s => s.RIP = 0x10865b) (andR64R64Effect 0x10865b 13 5) (Reg.operands [.gpr 13, .gpr 5] [])) #v[265, 261]
    (.letOp (n := 269) (.out 0x10865e (xorR64R64Effect 0x10865e 13 15) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 15] []) (.reg (.gpr 13))) #v[267, 192]
    (.letOp (n := 270) (.exec 0x10865e (fun s => s.RIP = 0x10865e) (xorR64R64Effect 0x10865e 13 15) (Reg.operands [.gpr 13, .gpr 15] [])) #v[267, 192]
    (.letOp (n := 271) (.exec 0x108661 (StorePre 0x108661 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108661 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108661 4 11 (.sib 4 none 0 .none)) (Reg.operands [.gpr 11, .gpr 4] [])) #v[217, 65]
    (.letOp (n := 272) (.exec 0x108665 (fun s => s.RIP = 0x108665) (movR64R64Effect 0x108665 15 14) (Reg.operands [.gpr 14] [])) #v[259]
    (.letOp (n := 273) (.out 0x108668 (movR64M64Effect 0x108668 14 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[65]
    (.letOp (n := 274) (.exec 0x108668 (LoadPre 0x108668 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x108668 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x108668 14 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 275) (.out 0x10866d (xorR64R64Effect 0x10866d 8 14) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 14] []) (.reg (.gpr 8))) #v[233, 273]
    (.letOp (n := 276) (.exec 0x10866d (fun s => s.RIP = 0x10866d) (xorR64R64Effect 0x10866d 8 14) (Reg.operands [.gpr 8, .gpr 14] [])) #v[233, 273]
    (.letOp (n := 277) (.out 0x108670 (movzxR32M8Effect 0x108670 4 5 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[65]
    (.letOp (n := 278) (.exec 0x108670 (LoadPre 0x108670 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108670 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x108670 4 5 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 279) (.out 0x108674 (negR64Effect 0x108674 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5] []) (.reg (.gpr 5))) #v[277]
    (.letOp (n := 280) (.exec 0x108674 (fun s => s.RIP = 0x108674) (negR64Effect 0x108674 5) (Reg.operands [.gpr 5] [])) #v[277]
    (.letOp (n := 281) (.out 0x108677 (andR64R64Effect 0x108677 5 8) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 8] []) (.reg (.gpr 5))) #v[279, 275]
    (.letOp (n := 282) (.exec 0x108677 (fun s => s.RIP = 0x108677) (andR64R64Effect 0x108677 5 8) (Reg.operands [.gpr 5, .gpr 8] [])) #v[279, 275]
    (.letOp (n := 283) (.out 0x10867a (xorR64R64Effect 0x10867a 5 14) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 14] []) (.reg (.gpr 5))) #v[281, 273]
    (.letOp (n := 284) (.exec 0x10867a (fun s => s.RIP = 0x10867a) (xorR64R64Effect 0x10867a 5 14) (Reg.operands [.gpr 5, .gpr 14] [])) #v[281, 273]
    (.letOp (n := 285) (.exec 0x10867d (StorePre 0x10867d 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10867d + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10867d 4 11 (.sib 4 none 0 .none)) (Reg.operands [.gpr 11, .gpr 4] [])) #v[217, 65]
    (.letOp (n := 286) (.out 0x108681 (xorR64R64Effect 0x108681 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[238, 201]
    (.letOp (n := 287) (.exec 0x108681 (fun s => s.RIP = 0x108681) (xorR64R64Effect 0x108681 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[238, 201]
    (b_l1084e0_6))))))))))))))))))))))))))))))))))))

def bytes_l1084e0_5 : List UInt8 :=
  [0x48, 0xF7, 0xDE, 0x4C, 0x21, 0xEE, 0x4C, 0x31, 0xF6, 0x44, 0x88, 0x1C, 0x24, 0x49, 0x89, 0xE6,
    0x4C, 0x31, 0xFD, 0x44, 0x0F, 0xB6, 0x2C, 0x24, 0x49, 0xF7, 0xDD, 0x49, 0x21, 0xED, 0x4D, 0x31,
    0xFD, 0x44, 0x88, 0x1C, 0x24, 0x4D, 0x89, 0xF7, 0x4C, 0x8B, 0x74, 0x24, 0x30, 0x4D, 0x31, 0xF0,
    0x0F, 0xB6, 0x2C, 0x24, 0x48, 0xF7, 0xDD, 0x4C, 0x21, 0xC5, 0x4C, 0x31, 0xF5, 0x44, 0x88, 0x1C,
    0x24, 0x48, 0x31, 0xC2] ++ bytes_l1084e0_6

theorem code_l1084e0_5 : ∀ x ∈ codeRange 0x108640 bytes_l1084e0_5, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x8640 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1084e0_6

def b_l1084e0_4 : Block Op Label signature Reg.count 214 :=
  .letOp (n := 214) (.out 0x1085f2 (xorR8R8Effect 0x1085f2 3 11 8) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 8] []) (.reg (.gpr 11))) #v[212, 184]
    (.letOp (n := 215) (.exec 0x1085f2 (fun s => s.RIP = 0x1085f2) (xorR8R8Effect 0x1085f2 3 11 8) (Reg.operands [.gpr 11, .gpr 8] [])) #v[212, 184]
    (.letOp (n := 216) (.exec 0x1085f5 (StorePre 0x1085f5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1085f5 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1085f5 5 11 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[214, 65]
    (.letOp (n := 217) (.out 0x1085fa (xorR8Imm8Effect 0x1085fa 4 11 0x1) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11] []) (.reg (.gpr 11))) #v[214]
    (.letOp (n := 218) (.exec 0x1085fa (fun s => s.RIP = 0x1085fa) (xorR8Imm8Effect 0x1085fa 4 11 0x1) (Reg.operands [.gpr 11] [])) #v[214]
    (.letOp (n := 219) (.out 0x1085fe (movR64M64Effect 0x1085fe 14 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[65]
    (.letOp (n := 220) (.exec 0x1085fe (LoadPre 0x1085fe (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1085fe + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1085fe 14 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 221) (.out 0x108603 (movR64R64Effect 0x108603 13 14) (EffectPart.reads (.reg (.gpr 13)) [.gpr 14] []) (.reg (.gpr 13))) #v[219]
    (.letOp (n := 222) (.exec 0x108603 (fun s => s.RIP = 0x108603) (movR64R64Effect 0x108603 13 14) (Reg.operands [.gpr 14] [])) #v[219]
    (.letOp (n := 223) (.out 0x108606 (negR64Effect 0x108606 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[221]
    (.letOp (n := 224) (.out 0x108606 (negR64Effect 0x108606 13) (EffectPart.reads (.flag .CF) [.gpr 13] []) (.flag .CF)) #v[221]
    (.letOp (n := 225) (.exec 0x108606 (fun s => s.RIP = 0x108606) (negR64Effect 0x108606 13) (Reg.operands [.gpr 13] [])) #v[221]
    (.letOp (n := 226) (.out 0x108609 (movR32Imm32Effect 0x108609 5 5 0x0) (EffectPart.reads (.reg (.gpr 5)) [] []) (.reg (.gpr 5))) #v[]
    (.letOp (n := 227) (.exec 0x108609 (fun s => s.RIP = 0x108609) (movR32Imm32Effect 0x108609 5 5 0x0) (Reg.operands [] [])) #v[]
    (.letOp (n := 228) (.out 0x10860e (atFlags StatusFlags.CF (sbbR64R64Effect 0x10860e 5 15)) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 5))) #v[226, 192, 224]
    (.letOp (n := 229) (.out 0x10860e (atFlags StatusFlags.CF (sbbR64R64Effect 0x10860e 5 15)) (Reg.operands [.gpr 5, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[226, 192, 224]
    (.letOp (n := 230) (.exec 0x10860e (fun s => s.RIP = 0x10860e) (atFlags StatusFlags.CF (sbbR64R64Effect 0x10860e 5 15)) (Reg.operands [.gpr 5, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[226, 192, 224]
    (.letOp (n := 231) (.out 0x108611 (movR32Imm32Effect 0x108611 6 8 0x0) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 232) (.exec 0x108611 (fun s => s.RIP = 0x108611) (movR32Imm32Effect 0x108611 6 8 0x0) (Reg.operands [] [])) #v[]
    (.letOp (n := 233) (.out 0x108617 (atFlags StatusFlags.CF (sbbR64R64Effect 0x108617 8 6)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[231, 198, 229]
    (.letOp (n := 234) (.out 0x108617 (atFlags StatusFlags.CF (sbbR64R64Effect 0x108617 8 6)) (Reg.operands [.gpr 8, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[231, 198, 229]
    (.letOp (n := 235) (.exec 0x108617 (fun s => s.RIP = 0x108617) (atFlags StatusFlags.CF (sbbR64R64Effect 0x108617 8 6)) (Reg.operands [.gpr 8, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[231, 198, 229]
    (.letOp (n := 236) (.out 0x10861a (movR32Imm32Effect 0x10861a 5 2 0x0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 237) (.exec 0x10861a (fun s => s.RIP = 0x10861a) (movR32Imm32Effect 0x10861a 5 2 0x0) (Reg.operands [] [])) #v[]
    (.letOp (n := 238) (.out 0x10861f (atFlags StatusFlags.CF (sbbR64R64Effect 0x10861f 2 0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[236, 201, 234]
    (.letOp (n := 239) (.out 0x10861f (atFlags StatusFlags.CF (sbbR64R64Effect 0x10861f 2 0)) (Reg.operands [.gpr 2, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[236, 201, 234]
    (.letOp (n := 240) (.exec 0x10861f (fun s => s.RIP = 0x10861f) (atFlags StatusFlags.CF (sbbR64R64Effect 0x10861f 2 0)) (Reg.operands [.gpr 2, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[236, 201, 234]
    (.letOp (n := 241) (.exec 0x108622 (StorePre 0x108622 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108622 + BitVec.ofNat 64 4)) 1) (atFlags (condHolds 3) (setccM8Effect 0x108622 4 (.sib 4 none 0 .none))) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[65, 239]
    (.letOp (n := 242) (.exec 0x108626 (fun s => s.RIP = 0x108626) (movR64R64Effect 0x108626 6 4) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 243) (.out 0x108629 (movzxR32M8Effect 0x108629 4 6 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[65]
    (.letOp (n := 244) (.exec 0x108629 (LoadPre 0x108629 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108629 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x108629 4 6 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 245) (.exec 0x10862d (StorePre 0x10862d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10862d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10862d 6 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[243, 65]
    (.letOp (n := 246) (.exec 0x108632 (StorePre 0x108632 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108632 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108632 4 11 (.sib 4 none 0 .none)) (Reg.operands [.gpr 11, .gpr 4] [])) #v[217, 65]
    (.letOp (n := 247) (.exec 0x108636 (fun s => s.RIP = 0x108636) (movR64R64Effect 0x108636 6 4) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 248) (.out 0x108639 (xorR64R64Effect 0x108639 13 14) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 14] []) (.reg (.gpr 13))) #v[223, 219]
    (.letOp (n := 249) (.exec 0x108639 (fun s => s.RIP = 0x108639) (xorR64R64Effect 0x108639 13 14) (Reg.operands [.gpr 13, .gpr 14] [])) #v[223, 219]
    (.letOp (n := 250) (.out 0x10863c (movzxR32M8Effect 0x10863c 4 6 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[65]
    (.letOp (n := 251) (.exec 0x10863c (LoadPre 0x10863c (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10863c + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10863c 4 6 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (b_l1084e0_5))))))))))))))))))))))))))))))))))))))

def bytes_l1084e0_4 : List UInt8 :=
  [0x45, 0x30, 0xC3, 0x44, 0x88, 0x5C, 0x24, 0x10, 0x41, 0x80, 0xF3, 0x01, 0x4C, 0x8B, 0x74, 0x24,
    0x28, 0x4D, 0x89, 0xF5, 0x49, 0xF7, 0xDD, 0xBD, 0x00, 0x00, 0x00, 0x00, 0x4C, 0x19, 0xFD, 0x41,
    0xB8, 0x00, 0x00, 0x00, 0x00, 0x49, 0x19, 0xF0, 0xBA, 0x00, 0x00, 0x00, 0x00, 0x48, 0x19, 0xC2,
    0x0F, 0x93, 0x04, 0x24, 0x48, 0x89, 0xE6, 0x0F, 0xB6, 0x34, 0x24, 0x48, 0x89, 0x74, 0x24, 0x38,
    0x44, 0x88, 0x1C, 0x24, 0x48, 0x89, 0xE6, 0x4D, 0x31, 0xF5, 0x0F, 0xB6, 0x34, 0x24] ++ bytes_l1084e0_5

theorem code_l1084e0_4 : ∀ x ∈ codeRange 0x1085f2 bytes_l1084e0_4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x85f2 78 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1084e0_5

def b_l1084e0_3 : Block Op Label signature Reg.count 173 :=
  .letOp (n := 173) (.out 0x1085a1 (movR64R64Effect 0x1085a1 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[145]
    (.letOp (n := 174) (.exec 0x1085a1 (fun s => s.RIP = 0x1085a1) (movR64R64Effect 0x1085a1 0 13) (Reg.operands [.gpr 13] [])) #v[145]
    (.letOp (n := 175) (.out 0x1085a4 (mulM64Effect 0x1085a4 4 (.base 11 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[173, 67]
    (.letOp (n := 176) (.out 0x1085a4 (mulM64Effect 0x1085a4 4 (.base 11 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 11] []) (.reg (.gpr 2))) #v[173, 67]
    (.letOp (n := 177) (.exec 0x1085a4 (LoadPre 0x1085a4 (fun s => AddrMode.addr (.base 11 (.d8 0x10)) s (0x1085a4 + BitVec.ofNat 64 4)) 8) (mulM64Effect 0x1085a4 4 (.base 11 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 11] [])) #v[173, 67]
    (.letOp (n := 178) (.out 0x1085a8 (movR64R64Effect 0x1085a8 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[175]
    (.letOp (n := 179) (.exec 0x1085a8 (fun s => s.RIP = 0x1085a8) (movR64R64Effect 0x1085a8 14 0) (Reg.operands [.gpr 0] [])) #v[175]
    (.letOp (n := 180) (.out 0x1085ab (movR64R64Effect 0x1085ab 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[176]
    (.letOp (n := 181) (.exec 0x1085ab (fun s => s.RIP = 0x1085ab) (movR64R64Effect 0x1085ab 5 2) (Reg.operands [.gpr 2] [])) #v[176]
    (.letOp (n := 182) (.out 0x1085ae (movR64M64Effect 0x1085ae 8 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[65]
    (.letOp (n := 183) (.exec 0x1085ae (LoadPre 0x1085ae (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1085ae + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1085ae 8 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 184) (.out 0x1085b3 (xorR8M8Effect 0x1085b3 4 8 (.base 6 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6] []) (.reg (.gpr 8))) #v[182, 6]
    (.letOp (n := 185) (.exec 0x1085b3 (LoadPre 0x1085b3 (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x1085b3 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1085b3 4 8 (.base 6 (.d8 0x20))) (Reg.operands [.gpr 8, .gpr 6] [])) #v[182, 6]
    (.letOp (n := 186) (.exec 0x1085b7 (StorePre 0x1085b7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1085b7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1085b7 8 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[184, 65]
    (.letOp (n := 187) (.out 0x1085bc (movR64R64Effect 0x1085bc 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[145]
    (.letOp (n := 188) (.exec 0x1085bc (fun s => s.RIP = 0x1085bc) (movR64R64Effect 0x1085bc 0 13) (Reg.operands [.gpr 13] [])) #v[145]
    (.letOp (n := 189) (.out 0x1085bf (mulM64Effect 0x1085bf 4 (.base 11 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[187, 67]
    (.letOp (n := 190) (.out 0x1085bf (mulM64Effect 0x1085bf 4 (.base 11 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 11] []) (.reg (.gpr 2))) #v[187, 67]
    (.letOp (n := 191) (.exec 0x1085bf (LoadPre 0x1085bf (fun s => AddrMode.addr (.base 11 (.d8 0x18)) s (0x1085bf + BitVec.ofNat 64 4)) 8) (mulM64Effect 0x1085bf 4 (.base 11 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 11] [])) #v[187, 67]
    (.letOp (n := 192) (.out 0x1085c3 (addR64M64Effect 0x1085c3 15 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 4] []) (.reg (.gpr 15))) #v[171, 65]
    (.letOp (n := 193) (.out 0x1085c3 (addR64M64Effect 0x1085c3 15 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 4] []) (.flag .CF)) #v[171, 65]
    (.letOp (n := 194) (.exec 0x1085c3 (LoadPre 0x1085c3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1085c3 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x1085c3 15 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[171, 65]
    (.letOp (n := 195) (.out 0x1085c8 (atFlags StatusFlags.CF (adcR64M64Effect 0x1085c8 14 (.sib 4 none 0 (.d8 0x8)))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 14))) #v[178, 65, 193]
    (.letOp (n := 196) (.out 0x1085c8 (atFlags StatusFlags.CF (adcR64M64Effect 0x1085c8 14 (.sib 4 none 0 (.d8 0x8)))) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.flag .CF)) #v[178, 65, 193]
    (.letOp (n := 197) (.exec 0x1085c8 (LoadPre 0x1085c8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1085c8 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x1085c8 14 (.sib 4 none 0 (.d8 0x8)))) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[178, 65, 193]
    (.letOp (n := 198) (.out 0x1085cd (movR64R64Effect 0x1085cd 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[195]
    (.letOp (n := 199) (.exec 0x1085cd (fun s => s.RIP = 0x1085cd) (movR64R64Effect 0x1085cd 6 14) (Reg.operands [.gpr 14] [])) #v[195]
    (.letOp (n := 200) (.exec 0x1085d0 (StorePre 0x1085d0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1085d0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1085d0 14 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[195, 65]
    (.letOp (n := 201) (.out 0x1085d5 (atFlags StatusFlags.CF (adcR64R64Effect 0x1085d5 0 5)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 0))) #v[189, 180, 196]
    (.letOp (n := 202) (.out 0x1085d5 (atFlags StatusFlags.CF (adcR64R64Effect 0x1085d5 0 5)) (Reg.operands [.gpr 0, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[189, 180, 196]
    (.letOp (n := 203) (.exec 0x1085d5 (fun s => s.RIP = 0x1085d5) (atFlags StatusFlags.CF (adcR64R64Effect 0x1085d5 0 5)) (Reg.operands [.gpr 0, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[189, 180, 196]
    (.letOp (n := 204) (.out 0x1085d8 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1085d8 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[190, 202]
    (.letOp (n := 205) (.exec 0x1085d8 (fun s => s.RIP = 0x1085d8) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1085d8 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[190, 202]
    (.letOp (n := 206) (.exec 0x1085dc (StorePre 0x1085dc 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1085dc + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1085dc 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[204, 65]
    (.letOp (n := 207) (.out 0x1085e1 (movR64M64Effect 0x1085e1 2 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[65]
    (.letOp (n := 208) (.exec 0x1085e1 (LoadPre 0x1085e1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1085e1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1085e1 2 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 209) (.out 0x1085e6 (xorR8M8Effect 0x1085e6 4 2 (.base 11 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 11] []) (.reg (.gpr 2))) #v[207, 67]
    (.letOp (n := 210) (.exec 0x1085e6 (LoadPre 0x1085e6 (fun s => AddrMode.addr (.base 11 (.d8 0x20)) s (0x1085e6 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1085e6 4 2 (.base 11 (.d8 0x20))) (Reg.operands [.gpr 2, .gpr 11] [])) #v[207, 67]
    (.letOp (n := 211) (.exec 0x1085ea (StorePre 0x1085ea 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1085ea + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1085ea 2 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[209, 65]
    (.letOp (n := 212) (.out 0x1085ef (movR32R32Effect 0x1085ef 3 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[209]
    (.letOp (n := 213) (.exec 0x1085ef (fun s => s.RIP = 0x1085ef) (movR32R32Effect 0x1085ef 3 11 2) (Reg.operands [.gpr 2] [])) #v[209]
    (b_l1084e0_4)))))))))))))))))))))))))))))))))))))))))

def bytes_l1084e0_3 : List UInt8 :=
  [0x4C, 0x89, 0xE8, 0x49, 0xF7, 0x63, 0x10, 0x49, 0x89, 0xC6, 0x48, 0x89, 0xD5, 0x4C, 0x8B, 0x44,
    0x24, 0x20, 0x44, 0x32, 0x46, 0x20, 0x4C, 0x89, 0x44, 0x24, 0x20, 0x4C, 0x89, 0xE8, 0x49, 0xF7,
    0x63, 0x18, 0x4C, 0x03, 0x7C, 0x24, 0x10, 0x4C, 0x13, 0x74, 0x24, 0x08, 0x4C, 0x89, 0xF6, 0x4C,
    0x89, 0x74, 0x24, 0x30, 0x48, 0x11, 0xE8, 0x48, 0x83, 0xD2, 0x00, 0x48, 0x89, 0x54, 0x24, 0x08,
    0x48, 0x8B, 0x54, 0x24, 0x18, 0x41, 0x32, 0x53, 0x20, 0x48, 0x89, 0x54, 0x24, 0x18, 0x41, 0x89,
    0xD3] ++ bytes_l1084e0_4

theorem code_l1084e0_3 : ∀ x ∈ codeRange 0x1085a1 bytes_l1084e0_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x85a1 81 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1084e0_4

def b_l1084e0_2 : Block Op Label signature Reg.count 130 :=
  .letOp (n := 130) (.out 0x10855c (movR64R64Effect 0x10855c 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[126]
    (.letOp (n := 131) (.exec 0x10855c (fun s => s.RIP = 0x10855c) (movR64R64Effect 0x10855c 5 2) (Reg.operands [.gpr 2] [])) #v[126]
    (.letOp (n := 132) (.out 0x10855f (negR64Effect 0x10855f 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[119]
    (.letOp (n := 133) (.exec 0x10855f (fun s => s.RIP = 0x10855f) (negR64Effect 0x10855f 13) (Reg.operands [.gpr 13] [])) #v[119]
    (.letOp (n := 134) (.out 0x108562 (andR64R64Effect 0x108562 13 1) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 1] []) (.reg (.gpr 13))) #v[132, 121]
    (.letOp (n := 135) (.exec 0x108562 (fun s => s.RIP = 0x108562) (andR64R64Effect 0x108562 13 1) (Reg.operands [.gpr 13, .gpr 1] [])) #v[132, 121]
    (.letOp (n := 136) (.out 0x108565 (movR64R64Effect 0x108565 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[88]
    (.letOp (n := 137) (.exec 0x108565 (fun s => s.RIP = 0x108565) (movR64R64Effect 0x108565 0 3) (Reg.operands [.gpr 3] [])) #v[88]
    (.letOp (n := 138) (.out 0x108568 (mulM64Effect 0x108568 4 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[136, 6]
    (.letOp (n := 139) (.out 0x108568 (mulM64Effect 0x108568 4 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 6] []) (.reg (.gpr 2))) #v[136, 6]
    (.letOp (n := 140) (.exec 0x108568 (LoadPre 0x108568 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x108568 + BitVec.ofNat 64 4)) 8) (mulM64Effect 0x108568 4 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 6] [])) #v[136, 6]
    (.letOp (n := 141) (.out 0x10856c (movR64R64Effect 0x10856c 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[138]
    (.letOp (n := 142) (.exec 0x10856c (fun s => s.RIP = 0x10856c) (movR64R64Effect 0x10856c 3 0) (Reg.operands [.gpr 0] [])) #v[138]
    (.letOp (n := 143) (.out 0x10856f (movR64R64Effect 0x10856f 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[139]
    (.letOp (n := 144) (.exec 0x10856f (fun s => s.RIP = 0x10856f) (movR64R64Effect 0x10856f 1 2) (Reg.operands [.gpr 2] [])) #v[139]
    (.letOp (n := 145) (.out 0x108572 (xorR64R64Effect 0x108572 13 8) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 8] []) (.reg (.gpr 13))) #v[134, 8]
    (.letOp (n := 146) (.exec 0x108572 (fun s => s.RIP = 0x108572) (xorR64R64Effect 0x108572 13 8) (Reg.operands [.gpr 13, .gpr 8] [])) #v[134, 8]
    (.letOp (n := 147) (.out 0x108575 (addR64R64Effect 0x108575 9 14) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 14] []) (.reg (.gpr 9))) #v[115, 104]
    (.letOp (n := 148) (.out 0x108575 (addR64R64Effect 0x108575 9 14) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 14] []) (.flag .CF)) #v[115, 104]
    (.letOp (n := 149) (.exec 0x108575 (fun s => s.RIP = 0x108575) (addR64R64Effect 0x108575 9 14) (Reg.operands [.gpr 9, .gpr 14] [])) #v[115, 104]
    (.letOp (n := 150) (.out 0x108578 (atFlags StatusFlags.CF (adcR64R64Effect 0x108578 12 15)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 12))) #v[128, 117, 148]
    (.letOp (n := 151) (.out 0x108578 (atFlags StatusFlags.CF (adcR64R64Effect 0x108578 12 15)) (Reg.operands [.gpr 12, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[128, 117, 148]
    (.letOp (n := 152) (.exec 0x108578 (fun s => s.RIP = 0x108578) (atFlags StatusFlags.CF (adcR64R64Effect 0x108578 12 15)) (Reg.operands [.gpr 12, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[128, 117, 148]
    (.letOp (n := 153) (.out 0x10857b (atFlags StatusFlags.CF (adcR64R64Effect 0x10857b 3 5)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[141, 130, 151]
    (.letOp (n := 154) (.out 0x10857b (atFlags StatusFlags.CF (adcR64R64Effect 0x10857b 3 5)) (Reg.operands [.gpr 3, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[141, 130, 151]
    (.letOp (n := 155) (.exec 0x10857b (fun s => s.RIP = 0x10857b) (atFlags StatusFlags.CF (adcR64R64Effect 0x10857b 3 5)) (Reg.operands [.gpr 3, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[141, 130, 151]
    (.letOp (n := 156) (.out 0x10857e (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10857e 1 0x0)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[143, 154]
    (.letOp (n := 157) (.exec 0x10857e (fun s => s.RIP = 0x10857e) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10857e 1 0x0)) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[143, 154]
    (.letOp (n := 158) (.out 0x108582 (movR64R64Effect 0x108582 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[145]
    (.letOp (n := 159) (.exec 0x108582 (fun s => s.RIP = 0x108582) (movR64R64Effect 0x108582 0 13) (Reg.operands [.gpr 13] [])) #v[145]
    (.letOp (n := 160) (.out 0x108585 (mulM64Effect 0x108585 3 (.base 11 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[158, 67]
    (.letOp (n := 161) (.out 0x108585 (mulM64Effect 0x108585 3 (.base 11 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 11] []) (.reg (.gpr 2))) #v[158, 67]
    (.letOp (n := 162) (.exec 0x108585 (LoadPre 0x108585 (fun s => AddrMode.addr (.base 11 .none) s (0x108585 + BitVec.ofNat 64 3)) 8) (mulM64Effect 0x108585 3 (.base 11 .none)) (Reg.operands [.gpr 0, .gpr 11] [])) #v[158, 67]
    (.letOp (n := 163) (.exec 0x108588 (StorePre 0x108588 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108588 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108588 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[161, 65]
    (.letOp (n := 164) (.exec 0x10858d (StorePre 0x10858d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10858d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10858d 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[160, 65]
    (.letOp (n := 165) (.out 0x108592 (movR64R64Effect 0x108592 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[145]
    (.letOp (n := 166) (.exec 0x108592 (fun s => s.RIP = 0x108592) (movR64R64Effect 0x108592 0 13) (Reg.operands [.gpr 13] [])) #v[145]
    (.letOp (n := 167) (.out 0x108595 (mulM64Effect 0x108595 4 (.base 11 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[165, 67]
    (.letOp (n := 168) (.out 0x108595 (mulM64Effect 0x108595 4 (.base 11 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 11] []) (.reg (.gpr 2))) #v[165, 67]
    (.letOp (n := 169) (.exec 0x108595 (LoadPre 0x108595 (fun s => AddrMode.addr (.base 11 (.d8 0x8)) s (0x108595 + BitVec.ofNat 64 4)) 8) (mulM64Effect 0x108595 4 (.base 11 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 11] [])) #v[165, 67]
    (.letOp (n := 170) (.exec 0x108599 (StorePre 0x108599 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x108599 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108599 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[168, 65]
    (.letOp (n := 171) (.out 0x10859e (movR64R64Effect 0x10859e 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[167]
    (.letOp (n := 172) (.exec 0x10859e (fun s => s.RIP = 0x10859e) (movR64R64Effect 0x10859e 15 0) (Reg.operands [.gpr 0] [])) #v[167]
    (b_l1084e0_3)))))))))))))))))))))))))))))))))))))))))))

def bytes_l1084e0_2 : List UInt8 :=
  [0x48, 0x89, 0xD5, 0x49, 0xF7, 0xDD, 0x49, 0x21, 0xCD, 0x48, 0x89, 0xD8, 0x48, 0xF7, 0x66, 0x18,
    0x48, 0x89, 0xC3, 0x48, 0x89, 0xD1, 0x4D, 0x31, 0xC5, 0x4D, 0x01, 0xF1, 0x4D, 0x11, 0xFC, 0x48,
    0x11, 0xEB, 0x48, 0x83, 0xD1, 0x00, 0x4C, 0x89, 0xE8, 0x49, 0xF7, 0x23, 0x48, 0x89, 0x54, 0x24,
    0x10, 0x48, 0x89, 0x44, 0x24, 0x28, 0x4C, 0x89, 0xE8, 0x49, 0xF7, 0x63, 0x08, 0x48, 0x89, 0x54,
    0x24, 0x08, 0x49, 0x89, 0xC7] ++ bytes_l1084e0_3

theorem code_l1084e0_2 : ∀ x ∈ codeRange 0x10855c bytes_l1084e0_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x855c 69 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1084e0_3

def b_l1084e0_1 : Block Op Label signature Reg.count 90 :=
  .letOp (n := 90) (.out 0x108519 (movR64R64Effect 0x108519 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[8]
    (.letOp (n := 91) (.exec 0x108519 (fun s => s.RIP = 0x108519) (movR64R64Effect 0x108519 0 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 92) (.out 0x10851c (shrR64Effect 0x10851c 4 0 63) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[90]
    (.letOp (n := 93) (.exec 0x10851c (fun s => s.RIP = 0x10851c) (shrR64Effect 0x10851c 4 0 63) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[90]
    (.letOp (n := 94) (.exec 0x108520 (StorePre 0x108520 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x108520 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108520 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[92, 65]
    (.letOp (n := 95) (.exec 0x108525 (StorePre 0x108525 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108525 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x108525 3 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[92, 65]
    (.letOp (n := 96) (.exec 0x108528 (fun s => s.RIP = 0x108528) (movR64R64Effect 0x108528 0 4) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 97) (.out 0x10852b (movR64R64Effect 0x10852b 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[88]
    (.letOp (n := 98) (.exec 0x10852b (fun s => s.RIP = 0x10852b) (movR64R64Effect 0x10852b 0 3) (Reg.operands [.gpr 3] [])) #v[88]
    (.letOp (n := 99) (.out 0x10852e (mulM64Effect 0x10852e 3 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[97, 6]
    (.letOp (n := 100) (.out 0x10852e (mulM64Effect 0x10852e 3 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 6] []) (.reg (.gpr 2))) #v[97, 6]
    (.letOp (n := 101) (.exec 0x10852e (LoadPre 0x10852e (fun s => AddrMode.addr (.base 6 .none) s (0x10852e + BitVec.ofNat 64 3)) 8) (mulM64Effect 0x10852e 3 (.base 6 .none)) (Reg.operands [.gpr 0, .gpr 6] [])) #v[97, 6]
    (.letOp (n := 102) (.out 0x108531 (movR64R64Effect 0x108531 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[99]
    (.letOp (n := 103) (.exec 0x108531 (fun s => s.RIP = 0x108531) (movR64R64Effect 0x108531 10 0) (Reg.operands [.gpr 0] [])) #v[99]
    (.letOp (n := 104) (.out 0x108534 (movR64R64Effect 0x108534 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[100]
    (.letOp (n := 105) (.exec 0x108534 (fun s => s.RIP = 0x108534) (movR64R64Effect 0x108534 14 2) (Reg.operands [.gpr 2] [])) #v[100]
    (.letOp (n := 106) (.out 0x108537 (movR64R64Effect 0x108537 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 8] []) (.reg (.gpr 1))) #v[8]
    (.letOp (n := 107) (.exec 0x108537 (fun s => s.RIP = 0x108537) (movR64R64Effect 0x108537 1 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 108) (.out 0x10853a (negR64Effect 0x10853a 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[106]
    (.letOp (n := 109) (.exec 0x10853a (fun s => s.RIP = 0x10853a) (negR64Effect 0x10853a 1) (Reg.operands [.gpr 1] [])) #v[106]
    (.letOp (n := 110) (.out 0x10853d (movR64R64Effect 0x10853d 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[88]
    (.letOp (n := 111) (.exec 0x10853d (fun s => s.RIP = 0x10853d) (movR64R64Effect 0x10853d 0 3) (Reg.operands [.gpr 3] [])) #v[88]
    (.letOp (n := 112) (.out 0x108540 (mulM64Effect 0x108540 4 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[110, 6]
    (.letOp (n := 113) (.out 0x108540 (mulM64Effect 0x108540 4 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 6] []) (.reg (.gpr 2))) #v[110, 6]
    (.letOp (n := 114) (.exec 0x108540 (LoadPre 0x108540 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x108540 + BitVec.ofNat 64 4)) 8) (mulM64Effect 0x108540 4 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 6] [])) #v[110, 6]
    (.letOp (n := 115) (.out 0x108544 (movR64R64Effect 0x108544 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[112]
    (.letOp (n := 116) (.exec 0x108544 (fun s => s.RIP = 0x108544) (movR64R64Effect 0x108544 9 0) (Reg.operands [.gpr 0] [])) #v[112]
    (.letOp (n := 117) (.out 0x108547 (movR64R64Effect 0x108547 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[113]
    (.letOp (n := 118) (.exec 0x108547 (fun s => s.RIP = 0x108547) (movR64R64Effect 0x108547 15 2) (Reg.operands [.gpr 2] [])) #v[113]
    (.letOp (n := 119) (.out 0x10854a (movzxR32M8Effect 0x10854a 5 13 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[65]
    (.letOp (n := 120) (.exec 0x10854a (LoadPre 0x10854a (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10854a + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10854a 5 13 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 121) (.out 0x10854f (xorR64R64Effect 0x10854f 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8] []) (.reg (.gpr 1))) #v[108, 8]
    (.letOp (n := 122) (.exec 0x10854f (fun s => s.RIP = 0x10854f) (xorR64R64Effect 0x10854f 1 8) (Reg.operands [.gpr 1, .gpr 8] [])) #v[108, 8]
    (.letOp (n := 123) (.out 0x108552 (movR64R64Effect 0x108552 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[88]
    (.letOp (n := 124) (.exec 0x108552 (fun s => s.RIP = 0x108552) (movR64R64Effect 0x108552 0 3) (Reg.operands [.gpr 3] [])) #v[88]
    (.letOp (n := 125) (.out 0x108555 (mulM64Effect 0x108555 4 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[123, 6]
    (.letOp (n := 126) (.out 0x108555 (mulM64Effect 0x108555 4 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 6] []) (.reg (.gpr 2))) #v[123, 6]
    (.letOp (n := 127) (.exec 0x108555 (LoadPre 0x108555 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x108555 + BitVec.ofNat 64 4)) 8) (mulM64Effect 0x108555 4 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 6] [])) #v[123, 6]
    (.letOp (n := 128) (.out 0x108559 (movR64R64Effect 0x108559 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[125]
    (.letOp (n := 129) (.exec 0x108559 (fun s => s.RIP = 0x108559) (movR64R64Effect 0x108559 12 0) (Reg.operands [.gpr 0] [])) #v[125]
    (b_l1084e0_2))))))))))))))))))))))))))))))))))))))))

def bytes_l1084e0_1 : List UInt8 :=
  [0x4C, 0x89, 0xC0, 0x48, 0xC1, 0xE8, 0x3F, 0x48, 0x89, 0x44, 0x24, 0x18, 0x88, 0x04, 0x24, 0x48,
    0x89, 0xE0, 0x48, 0x89, 0xD8, 0x48, 0xF7, 0x26, 0x49, 0x89, 0xC2, 0x49, 0x89, 0xD6, 0x4C, 0x89,
    0xC1, 0x48, 0xF7, 0xD9, 0x48, 0x89, 0xD8, 0x48, 0xF7, 0x66, 0x08, 0x49, 0x89, 0xC1, 0x49, 0x89,
    0xD7, 0x44, 0x0F, 0xB6, 0x2C, 0x24, 0x4C, 0x31, 0xC1, 0x48, 0x89, 0xD8, 0x48, 0xF7, 0x66, 0x10,
    0x49, 0x89, 0xC4] ++ bytes_l1084e0_2

theorem code_l1084e0_1 : ∀ x ∈ codeRange 0x108519 bytes_l1084e0_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x8519 67 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1084e0_2

def b_l1084e0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1084e0 (pushR64Effect 0x1084e0 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x1084e0 (PushPre 0x1084e0 1) (pushR64Effect 0x1084e0 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x1084e1 (pushR64Effect 0x1084e1 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x1084e1 (PushPre 0x1084e1 2) (pushR64Effect 0x1084e1 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x1084e3 (pushR64Effect 0x1084e3 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x1084e3 (PushPre 0x1084e3 2) (pushR64Effect 0x1084e3 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x1084e5 (pushR64Effect 0x1084e5 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x1084e5 (PushPre 0x1084e5 2) (pushR64Effect 0x1084e5 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x1084e7 (pushR64Effect 0x1084e7 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x1084e7 (PushPre 0x1084e7 2) (pushR64Effect 0x1084e7 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x1084e9 (pushR64Effect 0x1084e9 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x1084e9 (PushPre 0x1084e9 1) (pushR64Effect 0x1084e9 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x1084ea (subR64Imm8Effect 0x1084ea 4 0x40) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x1084ea (fun s => s.RIP = 0x1084ea) (subR64Imm8Effect 0x1084ea 4 0x40) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x1084ee (movR64R64Effect 0x1084ee 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[2]
    (.letOp (n := 68) (.exec 0x1084ee (fun s => s.RIP = 0x1084ee) (movR64R64Effect 0x1084ee 11 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 69) (.out 0x1084f1 (movR64R64Effect 0x1084f1 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[1]
    (.letOp (n := 70) (.exec 0x1084f1 (fun s => s.RIP = 0x1084f1) (movR64R64Effect 0x1084f1 2 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 71) (.out 0x1084f4 (shrR64Effect 0x1084f4 4 2 63) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[69]
    (.letOp (n := 72) (.exec 0x1084f4 (fun s => s.RIP = 0x1084f4) (shrR64Effect 0x1084f4 4 2 63) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[69]
    (.letOp (n := 73) (.exec 0x1084f8 (StorePre 0x1084f8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1084f8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1084f8 2 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[71, 65]
    (.letOp (n := 74) (.out 0x1084fd (movR64R64Effect 0x1084fd 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[1]
    (.letOp (n := 75) (.exec 0x1084fd (fun s => s.RIP = 0x1084fd) (movR64R64Effect 0x1084fd 0 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 76) (.out 0x108500 (negR64Effect 0x108500 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[74]
    (.letOp (n := 77) (.exec 0x108500 (fun s => s.RIP = 0x108500) (negR64Effect 0x108500 0) (Reg.operands [.gpr 0] [])) #v[74]
    (.letOp (n := 78) (.exec 0x108503 (StorePre 0x108503 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108503 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x108503 3 2 (.sib 4 none 0 .none)) (Reg.operands [.gpr 2, .gpr 4] [])) #v[71, 65]
    (.letOp (n := 79) (.exec 0x108506 (fun s => s.RIP = 0x108506) (movR64R64Effect 0x108506 2 4) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 80) (.out 0x108509 (movzxR32M8Effect 0x108509 4 3 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[65]
    (.letOp (n := 81) (.exec 0x108509 (LoadPre 0x108509 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108509 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x108509 4 3 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 82) (.out 0x10850d (xorR64R64Effect 0x10850d 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[76, 1]
    (.letOp (n := 83) (.exec 0x10850d (fun s => s.RIP = 0x10850d) (xorR64R64Effect 0x10850d 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[76, 1]
    (.letOp (n := 84) (.out 0x108510 (negR64Effect 0x108510 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[80]
    (.letOp (n := 85) (.exec 0x108510 (fun s => s.RIP = 0x108510) (negR64Effect 0x108510 3) (Reg.operands [.gpr 3] [])) #v[80]
    (.letOp (n := 86) (.out 0x108513 (andR64R64Effect 0x108513 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0] []) (.reg (.gpr 3))) #v[84, 82]
    (.letOp (n := 87) (.exec 0x108513 (fun s => s.RIP = 0x108513) (andR64R64Effect 0x108513 3 0) (Reg.operands [.gpr 3, .gpr 0] [])) #v[84, 82]
    (.letOp (n := 88) (.out 0x108516 (xorR64R64Effect 0x108516 3 1) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 1] []) (.reg (.gpr 3))) #v[86, 1]
    (.letOp (n := 89) (.exec 0x108516 (fun s => s.RIP = 0x108516) (xorR64R64Effect 0x108516 3 1) (Reg.operands [.gpr 3, .gpr 1] [])) #v[86, 1]
    (b_l1084e0_1)))))))))))))))))))))))))))))))))))))

def bytes_l1084e0 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x83, 0xEC, 0x40, 0x49, 0x89,
    0xD3, 0x48, 0x89, 0xCA, 0x48, 0xC1, 0xEA, 0x3F, 0x48, 0x89, 0x54, 0x24, 0x20, 0x48, 0x89, 0xC8,
    0x48, 0xF7, 0xD8, 0x88, 0x14, 0x24, 0x48, 0x89, 0xE2, 0x0F, 0xB6, 0x1C, 0x24, 0x48, 0x31, 0xC8,
    0x48, 0xF7, 0xDB, 0x48, 0x21, 0xC3, 0x48, 0x31, 0xCB] ++ bytes_l1084e0_1

theorem code_l1084e0 : ∀ x ∈ codeRange 0x1084e0 bytes_l1084e0, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x84e0 57 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1084e0_1

@[cfg_block] def b_l108890 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x108890 (pushR64Effect 0x108890 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x108890 (PushPre 0x108890 1) (pushR64Effect 0x108890 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x108891 (pushR64Effect 0x108891 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[53, 14]
    (.letOp (n := 56) (.exec 0x108891 (PushPre 0x108891 2) (pushR64Effect 0x108891 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 57) (.out 0x108893 (pushR64Effect 0x108893 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[55, 3]
    (.letOp (n := 58) (.exec 0x108893 (PushPre 0x108893 1) (pushR64Effect 0x108893 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[55, 3]
    (.letOp (n := 59) (.out 0x108894 (subR64Imm8Effect 0x108894 4 0x30) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[57]
    (.letOp (n := 60) (.exec 0x108894 (fun s => s.RIP = 0x108894) (subR64Imm8Effect 0x108894 4 0x30) (Reg.operands [.gpr 4] [])) #v[57]
    (.letOp (n := 61) (.out 0x108898 (movR32R32Effect 0x108898 3 5 9) (EffectPart.reads (.reg (.gpr 5)) [.gpr 9] []) (.reg (.gpr 5))) #v[9]
    (.letOp (n := 62) (.exec 0x108898 (fun s => s.RIP = 0x108898) (movR32R32Effect 0x108898 3 5 9) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 63) (.out 0x10889b (movR64R64Effect 0x10889b 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 64) (.exec 0x10889b (fun s => s.RIP = 0x10889b) (movR64R64Effect 0x10889b 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 65) (.out 0x10889e (movR64R64Effect 0x10889e 7 4) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[59]
    (.letOp (n := 66) (.exec 0x10889e (fun s => s.RIP = 0x10889e) (movR64R64Effect 0x10889e 7 4) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 67) (.out 0x1088a1 (callEffect (fun _ => 0x1084e0) 0x1088a6) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 68) (.exec 0x1088a1 (PushPre 0x1088a1 5) (callEffect (fun _ => 0x1084e0) 0x1088a6) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 69) (.const ⟨64, 0x1088a6⟩) #v[]
    (.terminate (.call ⟨.l1084e0, RegMap.args [(1, 1), (2, 2), (3, 63), (4, 67), (5, 61), (6, 6), (7, 65), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 70⟩ { target := .l1088a6, kept := #v[], arity := rfl, guard := some (Fin.last 69) }))))))))))))))))))

def bytes_l108890 : List UInt8 :=
  [0x55, 0x41, 0x56, 0x53, 0x48, 0x83, 0xEC, 0x30, 0x44, 0x89, 0xCD, 0x48, 0x89, 0xFB, 0x48, 0x89,
    0xE7, 0xE8, 0x3A, 0xFC, 0xFF, 0xFF]

theorem code_l108890 : ∀ x ∈ codeRange 0x108890 bytes_l108890, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x8890 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1088a6 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1088a6 (movR32Imm32Effect 0x1088a6 5 0 0x40) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 54) (.exec 0x1088a6 (fun s => s.RIP = 0x1088a6) (movR32Imm32Effect 0x1088a6 5 0 0x40) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x1088ab (subR32R32Effect 0x1088ab 2 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[53, 5]
    (.letOp (n := 56) (.exec 0x1088ab (fun s => s.RIP = 0x1088ab) (subR32R32Effect 0x1088ab 2 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[53, 5]
    (.letOp (n := 57) (.out 0x1088ad (cmpR32Imm8Effect 0x1088ad 3 0 0x40) (EffectPart.reads (.flag .CF) [.gpr 0] []) (.flag .CF)) #v[55]
    (.letOp (n := 58) (.exec 0x1088ad (fun s => s.RIP = 0x1088ad) (cmpR32Imm8Effect 0x1088ad 3 0 0x40) (Reg.operands [.gpr 0] [])) #v[55]
    (.letOp (n := 59) (.pure (condOp 3)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l108952, RegMap.args [(0, 55), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (16, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l1088b6, RegMap.args [(0, 55), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (16, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l1088a6 : List UInt8 :=
  [0xB8, 0x40, 0x00, 0x00, 0x00, 0x29, 0xE8, 0x83, 0xF8, 0x40, 0x0F, 0x83, 0x9C, 0x00, 0x00, 0x00]

theorem code_l1088a6 : ∀ x ∈ codeRange 0x1088a6 bytes_l1088a6, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x88a6 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1088b6 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1088b6 (cmpR32Imm8Effect 0x1088b6 3 5 0x40) (EffectPart.reads (.flag .CF) [.gpr 5] []) (.flag .CF)) #v[5]
    (.letOp (n := 54) (.exec 0x1088b6 (fun s => s.RIP = 0x1088b6) (cmpR32Imm8Effect 0x1088b6 3 5 0x40) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 55) (.pure (condOp 3)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l10893a, RegMap.args [(0, 0), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l1088bb, RegMap.args [(0, 0), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l1088b6 : List UInt8 :=
  [0x83, 0xFD, 0x40, 0x73, 0x7F]

theorem code_l1088b6 : ∀ x ∈ codeRange 0x1088b6 bytes_l1088b6, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x88b6 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1088bb : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1088bb (testR32R32Effect 0x1088bb 2 5 5) (EffectPart.reads (.flag .ZF) [.gpr 5, .gpr 5] []) (.flag .ZF)) #v[5, 5]
    (.letOp (n := 54) (.exec 0x1088bb (fun s => s.RIP = 0x1088bb) (testR32R32Effect 0x1088bb 2 5 5) (Reg.operands [.gpr 5, .gpr 5] [])) #v[5, 5]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l10896a, RegMap.args [(0, 0), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l1088c3, RegMap.args [(0, 0), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l1088bb : List UInt8 :=
  [0x85, 0xED, 0x0F, 0x84, 0xA7, 0x00, 0x00, 0x00]

theorem code_l1088bb : ∀ x ∈ codeRange 0x1088bb bytes_l1088bb, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x88bb 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1088c3_1 : Block Op Label signature Reg.count 93 :=
  .letOp (n := 93) (.out 0x108906 (movR32R32Effect 0x108906 2 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[5]
    (.letOp (n := 94) (.exec 0x108906 (fun s => s.RIP = 0x108906) (movR32R32Effect 0x108906 2 1 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 95) (.out 0x108908 (shrR64ClEffect 0x108908 3 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[91, 93]
    (.letOp (n := 96) (.exec 0x108908 (fun s => s.RIP = 0x108908) (shrR64ClEffect 0x108908 3 14) (Reg.operands [.gpr 14, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[91, 93]
    (.letOp (n := 97) (.out 0x10890b (movR32R32Effect 0x10890b 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[0]
    (.letOp (n := 98) (.exec 0x10890b (fun s => s.RIP = 0x10890b) (movR32R32Effect 0x10890b 2 1 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 99) (.out 0x10890d (shlR64ClEffect 0x10890d 3 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[55, 97]
    (.letOp (n := 100) (.exec 0x10890d (fun s => s.RIP = 0x10890d) (shlR64ClEffect 0x10890d 3 6) (Reg.operands [.gpr 6, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[55, 97]
    (.letOp (n := 101) (.out 0x108910 (movR32R32Effect 0x108910 2 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[5]
    (.letOp (n := 102) (.exec 0x108910 (fun s => s.RIP = 0x108910) (movR32R32Effect 0x108910 2 1 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 103) (.out 0x108912 (shrR64ClEffect 0x108912 3 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[53, 101]
    (.letOp (n := 104) (.exec 0x108912 (fun s => s.RIP = 0x108912) (shrR64ClEffect 0x108912 3 2) (Reg.operands [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53, 101]
    (.letOp (n := 105) (.out 0x108915 (orR64R64Effect 0x108915 11 8) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 8] []) (.reg (.gpr 11))) #v[85, 75]
    (.letOp (n := 106) (.exec 0x108915 (fun s => s.RIP = 0x108915) (orR64R64Effect 0x108915 11 8) (Reg.operands [.gpr 11, .gpr 8] [])) #v[85, 75]
    (.letOp (n := 107) (.out 0x108918 (orR64R64Effect 0x108918 14 7) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 7] []) (.reg (.gpr 14))) #v[95, 89]
    (.letOp (n := 108) (.exec 0x108918 (fun s => s.RIP = 0x108918) (orR64R64Effect 0x108918 14 7) (Reg.operands [.gpr 14, .gpr 7] [])) #v[95, 89]
    (.letOp (n := 109) (.out 0x10891b (orR64R64Effect 0x10891b 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[103, 99]
    (.letOp (n := 110) (.exec 0x10891b (fun s => s.RIP = 0x10891b) (orR64R64Effect 0x10891b 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[103, 99]
    (.letOp (n := 111) (.exec 0x10891e (StorePre 0x10891e 3 (fun s => AddrMode.addr (.base 3 .none) s (0x10891e + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x10891e 2 (.base 3 .none)) (Reg.operands [.gpr 2, .gpr 3] [])) #v[109, 3]
    (.letOp (n := 112) (.exec 0x108921 (StorePre 0x108921 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x108921 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x108921 14 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 14, .gpr 3] [])) #v[107, 3]
    (.letOp (n := 113) (.exec 0x108925 (StorePre 0x108925 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x108925 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x108925 11 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 11, .gpr 3] [])) #v[105, 3]
    (.letOp (n := 114) (.exec 0x108929 (StorePre 0x108929 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x108929 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x108929 9 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 9, .gpr 3] [])) #v[79, 3]
    (.letOp (n := 115) (.exec 0x10892d (StorePre 0x10892d 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x10892d + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10892d 4 10 (.base 3 (.d8 0x20))) (Reg.operands [.gpr 10, .gpr 3] [])) #v[77, 3]
    (.letOp (n := 116) (.out 0x108931 (addR64Imm8Effect 0x108931 4 0x30) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 117) (.exec 0x108931 (fun s => s.RIP = 0x108931) (addR64Imm8Effect 0x108931 4 0x30) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 118) (.out 0x108935 (popR64Effect 0x108935 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[116]
    (.letOp (n := 119) (.out 0x108935 (popR64Effect 0x108935 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[116]
    (.letOp (n := 120) (.exec 0x108935 (PopPre 0x108935) (popR64Effect 0x108935 1 3) (Reg.operands [.gpr 4] [])) #v[116]
    (.letOp (n := 121) (.out 0x108936 (popR64Effect 0x108936 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[119]
    (.letOp (n := 122) (.out 0x108936 (popR64Effect 0x108936 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[119]
    (.letOp (n := 123) (.exec 0x108936 (PopPre 0x108936) (popR64Effect 0x108936 2 14) (Reg.operands [.gpr 4] [])) #v[119]
    (.letOp (n := 124) (.out 0x108938 (popR64Effect 0x108938 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[122]
    (.letOp (n := 125) (.out 0x108938 (popR64Effect 0x108938 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[122]
    (.letOp (n := 126) (.exec 0x108938 (PopPre 0x108938) (popR64Effect 0x108938 1 5) (Reg.operands [.gpr 4] [])) #v[122]
    (.letOp (n := 127) (.out 0x108939 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[125]
    (.letOp (n := 128) (.out 0x108939 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[125]
    (.letOp (n := 129) (.exec 0x108939 (RetPre 0x108939) (retEffect) (Reg.operands [.gpr 4] [])) #v[125]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 101), (2, 109), (3, 118), (4, 128), (5, 124), (6, 99), (7, 89), (8, 75), (9, 79), (10, 77), (11, 105), (12, 12), (13, 13), (14, 121), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 130) (some ⟨127, by decide⟩)))))))))))))))))))))))))))))))))))))))

def bytes_l1088c3_1 : List UInt8 :=
  [0x89, 0xE9, 0x49, 0xD3, 0xEE, 0x89, 0xC1, 0x48, 0xD3, 0xE6, 0x89, 0xE9, 0x48, 0xD3, 0xEA, 0x4D,
    0x09, 0xC3, 0x49, 0x09, 0xFE, 0x48, 0x09, 0xF2, 0x48, 0x89, 0x13, 0x4C, 0x89, 0x73, 0x08, 0x4C,
    0x89, 0x5B, 0x10, 0x4C, 0x89, 0x4B, 0x18, 0x44, 0x88, 0x53, 0x20, 0x48, 0x83, 0xC4, 0x30, 0x5B,
    0x41, 0x5E, 0x5D, 0xC3]

theorem code_l1088c3_1 : ∀ x ∈ codeRange 0x108906 bytes_l1088c3_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x8906 52 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1088c3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1088c3 (movR64M64Effect 0x1088c3 2 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 54) (.exec 0x1088c3 (LoadPre 0x1088c3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1088c3 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1088c3 2 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1088c7 (movR64M64Effect 0x1088c7 6 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 56) (.exec 0x1088c7 (LoadPre 0x1088c7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1088c7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1088c7 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1088cc (movR64M64Effect 0x1088cc 7 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 58) (.exec 0x1088cc (LoadPre 0x1088cc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1088cc + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1088cc 7 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x1088d1 (movR64M64Effect 0x1088d1 8 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 60) (.exec 0x1088d1 (LoadPre 0x1088d1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1088d1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1088d1 8 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x1088d6 (movR64M64Effect 0x1088d6 11 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 62) (.exec 0x1088d6 (LoadPre 0x1088d6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1088d6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1088d6 11 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x1088db (movR32R32Effect 0x1088db 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[0]
    (.letOp (n := 64) (.exec 0x1088db (fun s => s.RIP = 0x1088db) (movR32R32Effect 0x1088db 2 1 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 65) (.out 0x1088dd (shlR64ClEffect 0x1088dd 3 11) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[61, 63]
    (.letOp (n := 66) (.exec 0x1088dd (fun s => s.RIP = 0x1088dd) (shlR64ClEffect 0x1088dd 3 11) (Reg.operands [.gpr 11, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[61, 63]
    (.letOp (n := 67) (.out 0x1088e0 (movR64R64Effect 0x1088e0 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 8] []) (.reg (.gpr 9))) #v[59]
    (.letOp (n := 68) (.exec 0x1088e0 (fun s => s.RIP = 0x1088e0) (movR64R64Effect 0x1088e0 9 8) (Reg.operands [.gpr 8] [])) #v[59]
    (.letOp (n := 69) (.out 0x1088e3 (movR32R32Effect 0x1088e3 2 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[5]
    (.letOp (n := 70) (.exec 0x1088e3 (fun s => s.RIP = 0x1088e3) (movR32R32Effect 0x1088e3 2 1 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 71) (.out 0x1088e5 (shrR64ClEffect 0x1088e5 3 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[67, 69]
    (.letOp (n := 72) (.exec 0x1088e5 (fun s => s.RIP = 0x1088e5) (shrR64ClEffect 0x1088e5 3 9) (Reg.operands [.gpr 9, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[67, 69]
    (.letOp (n := 73) (.out 0x1088e8 (movR32R32Effect 0x1088e8 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[0]
    (.letOp (n := 74) (.exec 0x1088e8 (fun s => s.RIP = 0x1088e8) (movR32R32Effect 0x1088e8 2 1 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 75) (.out 0x1088ea (shlR64ClEffect 0x1088ea 3 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[59, 73]
    (.letOp (n := 76) (.exec 0x1088ea (fun s => s.RIP = 0x1088ea) (shlR64ClEffect 0x1088ea 3 8) (Reg.operands [.gpr 8, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[59, 73]
    (.letOp (n := 77) (.out 0x1088ed (movzxR32M8Effect 0x1088ed 6 10 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 78) (.exec 0x1088ed (LoadPre 0x1088ed (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1088ed + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1088ed 6 10 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.out 0x1088f3 (orR64R64Effect 0x1088f3 9 11) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 11] []) (.reg (.gpr 9))) #v[71, 65]
    (.letOp (n := 80) (.exec 0x1088f3 (fun s => s.RIP = 0x1088f3) (orR64R64Effect 0x1088f3 9 11) (Reg.operands [.gpr 9, .gpr 11] [])) #v[71, 65]
    (.letOp (n := 81) (.out 0x1088f6 (movR64R64Effect 0x1088f6 11 7) (EffectPart.reads (.reg (.gpr 11)) [.gpr 7] []) (.reg (.gpr 11))) #v[57]
    (.letOp (n := 82) (.exec 0x1088f6 (fun s => s.RIP = 0x1088f6) (movR64R64Effect 0x1088f6 11 7) (Reg.operands [.gpr 7] [])) #v[57]
    (.letOp (n := 83) (.out 0x1088f9 (movR32R32Effect 0x1088f9 2 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[5]
    (.letOp (n := 84) (.exec 0x1088f9 (fun s => s.RIP = 0x1088f9) (movR32R32Effect 0x1088f9 2 1 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 85) (.out 0x1088fb (shrR64ClEffect 0x1088fb 3 11) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[81, 83]
    (.letOp (n := 86) (.exec 0x1088fb (fun s => s.RIP = 0x1088fb) (shrR64ClEffect 0x1088fb 3 11) (Reg.operands [.gpr 11, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[81, 83]
    (.letOp (n := 87) (.out 0x1088fe (movR32R32Effect 0x1088fe 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[0]
    (.letOp (n := 88) (.exec 0x1088fe (fun s => s.RIP = 0x1088fe) (movR32R32Effect 0x1088fe 2 1 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 89) (.out 0x108900 (shlR64ClEffect 0x108900 3 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[57, 87]
    (.letOp (n := 90) (.exec 0x108900 (fun s => s.RIP = 0x108900) (shlR64ClEffect 0x108900 3 7) (Reg.operands [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[57, 87]
    (.letOp (n := 91) (.out 0x108903 (movR64R64Effect 0x108903 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 6] []) (.reg (.gpr 14))) #v[55]
    (.letOp (n := 92) (.exec 0x108903 (fun s => s.RIP = 0x108903) (movR64R64Effect 0x108903 14 6) (Reg.operands [.gpr 6] [])) #v[55]
    (b_l1088c3_1))))))))))))))))))))))))))))))))))))))))

def bytes_l1088c3 : List UInt8 :=
  [0x48, 0x8B, 0x14, 0x24, 0x48, 0x8B, 0x74, 0x24, 0x08, 0x48, 0x8B, 0x7C, 0x24, 0x10, 0x4C, 0x8B,
    0x44, 0x24, 0x18, 0x4C, 0x8B, 0x5C, 0x24, 0x20, 0x89, 0xC1, 0x49, 0xD3, 0xE3, 0x4D, 0x89, 0xC1,
    0x89, 0xE9, 0x49, 0xD3, 0xE9, 0x89, 0xC1, 0x49, 0xD3, 0xE0, 0x44, 0x0F, 0xB6, 0x54, 0x24, 0x28,
    0x4D, 0x09, 0xD9, 0x49, 0x89, 0xFB, 0x89, 0xE9, 0x49, 0xD3, 0xEB, 0x89, 0xC1, 0x48, 0xD3, 0xE7,
    0x49, 0x89, 0xF6] ++ bytes_l1088c3_1

theorem code_l1088c3 : ∀ x ∈ codeRange 0x1088c3 bytes_l1088c3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x88c3 67 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1088c3_1

@[cfg_block] def b_l10893a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10893a (movR32Imm32Effect 0x10893a 5 6 0x1b) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 54) (.exec 0x10893a (fun s => s.RIP = 0x10893a) (movR32Imm32Effect 0x10893a 5 6 0x1b) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x10893f (movR64Imm32Effect 0x10893f 7 0x202b38) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 56) (.exec 0x10893f (fun s => s.RIP = 0x10893f) (movR64Imm32Effect 0x10893f 7 0x202b38) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x108946 (movR64Imm32Effect 0x108946 2 0x202b58) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x108946 (fun s => s.RIP = 0x108946) (movR64Imm32Effect 0x108946 2 0x202b58) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x10894d (callEffect (fun _ => 0x129560) 0x108952) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x10894d (PushPre 0x10894d 5) (callEffect (fun _ => 0x129560) 0x108952) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x108952⟩) #v[]
    (.terminate (.call ⟨.l129560, RegMap.args [(2, 57), (4, 59), (5, 5), (6, 53), (7, 55)] 62⟩ { target := .l108952, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l10893a : List UInt8 :=
  [0xBE, 0x1B, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC7, 0x38, 0x2B, 0x20, 0x00, 0x48, 0xC7, 0xC2, 0x58,
    0x2B, 0x20, 0x00, 0xE8, 0x0E, 0x0C, 0x02, 0x00]

theorem code_l10893a : ∀ x ∈ codeRange 0x10893a bytes_l10893a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x893a 24 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l108952 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x108952 (movR32Imm32Effect 0x108952 5 6 0x1b) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 54) (.exec 0x108952 (fun s => s.RIP = 0x108952) (movR32Imm32Effect 0x108952 5 6 0x1b) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x108957 (movR64Imm32Effect 0x108957 7 0x202b38) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 56) (.exec 0x108957 (fun s => s.RIP = 0x108957) (movR64Imm32Effect 0x108957 7 0x202b38) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x10895e (movR64Imm32Effect 0x10895e 2 0x202b08) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x10895e (fun s => s.RIP = 0x10895e) (movR64Imm32Effect 0x10895e 2 0x202b08) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x108965 (callEffect (fun _ => 0x129560) 0x10896a) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x108965 (PushPre 0x108965 5) (callEffect (fun _ => 0x129560) 0x10896a) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x10896a⟩) #v[]
    (.terminate (.call ⟨.l129560, RegMap.args [(2, 57), (4, 59), (5, 5), (6, 53), (7, 55)] 62⟩ { target := .l10896a, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l108952 : List UInt8 :=
  [0xBE, 0x1B, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC7, 0x38, 0x2B, 0x20, 0x00, 0x48, 0xC7, 0xC2, 0x08,
    0x2B, 0x20, 0x00, 0xE8, 0xF6, 0x0B, 0x02, 0x00]

theorem code_l108952 : ∀ x ∈ codeRange 0x108952 bytes_l108952, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x8952 24 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10896a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10896a (movR32Imm32Effect 0x10896a 5 7 0x4) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 54) (.exec 0x10896a (fun s => s.RIP = 0x10896a) (movR32Imm32Effect 0x10896a 5 7 0x4) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x10896f (movR32Imm32Effect 0x10896f 5 6 0x4) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 56) (.exec 0x10896f (fun s => s.RIP = 0x10896f) (movR32Imm32Effect 0x10896f 5 6 0x4) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x108974 (movR64Imm32Effect 0x108974 2 0x202b20) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x108974 (fun s => s.RIP = 0x108974) (movR64Imm32Effect 0x108974 2 0x202b20) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x10897b (callEffect (fun _ => 0x1295f2) 0x108980) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x10897b (PushPre 0x10897b 5) (callEffect (fun _ => 0x1295f2) 0x108980) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x108980⟩) #v[]
    (.terminate (.call ⟨.l1295f2, RegMap.args [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)] 62⟩ { target := .l108980, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l10896a : List UInt8 :=
  [0xBF, 0x04, 0x00, 0x00, 0x00, 0xBE, 0x04, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC2, 0x20, 0x2B, 0x20,
    0x00, 0xE8, 0x72, 0x0C, 0x02, 0x00]

theorem code_l10896a : ∀ x ∈ codeRange 0x10896a bytes_l10896a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x896a 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l108980 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x108980 (pushR64Effect 0x108980 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x108980 (PushPre 0x108980 1) (pushR64Effect 0x108980 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x108981 (pushR64Effect 0x108981 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x108981 (PushPre 0x108981 2) (pushR64Effect 0x108981 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x108983 (pushR64Effect 0x108983 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x108983 (PushPre 0x108983 2) (pushR64Effect 0x108983 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x108985 (pushR64Effect 0x108985 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x108985 (PushPre 0x108985 2) (pushR64Effect 0x108985 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x108987 (pushR64Effect 0x108987 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x108987 (PushPre 0x108987 2) (pushR64Effect 0x108987 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x108989 (pushR64Effect 0x108989 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x108989 (PushPre 0x108989 1) (pushR64Effect 0x108989 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x10898a (subR64Imm8Effect 0x10898a 4 0x78) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x10898a (fun s => s.RIP = 0x10898a) (subR64Imm8Effect 0x10898a 4 0x78) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x10898e (movR32R32Effect 0x10898e 3 5 9) (EffectPart.reads (.reg (.gpr 5)) [.gpr 9] []) (.reg (.gpr 5))) #v[9]
    (.letOp (n := 68) (.exec 0x10898e (fun s => s.RIP = 0x10898e) (movR32R32Effect 0x10898e 3 5 9) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 69) (.out 0x108991 (movR64R64Effect 0x108991 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 70) (.exec 0x108991 (fun s => s.RIP = 0x108991) (movR64R64Effect 0x108991 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 71) (.out 0x108994 (leaR64Effect 0x108994 7 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[65]
    (.letOp (n := 72) (.exec 0x108994 (fun s => s.RIP = 0x108994) (leaR64Effect 0x108994 7 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 73) (.out 0x108999 (callEffect (fun _ => 0x1084e0) 0x10899e) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 74) (.exec 0x108999 (PushPre 0x108999 5) (callEffect (fun _ => 0x1084e0) 0x10899e) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 75) (.const ⟨64, 0x10899e⟩) #v[]
    (.terminate (.call ⟨.l1084e0, RegMap.args [(1, 1), (2, 2), (3, 69), (4, 73), (5, 67), (6, 6), (7, 71), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 76⟩ { target := .l10899e, kept := #v[], arity := rfl, guard := some (Fin.last 75) }))))))))))))))))))))))))

def bytes_l108980 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x83, 0xEC, 0x78, 0x44, 0x89,
    0xCD, 0x48, 0x89, 0xFB, 0x48, 0x8D, 0x7C, 0x24, 0x10, 0xE8, 0x42, 0xFB, 0xFF, 0xFF]

theorem code_l108980 : ∀ x ∈ codeRange 0x108980 bytes_l108980, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x8980 30 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10899e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10899e (movR32Imm32Effect 0x10899e 5 1 0x40) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 54) (.exec 0x10899e (fun s => s.RIP = 0x10899e) (movR32Imm32Effect 0x10899e 5 1 0x40) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.exec 0x1089a3 (StorePre 0x1089a3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x1089a3 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x1089a3 5 (.sib 4 none 0 (.d8 0x44))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[5, 4]
    (.letOp (n := 56) (.out 0x1089a7 (subR32R32Effect 0x1089a7 2 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 5] []) (.reg (.gpr 1))) #v[53, 5]
    (.letOp (n := 57) (.exec 0x1089a7 (fun s => s.RIP = 0x1089a7) (subR32R32Effect 0x1089a7 2 1 5) (Reg.operands [.gpr 1, .gpr 5] [])) #v[53, 5]
    (.letOp (n := 58) (.out 0x1089a9 (cmpR32Imm8Effect 0x1089a9 3 1 0x40) (EffectPart.reads (.flag .CF) [.gpr 1] []) (.flag .CF)) #v[56]
    (.letOp (n := 59) (.exec 0x1089a9 (fun s => s.RIP = 0x1089a9) (cmpR32Imm8Effect 0x1089a9 3 1 0x40) (Reg.operands [.gpr 1] [])) #v[56]
    (.letOp (n := 60) (.pure (condOp 3)) #v[58]
    (.terminate (.condBr (Fin.last 60) ⟨.l108df9, RegMap.args [(1, 56), (3, 3), (4, 4), (5, 5), (16, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩ ⟨.l1089b2, RegMap.args [(1, 56), (3, 3), (4, 4), (5, 5), (16, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩)))))))))

def bytes_l10899e : List UInt8 :=
  [0xB9, 0x40, 0x00, 0x00, 0x00, 0x89, 0x6C, 0x24, 0x44, 0x29, 0xE9, 0x83, 0xF9, 0x40, 0x0F, 0x83,
    0x47, 0x04, 0x00, 0x00]

theorem code_l10899e : ∀ x ∈ codeRange 0x10899e bytes_l10899e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x899e 20 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1089b2_6 : Block Op Label signature Reg.count 286 :=
  .letOp (n := 286) (.out 0x108b73 (movzxR32M8Effect 0x108b73 5 2 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 287) (.exec 0x108b73 (LoadPre 0x108b73 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108b73 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x108b73 5 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 288) (.exec 0x108b78 (StorePre 0x108b78 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108b78 + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 5) (setccM8Effect 0x108b78 5 (.sib 4 none 0 (.d8 0x10)))) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.ZF])) #v[4, 279]
    (.letOp (n := 289) (.out 0x108b7d (movzxR32M8Effect 0x108b7d 6 15 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 290) (.exec 0x108b7d (LoadPre 0x108b7d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108b7d + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108b7d 6 15 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 291) (.exec 0x108b83 (StorePre 0x108b83 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108b83 + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 5) (setccM8Effect 0x108b83 5 (.sib 4 none 0 (.d8 0x10)))) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.ZF])) #v[4, 279]
    (.letOp (n := 292) (.out 0x108b88 (movzxR32M8Effect 0x108b88 6 14 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 293) (.exec 0x108b88 (LoadPre 0x108b88 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108b88 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108b88 6 14 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 294) (.exec 0x108b8e (StorePre 0x108b8e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108b8e + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 5) (setccM8Effect 0x108b8e 5 (.sib 4 none 0 (.d8 0x10)))) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.ZF])) #v[4, 279]
    (.letOp (n := 295) (.out 0x108b93 (movzxR32M8Effect 0x108b93 5 7 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 296) (.exec 0x108b93 (LoadPre 0x108b93 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108b93 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x108b93 5 7 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 297) (.exec 0x108b98 (StorePre 0x108b98 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108b98 + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 5) (setccM8Effect 0x108b98 5 (.sib 4 none 0 (.d8 0x10)))) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.ZF])) #v[4, 279]
    (.letOp (n := 298) (.out 0x108b9d (leaR64Effect 0x108b9d 9 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 299) (.exec 0x108b9d (fun s => s.RIP = 0x108b9d) (leaR64Effect 0x108b9d 9 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 300) (.out 0x108ba2 (atFlags (condHolds 5) (setccR8Effect 0x108ba2 4 9)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 9))) #v[298, 279]
    (.letOp (n := 301) (.exec 0x108ba2 (fun s => s.RIP = 0x108ba2) (atFlags (condHolds 5) (setccR8Effect 0x108ba2 4 9)) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[298, 279]
    (.letOp (n := 302) (.out 0x108ba6 (cmpMImm8Effect 0x108ba6 5 32 (.sib 4 none 0 (.d8 0x44)) 0x40) (EffectPart.reads (.flag .CF) [.gpr 4] []) (.flag .CF)) #v[4]
    (.letOp (n := 303) (.exec 0x108ba6 (LoadPre 0x108ba6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x108ba6 + BitVec.ofNat 64 5)) 4) (cmpMImm8Effect 0x108ba6 5 32 (.sib 4 none 0 (.d8 0x44)) 0x40) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 304) (.pure (condOp 3)) #v[302]
    (.terminate (.condBr (Fin.last 304) ⟨.l108df9, RegMap.args [(0, 247), (1, 1), (2, 286), (3, 260), (4, 4), (5, 270), (6, 282), (7, 295), (8, 265), (9, 300), (10, 273), (11, 183), (12, 156), (13, 210), (14, 292), (15, 289), (16, 302), (22, 22), (39, 39), (50, 50), (51, 51)] 305⟩ ⟨.l108bb1, RegMap.args [(0, 247), (1, 1), (2, 286), (3, 260), (4, 4), (5, 270), (6, 282), (7, 295), (8, 265), (9, 300), (10, 273), (11, 183), (12, 156), (13, 210), (14, 292), (15, 289), (16, 302), (22, 22), (39, 39), (50, 50), (51, 51)] 305⟩))))))))))))))))))))

def bytes_l1089b2_6 : List UInt8 :=
  [0x0F, 0xB6, 0x54, 0x24, 0x10, 0x0F, 0x95, 0x44, 0x24, 0x10, 0x44, 0x0F, 0xB6, 0x7C, 0x24, 0x10,
    0x0F, 0x95, 0x44, 0x24, 0x10, 0x44, 0x0F, 0xB6, 0x74, 0x24, 0x10, 0x0F, 0x95, 0x44, 0x24, 0x10,
    0x0F, 0xB6, 0x7C, 0x24, 0x10, 0x0F, 0x95, 0x44, 0x24, 0x10, 0x4C, 0x8D, 0x4C, 0x24, 0x10, 0x41,
    0x0F, 0x95, 0xC1, 0x83, 0x7C, 0x24, 0x44, 0x40, 0x0F, 0x83, 0x48, 0x02, 0x00, 0x00]

theorem code_l1089b2_6 : ∀ x ∈ codeRange 0x108b73 bytes_l1089b2_6, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x8b73 62 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1089b2_5 : Block Op Label signature Reg.count 249 :=
  .letOp (n := 249) (.out 0x108b1f (andR64R64Effect 0x108b1f 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 0] []) (.reg (.gpr 14))) #v[243, 247]
    (.letOp (n := 250) (.exec 0x108b1f (fun s => s.RIP = 0x108b1f) (andR64R64Effect 0x108b1f 14 0) (Reg.operands [.gpr 14, .gpr 0] [])) #v[243, 247]
    (.letOp (n := 251) (.out 0x108b22 (orR64R64Effect 0x108b22 14 7) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 7] []) (.reg (.gpr 14))) #v[249, 241]
    (.letOp (n := 252) (.exec 0x108b22 (fun s => s.RIP = 0x108b22) (orR64R64Effect 0x108b22 14 7) (Reg.operands [.gpr 14, .gpr 7] [])) #v[249, 241]
    (.letOp (n := 253) (.out 0x108b25 (shrR64Effect 0x108b25 4 14 63) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[251]
    (.letOp (n := 254) (.exec 0x108b25 (fun s => s.RIP = 0x108b25) (shrR64Effect 0x108b25 4 14 63) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[251]
    (.letOp (n := 255) (.exec 0x108b29 (StorePre 0x108b29 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108b29 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108b29 14 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[253, 4]
    (.letOp (n := 256) (.exec 0x108b2e (fun s => s.RIP = 0x108b2e) (leaR64Effect 0x108b2e 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 257) (.exec 0x108b33 (StorePre 0x108b33 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x108b33 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108b33 5 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[123, 4]
    (.letOp (n := 258) (.out 0x108b38 (movR64R64Effect 0x108b38 3 5) (EffectPart.reads (.reg (.gpr 3)) [.gpr 5] []) (.reg (.gpr 3))) #v[123]
    (.letOp (n := 259) (.exec 0x108b38 (fun s => s.RIP = 0x108b38) (movR64R64Effect 0x108b38 3 5) (Reg.operands [.gpr 5] [])) #v[123]
    (.letOp (n := 260) (.out 0x108b3b (negR64Effect 0x108b3b 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[258]
    (.letOp (n := 261) (.out 0x108b3b (negR64Effect 0x108b3b 3) (EffectPart.reads (.flag .CF) [.gpr 3] []) (.flag .CF)) #v[258]
    (.letOp (n := 262) (.exec 0x108b3b (fun s => s.RIP = 0x108b3b) (negR64Effect 0x108b3b 3) (Reg.operands [.gpr 3] [])) #v[258]
    (.letOp (n := 263) (.out 0x108b3e (movR32Imm32Effect 0x108b3e 6 8 0x0) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 264) (.exec 0x108b3e (fun s => s.RIP = 0x108b3e) (movR32Imm32Effect 0x108b3e 6 8 0x0) (Reg.operands [] [])) #v[]
    (.letOp (n := 265) (.out 0x108b44 (atFlags StatusFlags.CF (sbbR64R64Effect 0x108b44 8 12)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[263, 156, 261]
    (.letOp (n := 266) (.out 0x108b44 (atFlags StatusFlags.CF (sbbR64R64Effect 0x108b44 8 12)) (Reg.operands [.gpr 8, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[263, 156, 261]
    (.letOp (n := 267) (.exec 0x108b44 (fun s => s.RIP = 0x108b44) (atFlags StatusFlags.CF (sbbR64R64Effect 0x108b44 8 12)) (Reg.operands [.gpr 8, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[263, 156, 261]
    (.letOp (n := 268) (.out 0x108b47 (movR32Imm32Effect 0x108b47 5 5 0x0) (EffectPart.reads (.reg (.gpr 5)) [] []) (.reg (.gpr 5))) #v[]
    (.letOp (n := 269) (.exec 0x108b47 (fun s => s.RIP = 0x108b47) (movR32Imm32Effect 0x108b47 5 5 0x0) (Reg.operands [] [])) #v[]
    (.letOp (n := 270) (.out 0x108b4c (atFlags StatusFlags.CF (sbbR64R64Effect 0x108b4c 5 11)) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 5))) #v[268, 183, 266]
    (.letOp (n := 271) (.out 0x108b4c (atFlags StatusFlags.CF (sbbR64R64Effect 0x108b4c 5 11)) (Reg.operands [.gpr 5, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[268, 183, 266]
    (.letOp (n := 272) (.exec 0x108b4c (fun s => s.RIP = 0x108b4c) (atFlags StatusFlags.CF (sbbR64R64Effect 0x108b4c 5 11)) (Reg.operands [.gpr 5, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[268, 183, 266]
    (.letOp (n := 273) (.out 0x108b4f (atFlags StatusFlags.CF (sbbR64R64Effect 0x108b4f 10 13)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[220, 210, 271]
    (.letOp (n := 274) (.out 0x108b4f (atFlags StatusFlags.CF (sbbR64R64Effect 0x108b4f 10 13)) (Reg.operands [.gpr 10, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[220, 210, 271]
    (.letOp (n := 275) (.exec 0x108b4f (fun s => s.RIP = 0x108b4f) (atFlags StatusFlags.CF (sbbR64R64Effect 0x108b4f 10 13)) (Reg.operands [.gpr 10, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[220, 210, 271]
    (.letOp (n := 276) (.out 0x108b52 (movR64M64Effect 0x108b52 2 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 277) (.exec 0x108b52 (LoadPre 0x108b52 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108b52 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x108b52 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 278) (.exec 0x108b57 (StorePre 0x108b57 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108b57 + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 3) (setccM8Effect 0x108b57 5 (.sib 4 none 0 (.d8 0x10)))) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[4, 274]
    (.letOp (n := 279) (.out 0x108b5c (testR64R64Effect 0x108b5c 2 2) (EffectPart.reads (.flag .ZF) [.gpr 2, .gpr 2] []) (.flag .ZF)) #v[276, 276]
    (.letOp (n := 280) (.exec 0x108b5c (fun s => s.RIP = 0x108b5c) (testR64R64Effect 0x108b5c 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[276, 276]
    (.letOp (n := 281) (.exec 0x108b5f (fun s => s.RIP = 0x108b5f) (leaR64Effect 0x108b5f 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 282) (.out 0x108b64 (movzxR32M8Effect 0x108b64 5 6 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 283) (.exec 0x108b64 (LoadPre 0x108b64 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108b64 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x108b64 5 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 284) (.exec 0x108b69 (StorePre 0x108b69 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108b69 + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 5) (setccM8Effect 0x108b69 5 (.sib 4 none 0 (.d8 0x10)))) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.ZF])) #v[4, 279]
    (.letOp (n := 285) (.exec 0x108b6e (fun s => s.RIP = 0x108b6e) (leaR64Effect 0x108b6e 7 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l1089b2_6)))))))))))))))))))))))))))))))))))))

def bytes_l1089b2_5 : List UInt8 :=
  [0x49, 0x21, 0xC6, 0x49, 0x09, 0xFE, 0x49, 0xC1, 0xEE, 0x3F, 0x4C, 0x89, 0x74, 0x24, 0x10, 0x48,
    0x8D, 0x54, 0x24, 0x10, 0x48, 0x89, 0x6C, 0x24, 0x48, 0x48, 0x89, 0xEB, 0x48, 0xF7, 0xDB, 0x41,
    0xB8, 0x00, 0x00, 0x00, 0x00, 0x4D, 0x19, 0xE0, 0xBD, 0x00, 0x00, 0x00, 0x00, 0x4C, 0x19, 0xDD,
    0x4D, 0x19, 0xEA, 0x48, 0x8B, 0x54, 0x24, 0x10, 0x0F, 0x93, 0x44, 0x24, 0x10, 0x48, 0x85, 0xD2,
    0x48, 0x8D, 0x54, 0x24, 0x10, 0x0F, 0xB6, 0x74, 0x24, 0x10, 0x0F, 0x95, 0x44, 0x24, 0x10, 0x48,
    0x8D, 0x7C, 0x24, 0x10] ++ bytes_l1089b2_6

theorem code_l1089b2_5 : ∀ x ∈ codeRange 0x108b1f bytes_l1089b2_5, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x8b1f 84 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1089b2_6

@[cfg_block] def b_l1089b2_4 : Block Op Label signature Reg.count 210 :=
  .letOp (n := 210) (.out 0x108ade (addR64R64Effect 0x108ade 13 8) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 8] []) (.reg (.gpr 13))) #v[208, 206]
    (.letOp (n := 211) (.exec 0x108ade (fun s => s.RIP = 0x108ade) (addR64R64Effect 0x108ade 13 8) (Reg.operands [.gpr 13, .gpr 8] [])) #v[208, 206]
    (.letOp (n := 212) (.out 0x108ae1 (notR64Effect 0x108ae1 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[111]
    (.letOp (n := 213) (.exec 0x108ae1 (fun s => s.RIP = 0x108ae1) (notR64Effect 0x108ae1 7) (Reg.operands [.gpr 7] [])) #v[111]
    (.letOp (n := 214) (.out 0x108ae4 (movR64R64Effect 0x108ae4 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[116]
    (.letOp (n := 215) (.exec 0x108ae4 (fun s => s.RIP = 0x108ae4) (movR64R64Effect 0x108ae4 8 0) (Reg.operands [.gpr 0] [])) #v[116]
    (.letOp (n := 216) (.out 0x108ae7 (andR64R64Effect 0x108ae7 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 7] []) (.reg (.gpr 8))) #v[214, 212]
    (.letOp (n := 217) (.exec 0x108ae7 (fun s => s.RIP = 0x108ae7) (andR64R64Effect 0x108ae7 8 7) (Reg.operands [.gpr 8, .gpr 7] [])) #v[214, 212]
    (.letOp (n := 218) (.out 0x108aea (orR64R64Effect 0x108aea 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[212, 116]
    (.letOp (n := 219) (.exec 0x108aea (fun s => s.RIP = 0x108aea) (orR64R64Effect 0x108aea 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[212, 116]
    (.letOp (n := 220) (.out 0x108aed (xorR32R32Effect 0x108aed 3 10 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 10] []) (.reg (.gpr 10))) #v[113, 113]
    (.letOp (n := 221) (.exec 0x108aed (fun s => s.RIP = 0x108aed) (xorR32R32Effect 0x108aed 3 10 10) (Reg.operands [.gpr 10, .gpr 10] [])) #v[113, 113]
    (.letOp (n := 222) (.out 0x108af0 (andR64R64Effect 0x108af0 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 13] []) (.reg (.gpr 7))) #v[218, 210]
    (.letOp (n := 223) (.exec 0x108af0 (fun s => s.RIP = 0x108af0) (andR64R64Effect 0x108af0 7 13) (Reg.operands [.gpr 7, .gpr 13] [])) #v[218, 210]
    (.letOp (n := 224) (.out 0x108af3 (orR64R64Effect 0x108af3 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 8] []) (.reg (.gpr 7))) #v[222, 216]
    (.letOp (n := 225) (.exec 0x108af3 (fun s => s.RIP = 0x108af3) (orR64R64Effect 0x108af3 7 8) (Reg.operands [.gpr 7, .gpr 8] [])) #v[222, 216]
    (.letOp (n := 226) (.out 0x108af6 (shrR64Effect 0x108af6 4 7 63) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[224]
    (.letOp (n := 227) (.exec 0x108af6 (fun s => s.RIP = 0x108af6) (shrR64Effect 0x108af6 4 7 63) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[224]
    (.letOp (n := 228) (.exec 0x108afa (StorePre 0x108afa 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108afa + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108afa 7 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[226, 4]
    (.letOp (n := 229) (.out 0x108aff (xorR32R32Effect 0x108aff 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[116, 116]
    (.letOp (n := 230) (.exec 0x108aff (fun s => s.RIP = 0x108aff) (xorR32R32Effect 0x108aff 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[116, 116]
    (.letOp (n := 231) (.out 0x108b01 (subR64M64Effect 0x108b01 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[229, 4]
    (.letOp (n := 232) (.exec 0x108b01 (LoadPre 0x108b01 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108b01 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x108b01 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[229, 4]
    (.letOp (n := 233) (.out 0x108b06 (movR64R64Effect 0x108b06 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[133]
    (.letOp (n := 234) (.exec 0x108b06 (fun s => s.RIP = 0x108b06) (movR64R64Effect 0x108b06 6 14) (Reg.operands [.gpr 14] [])) #v[133]
    (.letOp (n := 235) (.out 0x108b09 (subR64R64Effect 0x108b09 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[233, 119]
    (.letOp (n := 236) (.exec 0x108b09 (fun s => s.RIP = 0x108b09) (subR64R64Effect 0x108b09 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[233, 119]
    (.letOp (n := 237) (.out 0x108b0c (notR64Effect 0x108b0c 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14] []) (.reg (.gpr 14))) #v[133]
    (.letOp (n := 238) (.exec 0x108b0c (fun s => s.RIP = 0x108b0c) (notR64Effect 0x108b0c 14) (Reg.operands [.gpr 14] [])) #v[133]
    (.letOp (n := 239) (.out 0x108b0f (movR64R64Effect 0x108b0f 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[119]
    (.letOp (n := 240) (.exec 0x108b0f (fun s => s.RIP = 0x108b0f) (movR64R64Effect 0x108b0f 7 2) (Reg.operands [.gpr 2] [])) #v[119]
    (.letOp (n := 241) (.out 0x108b12 (andR64R64Effect 0x108b12 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 14] []) (.reg (.gpr 7))) #v[239, 237]
    (.letOp (n := 242) (.exec 0x108b12 (fun s => s.RIP = 0x108b12) (andR64R64Effect 0x108b12 7 14) (Reg.operands [.gpr 7, .gpr 14] [])) #v[239, 237]
    (.letOp (n := 243) (.out 0x108b15 (orR64R64Effect 0x108b15 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 2] []) (.reg (.gpr 14))) #v[237, 119]
    (.letOp (n := 244) (.exec 0x108b15 (fun s => s.RIP = 0x108b15) (orR64R64Effect 0x108b15 14 2) (Reg.operands [.gpr 14, .gpr 2] [])) #v[237, 119]
    (.letOp (n := 245) (.out 0x108b18 (sarR64Effect 0x108b18 4 0 63) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[231]
    (.letOp (n := 246) (.exec 0x108b18 (fun s => s.RIP = 0x108b18) (sarR64Effect 0x108b18 4 0 63) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[231]
    (.letOp (n := 247) (.out 0x108b1c (addR64R64Effect 0x108b1c 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[245, 235]
    (.letOp (n := 248) (.exec 0x108b1c (fun s => s.RIP = 0x108b1c) (addR64R64Effect 0x108b1c 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[245, 235]
    (b_l1089b2_5)))))))))))))))))))))))))))))))))))))))

def bytes_l1089b2_4 : List UInt8 :=
  [0x4D, 0x01, 0xC5, 0x48, 0xF7, 0xD7, 0x49, 0x89, 0xC0, 0x49, 0x21, 0xF8, 0x48, 0x09, 0xC7, 0x45,
    0x31, 0xD2, 0x4C, 0x21, 0xEF, 0x4C, 0x09, 0xC7, 0x48, 0xC1, 0xEF, 0x3F, 0x48, 0x89, 0x7C, 0x24,
    0x10, 0x31, 0xC0, 0x48, 0x2B, 0x44, 0x24, 0x10, 0x4C, 0x89, 0xF6, 0x48, 0x29, 0xD6, 0x49, 0xF7,
    0xD6, 0x48, 0x89, 0xD7, 0x4C, 0x21, 0xF7, 0x49, 0x09, 0xD6, 0x48, 0xC1, 0xF8, 0x3F, 0x48, 0x01,
    0xF0] ++ bytes_l1089b2_5

theorem code_l1089b2_4 : ∀ x ∈ codeRange 0x108ade bytes_l1089b2_4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x8ade 65 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1089b2_5

@[cfg_block] def b_l1089b2_3 : Block Op Label signature Reg.count 172 :=
  .letOp (n := 172) (.exec 0x108a97 (StorePre 0x108a97 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108a97 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108a97 8 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[170, 4]
    (.letOp (n := 173) (.out 0x108a9c (xorR32R32Effect 0x108a9c 3 11 11) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 11] []) (.reg (.gpr 11))) #v[108, 108]
    (.letOp (n := 174) (.exec 0x108a9c (fun s => s.RIP = 0x108a9c) (xorR32R32Effect 0x108a9c 3 11 11) (Reg.operands [.gpr 11, .gpr 11] [])) #v[108, 108]
    (.letOp (n := 175) (.out 0x108a9f (subR64M64Effect 0x108a9f 11 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 4] []) (.reg (.gpr 11))) #v[173, 4]
    (.letOp (n := 176) (.exec 0x108a9f (LoadPre 0x108a9f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108a9f + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x108a9f 11 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[173, 4]
    (.letOp (n := 177) (.out 0x108aa4 (movR64R64Effect 0x108aa4 8 3) (EffectPart.reads (.reg (.gpr 8)) [.gpr 3] []) (.reg (.gpr 8))) #v[68]
    (.letOp (n := 178) (.exec 0x108aa4 (fun s => s.RIP = 0x108aa4) (movR64R64Effect 0x108aa4 8 3) (Reg.operands [.gpr 3] [])) #v[68]
    (.letOp (n := 179) (.out 0x108aa7 (subR64R64Effect 0x108aa7 8 10) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 10] []) (.reg (.gpr 8))) #v[177, 113]
    (.letOp (n := 180) (.exec 0x108aa7 (fun s => s.RIP = 0x108aa7) (subR64R64Effect 0x108aa7 8 10) (Reg.operands [.gpr 8, .gpr 10] [])) #v[177, 113]
    (.letOp (n := 181) (.out 0x108aaa (sarR64Effect 0x108aaa 4 11 63) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[175]
    (.letOp (n := 182) (.exec 0x108aaa (fun s => s.RIP = 0x108aaa) (sarR64Effect 0x108aaa 4 11 63) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[175]
    (.letOp (n := 183) (.out 0x108aae (addR64R64Effect 0x108aae 11 8) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 8] []) (.reg (.gpr 11))) #v[181, 179]
    (.letOp (n := 184) (.exec 0x108aae (fun s => s.RIP = 0x108aae) (addR64R64Effect 0x108aae 11 8) (Reg.operands [.gpr 11, .gpr 8] [])) #v[181, 179]
    (.letOp (n := 185) (.out 0x108ab1 (notR64Effect 0x108ab1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[68]
    (.letOp (n := 186) (.exec 0x108ab1 (fun s => s.RIP = 0x108ab1) (notR64Effect 0x108ab1 3) (Reg.operands [.gpr 3] [])) #v[68]
    (.letOp (n := 187) (.out 0x108ab4 (movR64R64Effect 0x108ab4 8 10) (EffectPart.reads (.reg (.gpr 8)) [.gpr 10] []) (.reg (.gpr 8))) #v[113]
    (.letOp (n := 188) (.exec 0x108ab4 (fun s => s.RIP = 0x108ab4) (movR64R64Effect 0x108ab4 8 10) (Reg.operands [.gpr 10] [])) #v[113]
    (.letOp (n := 189) (.out 0x108ab7 (andR64R64Effect 0x108ab7 8 3) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 3] []) (.reg (.gpr 8))) #v[187, 185]
    (.letOp (n := 190) (.exec 0x108ab7 (fun s => s.RIP = 0x108ab7) (andR64R64Effect 0x108ab7 8 3) (Reg.operands [.gpr 8, .gpr 3] [])) #v[187, 185]
    (.letOp (n := 191) (.out 0x108aba (orR64R64Effect 0x108aba 3 10) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 10] []) (.reg (.gpr 3))) #v[185, 113]
    (.letOp (n := 192) (.exec 0x108aba (fun s => s.RIP = 0x108aba) (orR64R64Effect 0x108aba 3 10) (Reg.operands [.gpr 3, .gpr 10] [])) #v[185, 113]
    (.letOp (n := 193) (.out 0x108abd (andR64R64Effect 0x108abd 3 11) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 11] []) (.reg (.gpr 3))) #v[191, 183]
    (.letOp (n := 194) (.exec 0x108abd (fun s => s.RIP = 0x108abd) (andR64R64Effect 0x108abd 3 11) (Reg.operands [.gpr 3, .gpr 11] [])) #v[191, 183]
    (.letOp (n := 195) (.out 0x108ac0 (orR64R64Effect 0x108ac0 3 8) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 8] []) (.reg (.gpr 3))) #v[193, 189]
    (.letOp (n := 196) (.exec 0x108ac0 (fun s => s.RIP = 0x108ac0) (orR64R64Effect 0x108ac0 3 8) (Reg.operands [.gpr 3, .gpr 8] [])) #v[193, 189]
    (.letOp (n := 197) (.out 0x108ac3 (shrR64Effect 0x108ac3 4 3 63) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[195]
    (.letOp (n := 198) (.exec 0x108ac3 (fun s => s.RIP = 0x108ac3) (shrR64Effect 0x108ac3 4 3 63) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[195]
    (.letOp (n := 199) (.exec 0x108ac7 (StorePre 0x108ac7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108ac7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108ac7 3 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[197, 4]
    (.letOp (n := 200) (.out 0x108acc (xorR32R32Effect 0x108acc 3 13 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 13] []) (.reg (.gpr 13))) #v[100, 100]
    (.letOp (n := 201) (.exec 0x108acc (fun s => s.RIP = 0x108acc) (xorR32R32Effect 0x108acc 3 13 13) (Reg.operands [.gpr 13, .gpr 13] [])) #v[100, 100]
    (.letOp (n := 202) (.out 0x108acf (subR64M64Effect 0x108acf 13 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 4] []) (.reg (.gpr 13))) #v[200, 4]
    (.letOp (n := 203) (.exec 0x108acf (LoadPre 0x108acf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108acf + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x108acf 13 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[200, 4]
    (.letOp (n := 204) (.out 0x108ad4 (movR64R64Effect 0x108ad4 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 7] []) (.reg (.gpr 8))) #v[111]
    (.letOp (n := 205) (.exec 0x108ad4 (fun s => s.RIP = 0x108ad4) (movR64R64Effect 0x108ad4 8 7) (Reg.operands [.gpr 7] [])) #v[111]
    (.letOp (n := 206) (.out 0x108ad7 (subR64R64Effect 0x108ad7 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[204, 116]
    (.letOp (n := 207) (.exec 0x108ad7 (fun s => s.RIP = 0x108ad7) (subR64R64Effect 0x108ad7 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[204, 116]
    (.letOp (n := 208) (.out 0x108ada (sarR64Effect 0x108ada 4 13 63) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[202]
    (.letOp (n := 209) (.exec 0x108ada (fun s => s.RIP = 0x108ada) (sarR64Effect 0x108ada 4 13 63) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[202]
    (b_l1089b2_4))))))))))))))))))))))))))))))))))))))

def bytes_l1089b2_3 : List UInt8 :=
  [0x4C, 0x89, 0x44, 0x24, 0x10, 0x45, 0x31, 0xDB, 0x4C, 0x2B, 0x5C, 0x24, 0x10, 0x49, 0x89, 0xD8,
    0x4D, 0x29, 0xD0, 0x49, 0xC1, 0xFB, 0x3F, 0x4D, 0x01, 0xC3, 0x48, 0xF7, 0xD3, 0x4D, 0x89, 0xD0,
    0x49, 0x21, 0xD8, 0x4C, 0x09, 0xD3, 0x4C, 0x21, 0xDB, 0x4C, 0x09, 0xC3, 0x48, 0xC1, 0xEB, 0x3F,
    0x48, 0x89, 0x5C, 0x24, 0x10, 0x45, 0x31, 0xED, 0x4C, 0x2B, 0x6C, 0x24, 0x10, 0x49, 0x89, 0xF8,
    0x49, 0x29, 0xC0, 0x49, 0xC1, 0xFD, 0x3F] ++ bytes_l1089b2_4

theorem code_l1089b2_3 : ∀ x ∈ codeRange 0x108a97 bytes_l1089b2_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x8a97 71 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1089b2_4

@[cfg_block] def b_l1089b2_2 : Block Op Label signature Reg.count 135 :=
  .letOp (n := 135) (.out 0x108a4d (andR64R64Effect 0x108a4d 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 5] []) (.reg (.gpr 6))) #v[131, 123]
    (.letOp (n := 136) (.exec 0x108a4d (fun s => s.RIP = 0x108a4d) (andR64R64Effect 0x108a4d 6 5) (Reg.operands [.gpr 6, .gpr 5] [])) #v[131, 123]
    (.letOp (n := 137) (.out 0x108a50 (orR64R64Effect 0x108a50 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 15] []) (.reg (.gpr 6))) #v[135, 129]
    (.letOp (n := 138) (.exec 0x108a50 (fun s => s.RIP = 0x108a50) (orR64R64Effect 0x108a50 6 15) (Reg.operands [.gpr 6, .gpr 15] [])) #v[135, 129]
    (.letOp (n := 139) (.out 0x108a53 (movzxR32M8Effect 0x108a53 6 9 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 140) (.exec 0x108a53 (LoadPre 0x108a53 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x108a53 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108a53 6 9 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 141) (.exec 0x108a59 (StorePre 0x108a59 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x108a59 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108a59 5 9 (.sib 4 none 0 (.d8 0xf))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[139, 4]
    (.letOp (n := 142) (.out 0x108a5e (shrR64Effect 0x108a5e 4 6 63) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[137]
    (.letOp (n := 143) (.exec 0x108a5e (fun s => s.RIP = 0x108a5e) (shrR64Effect 0x108a5e 4 6 63) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[137]
    (.letOp (n := 144) (.exec 0x108a62 (StorePre 0x108a62 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108a62 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108a62 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[142, 4]
    (.letOp (n := 145) (.exec 0x108a67 (fun s => s.RIP = 0x108a67) (leaR64Effect 0x108a67 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 146) (.out 0x108a6c (xorR32R32Effect 0x108a6c 3 12 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 12] []) (.reg (.gpr 12))) #v[90, 90]
    (.letOp (n := 147) (.exec 0x108a6c (fun s => s.RIP = 0x108a6c) (xorR32R32Effect 0x108a6c 3 12 12) (Reg.operands [.gpr 12, .gpr 12] [])) #v[90, 90]
    (.letOp (n := 148) (.out 0x108a6f (subR64M64Effect 0x108a6f 12 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 4] []) (.reg (.gpr 12))) #v[146, 4]
    (.letOp (n := 149) (.exec 0x108a6f (LoadPre 0x108a6f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108a6f + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x108a6f 12 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[146, 4]
    (.letOp (n := 150) (.out 0x108a74 (movR64R64Effect 0x108a74 15 8) (EffectPart.reads (.reg (.gpr 15)) [.gpr 8] []) (.reg (.gpr 15))) #v[66]
    (.letOp (n := 151) (.exec 0x108a74 (fun s => s.RIP = 0x108a74) (movR64R64Effect 0x108a74 15 8) (Reg.operands [.gpr 8] [])) #v[66]
    (.letOp (n := 152) (.out 0x108a77 (subR64R64Effect 0x108a77 15 11) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 11] []) (.reg (.gpr 15))) #v[150, 108]
    (.letOp (n := 153) (.exec 0x108a77 (fun s => s.RIP = 0x108a77) (subR64R64Effect 0x108a77 15 11) (Reg.operands [.gpr 15, .gpr 11] [])) #v[150, 108]
    (.letOp (n := 154) (.out 0x108a7a (sarR64Effect 0x108a7a 4 12 63) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[148]
    (.letOp (n := 155) (.exec 0x108a7a (fun s => s.RIP = 0x108a7a) (sarR64Effect 0x108a7a 4 12 63) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[148]
    (.letOp (n := 156) (.out 0x108a7e (addR64R64Effect 0x108a7e 12 15) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 15] []) (.reg (.gpr 12))) #v[154, 152]
    (.letOp (n := 157) (.exec 0x108a7e (fun s => s.RIP = 0x108a7e) (addR64R64Effect 0x108a7e 12 15) (Reg.operands [.gpr 12, .gpr 15] [])) #v[154, 152]
    (.letOp (n := 158) (.out 0x108a81 (notR64Effect 0x108a81 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[66]
    (.letOp (n := 159) (.exec 0x108a81 (fun s => s.RIP = 0x108a81) (notR64Effect 0x108a81 8) (Reg.operands [.gpr 8] [])) #v[66]
    (.letOp (n := 160) (.out 0x108a84 (movR64R64Effect 0x108a84 15 11) (EffectPart.reads (.reg (.gpr 15)) [.gpr 11] []) (.reg (.gpr 15))) #v[108]
    (.letOp (n := 161) (.exec 0x108a84 (fun s => s.RIP = 0x108a84) (movR64R64Effect 0x108a84 15 11) (Reg.operands [.gpr 11] [])) #v[108]
    (.letOp (n := 162) (.out 0x108a87 (andR64R64Effect 0x108a87 15 8) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 8] []) (.reg (.gpr 15))) #v[160, 158]
    (.letOp (n := 163) (.exec 0x108a87 (fun s => s.RIP = 0x108a87) (andR64R64Effect 0x108a87 15 8) (Reg.operands [.gpr 15, .gpr 8] [])) #v[160, 158]
    (.letOp (n := 164) (.out 0x108a8a (orR64R64Effect 0x108a8a 8 11) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 11] []) (.reg (.gpr 8))) #v[158, 108]
    (.letOp (n := 165) (.exec 0x108a8a (fun s => s.RIP = 0x108a8a) (orR64R64Effect 0x108a8a 8 11) (Reg.operands [.gpr 8, .gpr 11] [])) #v[158, 108]
    (.letOp (n := 166) (.out 0x108a8d (andR64R64Effect 0x108a8d 8 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 12] []) (.reg (.gpr 8))) #v[164, 156]
    (.letOp (n := 167) (.exec 0x108a8d (fun s => s.RIP = 0x108a8d) (andR64R64Effect 0x108a8d 8 12) (Reg.operands [.gpr 8, .gpr 12] [])) #v[164, 156]
    (.letOp (n := 168) (.out 0x108a90 (orR64R64Effect 0x108a90 8 15) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 15] []) (.reg (.gpr 8))) #v[166, 162]
    (.letOp (n := 169) (.exec 0x108a90 (fun s => s.RIP = 0x108a90) (orR64R64Effect 0x108a90 8 15) (Reg.operands [.gpr 8, .gpr 15] [])) #v[166, 162]
    (.letOp (n := 170) (.out 0x108a93 (shrR64Effect 0x108a93 4 8 63) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[168]
    (.letOp (n := 171) (.exec 0x108a93 (fun s => s.RIP = 0x108a93) (shrR64Effect 0x108a93 4 8 63) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[168]
    (b_l1089b2_3)))))))))))))))))))))))))))))))))))))

def bytes_l1089b2_2 : List UInt8 :=
  [0x48, 0x21, 0xEE, 0x4C, 0x09, 0xFE, 0x44, 0x0F, 0xB6, 0x4C, 0x24, 0x38, 0x44, 0x88, 0x4C, 0x24,
    0x0F, 0x48, 0xC1, 0xEE, 0x3F, 0x48, 0x89, 0x74, 0x24, 0x10, 0x48, 0x8D, 0x74, 0x24, 0x10, 0x45,
    0x31, 0xE4, 0x4C, 0x2B, 0x64, 0x24, 0x10, 0x4D, 0x89, 0xC7, 0x4D, 0x29, 0xDF, 0x49, 0xC1, 0xFC,
    0x3F, 0x4D, 0x01, 0xFC, 0x49, 0xF7, 0xD0, 0x4D, 0x89, 0xDF, 0x4D, 0x21, 0xC7, 0x4D, 0x09, 0xD8,
    0x4D, 0x21, 0xE0, 0x4D, 0x09, 0xF8, 0x49, 0xC1, 0xE8, 0x3F] ++ bytes_l1089b2_3

theorem code_l1089b2_2 : ∀ x ∈ codeRange 0x108a4d bytes_l1089b2_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x8a4d 74 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1089b2_3

@[cfg_block] def b_l1089b2_1 : Block Op Label signature Reg.count 92 :=
  .letOp (n := 92) (.out 0x108a06 (movR64M64Effect 0x108a06 0 (.base 7 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[54]
    (.letOp (n := 93) (.exec 0x108a06 (LoadPre 0x108a06 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x108a06 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x108a06 0 (.base 7 (.d8 0x10))) (Reg.operands [.gpr 7] [])) #v[54]
    (.letOp (n := 94) (.exec 0x108a0a (StorePre 0x108a0a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x108a0a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108a0a 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[92, 4]
    (.letOp (n := 95) (.out 0x108a0f (mulR64Effect 0x108a0f 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[64, 92]
    (.letOp (n := 96) (.out 0x108a0f (mulR64Effect 0x108a0f 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[64, 92]
    (.letOp (n := 97) (.exec 0x108a0f (fun s => s.RIP = 0x108a0f) (mulR64Effect 0x108a0f 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[64, 92]
    (.letOp (n := 98) (.out 0x108a12 (movR64R64Effect 0x108a12 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[95]
    (.letOp (n := 99) (.exec 0x108a12 (fun s => s.RIP = 0x108a12) (movR64R64Effect 0x108a12 10 0) (Reg.operands [.gpr 0] [])) #v[95]
    (.letOp (n := 100) (.out 0x108a15 (movR64R64Effect 0x108a15 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[96]
    (.letOp (n := 101) (.exec 0x108a15 (fun s => s.RIP = 0x108a15) (movR64R64Effect 0x108a15 13 2) (Reg.operands [.gpr 2] [])) #v[96]
    (.letOp (n := 102) (.out 0x108a18 (movR64M64Effect 0x108a18 0 (.base 7 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[54]
    (.letOp (n := 103) (.exec 0x108a18 (LoadPre 0x108a18 (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x108a18 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x108a18 0 (.base 7 (.d8 0x18))) (Reg.operands [.gpr 7] [])) #v[54]
    (.letOp (n := 104) (.exec 0x108a1c (StorePre 0x108a1c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x108a1c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108a1c 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[102, 4]
    (.letOp (n := 105) (.out 0x108a21 (mulR64Effect 0x108a21 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[64, 102]
    (.letOp (n := 106) (.out 0x108a21 (mulR64Effect 0x108a21 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[64, 102]
    (.letOp (n := 107) (.exec 0x108a21 (fun s => s.RIP = 0x108a21) (mulR64Effect 0x108a21 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[64, 102]
    (.letOp (n := 108) (.out 0x108a24 (addR64R64Effect 0x108a24 11 15) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 15] []) (.reg (.gpr 11))) #v[88, 78]
    (.letOp (n := 109) (.out 0x108a24 (addR64R64Effect 0x108a24 11 15) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 15] []) (.flag .CF)) #v[88, 78]
    (.letOp (n := 110) (.exec 0x108a24 (fun s => s.RIP = 0x108a24) (addR64R64Effect 0x108a24 11 15) (Reg.operands [.gpr 11, .gpr 15] [])) #v[88, 78]
    (.letOp (n := 111) (.out 0x108a27 (movR64M64Effect 0x108a27 7 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 112) (.exec 0x108a27 (LoadPre 0x108a27 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x108a27 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x108a27 7 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 113) (.out 0x108a2c (atFlags StatusFlags.CF (adcR64R64Effect 0x108a2c 10 12)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[98, 90, 109]
    (.letOp (n := 114) (.out 0x108a2c (atFlags StatusFlags.CF (adcR64R64Effect 0x108a2c 10 12)) (Reg.operands [.gpr 10, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[98, 90, 109]
    (.letOp (n := 115) (.exec 0x108a2c (fun s => s.RIP = 0x108a2c) (atFlags StatusFlags.CF (adcR64R64Effect 0x108a2c 10 12)) (Reg.operands [.gpr 10, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[98, 90, 109]
    (.letOp (n := 116) (.out 0x108a2f (atFlags StatusFlags.CF (adcR64R64Effect 0x108a2f 0 13)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 0))) #v[105, 100, 114]
    (.letOp (n := 117) (.out 0x108a2f (atFlags StatusFlags.CF (adcR64R64Effect 0x108a2f 0 13)) (Reg.operands [.gpr 0, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[105, 100, 114]
    (.letOp (n := 118) (.exec 0x108a2f (fun s => s.RIP = 0x108a2f) (atFlags StatusFlags.CF (adcR64R64Effect 0x108a2f 0 13)) (Reg.operands [.gpr 0, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[105, 100, 114]
    (.letOp (n := 119) (.out 0x108a32 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x108a32 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[106, 117]
    (.letOp (n := 120) (.exec 0x108a32 (fun s => s.RIP = 0x108a32) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x108a32 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[106, 117]
    (.letOp (n := 121) (.out 0x108a36 (movR64R64Effect 0x108a36 5 6) (EffectPart.reads (.reg (.gpr 5)) [.gpr 6] []) (.reg (.gpr 5))) #v[56]
    (.letOp (n := 122) (.exec 0x108a36 (fun s => s.RIP = 0x108a36) (movR64R64Effect 0x108a36 5 6) (Reg.operands [.gpr 6] [])) #v[56]
    (.letOp (n := 123) (.out 0x108a39 (subR64R64Effect 0x108a39 5 14) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 14] []) (.reg (.gpr 5))) #v[121, 80]
    (.letOp (n := 124) (.exec 0x108a39 (fun s => s.RIP = 0x108a39) (subR64R64Effect 0x108a39 5 14) (Reg.operands [.gpr 5, .gpr 14] [])) #v[121, 80]
    (.letOp (n := 125) (.out 0x108a3c (notR64Effect 0x108a3c 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[56]
    (.letOp (n := 126) (.exec 0x108a3c (fun s => s.RIP = 0x108a3c) (notR64Effect 0x108a3c 6) (Reg.operands [.gpr 6] [])) #v[56]
    (.letOp (n := 127) (.out 0x108a3f (movR64R64Effect 0x108a3f 15 14) (EffectPart.reads (.reg (.gpr 15)) [.gpr 14] []) (.reg (.gpr 15))) #v[80]
    (.letOp (n := 128) (.exec 0x108a3f (fun s => s.RIP = 0x108a3f) (movR64R64Effect 0x108a3f 15 14) (Reg.operands [.gpr 14] [])) #v[80]
    (.letOp (n := 129) (.out 0x108a42 (andR64R64Effect 0x108a42 15 6) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 6] []) (.reg (.gpr 15))) #v[127, 125]
    (.letOp (n := 130) (.exec 0x108a42 (fun s => s.RIP = 0x108a42) (andR64R64Effect 0x108a42 15 6) (Reg.operands [.gpr 15, .gpr 6] [])) #v[127, 125]
    (.letOp (n := 131) (.out 0x108a45 (orR64R64Effect 0x108a45 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 14] []) (.reg (.gpr 6))) #v[125, 80]
    (.letOp (n := 132) (.exec 0x108a45 (fun s => s.RIP = 0x108a45) (orR64R64Effect 0x108a45 6 14) (Reg.operands [.gpr 6, .gpr 14] [])) #v[125, 80]
    (.letOp (n := 133) (.out 0x108a48 (movR64M64Effect 0x108a48 14 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 134) (.exec 0x108a48 (LoadPre 0x108a48 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x108a48 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x108a48 14 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l1089b2_2)))))))))))))))))))))))))))))))))))))))))))

def bytes_l1089b2_1 : List UInt8 :=
  [0x48, 0x8B, 0x47, 0x10, 0x48, 0x89, 0x44, 0x24, 0x60, 0x49, 0xF7, 0xE1, 0x49, 0x89, 0xC2, 0x49,
    0x89, 0xD5, 0x48, 0x8B, 0x47, 0x18, 0x48, 0x89, 0x44, 0x24, 0x68, 0x49, 0xF7, 0xE1, 0x4D, 0x01,
    0xFB, 0x48, 0x8B, 0x7C, 0x24, 0x28, 0x4D, 0x11, 0xE2, 0x4C, 0x11, 0xE8, 0x48, 0x83, 0xD2, 0x00,
    0x48, 0x89, 0xF5, 0x4C, 0x29, 0xF5, 0x48, 0xF7, 0xD6, 0x4D, 0x89, 0xF7, 0x49, 0x21, 0xF7, 0x4C,
    0x09, 0xF6, 0x4C, 0x8B, 0x74, 0x24, 0x30] ++ bytes_l1089b2_2

theorem code_l1089b2_1 : ∀ x ∈ codeRange 0x108a06 bytes_l1089b2_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x8a06 71 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1089b2_2

@[cfg_block] def b_l1089b2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1089b2 (StorePre 0x1089b2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x1089b2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1089b2 3 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[3, 4]
    (.letOp (n := 54) (.out 0x1089b7 (movR64M64Effect 0x1089b7 7 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 55) (.exec 0x1089b7 (LoadPre 0x1089b7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x1089b7 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1089b7 7 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x1089bf (movR64M64Effect 0x1089bf 6 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 57) (.exec 0x1089bf (LoadPre 0x1089bf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1089bf + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1089bf 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.out 0x1089c4 (movR64M64Effect 0x1089c4 9 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 59) (.exec 0x1089c4 (LoadPre 0x1089c4 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x1089c4 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1089c4 9 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.out 0x1089cc (imulR64R64Effect 0x1089cc 4 9 6) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 6] []) (.reg (.gpr 9))) #v[58, 56]
    (.letOp (n := 61) (.exec 0x1089cc (fun s => s.RIP = 0x1089cc) (imulR64R64Effect 0x1089cc 4 9 6) (Reg.operands [.gpr 9, .gpr 6] [])) #v[58, 56]
    (.letOp (n := 62) (.out 0x1089d0 (shlR64ClEffect 0x1089d0 3 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[60, 1]
    (.letOp (n := 63) (.exec 0x1089d0 (fun s => s.RIP = 0x1089d0) (shlR64ClEffect 0x1089d0 3 9) (Reg.operands [.gpr 9, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[60, 1]
    (.letOp (n := 64) (.out 0x1089d3 (shrR64ClEffect 0x1089d3 3 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[62, 1]
    (.letOp (n := 65) (.exec 0x1089d3 (fun s => s.RIP = 0x1089d3) (shrR64ClEffect 0x1089d3 3 9) (Reg.operands [.gpr 9, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[62, 1]
    (.letOp (n := 66) (.out 0x1089d6 (movR64M64Effect 0x1089d6 8 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 67) (.exec 0x1089d6 (LoadPre 0x1089d6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1089d6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1089d6 8 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.out 0x1089db (movR64M64Effect 0x1089db 3 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 69) (.exec 0x1089db (LoadPre 0x1089db (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1089db + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1089db 3 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.out 0x1089e0 (movR64M64Effect 0x1089e0 0 (.base 7 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[54]
    (.letOp (n := 71) (.exec 0x1089e0 (LoadPre 0x1089e0 (fun s => AddrMode.addr (.base 7 .none) s (0x1089e0 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1089e0 0 (.base 7 .none)) (Reg.operands [.gpr 7] [])) #v[54]
    (.letOp (n := 72) (.out 0x1089e3 (movR64M64Effect 0x1089e3 10 (.base 7 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 7] []) (.reg (.gpr 10))) #v[54]
    (.letOp (n := 73) (.exec 0x1089e3 (LoadPre 0x1089e3 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x1089e3 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1089e3 10 (.base 7 (.d8 0x8))) (Reg.operands [.gpr 7] [])) #v[54]
    (.letOp (n := 74) (.exec 0x1089e7 (StorePre 0x1089e7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1089e7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1089e7 0 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[70, 4]
    (.letOp (n := 75) (.out 0x1089ec (mulR64Effect 0x1089ec 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[64, 70]
    (.letOp (n := 76) (.out 0x1089ec (mulR64Effect 0x1089ec 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[64, 70]
    (.letOp (n := 77) (.exec 0x1089ec (fun s => s.RIP = 0x1089ec) (mulR64Effect 0x1089ec 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[64, 70]
    (.letOp (n := 78) (.out 0x1089ef (movR64R64Effect 0x1089ef 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[76]
    (.letOp (n := 79) (.exec 0x1089ef (fun s => s.RIP = 0x1089ef) (movR64R64Effect 0x1089ef 15 2) (Reg.operands [.gpr 2] [])) #v[76]
    (.letOp (n := 80) (.out 0x1089f2 (movR64R64Effect 0x1089f2 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[75]
    (.letOp (n := 81) (.exec 0x1089f2 (fun s => s.RIP = 0x1089f2) (movR64R64Effect 0x1089f2 14 0) (Reg.operands [.gpr 0] [])) #v[75]
    (.letOp (n := 82) (.exec 0x1089f5 (StorePre 0x1089f5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1089f5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1089f5 10 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[72, 4]
    (.letOp (n := 83) (.out 0x1089fa (movR64R64Effect 0x1089fa 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[72]
    (.letOp (n := 84) (.exec 0x1089fa (fun s => s.RIP = 0x1089fa) (movR64R64Effect 0x1089fa 0 10) (Reg.operands [.gpr 10] [])) #v[72]
    (.letOp (n := 85) (.out 0x1089fd (mulR64Effect 0x1089fd 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[64, 83]
    (.letOp (n := 86) (.out 0x1089fd (mulR64Effect 0x1089fd 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[64, 83]
    (.letOp (n := 87) (.exec 0x1089fd (fun s => s.RIP = 0x1089fd) (mulR64Effect 0x1089fd 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[64, 83]
    (.letOp (n := 88) (.out 0x108a00 (movR64R64Effect 0x108a00 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[85]
    (.letOp (n := 89) (.exec 0x108a00 (fun s => s.RIP = 0x108a00) (movR64R64Effect 0x108a00 11 0) (Reg.operands [.gpr 0] [])) #v[85]
    (.letOp (n := 90) (.out 0x108a03 (movR64R64Effect 0x108a03 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 2] []) (.reg (.gpr 12))) #v[86]
    (.letOp (n := 91) (.exec 0x108a03 (fun s => s.RIP = 0x108a03) (movR64R64Effect 0x108a03 12 2) (Reg.operands [.gpr 2] [])) #v[86]
    (b_l1089b2_1)))))))))))))))))))))))))))))))))))))))

def bytes_l1089b2 : List UInt8 :=
  [0x48, 0x89, 0x5C, 0x24, 0x70, 0x48, 0x8B, 0xBC, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x74,
    0x24, 0x10, 0x4C, 0x8B, 0x8C, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x4C, 0x0F, 0xAF, 0xCE, 0x49, 0xD3,
    0xE1, 0x49, 0xD3, 0xE9, 0x4C, 0x8B, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x5C, 0x24, 0x20, 0x48, 0x8B,
    0x07, 0x4C, 0x8B, 0x57, 0x08, 0x48, 0x89, 0x44, 0x24, 0x50, 0x49, 0xF7, 0xE1, 0x49, 0x89, 0xD7,
    0x49, 0x89, 0xC6, 0x4C, 0x89, 0x54, 0x24, 0x58, 0x4C, 0x89, 0xD0, 0x49, 0xF7, 0xE1, 0x49, 0x89,
    0xC3, 0x49, 0x89, 0xD4] ++ bytes_l1089b2_1

theorem code_l1089b2 : ∀ x ∈ codeRange 0x1089b2 bytes_l1089b2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x89b2 84 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1089b2_1

@[cfg_block] def b_l108bb1 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x108bb1 (StorePre 0x108bb1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x108bb1 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108bb1 5 9 (.sib 4 none 0 (.d8 0xe))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[9, 4]
    (.letOp (n := 54) (.out 0x108bb6 (cmpMImm8Effect 0x108bb6 5 32 (.sib 4 none 0 (.d8 0x44)) 0x0) (EffectPart.reads (.flag .ZF) [.gpr 4] []) (.flag .ZF)) #v[4]
    (.letOp (n := 55) (.exec 0x108bb6 (LoadPre 0x108bb6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x108bb6 + BitVec.ofNat 64 5)) 4) (cmpMImm8Effect 0x108bb6 5 32 (.sib 4 none 0 (.d8 0x44)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.pure (condOp 4)) #v[54]
    (.terminate (.condBr (Fin.last 56) ⟨.l108e11, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩ ⟨.l108bc1, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l108bb1 : List UInt8 :=
  [0x44, 0x88, 0x4C, 0x24, 0x0E, 0x83, 0x7C, 0x24, 0x44, 0x00, 0x0F, 0x84, 0x50, 0x02, 0x00, 0x00]

theorem code_l108bb1 : ∀ x ∈ codeRange 0x108bb1 bytes_l108bb1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x8bb1 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l108bc1_8 : Block Op Label signature Reg.count 358 :=
  .letOp (n := 358) (.exec 0x108dde (StorePre 0x108dde 4 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x108dde + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x108dde 2 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 2, .gpr 6] [])) #v[341, 354]
    (.letOp (n := 359) (.exec 0x108de2 (StorePre 0x108de2 4 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x108de2 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x108de2 1 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 1, .gpr 6] [])) #v[352, 354]
    (.letOp (n := 360) (.exec 0x108de6 (StorePre 0x108de6 4 (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x108de6 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108de6 4 5 (.base 6 (.d8 0x20))) (Reg.operands [.gpr 5, .gpr 6] [])) #v[284, 354]
    (.letOp (n := 361) (.out 0x108dea (addR64Imm8Effect 0x108dea 4 0x78) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 362) (.exec 0x108dea (fun s => s.RIP = 0x108dea) (addR64Imm8Effect 0x108dea 4 0x78) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 363) (.out 0x108dee (popR64Effect 0x108dee 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[361]
    (.letOp (n := 364) (.out 0x108dee (popR64Effect 0x108dee 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[361]
    (.letOp (n := 365) (.exec 0x108dee (PopPre 0x108dee) (popR64Effect 0x108dee 1 3) (Reg.operands [.gpr 4] [])) #v[361]
    (.letOp (n := 366) (.out 0x108def (popR64Effect 0x108def 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[364]
    (.letOp (n := 367) (.out 0x108def (popR64Effect 0x108def 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[364]
    (.letOp (n := 368) (.exec 0x108def (PopPre 0x108def) (popR64Effect 0x108def 2 12) (Reg.operands [.gpr 4] [])) #v[364]
    (.letOp (n := 369) (.out 0x108df1 (popR64Effect 0x108df1 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[367]
    (.letOp (n := 370) (.out 0x108df1 (popR64Effect 0x108df1 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[367]
    (.letOp (n := 371) (.exec 0x108df1 (PopPre 0x108df1) (popR64Effect 0x108df1 2 13) (Reg.operands [.gpr 4] [])) #v[367]
    (.letOp (n := 372) (.out 0x108df3 (popR64Effect 0x108df3 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[370]
    (.letOp (n := 373) (.out 0x108df3 (popR64Effect 0x108df3 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[370]
    (.letOp (n := 374) (.exec 0x108df3 (PopPre 0x108df3) (popR64Effect 0x108df3 2 14) (Reg.operands [.gpr 4] [])) #v[370]
    (.letOp (n := 375) (.out 0x108df5 (popR64Effect 0x108df5 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[373]
    (.letOp (n := 376) (.out 0x108df5 (popR64Effect 0x108df5 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[373]
    (.letOp (n := 377) (.exec 0x108df5 (PopPre 0x108df5) (popR64Effect 0x108df5 2 15) (Reg.operands [.gpr 4] [])) #v[373]
    (.letOp (n := 378) (.out 0x108df7 (popR64Effect 0x108df7 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[376]
    (.letOp (n := 379) (.out 0x108df7 (popR64Effect 0x108df7 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[376]
    (.letOp (n := 380) (.exec 0x108df7 (PopPre 0x108df7) (popR64Effect 0x108df7 1 5) (Reg.operands [.gpr 4] [])) #v[376]
    (.letOp (n := 381) (.out 0x108df8 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[379]
    (.letOp (n := 382) (.out 0x108df8 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[379]
    (.letOp (n := 383) (.exec 0x108df8 (RetPre 0x108df8) (retEffect) (Reg.operands [.gpr 4] [])) #v[379]
    (.terminate (.ret (RegMap.args [(0, 330), (1, 352), (2, 341), (3, 363), (4, 382), (5, 378), (6, 354), (7, 255), (8, 319), (9, 191), (10, 309), (11, 346), (12, 366), (13, 369), (14, 372), (15, 375), (22, 22), (39, 39), (50, 50), (51, 51)] 384) (some ⟨381, by decide⟩))))))))))))))))))))))))))))

def bytes_l108bc1_8 : List UInt8 :=
  [0x48, 0x89, 0x56, 0x10, 0x48, 0x89, 0x4E, 0x18, 0x40, 0x88, 0x6E, 0x20, 0x48, 0x83, 0xC4, 0x78,
    0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l108bc1_8 : ∀ x ∈ codeRange 0x108dde bytes_l108bc1_8, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x8dde 27 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l108bc1_7 : Block Op Label signature Reg.count 322 :=
  .letOp (n := 322) (.out 0x108d97 (movzxR32M8Effect 0x108d97 5 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 323) (.exec 0x108d97 (LoadPre 0x108d97 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108d97 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x108d97 5 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 324) (.out 0x108d9c (xorR64R64Effect 0x108d9c 3 9) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 9] []) (.reg (.gpr 3))) #v[151, 191]
    (.letOp (n := 325) (.exec 0x108d9c (fun s => s.RIP = 0x108d9c) (xorR64R64Effect 0x108d9c 3 9) (Reg.operands [.gpr 3, .gpr 9] [])) #v[151, 191]
    (.letOp (n := 326) (.out 0x108d9f (negR64Effect 0x108d9f 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[322]
    (.letOp (n := 327) (.exec 0x108d9f (fun s => s.RIP = 0x108d9f) (negR64Effect 0x108d9f 0) (Reg.operands [.gpr 0] [])) #v[322]
    (.letOp (n := 328) (.out 0x108da2 (andR64R64Effect 0x108da2 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[326, 324]
    (.letOp (n := 329) (.exec 0x108da2 (fun s => s.RIP = 0x108da2) (andR64R64Effect 0x108da2 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[326, 324]
    (.letOp (n := 330) (.out 0x108da5 (xorR64R64Effect 0x108da5 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[328, 191]
    (.letOp (n := 331) (.exec 0x108da5 (fun s => s.RIP = 0x108da5) (xorR64R64Effect 0x108da5 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[328, 191]
    (.letOp (n := 332) (.exec 0x108da8 (StorePre 0x108da8 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108da8 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108da8 4 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[290, 4]
    (.letOp (n := 333) (.out 0x108dac (movzxR32M8Effect 0x108dac 5 2 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 334) (.exec 0x108dac (LoadPre 0x108dac (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108dac + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x108dac 5 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 335) (.out 0x108db1 (xorR64R64Effect 0x108db1 12 6) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 6] []) (.reg (.gpr 12))) #v[131, 222]
    (.letOp (n := 336) (.exec 0x108db1 (fun s => s.RIP = 0x108db1) (xorR64R64Effect 0x108db1 12 6) (Reg.operands [.gpr 12, .gpr 6] [])) #v[131, 222]
    (.letOp (n := 337) (.out 0x108db4 (negR64Effect 0x108db4 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[333]
    (.letOp (n := 338) (.exec 0x108db4 (fun s => s.RIP = 0x108db4) (negR64Effect 0x108db4 2) (Reg.operands [.gpr 2] [])) #v[333]
    (.letOp (n := 339) (.out 0x108db7 (andR64R64Effect 0x108db7 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 12] []) (.reg (.gpr 2))) #v[337, 335]
    (.letOp (n := 340) (.exec 0x108db7 (fun s => s.RIP = 0x108db7) (andR64R64Effect 0x108db7 2 12) (Reg.operands [.gpr 2, .gpr 12] [])) #v[337, 335]
    (.letOp (n := 341) (.out 0x108dba (xorR64R64Effect 0x108dba 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[339, 222]
    (.letOp (n := 342) (.exec 0x108dba (fun s => s.RIP = 0x108dba) (xorR64R64Effect 0x108dba 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[339, 222]
    (.letOp (n := 343) (.exec 0x108dbd (StorePre 0x108dbd 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108dbd + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108dbd 4 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[290, 4]
    (.letOp (n := 344) (.out 0x108dc1 (movzxR32M8Effect 0x108dc1 5 1 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 345) (.exec 0x108dc1 (LoadPre 0x108dc1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108dc1 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x108dc1 5 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 346) (.out 0x108dc6 (xorR64R64Effect 0x108dc6 11 7) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 7] []) (.reg (.gpr 11))) #v[245, 255]
    (.letOp (n := 347) (.exec 0x108dc6 (fun s => s.RIP = 0x108dc6) (xorR64R64Effect 0x108dc6 11 7) (Reg.operands [.gpr 11, .gpr 7] [])) #v[245, 255]
    (.letOp (n := 348) (.out 0x108dc9 (negR64Effect 0x108dc9 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[344]
    (.letOp (n := 349) (.exec 0x108dc9 (fun s => s.RIP = 0x108dc9) (negR64Effect 0x108dc9 1) (Reg.operands [.gpr 1] [])) #v[344]
    (.letOp (n := 350) (.out 0x108dcc (andR64R64Effect 0x108dcc 1 11) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 11] []) (.reg (.gpr 1))) #v[348, 346]
    (.letOp (n := 351) (.exec 0x108dcc (fun s => s.RIP = 0x108dcc) (andR64R64Effect 0x108dcc 1 11) (Reg.operands [.gpr 1, .gpr 11] [])) #v[348, 346]
    (.letOp (n := 352) (.out 0x108dcf (xorR64R64Effect 0x108dcf 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[350, 255]
    (.letOp (n := 353) (.exec 0x108dcf (fun s => s.RIP = 0x108dcf) (xorR64R64Effect 0x108dcf 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[350, 255]
    (.letOp (n := 354) (.out 0x108dd2 (movR64M64Effect 0x108dd2 6 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 355) (.exec 0x108dd2 (LoadPre 0x108dd2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x108dd2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x108dd2 6 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 356) (.exec 0x108dd7 (StorePre 0x108dd7 3 (fun s => AddrMode.addr (.base 6 .none) s (0x108dd7 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x108dd7 8 (.base 6 .none)) (Reg.operands [.gpr 8, .gpr 6] [])) #v[319, 354]
    (.letOp (n := 357) (.exec 0x108dda (StorePre 0x108dda 4 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x108dda + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x108dda 0 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 6] [])) #v[330, 354]
    (b_l108bc1_8))))))))))))))))))))))))))))))))))))

def bytes_l108bc1_7 : List UInt8 :=
  [0x0F, 0xB6, 0x44, 0x24, 0x10, 0x4C, 0x31, 0xCB, 0x48, 0xF7, 0xD8, 0x48, 0x21, 0xD8, 0x4C, 0x31,
    0xC8, 0x88, 0x4C, 0x24, 0x10, 0x0F, 0xB6, 0x54, 0x24, 0x10, 0x49, 0x31, 0xF4, 0x48, 0xF7, 0xDA,
    0x4C, 0x21, 0xE2, 0x48, 0x31, 0xF2, 0x88, 0x4C, 0x24, 0x10, 0x0F, 0xB6, 0x4C, 0x24, 0x10, 0x49,
    0x31, 0xFB, 0x48, 0xF7, 0xD9, 0x4C, 0x21, 0xD9, 0x48, 0x31, 0xF9, 0x48, 0x8B, 0x74, 0x24, 0x70,
    0x4C, 0x89, 0x06, 0x48, 0x89, 0x46, 0x08] ++ bytes_l108bc1_8

theorem code_l108bc1_7 : ∀ x ∈ codeRange 0x108d97 bytes_l108bc1_7, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x8d97 71 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l108bc1_8

@[cfg_block] def b_l108bc1_6 : Block Op Label signature Reg.count 288 :=
  .letOp (n := 288) (.out 0x108d48 (atFlags (condHolds 4) (setccR8Effect 0x108d48 3 1)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 1))) #v[276, 286]
    (.letOp (n := 289) (.exec 0x108d48 (fun s => s.RIP = 0x108d48) (atFlags (condHolds 4) (setccR8Effect 0x108d48 3 1)) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[276, 286]
    (.letOp (n := 290) (.out 0x108d4b (andR8R8Effect 0x108d4b 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8] []) (.reg (.gpr 1))) #v[288, 280]
    (.letOp (n := 291) (.exec 0x108d4b (fun s => s.RIP = 0x108d4b) (andR8R8Effect 0x108d4b 3 1 8) (Reg.operands [.gpr 1, .gpr 8] [])) #v[288, 280]
    (.letOp (n := 292) (.exec 0x108d4e (StorePre 0x108d4e 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108d4e + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108d4e 4 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[290, 4]
    (.letOp (n := 293) (.exec 0x108d52 (fun s => s.RIP = 0x108d52) (leaR64Effect 0x108d52 10 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 294) (.out 0x108d57 (movzxR32M8Effect 0x108d57 6 10 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 295) (.exec 0x108d57 (LoadPre 0x108d57 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108d57 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108d57 6 10 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 296) (.out 0x108d5d (decR64Effect 0x108d5d 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[294]
    (.letOp (n := 297) (.exec 0x108d5d (fun s => s.RIP = 0x108d5d) (decR64Effect 0x108d5d 10) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[294]
    (.letOp (n := 298) (.out 0x108d60 (andR64R64Effect 0x108d60 10 8) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 8] []) (.reg (.gpr 10))) #v[296, 280]
    (.letOp (n := 299) (.exec 0x108d60 (fun s => s.RIP = 0x108d60) (andR64R64Effect 0x108d60 10 8) (Reg.operands [.gpr 10, .gpr 8] [])) #v[296, 280]
    (.letOp (n := 300) (.out 0x108d63 (sarR64Effect 0x108d63 4 10 63) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[298]
    (.letOp (n := 301) (.exec 0x108d63 (fun s => s.RIP = 0x108d63) (sarR64Effect 0x108d63 4 10 63) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[298]
    (.letOp (n := 302) (.out 0x108d67 (addR64R64Effect 0x108d67 10 13) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 13] []) (.reg (.gpr 10))) #v[300, 278]
    (.letOp (n := 303) (.exec 0x108d67 (fun s => s.RIP = 0x108d67) (addR64R64Effect 0x108d67 10 13) (Reg.operands [.gpr 10, .gpr 13] [])) #v[300, 278]
    (.letOp (n := 304) (.out 0x108d6a (shrR64Effect 0x108d6a 4 10 63) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[302]
    (.letOp (n := 305) (.exec 0x108d6a (fun s => s.RIP = 0x108d6a) (shrR64Effect 0x108d6a 4 10 63) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[302]
    (.letOp (n := 306) (.exec 0x108d6e (StorePre 0x108d6e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108d6e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108d6e 10 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[304, 4]
    (.letOp (n := 307) (.exec 0x108d73 (fun s => s.RIP = 0x108d73) (leaR64Effect 0x108d73 8 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 308) (.exec 0x108d78 (StorePre 0x108d78 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108d78 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108d78 4 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[290, 4]
    (.letOp (n := 309) (.out 0x108d7c (leaR64Effect 0x108d7c 10 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 310) (.exec 0x108d7c (fun s => s.RIP = 0x108d7c) (leaR64Effect 0x108d7c 10 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 311) (.out 0x108d81 (movzxR32M8Effect 0x108d81 6 8 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 312) (.exec 0x108d81 (LoadPre 0x108d81 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108d81 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108d81 6 8 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 313) (.out 0x108d87 (xorR64R64Effect 0x108d87 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[153, 159]
    (.letOp (n := 314) (.exec 0x108d87 (fun s => s.RIP = 0x108d87) (xorR64R64Effect 0x108d87 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[153, 159]
    (.letOp (n := 315) (.out 0x108d8a (negR64Effect 0x108d8a 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[311]
    (.letOp (n := 316) (.exec 0x108d8a (fun s => s.RIP = 0x108d8a) (negR64Effect 0x108d8a 8) (Reg.operands [.gpr 8] [])) #v[311]
    (.letOp (n := 317) (.out 0x108d8d (andR64R64Effect 0x108d8d 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2] []) (.reg (.gpr 8))) #v[315, 313]
    (.letOp (n := 318) (.exec 0x108d8d (fun s => s.RIP = 0x108d8d) (andR64R64Effect 0x108d8d 8 2) (Reg.operands [.gpr 8, .gpr 2] [])) #v[315, 313]
    (.letOp (n := 319) (.out 0x108d90 (xorR64R64Effect 0x108d90 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[317, 159]
    (.letOp (n := 320) (.exec 0x108d90 (fun s => s.RIP = 0x108d90) (xorR64R64Effect 0x108d90 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[317, 159]
    (.letOp (n := 321) (.exec 0x108d93 (StorePre 0x108d93 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108d93 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108d93 4 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[290, 4]
    (b_l108bc1_7))))))))))))))))))))))))))))))))))

def bytes_l108bc1_6 : List UInt8 :=
  [0x0F, 0x94, 0xC1, 0x44, 0x20, 0xC1, 0x88, 0x4C, 0x24, 0x10, 0x4C, 0x8D, 0x54, 0x24, 0x10, 0x44,
    0x0F, 0xB6, 0x54, 0x24, 0x10, 0x49, 0xFF, 0xCA, 0x4D, 0x21, 0xC2, 0x49, 0xC1, 0xFA, 0x3F, 0x4D,
    0x01, 0xEA, 0x49, 0xC1, 0xEA, 0x3F, 0x4C, 0x89, 0x54, 0x24, 0x10, 0x4C, 0x8D, 0x44, 0x24, 0x10,
    0x88, 0x4C, 0x24, 0x10, 0x4C, 0x8D, 0x54, 0x24, 0x10, 0x44, 0x0F, 0xB6, 0x44, 0x24, 0x10, 0x48,
    0x31, 0xC2, 0x49, 0xF7, 0xD8, 0x49, 0x21, 0xD0, 0x49, 0x31, 0xC0, 0x88, 0x4C, 0x24, 0x10] ++ bytes_l108bc1_7

theorem code_l108bc1_6 : ∀ x ∈ codeRange 0x108d48 bytes_l108bc1_6, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x8d48 79 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l108bc1_7

@[cfg_block] def b_l108bc1_5 : Block Op Label signature Reg.count 249 :=
  .letOp (n := 249) (.out 0x108d01 (movR64M64Effect 0x108d01 14 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 250) (.exec 0x108d01 (LoadPre 0x108d01 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x108d01 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x108d01 14 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 251) (.out 0x108d06 (subR64R64Effect 0x108d06 8 14) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 14] []) (.reg (.gpr 8))) #v[247, 249]
    (.letOp (n := 252) (.exec 0x108d06 (fun s => s.RIP = 0x108d06) (subR64R64Effect 0x108d06 8 14) (Reg.operands [.gpr 8, .gpr 14] [])) #v[247, 249]
    (.letOp (n := 253) (.out 0x108d09 (sarR64Effect 0x108d09 4 7 63) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[243]
    (.letOp (n := 254) (.exec 0x108d09 (fun s => s.RIP = 0x108d09) (sarR64Effect 0x108d09 4 7 63) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[243]
    (.letOp (n := 255) (.out 0x108d0d (addR64R64Effect 0x108d0d 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 8] []) (.reg (.gpr 7))) #v[253, 251]
    (.letOp (n := 256) (.exec 0x108d0d (fun s => s.RIP = 0x108d0d) (addR64R64Effect 0x108d0d 7 8) (Reg.operands [.gpr 7, .gpr 8] [])) #v[253, 251]
    (.letOp (n := 257) (.out 0x108d10 (movR64R64Effect 0x108d10 8 11) (EffectPart.reads (.reg (.gpr 8)) [.gpr 11] []) (.reg (.gpr 8))) #v[245]
    (.letOp (n := 258) (.exec 0x108d10 (fun s => s.RIP = 0x108d10) (movR64R64Effect 0x108d10 8 11) (Reg.operands [.gpr 11] [])) #v[245]
    (.letOp (n := 259) (.out 0x108d13 (notR64Effect 0x108d13 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[257]
    (.letOp (n := 260) (.exec 0x108d13 (fun s => s.RIP = 0x108d13) (notR64Effect 0x108d13 8) (Reg.operands [.gpr 8] [])) #v[257]
    (.letOp (n := 261) (.out 0x108d16 (movR64R64Effect 0x108d16 10 14) (EffectPart.reads (.reg (.gpr 10)) [.gpr 14] []) (.reg (.gpr 10))) #v[249]
    (.letOp (n := 262) (.exec 0x108d16 (fun s => s.RIP = 0x108d16) (movR64R64Effect 0x108d16 10 14) (Reg.operands [.gpr 14] [])) #v[249]
    (.letOp (n := 263) (.out 0x108d19 (andR64R64Effect 0x108d19 10 8) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 8] []) (.reg (.gpr 10))) #v[261, 259]
    (.letOp (n := 264) (.exec 0x108d19 (fun s => s.RIP = 0x108d19) (andR64R64Effect 0x108d19 10 8) (Reg.operands [.gpr 10, .gpr 8] [])) #v[261, 259]
    (.letOp (n := 265) (.out 0x108d1c (orR64R64Effect 0x108d1c 8 14) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 14] []) (.reg (.gpr 8))) #v[259, 249]
    (.letOp (n := 266) (.exec 0x108d1c (fun s => s.RIP = 0x108d1c) (orR64R64Effect 0x108d1c 8 14) (Reg.operands [.gpr 8, .gpr 14] [])) #v[259, 249]
    (.letOp (n := 267) (.out 0x108d1f (andR64R64Effect 0x108d1f 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 7] []) (.reg (.gpr 8))) #v[265, 255]
    (.letOp (n := 268) (.exec 0x108d1f (fun s => s.RIP = 0x108d1f) (andR64R64Effect 0x108d1f 8 7) (Reg.operands [.gpr 8, .gpr 7] [])) #v[265, 255]
    (.letOp (n := 269) (.out 0x108d22 (orR64R64Effect 0x108d22 8 10) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 10] []) (.reg (.gpr 8))) #v[267, 263]
    (.letOp (n := 270) (.exec 0x108d22 (fun s => s.RIP = 0x108d22) (orR64R64Effect 0x108d22 8 10) (Reg.operands [.gpr 8, .gpr 10] [])) #v[267, 263]
    (.letOp (n := 271) (.out 0x108d25 (shrR64Effect 0x108d25 4 8 63) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[269]
    (.letOp (n := 272) (.exec 0x108d25 (fun s => s.RIP = 0x108d25) (shrR64Effect 0x108d25 4 8 63) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[269]
    (.letOp (n := 273) (.exec 0x108d29 (StorePre 0x108d29 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108d29 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108d29 8 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[271, 4]
    (.letOp (n := 274) (.out 0x108d2e (xorR32R32Effect 0x108d2e 3 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 8] []) (.reg (.gpr 8))) #v[271, 271]
    (.letOp (n := 275) (.exec 0x108d2e (fun s => s.RIP = 0x108d2e) (xorR32R32Effect 0x108d2e 3 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[271, 271]
    (.letOp (n := 276) (.out 0x108d31 (movR32R32Effect 0x108d31 2 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[111]
    (.letOp (n := 277) (.exec 0x108d31 (fun s => s.RIP = 0x108d31) (movR32R32Effect 0x108d31 2 1 5) (Reg.operands [.gpr 5] [])) #v[111]
    (.letOp (n := 278) (.out 0x108d33 (shrR64ClEffect 0x108d33 3 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[93, 276]
    (.letOp (n := 279) (.exec 0x108d33 (fun s => s.RIP = 0x108d33) (shrR64ClEffect 0x108d33 3 13) (Reg.operands [.gpr 13, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[93, 276]
    (.letOp (n := 280) (.out 0x108d36 (subR64M64Effect 0x108d36 8 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 4] []) (.reg (.gpr 8))) #v[274, 4]
    (.letOp (n := 281) (.exec 0x108d36 (LoadPre 0x108d36 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108d36 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x108d36 8 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[274, 4]
    (.letOp (n := 282) (.out 0x108d3b (movzxR32M8Effect 0x108d3b 5 5 (.sib 4 none 0 (.d8 0xf))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 283) (.exec 0x108d3b (LoadPre 0x108d3b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x108d3b + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x108d3b 5 5 (.sib 4 none 0 (.d8 0xf))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 284) (.out 0x108d40 (xorR8M8Effect 0x108d40 5 5 (.sib 4 none 0 (.d8 0xe))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 4] []) (.reg (.gpr 5))) #v[282, 4]
    (.letOp (n := 285) (.exec 0x108d40 (LoadPre 0x108d40 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x108d40 + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x108d40 5 5 (.sib 4 none 0 (.d8 0xe))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[282, 4]
    (.letOp (n := 286) (.out 0x108d45 (testR64R64Effect 0x108d45 13 13) (EffectPart.reads (.flag .ZF) [.gpr 13, .gpr 13] []) (.flag .ZF)) #v[278, 278]
    (.letOp (n := 287) (.exec 0x108d45 (fun s => s.RIP = 0x108d45) (testR64R64Effect 0x108d45 13 13) (Reg.operands [.gpr 13, .gpr 13] [])) #v[278, 278]
    (b_l108bc1_6)))))))))))))))))))))))))))))))))))))))

def bytes_l108bc1_5 : List UInt8 :=
  [0x4C, 0x8B, 0x74, 0x24, 0x68, 0x4D, 0x29, 0xF0, 0x48, 0xC1, 0xFF, 0x3F, 0x4C, 0x01, 0xC7, 0x4D,
    0x89, 0xD8, 0x49, 0xF7, 0xD0, 0x4D, 0x89, 0xF2, 0x4D, 0x21, 0xC2, 0x4D, 0x09, 0xF0, 0x49, 0x21,
    0xF8, 0x4D, 0x09, 0xD0, 0x49, 0xC1, 0xE8, 0x3F, 0x4C, 0x89, 0x44, 0x24, 0x10, 0x45, 0x31, 0xC0,
    0x89, 0xE9, 0x49, 0xD3, 0xED, 0x4C, 0x2B, 0x44, 0x24, 0x10, 0x0F, 0xB6, 0x6C, 0x24, 0x0F, 0x40,
    0x32, 0x6C, 0x24, 0x0E, 0x4D, 0x85, 0xED] ++ bytes_l108bc1_6

theorem code_l108bc1_5 : ∀ x ∈ codeRange 0x108d01 bytes_l108bc1_5, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x8d01 71 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l108bc1_6

@[cfg_block] def b_l108bc1_4 : Block Op Label signature Reg.count 210 :=
  .letOp (n := 210) (.out 0x108cbd (xorR32R32Effect 0x108cbd 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[207, 207]
    (.letOp (n := 211) (.exec 0x108cbd (fun s => s.RIP = 0x108cbd) (xorR32R32Effect 0x108cbd 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[207, 207]
    (.letOp (n := 212) (.out 0x108cbf (subR64M64Effect 0x108cbf 6 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 4] []) (.reg (.gpr 6))) #v[210, 4]
    (.letOp (n := 213) (.exec 0x108cbf (LoadPre 0x108cbf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108cbf + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x108cbf 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[210, 4]
    (.letOp (n := 214) (.out 0x108cc4 (movR64R64Effect 0x108cc4 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[131]
    (.letOp (n := 215) (.exec 0x108cc4 (fun s => s.RIP = 0x108cc4) (movR64R64Effect 0x108cc4 7 12) (Reg.operands [.gpr 12] [])) #v[131]
    (.letOp (n := 216) (.out 0x108cc7 (movR64M64Effect 0x108cc7 14 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 217) (.exec 0x108cc7 (LoadPre 0x108cc7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x108cc7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x108cc7 14 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 218) (.out 0x108ccc (subR64R64Effect 0x108ccc 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 14] []) (.reg (.gpr 7))) #v[214, 216]
    (.letOp (n := 219) (.exec 0x108ccc (fun s => s.RIP = 0x108ccc) (subR64R64Effect 0x108ccc 7 14) (Reg.operands [.gpr 7, .gpr 14] [])) #v[214, 216]
    (.letOp (n := 220) (.out 0x108ccf (sarR64Effect 0x108ccf 4 6 63) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[212]
    (.letOp (n := 221) (.exec 0x108ccf (fun s => s.RIP = 0x108ccf) (sarR64Effect 0x108ccf 4 6 63) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[212]
    (.letOp (n := 222) (.out 0x108cd3 (addR64R64Effect 0x108cd3 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7] []) (.reg (.gpr 6))) #v[220, 218]
    (.letOp (n := 223) (.exec 0x108cd3 (fun s => s.RIP = 0x108cd3) (addR64R64Effect 0x108cd3 6 7) (Reg.operands [.gpr 6, .gpr 7] [])) #v[220, 218]
    (.letOp (n := 224) (.out 0x108cd6 (movR64R64Effect 0x108cd6 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[131]
    (.letOp (n := 225) (.exec 0x108cd6 (fun s => s.RIP = 0x108cd6) (movR64R64Effect 0x108cd6 7 12) (Reg.operands [.gpr 12] [])) #v[131]
    (.letOp (n := 226) (.out 0x108cd9 (notR64Effect 0x108cd9 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[224]
    (.letOp (n := 227) (.exec 0x108cd9 (fun s => s.RIP = 0x108cd9) (notR64Effect 0x108cd9 7) (Reg.operands [.gpr 7] [])) #v[224]
    (.letOp (n := 228) (.out 0x108cdc (movR64R64Effect 0x108cdc 8 14) (EffectPart.reads (.reg (.gpr 8)) [.gpr 14] []) (.reg (.gpr 8))) #v[216]
    (.letOp (n := 229) (.exec 0x108cdc (fun s => s.RIP = 0x108cdc) (movR64R64Effect 0x108cdc 8 14) (Reg.operands [.gpr 14] [])) #v[216]
    (.letOp (n := 230) (.out 0x108cdf (andR64R64Effect 0x108cdf 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 7] []) (.reg (.gpr 8))) #v[228, 226]
    (.letOp (n := 231) (.exec 0x108cdf (fun s => s.RIP = 0x108cdf) (andR64R64Effect 0x108cdf 8 7) (Reg.operands [.gpr 8, .gpr 7] [])) #v[228, 226]
    (.letOp (n := 232) (.out 0x108ce2 (orR64R64Effect 0x108ce2 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 14] []) (.reg (.gpr 7))) #v[226, 216]
    (.letOp (n := 233) (.exec 0x108ce2 (fun s => s.RIP = 0x108ce2) (orR64R64Effect 0x108ce2 7 14) (Reg.operands [.gpr 7, .gpr 14] [])) #v[226, 216]
    (.letOp (n := 234) (.out 0x108ce5 (andR64R64Effect 0x108ce5 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[232, 222]
    (.letOp (n := 235) (.exec 0x108ce5 (fun s => s.RIP = 0x108ce5) (andR64R64Effect 0x108ce5 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[232, 222]
    (.letOp (n := 236) (.out 0x108ce8 (orR64R64Effect 0x108ce8 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 8] []) (.reg (.gpr 7))) #v[234, 230]
    (.letOp (n := 237) (.exec 0x108ce8 (fun s => s.RIP = 0x108ce8) (orR64R64Effect 0x108ce8 7 8) (Reg.operands [.gpr 7, .gpr 8] [])) #v[234, 230]
    (.letOp (n := 238) (.out 0x108ceb (shrR64Effect 0x108ceb 4 7 63) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[236]
    (.letOp (n := 239) (.exec 0x108ceb (fun s => s.RIP = 0x108ceb) (shrR64Effect 0x108ceb 4 7 63) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[236]
    (.letOp (n := 240) (.exec 0x108cef (StorePre 0x108cef 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108cef + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108cef 7 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[238, 4]
    (.letOp (n := 241) (.out 0x108cf4 (xorR32R32Effect 0x108cf4 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[238, 238]
    (.letOp (n := 242) (.exec 0x108cf4 (fun s => s.RIP = 0x108cf4) (xorR32R32Effect 0x108cf4 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[238, 238]
    (.letOp (n := 243) (.out 0x108cf6 (subR64M64Effect 0x108cf6 7 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 4] []) (.reg (.gpr 7))) #v[241, 4]
    (.letOp (n := 244) (.exec 0x108cf6 (LoadPre 0x108cf6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108cf6 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x108cf6 7 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[241, 4]
    (.letOp (n := 245) (.out 0x108cfb (orR64R64Effect 0x108cfb 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 10] []) (.reg (.gpr 11))) #v[115, 101]
    (.letOp (n := 246) (.exec 0x108cfb (fun s => s.RIP = 0x108cfb) (orR64R64Effect 0x108cfb 11 10) (Reg.operands [.gpr 11, .gpr 10] [])) #v[115, 101]
    (.letOp (n := 247) (.out 0x108cfe (movR64R64Effect 0x108cfe 8 11) (EffectPart.reads (.reg (.gpr 8)) [.gpr 11] []) (.reg (.gpr 8))) #v[245]
    (.letOp (n := 248) (.exec 0x108cfe (fun s => s.RIP = 0x108cfe) (movR64R64Effect 0x108cfe 8 11) (Reg.operands [.gpr 11] [])) #v[245]
    (b_l108bc1_5)))))))))))))))))))))))))))))))))))))))

def bytes_l108bc1_4 : List UInt8 :=
  [0x31, 0xF6, 0x48, 0x2B, 0x74, 0x24, 0x10, 0x4C, 0x89, 0xE7, 0x4C, 0x8B, 0x74, 0x24, 0x60, 0x4C,
    0x29, 0xF7, 0x48, 0xC1, 0xFE, 0x3F, 0x48, 0x01, 0xFE, 0x4C, 0x89, 0xE7, 0x48, 0xF7, 0xD7, 0x4D,
    0x89, 0xF0, 0x49, 0x21, 0xF8, 0x4C, 0x09, 0xF7, 0x48, 0x21, 0xF7, 0x4C, 0x09, 0xC7, 0x48, 0xC1,
    0xEF, 0x3F, 0x48, 0x89, 0x7C, 0x24, 0x10, 0x31, 0xFF, 0x48, 0x2B, 0x7C, 0x24, 0x10, 0x4D, 0x09,
    0xD3, 0x4D, 0x89, 0xD8] ++ bytes_l108bc1_5

theorem code_l108bc1_4 : ∀ x ∈ codeRange 0x108cbd bytes_l108bc1_4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x8cbd 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l108bc1_5

@[cfg_block] def b_l108bc1_3 : Block Op Label signature Reg.count 173 :=
  .letOp (n := 173) (.out 0x108c74 (orR64R64Effect 0x108c74 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[171, 167]
    (.letOp (n := 174) (.exec 0x108c74 (fun s => s.RIP = 0x108c74) (orR64R64Effect 0x108c74 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[171, 167]
    (.letOp (n := 175) (.out 0x108c77 (shrR64Effect 0x108c77 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[173]
    (.letOp (n := 176) (.exec 0x108c77 (fun s => s.RIP = 0x108c77) (shrR64Effect 0x108c77 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[173]
    (.letOp (n := 177) (.exec 0x108c7b (StorePre 0x108c7b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108c7b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108c7b 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[175, 4]
    (.letOp (n := 178) (.exec 0x108c80 (fun s => s.RIP = 0x108c80) (leaR64Effect 0x108c80 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 179) (.out 0x108c85 (xorR32R32Effect 0x108c85 3 9 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 9] []) (.reg (.gpr 9))) #v[9, 9]
    (.letOp (n := 180) (.exec 0x108c85 (fun s => s.RIP = 0x108c85) (xorR32R32Effect 0x108c85 3 9 9) (Reg.operands [.gpr 9, .gpr 9] [])) #v[9, 9]
    (.letOp (n := 181) (.out 0x108c88 (subR64M64Effect 0x108c88 9 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 4] []) (.reg (.gpr 9))) #v[179, 4]
    (.letOp (n := 182) (.exec 0x108c88 (LoadPre 0x108c88 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108c88 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x108c88 9 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[179, 4]
    (.letOp (n := 183) (.out 0x108c8d (movR64R64Effect 0x108c8d 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[151]
    (.letOp (n := 184) (.exec 0x108c8d (fun s => s.RIP = 0x108c8d) (movR64R64Effect 0x108c8d 6 3) (Reg.operands [.gpr 3] [])) #v[151]
    (.letOp (n := 185) (.out 0x108c90 (movR64M64Effect 0x108c90 8 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 186) (.exec 0x108c90 (LoadPre 0x108c90 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x108c90 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x108c90 8 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 187) (.out 0x108c95 (subR64R64Effect 0x108c95 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 8] []) (.reg (.gpr 6))) #v[183, 185]
    (.letOp (n := 188) (.exec 0x108c95 (fun s => s.RIP = 0x108c95) (subR64R64Effect 0x108c95 6 8) (Reg.operands [.gpr 6, .gpr 8] [])) #v[183, 185]
    (.letOp (n := 189) (.out 0x108c98 (sarR64Effect 0x108c98 4 9 63) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[181]
    (.letOp (n := 190) (.exec 0x108c98 (fun s => s.RIP = 0x108c98) (sarR64Effect 0x108c98 4 9 63) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[181]
    (.letOp (n := 191) (.out 0x108c9c (addR64R64Effect 0x108c9c 9 6) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 6] []) (.reg (.gpr 9))) #v[189, 187]
    (.letOp (n := 192) (.exec 0x108c9c (fun s => s.RIP = 0x108c9c) (addR64R64Effect 0x108c9c 9 6) (Reg.operands [.gpr 9, .gpr 6] [])) #v[189, 187]
    (.letOp (n := 193) (.out 0x108c9f (movR64R64Effect 0x108c9f 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[151]
    (.letOp (n := 194) (.exec 0x108c9f (fun s => s.RIP = 0x108c9f) (movR64R64Effect 0x108c9f 6 3) (Reg.operands [.gpr 3] [])) #v[151]
    (.letOp (n := 195) (.out 0x108ca2 (notR64Effect 0x108ca2 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[193]
    (.letOp (n := 196) (.exec 0x108ca2 (fun s => s.RIP = 0x108ca2) (notR64Effect 0x108ca2 6) (Reg.operands [.gpr 6] [])) #v[193]
    (.letOp (n := 197) (.out 0x108ca5 (movR64R64Effect 0x108ca5 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 8] []) (.reg (.gpr 7))) #v[185]
    (.letOp (n := 198) (.exec 0x108ca5 (fun s => s.RIP = 0x108ca5) (movR64R64Effect 0x108ca5 7 8) (Reg.operands [.gpr 8] [])) #v[185]
    (.letOp (n := 199) (.out 0x108ca8 (andR64R64Effect 0x108ca8 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[197, 195]
    (.letOp (n := 200) (.exec 0x108ca8 (fun s => s.RIP = 0x108ca8) (andR64R64Effect 0x108ca8 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[197, 195]
    (.letOp (n := 201) (.out 0x108cab (orR64R64Effect 0x108cab 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 8] []) (.reg (.gpr 6))) #v[195, 185]
    (.letOp (n := 202) (.exec 0x108cab (fun s => s.RIP = 0x108cab) (orR64R64Effect 0x108cab 6 8) (Reg.operands [.gpr 6, .gpr 8] [])) #v[195, 185]
    (.letOp (n := 203) (.out 0x108cae (andR64R64Effect 0x108cae 6 9) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 9] []) (.reg (.gpr 6))) #v[201, 191]
    (.letOp (n := 204) (.exec 0x108cae (fun s => s.RIP = 0x108cae) (andR64R64Effect 0x108cae 6 9) (Reg.operands [.gpr 6, .gpr 9] [])) #v[201, 191]
    (.letOp (n := 205) (.out 0x108cb1 (orR64R64Effect 0x108cb1 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7] []) (.reg (.gpr 6))) #v[203, 199]
    (.letOp (n := 206) (.exec 0x108cb1 (fun s => s.RIP = 0x108cb1) (orR64R64Effect 0x108cb1 6 7) (Reg.operands [.gpr 6, .gpr 7] [])) #v[203, 199]
    (.letOp (n := 207) (.out 0x108cb4 (shrR64Effect 0x108cb4 4 6 63) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[205]
    (.letOp (n := 208) (.exec 0x108cb4 (fun s => s.RIP = 0x108cb4) (shrR64Effect 0x108cb4 4 6 63) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[205]
    (.letOp (n := 209) (.exec 0x108cb8 (StorePre 0x108cb8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108cb8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108cb8 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[207, 4]
    (b_l108bc1_4)))))))))))))))))))))))))))))))))))))

def bytes_l108bc1_3 : List UInt8 :=
  [0x48, 0x09, 0xF1, 0x48, 0xC1, 0xE9, 0x3F, 0x48, 0x89, 0x4C, 0x24, 0x10, 0x48, 0x8D, 0x4C, 0x24,
    0x10, 0x45, 0x31, 0xC9, 0x4C, 0x2B, 0x4C, 0x24, 0x10, 0x48, 0x89, 0xDE, 0x4C, 0x8B, 0x44, 0x24,
    0x58, 0x4C, 0x29, 0xC6, 0x49, 0xC1, 0xF9, 0x3F, 0x49, 0x01, 0xF1, 0x48, 0x89, 0xDE, 0x48, 0xF7,
    0xD6, 0x4C, 0x89, 0xC7, 0x48, 0x21, 0xF7, 0x4C, 0x09, 0xC6, 0x4C, 0x21, 0xCE, 0x48, 0x09, 0xFE,
    0x48, 0xC1, 0xEE, 0x3F, 0x48, 0x89, 0x74, 0x24, 0x10] ++ bytes_l108bc1_4

theorem code_l108bc1_3 : ∀ x ∈ codeRange 0x108c74 bytes_l108bc1_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x8c74 73 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l108bc1_4

@[cfg_block] def b_l108bc1_2 : Block Op Label signature Reg.count 133 :=
  .letOp (n := 133) (.out 0x108c3a (movR32R32Effect 0x108c3a 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[95]
    (.letOp (n := 134) (.exec 0x108c3a (fun s => s.RIP = 0x108c3a) (movR32R32Effect 0x108c3a 2 1 0) (Reg.operands [.gpr 0] [])) #v[95]
    (.letOp (n := 135) (.out 0x108c3c (shlR64ClEffect 0x108c3c 3 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[67, 133]
    (.letOp (n := 136) (.exec 0x108c3c (fun s => s.RIP = 0x108c3c) (shlR64ClEffect 0x108c3c 3 14) (Reg.operands [.gpr 14, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[67, 133]
    (.letOp (n := 137) (.out 0x108c3f (movR64R64Effect 0x108c3f 3 15) (EffectPart.reads (.reg (.gpr 3)) [.gpr 15] []) (.reg (.gpr 3))) #v[75]
    (.letOp (n := 138) (.exec 0x108c3f (fun s => s.RIP = 0x108c3f) (movR64R64Effect 0x108c3f 3 15) (Reg.operands [.gpr 15] [])) #v[75]
    (.letOp (n := 139) (.out 0x108c42 (movR32R32Effect 0x108c42 2 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[111]
    (.letOp (n := 140) (.exec 0x108c42 (fun s => s.RIP = 0x108c42) (movR32R32Effect 0x108c42 2 1 5) (Reg.operands [.gpr 5] [])) #v[111]
    (.letOp (n := 141) (.out 0x108c44 (shrR64ClEffect 0x108c44 3 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[137, 139]
    (.letOp (n := 142) (.exec 0x108c44 (fun s => s.RIP = 0x108c44) (shrR64ClEffect 0x108c44 3 3) (Reg.operands [.gpr 3, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[137, 139]
    (.letOp (n := 143) (.out 0x108c47 (movR32R32Effect 0x108c47 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[95]
    (.letOp (n := 144) (.exec 0x108c47 (fun s => s.RIP = 0x108c47) (movR32R32Effect 0x108c47 2 1 0) (Reg.operands [.gpr 0] [])) #v[95]
    (.letOp (n := 145) (.out 0x108c49 (shlR64ClEffect 0x108c49 3 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[75, 143]
    (.letOp (n := 146) (.exec 0x108c49 (fun s => s.RIP = 0x108c49) (shlR64ClEffect 0x108c49 3 15) (Reg.operands [.gpr 15, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[75, 143]
    (.letOp (n := 147) (.out 0x108c4c (movR32R32Effect 0x108c4c 2 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[111]
    (.letOp (n := 148) (.exec 0x108c4c (fun s => s.RIP = 0x108c4c) (movR32R32Effect 0x108c4c 2 1 5) (Reg.operands [.gpr 5] [])) #v[111]
    (.letOp (n := 149) (.out 0x108c4e (shrR64ClEffect 0x108c4e 3 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[129, 147]
    (.letOp (n := 150) (.exec 0x108c4e (fun s => s.RIP = 0x108c4e) (shrR64ClEffect 0x108c4e 3 2) (Reg.operands [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[129, 147]
    (.letOp (n := 151) (.out 0x108c51 (orR64R64Effect 0x108c51 3 14) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 14] []) (.reg (.gpr 3))) #v[141, 135]
    (.letOp (n := 152) (.exec 0x108c51 (fun s => s.RIP = 0x108c51) (orR64R64Effect 0x108c51 3 14) (Reg.operands [.gpr 3, .gpr 14] [])) #v[141, 135]
    (.letOp (n := 153) (.out 0x108c54 (orR64R64Effect 0x108c54 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 15] []) (.reg (.gpr 2))) #v[149, 145]
    (.letOp (n := 154) (.exec 0x108c54 (fun s => s.RIP = 0x108c54) (orR64R64Effect 0x108c54 2 15) (Reg.operands [.gpr 2, .gpr 15] [])) #v[149, 145]
    (.letOp (n := 155) (.out 0x108c57 (movR64R64Effect 0x108c57 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[153]
    (.letOp (n := 156) (.exec 0x108c57 (fun s => s.RIP = 0x108c57) (movR64R64Effect 0x108c57 0 2) (Reg.operands [.gpr 2] [])) #v[153]
    (.letOp (n := 157) (.out 0x108c5a (movR64M64Effect 0x108c5a 7 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 158) (.exec 0x108c5a (LoadPre 0x108c5a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x108c5a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x108c5a 7 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 159) (.out 0x108c5f (subR64R64Effect 0x108c5f 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[155, 157]
    (.letOp (n := 160) (.exec 0x108c5f (fun s => s.RIP = 0x108c5f) (subR64R64Effect 0x108c5f 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[155, 157]
    (.letOp (n := 161) (.out 0x108c62 (movR64R64Effect 0x108c62 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[153]
    (.letOp (n := 162) (.exec 0x108c62 (fun s => s.RIP = 0x108c62) (movR64R64Effect 0x108c62 1 2) (Reg.operands [.gpr 2] [])) #v[153]
    (.letOp (n := 163) (.out 0x108c65 (notR64Effect 0x108c65 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[161]
    (.letOp (n := 164) (.exec 0x108c65 (fun s => s.RIP = 0x108c65) (notR64Effect 0x108c65 1) (Reg.operands [.gpr 1] [])) #v[161]
    (.letOp (n := 165) (.out 0x108c68 (movR64R64Effect 0x108c68 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 7] []) (.reg (.gpr 6))) #v[157]
    (.letOp (n := 166) (.exec 0x108c68 (fun s => s.RIP = 0x108c68) (movR64R64Effect 0x108c68 6 7) (Reg.operands [.gpr 7] [])) #v[157]
    (.letOp (n := 167) (.out 0x108c6b (andR64R64Effect 0x108c6b 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[165, 163]
    (.letOp (n := 168) (.exec 0x108c6b (fun s => s.RIP = 0x108c6b) (andR64R64Effect 0x108c6b 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[165, 163]
    (.letOp (n := 169) (.out 0x108c6e (orR64R64Effect 0x108c6e 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[163, 157]
    (.letOp (n := 170) (.exec 0x108c6e (fun s => s.RIP = 0x108c6e) (orR64R64Effect 0x108c6e 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[163, 157]
    (.letOp (n := 171) (.out 0x108c71 (andR64R64Effect 0x108c71 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[169, 159]
    (.letOp (n := 172) (.exec 0x108c71 (fun s => s.RIP = 0x108c71) (andR64R64Effect 0x108c71 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[169, 159]
    (b_l108bc1_3))))))))))))))))))))))))))))))))))))))))

def bytes_l108bc1_2 : List UInt8 :=
  [0x89, 0xC1, 0x49, 0xD3, 0xE6, 0x4C, 0x89, 0xFB, 0x89, 0xE9, 0x48, 0xD3, 0xEB, 0x89, 0xC1, 0x49,
    0xD3, 0xE7, 0x89, 0xE9, 0x48, 0xD3, 0xEA, 0x4C, 0x09, 0xF3, 0x4C, 0x09, 0xFA, 0x48, 0x89, 0xD0,
    0x48, 0x8B, 0x7C, 0x24, 0x50, 0x48, 0x29, 0xF8, 0x48, 0x89, 0xD1, 0x48, 0xF7, 0xD1, 0x48, 0x89,
    0xFE, 0x48, 0x21, 0xCE, 0x48, 0x09, 0xF9, 0x48, 0x21, 0xC1] ++ bytes_l108bc1_3

theorem code_l108bc1_2 : ∀ x ∈ codeRange 0x108c3a bytes_l108bc1_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x8c3a 58 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l108bc1_3

@[cfg_block] def b_l108bc1_1 : Block Op Label signature Reg.count 93 :=
  .letOp (n := 93) (.out 0x108c00 (xorR64R64Effect 0x108c00 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 0] []) (.reg (.gpr 13))) #v[91, 0]
    (.letOp (n := 94) (.exec 0x108c00 (fun s => s.RIP = 0x108c00) (xorR64R64Effect 0x108c00 13 0) (Reg.operands [.gpr 13, .gpr 0] [])) #v[91, 0]
    (.letOp (n := 95) (.out 0x108c03 (movR32R32Effect 0x108c03 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[1]
    (.letOp (n := 96) (.exec 0x108c03 (fun s => s.RIP = 0x108c03) (movR32R32Effect 0x108c03 2 0 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 97) (.out 0x108c05 (movR64R64Effect 0x108c05 10 13) (EffectPart.reads (.reg (.gpr 10)) [.gpr 13] []) (.reg (.gpr 10))) #v[93]
    (.letOp (n := 98) (.exec 0x108c05 (fun s => s.RIP = 0x108c05) (movR64R64Effect 0x108c05 10 13) (Reg.operands [.gpr 13] [])) #v[93]
    (.letOp (n := 99) (.out 0x108c08 (movR32R32Effect 0x108c08 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[95]
    (.letOp (n := 100) (.exec 0x108c08 (fun s => s.RIP = 0x108c08) (movR32R32Effect 0x108c08 2 1 0) (Reg.operands [.gpr 0] [])) #v[95]
    (.letOp (n := 101) (.out 0x108c0a (shlR64ClEffect 0x108c0a 3 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[97, 99]
    (.letOp (n := 102) (.exec 0x108c0a (fun s => s.RIP = 0x108c0a) (shlR64ClEffect 0x108c0a 3 10) (Reg.operands [.gpr 10, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[97, 99]
    (.letOp (n := 103) (.out 0x108c0d (movR64M64Effect 0x108c0d 6 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 104) (.exec 0x108c0d (LoadPre 0x108c0d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x108c0d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x108c0d 6 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 105) (.out 0x108c12 (xorR64R64Effect 0x108c12 3 6) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 6] []) (.reg (.gpr 3))) #v[3, 103]
    (.letOp (n := 106) (.exec 0x108c12 (fun s => s.RIP = 0x108c12) (xorR64R64Effect 0x108c12 3 6) (Reg.operands [.gpr 3, .gpr 6] [])) #v[3, 103]
    (.letOp (n := 107) (.out 0x108c15 (negR64Effect 0x108c15 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[2]
    (.letOp (n := 108) (.exec 0x108c15 (fun s => s.RIP = 0x108c15) (negR64Effect 0x108c15 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 109) (.out 0x108c18 (movR64R64Effect 0x108c18 11 7) (EffectPart.reads (.reg (.gpr 11)) [.gpr 7] []) (.reg (.gpr 11))) #v[59]
    (.letOp (n := 110) (.exec 0x108c18 (fun s => s.RIP = 0x108c18) (movR64R64Effect 0x108c18 11 7) (Reg.operands [.gpr 7] [])) #v[59]
    (.letOp (n := 111) (.out 0x108c1b (movR32M32LowEffect 0x108c1b 5 (.sib 4 none 0 (.d8 0x44))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 112) (.exec 0x108c1b (LoadPre 0x108c1b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x108c1b + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x108c1b 5 (.sib 4 none 0 (.d8 0x44))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 113) (.out 0x108c1f (movR32R32Effect 0x108c1f 2 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[111]
    (.letOp (n := 114) (.exec 0x108c1f (fun s => s.RIP = 0x108c1f) (movR32R32Effect 0x108c1f 2 1 5) (Reg.operands [.gpr 5] [])) #v[111]
    (.letOp (n := 115) (.out 0x108c21 (shrR64ClEffect 0x108c21 3 11) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[109, 113]
    (.letOp (n := 116) (.exec 0x108c21 (fun s => s.RIP = 0x108c21) (shrR64ClEffect 0x108c21 3 11) (Reg.operands [.gpr 11, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[109, 113]
    (.letOp (n := 117) (.out 0x108c24 (movR32R32Effect 0x108c24 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[95]
    (.letOp (n := 118) (.exec 0x108c24 (fun s => s.RIP = 0x108c24) (movR32R32Effect 0x108c24 2 1 0) (Reg.operands [.gpr 0] [])) #v[95]
    (.letOp (n := 119) (.out 0x108c26 (shlR64ClEffect 0x108c26 3 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[59, 117]
    (.letOp (n := 120) (.exec 0x108c26 (fun s => s.RIP = 0x108c26) (shlR64ClEffect 0x108c26 3 7) (Reg.operands [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[59, 117]
    (.letOp (n := 121) (.out 0x108c29 (movR64R64Effect 0x108c29 12 14) (EffectPart.reads (.reg (.gpr 12)) [.gpr 14] []) (.reg (.gpr 12))) #v[67]
    (.letOp (n := 122) (.exec 0x108c29 (fun s => s.RIP = 0x108c29) (movR64R64Effect 0x108c29 12 14) (Reg.operands [.gpr 14] [])) #v[67]
    (.letOp (n := 123) (.out 0x108c2c (movR32R32Effect 0x108c2c 2 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[111]
    (.letOp (n := 124) (.exec 0x108c2c (fun s => s.RIP = 0x108c2c) (movR32R32Effect 0x108c2c 2 1 5) (Reg.operands [.gpr 5] [])) #v[111]
    (.letOp (n := 125) (.out 0x108c2e (shrR64ClEffect 0x108c2e 3 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[121, 123]
    (.letOp (n := 126) (.exec 0x108c2e (fun s => s.RIP = 0x108c2e) (shrR64ClEffect 0x108c2e 3 12) (Reg.operands [.gpr 12, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[121, 123]
    (.letOp (n := 127) (.out 0x108c31 (andR64R64Effect 0x108c31 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 3] []) (.reg (.gpr 2))) #v[107, 105]
    (.letOp (n := 128) (.exec 0x108c31 (fun s => s.RIP = 0x108c31) (andR64R64Effect 0x108c31 2 3) (Reg.operands [.gpr 2, .gpr 3] [])) #v[107, 105]
    (.letOp (n := 129) (.out 0x108c34 (xorR64R64Effect 0x108c34 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[127, 103]
    (.letOp (n := 130) (.exec 0x108c34 (fun s => s.RIP = 0x108c34) (xorR64R64Effect 0x108c34 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[127, 103]
    (.letOp (n := 131) (.out 0x108c37 (orR64R64Effect 0x108c37 12 7) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 7] []) (.reg (.gpr 12))) #v[125, 119]
    (.letOp (n := 132) (.exec 0x108c37 (fun s => s.RIP = 0x108c37) (orR64R64Effect 0x108c37 12 7) (Reg.operands [.gpr 12, .gpr 7] [])) #v[125, 119]
    (b_l108bc1_2))))))))))))))))))))))))))))))))))))))))

def bytes_l108bc1_1 : List UInt8 :=
  [0x49, 0x31, 0xC5, 0x89, 0xC8, 0x4D, 0x89, 0xEA, 0x89, 0xC1, 0x49, 0xD3, 0xE2, 0x48, 0x8B, 0x74,
    0x24, 0x48, 0x48, 0x31, 0xF3, 0x48, 0xF7, 0xDA, 0x49, 0x89, 0xFB, 0x8B, 0x6C, 0x24, 0x44, 0x89,
    0xE9, 0x49, 0xD3, 0xEB, 0x89, 0xC1, 0x48, 0xD3, 0xE7, 0x4D, 0x89, 0xF4, 0x89, 0xE9, 0x49, 0xD3,
    0xEC, 0x48, 0x21, 0xDA, 0x48, 0x31, 0xF2, 0x49, 0x09, 0xFC] ++ bytes_l108bc1_2

theorem code_l108bc1_1 : ∀ x ∈ codeRange 0x108c00 bytes_l108bc1_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x8c00 58 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l108bc1_2

@[cfg_block] def b_l108bc1 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x108bc1 (xorR64R64Effect 0x108bc1 10 13) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 13] []) (.reg (.gpr 10))) #v[10, 13]
    (.letOp (n := 54) (.exec 0x108bc1 (fun s => s.RIP = 0x108bc1) (xorR64R64Effect 0x108bc1 10 13) (Reg.operands [.gpr 10, .gpr 13] [])) #v[10, 13]
    (.letOp (n := 55) (.out 0x108bc4 (negR64Effect 0x108bc4 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[7]
    (.letOp (n := 56) (.exec 0x108bc4 (fun s => s.RIP = 0x108bc4) (negR64Effect 0x108bc4 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 57) (.out 0x108bc7 (andR64R64Effect 0x108bc7 7 10) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 10] []) (.reg (.gpr 7))) #v[55, 53]
    (.letOp (n := 58) (.exec 0x108bc7 (fun s => s.RIP = 0x108bc7) (andR64R64Effect 0x108bc7 7 10) (Reg.operands [.gpr 7, .gpr 10] [])) #v[55, 53]
    (.letOp (n := 59) (.out 0x108bca (xorR64R64Effect 0x108bca 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 13] []) (.reg (.gpr 7))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x108bca (fun s => s.RIP = 0x108bca) (xorR64R64Effect 0x108bca 7 13) (Reg.operands [.gpr 7, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x108bcd (xorR64R64Effect 0x108bcd 5 11) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 11] []) (.reg (.gpr 5))) #v[5, 11]
    (.letOp (n := 62) (.exec 0x108bcd (fun s => s.RIP = 0x108bcd) (xorR64R64Effect 0x108bcd 5 11) (Reg.operands [.gpr 5, .gpr 11] [])) #v[5, 11]
    (.letOp (n := 63) (.out 0x108bd0 (negR64Effect 0x108bd0 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14] []) (.reg (.gpr 14))) #v[14]
    (.letOp (n := 64) (.exec 0x108bd0 (fun s => s.RIP = 0x108bd0) (negR64Effect 0x108bd0 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 65) (.out 0x108bd3 (andR64R64Effect 0x108bd3 14 5) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 5] []) (.reg (.gpr 14))) #v[63, 61]
    (.letOp (n := 66) (.exec 0x108bd3 (fun s => s.RIP = 0x108bd3) (andR64R64Effect 0x108bd3 14 5) (Reg.operands [.gpr 14, .gpr 5] [])) #v[63, 61]
    (.letOp (n := 67) (.out 0x108bd6 (xorR64R64Effect 0x108bd6 14 11) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 11] []) (.reg (.gpr 14))) #v[65, 11]
    (.letOp (n := 68) (.exec 0x108bd6 (fun s => s.RIP = 0x108bd6) (xorR64R64Effect 0x108bd6 14 11) (Reg.operands [.gpr 14, .gpr 11] [])) #v[65, 11]
    (.letOp (n := 69) (.out 0x108bd9 (xorR64R64Effect 0x108bd9 8 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 12] []) (.reg (.gpr 8))) #v[8, 12]
    (.letOp (n := 70) (.exec 0x108bd9 (fun s => s.RIP = 0x108bd9) (xorR64R64Effect 0x108bd9 8 12) (Reg.operands [.gpr 8, .gpr 12] [])) #v[8, 12]
    (.letOp (n := 71) (.out 0x108bdc (negR64Effect 0x108bdc 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15] []) (.reg (.gpr 15))) #v[15]
    (.letOp (n := 72) (.exec 0x108bdc (fun s => s.RIP = 0x108bdc) (negR64Effect 0x108bdc 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 73) (.out 0x108bdf (andR64R64Effect 0x108bdf 15 8) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 8] []) (.reg (.gpr 15))) #v[71, 69]
    (.letOp (n := 74) (.exec 0x108bdf (fun s => s.RIP = 0x108bdf) (andR64R64Effect 0x108bdf 15 8) (Reg.operands [.gpr 15, .gpr 8] [])) #v[71, 69]
    (.letOp (n := 75) (.out 0x108be2 (xorR64R64Effect 0x108be2 15 12) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 12] []) (.reg (.gpr 15))) #v[73, 12]
    (.letOp (n := 76) (.exec 0x108be2 (fun s => s.RIP = 0x108be2) (xorR64R64Effect 0x108be2 15 12) (Reg.operands [.gpr 15, .gpr 12] [])) #v[73, 12]
    (.letOp (n := 77) (.out 0x108be5 (andR32Imm8Effect 0x108be5 3 6 0x1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[6]
    (.letOp (n := 78) (.exec 0x108be5 (fun s => s.RIP = 0x108be5) (andR32Imm8Effect 0x108be5 3 6 0x1) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 79) (.out 0x108be8 (movR64R64Effect 0x108be8 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[0]
    (.letOp (n := 80) (.exec 0x108be8 (fun s => s.RIP = 0x108be8) (movR64R64Effect 0x108be8 8 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 81) (.out 0x108beb (notR64Effect 0x108beb 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[79]
    (.letOp (n := 82) (.exec 0x108beb (fun s => s.RIP = 0x108beb) (notR64Effect 0x108beb 8) (Reg.operands [.gpr 8] [])) #v[79]
    (.letOp (n := 83) (.out 0x108bee (addR64R64Effect 0x108bee 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6] []) (.reg (.gpr 8))) #v[81, 77]
    (.letOp (n := 84) (.exec 0x108bee (fun s => s.RIP = 0x108bee) (addR64R64Effect 0x108bee 8 6) (Reg.operands [.gpr 8, .gpr 6] [])) #v[81, 77]
    (.letOp (n := 85) (.out 0x108bf1 (xorR64R64Effect 0x108bf1 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[83, 0]
    (.letOp (n := 86) (.exec 0x108bf1 (fun s => s.RIP = 0x108bf1) (xorR64R64Effect 0x108bf1 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[83, 0]
    (.letOp (n := 87) (.out 0x108bf4 (movzxR32M8Effect 0x108bf4 6 13 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 88) (.exec 0x108bf4 (LoadPre 0x108bf4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108bf4 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108bf4 6 13 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 89) (.out 0x108bfa (negR64Effect 0x108bfa 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[87]
    (.letOp (n := 90) (.exec 0x108bfa (fun s => s.RIP = 0x108bfa) (negR64Effect 0x108bfa 13) (Reg.operands [.gpr 13] [])) #v[87]
    (.letOp (n := 91) (.out 0x108bfd (andR64R64Effect 0x108bfd 13 8) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 8] []) (.reg (.gpr 13))) #v[89, 85]
    (.letOp (n := 92) (.exec 0x108bfd (fun s => s.RIP = 0x108bfd) (andR64R64Effect 0x108bfd 13 8) (Reg.operands [.gpr 13, .gpr 8] [])) #v[89, 85]
    (b_l108bc1_1))))))))))))))))))))))))))))))))))))))))

def bytes_l108bc1 : List UInt8 :=
  [0x4D, 0x31, 0xEA, 0x48, 0xF7, 0xDF, 0x4C, 0x21, 0xD7, 0x4C, 0x31, 0xEF, 0x4C, 0x31, 0xDD, 0x49,
    0xF7, 0xDE, 0x49, 0x21, 0xEE, 0x4D, 0x31, 0xDE, 0x4D, 0x31, 0xE0, 0x49, 0xF7, 0xDF, 0x4D, 0x21,
    0xC7, 0x4D, 0x31, 0xE7, 0x83, 0xE6, 0x01, 0x49, 0x89, 0xC0, 0x49, 0xF7, 0xD0, 0x49, 0x01, 0xF0,
    0x49, 0x31, 0xC0, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x10, 0x49, 0xF7, 0xDD, 0x4D, 0x21, 0xC5] ++ bytes_l108bc1_1

theorem code_l108bc1 : ∀ x ∈ codeRange 0x108bc1 bytes_l108bc1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x8bc1 63 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l108bc1_1

@[cfg_block] def b_l108df9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x108df9 (movR32Imm32Effect 0x108df9 5 6 0x1b) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 54) (.exec 0x108df9 (fun s => s.RIP = 0x108df9) (movR32Imm32Effect 0x108df9 5 6 0x1b) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x108dfe (movR64Imm32Effect 0x108dfe 7 0x202b38) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 56) (.exec 0x108dfe (fun s => s.RIP = 0x108dfe) (movR64Imm32Effect 0x108dfe 7 0x202b38) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x108e05 (movR64Imm32Effect 0x108e05 2 0x202b58) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x108e05 (fun s => s.RIP = 0x108e05) (movR64Imm32Effect 0x108e05 2 0x202b58) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x108e0c (callEffect (fun _ => 0x129560) 0x108e11) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x108e0c (PushPre 0x108e0c 5) (callEffect (fun _ => 0x129560) 0x108e11) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x108e11⟩) #v[]
    (.terminate (.call ⟨.l129560, RegMap.args [(2, 57), (4, 59), (5, 5), (6, 53), (7, 55)] 62⟩ { target := .l108e11, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l108df9 : List UInt8 :=
  [0xBE, 0x1B, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC7, 0x38, 0x2B, 0x20, 0x00, 0x48, 0xC7, 0xC2, 0x58,
    0x2B, 0x20, 0x00, 0xE8, 0x4F, 0x07, 0x02, 0x00]

theorem code_l108df9 : ∀ x ∈ codeRange 0x108df9 bytes_l108df9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x8df9 24 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l108e11 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x108e11 (movR32Imm32Effect 0x108e11 5 7 0x4) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 54) (.exec 0x108e11 (fun s => s.RIP = 0x108e11) (movR32Imm32Effect 0x108e11 5 7 0x4) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x108e16 (movR32Imm32Effect 0x108e16 5 6 0x4) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 56) (.exec 0x108e16 (fun s => s.RIP = 0x108e16) (movR32Imm32Effect 0x108e16 5 6 0x4) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x108e1b (movR64Imm32Effect 0x108e1b 2 0x202b20) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x108e1b (fun s => s.RIP = 0x108e1b) (movR64Imm32Effect 0x108e1b 2 0x202b20) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x108e22 (callEffect (fun _ => 0x1295f2) 0x108e27) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x108e22 (PushPre 0x108e22 5) (callEffect (fun _ => 0x1295f2) 0x108e27) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x108e27⟩) #v[]
    (.terminate (.call ⟨.l1295f2, RegMap.args [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)] 62⟩ { target := .l108e27, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l108e11 : List UInt8 :=
  [0xBF, 0x04, 0x00, 0x00, 0x00, 0xBE, 0x04, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC2, 0x20, 0x2B, 0x20,
    0x00, 0xE8, 0xCB, 0x07, 0x02, 0x00]

theorem code_l108e11 : ∀ x ∈ codeRange 0x108e11 bytes_l108e11, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x8e11 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l108e27 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x108e27 (fun s => s.RIP = 0x108e27) (fun _ => nopEffect 0x108e27 9) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l108e30, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 54⟩))

def bytes_l108e27 : List UInt8 :=
  [0x66, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem code_l108e27 : ∀ x ∈ codeRange 0x108e27 bytes_l108e27, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x8e27 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l108e30_2 : Block Op Label signature Reg.count 112 :=
  .letOp (n := 112) (.exec 0x108f23 (StorePre 0x108f23 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x108f23 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x108f23 (.sib 4 none 0 (.d32 0xd0)) 0x0) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 113) (.out 0x108f2f (movR64M64Effect 0x108f2f 0 (.base 8 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[8]
    (.letOp (n := 114) (.exec 0x108f2f (LoadPre 0x108f2f (fun s => AddrMode.addr (.base 8 (.d8 0x18)) s (0x108f2f + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x108f2f 0 (.base 8 (.d8 0x18))) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 115) (.exec 0x108f33 (StorePre 0x108f33 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x108f33 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108f33 0 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[113, 65]
    (.letOp (n := 116) (.out 0x108f3b (movR64M64Effect 0x108f3b 0 (.base 8 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[8]
    (.letOp (n := 117) (.exec 0x108f3b (LoadPre 0x108f3b (fun s => AddrMode.addr (.base 8 (.d8 0x10)) s (0x108f3b + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x108f3b 0 (.base 8 (.d8 0x10))) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 118) (.exec 0x108f3f (StorePre 0x108f3f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x108f3f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108f3f 0 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[116, 65]
    (.letOp (n := 119) (.out 0x108f47 (movR64M64Effect 0x108f47 0 (.base 8 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[8]
    (.letOp (n := 120) (.exec 0x108f47 (LoadPre 0x108f47 (fun s => AddrMode.addr (.base 8 .none) s (0x108f47 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x108f47 0 (.base 8 .none)) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 121) (.out 0x108f4a (movR64M64Effect 0x108f4a 1 (.base 8 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 8] []) (.reg (.gpr 1))) #v[8]
    (.letOp (n := 122) (.exec 0x108f4a (LoadPre 0x108f4a (fun s => AddrMode.addr (.base 8 (.d8 0x8)) s (0x108f4a + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x108f4a 1 (.base 8 (.d8 0x8))) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 123) (.exec 0x108f4e (StorePre 0x108f4e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x108f4e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108f4e 1 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[121, 65]
    (.letOp (n := 124) (.exec 0x108f56 (StorePre 0x108f56 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x108f56 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108f56 0 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[119, 65]
    (.letOp (n := 125) (.exec 0x108f5e (StorePre 0x108f5e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x108f5e + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x108f5e (.sib 4 none 0 (.d32 0x118)) 0x0) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 126) (.out 0x108f66 (movR32Imm32Effect 0x108f66 5 5 0x1) (EffectPart.reads (.reg (.gpr 5)) [] []) (.reg (.gpr 5))) #v[]
    (.letOp (n := 127) (.exec 0x108f66 (fun s => s.RIP = 0x108f66) (movR32Imm32Effect 0x108f66 5 5 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 128) (.out 0x108f6b (movR32Imm32Effect 0x108f6b 5 2 0x24f) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 129) (.exec 0x108f6b (fun s => s.RIP = 0x108f6b) (movR32Imm32Effect 0x108f6b 5 2 0x24f) (Reg.operands [] [])) #v[]
    (.letOp (n := 130) (.out 0x108f70 (leaR64Effect 0x108f70 14 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[65]
    (.letOp (n := 131) (.exec 0x108f70 (fun s => s.RIP = 0x108f70) (leaR64Effect 0x108f70 14 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[65]
    (.terminate (.br ⟨.l1091e4, RegMap.args [(0, 119), (1, 121), (2, 128), (3, 3), (4, 65), (5, 126), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 130), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 132⟩)))))))))))))))))))))

def bytes_l108e30_2 : List UInt8 :=
  [0x48, 0xC7, 0x84, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x49, 0x8B, 0x40, 0x18,
    0x48, 0x89, 0x84, 0x24, 0x10, 0x01, 0x00, 0x00, 0x49, 0x8B, 0x40, 0x10, 0x48, 0x89, 0x84, 0x24,
    0x08, 0x01, 0x00, 0x00, 0x49, 0x8B, 0x00, 0x49, 0x8B, 0x48, 0x08, 0x48, 0x89, 0x8C, 0x24, 0x00,
    0x01, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0xF8, 0x00, 0x00, 0x00, 0xC6, 0x84, 0x24, 0x18, 0x01,
    0x00, 0x00, 0x00, 0xBD, 0x01, 0x00, 0x00, 0x00, 0xBA, 0x4F, 0x02, 0x00, 0x00, 0x4C, 0x8D, 0x74,
    0x24, 0x10, 0xE9, 0x6A, 0x02, 0x00, 0x00]

theorem code_l108e30_2 : ∀ x ∈ codeRange 0x108f23 bytes_l108e30_2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x8f23 87 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l108e30_1 : Block Op Label signature Reg.count 86 :=
  .letOp (n := 86) (.exec 0x108e90 (StorePre 0x108e90 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x108e90 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108e90 0 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[84, 65]
    (.letOp (n := 87) (.out 0x108e98 (movR64M64Effect 0x108e98 0 (.base 2 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 88) (.exec 0x108e98 (LoadPre 0x108e98 (fun s => AddrMode.addr (.base 2 .none) s (0x108e98 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x108e98 0 (.base 2 .none)) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 89) (.exec 0x108e9b (StorePre 0x108e9b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x108e9b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108e9b 2 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2, 65]
    (.letOp (n := 90) (.out 0x108ea3 (movR64M64Effect 0x108ea3 1 (.base 2 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2]
    (.letOp (n := 91) (.exec 0x108ea3 (LoadPre 0x108ea3 (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x108ea3 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x108ea3 1 (.base 2 (.d8 0x8))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 92) (.exec 0x108ea7 (StorePre 0x108ea7 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x108ea7 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108ea7 1 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[90, 65]
    (.letOp (n := 93) (.exec 0x108eaf (StorePre 0x108eaf 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x108eaf + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108eaf 0 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[87, 65]
    (.letOp (n := 94) (.exec 0x108eb4 (StorePre 0x108eb4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x108eb4 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x108eb4 (.sib 4 none 0 (.d32 0x98)) 0x0) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 95) (.out 0x108ebc (movR64M64Effect 0x108ebc 0 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 96) (.exec 0x108ebc (LoadPre 0x108ebc (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x108ebc + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x108ebc 0 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 97) (.exec 0x108ec0 (StorePre 0x108ec0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x108ec0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108ec0 0 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[95, 65]
    (.letOp (n := 98) (.out 0x108ec8 (movR64M64Effect 0x108ec8 0 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 99) (.exec 0x108ec8 (LoadPre 0x108ec8 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x108ec8 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x108ec8 0 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 100) (.exec 0x108ecc (StorePre 0x108ecc 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x108ecc + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108ecc 0 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[98, 65]
    (.letOp (n := 101) (.out 0x108ed4 (movR64M64Effect 0x108ed4 0 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 102) (.exec 0x108ed4 (LoadPre 0x108ed4 (fun s => AddrMode.addr (.base 6 .none) s (0x108ed4 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x108ed4 0 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 103) (.out 0x108ed7 (movR64M64Effect 0x108ed7 1 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[6]
    (.letOp (n := 104) (.exec 0x108ed7 (LoadPre 0x108ed7 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x108ed7 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x108ed7 1 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 105) (.exec 0x108edb (StorePre 0x108edb 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x108edb + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108edb 1 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[103, 65]
    (.letOp (n := 106) (.exec 0x108ee3 (StorePre 0x108ee3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x108ee3 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108ee3 0 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[101, 65]
    (.letOp (n := 107) (.exec 0x108eeb (StorePre 0x108eeb 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x108eeb + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x108eeb (.sib 4 none 0 (.d32 0xc8)) 0x0) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 108) (.exec 0x108ef3 (StorePre 0x108ef3 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x108ef3 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x108ef3 (.sib 4 none 0 (.d32 0xf0)) 0x0) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 109) (.exec 0x108eff (StorePre 0x108eff 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x108eff + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x108eff (.sib 4 none 0 (.d32 0xe8)) 0x0) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 110) (.exec 0x108f0b (StorePre 0x108f0b 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x108f0b + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x108f0b (.sib 4 none 0 (.d32 0xe0)) 0x0) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 111) (.exec 0x108f17 (StorePre 0x108f17 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x108f17 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x108f17 (.sib 4 none 0 (.d32 0xd8)) 0x0) (Reg.operands [.gpr 4] [])) #v[65]
    (b_l108e30_2))))))))))))))))))))))))))

def bytes_l108e30_1 : List UInt8 :=
  [0x48, 0x89, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x02, 0x48, 0x89, 0x94, 0x24, 0xA0,
    0x00, 0x00, 0x00, 0x48, 0x8B, 0x4A, 0x08, 0x48, 0x89, 0x8C, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48,
    0x89, 0x44, 0x24, 0x78, 0xC6, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x46, 0x18,
    0x48, 0x89, 0x84, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x46, 0x10, 0x48, 0x89, 0x84, 0x24,
    0xB8, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x06, 0x48, 0x8B, 0x4E, 0x08, 0x48, 0x89, 0x8C, 0x24, 0xB0,
    0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0xA8, 0x00, 0x00, 0x00, 0xC6, 0x84, 0x24, 0xC8, 0x00,
    0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0xF0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48,
    0xC7, 0x84, 0x24, 0xE8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0xE0,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00] ++ bytes_l108e30_2

theorem code_l108e30_1 : ∀ x ∈ codeRange 0x108e90 bytes_l108e30_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x8e90 147 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l108e30_2

@[cfg_block] def b_l108e30 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x108e30 (pushR64Effect 0x108e30 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x108e30 (PushPre 0x108e30 1) (pushR64Effect 0x108e30 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x108e31 (pushR64Effect 0x108e31 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x108e31 (PushPre 0x108e31 2) (pushR64Effect 0x108e31 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x108e33 (pushR64Effect 0x108e33 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x108e33 (PushPre 0x108e33 2) (pushR64Effect 0x108e33 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x108e35 (pushR64Effect 0x108e35 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x108e35 (PushPre 0x108e35 2) (pushR64Effect 0x108e35 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x108e37 (pushR64Effect 0x108e37 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x108e37 (PushPre 0x108e37 2) (pushR64Effect 0x108e37 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x108e39 (pushR64Effect 0x108e39 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x108e39 (PushPre 0x108e39 1) (pushR64Effect 0x108e39 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x108e3a (subR64Imm32Effect 0x108e3a 4 0x168) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x108e3a (fun s => s.RIP = 0x108e3a) (subR64Imm32Effect 0x108e3a 4 0x168) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.exec 0x108e41 (StorePre 0x108e41 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x148)) s (0x108e41 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108e41 1 (.sib 4 none 0 (.d32 0x148))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1, 65]
    (.letOp (n := 68) (.exec 0x108e49 (StorePre 0x108e49 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x108e49 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108e49 7 (.sib 4 none 0 (.d32 0x140))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[7, 65]
    (.letOp (n := 69) (.out 0x108e51 (movR64M64Effect 0x108e51 0 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 70) (.exec 0x108e51 (LoadPre 0x108e51 (fun s => AddrMode.addr (.base 6 .none) s (0x108e51 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x108e51 0 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 71) (.exec 0x108e54 (StorePre 0x108e54 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x108e54 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108e54 0 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[69, 65]
    (.letOp (n := 72) (.out 0x108e5c (movR64M64Effect 0x108e5c 0 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 73) (.exec 0x108e5c (LoadPre 0x108e5c (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x108e5c + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x108e5c 0 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 74) (.exec 0x108e60 (StorePre 0x108e60 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x138)) s (0x108e60 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108e60 0 (.sib 4 none 0 (.d32 0x138))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[72, 65]
    (.letOp (n := 75) (.out 0x108e68 (movR64M64Effect 0x108e68 0 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 76) (.exec 0x108e68 (LoadPre 0x108e68 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x108e68 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x108e68 0 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 77) (.exec 0x108e6c (StorePre 0x108e6c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x108e6c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108e6c 0 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[75, 65]
    (.letOp (n := 78) (.out 0x108e74 (movR64M64Effect 0x108e74 0 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 79) (.exec 0x108e74 (LoadPre 0x108e74 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x108e74 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x108e74 0 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 80) (.exec 0x108e78 (StorePre 0x108e78 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x108e78 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108e78 0 (.sib 4 none 0 (.d32 0x130))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[78, 65]
    (.letOp (n := 81) (.out 0x108e80 (movR64M64Effect 0x108e80 0 (.base 2 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 82) (.exec 0x108e80 (LoadPre 0x108e80 (fun s => AddrMode.addr (.base 2 (.d8 0x18)) s (0x108e80 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x108e80 0 (.base 2 (.d8 0x18))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 83) (.exec 0x108e84 (StorePre 0x108e84 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x108e84 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108e84 0 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[81, 65]
    (.letOp (n := 84) (.out 0x108e8c (movR64M64Effect 0x108e8c 0 (.base 2 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 85) (.exec 0x108e8c (LoadPre 0x108e8c (fun s => AddrMode.addr (.base 2 (.d8 0x10)) s (0x108e8c + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x108e8c 0 (.base 2 (.d8 0x10))) (Reg.operands [.gpr 2] [])) #v[2]
    (b_l108e30_1)))))))))))))))))))))))))))))))))

def bytes_l108e30 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0x68, 0x01, 0x00,
    0x00, 0x48, 0x89, 0x8C, 0x24, 0x48, 0x01, 0x00, 0x00, 0x48, 0x89, 0xBC, 0x24, 0x40, 0x01, 0x00,
    0x00, 0x48, 0x8B, 0x06, 0x48, 0x89, 0x84, 0x24, 0x28, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x46, 0x08,
    0x48, 0x89, 0x84, 0x24, 0x38, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x46, 0x10, 0x48, 0x89, 0x84, 0x24,
    0x20, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x46, 0x18, 0x48, 0x89, 0x84, 0x24, 0x30, 0x01, 0x00, 0x00,
    0x48, 0x8B, 0x42, 0x18, 0x48, 0x89, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x42, 0x10] ++ bytes_l108e30_1

theorem code_l108e30 : ∀ x ∈ codeRange 0x108e30 bytes_l108e30, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x8e30 96 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l108e30_1

@[cfg_block] def b_l108f80 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x108f80 (movR32Imm32Effect 0x108f80 6 12 0x1) (EffectPart.reads (.reg (.gpr 12)) [] []) (.reg (.gpr 12))) #v[]
    (.letOp (n := 54) (.exec 0x108f80 (fun s => s.RIP = 0x108f80) (movR32Imm32Effect 0x108f80 6 12 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.exec 0x108f86 (StorePre 0x108f86 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x108f86 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x108f86 (.sib 4 none 0 (.d8 0x8)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x108f8f (xorR32R32Effect 0x108f8f 2 3 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 3] []) (.reg (.gpr 3))) #v[3, 3]
    (.letOp (n := 57) (.exec 0x108f8f (fun s => s.RIP = 0x108f8f) (xorR32R32Effect 0x108f8f 2 3 3) (Reg.operands [.gpr 3, .gpr 3] [])) #v[3, 3]
    (.letOp (n := 58) (.out 0x108f91 (movR32Imm32Effect 0x108f91 6 15 0x1) (EffectPart.reads (.reg (.gpr 15)) [] []) (.reg (.gpr 15))) #v[]
    (.letOp (n := 59) (.exec 0x108f91 (fun s => s.RIP = 0x108f91) (movR32Imm32Effect 0x108f91 6 15 0x1) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l108f97, RegMap.args [(3, 56), (4, 4), (5, 5), (12, 53), (14, 14), (15, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l108f80 : List UInt8 :=
  [0x41, 0xBC, 0x01, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00, 0x31,
    0xDB, 0x41, 0xBF, 0x01, 0x00, 0x00, 0x00]

theorem code_l108f80 : ∀ x ∈ codeRange 0x108f80 bytes_l108f80, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x8f80 23 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l108f97 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x108f97 (movR64R64Effect 0x108f97 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[15]
    (.letOp (n := 54) (.exec 0x108f97 (fun s => s.RIP = 0x108f97) (movR64R64Effect 0x108f97 0 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.out 0x108f9a (shrR64Effect 0x108f9a 4 0 63) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x108f9a (fun s => s.RIP = 0x108f9a) (shrR64Effect 0x108f9a 4 0 63) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 57) (.exec 0x108f9e (StorePre 0x108f9e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x108f9e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108f9e 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 58) (.exec 0x108fa3 (StorePre 0x108fa3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x108fa3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108fa3 4 0 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 59) (.out 0x108fa7 (leaR64Effect 0x108fa7 13 (.sib 4 none 0 (.d8 0x7))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 60) (.exec 0x108fa7 (fun s => s.RIP = 0x108fa7) (leaR64Effect 0x108fa7 13 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x108fac (movR64R64Effect 0x108fac 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 62) (.exec 0x108fac (fun s => s.RIP = 0x108fac) (movR64R64Effect 0x108fac 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 63) (.out 0x108faf (shrR64Effect 0x108faf 4 0 63) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[61]
    (.letOp (n := 64) (.exec 0x108faf (fun s => s.RIP = 0x108faf) (shrR64Effect 0x108faf 4 0 63) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[61]
    (.letOp (n := 65) (.exec 0x108fb3 (StorePre 0x108fb3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x150)) s (0x108fb3 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108fb3 0 (.sib 4 none 0 (.d32 0x150))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[63, 4]
    (.letOp (n := 66) (.exec 0x108fbb (StorePre 0x108fbb 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x108fbb + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108fbb 4 0 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[63, 4]
    (.letOp (n := 67) (.out 0x108fbf (movR64R64Effect 0x108fbf 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 68) (.exec 0x108fbf (fun s => s.RIP = 0x108fbf) (movR64R64Effect 0x108fbf 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 69) (.out 0x108fc2 (leaR64Effect 0x108fc2 6 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 70) (.exec 0x108fc2 (fun s => s.RIP = 0x108fc2) (leaR64Effect 0x108fc2 6 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.out 0x108fc7 (leaR64Effect 0x108fc7 2 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 72) (.exec 0x108fc7 (fun s => s.RIP = 0x108fc7) (leaR64Effect 0x108fc7 2 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.out 0x108fcf (movR64R64Effect 0x108fcf 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 15] []) (.reg (.gpr 1))) #v[15]
    (.letOp (n := 74) (.exec 0x108fcf (fun s => s.RIP = 0x108fcf) (movR64R64Effect 0x108fcf 1 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 75) (.out 0x108fd2 (movR64R64Effect 0x108fd2 8 3) (EffectPart.reads (.reg (.gpr 8)) [.gpr 3] []) (.reg (.gpr 8))) #v[3]
    (.letOp (n := 76) (.exec 0x108fd2 (fun s => s.RIP = 0x108fd2) (movR64R64Effect 0x108fd2 8 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 77) (.out 0x108fd5 (movR32M32Effect 0x108fd5 14 (.sib 4 none 0 (.d8 0x74))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 78) (.exec 0x108fd5 (LoadPre 0x108fd5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x74)) s (0x108fd5 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x108fd5 14 (.sib 4 none 0 (.d8 0x74))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.out 0x108fda (movR32R32Effect 0x108fda 3 9 14) (EffectPart.reads (.reg (.gpr 9)) [.gpr 14] []) (.reg (.gpr 9))) #v[77]
    (.letOp (n := 80) (.exec 0x108fda (fun s => s.RIP = 0x108fda) (movR32R32Effect 0x108fda 3 9 14) (Reg.operands [.gpr 14] [])) #v[77]
    (.letOp (n := 81) (.out 0x108fdd (callEffect (fun _ => 0x108890) 0x108fe2) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 82) (.exec 0x108fdd (PushPre 0x108fdd 5) (callEffect (fun _ => 0x108890) 0x108fe2) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 83) (.const ⟨64, 0x108fe2⟩) #v[]
    (.terminate (.call ⟨.l108890, RegMap.args [(0, 63), (1, 73), (2, 71), (3, 3), (4, 81), (5, 5), (6, 69), (7, 67), (8, 75), (9, 79), (12, 12), (13, 59), (14, 77), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 84⟩ { target := .l108fe2, kept := #v[], arity := rfl, guard := some (Fin.last 83) }))))))))))))))))))))))))))))))))

def bytes_l108f97 : List UInt8 :=
  [0x4C, 0x89, 0xF8, 0x48, 0xC1, 0xE8, 0x3F, 0x48, 0x89, 0x44, 0x24, 0x60, 0x88, 0x44, 0x24, 0x07,
    0x4C, 0x8D, 0x6C, 0x24, 0x07, 0x48, 0x89, 0xD8, 0x48, 0xC1, 0xE8, 0x3F, 0x48, 0x89, 0x84, 0x24,
    0x50, 0x01, 0x00, 0x00, 0x88, 0x44, 0x24, 0x07, 0x4C, 0x89, 0xF7, 0x48, 0x8D, 0x74, 0x24, 0x78,
    0x48, 0x8D, 0x94, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF9, 0x49, 0x89, 0xD8, 0x44, 0x8B,
    0x74, 0x24, 0x74, 0x45, 0x89, 0xF1, 0xE8, 0xAE, 0xF8, 0xFF, 0xFF]

theorem code_l108f97 : ∀ x ∈ codeRange 0x108f97 bytes_l108f97, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x8f97 75 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l108fe2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x108fe2 (movR64M64Effect 0x108fe2 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x108fe2 (LoadPre 0x108fe2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x108fe2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x108fe2 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x108fe7 (movR64R64Effect 0x108fe7 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0] []) (.reg (.gpr 2))) #v[53]
    (.letOp (n := 56) (.exec 0x108fe7 (fun s => s.RIP = 0x108fe7) (movR64R64Effect 0x108fe7 2 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x108fea (movR64R64Effect 0x108fea 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 58) (.exec 0x108fea (fun s => s.RIP = 0x108fea) (movR64R64Effect 0x108fea 1 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 59) (.exec 0x108fed (StorePre 0x108fed 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x108fed + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108fed 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 60) (.out 0x108ff2 (shrR64Effect 0x108ff2 4 2 63) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[55]
    (.letOp (n := 61) (.exec 0x108ff2 (fun s => s.RIP = 0x108ff2) (shrR64Effect 0x108ff2 4 2 63) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[55]
    (.letOp (n := 62) (.exec 0x108ff6 (StorePre 0x108ff6 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x158)) s (0x108ff6 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108ff6 2 (.sib 4 none 0 (.d32 0x158))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[60, 4]
    (.letOp (n := 63) (.exec 0x108ffe (StorePre 0x108ffe 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x108ffe + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108ffe 4 2 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[60, 4]
    (.letOp (n := 64) (.exec 0x109002 (fun s => s.RIP = 0x109002) (movR64R64Effect 0x109002 0 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 65) (.out 0x109005 (movR64R64Effect 0x109005 13 12) (EffectPart.reads (.reg (.gpr 13)) [.gpr 12] []) (.reg (.gpr 13))) #v[12]
    (.letOp (n := 66) (.exec 0x109005 (fun s => s.RIP = 0x109005) (movR64R64Effect 0x109005 13 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 67) (.out 0x109008 (movR64R64Effect 0x109008 8 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 12] []) (.reg (.gpr 8))) #v[12]
    (.letOp (n := 68) (.exec 0x109008 (fun s => s.RIP = 0x109008) (movR64R64Effect 0x109008 8 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 69) (.exec 0x10900b (StorePre 0x10900b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x10900b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10900b 12 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[12, 4]
    (.letOp (n := 70) (.out 0x109010 (shrR64Effect 0x109010 4 13 63) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[65]
    (.letOp (n := 71) (.exec 0x109010 (fun s => s.RIP = 0x109010) (shrR64Effect 0x109010 4 13 63) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[65]
    (.letOp (n := 72) (.exec 0x109014 (StorePre 0x109014 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x109014 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x109014 5 13 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[70, 4]
    (.letOp (n := 73) (.out 0x109019 (leaR64Effect 0x109019 12 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 74) (.exec 0x109019 (fun s => s.RIP = 0x109019) (leaR64Effect 0x109019 12 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.out 0x10901e (movR64R64Effect 0x10901e 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[73]
    (.letOp (n := 76) (.exec 0x10901e (fun s => s.RIP = 0x10901e) (movR64R64Effect 0x10901e 7 12) (Reg.operands [.gpr 12] [])) #v[73]
    (.letOp (n := 77) (.out 0x109021 (leaR64Effect 0x109021 6 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 78) (.exec 0x109021 (fun s => s.RIP = 0x109021) (leaR64Effect 0x109021 6 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.out 0x109026 (leaR64Effect 0x109026 2 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 80) (.exec 0x109026 (fun s => s.RIP = 0x109026) (leaR64Effect 0x109026 2 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 81) (.out 0x10902e (movR32R32Effect 0x10902e 3 9 14) (EffectPart.reads (.reg (.gpr 9)) [.gpr 14] []) (.reg (.gpr 9))) #v[14]
    (.letOp (n := 82) (.exec 0x10902e (fun s => s.RIP = 0x10902e) (movR32R32Effect 0x10902e 3 9 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 83) (.out 0x109031 (callEffect (fun _ => 0x108890) 0x109036) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 84) (.exec 0x109031 (PushPre 0x109031 5) (callEffect (fun _ => 0x108890) 0x109036) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 85) (.const ⟨64, 0x109036⟩) #v[]
    (.terminate (.call ⟨.l108890, RegMap.args [(1, 57), (2, 79), (3, 3), (4, 83), (5, 5), (6, 77), (7, 75), (8, 67), (9, 81), (12, 73), (13, 70), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 86⟩ { target := .l109036, kept := #v[], arity := rfl, guard := some (Fin.last 85) }))))))))))))))))))))))))))))))))))

def bytes_l108fe2 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x08, 0x48, 0x89, 0xC2, 0x48, 0x89, 0xC1, 0x48, 0x89, 0x44, 0x24, 0x08,
    0x48, 0xC1, 0xEA, 0x3F, 0x48, 0x89, 0x94, 0x24, 0x58, 0x01, 0x00, 0x00, 0x88, 0x54, 0x24, 0x07,
    0x4C, 0x89, 0xE8, 0x4D, 0x89, 0xE5, 0x4D, 0x89, 0xE0, 0x4C, 0x89, 0x64, 0x24, 0x68, 0x49, 0xC1,
    0xED, 0x3F, 0x44, 0x88, 0x6C, 0x24, 0x07, 0x4C, 0x8D, 0x64, 0x24, 0x38, 0x4C, 0x89, 0xE7, 0x48,
    0x8D, 0x74, 0x24, 0x78, 0x48, 0x8D, 0x94, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x45, 0x89, 0xF1, 0xE8,
    0x5A, 0xF8, 0xFF, 0xFF]

theorem code_l108fe2 : ∀ x ∈ codeRange 0x108fe2 bytes_l108fe2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x8fe2 84 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109036_1 : Block Op Label signature Reg.count 83 :=
  .letOp (n := 83) (.out 0x1090b4 (movR64M64Effect 0x1090b4 0 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 84) (.exec 0x1090b4 (LoadPre 0x1090b4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1090b4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1090b4 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 85) (.exec 0x1090b9 (StorePre 0x1090b9 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x1090b9 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1090b9 4 0 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[83, 4]
    (.letOp (n := 86) (.exec 0x1090bd (fun s => s.RIP = 0x1090bd) (leaR64Effect 0x1090bd 0 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 87) (.out 0x1090c2 (movR64M64Effect 0x1090c2 1 (.sib 4 none 0 (.d32 0x150))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 88) (.exec 0x1090c2 (LoadPre 0x1090c2 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x150)) s (0x1090c2 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1090c2 1 (.sib 4 none 0 (.d32 0x150))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 89) (.exec 0x1090ca (StorePre 0x1090ca 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x1090ca + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1090ca 4 1 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[87, 4]
    (.letOp (n := 90) (.out 0x1090ce (leaR64Effect 0x1090ce 7 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 91) (.exec 0x1090ce (fun s => s.RIP = 0x1090ce) (leaR64Effect 0x1090ce 7 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 92) (.out 0x1090d3 (leaR64Effect 0x1090d3 6 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 93) (.exec 0x1090d3 (fun s => s.RIP = 0x1090d3) (leaR64Effect 0x1090d3 6 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 94) (.out 0x1090db (leaR64Effect 0x1090db 2 (.sib 4 none 0 (.d32 0xf8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 95) (.exec 0x1090db (fun s => s.RIP = 0x1090db) (leaR64Effect 0x1090db 2 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 96) (.out 0x1090e3 (movR64R64Effect 0x1090e3 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 15] []) (.reg (.gpr 1))) #v[15]
    (.letOp (n := 97) (.exec 0x1090e3 (fun s => s.RIP = 0x1090e3) (movR64R64Effect 0x1090e3 1 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 98) (.out 0x1090e6 (movR64R64Effect 0x1090e6 8 3) (EffectPart.reads (.reg (.gpr 8)) [.gpr 3] []) (.reg (.gpr 8))) #v[3]
    (.letOp (n := 99) (.exec 0x1090e6 (fun s => s.RIP = 0x1090e6) (movR64R64Effect 0x1090e6 8 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 100) (.out 0x1090e9 (movR32R32Effect 0x1090e9 3 15 14) (EffectPart.reads (.reg (.gpr 15)) [.gpr 14] []) (.reg (.gpr 15))) #v[14]
    (.letOp (n := 101) (.exec 0x1090e9 (fun s => s.RIP = 0x1090e9) (movR32R32Effect 0x1090e9 3 15 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 102) (.out 0x1090ec (movR32R32Effect 0x1090ec 3 9 14) (EffectPart.reads (.reg (.gpr 9)) [.gpr 14] []) (.reg (.gpr 9))) #v[14]
    (.letOp (n := 103) (.exec 0x1090ec (fun s => s.RIP = 0x1090ec) (movR32R32Effect 0x1090ec 3 9 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 104) (.out 0x1090ef (movR64M64Effect 0x1090ef 14 (.sib 4 none 0 (.d32 0x148))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 105) (.exec 0x1090ef (LoadPre 0x1090ef (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x148)) s (0x1090ef + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1090ef 14 (.sib 4 none 0 (.d32 0x148))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 106) (.out 0x1090f7 (pushR64Effect 0x1090f7 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[4, 104]
    (.letOp (n := 107) (.exec 0x1090f7 (PushPre 0x1090f7 2) (pushR64Effect 0x1090f7 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[4, 104]
    (.letOp (n := 108) (.out 0x1090f9 (movR64M64Effect 0x1090f9 3 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[106]
    (.letOp (n := 109) (.exec 0x1090f9 (LoadPre 0x1090f9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x1090f9 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1090f9 3 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[106]
    (.letOp (n := 110) (.out 0x109101 (pushR64Effect 0x109101 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[106, 108]
    (.letOp (n := 111) (.exec 0x109101 (PushPre 0x109101 1) (pushR64Effect 0x109101 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[106, 108]
    (.letOp (n := 112) (.out 0x109102 (callEffect (fun _ => 0x108980) 0x109107) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[110]
    (.letOp (n := 113) (.exec 0x109102 (PushPre 0x109102 5) (callEffect (fun _ => 0x108980) 0x109107) (Reg.operands [.gpr 4] [])) #v[110]
    (.letOp (n := 114) (.const ⟨64, 0x109107⟩) #v[]
    (.terminate (.call ⟨.l108980, RegMap.args [(1, 96), (2, 94), (3, 108), (4, 112), (5, 5), (6, 92), (7, 90), (8, 98), (9, 102), (12, 12), (13, 13), (14, 104), (15, 100), (22, 22), (39, 39), (50, 50), (51, 51)] 115⟩ { target := .l109107, kept := #v[], arity := rfl, guard := some (Fin.last 114) })))))))))))))))))))))))))))))))))

def bytes_l109036_1 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x60, 0x88, 0x44, 0x24, 0x07, 0x48, 0x8D, 0x44, 0x24, 0x07, 0x48, 0x8B,
    0x8C, 0x24, 0x50, 0x01, 0x00, 0x00, 0x88, 0x4C, 0x24, 0x07, 0x48, 0x8D, 0x7C, 0x24, 0x10, 0x48,
    0x8D, 0xB4, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x94, 0x24, 0xF8, 0x00, 0x00, 0x00, 0x4C,
    0x89, 0xF9, 0x49, 0x89, 0xD8, 0x45, 0x89, 0xF7, 0x45, 0x89, 0xF1, 0x4C, 0x8B, 0xB4, 0x24, 0x48,
    0x01, 0x00, 0x00, 0x41, 0x56, 0x48, 0x8B, 0x9C, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x53, 0xE8, 0x79,
    0xF8, 0xFF, 0xFF]

theorem code_l109036_1 : ∀ x ∈ codeRange 0x1090b4 bytes_l109036_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x90b4 83 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109036 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x109036 (movR64M64Effect 0x109036 0 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x109036 (LoadPre 0x109036 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x109036 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109036 0 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x10903b (StorePre 0x10903b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x10903b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10903b 0 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x109043 (movR64M64Effect 0x109043 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x109043 (LoadPre 0x109043 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x109043 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109043 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x109048 (StorePre 0x109048 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x109048 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x109048 0 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x109050 (movR64M64Effect 0x109050 0 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x109050 (LoadPre 0x109050 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x109050 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109050 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x109055 (StorePre 0x109055 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x109055 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x109055 0 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x10905d (movR64M64Effect 0x10905d 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x10905d (LoadPre 0x10905d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10905d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10905d 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x109062 (movR64M64Effect 0x109062 1 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x109062 (LoadPre 0x109062 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x109062 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109062 1 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x109067 (StorePre 0x109067 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x109067 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x109067 1 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x10906f (StorePre 0x10906f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10906f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10906f 0 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x109074 (movR64M64Effect 0x109074 0 (.sib 12 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[12]
    (.letOp (n := 69) (.exec 0x109074 (LoadPre 0x109074 (fun s => AddrMode.addr (.sib 12 none 0 .none) s (0x109074 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109074 0 (.sib 12 none 0 .none)) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 70) (.out 0x109078 (movR64M64Effect 0x109078 1 (.sib 12 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 12] []) (.reg (.gpr 1))) #v[12]
    (.letOp (n := 71) (.exec 0x109078 (LoadPre 0x109078 (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x8)) s (0x109078 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109078 1 (.sib 12 none 0 (.d8 0x8))) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 72) (.exec 0x10907d (StorePre 0x10907d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x10907d + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10907d 0 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[68, 4]
    (.letOp (n := 73) (.exec 0x109085 (StorePre 0x109085 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x109085 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x109085 1 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[70, 4]
    (.letOp (n := 74) (.out 0x10908d (movR64M64Effect 0x10908d 0 (.sib 12 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[12]
    (.letOp (n := 75) (.exec 0x10908d (LoadPre 0x10908d (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x10)) s (0x10908d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10908d 0 (.sib 12 none 0 (.d8 0x10))) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 76) (.exec 0x109092 (StorePre 0x109092 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x109092 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x109092 0 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[74, 4]
    (.letOp (n := 77) (.out 0x10909a (movR64M64Effect 0x10909a 0 (.sib 12 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[12]
    (.letOp (n := 78) (.exec 0x10909a (LoadPre 0x10909a (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x18)) s (0x10909a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10909a 0 (.sib 12 none 0 (.d8 0x18))) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 79) (.exec 0x10909f (StorePre 0x10909f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x10909f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10909f 0 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[77, 4]
    (.letOp (n := 80) (.out 0x1090a7 (movR64M64Effect 0x1090a7 0 (.sib 12 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[12]
    (.letOp (n := 81) (.exec 0x1090a7 (LoadPre 0x1090a7 (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x20)) s (0x1090a7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1090a7 0 (.sib 12 none 0 (.d8 0x20))) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 82) (.exec 0x1090ac (StorePre 0x1090ac 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x1090ac + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1090ac 0 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[80, 4]
    (b_l109036_1))))))))))))))))))))))))))))))

def bytes_l109036 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x30, 0x48, 0x89, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x44,
    0x24, 0x28, 0x48, 0x89, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x20, 0x48,
    0x89, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x10, 0x48, 0x8B, 0x4C, 0x24,
    0x18, 0x48, 0x89, 0x8C, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x78, 0x49, 0x8B,
    0x04, 0x24, 0x49, 0x8B, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x84, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x48,
    0x89, 0x8C, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x49, 0x8B, 0x44, 0x24, 0x10, 0x48, 0x89, 0x84, 0x24,
    0xB8, 0x00, 0x00, 0x00, 0x49, 0x8B, 0x44, 0x24, 0x18, 0x48, 0x89, 0x84, 0x24, 0xC0, 0x00, 0x00,
    0x00, 0x49, 0x8B, 0x44, 0x24, 0x20, 0x48, 0x89, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00] ++ bytes_l109036_1

theorem code_l109036 : ∀ x ∈ codeRange 0x109036 bytes_l109036, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x9036 126 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l109036_1

@[cfg_block] def b_l109107 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x109107 (addR64Imm8Effect 0x109107 4 0x10) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 54) (.exec 0x109107 (fun s => s.RIP = 0x109107) (addR64Imm8Effect 0x109107 4 0x10) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10910b (movR64M64Effect 0x10910b 0 (.sib 4 none 0 (.d32 0x158))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x10910b (LoadPre 0x10910b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x158)) s (0x10910b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10910b 0 (.sib 4 none 0 (.d32 0x158))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 57) (.exec 0x109113 (StorePre 0x109113 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x109113 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109113 4 0 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 53]
    (.letOp (n := 58) (.exec 0x109117 (fun s => s.RIP = 0x109117) (leaR64Effect 0x109117 0 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 59) (.exec 0x10911c (StorePre 0x10911c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x10911c + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x10911c 5 13 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[13, 53]
    (.letOp (n := 60) (.out 0x109121 (movR64R64Effect 0x109121 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[12]
    (.letOp (n := 61) (.exec 0x109121 (fun s => s.RIP = 0x109121) (movR64R64Effect 0x109121 7 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 62) (.out 0x109124 (leaR64Effect 0x109124 6 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[53]
    (.letOp (n := 63) (.exec 0x109124 (fun s => s.RIP = 0x109124) (leaR64Effect 0x109124 6 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 64) (.out 0x10912c (leaR64Effect 0x10912c 2 (.sib 4 none 0 (.d32 0xf8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[53]
    (.letOp (n := 65) (.exec 0x10912c (fun s => s.RIP = 0x10912c) (leaR64Effect 0x10912c 2 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 66) (.out 0x109134 (movR64M64Effect 0x109134 1 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 67) (.exec 0x109134 (LoadPre 0x109134 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109134 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109134 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 68) (.out 0x109139 (movR64M64Effect 0x109139 8 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[53]
    (.letOp (n := 69) (.exec 0x109139 (LoadPre 0x109139 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x109139 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109139 8 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 70) (.out 0x10913e (movR32R32Effect 0x10913e 3 9 15) (EffectPart.reads (.reg (.gpr 9)) [.gpr 15] []) (.reg (.gpr 9))) #v[15]
    (.letOp (n := 71) (.exec 0x10913e (fun s => s.RIP = 0x10913e) (movR32R32Effect 0x10913e 3 9 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 72) (.out 0x109141 (pushR64Effect 0x109141 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[53, 14]
    (.letOp (n := 73) (.exec 0x109141 (PushPre 0x109141 2) (pushR64Effect 0x109141 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 74) (.out 0x109143 (leaR64Effect 0x109143 14 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[72]
    (.letOp (n := 75) (.exec 0x109143 (fun s => s.RIP = 0x109143) (leaR64Effect 0x109143 14 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[72]
    (.letOp (n := 76) (.out 0x109148 (pushR64Effect 0x109148 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[72, 3]
    (.letOp (n := 77) (.exec 0x109148 (PushPre 0x109148 1) (pushR64Effect 0x109148 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[72, 3]
    (.letOp (n := 78) (.out 0x109149 (callEffect (fun _ => 0x108980) 0x10914e) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[76]
    (.letOp (n := 79) (.exec 0x109149 (PushPre 0x109149 5) (callEffect (fun _ => 0x108980) 0x10914e) (Reg.operands [.gpr 4] [])) #v[76]
    (.letOp (n := 80) (.const ⟨64, 0x10914e⟩) #v[]
    (.terminate (.call ⟨.l108980, RegMap.args [(1, 66), (2, 64), (3, 3), (4, 78), (5, 5), (6, 62), (7, 60), (8, 68), (9, 70), (12, 12), (13, 13), (14, 74), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 81⟩ { target := .l10914e, kept := #v[], arity := rfl, guard := some (Fin.last 80) })))))))))))))))))))))))))))))

def bytes_l109107 : List UInt8 :=
  [0x48, 0x83, 0xC4, 0x10, 0x48, 0x8B, 0x84, 0x24, 0x58, 0x01, 0x00, 0x00, 0x88, 0x44, 0x24, 0x07,
    0x48, 0x8D, 0x44, 0x24, 0x07, 0x44, 0x88, 0x6C, 0x24, 0x07, 0x4C, 0x89, 0xE7, 0x48, 0x8D, 0xB4,
    0x24, 0xD0, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x94, 0x24, 0xF8, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x4C,
    0x24, 0x08, 0x4C, 0x8B, 0x44, 0x24, 0x68, 0x45, 0x89, 0xF9, 0x41, 0x56, 0x4C, 0x8D, 0x74, 0x24,
    0x18, 0x53, 0xE8, 0x32, 0xF8, 0xFF, 0xFF]

theorem code_l109107 : ∀ x ∈ codeRange 0x109107 bytes_l109107, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9107 71 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10914e_1 : Block Op Label signature Reg.count 84 :=
  .letOp (n := 84) (.exec 0x1091cb (StorePre 0x1091cb 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x1091cb + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1091cb 0 (.sib 4 none 0 (.d32 0x118))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[82, 53]
    (.letOp (n := 85) (.out 0x1091d3 (movR64M64Effect 0x1091d3 2 (.sib 4 none 0 (.d32 0x160))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[53]
    (.letOp (n := 86) (.exec 0x1091d3 (LoadPre 0x1091d3 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x160)) s (0x1091d3 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1091d3 2 (.sib 4 none 0 (.d32 0x160))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 87) (.out 0x1091db (subR32R32Effect 0x1091db 3 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 15] []) (.reg (.gpr 2))) #v[85, 15]
    (.letOp (n := 88) (.out 0x1091db (subR32R32Effect 0x1091db 3 2 15) (EffectPart.reads (.flag .ZF) [.gpr 2, .gpr 15] []) (.flag .ZF)) #v[85, 15]
    (.letOp (n := 89) (.exec 0x1091db (fun s => s.RIP = 0x1091db) (subR32R32Effect 0x1091db 3 2 15) (Reg.operands [.gpr 2, .gpr 15] [])) #v[85, 15]
    (.letOp (n := 90) (.pure (condOp 4)) #v[88]
    (.terminate (.condBr (Fin.last 90) ⟨.l1093fe, RegMap.args [(0, 82), (1, 72), (2, 87), (3, 3), (4, 53), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (19, 88), (22, 22), (39, 39), (50, 50), (51, 51)] 91⟩ ⟨.l1091e4, RegMap.args [(0, 82), (1, 72), (2, 87), (3, 3), (4, 53), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (19, 88), (22, 22), (39, 39), (50, 50), (51, 51)] 91⟩))))))))

def bytes_l10914e_1 : List UInt8 :=
  [0x48, 0x89, 0x84, 0x24, 0x18, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x94, 0x24, 0x60, 0x01, 0x00, 0x00,
    0x44, 0x29, 0xFA, 0x0F, 0x84, 0x1A, 0x02, 0x00, 0x00]

theorem code_l10914e_1 : ∀ x ∈ codeRange 0x1091cb bytes_l10914e_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x91cb 25 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10914e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10914e (addR64Imm8Effect 0x10914e 4 0x10) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 54) (.exec 0x10914e (fun s => s.RIP = 0x10914e) (addR64Imm8Effect 0x10914e 4 0x10) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x109152 (movR64M64Effect 0x109152 0 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x109152 (LoadPre 0x109152 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x109152 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109152 0 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 57) (.exec 0x109157 (StorePre 0x109157 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x109157 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x109157 0 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 53]
    (.letOp (n := 58) (.out 0x10915f (movR64M64Effect 0x10915f 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 59) (.exec 0x10915f (LoadPre 0x10915f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10915f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10915f 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 60) (.exec 0x109164 (StorePre 0x109164 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x109164 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x109164 0 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[58, 53]
    (.letOp (n := 61) (.out 0x10916c (movR64M64Effect 0x10916c 0 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 62) (.exec 0x10916c (LoadPre 0x10916c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10916c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10916c 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 63) (.exec 0x109171 (StorePre 0x109171 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x109171 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x109171 0 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[61, 53]
    (.letOp (n := 64) (.out 0x109179 (movR64M64Effect 0x109179 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 65) (.exec 0x109179 (LoadPre 0x109179 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x109179 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109179 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 66) (.out 0x10917e (movR64M64Effect 0x10917e 1 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 67) (.exec 0x10917e (LoadPre 0x10917e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10917e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10917e 1 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 68) (.exec 0x109183 (StorePre 0x109183 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x109183 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x109183 1 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[66, 53]
    (.letOp (n := 69) (.exec 0x10918b (StorePre 0x10918b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x10918b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10918b 0 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[64, 53]
    (.letOp (n := 70) (.out 0x109193 (movR64M64Effect 0x109193 0 (.sib 12 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[12]
    (.letOp (n := 71) (.exec 0x109193 (LoadPre 0x109193 (fun s => AddrMode.addr (.sib 12 none 0 .none) s (0x109193 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109193 0 (.sib 12 none 0 .none)) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 72) (.out 0x109197 (movR64M64Effect 0x109197 1 (.sib 12 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 12] []) (.reg (.gpr 1))) #v[12]
    (.letOp (n := 73) (.exec 0x109197 (LoadPre 0x109197 (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x8)) s (0x109197 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109197 1 (.sib 12 none 0 (.d8 0x8))) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 74) (.exec 0x10919c (StorePre 0x10919c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x10919c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10919c 0 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[70, 53]
    (.letOp (n := 75) (.exec 0x1091a4 (StorePre 0x1091a4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x1091a4 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1091a4 1 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[72, 53]
    (.letOp (n := 76) (.out 0x1091ac (movR64M64Effect 0x1091ac 0 (.sib 12 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[12]
    (.letOp (n := 77) (.exec 0x1091ac (LoadPre 0x1091ac (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x10)) s (0x1091ac + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1091ac 0 (.sib 12 none 0 (.d8 0x10))) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 78) (.exec 0x1091b1 (StorePre 0x1091b1 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x1091b1 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1091b1 0 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[76, 53]
    (.letOp (n := 79) (.out 0x1091b9 (movR64M64Effect 0x1091b9 0 (.sib 12 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[12]
    (.letOp (n := 80) (.exec 0x1091b9 (LoadPre 0x1091b9 (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x18)) s (0x1091b9 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1091b9 0 (.sib 12 none 0 (.d8 0x18))) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 81) (.exec 0x1091be (StorePre 0x1091be 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x1091be + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1091be 0 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[79, 53]
    (.letOp (n := 82) (.out 0x1091c6 (movR64M64Effect 0x1091c6 0 (.sib 12 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[12]
    (.letOp (n := 83) (.exec 0x1091c6 (LoadPre 0x1091c6 (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x20)) s (0x1091c6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1091c6 0 (.sib 12 none 0 (.d8 0x20))) (Reg.operands [.gpr 12] [])) #v[12]
    (b_l10914e_1)))))))))))))))))))))))))))))))

def bytes_l10914e : List UInt8 :=
  [0x48, 0x83, 0xC4, 0x10, 0x48, 0x8B, 0x44, 0x24, 0x30, 0x48, 0x89, 0x84, 0x24, 0xF0, 0x00, 0x00,
    0x00, 0x48, 0x8B, 0x44, 0x24, 0x28, 0x48, 0x89, 0x84, 0x24, 0xE8, 0x00, 0x00, 0x00, 0x48, 0x8B,
    0x44, 0x24, 0x20, 0x48, 0x89, 0x84, 0x24, 0xE0, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x10,
    0x48, 0x8B, 0x4C, 0x24, 0x18, 0x48, 0x89, 0x8C, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84,
    0x24, 0xD0, 0x00, 0x00, 0x00, 0x49, 0x8B, 0x04, 0x24, 0x49, 0x8B, 0x4C, 0x24, 0x08, 0x48, 0x89,
    0x84, 0x24, 0xF8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x8C, 0x24, 0x00, 0x01, 0x00, 0x00, 0x49, 0x8B,
    0x44, 0x24, 0x10, 0x48, 0x89, 0x84, 0x24, 0x08, 0x01, 0x00, 0x00, 0x49, 0x8B, 0x44, 0x24, 0x18,
    0x48, 0x89, 0x84, 0x24, 0x10, 0x01, 0x00, 0x00, 0x49, 0x8B, 0x44, 0x24, 0x20] ++ bytes_l10914e_1

theorem code_l10914e : ∀ x ∈ codeRange 0x10914e bytes_l10914e, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x914e 125 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10914e_1

@[cfg_block] def b_l1091e4_1 : Block Op Label signature Reg.count 90 :=
  .letOp (n := 90) (.exec 0x10923b (StorePre 0x10923b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x74)) s (0x10923b + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x10923b 9 (.sib 4 none 0 (.d8 0x74))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[75, 4]
    (.letOp (n := 91) (.pure (condOp 4)) #v[76]
    (.terminate (.condBr (Fin.last 91) ⟨.l108f80, RegMap.args [(0, 83), (1, 87), (2, 78), (3, 3), (4, 4), (5, 5), (6, 85), (9, 75), (14, 14), (19, 76), (22, 22), (39, 39), (50, 50), (51, 51)] 92⟩ ⟨.l109246, RegMap.args [(0, 83), (1, 87), (2, 78), (3, 3), (4, 4), (5, 5), (6, 85), (9, 75), (14, 14), (19, 76), (22, 22), (39, 39), (50, 50), (51, 51)] 92⟩)))

def bytes_l1091e4_1 : List UInt8 :=
  [0x44, 0x89, 0x4C, 0x24, 0x74, 0x0F, 0x84, 0x3A, 0xFD, 0xFF, 0xFF]

theorem code_l1091e4_1 : ∀ x ∈ codeRange 0x10923b bytes_l1091e4_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x923b 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1091e4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1091e4 (movR32R32Effect 0x1091e4 2 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 54) (.exec 0x1091e4 (fun s => s.RIP = 0x1091e4) (movR32R32Effect 0x1091e4 2 0 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 55) (.out 0x1091e6 (notR32Effect 0x1091e6 2 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x1091e6 (fun s => s.RIP = 0x1091e6) (notR32Effect 0x1091e6 2 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x1091e8 (leaR32Effect 0x1091e8 3 1 (.base 2 (.d8 0xc2))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2]
    (.letOp (n := 58) (.exec 0x1091e8 (fun s => s.RIP = 0x1091e8) (leaR32Effect 0x1091e8 3 1 (.base 2 (.d8 0xc2))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 59) (.out 0x1091eb (andR32R32Effect 0x1091eb 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[57, 55]
    (.letOp (n := 60) (.exec 0x1091eb (fun s => s.RIP = 0x1091eb) (andR32R32Effect 0x1091eb 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[57, 55]
    (.letOp (n := 61) (.out 0x1091ed (shrR32Effect 0x1091ed 3 1 31) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[59]
    (.letOp (n := 62) (.exec 0x1091ed (fun s => s.RIP = 0x1091ed) (shrR32Effect 0x1091ed 3 1 31) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[59]
    (.letOp (n := 63) (.exec 0x1091f0 (StorePre 0x1091f0 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1091f0 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1091f0 4 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.out 0x1091f4 (movzxR32M8Effect 0x1091f4 5 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 65) (.exec 0x1091f4 (LoadPre 0x1091f4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1091f4 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1091f4 5 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.out 0x1091f9 (negR32Effect 0x1091f9 2 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[64]
    (.letOp (n := 67) (.exec 0x1091f9 (fun s => s.RIP = 0x1091f9) (negR32Effect 0x1091f9 2 0) (Reg.operands [.gpr 0] [])) #v[64]
    (.letOp (n := 68) (.exec 0x1091fb (StorePre 0x1091fb 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x160)) s (0x1091fb + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1091fb 2 (.sib 4 none 0 (.d32 0x160))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2, 4]
    (.letOp (n := 69) (.out 0x109203 (movR32R32Effect 0x109203 3 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[2]
    (.letOp (n := 70) (.exec 0x109203 (fun s => s.RIP = 0x109203) (movR32R32Effect 0x109203 3 9 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 71) (.out 0x109206 (xorR32Imm8Effect 0x109206 4 9 0x3e) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[69]
    (.letOp (n := 72) (.exec 0x109206 (fun s => s.RIP = 0x109206) (xorR32Imm8Effect 0x109206 4 9 0x3e) (Reg.operands [.gpr 9] [])) #v[69]
    (.letOp (n := 73) (.out 0x10920a (andR32R32Effect 0x10920a 3 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0] []) (.reg (.gpr 9))) #v[71, 66]
    (.letOp (n := 74) (.exec 0x10920a (fun s => s.RIP = 0x10920a) (andR32R32Effect 0x10920a 3 9 0) (Reg.operands [.gpr 9, .gpr 0] [])) #v[71, 66]
    (.letOp (n := 75) (.out 0x10920d (xorR32Imm8Effect 0x10920d 4 9 0x3e) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[73]
    (.letOp (n := 76) (.out 0x10920d (xorR32Imm8Effect 0x10920d 4 9 0x3e) (EffectPart.reads (.flag .ZF) [.gpr 9] []) (.flag .ZF)) #v[73]
    (.letOp (n := 77) (.exec 0x10920d (fun s => s.RIP = 0x10920d) (xorR32Imm8Effect 0x10920d 4 9 0x3e) (Reg.operands [.gpr 9] [])) #v[73]
    (.letOp (n := 78) (.out 0x109211 (movR64M64Effect 0x109211 2 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 79) (.exec 0x109211 (LoadPre 0x109211 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x109211 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109211 2 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 80) (.out 0x109216 (movzxR32M8Effect 0x109216 8 0 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 81) (.exec 0x109216 (LoadPre 0x109216 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x109216 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x109216 8 0 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 82) (.exec 0x10921e (StorePre 0x10921e 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10921e + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10921e 4 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[80, 4]
    (.letOp (n := 83) (.out 0x109222 (movzxR32M8Effect 0x109222 5 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 84) (.exec 0x109222 (LoadPre 0x109222 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x109222 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109222 5 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 85) (.out 0x109227 (movR64M64Effect 0x109227 6 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 86) (.exec 0x109227 (LoadPre 0x109227 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x109227 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x109227 6 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 87) (.out 0x10922f (movzxR32M8Effect 0x10922f 8 1 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 88) (.exec 0x10922f (LoadPre 0x10922f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x10922f + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x10922f 8 1 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 89) (.exec 0x109237 (StorePre 0x109237 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x109237 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109237 4 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[87, 4]
    (b_l1091e4_1)))))))))))))))))))))))))))))))))))))

def bytes_l1091e4 : List UInt8 :=
  [0x89, 0xD0, 0xF7, 0xD0, 0x8D, 0x4A, 0xC2, 0x21, 0xC1, 0xC1, 0xE9, 0x1F, 0x88, 0x4C, 0x24, 0x10,
    0x0F, 0xB6, 0x44, 0x24, 0x10, 0xF7, 0xD8, 0x48, 0x89, 0x94, 0x24, 0x60, 0x01, 0x00, 0x00, 0x41,
    0x89, 0xD1, 0x41, 0x83, 0xF1, 0x3E, 0x41, 0x21, 0xC1, 0x41, 0x83, 0xF1, 0x3E, 0x48, 0x8B, 0x54,
    0x24, 0x78, 0x0F, 0xB6, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00, 0x88, 0x44, 0x24, 0x10, 0x0F, 0xB6,
    0x44, 0x24, 0x10, 0x48, 0x8B, 0xB4, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x0F, 0xB6, 0x8C, 0x24, 0xC8,
    0x00, 0x00, 0x00, 0x88, 0x4C, 0x24, 0x10] ++ bytes_l1091e4_1

theorem code_l1091e4 : ∀ x ∈ codeRange 0x1091e4 bytes_l1091e4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x91e4 87 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1091e4_1

@[cfg_block] def b_l109246_1 : Block Op Label signature Reg.count 92 :=
  .letOp (n := 92) (.exec 0x109295 (fun s => s.RIP = 0x109295) (fun _ => nopEffect 0x109295 11) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l1092a0, RegMap.args [(0, 83), (1, 69), (2, 71), (4, 4), (5, 5), (6, 87), (7, 85), (8, 55), (9, 9), (12, 90), (22, 22), (39, 39), (50, 50), (51, 51)] 93⟩))

def bytes_l109246_1 : List UInt8 :=
  [0x66, 0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem code_l109246_1 : ∀ x ∈ codeRange 0x109295 bytes_l109246_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9295 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109246 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x109246 (movzxR32M8Effect 0x109246 5 1 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x109246 (LoadPre 0x109246 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x109246 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109246 5 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10924b (movR64Imm64Effect 0x10924b 8 0x7fffffffffffffff) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 56) (.exec 0x10924b (fun s => s.RIP = 0x10924b) (movR64Imm64Effect 0x10924b 8 0x7fffffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x109255 (andR64R64Effect 0x109255 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 8] []) (.reg (.gpr 6))) #v[6, 55]
    (.letOp (n := 58) (.exec 0x109255 (fun s => s.RIP = 0x109255) (andR64R64Effect 0x109255 6 8) (Reg.operands [.gpr 6, .gpr 8] [])) #v[6, 55]
    (.letOp (n := 59) (.out 0x109258 (movR64R64Effect 0x109258 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[57]
    (.letOp (n := 60) (.exec 0x109258 (fun s => s.RIP = 0x109258) (movR64R64Effect 0x109258 7 6) (Reg.operands [.gpr 6] [])) #v[57]
    (.letOp (n := 61) (.out 0x10925b (negR64Effect 0x10925b 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[59]
    (.letOp (n := 62) (.exec 0x10925b (fun s => s.RIP = 0x10925b) (negR64Effect 0x10925b 7) (Reg.operands [.gpr 7] [])) #v[59]
    (.letOp (n := 63) (.out 0x10925e (xorR64R64Effect 0x10925e 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[61, 57]
    (.letOp (n := 64) (.exec 0x10925e (fun s => s.RIP = 0x10925e) (xorR64R64Effect 0x10925e 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[61, 57]
    (.letOp (n := 65) (.out 0x109261 (negR64Effect 0x109261 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 66) (.exec 0x109261 (fun s => s.RIP = 0x109261) (negR64Effect 0x109261 1) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 67) (.out 0x109264 (andR64R64Effect 0x109264 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[65, 63]
    (.letOp (n := 68) (.exec 0x109264 (fun s => s.RIP = 0x109264) (andR64R64Effect 0x109264 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[65, 63]
    (.letOp (n := 69) (.out 0x109267 (xorR64R64Effect 0x109267 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[67, 57]
    (.letOp (n := 70) (.exec 0x109267 (fun s => s.RIP = 0x109267) (xorR64R64Effect 0x109267 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[67, 57]
    (.letOp (n := 71) (.out 0x10926a (andR64R64Effect 0x10926a 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 8] []) (.reg (.gpr 2))) #v[2, 55]
    (.letOp (n := 72) (.exec 0x10926a (fun s => s.RIP = 0x10926a) (andR64R64Effect 0x10926a 2 8) (Reg.operands [.gpr 2, .gpr 8] [])) #v[2, 55]
    (.letOp (n := 73) (.out 0x10926d (movR64R64Effect 0x10926d 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[71]
    (.letOp (n := 74) (.exec 0x10926d (fun s => s.RIP = 0x10926d) (movR64R64Effect 0x10926d 6 2) (Reg.operands [.gpr 2] [])) #v[71]
    (.letOp (n := 75) (.out 0x109270 (negR64Effect 0x109270 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[73]
    (.letOp (n := 76) (.exec 0x109270 (fun s => s.RIP = 0x109270) (negR64Effect 0x109270 6) (Reg.operands [.gpr 6] [])) #v[73]
    (.letOp (n := 77) (.out 0x109273 (xorR64R64Effect 0x109273 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[75, 71]
    (.letOp (n := 78) (.exec 0x109273 (fun s => s.RIP = 0x109273) (xorR64R64Effect 0x109273 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[75, 71]
    (.letOp (n := 79) (.out 0x109276 (negR64Effect 0x109276 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 80) (.exec 0x109276 (fun s => s.RIP = 0x109276) (negR64Effect 0x109276 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 81) (.out 0x109279 (andR64R64Effect 0x109279 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[79, 77]
    (.letOp (n := 82) (.exec 0x109279 (fun s => s.RIP = 0x109279) (andR64R64Effect 0x109279 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[79, 77]
    (.letOp (n := 83) (.out 0x10927c (xorR64R64Effect 0x10927c 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[81, 71]
    (.letOp (n := 84) (.exec 0x10927c (fun s => s.RIP = 0x10927c) (xorR64R64Effect 0x10927c 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[81, 71]
    (.letOp (n := 85) (.out 0x10927f (movR32Imm32Effect 0x10927f 5 7 0x1) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 86) (.exec 0x10927f (fun s => s.RIP = 0x10927f) (movR32Imm32Effect 0x10927f 5 7 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 87) (.out 0x109284 (xorR32R32Effect 0x109284 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[77, 77]
    (.letOp (n := 88) (.exec 0x109284 (fun s => s.RIP = 0x109284) (xorR32R32Effect 0x109284 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[77, 77]
    (.letOp (n := 89) (.exec 0x109286 (StorePre 0x109286 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109286 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x109286 (.sib 4 none 0 (.d8 0x8)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 90) (.out 0x10928f (movR32Imm32Effect 0x10928f 6 12 0x1) (EffectPart.reads (.reg (.gpr 12)) [] []) (.reg (.gpr 12))) #v[]
    (.letOp (n := 91) (.exec 0x10928f (fun s => s.RIP = 0x10928f) (movR32Imm32Effect 0x10928f 6 12 0x1) (Reg.operands [] [])) #v[]
    (b_l109246_1)))))))))))))))))))))))))))))))))))))))

def bytes_l109246 : List UInt8 :=
  [0x0F, 0xB6, 0x4C, 0x24, 0x10, 0x49, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F, 0x4C,
    0x21, 0xC6, 0x48, 0x89, 0xF7, 0x48, 0xF7, 0xDF, 0x48, 0x31, 0xF7, 0x48, 0xF7, 0xD9, 0x48, 0x21,
    0xF9, 0x48, 0x31, 0xF1, 0x4C, 0x21, 0xC2, 0x48, 0x89, 0xD6, 0x48, 0xF7, 0xDE, 0x48, 0x31, 0xD6,
    0x48, 0xF7, 0xD8, 0x48, 0x21, 0xF0, 0x48, 0x31, 0xD0, 0xBF, 0x01, 0x00, 0x00, 0x00, 0x31, 0xF6,
    0x48, 0xC7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00, 0x41, 0xBC, 0x01, 0x00, 0x00, 0x00] ++ bytes_l109246_1

theorem code_l109246 : ∀ x ∈ codeRange 0x109246 bytes_l109246, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x9246 79 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l109246_1

@[cfg_block] def b_l1092a0_4 : Block Op Label signature Reg.count 204 :=
  .letOp (n := 204) (.exec 0x1093cf (StorePre 0x1093cf 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1093cf + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1093cf 5 8 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 205) (.out 0x1093d4 (movR64R64Effect 0x1093d4 14 9) (EffectPart.reads (.reg (.gpr 14)) [.gpr 9] []) (.reg (.gpr 14))) #v[184]
    (.letOp (n := 206) (.exec 0x1093d4 (fun s => s.RIP = 0x1093d4) (movR64R64Effect 0x1093d4 14 9) (Reg.operands [.gpr 9] [])) #v[184]
    (.letOp (n := 207) (.out 0x1093d7 (movzxR32M8Effect 0x1093d7 5 6 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 208) (.exec 0x1093d7 (LoadPre 0x1093d7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1093d7 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1093d7 5 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 209) (.out 0x1093dc (negR64Effect 0x1093dc 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[207]
    (.letOp (n := 210) (.exec 0x1093dc (fun s => s.RIP = 0x1093dc) (negR64Effect 0x1093dc 6) (Reg.operands [.gpr 6] [])) #v[207]
    (.letOp (n := 211) (.out 0x1093df (andR64R64Effect 0x1093df 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[209, 196]
    (.letOp (n := 212) (.exec 0x1093df (fun s => s.RIP = 0x1093df) (andR64R64Effect 0x1093df 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[209, 196]
    (.letOp (n := 213) (.out 0x1093e2 (movR32M32Effect 0x1093e2 9 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 214) (.exec 0x1093e2 (LoadPre 0x1093e2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1093e2 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x1093e2 9 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 215) (.out 0x1093e7 (addR64R64Effect 0x1093e7 12 6) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 6] []) (.reg (.gpr 12))) #v[149, 211]
    (.letOp (n := 216) (.exec 0x1093e7 (fun s => s.RIP = 0x1093e7) (addR64R64Effect 0x1093e7 12 6) (Reg.operands [.gpr 12, .gpr 6] [])) #v[149, 211]
    (.letOp (n := 217) (.out 0x1093ea (movR64R64Effect 0x1093ea 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[200]
    (.letOp (n := 218) (.exec 0x1093ea (fun s => s.RIP = 0x1093ea) (movR64R64Effect 0x1093ea 7 15) (Reg.operands [.gpr 15] [])) #v[200]
    (.letOp (n := 219) (.out 0x1093ed (movR64R64Effect 0x1093ed 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[202]
    (.letOp (n := 220) (.exec 0x1093ed (fun s => s.RIP = 0x1093ed) (movR64R64Effect 0x1093ed 6 3) (Reg.operands [.gpr 3] [])) #v[202]
    (.letOp (n := 221) (.out 0x1093f0 (decR32Effect 0x1093f0 3 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[213]
    (.letOp (n := 222) (.out 0x1093f0 (decR32Effect 0x1093f0 3 9) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.flag .ZF)) #v[213]
    (.letOp (n := 223) (.exec 0x1093f0 (fun s => s.RIP = 0x1093f0) (decR32Effect 0x1093f0 3 9) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[213]
    (.letOp (n := 224) (.pure (condOp 5)) #v[222]
    (.terminate (.condBr (Fin.last 224) ⟨.l1092a0, RegMap.args [(0, 125), (1, 198), (2, 196), (3, 202), (4, 4), (5, 111), (6, 219), (7, 217), (8, 65), (9, 221), (10, 163), (11, 151), (12, 215), (13, 139), (14, 205), (15, 200), (19, 222), (22, 22), (39, 39), (50, 50), (51, 51)] 225⟩ ⟨.l1093f9, RegMap.args [(0, 125), (1, 198), (2, 196), (3, 202), (4, 4), (5, 111), (6, 219), (7, 217), (8, 65), (9, 221), (10, 163), (11, 151), (12, 215), (13, 139), (14, 205), (15, 200), (19, 222), (22, 22), (39, 39), (50, 50), (51, 51)] 225⟩))))))))))))))))))))))

def bytes_l1092a0_4 : List UInt8 :=
  [0x44, 0x88, 0x44, 0x24, 0x10, 0x4D, 0x89, 0xCE, 0x0F, 0xB6, 0x74, 0x24, 0x10, 0x48, 0xF7, 0xDE,
    0x48, 0x21, 0xD6, 0x44, 0x8B, 0x4C, 0x24, 0x60, 0x49, 0x01, 0xF4, 0x4C, 0x89, 0xFF, 0x48, 0x89,
    0xDE, 0x41, 0xFF, 0xC9, 0x0F, 0x85, 0xA7, 0xFE, 0xFF, 0xFF]

theorem code_l1092a0_4 : ∀ x ∈ codeRange 0x1093cf bytes_l1092a0_4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x93cf 42 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1092a0_3 : Block Op Label signature Reg.count 165 :=
  .letOp (n := 165) (.out 0x10938d (xorR64R64Effect 0x10938d 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 7] []) (.reg (.gpr 2))) #v[161, 7]
    (.letOp (n := 166) (.exec 0x10938d (fun s => s.RIP = 0x10938d) (xorR64R64Effect 0x10938d 2 7) (Reg.operands [.gpr 2, .gpr 7] [])) #v[161, 7]
    (.letOp (n := 167) (.out 0x109390 (andR64R64Effect 0x109390 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 10] []) (.reg (.gpr 2))) #v[165, 163]
    (.letOp (n := 168) (.exec 0x109390 (fun s => s.RIP = 0x109390) (andR64R64Effect 0x109390 2 10) (Reg.operands [.gpr 2, .gpr 10] [])) #v[165, 163]
    (.letOp (n := 169) (.out 0x109393 (xorR64R64Effect 0x109393 15 7) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 7] []) (.reg (.gpr 15))) #v[147, 7]
    (.letOp (n := 170) (.exec 0x109393 (fun s => s.RIP = 0x109393) (xorR64R64Effect 0x109393 15 7) (Reg.operands [.gpr 15, .gpr 7] [])) #v[147, 7]
    (.letOp (n := 171) (.out 0x109396 (xorR64R64Effect 0x109396 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 7] []) (.reg (.gpr 2))) #v[167, 7]
    (.letOp (n := 172) (.exec 0x109396 (fun s => s.RIP = 0x109396) (xorR64R64Effect 0x109396 2 7) (Reg.operands [.gpr 2, .gpr 7] [])) #v[167, 7]
    (.letOp (n := 173) (.out 0x109399 (negR64Effect 0x109399 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[94]
    (.letOp (n := 174) (.exec 0x109399 (fun s => s.RIP = 0x109399) (negR64Effect 0x109399 9) (Reg.operands [.gpr 9] [])) #v[94]
    (.letOp (n := 175) (.out 0x10939c (andR64R64Effect 0x10939c 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2] []) (.reg (.gpr 9))) #v[173, 171]
    (.letOp (n := 176) (.exec 0x10939c (fun s => s.RIP = 0x10939c) (andR64R64Effect 0x10939c 9 2) (Reg.operands [.gpr 9, .gpr 2] [])) #v[173, 171]
    (.letOp (n := 177) (.out 0x10939f (addR64R64Effect 0x10939f 14 9) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 9] []) (.reg (.gpr 14))) #v[141, 175]
    (.letOp (n := 178) (.exec 0x10939f (fun s => s.RIP = 0x10939f) (addR64R64Effect 0x10939f 14 9) (Reg.operands [.gpr 14, .gpr 9] [])) #v[141, 175]
    (.letOp (n := 179) (.exec 0x1093a2 (StorePre 0x1093a2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1093a2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1093a2 14 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[177, 4]
    (.letOp (n := 180) (.out 0x1093a7 (movR64R64Effect 0x1093a7 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6] []) (.reg (.gpr 2))) #v[6]
    (.letOp (n := 181) (.exec 0x1093a7 (fun s => s.RIP = 0x1093a7) (movR64R64Effect 0x1093a7 2 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 182) (.out 0x1093aa (negR64Effect 0x1093aa 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[180]
    (.letOp (n := 183) (.exec 0x1093aa (fun s => s.RIP = 0x1093aa) (negR64Effect 0x1093aa 2) (Reg.operands [.gpr 2] [])) #v[180]
    (.letOp (n := 184) (.out 0x1093ad (leaR64Effect 0x1093ad 9 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 185) (.exec 0x1093ad (fun s => s.RIP = 0x1093ad) (leaR64Effect 0x1093ad 9 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 186) (.out 0x1093b2 (movzxR32M8Effect 0x1093b2 5 7 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 187) (.exec 0x1093b2 (LoadPre 0x1093b2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1093b2 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1093b2 5 7 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 188) (.out 0x1093b7 (negR64Effect 0x1093b7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[186]
    (.letOp (n := 189) (.exec 0x1093b7 (fun s => s.RIP = 0x1093b7) (negR64Effect 0x1093b7 7) (Reg.operands [.gpr 7] [])) #v[186]
    (.letOp (n := 190) (.out 0x1093ba (xorR64R64Effect 0x1093ba 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[182, 6]
    (.letOp (n := 191) (.exec 0x1093ba (fun s => s.RIP = 0x1093ba) (xorR64R64Effect 0x1093ba 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[182, 6]
    (.letOp (n := 192) (.out 0x1093bd (andR64R64Effect 0x1093bd 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 7] []) (.reg (.gpr 2))) #v[190, 188]
    (.letOp (n := 193) (.exec 0x1093bd (fun s => s.RIP = 0x1093bd) (andR64R64Effect 0x1093bd 2 7) (Reg.operands [.gpr 2, .gpr 7] [])) #v[190, 188]
    (.letOp (n := 194) (.out 0x1093c0 (xorR64R64Effect 0x1093c0 3 6) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 6] []) (.reg (.gpr 3))) #v[157, 6]
    (.letOp (n := 195) (.exec 0x1093c0 (fun s => s.RIP = 0x1093c0) (xorR64R64Effect 0x1093c0 3 6) (Reg.operands [.gpr 3, .gpr 6] [])) #v[157, 6]
    (.letOp (n := 196) (.out 0x1093c3 (xorR64R64Effect 0x1093c3 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[192, 6]
    (.letOp (n := 197) (.exec 0x1093c3 (fun s => s.RIP = 0x1093c3) (xorR64R64Effect 0x1093c3 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[192, 6]
    (.letOp (n := 198) (.out 0x1093c6 (sarR64Effect 0x1093c6 3 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[137]
    (.letOp (n := 199) (.exec 0x1093c6 (fun s => s.RIP = 0x1093c6) (sarR64Effect 0x1093c6 3 1 1) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[137]
    (.letOp (n := 200) (.out 0x1093c9 (addR64R64Effect 0x1093c9 15 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 15] []) (.reg (.gpr 15))) #v[169, 169]
    (.letOp (n := 201) (.exec 0x1093c9 (fun s => s.RIP = 0x1093c9) (addR64R64Effect 0x1093c9 15 15) (Reg.operands [.gpr 15, .gpr 15] [])) #v[169, 169]
    (.letOp (n := 202) (.out 0x1093cc (addR64R64Effect 0x1093cc 3 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 3] []) (.reg (.gpr 3))) #v[194, 194]
    (.letOp (n := 203) (.exec 0x1093cc (fun s => s.RIP = 0x1093cc) (addR64R64Effect 0x1093cc 3 3) (Reg.operands [.gpr 3, .gpr 3] [])) #v[194, 194]
    (b_l1092a0_4)))))))))))))))))))))))))))))))))))))))

def bytes_l1092a0_3 : List UInt8 :=
  [0x48, 0x31, 0xFA, 0x4C, 0x21, 0xD2, 0x49, 0x31, 0xFF, 0x48, 0x31, 0xFA, 0x49, 0xF7, 0xD9, 0x49,
    0x21, 0xD1, 0x4D, 0x01, 0xCE, 0x4C, 0x89, 0x74, 0x24, 0x08, 0x48, 0x89, 0xF2, 0x48, 0xF7, 0xDA,
    0x4C, 0x8D, 0x4C, 0x24, 0x10, 0x0F, 0xB6, 0x7C, 0x24, 0x10, 0x48, 0xF7, 0xDF, 0x48, 0x31, 0xF2,
    0x48, 0x21, 0xFA, 0x48, 0x31, 0xF3, 0x48, 0x31, 0xF2, 0x48, 0xD1, 0xF9, 0x4D, 0x01, 0xFF, 0x48,
    0x01, 0xDB] ++ bytes_l1092a0_4

theorem code_l1092a0_3 : ∀ x ∈ codeRange 0x10938d bytes_l1092a0_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x938d 66 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1092a0_4

@[cfg_block] def b_l1092a0_2 : Block Op Label signature Reg.count 125 :=
  .letOp (n := 125) (.out 0x10934c (xorR64R64Effect 0x10934c 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[119, 109]
    (.letOp (n := 126) (.exec 0x10934c (fun s => s.RIP = 0x10934c) (xorR64R64Effect 0x10934c 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[119, 109]
    (.letOp (n := 127) (.out 0x10934f (leaR64Effect 0x10934f 2 (.sib 3 (some 1) 0 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3, .gpr 1] []) (.reg (.gpr 2))) #v[123, 1]
    (.letOp (n := 128) (.exec 0x10934f (fun s => s.RIP = 0x10934f) (leaR64Effect 0x10934f 2 (.sib 3 (some 1) 0 .none)) (Reg.operands [.gpr 3, .gpr 1] [])) #v[123, 1]
    (.letOp (n := 129) (.out 0x109353 (subR64R64Effect 0x109353 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 3] []) (.reg (.gpr 1))) #v[1, 123]
    (.letOp (n := 130) (.exec 0x109353 (fun s => s.RIP = 0x109353) (subR64R64Effect 0x109353 1 3) (Reg.operands [.gpr 1, .gpr 3] [])) #v[1, 123]
    (.letOp (n := 131) (.out 0x109356 (negR64Effect 0x109356 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15] []) (.reg (.gpr 15))) #v[82]
    (.letOp (n := 132) (.exec 0x109356 (fun s => s.RIP = 0x109356) (negR64Effect 0x109356 15) (Reg.operands [.gpr 15] [])) #v[82]
    (.letOp (n := 133) (.out 0x109359 (xorR64R64Effect 0x109359 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[129, 127]
    (.letOp (n := 134) (.exec 0x109359 (fun s => s.RIP = 0x109359) (xorR64R64Effect 0x109359 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[129, 127]
    (.letOp (n := 135) (.out 0x10935c (andR64R64Effect 0x10935c 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 15] []) (.reg (.gpr 1))) #v[133, 131]
    (.letOp (n := 136) (.exec 0x10935c (fun s => s.RIP = 0x10935c) (andR64R64Effect 0x10935c 1 15) (Reg.operands [.gpr 1, .gpr 15] [])) #v[133, 131]
    (.letOp (n := 137) (.out 0x10935f (xorR64R64Effect 0x10935f 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[135, 127]
    (.letOp (n := 138) (.exec 0x10935f (fun s => s.RIP = 0x10935f) (xorR64R64Effect 0x10935f 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[135, 127]
    (.letOp (n := 139) (.out 0x109362 (negR64Effect 0x109362 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[85]
    (.letOp (n := 140) (.exec 0x109362 (fun s => s.RIP = 0x109362) (negR64Effect 0x109362 13) (Reg.operands [.gpr 13] [])) #v[85]
    (.letOp (n := 141) (.out 0x109365 (movR64M64Effect 0x109365 14 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 142) (.exec 0x109365 (LoadPre 0x109365 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109365 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109365 14 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 143) (.out 0x10936a (movR64R64Effect 0x10936a 15 14) (EffectPart.reads (.reg (.gpr 15)) [.gpr 14] []) (.reg (.gpr 15))) #v[141]
    (.letOp (n := 144) (.exec 0x10936a (fun s => s.RIP = 0x10936a) (movR64R64Effect 0x10936a 15 14) (Reg.operands [.gpr 14] [])) #v[141]
    (.letOp (n := 145) (.out 0x10936d (xorR64R64Effect 0x10936d 15 7) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 7] []) (.reg (.gpr 15))) #v[143, 7]
    (.letOp (n := 146) (.exec 0x10936d (fun s => s.RIP = 0x10936d) (xorR64R64Effect 0x10936d 15 7) (Reg.operands [.gpr 15, .gpr 7] [])) #v[143, 7]
    (.letOp (n := 147) (.out 0x109370 (andR64R64Effect 0x109370 15 13) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 13] []) (.reg (.gpr 15))) #v[145, 139]
    (.letOp (n := 148) (.exec 0x109370 (fun s => s.RIP = 0x109370) (andR64R64Effect 0x109370 15 13) (Reg.operands [.gpr 15, .gpr 13] [])) #v[145, 139]
    (.letOp (n := 149) (.out 0x109373 (movR64M64Effect 0x109373 12 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 150) (.exec 0x109373 (LoadPre 0x109373 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x109373 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109373 12 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 151) (.out 0x109378 (negR64Effect 0x109378 11) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11] []) (.reg (.gpr 11))) #v[88]
    (.letOp (n := 152) (.exec 0x109378 (fun s => s.RIP = 0x109378) (negR64Effect 0x109378 11) (Reg.operands [.gpr 11] [])) #v[88]
    (.letOp (n := 153) (.out 0x10937b (movR64R64Effect 0x10937b 3 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 12] []) (.reg (.gpr 3))) #v[149]
    (.letOp (n := 154) (.exec 0x10937b (fun s => s.RIP = 0x10937b) (movR64R64Effect 0x10937b 3 12) (Reg.operands [.gpr 12] [])) #v[149]
    (.letOp (n := 155) (.out 0x10937e (xorR64R64Effect 0x10937e 3 6) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 6] []) (.reg (.gpr 3))) #v[153, 6]
    (.letOp (n := 156) (.exec 0x10937e (fun s => s.RIP = 0x10937e) (xorR64R64Effect 0x10937e 3 6) (Reg.operands [.gpr 3, .gpr 6] [])) #v[153, 6]
    (.letOp (n := 157) (.out 0x109381 (andR64R64Effect 0x109381 3 11) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 11] []) (.reg (.gpr 3))) #v[155, 151]
    (.letOp (n := 158) (.exec 0x109381 (fun s => s.RIP = 0x109381) (andR64R64Effect 0x109381 3 11) (Reg.operands [.gpr 3, .gpr 11] [])) #v[155, 151]
    (.letOp (n := 159) (.out 0x109384 (movR64R64Effect 0x109384 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7] []) (.reg (.gpr 2))) #v[7]
    (.letOp (n := 160) (.exec 0x109384 (fun s => s.RIP = 0x109384) (movR64R64Effect 0x109384 2 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 161) (.out 0x109387 (negR64Effect 0x109387 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[159]
    (.letOp (n := 162) (.exec 0x109387 (fun s => s.RIP = 0x109387) (negR64Effect 0x109387 2) (Reg.operands [.gpr 2] [])) #v[159]
    (.letOp (n := 163) (.out 0x10938a (negR64Effect 0x10938a 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[91]
    (.letOp (n := 164) (.exec 0x10938a (fun s => s.RIP = 0x10938a) (negR64Effect 0x10938a 10) (Reg.operands [.gpr 10] [])) #v[91]
    (b_l1092a0_3))))))))))))))))))))))))))))))))))))))))

def bytes_l1092a0_2 : List UInt8 :=
  [0x4C, 0x31, 0xF0, 0x48, 0x8D, 0x14, 0x0B, 0x48, 0x29, 0xD9, 0x49, 0xF7, 0xDF, 0x48, 0x31, 0xD1,
    0x4C, 0x21, 0xF9, 0x48, 0x31, 0xD1, 0x49, 0xF7, 0xDD, 0x4C, 0x8B, 0x74, 0x24, 0x08, 0x4D, 0x89,
    0xF7, 0x49, 0x31, 0xFF, 0x4D, 0x21, 0xEF, 0x4C, 0x8B, 0x64, 0x24, 0x68, 0x49, 0xF7, 0xDB, 0x4C,
    0x89, 0xE3, 0x48, 0x31, 0xF3, 0x4C, 0x21, 0xDB, 0x48, 0x89, 0xFA, 0x48, 0xF7, 0xDA, 0x49, 0xF7,
    0xDA] ++ bytes_l1092a0_3

theorem code_l1092a0_2 : ∀ x ∈ codeRange 0x10934c bytes_l1092a0_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x934c 65 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1092a0_3

@[cfg_block] def b_l1092a0_1 : Block Op Label signature Reg.count 88 :=
  .letOp (n := 88) (.out 0x1092fe (movzxR32M8Effect 0x1092fe 6 11 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 89) (.exec 0x1092fe (LoadPre 0x1092fe (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1092fe + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1092fe 6 11 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 90) (.exec 0x109304 (StorePre 0x109304 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x109304 + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 15) (setccM8Effect 0x109304 5 (.sib 4 none 0 (.d8 0x10)))) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.ZF, .SF, .OF])) #v[4, 67, 68, 69]
    (.letOp (n := 91) (.out 0x109309 (movzxR32M8Effect 0x109309 6 10 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 92) (.exec 0x109309 (LoadPre 0x109309 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x109309 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x109309 6 10 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 93) (.exec 0x10930f (StorePre 0x10930f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10930f + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x10930f 5 8 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 94) (.out 0x109314 (movzxR32M8Effect 0x109314 6 9 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 95) (.exec 0x109314 (LoadPre 0x109314 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x109314 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x109314 6 9 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 96) (.exec 0x10931a (StorePre 0x10931a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10931a + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 15) (setccM8Effect 0x10931a 5 (.sib 4 none 0 (.d8 0x10)))) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.ZF, .SF, .OF])) #v[4, 67, 68, 69]
    (.letOp (n := 97) (.out 0x10931f (movR32Imm32Effect 0x10931f 5 2 0x2) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 98) (.exec 0x10931f (fun s => s.RIP = 0x10931f) (movR32Imm32Effect 0x10931f 5 2 0x2) (Reg.operands [] [])) #v[]
    (.letOp (n := 99) (.out 0x109324 (subR64R64Effect 0x109324 2 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 5] []) (.reg (.gpr 2))) #v[97, 5]
    (.letOp (n := 100) (.exec 0x109324 (fun s => s.RIP = 0x109324) (subR64R64Effect 0x109324 2 5) (Reg.operands [.gpr 2, .gpr 5] [])) #v[97, 5]
    (.letOp (n := 101) (.out 0x109327 (addR64Imm8Effect 0x109327 5 0x2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5] []) (.reg (.gpr 5))) #v[5]
    (.letOp (n := 102) (.exec 0x109327 (fun s => s.RIP = 0x109327) (addR64Imm8Effect 0x109327 5 0x2) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 103) (.out 0x10932b (negR64Effect 0x10932b 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14] []) (.reg (.gpr 14))) #v[75]
    (.letOp (n := 104) (.exec 0x10932b (fun s => s.RIP = 0x10932b) (negR64Effect 0x10932b 14) (Reg.operands [.gpr 14] [])) #v[75]
    (.letOp (n := 105) (.out 0x10932e (xorR64R64Effect 0x10932e 2 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 5] []) (.reg (.gpr 2))) #v[99, 101]
    (.letOp (n := 106) (.exec 0x10932e (fun s => s.RIP = 0x10932e) (xorR64R64Effect 0x10932e 2 5) (Reg.operands [.gpr 2, .gpr 5] [])) #v[99, 101]
    (.letOp (n := 107) (.out 0x109331 (andR64R64Effect 0x109331 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 14] []) (.reg (.gpr 2))) #v[105, 103]
    (.letOp (n := 108) (.exec 0x109331 (fun s => s.RIP = 0x109331) (andR64R64Effect 0x109331 2 14) (Reg.operands [.gpr 2, .gpr 14] [])) #v[105, 103]
    (.letOp (n := 109) (.out 0x109334 (movR64R64Effect 0x109334 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[0]
    (.letOp (n := 110) (.exec 0x109334 (fun s => s.RIP = 0x109334) (movR64R64Effect 0x109334 14 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 111) (.out 0x109337 (xorR64R64Effect 0x109337 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 2] []) (.reg (.gpr 5))) #v[101, 107]
    (.letOp (n := 112) (.exec 0x109337 (fun s => s.RIP = 0x109337) (xorR64R64Effect 0x109337 5 2) (Reg.operands [.gpr 5, .gpr 2] [])) #v[101, 107]
    (.letOp (n := 113) (.out 0x10933a (negR64Effect 0x10933a 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[79]
    (.letOp (n := 114) (.exec 0x10933a (fun s => s.RIP = 0x10933a) (negR64Effect 0x10933a 12) (Reg.operands [.gpr 12] [])) #v[79]
    (.letOp (n := 115) (.out 0x10933d (movR64R64Effect 0x10933d 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[1]
    (.letOp (n := 116) (.exec 0x10933d (fun s => s.RIP = 0x10933d) (movR64R64Effect 0x10933d 0 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 117) (.out 0x109340 (xorR64R64Effect 0x109340 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[115, 109]
    (.letOp (n := 118) (.exec 0x109340 (fun s => s.RIP = 0x109340) (xorR64R64Effect 0x109340 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[115, 109]
    (.letOp (n := 119) (.out 0x109343 (andR64R64Effect 0x109343 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 12] []) (.reg (.gpr 0))) #v[117, 113]
    (.letOp (n := 120) (.exec 0x109343 (fun s => s.RIP = 0x109343) (andR64R64Effect 0x109343 0 12) (Reg.operands [.gpr 0, .gpr 12] [])) #v[117, 113]
    (.letOp (n := 121) (.out 0x109346 (negR64Effect 0x109346 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[72]
    (.letOp (n := 122) (.exec 0x109346 (fun s => s.RIP = 0x109346) (negR64Effect 0x109346 3) (Reg.operands [.gpr 3] [])) #v[72]
    (.letOp (n := 123) (.out 0x109349 (andR64R64Effect 0x109349 3 14) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 14] []) (.reg (.gpr 3))) #v[121, 109]
    (.letOp (n := 124) (.exec 0x109349 (fun s => s.RIP = 0x109349) (andR64R64Effect 0x109349 3 14) (Reg.operands [.gpr 3, .gpr 14] [])) #v[121, 109]
    (b_l1092a0_2)))))))))))))))))))))))))))))))))))))

def bytes_l1092a0_1 : List UInt8 :=
  [0x44, 0x0F, 0xB6, 0x5C, 0x24, 0x10, 0x0F, 0x9F, 0x44, 0x24, 0x10, 0x44, 0x0F, 0xB6, 0x54, 0x24,
    0x10, 0x44, 0x88, 0x44, 0x24, 0x10, 0x44, 0x0F, 0xB6, 0x4C, 0x24, 0x10, 0x0F, 0x9F, 0x44, 0x24,
    0x10, 0xBA, 0x02, 0x00, 0x00, 0x00, 0x48, 0x29, 0xEA, 0x48, 0x83, 0xC5, 0x02, 0x49, 0xF7, 0xDE,
    0x48, 0x31, 0xEA, 0x4C, 0x21, 0xF2, 0x49, 0x89, 0xC6, 0x48, 0x31, 0xD5, 0x49, 0xF7, 0xDC, 0x48,
    0x89, 0xC8, 0x4C, 0x31, 0xF0, 0x4C, 0x21, 0xE0, 0x48, 0xF7, 0xDB, 0x4C, 0x21, 0xF3] ++ bytes_l1092a0_2

theorem code_l1092a0_1 : ∀ x ∈ codeRange 0x1092fe bytes_l1092a0_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x92fe 78 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1092a0_2

@[cfg_block] def b_l1092a0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1092a0 (StorePre 0x1092a0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1092a0 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x1092a0 9 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[9, 4]
    (.letOp (n := 54) (.exec 0x1092a5 (StorePre 0x1092a5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x1092a5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1092a5 12 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[12, 4]
    (.letOp (n := 55) (.out 0x1092aa (testR64R64Effect 0x1092aa 5 5) (EffectPart.reads (.flag .ZF) [.gpr 5, .gpr 5] []) (.flag .ZF)) #v[5, 5]
    (.letOp (n := 56) (.out 0x1092aa (testR64R64Effect 0x1092aa 5 5) (EffectPart.reads (.flag .SF) [.gpr 5, .gpr 5] []) (.flag .SF)) #v[5, 5]
    (.letOp (n := 57) (.out 0x1092aa (testR64R64Effect 0x1092aa 5 5) (EffectPart.reads (.flag .OF) [.gpr 5, .gpr 5] []) (.flag .OF)) #v[5, 5]
    (.letOp (n := 58) (.exec 0x1092aa (fun s => s.RIP = 0x1092aa) (testR64R64Effect 0x1092aa 5 5) (Reg.operands [.gpr 5, .gpr 5] [])) #v[5, 5]
    (.letOp (n := 59) (.out 0x1092ad (atFlags (condHolds 15) (setccR8Effect 0x1092ad 4 9)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF, .SF, .OF]) (.reg (.gpr 9))) #v[9, 55, 56, 57]
    (.letOp (n := 60) (.exec 0x1092ad (fun s => s.RIP = 0x1092ad) (atFlags (condHolds 15) (setccR8Effect 0x1092ad 4 9)) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF, .SF, .OF])) #v[9, 55, 56, 57]
    (.letOp (n := 61) (.out 0x1092b1 (andR8R8Effect 0x1092b1 3 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1] []) (.reg (.gpr 9))) #v[59, 1]
    (.letOp (n := 62) (.exec 0x1092b1 (fun s => s.RIP = 0x1092b1) (andR8R8Effect 0x1092b1 3 9 1) (Reg.operands [.gpr 9, .gpr 1] [])) #v[59, 1]
    (.letOp (n := 63) (.out 0x1092b4 (movR32R32Effect 0x1092b4 3 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 1] []) (.reg (.gpr 8))) #v[1]
    (.letOp (n := 64) (.exec 0x1092b4 (fun s => s.RIP = 0x1092b4) (movR32R32Effect 0x1092b4 3 8 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 65) (.out 0x1092b7 (andR8Imm8Effect 0x1092b7 4 8 0x1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[63]
    (.letOp (n := 66) (.exec 0x1092b7 (fun s => s.RIP = 0x1092b7) (andR8Imm8Effect 0x1092b7 4 8 0x1) (Reg.operands [.gpr 8] [])) #v[63]
    (.letOp (n := 67) (.out 0x1092bb (testR64R64Effect 0x1092bb 5 5) (EffectPart.reads (.flag .ZF) [.gpr 5, .gpr 5] []) (.flag .ZF)) #v[5, 5]
    (.letOp (n := 68) (.out 0x1092bb (testR64R64Effect 0x1092bb 5 5) (EffectPart.reads (.flag .SF) [.gpr 5, .gpr 5] []) (.flag .SF)) #v[5, 5]
    (.letOp (n := 69) (.out 0x1092bb (testR64R64Effect 0x1092bb 5 5) (EffectPart.reads (.flag .OF) [.gpr 5, .gpr 5] []) (.flag .OF)) #v[5, 5]
    (.letOp (n := 70) (.exec 0x1092bb (fun s => s.RIP = 0x1092bb) (testR64R64Effect 0x1092bb 5 5) (Reg.operands [.gpr 5, .gpr 5] [])) #v[5, 5]
    (.letOp (n := 71) (.exec 0x1092be (StorePre 0x1092be 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1092be + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1092be 5 8 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 72) (.out 0x1092c3 (movzxR32M8Effect 0x1092c3 5 3 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 73) (.exec 0x1092c3 (LoadPre 0x1092c3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1092c3 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1092c3 5 3 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.exec 0x1092c8 (StorePre 0x1092c8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1092c8 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1092c8 5 9 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 75) (.out 0x1092cd (movzxR32M8Effect 0x1092cd 6 14 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 76) (.exec 0x1092cd (LoadPre 0x1092cd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1092cd + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1092cd 6 14 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 77) (.exec 0x1092d3 (StorePre 0x1092d3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1092d3 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1092d3 5 9 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 78) (.exec 0x1092d8 (fun s => s.RIP = 0x1092d8) (leaR64Effect 0x1092d8 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.out 0x1092dd (movzxR32M8Effect 0x1092dd 6 12 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 80) (.exec 0x1092dd (LoadPre 0x1092dd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1092dd + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1092dd 6 12 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 81) (.exec 0x1092e3 (StorePre 0x1092e3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1092e3 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1092e3 5 9 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 82) (.out 0x1092e8 (movzxR32M8Effect 0x1092e8 6 15 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 83) (.exec 0x1092e8 (LoadPre 0x1092e8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1092e8 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1092e8 6 15 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 84) (.exec 0x1092ee (StorePre 0x1092ee 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1092ee + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1092ee 5 9 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 85) (.out 0x1092f3 (movzxR32M8Effect 0x1092f3 6 13 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 86) (.exec 0x1092f3 (LoadPre 0x1092f3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1092f3 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1092f3 6 13 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 87) (.exec 0x1092f9 (StorePre 0x1092f9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1092f9 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1092f9 5 9 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[61, 4]
    (b_l1092a0_1)))))))))))))))))))))))))))))))))))

def bytes_l1092a0 : List UInt8 :=
  [0x44, 0x89, 0x4C, 0x24, 0x60, 0x4C, 0x89, 0x64, 0x24, 0x68, 0x48, 0x85, 0xED, 0x41, 0x0F, 0x9F,
    0xC1, 0x41, 0x20, 0xC9, 0x41, 0x89, 0xC8, 0x41, 0x80, 0xE0, 0x01, 0x48, 0x85, 0xED, 0x44, 0x88,
    0x44, 0x24, 0x10, 0x0F, 0xB6, 0x5C, 0x24, 0x10, 0x44, 0x88, 0x4C, 0x24, 0x10, 0x44, 0x0F, 0xB6,
    0x74, 0x24, 0x10, 0x44, 0x88, 0x4C, 0x24, 0x10, 0x48, 0x8D, 0x54, 0x24, 0x10, 0x44, 0x0F, 0xB6,
    0x64, 0x24, 0x10, 0x44, 0x88, 0x4C, 0x24, 0x10, 0x44, 0x0F, 0xB6, 0x7C, 0x24, 0x10, 0x44, 0x88,
    0x4C, 0x24, 0x10, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x10, 0x44, 0x88, 0x4C, 0x24, 0x10] ++ bytes_l1092a0_1

theorem code_l1092a0 : ∀ x ∈ codeRange 0x1092a0 bytes_l1092a0, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x92a0 94 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1092a0_1

@[cfg_block] def b_l1093f9 : Block Op Label signature Reg.count 53 :=
  .terminate (.br ⟨.l108f97, RegMap.args (entryMap (live .l1093f9)) 53⟩)

def bytes_l1093f9 : List UInt8 :=
  [0xE9, 0x99, 0xFB, 0xFF, 0xFF]

theorem code_l1093f9 : ∀ x ∈ codeRange 0x1093f9 bytes_l1093f9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x93f9 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1093fe : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1093fe (movR64M64Effect 0x1093fe 0 (.sib 4 none 0 (.d32 0x138))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1093fe (LoadPre 0x1093fe (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x138)) s (0x1093fe + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1093fe 0 (.sib 4 none 0 (.d32 0x138))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x109406 (orR64M64Effect 0x109406 0 (.sib 4 none 0 (.d32 0x128))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[53, 4]
    (.letOp (n := 56) (.exec 0x109406 (LoadPre 0x109406 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x109406 + BitVec.ofNat 64 8)) 8) (orR64M64Effect 0x109406 0 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 57) (.out 0x10940e (orR64M64Effect 0x10940e 0 (.sib 4 none 0 (.d32 0x120))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[55, 4]
    (.letOp (n := 58) (.exec 0x10940e (LoadPre 0x10940e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x10940e + BitVec.ofNat 64 8)) 8) (orR64M64Effect 0x10940e 0 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 59) (.out 0x109416 (orR64M64Effect 0x109416 0 (.sib 4 none 0 (.d32 0x130))) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 4] []) (.flag .ZF)) #v[57, 4]
    (.letOp (n := 60) (.exec 0x109416 (LoadPre 0x109416 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x109416 + BitVec.ofNat 64 8)) 8) (orR64M64Effect 0x109416 0 (.sib 4 none 0 (.d32 0x130))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 61) (.out 0x10941e (atFlags (condHolds 5) (setccR8Effect 0x10941e 3 3)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 3))) #v[3, 59]
    (.letOp (n := 62) (.exec 0x10941e (fun s => s.RIP = 0x10941e) (atFlags (condHolds 5) (setccR8Effect 0x10941e 3 3)) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[3, 59]
    (.letOp (n := 63) (.out 0x109421 (movR32M32LowEffect 0x109421 2 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 64) (.exec 0x109421 (LoadPre 0x109421 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x109421 + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x109421 2 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x109428 (leaR64Effect 0x109428 6 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 66) (.exec 0x109428 (fun s => s.RIP = 0x109428) (leaR64Effect 0x109428 6 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x109430 (movR64M64Effect 0x109430 14 (.sib 4 none 0 (.d32 0x140))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 68) (.exec 0x109430 (LoadPre 0x109430 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x109430 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x109430 14 (.sib 4 none 0 (.d32 0x140))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.out 0x109438 (movR64R64Effect 0x109438 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[67]
    (.letOp (n := 70) (.exec 0x109438 (fun s => s.RIP = 0x109438) (movR64R64Effect 0x109438 7 14) (Reg.operands [.gpr 14] [])) #v[67]
    (.letOp (n := 71) (.out 0x10943b (movR64M64Effect 0x10943b 1 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 72) (.exec 0x10943b (LoadPre 0x10943b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x10943b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10943b 1 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.out 0x109443 (callEffect (fun _ => 0x109c00) 0x109448) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 74) (.exec 0x109443 (PushPre 0x109443 5) (callEffect (fun _ => 0x109c00) 0x109448) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.const ⟨64, 0x109448⟩) #v[]
    (.terminate (.call ⟨.l109c00, RegMap.args [(1, 71), (2, 63), (3, 61), (4, 73), (5, 5), (6, 65), (7, 69), (12, 12), (13, 13), (14, 67), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 76⟩ { target := .l109448, kept := #v[], arity := rfl, guard := some (Fin.last 75) }))))))))))))))))))))))))

def bytes_l1093fe : List UInt8 :=
  [0x48, 0x8B, 0x84, 0x24, 0x38, 0x01, 0x00, 0x00, 0x48, 0x0B, 0x84, 0x24, 0x28, 0x01, 0x00, 0x00,
    0x48, 0x0B, 0x84, 0x24, 0x20, 0x01, 0x00, 0x00, 0x48, 0x0B, 0x84, 0x24, 0x30, 0x01, 0x00, 0x00,
    0x0F, 0x95, 0xC3, 0x8B, 0x94, 0x24, 0x98, 0x00, 0x00, 0x00, 0x48, 0x8D, 0xB4, 0x24, 0xD0, 0x00,
    0x00, 0x00, 0x4C, 0x8B, 0xB4, 0x24, 0x40, 0x01, 0x00, 0x00, 0x4C, 0x89, 0xF7, 0x48, 0x8B, 0x8C,
    0x24, 0xA0, 0x00, 0x00, 0x00, 0xE8, 0xB8, 0x07, 0x00, 0x00]

theorem code_l1093fe : ∀ x ∈ codeRange 0x1093fe bytes_l1093fe, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x93fe 74 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109448 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x109448 (movR64M64Effect 0x109448 0 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x109448 (LoadPre 0x109448 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x109448 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109448 0 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10944d (xorR64Imm8Effect 0x10944d 0 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x10944d (fun s => s.RIP = 0x10944d) (xorR64Imm8Effect 0x10944d 0 0x1) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x109451 (orR64M64Effect 0x109451 0 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[55, 4]
    (.letOp (n := 58) (.exec 0x109451 (LoadPre 0x109451 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x109451 + BitVec.ofNat 64 8)) 8) (orR64M64Effect 0x109451 0 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 59) (.out 0x109459 (orR64M64Effect 0x109459 0 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[57, 4]
    (.letOp (n := 60) (.exec 0x109459 (LoadPre 0x109459 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x109459 + BitVec.ofNat 64 8)) 8) (orR64M64Effect 0x109459 0 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 61) (.out 0x109461 (orR64M64Effect 0x109461 0 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[59, 4]
    (.letOp (n := 62) (.out 0x109461 (orR64M64Effect 0x109461 0 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 4] []) (.flag .ZF)) #v[59, 4]
    (.letOp (n := 63) (.exec 0x109461 (LoadPre 0x109461 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x109461 + BitVec.ofNat 64 8)) 8) (orR64M64Effect 0x109461 0 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 64) (.out 0x109469 (atFlags (condHolds 4) (setccR8Effect 0x109469 3 0)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 0))) #v[61, 62]
    (.letOp (n := 65) (.exec 0x109469 (fun s => s.RIP = 0x109469) (atFlags (condHolds 4) (setccR8Effect 0x109469 3 0)) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[61, 62]
    (.letOp (n := 66) (.out 0x10946c (andR8R8Effect 0x10946c 2 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[64, 3]
    (.letOp (n := 67) (.exec 0x10946c (fun s => s.RIP = 0x10946c) (andR8R8Effect 0x10946c 2 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[64, 3]
    (.letOp (n := 68) (.exec 0x10946e (StorePre 0x10946e 4 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x10946e + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10946e 4 0 (.base 14 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 14] [])) #v[66, 14]
    (.letOp (n := 69) (.out 0x109472 (movR64R64Effect 0x109472 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[14]
    (.letOp (n := 70) (.exec 0x109472 (fun s => s.RIP = 0x109472) (movR64R64Effect 0x109472 0 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 71) (.out 0x109475 (addR64Imm32Effect 0x109475 4 0x168) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 72) (.exec 0x109475 (fun s => s.RIP = 0x109475) (addR64Imm32Effect 0x109475 4 0x168) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.out 0x10947c (popR64Effect 0x10947c 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[71]
    (.letOp (n := 74) (.out 0x10947c (popR64Effect 0x10947c 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[71]
    (.letOp (n := 75) (.exec 0x10947c (PopPre 0x10947c) (popR64Effect 0x10947c 1 3) (Reg.operands [.gpr 4] [])) #v[71]
    (.letOp (n := 76) (.out 0x10947d (popR64Effect 0x10947d 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[74]
    (.letOp (n := 77) (.out 0x10947d (popR64Effect 0x10947d 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[74]
    (.letOp (n := 78) (.exec 0x10947d (PopPre 0x10947d) (popR64Effect 0x10947d 2 12) (Reg.operands [.gpr 4] [])) #v[74]
    (.letOp (n := 79) (.out 0x10947f (popR64Effect 0x10947f 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[77]
    (.letOp (n := 80) (.out 0x10947f (popR64Effect 0x10947f 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[77]
    (.letOp (n := 81) (.exec 0x10947f (PopPre 0x10947f) (popR64Effect 0x10947f 2 13) (Reg.operands [.gpr 4] [])) #v[77]
    (.letOp (n := 82) (.out 0x109481 (popR64Effect 0x109481 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[80]
    (.letOp (n := 83) (.out 0x109481 (popR64Effect 0x109481 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[80]
    (.letOp (n := 84) (.exec 0x109481 (PopPre 0x109481) (popR64Effect 0x109481 2 14) (Reg.operands [.gpr 4] [])) #v[80]
    (.letOp (n := 85) (.out 0x109483 (popR64Effect 0x109483 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[83]
    (.letOp (n := 86) (.out 0x109483 (popR64Effect 0x109483 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[83]
    (.letOp (n := 87) (.exec 0x109483 (PopPre 0x109483) (popR64Effect 0x109483 2 15) (Reg.operands [.gpr 4] [])) #v[83]
    (.letOp (n := 88) (.out 0x109485 (popR64Effect 0x109485 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[86]
    (.letOp (n := 89) (.out 0x109485 (popR64Effect 0x109485 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[86]
    (.letOp (n := 90) (.exec 0x109485 (PopPre 0x109485) (popR64Effect 0x109485 1 5) (Reg.operands [.gpr 4] [])) #v[86]
    (.letOp (n := 91) (.out 0x109486 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[89]
    (.letOp (n := 92) (.out 0x109486 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[89]
    (.letOp (n := 93) (.exec 0x109486 (RetPre 0x109486) (retEffect) (Reg.operands [.gpr 4] [])) #v[89]
    (.terminate (.ret (RegMap.args [(0, 69), (1, 1), (2, 2), (3, 73), (4, 92), (5, 88), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 76), (13, 79), (14, 82), (15, 85), (22, 22), (39, 39), (50, 50), (51, 51)] 94) (some ⟨91, by decide⟩)))))))))))))))))))))))))))))))))))))))))))

def bytes_l109448 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x78, 0x48, 0x83, 0xF0, 0x01, 0x48, 0x0B, 0x84, 0x24, 0x80, 0x00, 0x00,
    0x00, 0x48, 0x0B, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x0B, 0x84, 0x24, 0x90, 0x00, 0x00,
    0x00, 0x0F, 0x94, 0xC0, 0x20, 0xD8, 0x41, 0x88, 0x46, 0x20, 0x4C, 0x89, 0xF0, 0x48, 0x81, 0xC4,
    0x68, 0x01, 0x00, 0x00, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l109448 : ∀ x ∈ codeRange 0x109448 bytes_l109448, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9448 63 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

end K256.Proofs.Signing.LIR
