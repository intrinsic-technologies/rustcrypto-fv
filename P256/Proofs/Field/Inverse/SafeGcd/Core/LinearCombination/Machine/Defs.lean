import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine.Labels
import P256.Proofs.Common.CFG.EvalAttr
import P256.Proofs.Common.Lift.Generated.Footprints

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

@[cfg_block] def b_l116d00 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x111220 (pushR64Effect 0x111220 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x111220 (PushPre 0x111220 1) (pushR64Effect 0x111220 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x111221 (pushR64Effect 0x111221 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x111221 (PushPre 0x111221 2) (pushR64Effect 0x111221 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x111223 (pushR64Effect 0x111223 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x111223 (PushPre 0x111223 2) (pushR64Effect 0x111223 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x111225 (pushR64Effect 0x111225 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x111225 (PushPre 0x111225 2) (pushR64Effect 0x111225 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x111227 (pushR64Effect 0x111227 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x111227 (PushPre 0x111227 2) (pushR64Effect 0x111227 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x111229 (pushR64Effect 0x111229 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x111229 (PushPre 0x111229 1) (pushR64Effect 0x111229 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x11122a (subR64Imm8Effect 0x11122a 4 0x40) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x11122a (fun s => s.RIP = 0x11122a) (subR64Imm8Effect 0x11122a 4 0x40) (Reg.operands [.gpr 4] [])) #v[63]
    (.terminate (.br ⟨.l116d0e, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)] 67⟩)))))))))))))))

def bytes_l116d00 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x83, 0xEC, 0x40]

theorem code_l116d00 : ∀ x ∈ codeRange 0x111220 bytes_l116d00, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x11220 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l116d0e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11122e (movR64R64Effect 0x11122e 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[2]
    (.letOp (n := 54) (.exec 0x11122e (fun s => s.RIP = 0x11122e) (movR64R64Effect 0x11122e 11 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 55) (.out 0x111231 (movR64R64Effect 0x111231 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[1]
    (.letOp (n := 56) (.exec 0x111231 (fun s => s.RIP = 0x111231) (movR64R64Effect 0x111231 2 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 57) (.out 0x111234 (shrR64Effect 0x111234 4 2 63) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[55]
    (.letOp (n := 58) (.exec 0x111234 (fun s => s.RIP = 0x111234) (shrR64Effect 0x111234 4 2 63) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[55]
    (.letOp (n := 59) (.exec 0x111238 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111238 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x111238 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x111238 2 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 60) (.out 0x11123d (movR64R64Effect 0x11123d 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[1]
    (.letOp (n := 61) (.exec 0x11123d (fun s => s.RIP = 0x11123d) (movR64R64Effect 0x11123d 0 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 62) (.out 0x111240 (negR64Effect 0x111240 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[60]
    (.letOp (n := 63) (.exec 0x111240 (fun s => s.RIP = 0x111240) (negR64Effect 0x111240 0) (Reg.operands [.gpr 0] [])) #v[60]
    (.letOp (n := 64) (.exec 0x111243 (StorePre 0x111243 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x111243 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x111243 3 2 (.sib 4 none 0 .none)) (Reg.operands [.gpr 2, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 65) (.exec 0x111246 (fun s => s.RIP = 0x111246) (movR64R64Effect 0x111246 2 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.out 0x111249 (movzxR32M8Effect 0x111249 4 3 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 67) (.exec 0x111249 (LoadPre 0x111249 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x111249 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x111249 4 3 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.out 0x11124d (xorR64R64Effect 0x11124d 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[62, 1]
    (.letOp (n := 69) (.exec 0x11124d (fun s => s.RIP = 0x11124d) (xorR64R64Effect 0x11124d 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[62, 1]
    (.letOp (n := 70) (.out 0x111250 (negR64Effect 0x111250 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[66]
    (.letOp (n := 71) (.exec 0x111250 (fun s => s.RIP = 0x111250) (negR64Effect 0x111250 3) (Reg.operands [.gpr 3] [])) #v[66]
    (.letOp (n := 72) (.out 0x111253 (andR64R64Effect 0x111253 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0] []) (.reg (.gpr 3))) #v[70, 68]
    (.letOp (n := 73) (.exec 0x111253 (fun s => s.RIP = 0x111253) (andR64R64Effect 0x111253 3 0) (Reg.operands [.gpr 3, .gpr 0] [])) #v[70, 68]
    (.letOp (n := 74) (.out 0x111256 (xorR64R64Effect 0x111256 3 1) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 1] []) (.reg (.gpr 3))) #v[72, 1]
    (.letOp (n := 75) (.exec 0x111256 (fun s => s.RIP = 0x111256) (xorR64R64Effect 0x111256 3 1) (Reg.operands [.gpr 3, .gpr 1] [])) #v[72, 1]
    (.letOp (n := 76) (.out 0x111259 (movR64R64Effect 0x111259 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[8]
    (.letOp (n := 77) (.exec 0x111259 (fun s => s.RIP = 0x111259) (movR64R64Effect 0x111259 0 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 78) (.out 0x11125c (shrR64Effect 0x11125c 4 0 63) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[76]
    (.letOp (n := 79) (.exec 0x11125c (fun s => s.RIP = 0x11125c) (shrR64Effect 0x11125c 4 0 63) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[76]
    (.letOp (n := 80) (.exec 0x111260 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111260 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x111260 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x111260 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[78, 4]
    (.letOp (n := 81) (.exec 0x111265 (StorePre 0x111265 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x111265 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x111265 3 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[78, 4]
    (.letOp (n := 82) (.exec 0x111268 (fun s => s.RIP = 0x111268) (movR64R64Effect 0x111268 0 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 83) (.out 0x11126b (movR64R64Effect 0x11126b 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[74]
    (.letOp (n := 84) (.exec 0x11126b (fun s => s.RIP = 0x11126b) (movR64R64Effect 0x11126b 0 3) (Reg.operands [.gpr 3] [])) #v[74]
    (.terminate (.br ⟨.l116d4e, RegMap.args [(0, 83), (1, 1), (3, 74), (4, 4), (6, 6), (7, 7), (8, 8), (11, 53), (22, 22), (39, 39), (51, 51)] 85⟩)))))))))))))))))))))))))))))))))

def bytes_l116d0e : List UInt8 :=
  [0x49, 0x89, 0xD3, 0x48, 0x89, 0xCA, 0x48, 0xC1, 0xEA, 0x3F, 0x48, 0x89, 0x54, 0x24, 0x20, 0x48,
    0x89, 0xC8, 0x48, 0xF7, 0xD8, 0x88, 0x14, 0x24, 0x48, 0x89, 0xE2, 0x0F, 0xB6, 0x1C, 0x24, 0x48,
    0x31, 0xC8, 0x48, 0xF7, 0xDB, 0x48, 0x21, 0xC3, 0x48, 0x31, 0xCB, 0x4C, 0x89, 0xC0, 0x48, 0xC1,
    0xE8, 0x3F, 0x48, 0x89, 0x44, 0x24, 0x18, 0x88, 0x04, 0x24, 0x48, 0x89, 0xE0, 0x48, 0x89, 0xD8]

theorem code_l116d0e : ∀ x ∈ codeRange 0x11122e bytes_l116d0e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1122e 64 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l116d4e_1 : Block Op Label signature Reg.count 97 :=
  .letOp (n := 97) (.out 0x1112af (movR64R64Effect 0x1112af 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[93]
    (.letOp (n := 98) (.exec 0x1112af (fun s => s.RIP = 0x1112af) (movR64R64Effect 0x1112af 1 2) (Reg.operands [.gpr 2] [])) #v[93]
    (.letOp (n := 99) (.out 0x1112b2 (xorR64R64Effect 0x1112b2 13 8) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 8] []) (.reg (.gpr 13))) #v[88, 8]
    (.letOp (n := 100) (.exec 0x1112b2 (fun s => s.RIP = 0x1112b2) (xorR64R64Effect 0x1112b2 13 8) (Reg.operands [.gpr 13, .gpr 8] [])) #v[88, 8]
    (.terminate (.br ⟨.l116d95, RegMap.args [(0, 92), (1, 97), (2, 93), (3, 95), (4, 4), (5, 84), (6, 6), (7, 7), (8, 8), (9, 69), (10, 56), (11, 11), (12, 82), (13, 99), (14, 58), (15, 71), (22, 22), (39, 39), (51, 51)] 101⟩)))))

def bytes_l116d4e_1 : List UInt8 :=
  [0x48, 0x89, 0xD1, 0x4D, 0x31, 0xC5]

theorem code_l116d4e_1 : ∀ x ∈ codeRange 0x1112af bytes_l116d4e_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x112af 6 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l116d4e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11126e (mulM64Effect 0x11126e 3 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[0, 6]
    (.letOp (n := 54) (.out 0x11126e (mulM64Effect 0x11126e 3 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 6] []) (.reg (.gpr 2))) #v[0, 6]
    (.letOp (n := 55) (.exec 0x11126e (LoadPre 0x11126e (fun s => AddrMode.addr (.base 6 .none) s (0x11126e + BitVec.ofNat 64 3)) 8) (mulM64Effect 0x11126e 3 (.base 6 .none)) (Reg.operands [.gpr 0, .gpr 6] [])) #v[0, 6]
    (.letOp (n := 56) (.out 0x111271 (movR64R64Effect 0x111271 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[53]
    (.letOp (n := 57) (.exec 0x111271 (fun s => s.RIP = 0x111271) (movR64R64Effect 0x111271 10 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 58) (.out 0x111274 (movR64R64Effect 0x111274 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[54]
    (.letOp (n := 59) (.exec 0x111274 (fun s => s.RIP = 0x111274) (movR64R64Effect 0x111274 14 2) (Reg.operands [.gpr 2] [])) #v[54]
    (.letOp (n := 60) (.out 0x111277 (movR64R64Effect 0x111277 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 8] []) (.reg (.gpr 1))) #v[8]
    (.letOp (n := 61) (.exec 0x111277 (fun s => s.RIP = 0x111277) (movR64R64Effect 0x111277 1 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 62) (.out 0x11127a (negR64Effect 0x11127a 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[60]
    (.letOp (n := 63) (.exec 0x11127a (fun s => s.RIP = 0x11127a) (negR64Effect 0x11127a 1) (Reg.operands [.gpr 1] [])) #v[60]
    (.letOp (n := 64) (.out 0x11127d (movR64R64Effect 0x11127d 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 65) (.exec 0x11127d (fun s => s.RIP = 0x11127d) (movR64R64Effect 0x11127d 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 66) (.out 0x111280 (mulM64Effect 0x111280 4 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[64, 6]
    (.letOp (n := 67) (.out 0x111280 (mulM64Effect 0x111280 4 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 6] []) (.reg (.gpr 2))) #v[64, 6]
    (.letOp (n := 68) (.exec 0x111280 (LoadPre 0x111280 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x111280 + BitVec.ofNat 64 4)) 8) (mulM64Effect 0x111280 4 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 6] [])) #v[64, 6]
    (.letOp (n := 69) (.out 0x111284 (movR64R64Effect 0x111284 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[66]
    (.letOp (n := 70) (.exec 0x111284 (fun s => s.RIP = 0x111284) (movR64R64Effect 0x111284 9 0) (Reg.operands [.gpr 0] [])) #v[66]
    (.letOp (n := 71) (.out 0x111287 (movR64R64Effect 0x111287 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[67]
    (.letOp (n := 72) (.exec 0x111287 (fun s => s.RIP = 0x111287) (movR64R64Effect 0x111287 15 2) (Reg.operands [.gpr 2] [])) #v[67]
    (.letOp (n := 73) (.out 0x11128a (movzxR32M8Effect 0x11128a 5 13 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 74) (.exec 0x11128a (LoadPre 0x11128a (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x11128a + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x11128a 5 13 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.out 0x11128f (xorR64R64Effect 0x11128f 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8] []) (.reg (.gpr 1))) #v[62, 8]
    (.letOp (n := 76) (.exec 0x11128f (fun s => s.RIP = 0x11128f) (xorR64R64Effect 0x11128f 1 8) (Reg.operands [.gpr 1, .gpr 8] [])) #v[62, 8]
    (.letOp (n := 77) (.out 0x111292 (movR64R64Effect 0x111292 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 78) (.exec 0x111292 (fun s => s.RIP = 0x111292) (movR64R64Effect 0x111292 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 79) (.out 0x111295 (mulM64Effect 0x111295 4 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[77, 6]
    (.letOp (n := 80) (.out 0x111295 (mulM64Effect 0x111295 4 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 6] []) (.reg (.gpr 2))) #v[77, 6]
    (.letOp (n := 81) (.exec 0x111295 (LoadPre 0x111295 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x111295 + BitVec.ofNat 64 4)) 8) (mulM64Effect 0x111295 4 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 6] [])) #v[77, 6]
    (.letOp (n := 82) (.out 0x111299 (movR64R64Effect 0x111299 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[79]
    (.letOp (n := 83) (.exec 0x111299 (fun s => s.RIP = 0x111299) (movR64R64Effect 0x111299 12 0) (Reg.operands [.gpr 0] [])) #v[79]
    (.letOp (n := 84) (.out 0x11129c (movR64R64Effect 0x11129c 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[80]
    (.letOp (n := 85) (.exec 0x11129c (fun s => s.RIP = 0x11129c) (movR64R64Effect 0x11129c 5 2) (Reg.operands [.gpr 2] [])) #v[80]
    (.letOp (n := 86) (.out 0x11129f (negR64Effect 0x11129f 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[73]
    (.letOp (n := 87) (.exec 0x11129f (fun s => s.RIP = 0x11129f) (negR64Effect 0x11129f 13) (Reg.operands [.gpr 13] [])) #v[73]
    (.letOp (n := 88) (.out 0x1112a2 (andR64R64Effect 0x1112a2 13 1) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 1] []) (.reg (.gpr 13))) #v[86, 75]
    (.letOp (n := 89) (.exec 0x1112a2 (fun s => s.RIP = 0x1112a2) (andR64R64Effect 0x1112a2 13 1) (Reg.operands [.gpr 13, .gpr 1] [])) #v[86, 75]
    (.letOp (n := 90) (.out 0x1112a5 (movR64R64Effect 0x1112a5 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 91) (.exec 0x1112a5 (fun s => s.RIP = 0x1112a5) (movR64R64Effect 0x1112a5 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 92) (.out 0x1112a8 (mulM64Effect 0x1112a8 4 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[90, 6]
    (.letOp (n := 93) (.out 0x1112a8 (mulM64Effect 0x1112a8 4 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 6] []) (.reg (.gpr 2))) #v[90, 6]
    (.letOp (n := 94) (.exec 0x1112a8 (LoadPre 0x1112a8 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x1112a8 + BitVec.ofNat 64 4)) 8) (mulM64Effect 0x1112a8 4 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 6] [])) #v[90, 6]
    (.letOp (n := 95) (.out 0x1112ac (movR64R64Effect 0x1112ac 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[92]
    (.letOp (n := 96) (.exec 0x1112ac (fun s => s.RIP = 0x1112ac) (movR64R64Effect 0x1112ac 3 0) (Reg.operands [.gpr 0] [])) #v[92]
    (b_l116d4e_1))))))))))))))))))))))))))))))))))))))))))))

def bytes_l116d4e : List UInt8 :=
  [0x48, 0xF7, 0x26, 0x49, 0x89, 0xC2, 0x49, 0x89, 0xD6, 0x4C, 0x89, 0xC1, 0x48, 0xF7, 0xD9, 0x48,
    0x89, 0xD8, 0x48, 0xF7, 0x66, 0x08, 0x49, 0x89, 0xC1, 0x49, 0x89, 0xD7, 0x44, 0x0F, 0xB6, 0x2C,
    0x24, 0x4C, 0x31, 0xC1, 0x48, 0x89, 0xD8, 0x48, 0xF7, 0x66, 0x10, 0x49, 0x89, 0xC4, 0x48, 0x89,
    0xD5, 0x49, 0xF7, 0xDD, 0x49, 0x21, 0xCD, 0x48, 0x89, 0xD8, 0x48, 0xF7, 0x66, 0x18, 0x48, 0x89,
    0xC3] ++ bytes_l116d4e_1

theorem code_l116d4e : ∀ x ∈ codeRange 0x11126e bytes_l116d4e, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1126e 65 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l116d4e_1

@[cfg_block] def b_l116d95_1 : Block Op Label signature Reg.count 95 :=
  .letOp (n := 95) (.out 0x1112ff (mulM64Effect 0x1112ff 4 (.base 11 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[93, 11]
    (.letOp (n := 96) (.out 0x1112ff (mulM64Effect 0x1112ff 4 (.base 11 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 11] []) (.reg (.gpr 2))) #v[93, 11]
    (.letOp (n := 97) (.exec 0x1112ff (LoadPre 0x1112ff (fun s => AddrMode.addr (.base 11 (.d8 0x18)) s (0x1112ff + BitVec.ofNat 64 4)) 8) (mulM64Effect 0x1112ff 4 (.base 11 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 11] [])) #v[93, 11]
    (.terminate (.br ⟨.l116de3, RegMap.args [(0, 95), (1, 62), (2, 96), (3, 59), (4, 4), (5, 86), (6, 6), (7, 7), (8, 90), (9, 53), (10, 10), (11, 11), (12, 56), (13, 13), (14, 84), (15, 77), (22, 22), (39, 39), (51, 51)] 98⟩))))

def bytes_l116d95_1 : List UInt8 :=
  [0x49, 0xF7, 0x63, 0x18]

theorem code_l116d95_1 : ∀ x ∈ codeRange 0x1112ff bytes_l116d95_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x112ff 4 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l116d95 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1112b5 (addR64R64Effect 0x1112b5 9 14) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 14] []) (.reg (.gpr 9))) #v[9, 14]
    (.letOp (n := 54) (.out 0x1112b5 (addR64R64Effect 0x1112b5 9 14) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 14] []) (.flag .CF)) #v[9, 14]
    (.letOp (n := 55) (.exec 0x1112b5 (fun s => s.RIP = 0x1112b5) (addR64R64Effect 0x1112b5 9 14) (Reg.operands [.gpr 9, .gpr 14] [])) #v[9, 14]
    (.letOp (n := 56) (.out 0x1112b8 (atFlags StatusFlags.CF (adcR64R64Effect 0x1112b8 12 15)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 12))) #v[12, 15, 54]
    (.letOp (n := 57) (.out 0x1112b8 (atFlags StatusFlags.CF (adcR64R64Effect 0x1112b8 12 15)) (Reg.operands [.gpr 12, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[12, 15, 54]
    (.letOp (n := 58) (.exec 0x1112b8 (fun s => s.RIP = 0x1112b8) (atFlags StatusFlags.CF (adcR64R64Effect 0x1112b8 12 15)) (Reg.operands [.gpr 12, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[12, 15, 54]
    (.letOp (n := 59) (.out 0x1112bb (atFlags StatusFlags.CF (adcR64R64Effect 0x1112bb 3 5)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[3, 5, 57]
    (.letOp (n := 60) (.out 0x1112bb (atFlags StatusFlags.CF (adcR64R64Effect 0x1112bb 3 5)) (Reg.operands [.gpr 3, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[3, 5, 57]
    (.letOp (n := 61) (.exec 0x1112bb (fun s => s.RIP = 0x1112bb) (atFlags StatusFlags.CF (adcR64R64Effect 0x1112bb 3 5)) (Reg.operands [.gpr 3, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3, 5, 57]
    (.letOp (n := 62) (.out 0x1112be (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1112be 1 0x0)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[1, 60]
    (.letOp (n := 63) (.exec 0x1112be (fun s => s.RIP = 0x1112be) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1112be 1 0x0)) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1, 60]
    (.letOp (n := 64) (.out 0x1112c2 (movR64R64Effect 0x1112c2 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[13]
    (.letOp (n := 65) (.exec 0x1112c2 (fun s => s.RIP = 0x1112c2) (movR64R64Effect 0x1112c2 0 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 66) (.out 0x1112c5 (mulM64Effect 0x1112c5 3 (.base 11 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[64, 11]
    (.letOp (n := 67) (.out 0x1112c5 (mulM64Effect 0x1112c5 3 (.base 11 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 11] []) (.reg (.gpr 2))) #v[64, 11]
    (.letOp (n := 68) (.exec 0x1112c5 (LoadPre 0x1112c5 (fun s => AddrMode.addr (.base 11 .none) s (0x1112c5 + BitVec.ofNat 64 3)) 8) (mulM64Effect 0x1112c5 3 (.base 11 .none)) (Reg.operands [.gpr 0, .gpr 11] [])) #v[64, 11]
    (.letOp (n := 69) (.exec 0x1112c8 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1112c8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1112c8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1112c8 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[67, 4]
    (.letOp (n := 70) (.exec 0x1112cd (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1112cd 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1112cd + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1112cd 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[66, 4]
    (.letOp (n := 71) (.out 0x1112d2 (movR64R64Effect 0x1112d2 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[13]
    (.letOp (n := 72) (.exec 0x1112d2 (fun s => s.RIP = 0x1112d2) (movR64R64Effect 0x1112d2 0 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 73) (.out 0x1112d5 (mulM64Effect 0x1112d5 4 (.base 11 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[71, 11]
    (.letOp (n := 74) (.out 0x1112d5 (mulM64Effect 0x1112d5 4 (.base 11 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 11] []) (.reg (.gpr 2))) #v[71, 11]
    (.letOp (n := 75) (.exec 0x1112d5 (LoadPre 0x1112d5 (fun s => AddrMode.addr (.base 11 (.d8 0x8)) s (0x1112d5 + BitVec.ofNat 64 4)) 8) (mulM64Effect 0x1112d5 4 (.base 11 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 11] [])) #v[71, 11]
    (.letOp (n := 76) (.exec 0x1112d9 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1112d9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1112d9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1112d9 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[74, 4]
    (.letOp (n := 77) (.out 0x1112de (movR64R64Effect 0x1112de 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[73]
    (.letOp (n := 78) (.exec 0x1112de (fun s => s.RIP = 0x1112de) (movR64R64Effect 0x1112de 15 0) (Reg.operands [.gpr 0] [])) #v[73]
    (.letOp (n := 79) (.out 0x1112e1 (movR64R64Effect 0x1112e1 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[13]
    (.letOp (n := 80) (.exec 0x1112e1 (fun s => s.RIP = 0x1112e1) (movR64R64Effect 0x1112e1 0 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 81) (.out 0x1112e4 (mulM64Effect 0x1112e4 4 (.base 11 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[79, 11]
    (.letOp (n := 82) (.out 0x1112e4 (mulM64Effect 0x1112e4 4 (.base 11 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 11] []) (.reg (.gpr 2))) #v[79, 11]
    (.letOp (n := 83) (.exec 0x1112e4 (LoadPre 0x1112e4 (fun s => AddrMode.addr (.base 11 (.d8 0x10)) s (0x1112e4 + BitVec.ofNat 64 4)) 8) (mulM64Effect 0x1112e4 4 (.base 11 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 11] [])) #v[79, 11]
    (.letOp (n := 84) (.out 0x1112e8 (movR64R64Effect 0x1112e8 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[81]
    (.letOp (n := 85) (.exec 0x1112e8 (fun s => s.RIP = 0x1112e8) (movR64R64Effect 0x1112e8 14 0) (Reg.operands [.gpr 0] [])) #v[81]
    (.letOp (n := 86) (.out 0x1112eb (movR64R64Effect 0x1112eb 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[82]
    (.letOp (n := 87) (.exec 0x1112eb (fun s => s.RIP = 0x1112eb) (movR64R64Effect 0x1112eb 5 2) (Reg.operands [.gpr 2] [])) #v[82]
    (.letOp (n := 88) (.out 0x1112ee (movR64M64Effect 0x1112ee 8 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 89) (.exec 0x1112ee (LoadPre 0x1112ee (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1112ee + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1112ee 8 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 90) (.out 0x1112f3 (xorR8M8Effect 0x1112f3 4 8 (.base 6 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6] []) (.reg (.gpr 8))) #v[88, 6]
    (.letOp (n := 91) (.exec 0x1112f3 (LoadPre 0x1112f3 (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x1112f3 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1112f3 4 8 (.base 6 (.d8 0x20))) (Reg.operands [.gpr 8, .gpr 6] [])) #v[88, 6]
    (.letOp (n := 92) (.exec 0x1112f7 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1112f7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1112f7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1112f7 8 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[90, 4]
    (.letOp (n := 93) (.out 0x1112fc (movR64R64Effect 0x1112fc 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[13]
    (.letOp (n := 94) (.exec 0x1112fc (fun s => s.RIP = 0x1112fc) (movR64R64Effect 0x1112fc 0 13) (Reg.operands [.gpr 13] [])) #v[13]
    (b_l116d95_1))))))))))))))))))))))))))))))))))))))))))

def bytes_l116d95 : List UInt8 :=
  [0x4D, 0x01, 0xF1, 0x4D, 0x11, 0xFC, 0x48, 0x11, 0xEB, 0x48, 0x83, 0xD1, 0x00, 0x4C, 0x89, 0xE8,
    0x49, 0xF7, 0x23, 0x48, 0x89, 0x54, 0x24, 0x10, 0x48, 0x89, 0x44, 0x24, 0x28, 0x4C, 0x89, 0xE8,
    0x49, 0xF7, 0x63, 0x08, 0x48, 0x89, 0x54, 0x24, 0x08, 0x49, 0x89, 0xC7, 0x4C, 0x89, 0xE8, 0x49,
    0xF7, 0x63, 0x10, 0x49, 0x89, 0xC6, 0x48, 0x89, 0xD5, 0x4C, 0x8B, 0x44, 0x24, 0x20, 0x44, 0x32,
    0x46, 0x20, 0x4C, 0x89, 0x44, 0x24, 0x20, 0x4C, 0x89, 0xE8] ++ bytes_l116d95_1

theorem code_l116d95 : ∀ x ∈ codeRange 0x1112b5 bytes_l116d95, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x112b5 74 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l116d95_1

@[cfg_block] def b_l116de3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x111303 (addR64M64Effect 0x111303 15 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 4] []) (.reg (.gpr 15))) #v[15, 4]
    (.letOp (n := 54) (.out 0x111303 (addR64M64Effect 0x111303 15 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 4] []) (.flag .CF)) #v[15, 4]
    (.letOp (n := 55) (.exec 0x111303 (LoadPre 0x111303 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x111303 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x111303 15 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[15, 4]
    (.letOp (n := 56) (.out 0x111308 (atFlags StatusFlags.CF (adcR64M64Effect 0x111308 14 (.sib 4 none 0 (.d8 0x8)))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 14))) #v[14, 4, 54]
    (.letOp (n := 57) (.out 0x111308 (atFlags StatusFlags.CF (adcR64M64Effect 0x111308 14 (.sib 4 none 0 (.d8 0x8)))) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.flag .CF)) #v[14, 4, 54]
    (.letOp (n := 58) (.exec 0x111308 (LoadPre 0x111308 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x111308 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x111308 14 (.sib 4 none 0 (.d8 0x8)))) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[14, 4, 54]
    (.letOp (n := 59) (.out 0x11130d (movR64R64Effect 0x11130d 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[56]
    (.letOp (n := 60) (.exec 0x11130d (fun s => s.RIP = 0x11130d) (movR64R64Effect 0x11130d 6 14) (Reg.operands [.gpr 14] [])) #v[56]
    (.letOp (n := 61) (.exec 0x111310 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111310 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x111310 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x111310 14 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 62) (.out 0x111315 (atFlags StatusFlags.CF (adcR64R64Effect 0x111315 0 5)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 0))) #v[0, 5, 57]
    (.letOp (n := 63) (.out 0x111315 (atFlags StatusFlags.CF (adcR64R64Effect 0x111315 0 5)) (Reg.operands [.gpr 0, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[0, 5, 57]
    (.letOp (n := 64) (.exec 0x111315 (fun s => s.RIP = 0x111315) (atFlags StatusFlags.CF (adcR64R64Effect 0x111315 0 5)) (Reg.operands [.gpr 0, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[0, 5, 57]
    (.letOp (n := 65) (.out 0x111318 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x111318 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[2, 63]
    (.letOp (n := 66) (.exec 0x111318 (fun s => s.RIP = 0x111318) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x111318 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2, 63]
    (.letOp (n := 67) (.exec 0x11131c (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x11131c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11131c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11131c 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x111321 (movR64M64Effect 0x111321 2 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 69) (.exec 0x111321 (LoadPre 0x111321 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x111321 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111321 2 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.out 0x111326 (xorR8M8Effect 0x111326 4 2 (.base 11 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 11] []) (.reg (.gpr 2))) #v[68, 11]
    (.letOp (n := 71) (.exec 0x111326 (LoadPre 0x111326 (fun s => AddrMode.addr (.base 11 (.d8 0x20)) s (0x111326 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x111326 4 2 (.base 11 (.d8 0x20))) (Reg.operands [.gpr 2, .gpr 11] [])) #v[68, 11]
    (.letOp (n := 72) (.exec 0x11132a (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x11132a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11132a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11132a 2 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[70, 4]
    (.terminate (.br ⟨.l116e0f, RegMap.args [(0, 62), (1, 1), (2, 70), (3, 3), (4, 4), (5, 5), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 56), (15, 53), (22, 22), (39, 39), (51, 51)] 73⟩)))))))))))))))))))))

def bytes_l116de3 : List UInt8 :=
  [0x4C, 0x03, 0x7C, 0x24, 0x10, 0x4C, 0x13, 0x74, 0x24, 0x08, 0x4C, 0x89, 0xF6, 0x4C, 0x89, 0x74,
    0x24, 0x30, 0x48, 0x11, 0xE8, 0x48, 0x83, 0xD2, 0x00, 0x48, 0x89, 0x54, 0x24, 0x08, 0x48, 0x8B,
    0x54, 0x24, 0x18, 0x41, 0x32, 0x53, 0x20, 0x48, 0x89, 0x54, 0x24, 0x18]

theorem code_l116de3 : ∀ x ∈ codeRange 0x111303 bytes_l116de3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x11303 44 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l116e0f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11132f (movR32R32Effect 0x11132f 3 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[2]
    (.letOp (n := 54) (.exec 0x11132f (fun s => s.RIP = 0x11132f) (movR32R32Effect 0x11132f 3 11 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 55) (.out 0x111332 (xorR8R8Effect 0x111332 3 11 8) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 8] []) (.reg (.gpr 11))) #v[53, 8]
    (.letOp (n := 56) (.exec 0x111332 (fun s => s.RIP = 0x111332) (xorR8R8Effect 0x111332 3 11 8) (Reg.operands [.gpr 11, .gpr 8] [])) #v[53, 8]
    (.letOp (n := 57) (.exec 0x111335 (StorePre 0x111335 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x111335 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x111335 5 11 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 58) (.out 0x11133a (xorR8Imm8Effect 0x11133a 4 11 0x1) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11] []) (.reg (.gpr 11))) #v[55]
    (.letOp (n := 59) (.exec 0x11133a (fun s => s.RIP = 0x11133a) (xorR8Imm8Effect 0x11133a 4 11 0x1) (Reg.operands [.gpr 11] [])) #v[55]
    (.letOp (n := 60) (.out 0x11133e (movR64M64Effect 0x11133e 14 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 61) (.exec 0x11133e (LoadPre 0x11133e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11133e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11133e 14 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.out 0x111343 (movR64R64Effect 0x111343 13 14) (EffectPart.reads (.reg (.gpr 13)) [.gpr 14] []) (.reg (.gpr 13))) #v[60]
    (.letOp (n := 63) (.exec 0x111343 (fun s => s.RIP = 0x111343) (movR64R64Effect 0x111343 13 14) (Reg.operands [.gpr 14] [])) #v[60]
    (.letOp (n := 64) (.out 0x111346 (negR64Effect 0x111346 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[62]
    (.letOp (n := 65) (.out 0x111346 (negR64Effect 0x111346 13) (EffectPart.reads (.flag .CF) [.gpr 13] []) (.flag .CF)) #v[62]
    (.letOp (n := 66) (.exec 0x111346 (fun s => s.RIP = 0x111346) (negR64Effect 0x111346 13) (Reg.operands [.gpr 13] [])) #v[62]
    (.letOp (n := 67) (.out 0x111349 (movR32Imm32Effect 0x111349 5 5 0x0) (EffectPart.reads (.reg (.gpr 5)) [] []) (.reg (.gpr 5))) #v[]
    (.letOp (n := 68) (.exec 0x111349 (fun s => s.RIP = 0x111349) (movR32Imm32Effect 0x111349 5 5 0x0) (Reg.operands [] [])) #v[]
    (.letOp (n := 69) (.out 0x11134e (atFlags StatusFlags.CF (sbbR64R64Effect 0x11134e 5 15)) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 5))) #v[67, 15, 65]
    (.letOp (n := 70) (.out 0x11134e (atFlags StatusFlags.CF (sbbR64R64Effect 0x11134e 5 15)) (Reg.operands [.gpr 5, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[67, 15, 65]
    (.letOp (n := 71) (.exec 0x11134e (fun s => s.RIP = 0x11134e) (atFlags StatusFlags.CF (sbbR64R64Effect 0x11134e 5 15)) (Reg.operands [.gpr 5, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[67, 15, 65]
    (.letOp (n := 72) (.out 0x111351 (movR32Imm32Effect 0x111351 6 8 0x0) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 73) (.exec 0x111351 (fun s => s.RIP = 0x111351) (movR32Imm32Effect 0x111351 6 8 0x0) (Reg.operands [] [])) #v[]
    (.letOp (n := 74) (.out 0x111357 (atFlags StatusFlags.CF (sbbR64R64Effect 0x111357 8 6)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[72, 6, 70]
    (.letOp (n := 75) (.out 0x111357 (atFlags StatusFlags.CF (sbbR64R64Effect 0x111357 8 6)) (Reg.operands [.gpr 8, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[72, 6, 70]
    (.letOp (n := 76) (.exec 0x111357 (fun s => s.RIP = 0x111357) (atFlags StatusFlags.CF (sbbR64R64Effect 0x111357 8 6)) (Reg.operands [.gpr 8, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[72, 6, 70]
    (.letOp (n := 77) (.out 0x11135a (movR32Imm32Effect 0x11135a 5 2 0x0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 78) (.exec 0x11135a (fun s => s.RIP = 0x11135a) (movR32Imm32Effect 0x11135a 5 2 0x0) (Reg.operands [] [])) #v[]
    (.letOp (n := 79) (.out 0x11135f (atFlags StatusFlags.CF (sbbR64R64Effect 0x11135f 2 0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[77, 0, 75]
    (.letOp (n := 80) (.out 0x11135f (atFlags StatusFlags.CF (sbbR64R64Effect 0x11135f 2 0)) (Reg.operands [.gpr 2, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[77, 0, 75]
    (.letOp (n := 81) (.exec 0x11135f (fun s => s.RIP = 0x11135f) (atFlags StatusFlags.CF (sbbR64R64Effect 0x11135f 2 0)) (Reg.operands [.gpr 2, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[77, 0, 75]
    (.letOp (n := 82) (.exec 0x111362 (StorePre 0x111362 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x111362 + BitVec.ofNat 64 4)) 1) (atFlags (condHolds 3) (setccM8Effect 0x111362 4 (.sib 4 none 0 .none))) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[4, 80]
    (.letOp (n := 83) (.exec 0x111366 (fun s => s.RIP = 0x111366) (movR64R64Effect 0x111366 6 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 84) (.out 0x111369 (movzxR32M8Effect 0x111369 4 6 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 85) (.exec 0x111369 (LoadPre 0x111369 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x111369 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x111369 4 6 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 86) (.exec 0x11136d (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x11136d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11136d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11136d 6 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[84, 4]
    (.letOp (n := 87) (.exec 0x111372 (StorePre 0x111372 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x111372 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x111372 4 11 (.sib 4 none 0 .none)) (Reg.operands [.gpr 11, .gpr 4] [])) #v[58, 4]
    (.letOp (n := 88) (.exec 0x111376 (fun s => s.RIP = 0x111376) (movR64R64Effect 0x111376 6 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.br ⟨.l116e59, RegMap.args [(0, 0), (1, 1), (2, 79), (3, 3), (4, 4), (5, 69), (7, 7), (8, 74), (9, 9), (10, 10), (11, 58), (12, 12), (13, 64), (14, 60), (15, 15), (16, 80), (22, 22), (39, 39), (51, 51)] 89⟩)))))))))))))))))))))))))))))))))))))

def bytes_l116e0f : List UInt8 :=
  [0x41, 0x89, 0xD3, 0x45, 0x30, 0xC3, 0x44, 0x88, 0x5C, 0x24, 0x10, 0x41, 0x80, 0xF3, 0x01, 0x4C,
    0x8B, 0x74, 0x24, 0x28, 0x4D, 0x89, 0xF5, 0x49, 0xF7, 0xDD, 0xBD, 0x00, 0x00, 0x00, 0x00, 0x4C,
    0x19, 0xFD, 0x41, 0xB8, 0x00, 0x00, 0x00, 0x00, 0x49, 0x19, 0xF0, 0xBA, 0x00, 0x00, 0x00, 0x00,
    0x48, 0x19, 0xC2, 0x0F, 0x93, 0x04, 0x24, 0x48, 0x89, 0xE6, 0x0F, 0xB6, 0x34, 0x24, 0x48, 0x89,
    0x74, 0x24, 0x38, 0x44, 0x88, 0x1C, 0x24, 0x48, 0x89, 0xE6]

theorem code_l116e0f : ∀ x ∈ codeRange 0x11132f bytes_l116e0f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1132f 74 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l116e59 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x111379 (xorR64R64Effect 0x111379 13 14) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 14] []) (.reg (.gpr 13))) #v[13, 14]
    (.letOp (n := 54) (.exec 0x111379 (fun s => s.RIP = 0x111379) (xorR64R64Effect 0x111379 13 14) (Reg.operands [.gpr 13, .gpr 14] [])) #v[13, 14]
    (.letOp (n := 55) (.out 0x11137c (movzxR32M8Effect 0x11137c 4 6 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 56) (.exec 0x11137c (LoadPre 0x11137c (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x11137c + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x11137c 4 6 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x111380 (negR64Effect 0x111380 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[55]
    (.letOp (n := 58) (.exec 0x111380 (fun s => s.RIP = 0x111380) (negR64Effect 0x111380 6) (Reg.operands [.gpr 6] [])) #v[55]
    (.letOp (n := 59) (.out 0x111383 (andR64R64Effect 0x111383 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 13] []) (.reg (.gpr 6))) #v[57, 53]
    (.letOp (n := 60) (.exec 0x111383 (fun s => s.RIP = 0x111383) (andR64R64Effect 0x111383 6 13) (Reg.operands [.gpr 6, .gpr 13] [])) #v[57, 53]
    (.letOp (n := 61) (.out 0x111386 (xorR64R64Effect 0x111386 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 14] []) (.reg (.gpr 6))) #v[59, 14]
    (.letOp (n := 62) (.exec 0x111386 (fun s => s.RIP = 0x111386) (xorR64R64Effect 0x111386 6 14) (Reg.operands [.gpr 6, .gpr 14] [])) #v[59, 14]
    (.letOp (n := 63) (.exec 0x111389 (StorePre 0x111389 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x111389 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x111389 4 11 (.sib 4 none 0 .none)) (Reg.operands [.gpr 11, .gpr 4] [])) #v[11, 4]
    (.letOp (n := 64) (.out 0x11138d (movR64R64Effect 0x11138d 14 4) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 65) (.exec 0x11138d (fun s => s.RIP = 0x11138d) (movR64R64Effect 0x11138d 14 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.out 0x111390 (xorR64R64Effect 0x111390 5 15) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 15] []) (.reg (.gpr 5))) #v[5, 15]
    (.letOp (n := 67) (.exec 0x111390 (fun s => s.RIP = 0x111390) (xorR64R64Effect 0x111390 5 15) (Reg.operands [.gpr 5, .gpr 15] [])) #v[5, 15]
    (.letOp (n := 68) (.out 0x111393 (movzxR32M8Effect 0x111393 5 13 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 69) (.exec 0x111393 (LoadPre 0x111393 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x111393 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x111393 5 13 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.out 0x111398 (negR64Effect 0x111398 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[68]
    (.letOp (n := 71) (.exec 0x111398 (fun s => s.RIP = 0x111398) (negR64Effect 0x111398 13) (Reg.operands [.gpr 13] [])) #v[68]
    (.letOp (n := 72) (.out 0x11139b (andR64R64Effect 0x11139b 13 5) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 5] []) (.reg (.gpr 13))) #v[70, 66]
    (.letOp (n := 73) (.exec 0x11139b (fun s => s.RIP = 0x11139b) (andR64R64Effect 0x11139b 13 5) (Reg.operands [.gpr 13, .gpr 5] [])) #v[70, 66]
    (.letOp (n := 74) (.out 0x11139e (xorR64R64Effect 0x11139e 13 15) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 15] []) (.reg (.gpr 13))) #v[72, 15]
    (.letOp (n := 75) (.exec 0x11139e (fun s => s.RIP = 0x11139e) (xorR64R64Effect 0x11139e 13 15) (Reg.operands [.gpr 13, .gpr 15] [])) #v[72, 15]
    (.letOp (n := 76) (.exec 0x1113a1 (StorePre 0x1113a1 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1113a1 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1113a1 4 11 (.sib 4 none 0 .none)) (Reg.operands [.gpr 11, .gpr 4] [])) #v[11, 4]
    (.letOp (n := 77) (.exec 0x1113a5 (fun s => s.RIP = 0x1113a5) (movR64R64Effect 0x1113a5 15 14) (Reg.operands [.gpr 14] [])) #v[64]
    (.letOp (n := 78) (.out 0x1113a8 (movR64M64Effect 0x1113a8 14 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 79) (.exec 0x1113a8 (LoadPre 0x1113a8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1113a8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1113a8 14 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 80) (.out 0x1113ad (xorR64R64Effect 0x1113ad 8 14) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 14] []) (.reg (.gpr 8))) #v[8, 78]
    (.letOp (n := 81) (.exec 0x1113ad (fun s => s.RIP = 0x1113ad) (xorR64R64Effect 0x1113ad 8 14) (Reg.operands [.gpr 8, .gpr 14] [])) #v[8, 78]
    (.letOp (n := 82) (.out 0x1113b0 (movzxR32M8Effect 0x1113b0 4 5 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 83) (.exec 0x1113b0 (LoadPre 0x1113b0 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1113b0 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x1113b0 4 5 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 84) (.out 0x1113b4 (negR64Effect 0x1113b4 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5] []) (.reg (.gpr 5))) #v[82]
    (.letOp (n := 85) (.exec 0x1113b4 (fun s => s.RIP = 0x1113b4) (negR64Effect 0x1113b4 5) (Reg.operands [.gpr 5] [])) #v[82]
    (.letOp (n := 86) (.out 0x1113b7 (andR64R64Effect 0x1113b7 5 8) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 8] []) (.reg (.gpr 5))) #v[84, 80]
    (.letOp (n := 87) (.exec 0x1113b7 (fun s => s.RIP = 0x1113b7) (andR64R64Effect 0x1113b7 5 8) (Reg.operands [.gpr 5, .gpr 8] [])) #v[84, 80]
    (.letOp (n := 88) (.out 0x1113ba (xorR64R64Effect 0x1113ba 5 14) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 14] []) (.reg (.gpr 5))) #v[86, 78]
    (.letOp (n := 89) (.exec 0x1113ba (fun s => s.RIP = 0x1113ba) (xorR64R64Effect 0x1113ba 5 14) (Reg.operands [.gpr 5, .gpr 14] [])) #v[86, 78]
    (.terminate (.br ⟨.l116e9d, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 88), (6, 61), (7, 7), (8, 80), (9, 9), (10, 10), (11, 11), (12, 12), (13, 74), (14, 78), (22, 22), (39, 39), (51, 51)] 90⟩))))))))))))))))))))))))))))))))))))))

def bytes_l116e59 : List UInt8 :=
  [0x4D, 0x31, 0xF5, 0x0F, 0xB6, 0x34, 0x24, 0x48, 0xF7, 0xDE, 0x4C, 0x21, 0xEE, 0x4C, 0x31, 0xF6,
    0x44, 0x88, 0x1C, 0x24, 0x49, 0x89, 0xE6, 0x4C, 0x31, 0xFD, 0x44, 0x0F, 0xB6, 0x2C, 0x24, 0x49,
    0xF7, 0xDD, 0x49, 0x21, 0xED, 0x4D, 0x31, 0xFD, 0x44, 0x88, 0x1C, 0x24, 0x4D, 0x89, 0xF7, 0x4C,
    0x8B, 0x74, 0x24, 0x30, 0x4D, 0x31, 0xF0, 0x0F, 0xB6, 0x2C, 0x24, 0x48, 0xF7, 0xDD, 0x4C, 0x21,
    0xC5, 0x4C, 0x31, 0xF5]

theorem code_l116e59 : ∀ x ∈ codeRange 0x111379 bytes_l116e59, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x11379 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l116e9d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1113bd (StorePre 0x1113bd 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1113bd + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1113bd 4 11 (.sib 4 none 0 .none)) (Reg.operands [.gpr 11, .gpr 4] [])) #v[11, 4]
    (.letOp (n := 54) (.out 0x1113c1 (xorR64R64Effect 0x1113c1 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[2, 0]
    (.letOp (n := 55) (.exec 0x1113c1 (fun s => s.RIP = 0x1113c1) (xorR64R64Effect 0x1113c1 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[2, 0]
    (.letOp (n := 56) (.out 0x1113c4 (movzxR32M8Effect 0x1113c4 5 15 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 57) (.exec 0x1113c4 (LoadPre 0x1113c4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1113c4 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1113c4 5 15 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.out 0x1113c9 (negR64Effect 0x1113c9 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15] []) (.reg (.gpr 15))) #v[56]
    (.letOp (n := 59) (.exec 0x1113c9 (fun s => s.RIP = 0x1113c9) (negR64Effect 0x1113c9 15) (Reg.operands [.gpr 15] [])) #v[56]
    (.letOp (n := 60) (.out 0x1113cc (andR64R64Effect 0x1113cc 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 2] []) (.reg (.gpr 15))) #v[58, 54]
    (.letOp (n := 61) (.exec 0x1113cc (fun s => s.RIP = 0x1113cc) (andR64R64Effect 0x1113cc 15 2) (Reg.operands [.gpr 15, .gpr 2] [])) #v[58, 54]
    (.letOp (n := 62) (.out 0x1113cf (xorR64R64Effect 0x1113cf 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 0] []) (.reg (.gpr 15))) #v[60, 0]
    (.letOp (n := 63) (.exec 0x1113cf (fun s => s.RIP = 0x1113cf) (xorR64R64Effect 0x1113cf 15 0) (Reg.operands [.gpr 15, .gpr 0] [])) #v[60, 0]
    (.letOp (n := 64) (.exec 0x1113d2 (StorePre 0x1113d2 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1113d2 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1113d2 4 11 (.sib 4 none 0 .none)) (Reg.operands [.gpr 11, .gpr 4] [])) #v[11, 4]
    (.letOp (n := 65) (.exec 0x1113d6 (fun s => s.RIP = 0x1113d6) (movR64R64Effect 0x1113d6 0 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.br ⟨.l116eb9, RegMap.args [(1, 1), (2, 54), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 62), (22, 22), (39, 39), (51, 51)] 66⟩))))))))))))))

def bytes_l116e9d : List UInt8 :=
  [0x44, 0x88, 0x1C, 0x24, 0x48, 0x31, 0xC2, 0x44, 0x0F, 0xB6, 0x3C, 0x24, 0x49, 0xF7, 0xDF, 0x49,
    0x21, 0xD7, 0x49, 0x31, 0xC7, 0x44, 0x88, 0x1C, 0x24, 0x48, 0x89, 0xE0]

theorem code_l116e9d : ∀ x ∈ codeRange 0x1113bd bytes_l116e9d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x113bd 28 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l116eb9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1113d9 (movR64R64Effect 0x1113d9 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[10]
    (.letOp (n := 54) (.exec 0x1113d9 (fun s => s.RIP = 0x1113d9) (movR64R64Effect 0x1113d9 0 10) (Reg.operands [.gpr 10] [])) #v[10]
    (.letOp (n := 55) (.out 0x1113dc (subR64R64Effect 0x1113dc 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[53, 6]
    (.letOp (n := 56) (.exec 0x1113dc (fun s => s.RIP = 0x1113dc) (subR64R64Effect 0x1113dc 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[53, 6]
    (.letOp (n := 57) (.out 0x1113df (notR64Effect 0x1113df 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[10]
    (.letOp (n := 58) (.exec 0x1113df (fun s => s.RIP = 0x1113df) (notR64Effect 0x1113df 10) (Reg.operands [.gpr 10] [])) #v[10]
    (.letOp (n := 59) (.out 0x1113e2 (movR64R64Effect 0x1113e2 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6] []) (.reg (.gpr 2))) #v[6]
    (.letOp (n := 60) (.exec 0x1113e2 (fun s => s.RIP = 0x1113e2) (movR64R64Effect 0x1113e2 2 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 61) (.out 0x1113e5 (andR64R64Effect 0x1113e5 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 10] []) (.reg (.gpr 2))) #v[59, 57]
    (.letOp (n := 62) (.exec 0x1113e5 (fun s => s.RIP = 0x1113e5) (andR64R64Effect 0x1113e5 2 10) (Reg.operands [.gpr 2, .gpr 10] [])) #v[59, 57]
    (.letOp (n := 63) (.out 0x1113e8 (orR64R64Effect 0x1113e8 10 6) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 6] []) (.reg (.gpr 10))) #v[57, 6]
    (.letOp (n := 64) (.exec 0x1113e8 (fun s => s.RIP = 0x1113e8) (orR64R64Effect 0x1113e8 10 6) (Reg.operands [.gpr 10, .gpr 6] [])) #v[57, 6]
    (.letOp (n := 65) (.out 0x1113eb (andR64R64Effect 0x1113eb 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0] []) (.reg (.gpr 10))) #v[63, 55]
    (.letOp (n := 66) (.exec 0x1113eb (fun s => s.RIP = 0x1113eb) (andR64R64Effect 0x1113eb 10 0) (Reg.operands [.gpr 10, .gpr 0] [])) #v[63, 55]
    (.letOp (n := 67) (.out 0x1113ee (orR64R64Effect 0x1113ee 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2] []) (.reg (.gpr 10))) #v[65, 61]
    (.letOp (n := 68) (.exec 0x1113ee (fun s => s.RIP = 0x1113ee) (orR64R64Effect 0x1113ee 10 2) (Reg.operands [.gpr 10, .gpr 2] [])) #v[65, 61]
    (.letOp (n := 69) (.out 0x1113f1 (shrR64Effect 0x1113f1 4 10 63) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[67]
    (.letOp (n := 70) (.exec 0x1113f1 (fun s => s.RIP = 0x1113f1) (shrR64Effect 0x1113f1 4 10 63) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[67]
    (.letOp (n := 71) (.out 0x1113f5 (movzxR32M8Effect 0x1113f5 5 14 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 72) (.exec 0x1113f5 (LoadPre 0x1113f5 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1113f5 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1113f5 5 14 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.exec 0x1113fa (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1113fa 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1113fa + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1113fa 10 (.sib 4 none 0 .none)) (Reg.operands [.gpr 10, .gpr 4] [])) #v[69, 4]
    (.terminate (.br ⟨.l116ede, RegMap.args [(0, 55), (1, 1), (2, 61), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 69), (12, 12), (13, 13), (14, 71), (15, 15), (22, 22), (39, 39), (51, 51)] 74⟩))))))))))))))))))))))

def bytes_l116eb9 : List UInt8 :=
  [0x4C, 0x89, 0xD0, 0x48, 0x29, 0xF0, 0x49, 0xF7, 0xD2, 0x48, 0x89, 0xF2, 0x4C, 0x21, 0xD2, 0x49,
    0x09, 0xF2, 0x49, 0x21, 0xC2, 0x49, 0x09, 0xD2, 0x49, 0xC1, 0xEA, 0x3F, 0x44, 0x0F, 0xB6, 0x34,
    0x24, 0x4C, 0x89, 0x14, 0x24]

theorem code_l116eb9 : ∀ x ∈ codeRange 0x1113d9 bytes_l116eb9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x113d9 37 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l116ede : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1113fe (fun s => s.RIP = 0x1113fe) (movR64R64Effect 0x1113fe 11 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.out 0x111401 (xorR32R32Effect 0x111401 3 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 8] []) (.reg (.gpr 8))) #v[8, 8]
    (.letOp (n := 55) (.exec 0x111401 (fun s => s.RIP = 0x111401) (xorR32R32Effect 0x111401 3 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[8, 8]
    (.letOp (n := 56) (.out 0x111404 (subR64M64Effect 0x111404 8 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 4] []) (.reg (.gpr 8))) #v[54, 4]
    (.letOp (n := 57) (.exec 0x111404 (LoadPre 0x111404 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x111404 + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x111404 8 (.sib 4 none 0 .none)) (Reg.operands [.gpr 8, .gpr 4] [])) #v[54, 4]
    (.letOp (n := 58) (.out 0x111408 (movR64R64Effect 0x111408 2 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9] []) (.reg (.gpr 2))) #v[9]
    (.letOp (n := 59) (.exec 0x111408 (fun s => s.RIP = 0x111408) (movR64R64Effect 0x111408 2 9) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 60) (.out 0x11140b (subR64R64Effect 0x11140b 2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 13] []) (.reg (.gpr 2))) #v[58, 13]
    (.letOp (n := 61) (.exec 0x11140b (fun s => s.RIP = 0x11140b) (subR64R64Effect 0x11140b 2 13) (Reg.operands [.gpr 2, .gpr 13] [])) #v[58, 13]
    (.letOp (n := 62) (.out 0x11140e (sarR64Effect 0x11140e 4 8 63) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[56]
    (.letOp (n := 63) (.exec 0x11140e (fun s => s.RIP = 0x11140e) (sarR64Effect 0x11140e 4 8 63) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[56]
    (.letOp (n := 64) (.out 0x111412 (addR64R64Effect 0x111412 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2] []) (.reg (.gpr 8))) #v[62, 60]
    (.letOp (n := 65) (.exec 0x111412 (fun s => s.RIP = 0x111412) (addR64R64Effect 0x111412 8 2) (Reg.operands [.gpr 8, .gpr 2] [])) #v[62, 60]
    (.letOp (n := 66) (.out 0x111415 (notR64Effect 0x111415 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[9]
    (.letOp (n := 67) (.exec 0x111415 (fun s => s.RIP = 0x111415) (notR64Effect 0x111415 9) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 68) (.out 0x111418 (movR64R64Effect 0x111418 2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13] []) (.reg (.gpr 2))) #v[13]
    (.letOp (n := 69) (.exec 0x111418 (fun s => s.RIP = 0x111418) (movR64R64Effect 0x111418 2 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 70) (.out 0x11141b (andR64R64Effect 0x11141b 2 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 9] []) (.reg (.gpr 2))) #v[68, 66]
    (.letOp (n := 71) (.exec 0x11141b (fun s => s.RIP = 0x11141b) (andR64R64Effect 0x11141b 2 9) (Reg.operands [.gpr 2, .gpr 9] [])) #v[68, 66]
    (.letOp (n := 72) (.out 0x11141e (orR64R64Effect 0x11141e 9 13) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 13] []) (.reg (.gpr 9))) #v[66, 13]
    (.letOp (n := 73) (.exec 0x11141e (fun s => s.RIP = 0x11141e) (orR64R64Effect 0x11141e 9 13) (Reg.operands [.gpr 9, .gpr 13] [])) #v[66, 13]
    (.letOp (n := 74) (.out 0x111421 (andR64R64Effect 0x111421 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8] []) (.reg (.gpr 9))) #v[72, 64]
    (.letOp (n := 75) (.exec 0x111421 (fun s => s.RIP = 0x111421) (andR64R64Effect 0x111421 9 8) (Reg.operands [.gpr 9, .gpr 8] [])) #v[72, 64]
    (.letOp (n := 76) (.out 0x111424 (orR64R64Effect 0x111424 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2] []) (.reg (.gpr 9))) #v[74, 70]
    (.letOp (n := 77) (.exec 0x111424 (fun s => s.RIP = 0x111424) (orR64R64Effect 0x111424 9 2) (Reg.operands [.gpr 9, .gpr 2] [])) #v[74, 70]
    (.letOp (n := 78) (.out 0x111427 (shrR64Effect 0x111427 4 9 63) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[76]
    (.letOp (n := 79) (.exec 0x111427 (fun s => s.RIP = 0x111427) (shrR64Effect 0x111427 4 9 63) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[76]
    (.terminate (.br ⟨.l116f0b, RegMap.args [(0, 0), (1, 1), (2, 70), (3, 3), (4, 4), (5, 5), (7, 7), (8, 64), (9, 78), (10, 10), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)] 80⟩))))))))))))))))))))))))))))

def bytes_l116ede : List UInt8 :=
  [0x49, 0x89, 0xE3, 0x45, 0x31, 0xC0, 0x4C, 0x2B, 0x04, 0x24, 0x4C, 0x89, 0xCA, 0x4C, 0x29, 0xEA,
    0x49, 0xC1, 0xF8, 0x3F, 0x49, 0x01, 0xD0, 0x49, 0xF7, 0xD1, 0x4C, 0x89, 0xEA, 0x4C, 0x21, 0xCA,
    0x4D, 0x09, 0xE9, 0x4D, 0x21, 0xC1, 0x49, 0x09, 0xD1, 0x49, 0xC1, 0xE9, 0x3F]

theorem code_l116ede : ∀ x ∈ codeRange 0x1113fe bytes_l116ede, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x113fe 45 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l116f0b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x11142b (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x11142b 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x11142b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11142b 9 (.sib 4 none 0 .none)) (Reg.operands [.gpr 9, .gpr 4] [])) #v[9, 4]
    (.letOp (n := 54) (.out 0x11142f (xorR32R32Effect 0x11142f 3 9 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 9] []) (.reg (.gpr 9))) #v[9, 9]
    (.letOp (n := 55) (.exec 0x11142f (fun s => s.RIP = 0x11142f) (xorR32R32Effect 0x11142f 3 9 9) (Reg.operands [.gpr 9, .gpr 9] [])) #v[9, 9]
    (.letOp (n := 56) (.out 0x111432 (subR64M64Effect 0x111432 9 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 4] []) (.reg (.gpr 9))) #v[54, 4]
    (.letOp (n := 57) (.exec 0x111432 (LoadPre 0x111432 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x111432 + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x111432 9 (.sib 4 none 0 .none)) (Reg.operands [.gpr 9, .gpr 4] [])) #v[54, 4]
    (.letOp (n := 58) (.out 0x111436 (movR64R64Effect 0x111436 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12] []) (.reg (.gpr 2))) #v[12]
    (.letOp (n := 59) (.exec 0x111436 (fun s => s.RIP = 0x111436) (movR64R64Effect 0x111436 2 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 60) (.out 0x111439 (subR64R64Effect 0x111439 2 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 5] []) (.reg (.gpr 2))) #v[58, 5]
    (.letOp (n := 61) (.exec 0x111439 (fun s => s.RIP = 0x111439) (subR64R64Effect 0x111439 2 5) (Reg.operands [.gpr 2, .gpr 5] [])) #v[58, 5]
    (.letOp (n := 62) (.out 0x11143c (sarR64Effect 0x11143c 4 9 63) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[56]
    (.letOp (n := 63) (.exec 0x11143c (fun s => s.RIP = 0x11143c) (sarR64Effect 0x11143c 4 9 63) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[56]
    (.letOp (n := 64) (.out 0x111440 (addR64R64Effect 0x111440 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2] []) (.reg (.gpr 9))) #v[62, 60]
    (.letOp (n := 65) (.exec 0x111440 (fun s => s.RIP = 0x111440) (addR64R64Effect 0x111440 9 2) (Reg.operands [.gpr 9, .gpr 2] [])) #v[62, 60]
    (.letOp (n := 66) (.out 0x111443 (notR64Effect 0x111443 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[12]
    (.letOp (n := 67) (.exec 0x111443 (fun s => s.RIP = 0x111443) (notR64Effect 0x111443 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 68) (.out 0x111446 (movR64R64Effect 0x111446 2 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5] []) (.reg (.gpr 2))) #v[5]
    (.letOp (n := 69) (.exec 0x111446 (fun s => s.RIP = 0x111446) (movR64R64Effect 0x111446 2 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 70) (.out 0x111449 (andR64R64Effect 0x111449 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 12] []) (.reg (.gpr 2))) #v[68, 66]
    (.letOp (n := 71) (.exec 0x111449 (fun s => s.RIP = 0x111449) (andR64R64Effect 0x111449 2 12) (Reg.operands [.gpr 2, .gpr 12] [])) #v[68, 66]
    (.letOp (n := 72) (.out 0x11144c (orR64R64Effect 0x11144c 12 5) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 5] []) (.reg (.gpr 12))) #v[66, 5]
    (.letOp (n := 73) (.exec 0x11144c (fun s => s.RIP = 0x11144c) (orR64R64Effect 0x11144c 12 5) (Reg.operands [.gpr 12, .gpr 5] [])) #v[66, 5]
    (.letOp (n := 74) (.out 0x11144f (andR64R64Effect 0x11144f 12 9) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 9] []) (.reg (.gpr 12))) #v[72, 64]
    (.letOp (n := 75) (.exec 0x11144f (fun s => s.RIP = 0x11144f) (andR64R64Effect 0x11144f 12 9) (Reg.operands [.gpr 12, .gpr 9] [])) #v[72, 64]
    (.letOp (n := 76) (.out 0x111452 (orR64R64Effect 0x111452 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 2] []) (.reg (.gpr 12))) #v[74, 70]
    (.letOp (n := 77) (.exec 0x111452 (fun s => s.RIP = 0x111452) (orR64R64Effect 0x111452 12 2) (Reg.operands [.gpr 12, .gpr 2] [])) #v[74, 70]
    (.letOp (n := 78) (.out 0x111455 (shrR64Effect 0x111455 4 12 63) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[76]
    (.letOp (n := 79) (.exec 0x111455 (fun s => s.RIP = 0x111455) (shrR64Effect 0x111455 4 12 63) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[76]
    (.terminate (.br ⟨.l116f39, RegMap.args [(0, 0), (1, 1), (2, 70), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 64), (10, 10), (12, 78), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)] 80⟩))))))))))))))))))))))))))))

def bytes_l116f0b : List UInt8 :=
  [0x4C, 0x89, 0x0C, 0x24, 0x45, 0x31, 0xC9, 0x4C, 0x2B, 0x0C, 0x24, 0x4C, 0x89, 0xE2, 0x48, 0x29,
    0xEA, 0x49, 0xC1, 0xF9, 0x3F, 0x49, 0x01, 0xD1, 0x49, 0xF7, 0xD4, 0x48, 0x89, 0xEA, 0x4C, 0x21,
    0xE2, 0x49, 0x09, 0xEC, 0x4D, 0x21, 0xCC, 0x49, 0x09, 0xD4, 0x49, 0xC1, 0xEC, 0x3F]

theorem code_l116f0b : ∀ x ∈ codeRange 0x11142b bytes_l116f0b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1142b 46 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l116f39 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x111459 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111459 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x111459 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x111459 12 (.sib 4 none 0 .none)) (Reg.operands [.gpr 12, .gpr 4] [])) #v[12, 4]
    (.letOp (n := 54) (.out 0x11145d (xorR32R32Effect 0x11145d 3 10 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 10] []) (.reg (.gpr 10))) #v[10, 10]
    (.letOp (n := 55) (.exec 0x11145d (fun s => s.RIP = 0x11145d) (xorR32R32Effect 0x11145d 3 10 10) (Reg.operands [.gpr 10, .gpr 10] [])) #v[10, 10]
    (.letOp (n := 56) (.out 0x111460 (subR64M64Effect 0x111460 10 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 4] []) (.reg (.gpr 10))) #v[54, 4]
    (.letOp (n := 57) (.exec 0x111460 (LoadPre 0x111460 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x111460 + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x111460 10 (.sib 4 none 0 .none)) (Reg.operands [.gpr 10, .gpr 4] [])) #v[54, 4]
    (.letOp (n := 58) (.out 0x111464 (movR64R64Effect 0x111464 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3] []) (.reg (.gpr 2))) #v[3]
    (.letOp (n := 59) (.exec 0x111464 (fun s => s.RIP = 0x111464) (movR64R64Effect 0x111464 2 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 60) (.out 0x111467 (subR64R64Effect 0x111467 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 15] []) (.reg (.gpr 2))) #v[58, 15]
    (.letOp (n := 61) (.exec 0x111467 (fun s => s.RIP = 0x111467) (subR64R64Effect 0x111467 2 15) (Reg.operands [.gpr 2, .gpr 15] [])) #v[58, 15]
    (.letOp (n := 62) (.out 0x11146a (sarR64Effect 0x11146a 4 10 63) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[56]
    (.letOp (n := 63) (.exec 0x11146a (fun s => s.RIP = 0x11146a) (sarR64Effect 0x11146a 4 10 63) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[56]
    (.letOp (n := 64) (.out 0x11146e (addR64R64Effect 0x11146e 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2] []) (.reg (.gpr 10))) #v[62, 60]
    (.letOp (n := 65) (.exec 0x11146e (fun s => s.RIP = 0x11146e) (addR64R64Effect 0x11146e 10 2) (Reg.operands [.gpr 10, .gpr 2] [])) #v[62, 60]
    (.letOp (n := 66) (.out 0x111471 (notR64Effect 0x111471 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[3]
    (.letOp (n := 67) (.exec 0x111471 (fun s => s.RIP = 0x111471) (notR64Effect 0x111471 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 68) (.out 0x111474 (movR64R64Effect 0x111474 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15] []) (.reg (.gpr 2))) #v[15]
    (.letOp (n := 69) (.exec 0x111474 (fun s => s.RIP = 0x111474) (movR64R64Effect 0x111474 2 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 70) (.out 0x111477 (andR64R64Effect 0x111477 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 3] []) (.reg (.gpr 2))) #v[68, 66]
    (.letOp (n := 71) (.exec 0x111477 (fun s => s.RIP = 0x111477) (andR64R64Effect 0x111477 2 3) (Reg.operands [.gpr 2, .gpr 3] [])) #v[68, 66]
    (.letOp (n := 72) (.out 0x11147a (orR64R64Effect 0x11147a 3 15) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 15] []) (.reg (.gpr 3))) #v[66, 15]
    (.letOp (n := 73) (.exec 0x11147a (fun s => s.RIP = 0x11147a) (orR64R64Effect 0x11147a 3 15) (Reg.operands [.gpr 3, .gpr 15] [])) #v[66, 15]
    (.letOp (n := 74) (.out 0x11147d (andR64R64Effect 0x11147d 3 10) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 10] []) (.reg (.gpr 3))) #v[72, 64]
    (.letOp (n := 75) (.exec 0x11147d (fun s => s.RIP = 0x11147d) (andR64R64Effect 0x11147d 3 10) (Reg.operands [.gpr 3, .gpr 10] [])) #v[72, 64]
    (.letOp (n := 76) (.out 0x111480 (orR64R64Effect 0x111480 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 2] []) (.reg (.gpr 3))) #v[74, 70]
    (.letOp (n := 77) (.exec 0x111480 (fun s => s.RIP = 0x111480) (orR64R64Effect 0x111480 3 2) (Reg.operands [.gpr 3, .gpr 2] [])) #v[74, 70]
    (.letOp (n := 78) (.out 0x111483 (shrR64Effect 0x111483 4 3 63) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[76]
    (.letOp (n := 79) (.exec 0x111483 (fun s => s.RIP = 0x111483) (shrR64Effect 0x111483 4 3 63) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[76]
    (.terminate (.br ⟨.l116f67, RegMap.args [(0, 0), (1, 1), (2, 70), (3, 78), (4, 4), (7, 7), (8, 8), (9, 9), (10, 64), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)] 80⟩))))))))))))))))))))))))))))

def bytes_l116f39 : List UInt8 :=
  [0x4C, 0x89, 0x24, 0x24, 0x45, 0x31, 0xD2, 0x4C, 0x2B, 0x14, 0x24, 0x48, 0x89, 0xDA, 0x4C, 0x29,
    0xFA, 0x49, 0xC1, 0xFA, 0x3F, 0x49, 0x01, 0xD2, 0x48, 0xF7, 0xD3, 0x4C, 0x89, 0xFA, 0x48, 0x21,
    0xDA, 0x4C, 0x09, 0xFB, 0x4C, 0x21, 0xD3, 0x48, 0x09, 0xD3, 0x48, 0xC1, 0xEB, 0x3F]

theorem code_l116f39 : ∀ x ∈ codeRange 0x111459 bytes_l116f39, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x11459 46 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l116f67_1 : Block Op Label signature Reg.count 92 :=
  .letOp (n := 92) (.out 0x1114ca (addR64R64Effect 0x1114ca 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 2] []) (.reg (.gpr 3))) #v[90, 80]
    (.letOp (n := 93) (.exec 0x1114ca (fun s => s.RIP = 0x1114ca) (addR64R64Effect 0x1114ca 3 2) (Reg.operands [.gpr 3, .gpr 2] [])) #v[90, 80]
    (.letOp (n := 94) (.out 0x1114cd (andR64R64Effect 0x1114cd 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 3] []) (.reg (.gpr 1))) #v[88, 92]
    (.letOp (n := 95) (.exec 0x1114cd (fun s => s.RIP = 0x1114cd) (andR64R64Effect 0x1114cd 1 3) (Reg.operands [.gpr 1, .gpr 3] [])) #v[88, 92]
    (.letOp (n := 96) (.out 0x1114d0 (orR64R64Effect 0x1114d0 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[94, 86]
    (.letOp (n := 97) (.exec 0x1114d0 (fun s => s.RIP = 0x1114d0) (orR64R64Effect 0x1114d0 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[94, 86]
    (.letOp (n := 98) (.out 0x1114d3 (shrR64Effect 0x1114d3 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[96]
    (.letOp (n := 99) (.exec 0x1114d3 (fun s => s.RIP = 0x1114d3) (shrR64Effect 0x1114d3 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[96]
    (.letOp (n := 100) (.exec 0x1114d7 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1114d7 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1114d7 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1114d7 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 1, .gpr 4] [])) #v[98, 4]
    (.terminate (.br ⟨.l116fbb, RegMap.args [(0, 0), (1, 98), (2, 80), (3, 92), (4, 4), (6, 86), (7, 7), (8, 8), (9, 9), (10, 10), (11, 60), (14, 76), (22, 22), (39, 39), (51, 51)] 101⟩))))))))))

def bytes_l116f67_1 : List UInt8 :=
  [0x48, 0x01, 0xD3, 0x48, 0x21, 0xD9, 0x48, 0x09, 0xF1, 0x48, 0xC1, 0xE9, 0x3F, 0x48, 0x89, 0x0C,
    0x24]

theorem code_l116f67_1 : ∀ x ∈ codeRange 0x1114ca bytes_l116f67_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x114ca 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l116f67 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x111487 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111487 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x111487 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x111487 3 (.sib 4 none 0 .none)) (Reg.operands [.gpr 3, .gpr 4] [])) #v[3, 4]
    (.letOp (n := 54) (.out 0x11148b (xorR32R32Effect 0x11148b 2 3 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 3] []) (.reg (.gpr 3))) #v[3, 3]
    (.letOp (n := 55) (.exec 0x11148b (fun s => s.RIP = 0x11148b) (xorR32R32Effect 0x11148b 2 3 3) (Reg.operands [.gpr 3, .gpr 3] [])) #v[3, 3]
    (.letOp (n := 56) (.out 0x11148d (subR64M64Effect 0x11148d 3 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 4] []) (.reg (.gpr 3))) #v[54, 4]
    (.letOp (n := 57) (.exec 0x11148d (LoadPre 0x11148d (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x11148d + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x11148d 3 (.sib 4 none 0 .none)) (Reg.operands [.gpr 3, .gpr 4] [])) #v[54, 4]
    (.letOp (n := 58) (.out 0x111491 (movR64M64Effect 0x111491 11 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 59) (.exec 0x111491 (LoadPre 0x111491 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x111491 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111491 11 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.out 0x111496 (andR32Imm8Effect 0x111496 4 11 0x1) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11] []) (.reg (.gpr 11))) #v[58]
    (.letOp (n := 61) (.exec 0x111496 (fun s => s.RIP = 0x111496) (andR32Imm8Effect 0x111496 4 11 0x1) (Reg.operands [.gpr 11] [])) #v[58]
    (.letOp (n := 62) (.out 0x11149a (movR64M64Effect 0x11149a 6 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 63) (.exec 0x11149a (LoadPre 0x11149a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11149a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11149a 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x11149f (movR64R64Effect 0x11149f 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6] []) (.reg (.gpr 2))) #v[62]
    (.letOp (n := 65) (.exec 0x11149f (fun s => s.RIP = 0x11149f) (movR64R64Effect 0x11149f 2 6) (Reg.operands [.gpr 6] [])) #v[62]
    (.letOp (n := 66) (.out 0x1114a2 (notR64Effect 0x1114a2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[64]
    (.letOp (n := 67) (.exec 0x1114a2 (fun s => s.RIP = 0x1114a2) (notR64Effect 0x1114a2 2) (Reg.operands [.gpr 2] [])) #v[64]
    (.letOp (n := 68) (.out 0x1114a5 (addR64R64Effect 0x1114a5 2 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 11] []) (.reg (.gpr 2))) #v[66, 60]
    (.letOp (n := 69) (.exec 0x1114a5 (fun s => s.RIP = 0x1114a5) (addR64R64Effect 0x1114a5 2 11) (Reg.operands [.gpr 2, .gpr 11] [])) #v[66, 60]
    (.letOp (n := 70) (.out 0x1114a8 (xorR64R64Effect 0x1114a8 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[68, 62]
    (.letOp (n := 71) (.exec 0x1114a8 (fun s => s.RIP = 0x1114a8) (xorR64R64Effect 0x1114a8 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[68, 62]
    (.letOp (n := 72) (.out 0x1114ab (negR64Effect 0x1114ab 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14] []) (.reg (.gpr 14))) #v[14]
    (.letOp (n := 73) (.exec 0x1114ab (fun s => s.RIP = 0x1114ab) (negR64Effect 0x1114ab 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 74) (.out 0x1114ae (andR64R64Effect 0x1114ae 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 2] []) (.reg (.gpr 14))) #v[72, 70]
    (.letOp (n := 75) (.exec 0x1114ae (fun s => s.RIP = 0x1114ae) (andR64R64Effect 0x1114ae 14 2) (Reg.operands [.gpr 14, .gpr 2] [])) #v[72, 70]
    (.letOp (n := 76) (.out 0x1114b1 (xorR64R64Effect 0x1114b1 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 6] []) (.reg (.gpr 14))) #v[74, 62]
    (.letOp (n := 77) (.exec 0x1114b1 (fun s => s.RIP = 0x1114b1) (xorR64R64Effect 0x1114b1 14 6) (Reg.operands [.gpr 14, .gpr 6] [])) #v[74, 62]
    (.letOp (n := 78) (.out 0x1114b4 (movR64R64Effect 0x1114b4 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[1]
    (.letOp (n := 79) (.exec 0x1114b4 (fun s => s.RIP = 0x1114b4) (movR64R64Effect 0x1114b4 2 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 80) (.out 0x1114b7 (subR64R64Effect 0x1114b7 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 14] []) (.reg (.gpr 2))) #v[78, 76]
    (.letOp (n := 81) (.exec 0x1114b7 (fun s => s.RIP = 0x1114b7) (subR64R64Effect 0x1114b7 2 14) (Reg.operands [.gpr 2, .gpr 14] [])) #v[78, 76]
    (.letOp (n := 82) (.out 0x1114ba (notR64Effect 0x1114ba 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1]
    (.letOp (n := 83) (.exec 0x1114ba (fun s => s.RIP = 0x1114ba) (notR64Effect 0x1114ba 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 84) (.out 0x1114bd (movR64R64Effect 0x1114bd 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[76]
    (.letOp (n := 85) (.exec 0x1114bd (fun s => s.RIP = 0x1114bd) (movR64R64Effect 0x1114bd 6 14) (Reg.operands [.gpr 14] [])) #v[76]
    (.letOp (n := 86) (.out 0x1114c0 (andR64R64Effect 0x1114c0 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[84, 82]
    (.letOp (n := 87) (.exec 0x1114c0 (fun s => s.RIP = 0x1114c0) (andR64R64Effect 0x1114c0 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[84, 82]
    (.letOp (n := 88) (.out 0x1114c3 (orR64R64Effect 0x1114c3 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 14] []) (.reg (.gpr 1))) #v[82, 76]
    (.letOp (n := 89) (.exec 0x1114c3 (fun s => s.RIP = 0x1114c3) (orR64R64Effect 0x1114c3 1 14) (Reg.operands [.gpr 1, .gpr 14] [])) #v[82, 76]
    (.letOp (n := 90) (.out 0x1114c6 (sarR64Effect 0x1114c6 4 3 63) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[56]
    (.letOp (n := 91) (.exec 0x1114c6 (fun s => s.RIP = 0x1114c6) (sarR64Effect 0x1114c6 4 3 63) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[56]
    (b_l116f67_1)))))))))))))))))))))))))))))))))))))))

def bytes_l116f67 : List UInt8 :=
  [0x48, 0x89, 0x1C, 0x24, 0x31, 0xDB, 0x48, 0x2B, 0x1C, 0x24, 0x4C, 0x8B, 0x5C, 0x24, 0x38, 0x41,
    0x83, 0xE3, 0x01, 0x48, 0x8B, 0x74, 0x24, 0x08, 0x48, 0x89, 0xF2, 0x48, 0xF7, 0xD2, 0x4C, 0x01,
    0xDA, 0x48, 0x31, 0xF2, 0x49, 0xF7, 0xDE, 0x49, 0x21, 0xD6, 0x49, 0x31, 0xF6, 0x48, 0x89, 0xCA,
    0x4C, 0x29, 0xF2, 0x48, 0xF7, 0xD1, 0x4C, 0x89, 0xF6, 0x48, 0x21, 0xCE, 0x4C, 0x09, 0xF1, 0x48,
    0xC1, 0xFB, 0x3F] ++ bytes_l116f67_1

theorem code_l116f67 : ∀ x ∈ codeRange 0x111487 bytes_l116f67, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x11487 67 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l116f67_1

@[cfg_block] def b_l116fbb : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1114db (fun s => s.RIP = 0x1114db) (movR64R64Effect 0x1114db 1 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.out 0x1114de (movzxR32M8Effect 0x1114de 5 1 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 55) (.exec 0x1114de (LoadPre 0x1114de (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1114de + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1114de 5 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x1114e3 (andR8Imm8Effect 0x1114e3 3 1 0x1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[54]
    (.letOp (n := 57) (.exec 0x1114e3 (fun s => s.RIP = 0x1114e3) (andR8Imm8Effect 0x1114e3 3 1 0x1) (Reg.operands [.gpr 1] [])) #v[54]
    (.letOp (n := 58) (.out 0x1114e6 (cmpMImm8Effect 0x1114e6 5 64 (.sib 4 none 0 .none) 0x0) (EffectPart.reads (.flag .ZF) [.gpr 4] []) (.flag .ZF)) #v[4]
    (.letOp (n := 59) (.exec 0x1114e6 (LoadPre 0x1114e6 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1114e6 + BitVec.ofNat 64 5)) 8) (cmpMImm8Effect 0x1114e6 5 64 (.sib 4 none 0 .none) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.out 0x1114eb (movzxR32R8Effect 0x1114eb 3 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[56]
    (.letOp (n := 61) (.exec 0x1114eb (fun s => s.RIP = 0x1114eb) (movzxR32R8Effect 0x1114eb 3 1 1) (Reg.operands [.gpr 1] [])) #v[56]
    (.letOp (n := 62) (.out 0x1114ee (movR32Imm32Effect 0x1114ee 6 13 0x0) (EffectPart.reads (.reg (.gpr 13)) [] []) (.reg (.gpr 13))) #v[]
    (.letOp (n := 63) (.exec 0x1114ee (fun s => s.RIP = 0x1114ee) (movR32Imm32Effect 0x1114ee 6 13 0x0) (Reg.operands [] [])) #v[]
    (.letOp (n := 64) (.out 0x1114f4 (atFlags (condHolds 4) (cmovR32R32Effect 0x1114f4 4 1 13)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 1))) #v[60, 62, 58]
    (.letOp (n := 65) (.exec 0x1114f4 (fun s => s.RIP = 0x1114f4) (atFlags (condHolds 4) (cmovR32R32Effect 0x1114f4 4 1 13)) (Reg.operands [.gpr 1, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[60, 62, 58]
    (.terminate (.br ⟨.l116fd8, RegMap.args [(0, 0), (1, 64), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (13, 62), (19, 58), (22, 22), (39, 39), (51, 51)] 66⟩))))))))))))))

def bytes_l116fbb : List UInt8 :=
  [0x48, 0x89, 0xE1, 0x0F, 0xB6, 0x4C, 0x24, 0x10, 0x80, 0xE1, 0x01, 0x48, 0x83, 0x3C, 0x24, 0x00,
    0x0F, 0xB6, 0xC9, 0x41, 0xBD, 0x00, 0x00, 0x00, 0x00, 0x41, 0x0F, 0x44, 0xCD]

theorem code_l116fbb : ∀ x ∈ codeRange 0x1114db bytes_l116fbb, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x114db 29 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l116fd8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1114f8 (movR64R64Effect 0x1114f8 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[0]
    (.letOp (n := 54) (.exec 0x1114f8 (fun s => s.RIP = 0x1114f8) (movR64R64Effect 0x1114f8 12 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x1114fb (negR64Effect 0x1114fb 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[53]
    (.letOp (n := 56) (.out 0x1114fb (negR64Effect 0x1114fb 12) (EffectPart.reads (.flag .CF) [.gpr 12] []) (.flag .CF)) #v[53]
    (.letOp (n := 57) (.exec 0x1114fb (fun s => s.RIP = 0x1114fb) (negR64Effect 0x1114fb 12) (Reg.operands [.gpr 12] [])) #v[53]
    (.letOp (n := 58) (.out 0x1114fe (movR32Imm32Effect 0x1114fe 6 14 0x0) (EffectPart.reads (.reg (.gpr 14)) [] []) (.reg (.gpr 14))) #v[]
    (.letOp (n := 59) (.exec 0x1114fe (fun s => s.RIP = 0x1114fe) (movR32Imm32Effect 0x1114fe 6 14 0x0) (Reg.operands [] [])) #v[]
    (.letOp (n := 60) (.out 0x111504 (atFlags StatusFlags.CF (sbbR64R64Effect 0x111504 14 8)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[58, 8, 56]
    (.letOp (n := 61) (.out 0x111504 (atFlags StatusFlags.CF (sbbR64R64Effect 0x111504 14 8)) (Reg.operands [.gpr 14, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[58, 8, 56]
    (.letOp (n := 62) (.exec 0x111504 (fun s => s.RIP = 0x111504) (atFlags StatusFlags.CF (sbbR64R64Effect 0x111504 14 8)) (Reg.operands [.gpr 14, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[58, 8, 56]
    (.letOp (n := 63) (.out 0x111507 (movR32Imm32Effect 0x111507 6 11 0x0) (EffectPart.reads (.reg (.gpr 11)) [] []) (.reg (.gpr 11))) #v[]
    (.letOp (n := 64) (.exec 0x111507 (fun s => s.RIP = 0x111507) (movR32Imm32Effect 0x111507 6 11 0x0) (Reg.operands [] [])) #v[]
    (.letOp (n := 65) (.out 0x11150d (atFlags StatusFlags.CF (sbbR64R64Effect 0x11150d 11 9)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[63, 9, 61]
    (.letOp (n := 66) (.out 0x11150d (atFlags StatusFlags.CF (sbbR64R64Effect 0x11150d 11 9)) (Reg.operands [.gpr 11, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[63, 9, 61]
    (.letOp (n := 67) (.exec 0x11150d (fun s => s.RIP = 0x11150d) (atFlags StatusFlags.CF (sbbR64R64Effect 0x11150d 11 9)) (Reg.operands [.gpr 11, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[63, 9, 61]
    (.letOp (n := 68) (.out 0x111510 (atFlags StatusFlags.CF (sbbR64R64Effect 0x111510 13 10)) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 13))) #v[13, 10, 66]
    (.letOp (n := 69) (.out 0x111510 (atFlags StatusFlags.CF (sbbR64R64Effect 0x111510 13 10)) (Reg.operands [.gpr 13, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[13, 10, 66]
    (.letOp (n := 70) (.exec 0x111510 (fun s => s.RIP = 0x111510) (atFlags StatusFlags.CF (sbbR64R64Effect 0x111510 13 10)) (Reg.operands [.gpr 13, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[13, 10, 66]
    (.letOp (n := 71) (.out 0x111513 (movR64R64Effect 0x111513 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[3]
    (.letOp (n := 72) (.exec 0x111513 (fun s => s.RIP = 0x111513) (movR64R64Effect 0x111513 6 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 73) (.out 0x111516 (notR64Effect 0x111516 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[71]
    (.letOp (n := 74) (.exec 0x111516 (fun s => s.RIP = 0x111516) (notR64Effect 0x111516 6) (Reg.operands [.gpr 6] [])) #v[71]
    (.letOp (n := 75) (.exec 0x111519 (StorePre 0x111519 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x111519 + BitVec.ofNat 64 4)) 1) (atFlags (condHolds 3) (setccM8Effect 0x111519 4 (.sib 4 none 0 .none))) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[4, 69]
    (.letOp (n := 76) (.exec 0x11151d (fun s => s.RIP = 0x11151d) (movR64R64Effect 0x11151d 2 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 77) (.out 0x111520 (movzxR32M8Effect 0x111520 4 2 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 78) (.exec 0x111520 (LoadPre 0x111520 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x111520 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x111520 4 2 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.out 0x111524 (andR32Imm8Effect 0x111524 3 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[77]
    (.letOp (n := 80) (.exec 0x111524 (fun s => s.RIP = 0x111524) (andR32Imm8Effect 0x111524 3 2 0x1) (Reg.operands [.gpr 2] [])) #v[77]
    (.letOp (n := 81) (.out 0x111527 (addR64R64Effect 0x111527 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[79, 73]
    (.letOp (n := 82) (.exec 0x111527 (fun s => s.RIP = 0x111527) (addR64R64Effect 0x111527 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[79, 73]
    (.terminate (.br ⟨.l11700a, RegMap.args [(0, 0), (1, 1), (2, 81), (3, 3), (4, 4), (6, 73), (7, 7), (8, 8), (9, 9), (10, 10), (11, 65), (12, 55), (13, 68), (14, 60), (22, 22), (39, 39), (51, 51)] 83⟩)))))))))))))))))))))))))))))))

def bytes_l116fd8 : List UInt8 :=
  [0x49, 0x89, 0xC4, 0x49, 0xF7, 0xDC, 0x41, 0xBE, 0x00, 0x00, 0x00, 0x00, 0x4D, 0x19, 0xC6, 0x41,
    0xBB, 0x00, 0x00, 0x00, 0x00, 0x4D, 0x19, 0xCB, 0x4D, 0x19, 0xD5, 0x48, 0x89, 0xDE, 0x48, 0xF7,
    0xD6, 0x0F, 0x93, 0x04, 0x24, 0x48, 0x89, 0xE2, 0x0F, 0xB6, 0x14, 0x24, 0x83, 0xE2, 0x01, 0x48,
    0x01, 0xF2]

theorem code_l116fd8 : ∀ x ∈ codeRange 0x1114f8 bytes_l116fd8, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x114f8 50 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11700a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x11152a (StorePre 0x11152a 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x11152a + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x11152a 3 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1, 4]
    (.letOp (n := 54) (.exec 0x11152d (fun s => s.RIP = 0x11152d) (movR64R64Effect 0x11152d 15 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x111530 (xorR64R64Effect 0x111530 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 0] []) (.reg (.gpr 12))) #v[12, 0]
    (.letOp (n := 56) (.exec 0x111530 (fun s => s.RIP = 0x111530) (xorR64R64Effect 0x111530 12 0) (Reg.operands [.gpr 12, .gpr 0] [])) #v[12, 0]
    (.letOp (n := 57) (.out 0x111533 (movzxR32M8Effect 0x111533 4 6 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 58) (.exec 0x111533 (LoadPre 0x111533 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x111533 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x111533 4 6 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x111537 (negR64Effect 0x111537 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[57]
    (.letOp (n := 60) (.exec 0x111537 (fun s => s.RIP = 0x111537) (negR64Effect 0x111537 6) (Reg.operands [.gpr 6] [])) #v[57]
    (.letOp (n := 61) (.out 0x11153a (andR64R64Effect 0x11153a 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 12] []) (.reg (.gpr 6))) #v[59, 55]
    (.letOp (n := 62) (.exec 0x11153a (fun s => s.RIP = 0x11153a) (andR64R64Effect 0x11153a 6 12) (Reg.operands [.gpr 6, .gpr 12] [])) #v[59, 55]
    (.letOp (n := 63) (.out 0x11153d (xorR64R64Effect 0x11153d 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[61, 0]
    (.letOp (n := 64) (.exec 0x11153d (fun s => s.RIP = 0x11153d) (xorR64R64Effect 0x11153d 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[61, 0]
    (.letOp (n := 65) (.exec 0x111540 (StorePre 0x111540 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x111540 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x111540 3 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1, 4]
    (.letOp (n := 66) (.out 0x111543 (movzxR32M8Effect 0x111543 4 0 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 67) (.exec 0x111543 (LoadPre 0x111543 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x111543 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x111543 4 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.out 0x111547 (xorR64R64Effect 0x111547 14 8) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 8] []) (.reg (.gpr 14))) #v[14, 8]
    (.letOp (n := 69) (.exec 0x111547 (fun s => s.RIP = 0x111547) (xorR64R64Effect 0x111547 14 8) (Reg.operands [.gpr 14, .gpr 8] [])) #v[14, 8]
    (.letOp (n := 70) (.out 0x11154a (negR64Effect 0x11154a 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[66]
    (.letOp (n := 71) (.exec 0x11154a (fun s => s.RIP = 0x11154a) (negR64Effect 0x11154a 0) (Reg.operands [.gpr 0] [])) #v[66]
    (.letOp (n := 72) (.out 0x11154d (andR64R64Effect 0x11154d 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[70, 68]
    (.letOp (n := 73) (.exec 0x11154d (fun s => s.RIP = 0x11154d) (andR64R64Effect 0x11154d 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[70, 68]
    (.letOp (n := 74) (.out 0x111550 (xorR64R64Effect 0x111550 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 8] []) (.reg (.gpr 0))) #v[72, 8]
    (.letOp (n := 75) (.exec 0x111550 (fun s => s.RIP = 0x111550) (xorR64R64Effect 0x111550 0 8) (Reg.operands [.gpr 0, .gpr 8] [])) #v[72, 8]
    (.terminate (.br ⟨.l117033, RegMap.args [(0, 74), (1, 1), (2, 2), (3, 3), (4, 4), (6, 63), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 68), (22, 22), (39, 39), (51, 51)] 76⟩))))))))))))))))))))))))

def bytes_l11700a : List UInt8 :=
  [0x88, 0x0C, 0x24, 0x49, 0x89, 0xE7, 0x49, 0x31, 0xC4, 0x0F, 0xB6, 0x34, 0x24, 0x48, 0xF7, 0xDE,
    0x4C, 0x21, 0xE6, 0x48, 0x31, 0xC6, 0x88, 0x0C, 0x24, 0x0F, 0xB6, 0x04, 0x24, 0x4D, 0x31, 0xC6,
    0x48, 0xF7, 0xD8, 0x4C, 0x21, 0xF0, 0x4C, 0x31, 0xC0]

theorem code_l11700a : ∀ x ∈ codeRange 0x11152a bytes_l11700a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1152a 41 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l117033 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x111553 (StorePre 0x111553 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x111553 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x111553 3 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1, 4]
    (.letOp (n := 54) (.out 0x111556 (movzxR32M8Effect 0x111556 5 8 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 55) (.exec 0x111556 (LoadPre 0x111556 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x111556 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x111556 5 8 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x11155b (xorR64R64Effect 0x11155b 11 9) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 9] []) (.reg (.gpr 11))) #v[11, 9]
    (.letOp (n := 57) (.exec 0x11155b (fun s => s.RIP = 0x11155b) (xorR64R64Effect 0x11155b 11 9) (Reg.operands [.gpr 11, .gpr 9] [])) #v[11, 9]
    (.letOp (n := 58) (.out 0x11155e (negR64Effect 0x11155e 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[54]
    (.letOp (n := 59) (.exec 0x11155e (fun s => s.RIP = 0x11155e) (negR64Effect 0x11155e 8) (Reg.operands [.gpr 8] [])) #v[54]
    (.letOp (n := 60) (.out 0x111561 (andR64R64Effect 0x111561 8 11) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 11] []) (.reg (.gpr 8))) #v[58, 56]
    (.letOp (n := 61) (.exec 0x111561 (fun s => s.RIP = 0x111561) (andR64R64Effect 0x111561 8 11) (Reg.operands [.gpr 8, .gpr 11] [])) #v[58, 56]
    (.letOp (n := 62) (.out 0x111564 (xorR64R64Effect 0x111564 8 9) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 9] []) (.reg (.gpr 8))) #v[60, 9]
    (.letOp (n := 63) (.exec 0x111564 (fun s => s.RIP = 0x111564) (xorR64R64Effect 0x111564 8 9) (Reg.operands [.gpr 8, .gpr 9] [])) #v[60, 9]
    (.letOp (n := 64) (.exec 0x111567 (StorePre 0x111567 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x111567 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x111567 3 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1, 4]
    (.letOp (n := 65) (.out 0x11156a (movzxR32M8Effect 0x11156a 5 9 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 66) (.exec 0x11156a (LoadPre 0x11156a (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x11156a + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x11156a 5 9 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x11156f (xorR64R64Effect 0x11156f 13 10) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 10] []) (.reg (.gpr 13))) #v[13, 10]
    (.letOp (n := 68) (.exec 0x11156f (fun s => s.RIP = 0x11156f) (xorR64R64Effect 0x11156f 13 10) (Reg.operands [.gpr 13, .gpr 10] [])) #v[13, 10]
    (.letOp (n := 69) (.out 0x111572 (negR64Effect 0x111572 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[65]
    (.letOp (n := 70) (.exec 0x111572 (fun s => s.RIP = 0x111572) (negR64Effect 0x111572 9) (Reg.operands [.gpr 9] [])) #v[65]
    (.letOp (n := 71) (.out 0x111575 (andR64R64Effect 0x111575 9 13) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 13] []) (.reg (.gpr 9))) #v[69, 67]
    (.letOp (n := 72) (.exec 0x111575 (fun s => s.RIP = 0x111575) (andR64R64Effect 0x111575 9 13) (Reg.operands [.gpr 9, .gpr 13] [])) #v[69, 67]
    (.letOp (n := 73) (.out 0x111578 (xorR64R64Effect 0x111578 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[71, 10]
    (.letOp (n := 74) (.exec 0x111578 (fun s => s.RIP = 0x111578) (xorR64R64Effect 0x111578 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[71, 10]
    (.letOp (n := 75) (.exec 0x11157b (StorePre 0x11157b 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x11157b + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x11157b 3 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1, 4]
    (.letOp (n := 76) (.exec 0x11157e (fun s => s.RIP = 0x11157e) (movR64R64Effect 0x11157e 10 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 77) (.out 0x111581 (movzxR32M8Effect 0x111581 5 10 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 78) (.exec 0x111581 (LoadPre 0x111581 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x111581 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x111581 5 10 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.out 0x111586 (xorR64R64Effect 0x111586 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 3] []) (.reg (.gpr 2))) #v[2, 3]
    (.letOp (n := 80) (.exec 0x111586 (fun s => s.RIP = 0x111586) (xorR64R64Effect 0x111586 2 3) (Reg.operands [.gpr 2, .gpr 3] [])) #v[2, 3]
    (.letOp (n := 81) (.out 0x111589 (negR64Effect 0x111589 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[77]
    (.letOp (n := 82) (.exec 0x111589 (fun s => s.RIP = 0x111589) (negR64Effect 0x111589 10) (Reg.operands [.gpr 10] [])) #v[77]
    (.letOp (n := 83) (.out 0x11158c (andR64R64Effect 0x11158c 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2] []) (.reg (.gpr 10))) #v[81, 79]
    (.letOp (n := 84) (.exec 0x11158c (fun s => s.RIP = 0x11158c) (andR64R64Effect 0x11158c 10 2) (Reg.operands [.gpr 10, .gpr 2] [])) #v[81, 79]
    (.letOp (n := 85) (.out 0x11158f (xorR64R64Effect 0x11158f 10 3) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 3] []) (.reg (.gpr 10))) #v[83, 3]
    (.letOp (n := 86) (.exec 0x11158f (fun s => s.RIP = 0x11158f) (xorR64R64Effect 0x11158f 10 3) (Reg.operands [.gpr 10, .gpr 3] [])) #v[83, 3]
    (.terminate (.br ⟨.l117072, RegMap.args [(0, 0), (1, 1), (2, 79), (3, 3), (4, 4), (6, 6), (7, 7), (8, 62), (9, 73), (10, 85), (11, 56), (13, 67), (22, 22), (39, 39), (51, 51)] 87⟩)))))))))))))))))))))))))))))))))))

def bytes_l117033 : List UInt8 :=
  [0x88, 0x0C, 0x24, 0x44, 0x0F, 0xB6, 0x04, 0x24, 0x4D, 0x31, 0xCB, 0x49, 0xF7, 0xD8, 0x4D, 0x21,
    0xD8, 0x4D, 0x31, 0xC8, 0x88, 0x0C, 0x24, 0x44, 0x0F, 0xB6, 0x0C, 0x24, 0x4D, 0x31, 0xD5, 0x49,
    0xF7, 0xD9, 0x4D, 0x21, 0xE9, 0x4D, 0x31, 0xD1, 0x88, 0x0C, 0x24, 0x49, 0x89, 0xE2, 0x44, 0x0F,
    0xB6, 0x14, 0x24, 0x48, 0x31, 0xDA, 0x49, 0xF7, 0xDA, 0x49, 0x21, 0xD2, 0x49, 0x31, 0xDA]

theorem code_l117033 : ∀ x ∈ codeRange 0x111553 bytes_l117033, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x11553 63 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l117072 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x111592 (movR64M64Effect 0x111592 2 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 54) (.exec 0x111592 (LoadPre 0x111592 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x111592 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111592 2 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x111597 (andR8R8Effect 0x111597 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[53, 1]
    (.letOp (n := 56) (.exec 0x111597 (fun s => s.RIP = 0x111597) (andR8R8Effect 0x111597 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[53, 1]
    (.letOp (n := 57) (.out 0x111599 (xorR8Imm8Effect 0x111599 3 1 0x1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1]
    (.letOp (n := 58) (.exec 0x111599 (fun s => s.RIP = 0x111599) (xorR8Imm8Effect 0x111599 3 1 0x1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 59) (.out 0x11159c (andR8M8Effect 0x11159c 4 1 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 4] []) (.reg (.gpr 1))) #v[57, 4]
    (.letOp (n := 60) (.exec 0x11159c (LoadPre 0x11159c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11159c + BitVec.ofNat 64 4)) 1) (andR8M8Effect 0x11159c 4 1 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[57, 4]
    (.terminate (.br ⟨.l117080, RegMap.args [(0, 0), (1, 59), (2, 55), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (22, 22), (39, 39), (51, 51)] 61⟩)))))))))

def bytes_l117072 : List UInt8 :=
  [0x48, 0x8B, 0x54, 0x24, 0x18, 0x20, 0xCA, 0x80, 0xF1, 0x01, 0x22, 0x4C, 0x24, 0x20]

theorem code_l117072 : ∀ x ∈ codeRange 0x111592 bytes_l117072, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x11592 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l117080 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1115a0 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1115a0 3 (fun s => AddrMode.addr (.base 7 .none) s (0x1115a0 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x1115a0 6 (.base 7 .none)) (Reg.operands [.gpr 6, .gpr 7] [])) #v[6, 7]
    (.letOp (n := 54) (.exec 0x1115a3 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1115a3 4 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x1115a3 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1115a3 0 (.base 7 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 7] [])) #v[0, 7]
    (.letOp (n := 55) (.exec 0x1115a7 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1115a7 4 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x1115a7 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1115a7 8 (.base 7 (.d8 0x10))) (Reg.operands [.gpr 8, .gpr 7] [])) #v[8, 7]
    (.letOp (n := 56) (.exec 0x1115ab (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1115ab 4 (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x1115ab + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1115ab 9 (.base 7 (.d8 0x18))) (Reg.operands [.gpr 9, .gpr 7] [])) #v[9, 7]
    (.letOp (n := 57) (.exec 0x1115af (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1115af 4 (fun s => AddrMode.addr (.base 7 (.d8 0x20)) s (0x1115af + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1115af 10 (.base 7 (.d8 0x20))) (Reg.operands [.gpr 10, .gpr 7] [])) #v[10, 7]
    (.letOp (n := 58) (.out 0x1115b3 (movR64R64Effect 0x1115b3 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 59) (.exec 0x1115b3 (fun s => s.RIP = 0x1115b3) (movR64R64Effect 0x1115b3 0 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 60) (.out 0x1115b6 (orR8R8Effect 0x1115b6 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[58, 1]
    (.letOp (n := 61) (.exec 0x1115b6 (fun s => s.RIP = 0x1115b6) (orR8R8Effect 0x1115b6 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[58, 1]
    (.letOp (n := 62) (.exec 0x1115b8 (StorePre 0x1115b8 3 (fun s => AddrMode.addr (.base 7 (.d8 0x28)) s (0x1115b8 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x1115b8 3 0 (.base 7 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 7] [])) #v[60, 7]
    (.letOp (n := 63) (.out 0x1115bb (addR64Imm8Effect 0x1115bb 4 0x40) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 64) (.exec 0x1115bb (fun s => s.RIP = 0x1115bb) (addR64Imm8Effect 0x1115bb 4 0x40) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x1115bf (popR64Effect 0x1115bf 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[63]
    (.letOp (n := 66) (.out 0x1115bf (popR64Effect 0x1115bf 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 67) (.exec 0x1115bf (PopPre 0x1115bf) (popR64Effect 0x1115bf 1 3) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 68) (.out 0x1115c0 (popR64Effect 0x1115c0 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[66]
    (.letOp (n := 69) (.out 0x1115c0 (popR64Effect 0x1115c0 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[66]
    (.letOp (n := 70) (.exec 0x1115c0 (PopPre 0x1115c0) (popR64Effect 0x1115c0 2 12) (Reg.operands [.gpr 4] [])) #v[66]
    (.letOp (n := 71) (.out 0x1115c2 (popR64Effect 0x1115c2 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[69]
    (.letOp (n := 72) (.out 0x1115c2 (popR64Effect 0x1115c2 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[69]
    (.letOp (n := 73) (.exec 0x1115c2 (PopPre 0x1115c2) (popR64Effect 0x1115c2 2 13) (Reg.operands [.gpr 4] [])) #v[69]
    (.letOp (n := 74) (.out 0x1115c4 (popR64Effect 0x1115c4 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[72]
    (.letOp (n := 75) (.out 0x1115c4 (popR64Effect 0x1115c4 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[72]
    (.letOp (n := 76) (.exec 0x1115c4 (PopPre 0x1115c4) (popR64Effect 0x1115c4 2 14) (Reg.operands [.gpr 4] [])) #v[72]
    (.letOp (n := 77) (.out 0x1115c6 (popR64Effect 0x1115c6 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[75]
    (.letOp (n := 78) (.out 0x1115c6 (popR64Effect 0x1115c6 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[75]
    (.letOp (n := 79) (.exec 0x1115c6 (PopPre 0x1115c6) (popR64Effect 0x1115c6 2 15) (Reg.operands [.gpr 4] [])) #v[75]
    (.letOp (n := 80) (.out 0x1115c8 (popR64Effect 0x1115c8 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[78]
    (.letOp (n := 81) (.out 0x1115c8 (popR64Effect 0x1115c8 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[78]
    (.letOp (n := 82) (.exec 0x1115c8 (PopPre 0x1115c8) (popR64Effect 0x1115c8 1 5) (Reg.operands [.gpr 4] [])) #v[78]
    (.letOp (n := 83) (.out 0x1115c9 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[81]
    (.letOp (n := 84) (.out 0x1115c9 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[81]
    (.letOp (n := 85) (.exec 0x1115c9 (RetPre 0x1115c9) (retEffect) (Reg.operands [.gpr 4] [])) #v[81]
    (.terminate (.ret (RegMap.args [(0, 60), (1, 1), (2, 2), (3, 65), (4, 84), (5, 80), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (12, 68), (13, 71), (14, 74), (15, 77), (22, 22), (39, 39), (51, 51)] 86) (some ⟨83, by decide⟩)))))))))))))))))))))))))))))))))))

def bytes_l117080 : List UInt8 :=
  [0x48, 0x89, 0x37, 0x48, 0x89, 0x47, 0x08, 0x4C, 0x89, 0x47, 0x10, 0x4C, 0x89, 0x4F, 0x18, 0x4C,
    0x89, 0x57, 0x20, 0x48, 0x89, 0xD0, 0x08, 0xC8, 0x88, 0x47, 0x28, 0x48, 0x83, 0xC4, 0x40, 0x5B,
    0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l117080 : ∀ x ∈ codeRange 0x1115a0 bytes_l117080, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x115a0 42 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

end P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine
