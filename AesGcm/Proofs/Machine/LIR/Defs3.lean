import AesGcm.Proofs.Machine.Instructions.Memory16
import AesGcm.Proofs.Machine.Instructions.HighByteStore
import AesGcm.Proofs.Machine.LIR.Labels
import AesGcm.Proofs.Copied.X86Proofs.CFG.EvalAttr
import AesGcm.Proofs.Copied.X86Proofs.Lift.Generated.Footprints

namespace AesGcm.Proofs.Machine.LIR

open AesGcm.Proofs.Machine.Instructions
open X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift

@[cfg_block] def b_l103930 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103930 (xorR32R32Effect 0x103930 3 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 8] []) (.reg (.gpr 8))) #v[8, 8]
    (.letOp (n := 54) (.exec 0x103930 (fun s => s.RIP = 0x103930) (xorR32R32Effect 0x103930 3 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[8, 8]
    (.letOp (n := 55) (.out 0x103933 (cmpM8Imm8Effect 0x103933 4 (.sib 7 (some 2) 0 .none) 0xc0) (EffectPart.reads (.flag .SF) [.gpr 7, .gpr 2] []) (.flag .SF)) #v[7, 2]
    (.letOp (n := 56) (.out 0x103933 (cmpM8Imm8Effect 0x103933 4 (.sib 7 (some 2) 0 .none) 0xc0) (EffectPart.reads (.flag .OF) [.gpr 7, .gpr 2] []) (.flag .OF)) #v[7, 2]
    (.letOp (n := 57) (.exec 0x103933 (LoadPre 0x103933 (fun s => AddrMode.addr (.sib 7 (some 2) 0 .none) s (0x103933 + BitVec.ofNat 64 4)) 1) (cmpM8Imm8Effect 0x103933 4 (.sib 7 (some 2) 0 .none) 0xc0) (Reg.operands [.gpr 7, .gpr 2] [])) #v[7, 2]
    (.letOp (n := 58) (.out 0x103937 (atFlags (condHolds 13) (setccR8Effect 0x103937 4 8)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF]) (.reg (.gpr 8))) #v[53, 55, 56]
    (.letOp (n := 59) (.exec 0x103937 (fun s => s.RIP = 0x103937) (atFlags (condHolds 13) (setccR8Effect 0x103937 4 8)) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF])) #v[53, 55, 56]
    (.letOp (n := 60) (.out 0x10393b (addR64R64Effect 0x10393b 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[58, 0]
    (.letOp (n := 61) (.exec 0x10393b (fun s => s.RIP = 0x10393b) (addR64R64Effect 0x10393b 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[58, 0]
    (.letOp (n := 62) (.out 0x10393e (xorR32R32Effect 0x10393e 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[0, 0]
    (.letOp (n := 63) (.exec 0x10393e (fun s => s.RIP = 0x10393e) (xorR32R32Effect 0x10393e 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.letOp (n := 64) (.out 0x103940 (cmpM8Imm8Effect 0x103940 5 (.sib 7 (some 2) 0 (.d8 0x1)) 0xc0) (EffectPart.reads (.flag .SF) [.gpr 7, .gpr 2] []) (.flag .SF)) #v[7, 2]
    (.letOp (n := 65) (.out 0x103940 (cmpM8Imm8Effect 0x103940 5 (.sib 7 (some 2) 0 (.d8 0x1)) 0xc0) (EffectPart.reads (.flag .OF) [.gpr 7, .gpr 2] []) (.flag .OF)) #v[7, 2]
    (.letOp (n := 66) (.exec 0x103940 (LoadPre 0x103940 (fun s => AddrMode.addr (.sib 7 (some 2) 0 (.d8 0x1)) s (0x103940 + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x103940 5 (.sib 7 (some 2) 0 (.d8 0x1)) 0xc0) (Reg.operands [.gpr 7, .gpr 2] [])) #v[7, 2]
    (.letOp (n := 67) (.out 0x103945 (atFlags (condHolds 13) (setccR8Effect 0x103945 3 0)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF]) (.reg (.gpr 0))) #v[62, 64, 65]
    (.letOp (n := 68) (.exec 0x103945 (fun s => s.RIP = 0x103945) (atFlags (condHolds 13) (setccR8Effect 0x103945 3 0)) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF])) #v[62, 64, 65]
    (.letOp (n := 69) (.out 0x103948 (xorR32R32Effect 0x103948 3 9 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 9] []) (.reg (.gpr 9))) #v[9, 9]
    (.letOp (n := 70) (.exec 0x103948 (fun s => s.RIP = 0x103948) (xorR32R32Effect 0x103948 3 9 9) (Reg.operands [.gpr 9, .gpr 9] [])) #v[9, 9]
    (.letOp (n := 71) (.out 0x10394b (cmpM8Imm8Effect 0x10394b 5 (.sib 7 (some 2) 0 (.d8 0x2)) 0xc0) (EffectPart.reads (.flag .SF) [.gpr 7, .gpr 2] []) (.flag .SF)) #v[7, 2]
    (.letOp (n := 72) (.out 0x10394b (cmpM8Imm8Effect 0x10394b 5 (.sib 7 (some 2) 0 (.d8 0x2)) 0xc0) (EffectPart.reads (.flag .OF) [.gpr 7, .gpr 2] []) (.flag .OF)) #v[7, 2]
    (.letOp (n := 73) (.exec 0x10394b (LoadPre 0x10394b (fun s => AddrMode.addr (.sib 7 (some 2) 0 (.d8 0x2)) s (0x10394b + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x10394b 5 (.sib 7 (some 2) 0 (.d8 0x2)) 0xc0) (Reg.operands [.gpr 7, .gpr 2] [])) #v[7, 2]
    (.letOp (n := 74) (.out 0x103950 (atFlags (condHolds 13) (setccR8Effect 0x103950 4 9)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF]) (.reg (.gpr 9))) #v[69, 71, 72]
    (.letOp (n := 75) (.exec 0x103950 (fun s => s.RIP = 0x103950) (atFlags (condHolds 13) (setccR8Effect 0x103950 4 9)) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF])) #v[69, 71, 72]
    (.letOp (n := 76) (.out 0x103954 (addR64R64Effect 0x103954 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0] []) (.reg (.gpr 9))) #v[74, 67]
    (.letOp (n := 77) (.exec 0x103954 (fun s => s.RIP = 0x103954) (addR64R64Effect 0x103954 9 0) (Reg.operands [.gpr 9, .gpr 0] [])) #v[74, 67]
    (.letOp (n := 78) (.out 0x103957 (addR64R64Effect 0x103957 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8] []) (.reg (.gpr 9))) #v[76, 60]
    (.letOp (n := 79) (.exec 0x103957 (fun s => s.RIP = 0x103957) (addR64R64Effect 0x103957 9 8) (Reg.operands [.gpr 9, .gpr 8] [])) #v[76, 60]
    (.letOp (n := 80) (.out 0x10395a (xorR32R32Effect 0x10395a 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[67, 67]
    (.letOp (n := 81) (.exec 0x10395a (fun s => s.RIP = 0x10395a) (xorR32R32Effect 0x10395a 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[67, 67]
    (.letOp (n := 82) (.out 0x10395c (cmpM8Imm8Effect 0x10395c 5 (.sib 7 (some 2) 0 (.d8 0x3)) 0xc0) (EffectPart.reads (.flag .SF) [.gpr 7, .gpr 2] []) (.flag .SF)) #v[7, 2]
    (.letOp (n := 83) (.out 0x10395c (cmpM8Imm8Effect 0x10395c 5 (.sib 7 (some 2) 0 (.d8 0x3)) 0xc0) (EffectPart.reads (.flag .OF) [.gpr 7, .gpr 2] []) (.flag .OF)) #v[7, 2]
    (.letOp (n := 84) (.exec 0x10395c (LoadPre 0x10395c (fun s => AddrMode.addr (.sib 7 (some 2) 0 (.d8 0x3)) s (0x10395c + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x10395c 5 (.sib 7 (some 2) 0 (.d8 0x3)) 0xc0) (Reg.operands [.gpr 7, .gpr 2] [])) #v[7, 2]
    (.letOp (n := 85) (.out 0x103961 (atFlags (condHolds 13) (setccR8Effect 0x103961 3 0)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF]) (.reg (.gpr 0))) #v[80, 82, 83]
    (.letOp (n := 86) (.exec 0x103961 (fun s => s.RIP = 0x103961) (atFlags (condHolds 13) (setccR8Effect 0x103961 3 0)) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF])) #v[80, 82, 83]
    (.letOp (n := 87) (.out 0x103964 (addR64R64Effect 0x103964 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[85, 78]
    (.letOp (n := 88) (.exec 0x103964 (fun s => s.RIP = 0x103964) (addR64R64Effect 0x103964 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[85, 78]
    (.letOp (n := 89) (.out 0x103967 (addR64Imm8Effect 0x103967 2 0x4) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[2]
    (.letOp (n := 90) (.exec 0x103967 (fun s => s.RIP = 0x103967) (addR64Imm8Effect 0x103967 2 0x4) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 91) (.out 0x10396b (cmpR64R64Effect 0x10396b 6 2) (EffectPart.reads (.flag .ZF) [.gpr 6, .gpr 2] []) (.flag .ZF)) #v[6, 89]
    (.letOp (n := 92) (.exec 0x10396b (fun s => s.RIP = 0x10396b) (cmpR64R64Effect 0x10396b 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[6, 89]
    (.letOp (n := 93) (.pure (condOp 5)) #v[91]
    (.terminate (.condBr (Fin.last 93) ⟨.l103930, RegMap.args [(0, 87), (1, 1), (2, 89), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 60), (9, 78), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 91), (22, 22), (39, 39), (50, 50), (51, 51)] 94⟩ ⟨.l103970, RegMap.args [(0, 87), (1, 1), (2, 89), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 60), (9, 78), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 91), (22, 22), (39, 39), (50, 50), (51, 51)] 94⟩))))))))))))))))))))))))))))))))))))))))))

def bytes_l103930 : List UInt8 :=
  [0x45, 0x31, 0xC0, 0x80, 0x3C, 0x17, 0xC0, 0x41, 0x0F, 0x9D, 0xC0, 0x49, 0x01, 0xC0, 0x31, 0xC0,
    0x80, 0x7C, 0x17, 0x01, 0xC0, 0x0F, 0x9D, 0xC0, 0x45, 0x31, 0xC9, 0x80, 0x7C, 0x17, 0x02, 0xC0,
    0x41, 0x0F, 0x9D, 0xC1, 0x49, 0x01, 0xC1, 0x4D, 0x01, 0xC1, 0x31, 0xC0, 0x80, 0x7C, 0x17, 0x03,
    0xC0, 0x0F, 0x9D, 0xC0, 0x4C, 0x01, 0xC8, 0x48, 0x83, 0xC2, 0x04, 0x48, 0x39, 0xD6, 0x75, 0xC0]

theorem code_l103930 : ∀ x ∈ codeRange 0x103930 bytes_l103930, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3930 64 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103970 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103970 (testR64R64Effect 0x103970 1 1) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 1] []) (.flag .ZF)) #v[1, 1]
    (.letOp (n := 54) (.exec 0x103970 (fun s => s.RIP = 0x103970) (testR64R64Effect 0x103970 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[1, 1]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l103995, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l103975, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l103970 : List UInt8 :=
  [0x48, 0x85, 0xC9, 0x74, 0x20]

theorem code_l103970 : ∀ x ∈ codeRange 0x103970 bytes_l103970, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3970 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103975 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103975 (addR64R64Effect 0x103975 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2] []) (.reg (.gpr 7))) #v[7, 2]
    (.letOp (n := 54) (.exec 0x103975 (fun s => s.RIP = 0x103975) (addR64R64Effect 0x103975 7 2) (Reg.operands [.gpr 7, .gpr 2] [])) #v[7, 2]
    (.letOp (n := 55) (.out 0x103978 (xorR32R32Effect 0x103978 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[2, 2]
    (.letOp (n := 56) (.exec 0x103978 (fun s => s.RIP = 0x103978) (xorR32R32Effect 0x103978 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 57) (.exec 0x10397a (fun s => s.RIP = 0x10397a) (fun _ => nopEffect 0x10397a 6) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l103980, RegMap.args [(0, 0), (1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l103975 : List UInt8 :=
  [0x48, 0x01, 0xD7, 0x31, 0xD2, 0x66, 0x0F, 0x1F, 0x44, 0x00, 0x00]

theorem code_l103975 : ∀ x ∈ codeRange 0x103975 bytes_l103975, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3975 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103980 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103980 (xorR32R32Effect 0x103980 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[6, 6]
    (.letOp (n := 54) (.exec 0x103980 (fun s => s.RIP = 0x103980) (xorR32R32Effect 0x103980 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 55) (.out 0x103982 (cmpM8Imm8Effect 0x103982 4 (.sib 7 (some 2) 0 .none) 0xc0) (EffectPart.reads (.flag .SF) [.gpr 7, .gpr 2] []) (.flag .SF)) #v[7, 2]
    (.letOp (n := 56) (.out 0x103982 (cmpM8Imm8Effect 0x103982 4 (.sib 7 (some 2) 0 .none) 0xc0) (EffectPart.reads (.flag .OF) [.gpr 7, .gpr 2] []) (.flag .OF)) #v[7, 2]
    (.letOp (n := 57) (.exec 0x103982 (LoadPre 0x103982 (fun s => AddrMode.addr (.sib 7 (some 2) 0 .none) s (0x103982 + BitVec.ofNat 64 4)) 1) (cmpM8Imm8Effect 0x103982 4 (.sib 7 (some 2) 0 .none) 0xc0) (Reg.operands [.gpr 7, .gpr 2] [])) #v[7, 2]
    (.letOp (n := 58) (.out 0x103986 (atFlags (condHolds 13) (setccR8Effect 0x103986 4 6)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF]) (.reg (.gpr 6))) #v[53, 55, 56]
    (.letOp (n := 59) (.exec 0x103986 (fun s => s.RIP = 0x103986) (atFlags (condHolds 13) (setccR8Effect 0x103986 4 6)) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF])) #v[53, 55, 56]
    (.letOp (n := 60) (.out 0x10398a (addR64R64Effect 0x10398a 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[0, 58]
    (.letOp (n := 61) (.exec 0x10398a (fun s => s.RIP = 0x10398a) (addR64R64Effect 0x10398a 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[0, 58]
    (.letOp (n := 62) (.out 0x10398d (incR64Effect 0x10398d 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[2]
    (.letOp (n := 63) (.exec 0x10398d (fun s => s.RIP = 0x10398d) (incR64Effect 0x10398d 2) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2]
    (.letOp (n := 64) (.out 0x103990 (cmpR64R64Effect 0x103990 1 2) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 2] []) (.flag .ZF)) #v[1, 62]
    (.letOp (n := 65) (.exec 0x103990 (fun s => s.RIP = 0x103990) (cmpR64R64Effect 0x103990 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[1, 62]
    (.letOp (n := 66) (.pure (condOp 5)) #v[64]
    (.terminate (.condBr (Fin.last 66) ⟨.l103980, RegMap.args [(0, 60), (1, 1), (2, 62), (3, 3), (4, 4), (5, 5), (6, 58), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 64), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩ ⟨.l103995, RegMap.args [(0, 60), (1, 1), (2, 62), (3, 3), (4, 4), (5, 5), (6, 58), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 64), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩)))))))))))))))

def bytes_l103980 : List UInt8 :=
  [0x31, 0xF6, 0x80, 0x3C, 0x17, 0xC0, 0x40, 0x0F, 0x9D, 0xC6, 0x48, 0x01, 0xF0, 0x48, 0xFF, 0xC2,
    0x48, 0x39, 0xD1, 0x75, 0xEB]

theorem code_l103980 : ∀ x ∈ codeRange 0x103980 bytes_l103980, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3980 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103995 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103995 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[4]
    (.letOp (n := 54) (.out 0x103995 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 55) (.exec 0x103995 (RetPre 0x103995) (retEffect) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 54), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 56) (some ⟨53, by decide⟩)))))

def bytes_l103995 : List UInt8 :=
  [0xC3]

theorem code_l103995 : ∀ x ∈ codeRange 0x103995 bytes_l103995, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3995 1 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103996 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103996 (movR32R32Effect 0x103996 3 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[0]
    (.letOp (n := 54) (.exec 0x103996 (fun s => s.RIP = 0x103996) (movR32R32Effect 0x103996 3 11 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x103999 (andR32Imm8Effect 0x103999 4 11 0x4) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11] []) (.reg (.gpr 11))) #v[53]
    (.letOp (n := 56) (.exec 0x103999 (fun s => s.RIP = 0x103999) (andR32Imm8Effect 0x103999 4 11 0x4) (Reg.operands [.gpr 11] [])) #v[53]
    (.letOp (n := 57) (.out 0x10399d (xorR32R32Effect 0x10399d 3 10 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 10] []) (.reg (.gpr 10))) #v[10, 10]
    (.letOp (n := 58) (.exec 0x10399d (fun s => s.RIP = 0x10399d) (xorR32R32Effect 0x10399d 3 10 10) (Reg.operands [.gpr 10, .gpr 10] [])) #v[10, 10]
    (.letOp (n := 59) (.out 0x1039a0 (xorR32R32Effect 0x1039a0 3 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 8] []) (.reg (.gpr 8))) #v[8, 8]
    (.letOp (n := 60) (.exec 0x1039a0 (fun s => s.RIP = 0x1039a0) (xorR32R32Effect 0x1039a0 3 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[8, 8]
    (.letOp (n := 61) (.exec 0x1039a3 (fun s => s.RIP = 0x1039a3) (fun _ => nopEffect 0x1039a3 13) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l1039b0, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 59), (9, 9), (10, 57), (11, 55), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩))))))))))

def bytes_l103996 : List UInt8 :=
  [0x41, 0x89, 0xC3, 0x41, 0x83, 0xE3, 0x04, 0x45, 0x31, 0xD2, 0x45, 0x31, 0xC0, 0x66, 0x66, 0x66,
    0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem code_l103996 : ∀ x ∈ codeRange 0x103996 bytes_l103996, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3996 26 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1039b0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1039b0 (xorR32R32Effect 0x1039b0 2 3 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 3] []) (.reg (.gpr 3))) #v[3, 3]
    (.letOp (n := 54) (.exec 0x1039b0 (fun s => s.RIP = 0x1039b0) (xorR32R32Effect 0x1039b0 2 3 3) (Reg.operands [.gpr 3, .gpr 3] [])) #v[3, 3]
    (.letOp (n := 55) (.out 0x1039b2 (cmpM8Imm8Effect 0x1039b2 5 (.sib 7 (some 10) 0 .none) 0xc0) (EffectPart.reads (.flag .SF) [.gpr 7, .gpr 10] []) (.flag .SF)) #v[7, 10]
    (.letOp (n := 56) (.out 0x1039b2 (cmpM8Imm8Effect 0x1039b2 5 (.sib 7 (some 10) 0 .none) 0xc0) (EffectPart.reads (.flag .OF) [.gpr 7, .gpr 10] []) (.flag .OF)) #v[7, 10]
    (.letOp (n := 57) (.exec 0x1039b2 (LoadPre 0x1039b2 (fun s => AddrMode.addr (.sib 7 (some 10) 0 .none) s (0x1039b2 + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x1039b2 5 (.sib 7 (some 10) 0 .none) 0xc0) (Reg.operands [.gpr 7, .gpr 10] [])) #v[7, 10]
    (.letOp (n := 58) (.out 0x1039b7 (atFlags (condHolds 13) (setccR8Effect 0x1039b7 3 3)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF]) (.reg (.gpr 3))) #v[53, 55, 56]
    (.letOp (n := 59) (.exec 0x1039b7 (fun s => s.RIP = 0x1039b7) (atFlags (condHolds 13) (setccR8Effect 0x1039b7 3 3)) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF])) #v[53, 55, 56]
    (.letOp (n := 60) (.out 0x1039ba (addR64R64Effect 0x1039ba 3 8) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 8] []) (.reg (.gpr 3))) #v[58, 8]
    (.letOp (n := 61) (.exec 0x1039ba (fun s => s.RIP = 0x1039ba) (addR64R64Effect 0x1039ba 3 8) (Reg.operands [.gpr 3, .gpr 8] [])) #v[58, 8]
    (.letOp (n := 62) (.out 0x1039bd (xorR32R32Effect 0x1039bd 3 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 8] []) (.reg (.gpr 8))) #v[8, 8]
    (.letOp (n := 63) (.exec 0x1039bd (fun s => s.RIP = 0x1039bd) (xorR32R32Effect 0x1039bd 3 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[8, 8]
    (.letOp (n := 64) (.out 0x1039c0 (cmpM8Imm8Effect 0x1039c0 6 (.sib 7 (some 10) 0 (.d8 0x1)) 0xc0) (EffectPart.reads (.flag .SF) [.gpr 7, .gpr 10] []) (.flag .SF)) #v[7, 10]
    (.letOp (n := 65) (.out 0x1039c0 (cmpM8Imm8Effect 0x1039c0 6 (.sib 7 (some 10) 0 (.d8 0x1)) 0xc0) (EffectPart.reads (.flag .OF) [.gpr 7, .gpr 10] []) (.flag .OF)) #v[7, 10]
    (.letOp (n := 66) (.exec 0x1039c0 (LoadPre 0x1039c0 (fun s => AddrMode.addr (.sib 7 (some 10) 0 (.d8 0x1)) s (0x1039c0 + BitVec.ofNat 64 6)) 1) (cmpM8Imm8Effect 0x1039c0 6 (.sib 7 (some 10) 0 (.d8 0x1)) 0xc0) (Reg.operands [.gpr 7, .gpr 10] [])) #v[7, 10]
    (.letOp (n := 67) (.out 0x1039c6 (atFlags (condHolds 13) (setccR8Effect 0x1039c6 4 8)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF]) (.reg (.gpr 8))) #v[62, 64, 65]
    (.letOp (n := 68) (.exec 0x1039c6 (fun s => s.RIP = 0x1039c6) (atFlags (condHolds 13) (setccR8Effect 0x1039c6 4 8)) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF])) #v[62, 64, 65]
    (.letOp (n := 69) (.out 0x1039ca (xorR32R32Effect 0x1039ca 3 14 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 14] []) (.reg (.gpr 14))) #v[14, 14]
    (.letOp (n := 70) (.exec 0x1039ca (fun s => s.RIP = 0x1039ca) (xorR32R32Effect 0x1039ca 3 14 14) (Reg.operands [.gpr 14, .gpr 14] [])) #v[14, 14]
    (.letOp (n := 71) (.out 0x1039cd (cmpM8Imm8Effect 0x1039cd 6 (.sib 7 (some 10) 0 (.d8 0x2)) 0xc0) (EffectPart.reads (.flag .SF) [.gpr 7, .gpr 10] []) (.flag .SF)) #v[7, 10]
    (.letOp (n := 72) (.out 0x1039cd (cmpM8Imm8Effect 0x1039cd 6 (.sib 7 (some 10) 0 (.d8 0x2)) 0xc0) (EffectPart.reads (.flag .OF) [.gpr 7, .gpr 10] []) (.flag .OF)) #v[7, 10]
    (.letOp (n := 73) (.exec 0x1039cd (LoadPre 0x1039cd (fun s => AddrMode.addr (.sib 7 (some 10) 0 (.d8 0x2)) s (0x1039cd + BitVec.ofNat 64 6)) 1) (cmpM8Imm8Effect 0x1039cd 6 (.sib 7 (some 10) 0 (.d8 0x2)) 0xc0) (Reg.operands [.gpr 7, .gpr 10] [])) #v[7, 10]
    (.letOp (n := 74) (.out 0x1039d3 (atFlags (condHolds 13) (setccR8Effect 0x1039d3 4 14)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF]) (.reg (.gpr 14))) #v[69, 71, 72]
    (.letOp (n := 75) (.exec 0x1039d3 (fun s => s.RIP = 0x1039d3) (atFlags (condHolds 13) (setccR8Effect 0x1039d3 4 14)) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF])) #v[69, 71, 72]
    (.letOp (n := 76) (.out 0x1039d7 (addR64R64Effect 0x1039d7 14 8) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 8] []) (.reg (.gpr 14))) #v[74, 67]
    (.letOp (n := 77) (.exec 0x1039d7 (fun s => s.RIP = 0x1039d7) (addR64R64Effect 0x1039d7 14 8) (Reg.operands [.gpr 14, .gpr 8] [])) #v[74, 67]
    (.letOp (n := 78) (.out 0x1039da (addR64R64Effect 0x1039da 14 3) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 3] []) (.reg (.gpr 14))) #v[76, 60]
    (.letOp (n := 79) (.exec 0x1039da (fun s => s.RIP = 0x1039da) (addR64R64Effect 0x1039da 14 3) (Reg.operands [.gpr 14, .gpr 3] [])) #v[76, 60]
    (.letOp (n := 80) (.out 0x1039dd (xorR32R32Effect 0x1039dd 3 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 8] []) (.reg (.gpr 8))) #v[67, 67]
    (.letOp (n := 81) (.exec 0x1039dd (fun s => s.RIP = 0x1039dd) (xorR32R32Effect 0x1039dd 3 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[67, 67]
    (.letOp (n := 82) (.out 0x1039e0 (cmpM8Imm8Effect 0x1039e0 6 (.sib 7 (some 10) 0 (.d8 0x3)) 0xc0) (EffectPart.reads (.flag .SF) [.gpr 7, .gpr 10] []) (.flag .SF)) #v[7, 10]
    (.letOp (n := 83) (.out 0x1039e0 (cmpM8Imm8Effect 0x1039e0 6 (.sib 7 (some 10) 0 (.d8 0x3)) 0xc0) (EffectPart.reads (.flag .OF) [.gpr 7, .gpr 10] []) (.flag .OF)) #v[7, 10]
    (.letOp (n := 84) (.exec 0x1039e0 (LoadPre 0x1039e0 (fun s => AddrMode.addr (.sib 7 (some 10) 0 (.d8 0x3)) s (0x1039e0 + BitVec.ofNat 64 6)) 1) (cmpM8Imm8Effect 0x1039e0 6 (.sib 7 (some 10) 0 (.d8 0x3)) 0xc0) (Reg.operands [.gpr 7, .gpr 10] [])) #v[7, 10]
    (.letOp (n := 85) (.out 0x1039e6 (atFlags (condHolds 13) (setccR8Effect 0x1039e6 4 8)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF]) (.reg (.gpr 8))) #v[80, 82, 83]
    (.letOp (n := 86) (.exec 0x1039e6 (fun s => s.RIP = 0x1039e6) (atFlags (condHolds 13) (setccR8Effect 0x1039e6 4 8)) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF])) #v[80, 82, 83]
    (.letOp (n := 87) (.out 0x1039ea (addR64R64Effect 0x1039ea 8 14) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 14] []) (.reg (.gpr 8))) #v[85, 78]
    (.letOp (n := 88) (.exec 0x1039ea (fun s => s.RIP = 0x1039ea) (addR64R64Effect 0x1039ea 8 14) (Reg.operands [.gpr 8, .gpr 14] [])) #v[85, 78]
    (.letOp (n := 89) (.out 0x1039ed (addR64Imm8Effect 0x1039ed 10 0x4) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[10]
    (.letOp (n := 90) (.exec 0x1039ed (fun s => s.RIP = 0x1039ed) (addR64Imm8Effect 0x1039ed 10 0x4) (Reg.operands [.gpr 10] [])) #v[10]
    (.letOp (n := 91) (.out 0x1039f1 (cmpR64R64Effect 0x1039f1 11 10) (EffectPart.reads (.flag .ZF) [.gpr 11, .gpr 10] []) (.flag .ZF)) #v[11, 89]
    (.letOp (n := 92) (.exec 0x1039f1 (fun s => s.RIP = 0x1039f1) (cmpR64R64Effect 0x1039f1 11 10) (Reg.operands [.gpr 11, .gpr 10] [])) #v[11, 89]
    (.letOp (n := 93) (.pure (condOp 5)) #v[91]
    (.terminate (.condBr (Fin.last 93) ⟨.l1039b0, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 60), (4, 4), (5, 5), (6, 6), (7, 7), (8, 87), (9, 9), (10, 89), (11, 11), (14, 78), (19, 91), (22, 22), (39, 39), (50, 50), (51, 51)] 94⟩ ⟨.l1039f6, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 60), (4, 4), (5, 5), (6, 6), (7, 7), (8, 87), (9, 9), (10, 89), (11, 11), (14, 78), (19, 91), (22, 22), (39, 39), (50, 50), (51, 51)] 94⟩))))))))))))))))))))))))))))))))))))))))))

def bytes_l1039b0 : List UInt8 :=
  [0x31, 0xDB, 0x42, 0x80, 0x3C, 0x17, 0xC0, 0x0F, 0x9D, 0xC3, 0x4C, 0x01, 0xC3, 0x45, 0x31, 0xC0,
    0x42, 0x80, 0x7C, 0x17, 0x01, 0xC0, 0x41, 0x0F, 0x9D, 0xC0, 0x45, 0x31, 0xF6, 0x42, 0x80, 0x7C,
    0x17, 0x02, 0xC0, 0x41, 0x0F, 0x9D, 0xC6, 0x4D, 0x01, 0xC6, 0x49, 0x01, 0xDE, 0x45, 0x31, 0xC0,
    0x42, 0x80, 0x7C, 0x17, 0x03, 0xC0, 0x41, 0x0F, 0x9D, 0xC0, 0x4D, 0x01, 0xF0, 0x49, 0x83, 0xC2,
    0x04, 0x4D, 0x39, 0xD3, 0x75, 0xBA]

theorem code_l1039b0 : ∀ x ∈ codeRange 0x1039b0 bytes_l1039b0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x39b0 70 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1039f6 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1039f6 (testR64R64Effect 0x1039f6 9 9) (EffectPart.reads (.flag .ZF) [.gpr 9, .gpr 9] []) (.flag .ZF)) #v[9, 9]
    (.letOp (n := 54) (.exec 0x1039f6 (fun s => s.RIP = 0x1039f6) (testR64R64Effect 0x1039f6 9 9) (Reg.operands [.gpr 9, .gpr 9] [])) #v[9, 9]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l103a25, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l1039fb, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l1039f6 : List UInt8 :=
  [0x4D, 0x85, 0xC9, 0x74, 0x2A]

theorem code_l1039f6 : ∀ x ∈ codeRange 0x1039f6 bytes_l1039f6, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x39f6 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1039fb : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1039fb (addR64R64Effect 0x1039fb 10 7) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 7] []) (.reg (.gpr 10))) #v[10, 7]
    (.letOp (n := 54) (.exec 0x1039fb (fun s => s.RIP = 0x1039fb) (addR64R64Effect 0x1039fb 10 7) (Reg.operands [.gpr 10, .gpr 7] [])) #v[10, 7]
    (.letOp (n := 55) (.out 0x1039fe (xorR32R32Effect 0x1039fe 3 11 11) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 11] []) (.reg (.gpr 11))) #v[11, 11]
    (.letOp (n := 56) (.exec 0x1039fe (fun s => s.RIP = 0x1039fe) (xorR32R32Effect 0x1039fe 3 11 11) (Reg.operands [.gpr 11, .gpr 11] [])) #v[11, 11]
    (.letOp (n := 57) (.exec 0x103a01 (fun s => s.RIP = 0x103a01) (fun _ => nopEffect 0x103a01 15) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l103a10, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 55), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l1039fb : List UInt8 :=
  [0x49, 0x01, 0xFA, 0x45, 0x31, 0xDB, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x2E, 0x0F, 0x1F, 0x84,
    0x00, 0x00, 0x00, 0x00, 0x00]

theorem code_l1039fb : ∀ x ∈ codeRange 0x1039fb bytes_l1039fb, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x39fb 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103a10 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103a10 (xorR32R32Effect 0x103a10 2 3 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 3] []) (.reg (.gpr 3))) #v[3, 3]
    (.letOp (n := 54) (.exec 0x103a10 (fun s => s.RIP = 0x103a10) (xorR32R32Effect 0x103a10 2 3 3) (Reg.operands [.gpr 3, .gpr 3] [])) #v[3, 3]
    (.letOp (n := 55) (.out 0x103a12 (cmpM8Imm8Effect 0x103a12 5 (.sib 10 (some 11) 0 .none) 0xc0) (EffectPart.reads (.flag .SF) [.gpr 10, .gpr 11] []) (.flag .SF)) #v[10, 11]
    (.letOp (n := 56) (.out 0x103a12 (cmpM8Imm8Effect 0x103a12 5 (.sib 10 (some 11) 0 .none) 0xc0) (EffectPart.reads (.flag .OF) [.gpr 10, .gpr 11] []) (.flag .OF)) #v[10, 11]
    (.letOp (n := 57) (.exec 0x103a12 (LoadPre 0x103a12 (fun s => AddrMode.addr (.sib 10 (some 11) 0 .none) s (0x103a12 + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x103a12 5 (.sib 10 (some 11) 0 .none) 0xc0) (Reg.operands [.gpr 10, .gpr 11] [])) #v[10, 11]
    (.letOp (n := 58) (.out 0x103a17 (atFlags (condHolds 13) (setccR8Effect 0x103a17 3 3)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF]) (.reg (.gpr 3))) #v[53, 55, 56]
    (.letOp (n := 59) (.exec 0x103a17 (fun s => s.RIP = 0x103a17) (atFlags (condHolds 13) (setccR8Effect 0x103a17 3 3)) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF])) #v[53, 55, 56]
    (.letOp (n := 60) (.out 0x103a1a (addR64R64Effect 0x103a1a 8 3) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 3] []) (.reg (.gpr 8))) #v[8, 58]
    (.letOp (n := 61) (.exec 0x103a1a (fun s => s.RIP = 0x103a1a) (addR64R64Effect 0x103a1a 8 3) (Reg.operands [.gpr 8, .gpr 3] [])) #v[8, 58]
    (.letOp (n := 62) (.out 0x103a1d (incR64Effect 0x103a1d 11) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[11]
    (.letOp (n := 63) (.exec 0x103a1d (fun s => s.RIP = 0x103a1d) (incR64Effect 0x103a1d 11) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[11]
    (.letOp (n := 64) (.out 0x103a20 (cmpR64R64Effect 0x103a20 9 11) (EffectPart.reads (.flag .ZF) [.gpr 9, .gpr 11] []) (.flag .ZF)) #v[9, 62]
    (.letOp (n := 65) (.exec 0x103a20 (fun s => s.RIP = 0x103a20) (cmpR64R64Effect 0x103a20 9 11) (Reg.operands [.gpr 9, .gpr 11] [])) #v[9, 62]
    (.letOp (n := 66) (.pure (condOp 5)) #v[64]
    (.terminate (.condBr (Fin.last 66) ⟨.l103a10, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 58), (4, 4), (5, 5), (6, 6), (7, 7), (8, 60), (9, 9), (10, 10), (11, 62), (14, 14), (19, 64), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩ ⟨.l103a25, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 58), (4, 4), (5, 5), (6, 6), (7, 7), (8, 60), (9, 9), (10, 10), (11, 62), (14, 14), (19, 64), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩)))))))))))))))

def bytes_l103a10 : List UInt8 :=
  [0x31, 0xDB, 0x43, 0x80, 0x3C, 0x1A, 0xC0, 0x0F, 0x9D, 0xC3, 0x49, 0x01, 0xD8, 0x49, 0xFF, 0xC3,
    0x4D, 0x39, 0xD9, 0x75, 0xEB]

theorem code_l103a10 : ∀ x ∈ codeRange 0x103a10 bytes_l103a10, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3a10 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103a25 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103a25 (addR64R64Effect 0x103a25 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[7, 0]
    (.letOp (n := 54) (.exec 0x103a25 (fun s => s.RIP = 0x103a25) (addR64R64Effect 0x103a25 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[7, 0]
    (.letOp (n := 55) (.out 0x103a28 (testR64R64Effect 0x103a28 6 6) (EffectPart.reads (.flag .ZF) [.gpr 6, .gpr 6] []) (.flag .ZF)) #v[6, 6]
    (.letOp (n := 56) (.exec 0x103a28 (fun s => s.RIP = 0x103a28) (testR64R64Effect 0x103a28 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 57) (.pure (condOp 4)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l103ac0, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (11, 11), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l103a31, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (11, 11), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l103a25 : List UInt8 :=
  [0x48, 0x01, 0xC7, 0x48, 0x85, 0xF6, 0x0F, 0x84, 0x8F, 0x00, 0x00, 0x00]

theorem code_l103a25 : ∀ x ∈ codeRange 0x103a25 bytes_l103a25, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3a25 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103a31 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103a31 (movR64Imm64Effect 0x103a31 0 0x7ffffffffffffff8) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 54) (.exec 0x103a31 (fun s => s.RIP = 0x103a31) (movR64Imm64Effect 0x103a31 0 0x7ffffffffffffff8) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x103a3b (andR64R64Effect 0x103a3b 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[2, 53]
    (.letOp (n := 56) (.exec 0x103a3b (fun s => s.RIP = 0x103a3b) (andR64R64Effect 0x103a3b 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[2, 53]
    (.letOp (n := 57) (.out 0x103a3e (xorR32R32Effect 0x103a3e 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[53, 53]
    (.letOp (n := 58) (.exec 0x103a3e (fun s => s.RIP = 0x103a3e) (xorR32R32Effect 0x103a3e 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[53, 53]
    (.letOp (n := 59) (.out 0x103a40 (cmpM8Imm8Effect 0x103a40 4 (.sib 7 (some 2) 0 .none) 0xc0) (EffectPart.reads (.flag .SF) [.gpr 7, .gpr 2] []) (.flag .SF)) #v[7, 55]
    (.letOp (n := 60) (.out 0x103a40 (cmpM8Imm8Effect 0x103a40 4 (.sib 7 (some 2) 0 .none) 0xc0) (EffectPart.reads (.flag .OF) [.gpr 7, .gpr 2] []) (.flag .OF)) #v[7, 55]
    (.letOp (n := 61) (.exec 0x103a40 (LoadPre 0x103a40 (fun s => AddrMode.addr (.sib 7 (some 2) 0 .none) s (0x103a40 + BitVec.ofNat 64 4)) 1) (cmpM8Imm8Effect 0x103a40 4 (.sib 7 (some 2) 0 .none) 0xc0) (Reg.operands [.gpr 7, .gpr 2] [])) #v[7, 55]
    (.letOp (n := 62) (.out 0x103a44 (atFlags (condHolds 13) (setccR8Effect 0x103a44 3 0)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF]) (.reg (.gpr 0))) #v[57, 59, 60]
    (.letOp (n := 63) (.exec 0x103a44 (fun s => s.RIP = 0x103a44) (atFlags (condHolds 13) (setccR8Effect 0x103a44 3 0)) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF])) #v[57, 59, 60]
    (.letOp (n := 64) (.out 0x103a47 (cmpR32Imm8Effect 0x103a47 3 6 0x1) (EffectPart.reads (.flag .ZF) [.gpr 6] []) (.flag .ZF)) #v[6]
    (.letOp (n := 65) (.exec 0x103a47 (fun s => s.RIP = 0x103a47) (cmpR32Imm8Effect 0x103a47 3 6 0x1) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 66) (.pure (condOp 4)) #v[64]
    (.terminate (.condBr (Fin.last 66) ⟨.l103ac2, RegMap.args [(0, 62), (1, 1), (2, 55), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (19, 64), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩ ⟨.l103a4c, RegMap.args [(0, 62), (1, 1), (2, 55), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (19, 64), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩)))))))))))))))

def bytes_l103a31 : List UInt8 :=
  [0x48, 0xB8, 0xF8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F, 0x48, 0x21, 0xC2, 0x31, 0xC0, 0x80,
    0x3C, 0x17, 0xC0, 0x0F, 0x9D, 0xC0, 0x83, 0xFE, 0x01, 0x74, 0x76]

theorem code_l103a31 : ∀ x ∈ codeRange 0x103a31 bytes_l103a31, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3a31 27 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103a4c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103a4c (xorR32R32Effect 0x103a4c 3 9 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 9] []) (.reg (.gpr 9))) #v[9, 9]
    (.letOp (n := 54) (.exec 0x103a4c (fun s => s.RIP = 0x103a4c) (xorR32R32Effect 0x103a4c 3 9 9) (Reg.operands [.gpr 9, .gpr 9] [])) #v[9, 9]
    (.letOp (n := 55) (.out 0x103a4f (cmpM8Imm8Effect 0x103a4f 5 (.sib 7 (some 2) 0 (.d8 0x1)) 0xc0) (EffectPart.reads (.flag .SF) [.gpr 7, .gpr 2] []) (.flag .SF)) #v[7, 2]
    (.letOp (n := 56) (.out 0x103a4f (cmpM8Imm8Effect 0x103a4f 5 (.sib 7 (some 2) 0 (.d8 0x1)) 0xc0) (EffectPart.reads (.flag .OF) [.gpr 7, .gpr 2] []) (.flag .OF)) #v[7, 2]
    (.letOp (n := 57) (.exec 0x103a4f (LoadPre 0x103a4f (fun s => AddrMode.addr (.sib 7 (some 2) 0 (.d8 0x1)) s (0x103a4f + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x103a4f 5 (.sib 7 (some 2) 0 (.d8 0x1)) 0xc0) (Reg.operands [.gpr 7, .gpr 2] [])) #v[7, 2]
    (.letOp (n := 58) (.out 0x103a54 (atFlags (condHolds 13) (setccR8Effect 0x103a54 4 9)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF]) (.reg (.gpr 9))) #v[53, 55, 56]
    (.letOp (n := 59) (.exec 0x103a54 (fun s => s.RIP = 0x103a54) (atFlags (condHolds 13) (setccR8Effect 0x103a54 4 9)) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF])) #v[53, 55, 56]
    (.letOp (n := 60) (.out 0x103a58 (addR64R64Effect 0x103a58 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[0, 58]
    (.letOp (n := 61) (.exec 0x103a58 (fun s => s.RIP = 0x103a58) (addR64R64Effect 0x103a58 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[0, 58]
    (.letOp (n := 62) (.out 0x103a5b (cmpR32Imm8Effect 0x103a5b 3 6 0x2) (EffectPart.reads (.flag .ZF) [.gpr 6] []) (.flag .ZF)) #v[6]
    (.letOp (n := 63) (.exec 0x103a5b (fun s => s.RIP = 0x103a5b) (cmpR32Imm8Effect 0x103a5b 3 6 0x2) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 64) (.pure (condOp 4)) #v[62]
    (.terminate (.condBr (Fin.last 64) ⟨.l103ac2, RegMap.args [(0, 60), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 58), (11, 11), (14, 14), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)] 65⟩ ⟨.l103a60, RegMap.args [(0, 60), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 58), (11, 11), (14, 14), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)] 65⟩)))))))))))))

def bytes_l103a4c : List UInt8 :=
  [0x45, 0x31, 0xC9, 0x80, 0x7C, 0x17, 0x01, 0xC0, 0x41, 0x0F, 0x9D, 0xC1, 0x4C, 0x01, 0xC8, 0x83,
    0xFE, 0x02, 0x74, 0x62]

theorem code_l103a4c : ∀ x ∈ codeRange 0x103a4c bytes_l103a4c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3a4c 20 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103a60 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103a60 (xorR32R32Effect 0x103a60 3 9 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 9] []) (.reg (.gpr 9))) #v[9, 9]
    (.letOp (n := 54) (.exec 0x103a60 (fun s => s.RIP = 0x103a60) (xorR32R32Effect 0x103a60 3 9 9) (Reg.operands [.gpr 9, .gpr 9] [])) #v[9, 9]
    (.letOp (n := 55) (.out 0x103a63 (cmpM8Imm8Effect 0x103a63 5 (.sib 7 (some 2) 0 (.d8 0x2)) 0xc0) (EffectPart.reads (.flag .SF) [.gpr 7, .gpr 2] []) (.flag .SF)) #v[7, 2]
    (.letOp (n := 56) (.out 0x103a63 (cmpM8Imm8Effect 0x103a63 5 (.sib 7 (some 2) 0 (.d8 0x2)) 0xc0) (EffectPart.reads (.flag .OF) [.gpr 7, .gpr 2] []) (.flag .OF)) #v[7, 2]
    (.letOp (n := 57) (.exec 0x103a63 (LoadPre 0x103a63 (fun s => AddrMode.addr (.sib 7 (some 2) 0 (.d8 0x2)) s (0x103a63 + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x103a63 5 (.sib 7 (some 2) 0 (.d8 0x2)) 0xc0) (Reg.operands [.gpr 7, .gpr 2] [])) #v[7, 2]
    (.letOp (n := 58) (.out 0x103a68 (atFlags (condHolds 13) (setccR8Effect 0x103a68 4 9)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF]) (.reg (.gpr 9))) #v[53, 55, 56]
    (.letOp (n := 59) (.exec 0x103a68 (fun s => s.RIP = 0x103a68) (atFlags (condHolds 13) (setccR8Effect 0x103a68 4 9)) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF])) #v[53, 55, 56]
    (.letOp (n := 60) (.out 0x103a6c (addR64R64Effect 0x103a6c 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[0, 58]
    (.letOp (n := 61) (.exec 0x103a6c (fun s => s.RIP = 0x103a6c) (addR64R64Effect 0x103a6c 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[0, 58]
    (.letOp (n := 62) (.out 0x103a6f (cmpR32Imm8Effect 0x103a6f 3 6 0x3) (EffectPart.reads (.flag .ZF) [.gpr 6] []) (.flag .ZF)) #v[6]
    (.letOp (n := 63) (.exec 0x103a6f (fun s => s.RIP = 0x103a6f) (cmpR32Imm8Effect 0x103a6f 3 6 0x3) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 64) (.pure (condOp 4)) #v[62]
    (.terminate (.condBr (Fin.last 64) ⟨.l103ac2, RegMap.args [(0, 60), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 58), (11, 11), (14, 14), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)] 65⟩ ⟨.l103a74, RegMap.args [(0, 60), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 58), (11, 11), (14, 14), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)] 65⟩)))))))))))))

def bytes_l103a60 : List UInt8 :=
  [0x45, 0x31, 0xC9, 0x80, 0x7C, 0x17, 0x02, 0xC0, 0x41, 0x0F, 0x9D, 0xC1, 0x4C, 0x01, 0xC8, 0x83,
    0xFE, 0x03, 0x74, 0x4E]

theorem code_l103a60 : ∀ x ∈ codeRange 0x103a60 bytes_l103a60, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3a60 20 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103a74 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103a74 (xorR32R32Effect 0x103a74 3 9 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 9] []) (.reg (.gpr 9))) #v[9, 9]
    (.letOp (n := 54) (.exec 0x103a74 (fun s => s.RIP = 0x103a74) (xorR32R32Effect 0x103a74 3 9 9) (Reg.operands [.gpr 9, .gpr 9] [])) #v[9, 9]
    (.letOp (n := 55) (.out 0x103a77 (cmpM8Imm8Effect 0x103a77 5 (.sib 7 (some 2) 0 (.d8 0x3)) 0xc0) (EffectPart.reads (.flag .SF) [.gpr 7, .gpr 2] []) (.flag .SF)) #v[7, 2]
    (.letOp (n := 56) (.out 0x103a77 (cmpM8Imm8Effect 0x103a77 5 (.sib 7 (some 2) 0 (.d8 0x3)) 0xc0) (EffectPart.reads (.flag .OF) [.gpr 7, .gpr 2] []) (.flag .OF)) #v[7, 2]
    (.letOp (n := 57) (.exec 0x103a77 (LoadPre 0x103a77 (fun s => AddrMode.addr (.sib 7 (some 2) 0 (.d8 0x3)) s (0x103a77 + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x103a77 5 (.sib 7 (some 2) 0 (.d8 0x3)) 0xc0) (Reg.operands [.gpr 7, .gpr 2] [])) #v[7, 2]
    (.letOp (n := 58) (.out 0x103a7c (atFlags (condHolds 13) (setccR8Effect 0x103a7c 4 9)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF]) (.reg (.gpr 9))) #v[53, 55, 56]
    (.letOp (n := 59) (.exec 0x103a7c (fun s => s.RIP = 0x103a7c) (atFlags (condHolds 13) (setccR8Effect 0x103a7c 4 9)) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF])) #v[53, 55, 56]
    (.letOp (n := 60) (.out 0x103a80 (addR64R64Effect 0x103a80 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[0, 58]
    (.letOp (n := 61) (.exec 0x103a80 (fun s => s.RIP = 0x103a80) (addR64R64Effect 0x103a80 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[0, 58]
    (.letOp (n := 62) (.out 0x103a83 (cmpR32Imm8Effect 0x103a83 3 6 0x4) (EffectPart.reads (.flag .ZF) [.gpr 6] []) (.flag .ZF)) #v[6]
    (.letOp (n := 63) (.exec 0x103a83 (fun s => s.RIP = 0x103a83) (cmpR32Imm8Effect 0x103a83 3 6 0x4) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 64) (.pure (condOp 4)) #v[62]
    (.terminate (.condBr (Fin.last 64) ⟨.l103ac2, RegMap.args [(0, 60), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 58), (11, 11), (14, 14), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)] 65⟩ ⟨.l103a88, RegMap.args [(0, 60), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 58), (11, 11), (14, 14), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)] 65⟩)))))))))))))

def bytes_l103a74 : List UInt8 :=
  [0x45, 0x31, 0xC9, 0x80, 0x7C, 0x17, 0x03, 0xC0, 0x41, 0x0F, 0x9D, 0xC1, 0x4C, 0x01, 0xC8, 0x83,
    0xFE, 0x04, 0x74, 0x3A]

theorem code_l103a74 : ∀ x ∈ codeRange 0x103a74 bytes_l103a74, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3a74 20 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103a88 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103a88 (xorR32R32Effect 0x103a88 3 9 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 9] []) (.reg (.gpr 9))) #v[9, 9]
    (.letOp (n := 54) (.exec 0x103a88 (fun s => s.RIP = 0x103a88) (xorR32R32Effect 0x103a88 3 9 9) (Reg.operands [.gpr 9, .gpr 9] [])) #v[9, 9]
    (.letOp (n := 55) (.out 0x103a8b (cmpM8Imm8Effect 0x103a8b 5 (.sib 7 (some 2) 0 (.d8 0x4)) 0xc0) (EffectPart.reads (.flag .SF) [.gpr 7, .gpr 2] []) (.flag .SF)) #v[7, 2]
    (.letOp (n := 56) (.out 0x103a8b (cmpM8Imm8Effect 0x103a8b 5 (.sib 7 (some 2) 0 (.d8 0x4)) 0xc0) (EffectPart.reads (.flag .OF) [.gpr 7, .gpr 2] []) (.flag .OF)) #v[7, 2]
    (.letOp (n := 57) (.exec 0x103a8b (LoadPre 0x103a8b (fun s => AddrMode.addr (.sib 7 (some 2) 0 (.d8 0x4)) s (0x103a8b + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x103a8b 5 (.sib 7 (some 2) 0 (.d8 0x4)) 0xc0) (Reg.operands [.gpr 7, .gpr 2] [])) #v[7, 2]
    (.letOp (n := 58) (.out 0x103a90 (atFlags (condHolds 13) (setccR8Effect 0x103a90 4 9)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF]) (.reg (.gpr 9))) #v[53, 55, 56]
    (.letOp (n := 59) (.exec 0x103a90 (fun s => s.RIP = 0x103a90) (atFlags (condHolds 13) (setccR8Effect 0x103a90 4 9)) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF])) #v[53, 55, 56]
    (.letOp (n := 60) (.out 0x103a94 (addR64R64Effect 0x103a94 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[0, 58]
    (.letOp (n := 61) (.exec 0x103a94 (fun s => s.RIP = 0x103a94) (addR64R64Effect 0x103a94 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[0, 58]
    (.letOp (n := 62) (.out 0x103a97 (cmpR32Imm8Effect 0x103a97 3 6 0x5) (EffectPart.reads (.flag .ZF) [.gpr 6] []) (.flag .ZF)) #v[6]
    (.letOp (n := 63) (.exec 0x103a97 (fun s => s.RIP = 0x103a97) (cmpR32Imm8Effect 0x103a97 3 6 0x5) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 64) (.pure (condOp 4)) #v[62]
    (.terminate (.condBr (Fin.last 64) ⟨.l103ac2, RegMap.args [(0, 60), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 58), (11, 11), (14, 14), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)] 65⟩ ⟨.l103a9c, RegMap.args [(0, 60), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 58), (11, 11), (14, 14), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)] 65⟩)))))))))))))

def bytes_l103a88 : List UInt8 :=
  [0x45, 0x31, 0xC9, 0x80, 0x7C, 0x17, 0x04, 0xC0, 0x41, 0x0F, 0x9D, 0xC1, 0x4C, 0x01, 0xC8, 0x83,
    0xFE, 0x05, 0x74, 0x26]

theorem code_l103a88 : ∀ x ∈ codeRange 0x103a88 bytes_l103a88, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3a88 20 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103a9c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103a9c (xorR32R32Effect 0x103a9c 3 9 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 9] []) (.reg (.gpr 9))) #v[9, 9]
    (.letOp (n := 54) (.exec 0x103a9c (fun s => s.RIP = 0x103a9c) (xorR32R32Effect 0x103a9c 3 9 9) (Reg.operands [.gpr 9, .gpr 9] [])) #v[9, 9]
    (.letOp (n := 55) (.out 0x103a9f (cmpM8Imm8Effect 0x103a9f 5 (.sib 7 (some 2) 0 (.d8 0x5)) 0xc0) (EffectPart.reads (.flag .SF) [.gpr 7, .gpr 2] []) (.flag .SF)) #v[7, 2]
    (.letOp (n := 56) (.out 0x103a9f (cmpM8Imm8Effect 0x103a9f 5 (.sib 7 (some 2) 0 (.d8 0x5)) 0xc0) (EffectPart.reads (.flag .OF) [.gpr 7, .gpr 2] []) (.flag .OF)) #v[7, 2]
    (.letOp (n := 57) (.exec 0x103a9f (LoadPre 0x103a9f (fun s => AddrMode.addr (.sib 7 (some 2) 0 (.d8 0x5)) s (0x103a9f + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x103a9f 5 (.sib 7 (some 2) 0 (.d8 0x5)) 0xc0) (Reg.operands [.gpr 7, .gpr 2] [])) #v[7, 2]
    (.letOp (n := 58) (.out 0x103aa4 (atFlags (condHolds 13) (setccR8Effect 0x103aa4 4 9)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF]) (.reg (.gpr 9))) #v[53, 55, 56]
    (.letOp (n := 59) (.exec 0x103aa4 (fun s => s.RIP = 0x103aa4) (atFlags (condHolds 13) (setccR8Effect 0x103aa4 4 9)) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF])) #v[53, 55, 56]
    (.letOp (n := 60) (.out 0x103aa8 (addR64R64Effect 0x103aa8 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[0, 58]
    (.letOp (n := 61) (.exec 0x103aa8 (fun s => s.RIP = 0x103aa8) (addR64R64Effect 0x103aa8 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[0, 58]
    (.letOp (n := 62) (.out 0x103aab (cmpR32Imm8Effect 0x103aab 3 6 0x6) (EffectPart.reads (.flag .ZF) [.gpr 6] []) (.flag .ZF)) #v[6]
    (.letOp (n := 63) (.exec 0x103aab (fun s => s.RIP = 0x103aab) (cmpR32Imm8Effect 0x103aab 3 6 0x6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 64) (.pure (condOp 4)) #v[62]
    (.terminate (.condBr (Fin.last 64) ⟨.l103ac2, RegMap.args [(0, 60), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 58), (11, 11), (14, 14), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)] 65⟩ ⟨.l103ab0, RegMap.args [(0, 60), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 58), (11, 11), (14, 14), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)] 65⟩)))))))))))))

def bytes_l103a9c : List UInt8 :=
  [0x45, 0x31, 0xC9, 0x80, 0x7C, 0x17, 0x05, 0xC0, 0x41, 0x0F, 0x9D, 0xC1, 0x4C, 0x01, 0xC8, 0x83,
    0xFE, 0x06, 0x74, 0x12]

theorem code_l103a9c : ∀ x ∈ codeRange 0x103a9c bytes_l103a9c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3a9c 20 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103ab0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103ab0 (xorR32R32Effect 0x103ab0 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[6, 6]
    (.letOp (n := 54) (.exec 0x103ab0 (fun s => s.RIP = 0x103ab0) (xorR32R32Effect 0x103ab0 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 55) (.out 0x103ab2 (cmpM8Imm8Effect 0x103ab2 5 (.sib 7 (some 2) 0 (.d8 0x6)) 0xc0) (EffectPart.reads (.flag .SF) [.gpr 7, .gpr 2] []) (.flag .SF)) #v[7, 2]
    (.letOp (n := 56) (.out 0x103ab2 (cmpM8Imm8Effect 0x103ab2 5 (.sib 7 (some 2) 0 (.d8 0x6)) 0xc0) (EffectPart.reads (.flag .OF) [.gpr 7, .gpr 2] []) (.flag .OF)) #v[7, 2]
    (.letOp (n := 57) (.exec 0x103ab2 (LoadPre 0x103ab2 (fun s => AddrMode.addr (.sib 7 (some 2) 0 (.d8 0x6)) s (0x103ab2 + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x103ab2 5 (.sib 7 (some 2) 0 (.d8 0x6)) 0xc0) (Reg.operands [.gpr 7, .gpr 2] [])) #v[7, 2]
    (.letOp (n := 58) (.out 0x103ab7 (atFlags (condHolds 13) (setccR8Effect 0x103ab7 4 6)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF]) (.reg (.gpr 6))) #v[53, 55, 56]
    (.letOp (n := 59) (.exec 0x103ab7 (fun s => s.RIP = 0x103ab7) (atFlags (condHolds 13) (setccR8Effect 0x103ab7 4 6)) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF])) #v[53, 55, 56]
    (.letOp (n := 60) (.out 0x103abb (addR64R64Effect 0x103abb 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[0, 58]
    (.letOp (n := 61) (.exec 0x103abb (fun s => s.RIP = 0x103abb) (addR64R64Effect 0x103abb 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[0, 58]
    (.terminate (.br ⟨.l103ac2, RegMap.args [(0, 60), (1, 1), (2, 2), (4, 4), (5, 5), (6, 58), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩))))))))))

def bytes_l103ab0 : List UInt8 :=
  [0x31, 0xF6, 0x80, 0x7C, 0x17, 0x06, 0xC0, 0x40, 0x0F, 0x9D, 0xC6, 0x48, 0x01, 0xF0, 0xEB, 0x02]

theorem code_l103ab0 : ∀ x ∈ codeRange 0x103ab0 bytes_l103ab0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3ab0 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103ac0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103ac0 (xorR32R32Effect 0x103ac0 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[0, 0]
    (.letOp (n := 54) (.exec 0x103ac0 (fun s => s.RIP = 0x103ac0) (xorR32R32Effect 0x103ac0 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.terminate (.br ⟨.l103ac2, RegMap.args [(0, 53), (1, 1), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l103ac0 : List UInt8 :=
  [0x31, 0xC0]

theorem code_l103ac0 : ∀ x ∈ codeRange 0x103ac0 bytes_l103ac0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3ac0 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103ac2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103ac2 (addR64R64Effect 0x103ac2 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 8] []) (.reg (.gpr 0))) #v[0, 8]
    (.letOp (n := 54) (.exec 0x103ac2 (fun s => s.RIP = 0x103ac2) (addR64R64Effect 0x103ac2 0 8) (Reg.operands [.gpr 0, .gpr 8] [])) #v[0, 8]
    (.letOp (n := 55) (.out 0x103ac5 (movR64Imm64Effect 0x103ac5 8 0x101010101010101) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 56) (.exec 0x103ac5 (fun s => s.RIP = 0x103ac5) (movR64Imm64Effect 0x103ac5 8 0x101010101010101) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x103acf (movR64Imm64Effect 0x103acf 6 0xff00ff00ff00ff) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 58) (.exec 0x103acf (fun s => s.RIP = 0x103acf) (movR64Imm64Effect 0x103acf 6 0xff00ff00ff00ff) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x103ad9 (movR64Imm64Effect 0x103ad9 2 0x1000100010001) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 60) (.exec 0x103ad9 (fun s => s.RIP = 0x103ad9) (movR64Imm64Effect 0x103ad9 2 0x1000100010001) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l103b24, RegMap.args [(0, 53), (1, 1), (2, 59), (4, 4), (5, 5), (6, 57), (7, 7), (8, 55), (9, 9), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩)))))))))

def bytes_l103ac2 : List UInt8 :=
  [0x4C, 0x01, 0xC0, 0x49, 0xB8, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x48, 0xBE, 0xFF,
    0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0x48, 0xBA, 0x01, 0x00, 0x01, 0x00, 0x01, 0x00, 0x01,
    0x00, 0xEB, 0x3F]

theorem code_l103ac2 : ∀ x ∈ codeRange 0x103ac2 bytes_l103ac2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3ac2 35 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103af0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103af0 (xorR32R32Effect 0x103af0 3 14 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 14] []) (.reg (.gpr 14))) #v[14, 14]
    (.letOp (n := 54) (.exec 0x103af0 (fun s => s.RIP = 0x103af0) (xorR32R32Effect 0x103af0 3 14 14) (Reg.operands [.gpr 14, .gpr 14] [])) #v[14, 14]
    (.terminate (.br ⟨.l103af3, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (14, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l103af0 : List UInt8 :=
  [0x45, 0x31, 0xF6]

theorem code_l103af0 : ∀ x ∈ codeRange 0x103af0 bytes_l103af0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3af0 3 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103af3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103af3 (addR64R64Effect 0x103af3 7 9) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 9] []) (.reg (.gpr 7))) #v[7, 9]
    (.letOp (n := 54) (.exec 0x103af3 (fun s => s.RIP = 0x103af3) (addR64R64Effect 0x103af3 7 9) (Reg.operands [.gpr 7, .gpr 9] [])) #v[7, 9]
    (.letOp (n := 55) (.out 0x103af6 (subR64R64Effect 0x103af6 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10] []) (.reg (.gpr 1))) #v[1, 10]
    (.letOp (n := 56) (.exec 0x103af6 (fun s => s.RIP = 0x103af6) (subR64R64Effect 0x103af6 1 10) (Reg.operands [.gpr 1, .gpr 10] [])) #v[1, 10]
    (.letOp (n := 57) (.out 0x103af9 (movR32R32Effect 0x103af9 3 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 10] []) (.reg (.gpr 11))) #v[10]
    (.letOp (n := 58) (.exec 0x103af9 (fun s => s.RIP = 0x103af9) (movR32R32Effect 0x103af9 3 11 10) (Reg.operands [.gpr 10] [])) #v[10]
    (.letOp (n := 59) (.out 0x103afc (andR32Imm8Effect 0x103afc 4 11 0x3) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11] []) (.reg (.gpr 11))) #v[57]
    (.letOp (n := 60) (.exec 0x103afc (fun s => s.RIP = 0x103afc) (andR32Imm8Effect 0x103afc 4 11 0x3) (Reg.operands [.gpr 11] [])) #v[57]
    (.letOp (n := 61) (.out 0x103b00 (movR64R64Effect 0x103b00 3 14) (EffectPart.reads (.reg (.gpr 3)) [.gpr 14] []) (.reg (.gpr 3))) #v[14]
    (.letOp (n := 62) (.exec 0x103b00 (fun s => s.RIP = 0x103b00) (movR64R64Effect 0x103b00 3 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 63) (.out 0x103b03 (andR64R64Effect 0x103b03 3 6) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 6] []) (.reg (.gpr 3))) #v[61, 6]
    (.letOp (n := 64) (.exec 0x103b03 (fun s => s.RIP = 0x103b03) (andR64R64Effect 0x103b03 3 6) (Reg.operands [.gpr 3, .gpr 6] [])) #v[61, 6]
    (.letOp (n := 65) (.out 0x103b06 (shrR64Effect 0x103b06 4 14 8) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[14]
    (.letOp (n := 66) (.exec 0x103b06 (fun s => s.RIP = 0x103b06) (shrR64Effect 0x103b06 4 14 8) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[14]
    (.letOp (n := 67) (.out 0x103b0a (andR64R64Effect 0x103b0a 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 6] []) (.reg (.gpr 14))) #v[65, 6]
    (.letOp (n := 68) (.exec 0x103b0a (fun s => s.RIP = 0x103b0a) (andR64R64Effect 0x103b0a 14 6) (Reg.operands [.gpr 14, .gpr 6] [])) #v[65, 6]
    (.letOp (n := 69) (.out 0x103b0d (addR64R64Effect 0x103b0d 14 3) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 3] []) (.reg (.gpr 14))) #v[67, 63]
    (.letOp (n := 70) (.exec 0x103b0d (fun s => s.RIP = 0x103b0d) (addR64R64Effect 0x103b0d 14 3) (Reg.operands [.gpr 14, .gpr 3] [])) #v[67, 63]
    (.letOp (n := 71) (.out 0x103b10 (imulR64R64Effect 0x103b10 4 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 2] []) (.reg (.gpr 14))) #v[69, 2]
    (.letOp (n := 72) (.exec 0x103b10 (fun s => s.RIP = 0x103b10) (imulR64R64Effect 0x103b10 4 14 2) (Reg.operands [.gpr 14, .gpr 2] [])) #v[69, 2]
    (.letOp (n := 73) (.out 0x103b14 (shrR64Effect 0x103b14 4 14 48) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[71]
    (.letOp (n := 74) (.exec 0x103b14 (fun s => s.RIP = 0x103b14) (shrR64Effect 0x103b14 4 14 48) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[71]
    (.letOp (n := 75) (.out 0x103b18 (addR64R64Effect 0x103b18 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[0, 73]
    (.letOp (n := 76) (.exec 0x103b18 (fun s => s.RIP = 0x103b18) (addR64R64Effect 0x103b18 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[0, 73]
    (.letOp (n := 77) (.out 0x103b1b (testR64R64Effect 0x103b1b 11 11) (EffectPart.reads (.flag .ZF) [.gpr 11, .gpr 11] []) (.flag .ZF)) #v[59, 59]
    (.letOp (n := 78) (.exec 0x103b1b (fun s => s.RIP = 0x103b1b) (testR64R64Effect 0x103b1b 11 11) (Reg.operands [.gpr 11, .gpr 11] [])) #v[59, 59]
    (.letOp (n := 79) (.pure (condOp 5)) #v[77]
    (.terminate (.condBr (Fin.last 79) ⟨.l103bd9, RegMap.args [(0, 75), (1, 55), (2, 2), (3, 63), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 59), (14, 73), (19, 77), (22, 22), (39, 39), (50, 50), (51, 51)] 80⟩ ⟨.l103b24, RegMap.args [(0, 75), (1, 55), (2, 2), (3, 63), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 59), (14, 73), (19, 77), (22, 22), (39, 39), (50, 50), (51, 51)] 80⟩))))))))))))))))))))))))))))

def bytes_l103af3 : List UInt8 :=
  [0x4C, 0x01, 0xCF, 0x4C, 0x29, 0xD1, 0x45, 0x89, 0xD3, 0x41, 0x83, 0xE3, 0x03, 0x4C, 0x89, 0xF3,
    0x48, 0x21, 0xF3, 0x49, 0xC1, 0xEE, 0x08, 0x49, 0x21, 0xF6, 0x49, 0x01, 0xDE, 0x4C, 0x0F, 0xAF,
    0xF2, 0x49, 0xC1, 0xEE, 0x30, 0x4C, 0x01, 0xF0, 0x4D, 0x85, 0xDB, 0x0F, 0x85, 0xB5, 0x00, 0x00,
    0x00]

theorem code_l103af3 : ∀ x ∈ codeRange 0x103af3 bytes_l103af3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3af3 49 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103b24 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103b24 (testR64R64Effect 0x103b24 1 1) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 1] []) (.flag .ZF)) #v[1, 1]
    (.letOp (n := 54) (.exec 0x103b24 (fun s => s.RIP = 0x103b24) (testR64R64Effect 0x103b24 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[1, 1]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l103c5a, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l103b2d, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l103b24 : List UInt8 :=
  [0x48, 0x85, 0xC9, 0x0F, 0x84, 0x2D, 0x01, 0x00, 0x00]

theorem code_l103b24 : ∀ x ∈ codeRange 0x103b24 bytes_l103b24, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3b24 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103b2d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103b2d (movR64R64Effect 0x103b2d 9 7) (EffectPart.reads (.reg (.gpr 9)) [.gpr 7] []) (.reg (.gpr 9))) #v[7]
    (.letOp (n := 54) (.exec 0x103b2d (fun s => s.RIP = 0x103b2d) (movR64R64Effect 0x103b2d 9 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 55) (.out 0x103b30 (cmpR64Imm32Effect 0x103b30 1 0xc0) (EffectPart.reads (.flag .CF) [.gpr 1] []) (.flag .CF)) #v[1]
    (.letOp (n := 56) (.exec 0x103b30 (fun s => s.RIP = 0x103b30) (cmpR64Imm32Effect 0x103b30 1 0xc0) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 57) (.out 0x103b37 (movR32Imm32Effect 0x103b37 6 10 0xc0) (EffectPart.reads (.reg (.gpr 10)) [] []) (.reg (.gpr 10))) #v[]
    (.letOp (n := 58) (.exec 0x103b37 (fun s => s.RIP = 0x103b37) (movR32Imm32Effect 0x103b37 6 10 0xc0) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x103b3d (atFlags (condHolds 2) (cmovR64R64Effect 0x103b3d 4 10 1)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[57, 1, 55]
    (.letOp (n := 60) (.exec 0x103b3d (fun s => s.RIP = 0x103b3d) (atFlags (condHolds 2) (cmovR64R64Effect 0x103b3d 4 10 1)) (Reg.operands [.gpr 10, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[57, 1, 55]
    (.letOp (n := 61) (.out 0x103b41 (leaR32Effect 0x103b41 8 7 (.abs (some 10) 3 0x0)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 10] []) (.reg (.gpr 7))) #v[59]
    (.letOp (n := 62) (.exec 0x103b41 (fun s => s.RIP = 0x103b41) (leaR32Effect 0x103b41 8 7 (.abs (some 10) 3 0x0)) (Reg.operands [.gpr 10] [])) #v[59]
    (.letOp (n := 63) (.out 0x103b49 (movR32R32Effect 0x103b49 3 11 7) (EffectPart.reads (.reg (.gpr 11)) [.gpr 7] []) (.reg (.gpr 11))) #v[61]
    (.letOp (n := 64) (.exec 0x103b49 (fun s => s.RIP = 0x103b49) (movR32R32Effect 0x103b49 3 11 7) (Reg.operands [.gpr 7] [])) #v[61]
    (.letOp (n := 65) (.out 0x103b4c (andR32Imm32Effect 0x103b4c 7 11 0x7e0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11] []) (.reg (.gpr 11))) #v[63]
    (.letOp (n := 66) (.out 0x103b4c (andR32Imm32Effect 0x103b4c 7 11 0x7e0) (EffectPart.reads (.flag .ZF) [.gpr 11] []) (.flag .ZF)) #v[63]
    (.letOp (n := 67) (.exec 0x103b4c (fun s => s.RIP = 0x103b4c) (andR32Imm32Effect 0x103b4c 7 11 0x7e0) (Reg.operands [.gpr 11] [])) #v[63]
    (.letOp (n := 68) (.pure (condOp 4)) #v[66]
    (.terminate (.condBr (Fin.last 68) ⟨.l103af0, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 61), (8, 8), (9, 53), (10, 59), (11, 65), (14, 14), (19, 66), (22, 22), (39, 39), (50, 50), (51, 51)] 69⟩ ⟨.l103b55, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 61), (8, 8), (9, 53), (10, 59), (11, 65), (14, 14), (19, 66), (22, 22), (39, 39), (50, 50), (51, 51)] 69⟩)))))))))))))))))

def bytes_l103b2d : List UInt8 :=
  [0x49, 0x89, 0xF9, 0x48, 0x81, 0xF9, 0xC0, 0x00, 0x00, 0x00, 0x41, 0xBA, 0xC0, 0x00, 0x00, 0x00,
    0x4C, 0x0F, 0x42, 0xD1, 0x42, 0x8D, 0x3C, 0xD5, 0x00, 0x00, 0x00, 0x00, 0x41, 0x89, 0xFB, 0x41,
    0x81, 0xE3, 0xE0, 0x07, 0x00, 0x00, 0x74, 0x9B]

theorem code_l103b2d : ∀ x ∈ codeRange 0x103b2d bytes_l103b2d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3b2d 40 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103b55 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103b55 (addR64R64Effect 0x103b55 11 9) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 9] []) (.reg (.gpr 11))) #v[11, 9]
    (.letOp (n := 54) (.exec 0x103b55 (fun s => s.RIP = 0x103b55) (addR64R64Effect 0x103b55 11 9) (Reg.operands [.gpr 11, .gpr 9] [])) #v[11, 9]
    (.letOp (n := 55) (.out 0x103b58 (xorR32R32Effect 0x103b58 3 14 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 14] []) (.reg (.gpr 14))) #v[14, 14]
    (.letOp (n := 56) (.exec 0x103b58 (fun s => s.RIP = 0x103b58) (xorR32R32Effect 0x103b58 3 14 14) (Reg.operands [.gpr 14, .gpr 14] [])) #v[14, 14]
    (.letOp (n := 57) (.out 0x103b5b (movR64R64Effect 0x103b5b 3 9) (EffectPart.reads (.reg (.gpr 3)) [.gpr 9] []) (.reg (.gpr 3))) #v[9]
    (.letOp (n := 58) (.exec 0x103b5b (fun s => s.RIP = 0x103b5b) (movR64R64Effect 0x103b5b 3 9) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 59) (.exec 0x103b5e (fun s => s.RIP = 0x103b5e) (fun _ => nopEffect 0x103b5e 2) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l103b60, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 53), (14, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l103b55 : List UInt8 :=
  [0x4D, 0x01, 0xCB, 0x45, 0x31, 0xF6, 0x4C, 0x89, 0xCB, 0x66, 0x90]

theorem code_l103b55 : ∀ x ∈ codeRange 0x103b55 bytes_l103b55, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3b55 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103b60_1 : Block Op Label signature Reg.count 93 :=
  .letOp (n := 93) (.out 0x103ba4 (orR64R64Effect 0x103ba4 13 14) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 14] []) (.reg (.gpr 13))) #v[91, 89]
    (.letOp (n := 94) (.exec 0x103ba4 (fun s => s.RIP = 0x103ba4) (orR64R64Effect 0x103ba4 13 14) (Reg.operands [.gpr 13, .gpr 14] [])) #v[91, 89]
    (.letOp (n := 95) (.out 0x103ba7 (andR64R64Effect 0x103ba7 13 8) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 8] []) (.reg (.gpr 13))) #v[93, 8]
    (.letOp (n := 96) (.exec 0x103ba7 (fun s => s.RIP = 0x103ba7) (andR64R64Effect 0x103ba7 13 8) (Reg.operands [.gpr 13, .gpr 8] [])) #v[93, 8]
    (.letOp (n := 97) (.out 0x103baa (addR64R64Effect 0x103baa 13 12) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 12] []) (.reg (.gpr 13))) #v[95, 81]
    (.letOp (n := 98) (.exec 0x103baa (fun s => s.RIP = 0x103baa) (addR64R64Effect 0x103baa 13 12) (Reg.operands [.gpr 13, .gpr 12] [])) #v[95, 81]
    (.letOp (n := 99) (.out 0x103bad (addR64R64Effect 0x103bad 13 15) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 15] []) (.reg (.gpr 13))) #v[97, 69]
    (.letOp (n := 100) (.exec 0x103bad (fun s => s.RIP = 0x103bad) (addR64R64Effect 0x103bad 13 15) (Reg.operands [.gpr 13, .gpr 15] [])) #v[97, 69]
    (.letOp (n := 101) (.out 0x103bb0 (movR64M64Effect 0x103bb0 14 (.base 3 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 3] []) (.reg (.gpr 14))) #v[3]
    (.letOp (n := 102) (.exec 0x103bb0 (LoadPre 0x103bb0 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x103bb0 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x103bb0 14 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 103) (.out 0x103bb4 (movR64R64Effect 0x103bb4 15 14) (EffectPart.reads (.reg (.gpr 15)) [.gpr 14] []) (.reg (.gpr 15))) #v[101]
    (.letOp (n := 104) (.exec 0x103bb4 (fun s => s.RIP = 0x103bb4) (movR64R64Effect 0x103bb4 15 14) (Reg.operands [.gpr 14] [])) #v[101]
    (.letOp (n := 105) (.out 0x103bb7 (notR64Effect 0x103bb7 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15] []) (.reg (.gpr 15))) #v[103]
    (.letOp (n := 106) (.exec 0x103bb7 (fun s => s.RIP = 0x103bb7) (notR64Effect 0x103bb7 15) (Reg.operands [.gpr 15] [])) #v[103]
    (.letOp (n := 107) (.out 0x103bba (shrR64Effect 0x103bba 4 15 7) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[105]
    (.letOp (n := 108) (.exec 0x103bba (fun s => s.RIP = 0x103bba) (shrR64Effect 0x103bba 4 15 7) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[105]
    (.letOp (n := 109) (.out 0x103bbe (shrR64Effect 0x103bbe 4 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[101]
    (.letOp (n := 110) (.exec 0x103bbe (fun s => s.RIP = 0x103bbe) (shrR64Effect 0x103bbe 4 14 6) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[101]
    (.letOp (n := 111) (.out 0x103bc2 (orR64R64Effect 0x103bc2 14 15) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 15] []) (.reg (.gpr 14))) #v[109, 107]
    (.letOp (n := 112) (.exec 0x103bc2 (fun s => s.RIP = 0x103bc2) (orR64R64Effect 0x103bc2 14 15) (Reg.operands [.gpr 14, .gpr 15] [])) #v[109, 107]
    (.letOp (n := 113) (.out 0x103bc5 (andR64R64Effect 0x103bc5 14 8) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 8] []) (.reg (.gpr 14))) #v[111, 8]
    (.letOp (n := 114) (.exec 0x103bc5 (fun s => s.RIP = 0x103bc5) (andR64R64Effect 0x103bc5 14 8) (Reg.operands [.gpr 14, .gpr 8] [])) #v[111, 8]
    (.letOp (n := 115) (.out 0x103bc8 (addR64R64Effect 0x103bc8 14 13) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 13] []) (.reg (.gpr 14))) #v[113, 99]
    (.letOp (n := 116) (.exec 0x103bc8 (fun s => s.RIP = 0x103bc8) (addR64R64Effect 0x103bc8 14 13) (Reg.operands [.gpr 14, .gpr 13] [])) #v[113, 99]
    (.letOp (n := 117) (.out 0x103bcb (addR64Imm8Effect 0x103bcb 3 0x20) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[3]
    (.letOp (n := 118) (.exec 0x103bcb (fun s => s.RIP = 0x103bcb) (addR64Imm8Effect 0x103bcb 3 0x20) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 119) (.out 0x103bcf (cmpR64R64Effect 0x103bcf 3 11) (EffectPart.reads (.flag .ZF) [.gpr 3, .gpr 11] []) (.flag .ZF)) #v[117, 11]
    (.letOp (n := 120) (.exec 0x103bcf (fun s => s.RIP = 0x103bcf) (cmpR64R64Effect 0x103bcf 3 11) (Reg.operands [.gpr 3, .gpr 11] [])) #v[117, 11]
    (.letOp (n := 121) (.pure (condOp 5)) #v[119]
    (.terminate (.condBr (Fin.last 121) ⟨.l103b60, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 117), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 81), (13, 99), (14, 115), (15, 107), (19, 119), (22, 22), (39, 39), (50, 50), (51, 51)] 122⟩ ⟨.l103bd4, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 117), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 81), (13, 99), (14, 115), (15, 107), (19, 119), (22, 22), (39, 39), (50, 50), (51, 51)] 122⟩))))))))))))))))))))))))))))))

def bytes_l103b60_1 : List UInt8 :=
  [0x4D, 0x09, 0xF5, 0x4D, 0x21, 0xC5, 0x4D, 0x01, 0xE5, 0x4D, 0x01, 0xFD, 0x4C, 0x8B, 0x73, 0x18,
    0x4D, 0x89, 0xF7, 0x49, 0xF7, 0xD7, 0x49, 0xC1, 0xEF, 0x07, 0x49, 0xC1, 0xEE, 0x06, 0x4D, 0x09,
    0xFE, 0x4D, 0x21, 0xC6, 0x4D, 0x01, 0xEE, 0x48, 0x83, 0xC3, 0x20, 0x4C, 0x39, 0xDB, 0x75, 0x8C]

theorem code_l103b60_1 : ∀ x ∈ codeRange 0x103ba4 bytes_l103b60_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3ba4 48 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103b60 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103b60 (movR64M64Effect 0x103b60 15 (.base 3 .none)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 3] []) (.reg (.gpr 15))) #v[3]
    (.letOp (n := 54) (.exec 0x103b60 (LoadPre 0x103b60 (fun s => AddrMode.addr (.base 3 .none) s (0x103b60 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x103b60 15 (.base 3 .none)) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x103b63 (movR64M64Effect 0x103b63 12 (.base 3 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 3] []) (.reg (.gpr 12))) #v[3]
    (.letOp (n := 56) (.exec 0x103b63 (LoadPre 0x103b63 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x103b63 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x103b63 12 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 57) (.out 0x103b67 (movR64R64Effect 0x103b67 13 15) (EffectPart.reads (.reg (.gpr 13)) [.gpr 15] []) (.reg (.gpr 13))) #v[53]
    (.letOp (n := 58) (.exec 0x103b67 (fun s => s.RIP = 0x103b67) (movR64R64Effect 0x103b67 13 15) (Reg.operands [.gpr 15] [])) #v[53]
    (.letOp (n := 59) (.out 0x103b6a (notR64Effect 0x103b6a 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[57]
    (.letOp (n := 60) (.exec 0x103b6a (fun s => s.RIP = 0x103b6a) (notR64Effect 0x103b6a 13) (Reg.operands [.gpr 13] [])) #v[57]
    (.letOp (n := 61) (.out 0x103b6d (shrR64Effect 0x103b6d 4 13 7) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[59]
    (.letOp (n := 62) (.exec 0x103b6d (fun s => s.RIP = 0x103b6d) (shrR64Effect 0x103b6d 4 13 7) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[59]
    (.letOp (n := 63) (.out 0x103b71 (shrR64Effect 0x103b71 4 15 6) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[53]
    (.letOp (n := 64) (.exec 0x103b71 (fun s => s.RIP = 0x103b71) (shrR64Effect 0x103b71 4 15 6) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 65) (.out 0x103b75 (orR64R64Effect 0x103b75 15 13) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 13] []) (.reg (.gpr 15))) #v[63, 61]
    (.letOp (n := 66) (.exec 0x103b75 (fun s => s.RIP = 0x103b75) (orR64R64Effect 0x103b75 15 13) (Reg.operands [.gpr 15, .gpr 13] [])) #v[63, 61]
    (.letOp (n := 67) (.out 0x103b78 (andR64R64Effect 0x103b78 15 8) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 8] []) (.reg (.gpr 15))) #v[65, 8]
    (.letOp (n := 68) (.exec 0x103b78 (fun s => s.RIP = 0x103b78) (andR64R64Effect 0x103b78 15 8) (Reg.operands [.gpr 15, .gpr 8] [])) #v[65, 8]
    (.letOp (n := 69) (.out 0x103b7b (addR64R64Effect 0x103b7b 15 14) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 14] []) (.reg (.gpr 15))) #v[67, 14]
    (.letOp (n := 70) (.exec 0x103b7b (fun s => s.RIP = 0x103b7b) (addR64R64Effect 0x103b7b 15 14) (Reg.operands [.gpr 15, .gpr 14] [])) #v[67, 14]
    (.letOp (n := 71) (.out 0x103b7e (movR64R64Effect 0x103b7e 14 12) (EffectPart.reads (.reg (.gpr 14)) [.gpr 12] []) (.reg (.gpr 14))) #v[55]
    (.letOp (n := 72) (.exec 0x103b7e (fun s => s.RIP = 0x103b7e) (movR64R64Effect 0x103b7e 14 12) (Reg.operands [.gpr 12] [])) #v[55]
    (.letOp (n := 73) (.out 0x103b81 (notR64Effect 0x103b81 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14] []) (.reg (.gpr 14))) #v[71]
    (.letOp (n := 74) (.exec 0x103b81 (fun s => s.RIP = 0x103b81) (notR64Effect 0x103b81 14) (Reg.operands [.gpr 14] [])) #v[71]
    (.letOp (n := 75) (.out 0x103b84 (shrR64Effect 0x103b84 4 14 7) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[73]
    (.letOp (n := 76) (.exec 0x103b84 (fun s => s.RIP = 0x103b84) (shrR64Effect 0x103b84 4 14 7) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[73]
    (.letOp (n := 77) (.out 0x103b88 (shrR64Effect 0x103b88 4 12 6) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[55]
    (.letOp (n := 78) (.exec 0x103b88 (fun s => s.RIP = 0x103b88) (shrR64Effect 0x103b88 4 12 6) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[55]
    (.letOp (n := 79) (.out 0x103b8c (orR64R64Effect 0x103b8c 12 14) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 14] []) (.reg (.gpr 12))) #v[77, 75]
    (.letOp (n := 80) (.exec 0x103b8c (fun s => s.RIP = 0x103b8c) (orR64R64Effect 0x103b8c 12 14) (Reg.operands [.gpr 12, .gpr 14] [])) #v[77, 75]
    (.letOp (n := 81) (.out 0x103b8f (andR64R64Effect 0x103b8f 12 8) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 8] []) (.reg (.gpr 12))) #v[79, 8]
    (.letOp (n := 82) (.exec 0x103b8f (fun s => s.RIP = 0x103b8f) (andR64R64Effect 0x103b8f 12 8) (Reg.operands [.gpr 12, .gpr 8] [])) #v[79, 8]
    (.letOp (n := 83) (.out 0x103b92 (movR64M64Effect 0x103b92 13 (.base 3 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 3] []) (.reg (.gpr 13))) #v[3]
    (.letOp (n := 84) (.exec 0x103b92 (LoadPre 0x103b92 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x103b92 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x103b92 13 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 85) (.out 0x103b96 (movR64R64Effect 0x103b96 14 13) (EffectPart.reads (.reg (.gpr 14)) [.gpr 13] []) (.reg (.gpr 14))) #v[83]
    (.letOp (n := 86) (.exec 0x103b96 (fun s => s.RIP = 0x103b96) (movR64R64Effect 0x103b96 14 13) (Reg.operands [.gpr 13] [])) #v[83]
    (.letOp (n := 87) (.out 0x103b99 (notR64Effect 0x103b99 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14] []) (.reg (.gpr 14))) #v[85]
    (.letOp (n := 88) (.exec 0x103b99 (fun s => s.RIP = 0x103b99) (notR64Effect 0x103b99 14) (Reg.operands [.gpr 14] [])) #v[85]
    (.letOp (n := 89) (.out 0x103b9c (shrR64Effect 0x103b9c 4 14 7) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[87]
    (.letOp (n := 90) (.exec 0x103b9c (fun s => s.RIP = 0x103b9c) (shrR64Effect 0x103b9c 4 14 7) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[87]
    (.letOp (n := 91) (.out 0x103ba0 (shrR64Effect 0x103ba0 4 13 6) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[83]
    (.letOp (n := 92) (.exec 0x103ba0 (fun s => s.RIP = 0x103ba0) (shrR64Effect 0x103ba0 4 13 6) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[83]
    (b_l103b60_1))))))))))))))))))))))))))))))))))))))))

def bytes_l103b60 : List UInt8 :=
  [0x4C, 0x8B, 0x3B, 0x4C, 0x8B, 0x63, 0x08, 0x4D, 0x89, 0xFD, 0x49, 0xF7, 0xD5, 0x49, 0xC1, 0xED,
    0x07, 0x49, 0xC1, 0xEF, 0x06, 0x4D, 0x09, 0xEF, 0x4D, 0x21, 0xC7, 0x4D, 0x01, 0xF7, 0x4D, 0x89,
    0xE6, 0x49, 0xF7, 0xD6, 0x49, 0xC1, 0xEE, 0x07, 0x49, 0xC1, 0xEC, 0x06, 0x4D, 0x09, 0xF4, 0x4D,
    0x21, 0xC4, 0x4C, 0x8B, 0x6B, 0x10, 0x4D, 0x89, 0xEE, 0x49, 0xF7, 0xD6, 0x49, 0xC1, 0xEE, 0x07,
    0x49, 0xC1, 0xED, 0x06] ++ bytes_l103b60_1

theorem code_l103b60 : ∀ x ∈ codeRange 0x103b60 bytes_l103b60, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x3b60 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l103b60_1

@[cfg_block] def b_l103bd4 : Block Op Label signature Reg.count 53 :=
  .terminate (.br ⟨.l103af3, RegMap.args (entryMap (live .l103bd4)) 53⟩)

def bytes_l103bd4 : List UInt8 :=
  [0xE9, 0x1A, 0xFF, 0xFF, 0xFF]

theorem code_l103bd4 : ∀ x ∈ codeRange 0x103bd4 bytes_l103bd4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3bd4 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103bd9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103bd9 (andR32Imm32Effect 0x103bd9 7 10 0xfc) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[10]
    (.letOp (n := 54) (.exec 0x103bd9 (fun s => s.RIP = 0x103bd9) (andR32Imm32Effect 0x103bd9 7 10 0xfc) (Reg.operands [.gpr 10] [])) #v[10]
    (.letOp (n := 55) (.out 0x103be0 (movR32R32Effect 0x103be0 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 10] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 56) (.exec 0x103be0 (fun s => s.RIP = 0x103be0) (movR32R32Effect 0x103be0 3 1 10) (Reg.operands [.gpr 10] [])) #v[53]
    (.letOp (n := 57) (.out 0x103be3 (movR64M64Effect 0x103be3 1 (.sib 9 (some 1) 3 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 9, .gpr 1] []) (.reg (.gpr 1))) #v[9, 55]
    (.letOp (n := 58) (.exec 0x103be3 (LoadPre 0x103be3 (fun s => AddrMode.addr (.sib 9 (some 1) 3 .none) s (0x103be3 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x103be3 1 (.sib 9 (some 1) 3 .none)) (Reg.operands [.gpr 9, .gpr 1] [])) #v[9, 55]
    (.letOp (n := 59) (.out 0x103be7 (movR64R64Effect 0x103be7 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 1] []) (.reg (.gpr 7))) #v[57]
    (.letOp (n := 60) (.exec 0x103be7 (fun s => s.RIP = 0x103be7) (movR64R64Effect 0x103be7 7 1) (Reg.operands [.gpr 1] [])) #v[57]
    (.letOp (n := 61) (.out 0x103bea (notR64Effect 0x103bea 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[59]
    (.letOp (n := 62) (.exec 0x103bea (fun s => s.RIP = 0x103bea) (notR64Effect 0x103bea 7) (Reg.operands [.gpr 7] [])) #v[59]
    (.letOp (n := 63) (.out 0x103bed (shrR64Effect 0x103bed 4 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[61]
    (.letOp (n := 64) (.exec 0x103bed (fun s => s.RIP = 0x103bed) (shrR64Effect 0x103bed 4 7 7) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[61]
    (.letOp (n := 65) (.out 0x103bf1 (shrR64Effect 0x103bf1 4 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[57]
    (.letOp (n := 66) (.exec 0x103bf1 (fun s => s.RIP = 0x103bf1) (shrR64Effect 0x103bf1 4 1 6) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[57]
    (.letOp (n := 67) (.out 0x103bf5 (orR64R64Effect 0x103bf5 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[65, 63]
    (.letOp (n := 68) (.exec 0x103bf5 (fun s => s.RIP = 0x103bf5) (orR64R64Effect 0x103bf5 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[65, 63]
    (.letOp (n := 69) (.out 0x103bf8 (andR64R64Effect 0x103bf8 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8] []) (.reg (.gpr 1))) #v[67, 8]
    (.letOp (n := 70) (.exec 0x103bf8 (fun s => s.RIP = 0x103bf8) (andR64R64Effect 0x103bf8 1 8) (Reg.operands [.gpr 1, .gpr 8] [])) #v[67, 8]
    (.letOp (n := 71) (.out 0x103bfb (cmpR32Imm8Effect 0x103bfb 4 11 0x1) (EffectPart.reads (.flag .ZF) [.gpr 11] []) (.flag .ZF)) #v[11]
    (.letOp (n := 72) (.exec 0x103bfb (fun s => s.RIP = 0x103bfb) (cmpR32Imm8Effect 0x103bfb 4 11 0x1) (Reg.operands [.gpr 11] [])) #v[11]
    (.letOp (n := 73) (.pure (condOp 4)) #v[71]
    (.terminate (.condBr (Fin.last 73) ⟨.l103c3f, RegMap.args [(0, 0), (1, 69), (2, 2), (4, 4), (5, 5), (6, 6), (7, 63), (8, 8), (9, 9), (10, 53), (11, 11), (19, 71), (22, 22), (39, 39), (50, 50), (51, 51)] 74⟩ ⟨.l103c01, RegMap.args [(0, 0), (1, 69), (2, 2), (4, 4), (5, 5), (6, 6), (7, 63), (8, 8), (9, 9), (10, 53), (11, 11), (19, 71), (22, 22), (39, 39), (50, 50), (51, 51)] 74⟩))))))))))))))))))))))

def bytes_l103bd9 : List UInt8 :=
  [0x41, 0x81, 0xE2, 0xFC, 0x00, 0x00, 0x00, 0x44, 0x89, 0xD1, 0x49, 0x8B, 0x0C, 0xC9, 0x48, 0x89,
    0xCF, 0x48, 0xF7, 0xD7, 0x48, 0xC1, 0xEF, 0x07, 0x48, 0xC1, 0xE9, 0x06, 0x48, 0x09, 0xF9, 0x4C,
    0x21, 0xC1, 0x41, 0x83, 0xFB, 0x01, 0x74, 0x3E]

theorem code_l103bd9 : ∀ x ∈ codeRange 0x103bd9 bytes_l103bd9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3bd9 40 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103c01 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103c01 (movR64M64Effect 0x103c01 7 (.sib 9 (some 10) 3 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 9, .gpr 10] []) (.reg (.gpr 7))) #v[9, 10]
    (.letOp (n := 54) (.exec 0x103c01 (LoadPre 0x103c01 (fun s => AddrMode.addr (.sib 9 (some 10) 3 (.d8 0x8)) s (0x103c01 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103c01 7 (.sib 9 (some 10) 3 (.d8 0x8))) (Reg.operands [.gpr 9, .gpr 10] [])) #v[9, 10]
    (.letOp (n := 55) (.out 0x103c06 (movR64R64Effect 0x103c06 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[53]
    (.letOp (n := 56) (.exec 0x103c06 (fun s => s.RIP = 0x103c06) (movR64R64Effect 0x103c06 3 7) (Reg.operands [.gpr 7] [])) #v[53]
    (.letOp (n := 57) (.out 0x103c09 (notR64Effect 0x103c09 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[55]
    (.letOp (n := 58) (.exec 0x103c09 (fun s => s.RIP = 0x103c09) (notR64Effect 0x103c09 3) (Reg.operands [.gpr 3] [])) #v[55]
    (.letOp (n := 59) (.out 0x103c0c (shrR64Effect 0x103c0c 4 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[57]
    (.letOp (n := 60) (.exec 0x103c0c (fun s => s.RIP = 0x103c0c) (shrR64Effect 0x103c0c 4 3 7) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[57]
    (.letOp (n := 61) (.out 0x103c10 (shrR64Effect 0x103c10 4 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 62) (.exec 0x103c10 (fun s => s.RIP = 0x103c10) (shrR64Effect 0x103c10 4 7 6) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 63) (.out 0x103c14 (orR64R64Effect 0x103c14 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 3] []) (.reg (.gpr 7))) #v[61, 59]
    (.letOp (n := 64) (.exec 0x103c14 (fun s => s.RIP = 0x103c14) (orR64R64Effect 0x103c14 7 3) (Reg.operands [.gpr 7, .gpr 3] [])) #v[61, 59]
    (.letOp (n := 65) (.out 0x103c17 (andR64R64Effect 0x103c17 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 8] []) (.reg (.gpr 7))) #v[63, 8]
    (.letOp (n := 66) (.exec 0x103c17 (fun s => s.RIP = 0x103c17) (andR64R64Effect 0x103c17 7 8) (Reg.operands [.gpr 7, .gpr 8] [])) #v[63, 8]
    (.letOp (n := 67) (.out 0x103c1a (addR64R64Effect 0x103c1a 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[1, 65]
    (.letOp (n := 68) (.exec 0x103c1a (fun s => s.RIP = 0x103c1a) (addR64R64Effect 0x103c1a 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[1, 65]
    (.letOp (n := 69) (.out 0x103c1d (cmpR32Imm8Effect 0x103c1d 4 11 0x2) (EffectPart.reads (.flag .ZF) [.gpr 11] []) (.flag .ZF)) #v[11]
    (.letOp (n := 70) (.exec 0x103c1d (fun s => s.RIP = 0x103c1d) (cmpR32Imm8Effect 0x103c1d 4 11 0x2) (Reg.operands [.gpr 11] [])) #v[11]
    (.letOp (n := 71) (.pure (condOp 4)) #v[69]
    (.terminate (.condBr (Fin.last 71) ⟨.l103c3f, RegMap.args [(0, 0), (1, 67), (2, 2), (3, 59), (4, 4), (5, 5), (6, 6), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (19, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩ ⟨.l103c23, RegMap.args [(0, 0), (1, 67), (2, 2), (3, 59), (4, 4), (5, 5), (6, 6), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (19, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩))))))))))))))))))))

def bytes_l103c01 : List UInt8 :=
  [0x4B, 0x8B, 0x7C, 0xD1, 0x08, 0x48, 0x89, 0xFB, 0x48, 0xF7, 0xD3, 0x48, 0xC1, 0xEB, 0x07, 0x48,
    0xC1, 0xEF, 0x06, 0x48, 0x09, 0xDF, 0x4C, 0x21, 0xC7, 0x48, 0x01, 0xF9, 0x41, 0x83, 0xFB, 0x02,
    0x74, 0x1C]

theorem code_l103c01 : ∀ x ∈ codeRange 0x103c01 bytes_l103c01, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3c01 34 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103c23 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103c23 (movR64M64Effect 0x103c23 7 (.sib 9 (some 10) 3 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 9, .gpr 10] []) (.reg (.gpr 7))) #v[9, 10]
    (.letOp (n := 54) (.exec 0x103c23 (LoadPre 0x103c23 (fun s => AddrMode.addr (.sib 9 (some 10) 3 (.d8 0x10)) s (0x103c23 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103c23 7 (.sib 9 (some 10) 3 (.d8 0x10))) (Reg.operands [.gpr 9, .gpr 10] [])) #v[9, 10]
    (.letOp (n := 55) (.out 0x103c28 (movR64R64Effect 0x103c28 9 7) (EffectPart.reads (.reg (.gpr 9)) [.gpr 7] []) (.reg (.gpr 9))) #v[53]
    (.letOp (n := 56) (.exec 0x103c28 (fun s => s.RIP = 0x103c28) (movR64R64Effect 0x103c28 9 7) (Reg.operands [.gpr 7] [])) #v[53]
    (.letOp (n := 57) (.out 0x103c2b (notR64Effect 0x103c2b 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[55]
    (.letOp (n := 58) (.exec 0x103c2b (fun s => s.RIP = 0x103c2b) (notR64Effect 0x103c2b 9) (Reg.operands [.gpr 9] [])) #v[55]
    (.letOp (n := 59) (.out 0x103c2e (shrR64Effect 0x103c2e 4 9 7) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[57]
    (.letOp (n := 60) (.exec 0x103c2e (fun s => s.RIP = 0x103c2e) (shrR64Effect 0x103c2e 4 9 7) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[57]
    (.letOp (n := 61) (.out 0x103c32 (shrR64Effect 0x103c32 4 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 62) (.exec 0x103c32 (fun s => s.RIP = 0x103c32) (shrR64Effect 0x103c32 4 7 6) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 63) (.out 0x103c36 (orR64R64Effect 0x103c36 7 9) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 9] []) (.reg (.gpr 7))) #v[61, 59]
    (.letOp (n := 64) (.exec 0x103c36 (fun s => s.RIP = 0x103c36) (orR64R64Effect 0x103c36 7 9) (Reg.operands [.gpr 7, .gpr 9] [])) #v[61, 59]
    (.letOp (n := 65) (.out 0x103c39 (andR64R64Effect 0x103c39 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 8] []) (.reg (.gpr 7))) #v[63, 8]
    (.letOp (n := 66) (.exec 0x103c39 (fun s => s.RIP = 0x103c39) (andR64R64Effect 0x103c39 7 8) (Reg.operands [.gpr 7, .gpr 8] [])) #v[63, 8]
    (.letOp (n := 67) (.out 0x103c3c (addR64R64Effect 0x103c3c 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[1, 65]
    (.letOp (n := 68) (.exec 0x103c3c (fun s => s.RIP = 0x103c3c) (addR64R64Effect 0x103c3c 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[1, 65]
    (.terminate (.br ⟨.l103c3f, RegMap.args [(0, 0), (1, 67), (2, 2), (4, 4), (5, 5), (6, 6), (7, 65), (8, 8), (9, 59), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 69⟩)))))))))))))))))

def bytes_l103c23 : List UInt8 :=
  [0x4B, 0x8B, 0x7C, 0xD1, 0x10, 0x49, 0x89, 0xF9, 0x49, 0xF7, 0xD1, 0x49, 0xC1, 0xE9, 0x07, 0x48,
    0xC1, 0xEF, 0x06, 0x4C, 0x09, 0xCF, 0x4C, 0x21, 0xC7, 0x48, 0x01, 0xF9]

theorem code_l103c23 : ∀ x ∈ codeRange 0x103c23 bytes_l103c23, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3c23 28 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103c3f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103c3f (movR64R64Effect 0x103c3f 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 1] []) (.reg (.gpr 7))) #v[1]
    (.letOp (n := 54) (.exec 0x103c3f (fun s => s.RIP = 0x103c3f) (movR64R64Effect 0x103c3f 7 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 55) (.out 0x103c42 (andR64R64Effect 0x103c42 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[53, 6]
    (.letOp (n := 56) (.exec 0x103c42 (fun s => s.RIP = 0x103c42) (andR64R64Effect 0x103c42 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[53, 6]
    (.letOp (n := 57) (.out 0x103c45 (shrR64Effect 0x103c45 4 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1]
    (.letOp (n := 58) (.exec 0x103c45 (fun s => s.RIP = 0x103c45) (shrR64Effect 0x103c45 4 1 8) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1]
    (.letOp (n := 59) (.out 0x103c49 (andR64R64Effect 0x103c49 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[57, 6]
    (.letOp (n := 60) (.exec 0x103c49 (fun s => s.RIP = 0x103c49) (andR64R64Effect 0x103c49 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[57, 6]
    (.letOp (n := 61) (.out 0x103c4c (addR64R64Effect 0x103c4c 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[59, 55]
    (.letOp (n := 62) (.exec 0x103c4c (fun s => s.RIP = 0x103c4c) (addR64R64Effect 0x103c4c 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[59, 55]
    (.letOp (n := 63) (.out 0x103c4f (imulR64R64Effect 0x103c4f 4 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[61, 2]
    (.letOp (n := 64) (.exec 0x103c4f (fun s => s.RIP = 0x103c4f) (imulR64R64Effect 0x103c4f 4 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[61, 2]
    (.letOp (n := 65) (.out 0x103c53 (shrR64Effect 0x103c53 4 1 48) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[63]
    (.letOp (n := 66) (.exec 0x103c53 (fun s => s.RIP = 0x103c53) (shrR64Effect 0x103c53 4 1 48) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[63]
    (.letOp (n := 67) (.out 0x103c57 (addR64R64Effect 0x103c57 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[0, 65]
    (.letOp (n := 68) (.exec 0x103c57 (fun s => s.RIP = 0x103c57) (addR64R64Effect 0x103c57 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[0, 65]
    (.terminate (.br ⟨.l103c5a, RegMap.args [(0, 67), (1, 65), (2, 2), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 69⟩)))))))))))))))))

def bytes_l103c3f : List UInt8 :=
  [0x48, 0x89, 0xCF, 0x48, 0x21, 0xF7, 0x48, 0xC1, 0xE9, 0x08, 0x48, 0x21, 0xF1, 0x48, 0x01, 0xF9,
    0x48, 0x0F, 0xAF, 0xCA, 0x48, 0xC1, 0xE9, 0x30, 0x48, 0x01, 0xC8]

theorem code_l103c3f : ∀ x ∈ codeRange 0x103c3f bytes_l103c3f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3c3f 27 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103c5a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103c5a (popR64Effect 0x103c5a 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 54) (.out 0x103c5a (popR64Effect 0x103c5a 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 55) (.exec 0x103c5a (PopPre 0x103c5a) (popR64Effect 0x103c5a 1 3) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x103c5b (popR64Effect 0x103c5b 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[54]
    (.letOp (n := 57) (.out 0x103c5b (popR64Effect 0x103c5b 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[54]
    (.letOp (n := 58) (.exec 0x103c5b (PopPre 0x103c5b) (popR64Effect 0x103c5b 2 12) (Reg.operands [.gpr 4] [])) #v[54]
    (.letOp (n := 59) (.out 0x103c5d (popR64Effect 0x103c5d 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[57]
    (.letOp (n := 60) (.out 0x103c5d (popR64Effect 0x103c5d 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[57]
    (.letOp (n := 61) (.exec 0x103c5d (PopPre 0x103c5d) (popR64Effect 0x103c5d 2 13) (Reg.operands [.gpr 4] [])) #v[57]
    (.letOp (n := 62) (.out 0x103c5f (popR64Effect 0x103c5f 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[60]
    (.letOp (n := 63) (.out 0x103c5f (popR64Effect 0x103c5f 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[60]
    (.letOp (n := 64) (.exec 0x103c5f (PopPre 0x103c5f) (popR64Effect 0x103c5f 2 14) (Reg.operands [.gpr 4] [])) #v[60]
    (.letOp (n := 65) (.out 0x103c61 (popR64Effect 0x103c61 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[63]
    (.letOp (n := 66) (.out 0x103c61 (popR64Effect 0x103c61 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 67) (.exec 0x103c61 (PopPre 0x103c61) (popR64Effect 0x103c61 2 15) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 68) (.out 0x103c63 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[66]
    (.letOp (n := 69) (.out 0x103c63 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[66]
    (.letOp (n := 70) (.exec 0x103c63 (RetPre 0x103c63) (retEffect) (Reg.operands [.gpr 4] [])) #v[66]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 2), (3, 53), (4, 69), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 56), (13, 59), (14, 62), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)] 71) (some ⟨68, by decide⟩))))))))))))))))))))

def bytes_l103c5a : List UInt8 :=
  [0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F, 0xC3]

theorem code_l103c5a : ∀ x ∈ codeRange 0x103c5a bytes_l103c5a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3c5a 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103c70 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103c70 (pushR64Effect 0x103c70 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x103c70 (PushPre 0x103c70 1) (pushR64Effect 0x103c70 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x103c71 (movR64R64Effect 0x103c71 5 4) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[53]
    (.letOp (n := 56) (.exec 0x103c71 (fun s => s.RIP = 0x103c71) (movR64R64Effect 0x103c71 5 4) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 57) (.out 0x103c74 (subR64Imm8Effect 0x103c74 4 0x30) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[53]
    (.letOp (n := 58) (.exec 0x103c74 (fun s => s.RIP = 0x103c74) (subR64Imm8Effect 0x103c74 4 0x30) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 59) (.out 0x103c78 (cmpR64R64Effect 0x103c78 7 2) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 2] []) (.flag .CF)) #v[7, 2]
    (.letOp (n := 60) (.out 0x103c78 (cmpR64R64Effect 0x103c78 7 2) (EffectPart.reads (.flag .ZF) [.gpr 7, .gpr 2] []) (.flag .ZF)) #v[7, 2]
    (.letOp (n := 61) (.exec 0x103c78 (fun s => s.RIP = 0x103c78) (cmpR64R64Effect 0x103c78 7 2) (Reg.operands [.gpr 7, .gpr 2] [])) #v[7, 2]
    (.letOp (n := 62) (.pure (condOp 6)) #v[59, 60]
    (.terminate (.condBr (Fin.last 62) ⟨.l103cb8, RegMap.args [(1, 1), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7), (16, 59), (19, 60)] 63⟩ ⟨.l103c7d, RegMap.args [(1, 1), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7), (16, 59), (19, 60)] 63⟩)))))))))))

def bytes_l103c70 : List UInt8 :=
  [0x55, 0x48, 0x89, 0xE5, 0x48, 0x83, 0xEC, 0x30, 0x48, 0x39, 0xD7, 0x76, 0x3B]

theorem code_l103c70 : ∀ x ∈ codeRange 0x103c70 bytes_l103c70, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3c70 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103c7d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x103c7d (StorePre 0x103c7d 4 (fun s => AddrMode.addr (.base 5 (.d8 0xf8)) s (0x103c7d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103c7d 7 (.base 5 (.d8 0xf8))) (Reg.operands [.gpr 7, .gpr 5] [])) #v[7, 5]
    (.letOp (n := 54) (.exec 0x103c81 (StorePre 0x103c81 4 (fun s => AddrMode.addr (.base 5 (.d8 0xf0)) s (0x103c81 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103c81 2 (.base 5 (.d8 0xf0))) (Reg.operands [.gpr 2, .gpr 5] [])) #v[2, 5]
    (.letOp (n := 55) (.out 0x103c85 (leaR64Effect 0x103c85 0 (.base 5 (.d8 0xf8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[5]
    (.letOp (n := 56) (.exec 0x103c85 (fun s => s.RIP = 0x103c85) (leaR64Effect 0x103c85 0 (.base 5 (.d8 0xf8))) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 57) (.exec 0x103c89 (StorePre 0x103c89 4 (fun s => AddrMode.addr (.base 5 (.d8 0xd0)) s (0x103c89 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103c89 0 (.base 5 (.d8 0xd0))) (Reg.operands [.gpr 0, .gpr 5] [])) #v[55, 5]
    (.letOp (n := 58) (.out 0x103c8d (leaR64Effect 0x103c8d 0 (.rip 0x10c)) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 59) (.exec 0x103c8d (fun s => s.RIP = 0x103c8d) (leaR64Effect 0x103c8d 0 (.rip 0x10c)) (Reg.operands [] [])) #v[]
    (.letOp (n := 60) (.exec 0x103c94 (StorePre 0x103c94 4 (fun s => AddrMode.addr (.base 5 (.d8 0xd8)) s (0x103c94 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103c94 0 (.base 5 (.d8 0xd8))) (Reg.operands [.gpr 0, .gpr 5] [])) #v[58, 5]
    (.letOp (n := 61) (.out 0x103c98 (leaR64Effect 0x103c98 2 (.base 5 (.d8 0xf0))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5] []) (.reg (.gpr 2))) #v[5]
    (.letOp (n := 62) (.exec 0x103c98 (fun s => s.RIP = 0x103c98) (leaR64Effect 0x103c98 2 (.base 5 (.d8 0xf0))) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 63) (.exec 0x103c9c (StorePre 0x103c9c 4 (fun s => AddrMode.addr (.base 5 (.d8 0xe0)) s (0x103c9c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103c9c 2 (.base 5 (.d8 0xe0))) (Reg.operands [.gpr 2, .gpr 5] [])) #v[61, 5]
    (.letOp (n := 64) (.exec 0x103ca0 (StorePre 0x103ca0 4 (fun s => AddrMode.addr (.base 5 (.d8 0xe8)) s (0x103ca0 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103ca0 0 (.base 5 (.d8 0xe8))) (Reg.operands [.gpr 0, .gpr 5] [])) #v[58, 5]
    (.letOp (n := 65) (.out 0x103ca4 (leaR64Effect 0x103ca4 7 (.rip 0xfcc49)) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 66) (.exec 0x103ca4 (fun s => s.RIP = 0x103ca4) (leaR64Effect 0x103ca4 7 (.rip 0xfcc49)) (Reg.operands [] [])) #v[]
    (.letOp (n := 67) (.out 0x103cab (leaR64Effect 0x103cab 6 (.base 5 (.d8 0xd0))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[5]
    (.letOp (n := 68) (.exec 0x103cab (fun s => s.RIP = 0x103cab) (leaR64Effect 0x103cab 6 (.base 5 (.d8 0xd0))) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 69) (.out 0x103caf (movR64R64Effect 0x103caf 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[1]
    (.letOp (n := 70) (.exec 0x103caf (fun s => s.RIP = 0x103caf) (movR64R64Effect 0x103caf 2 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 71) (.out 0x103cb2 (callEffect (callMemPtr 0x103cb2 (.rip 0xfd558)) (0x103cb2 + BitVec.ofNat 64 (callMemLen (.rip 0xfd558)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 72) (.exec 0x103cb2 (GoesTo (CallMemPre 0x103cb2 (.rip 0xfd558)) (callEffect (callMemPtr 0x103cb2 (.rip 0xfd558)) (0x103cb2 + BitVec.ofNat 64 (callMemLen (.rip 0xfd558)))) 0x103880) (callEffect (callMemPtr 0x103cb2 (.rip 0xfd558)) (0x103cb2 + BitVec.ofNat 64 (callMemLen (.rip 0xfd558)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.const ⟨64, 0x103cb8⟩) #v[]
    (.terminate (.call ⟨.l103880, RegMap.args [(0, 58), (1, 1), (2, 69), (4, 71), (5, 5), (6, 67), (7, 65)] 74⟩ { target := .l103cb8, kept := #v[], arity := rfl, guard := some (Fin.last 73) }))))))))))))))))))))))

def bytes_l103c7d : List UInt8 :=
  [0x48, 0x89, 0x7D, 0xF8, 0x48, 0x89, 0x55, 0xF0, 0x48, 0x8D, 0x45, 0xF8, 0x48, 0x89, 0x45, 0xD0,
    0x48, 0x8D, 0x05, 0x0C, 0x01, 0x00, 0x00, 0x48, 0x89, 0x45, 0xD8, 0x48, 0x8D, 0x55, 0xF0, 0x48,
    0x89, 0x55, 0xE0, 0x48, 0x89, 0x45, 0xE8, 0x48, 0x8D, 0x3D, 0x49, 0xCC, 0x0F, 0x00, 0x48, 0x8D,
    0x75, 0xD0, 0x48, 0x89, 0xCA, 0xFF, 0x15, 0x58, 0xD5, 0x0F, 0x00]

theorem code_l103c7d : ∀ x ∈ codeRange 0x103c7d bytes_l103c7d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3c7d 59 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103cb8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103cb8 (cmpR64R64Effect 0x103cb8 6 2) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 2] []) (.flag .CF)) #v[6, 2]
    (.letOp (n := 54) (.out 0x103cb8 (cmpR64R64Effect 0x103cb8 6 2) (EffectPart.reads (.flag .ZF) [.gpr 6, .gpr 2] []) (.flag .ZF)) #v[6, 2]
    (.letOp (n := 55) (.exec 0x103cb8 (fun s => s.RIP = 0x103cb8) (cmpR64R64Effect 0x103cb8 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[6, 2]
    (.letOp (n := 56) (.pure (condOp 7)) #v[53, 54]
    (.terminate (.condBr (Fin.last 56) ⟨.l103cfd, RegMap.args [(1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (16, 53), (19, 54)] 57⟩ ⟨.l103cbd, RegMap.args [(1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (16, 53), (19, 54)] 57⟩)))))

def bytes_l103cb8 : List UInt8 :=
  [0x48, 0x39, 0xD6, 0x77, 0x40]

theorem code_l103cb8 : ∀ x ∈ codeRange 0x103cb8 bytes_l103cb8, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3cb8 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103cbd : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103cbd (cmpR64R64Effect 0x103cbd 7 6) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 6] []) (.flag .CF)) #v[7, 6]
    (.letOp (n := 54) (.out 0x103cbd (cmpR64R64Effect 0x103cbd 7 6) (EffectPart.reads (.flag .ZF) [.gpr 7, .gpr 6] []) (.flag .ZF)) #v[7, 6]
    (.letOp (n := 55) (.exec 0x103cbd (fun s => s.RIP = 0x103cbd) (cmpR64R64Effect 0x103cbd 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[7, 6]
    (.letOp (n := 56) (.pure (condOp 6)) #v[53, 54]
    (.terminate (.condBr (Fin.last 56) ⟨.l103cfd, RegMap.args [(1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (16, 53), (19, 54)] 57⟩ ⟨.l103cc2, RegMap.args [(1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (16, 53), (19, 54)] 57⟩)))))

def bytes_l103cbd : List UInt8 :=
  [0x48, 0x39, 0xF7, 0x76, 0x3B]

theorem code_l103cbd : ∀ x ∈ codeRange 0x103cbd bytes_l103cbd, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3cbd 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103cc2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x103cc2 (StorePre 0x103cc2 4 (fun s => AddrMode.addr (.base 5 (.d8 0xf8)) s (0x103cc2 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103cc2 7 (.base 5 (.d8 0xf8))) (Reg.operands [.gpr 7, .gpr 5] [])) #v[7, 5]
    (.letOp (n := 54) (.exec 0x103cc6 (StorePre 0x103cc6 4 (fun s => AddrMode.addr (.base 5 (.d8 0xf0)) s (0x103cc6 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103cc6 6 (.base 5 (.d8 0xf0))) (Reg.operands [.gpr 6, .gpr 5] [])) #v[6, 5]
    (.letOp (n := 55) (.out 0x103cca (leaR64Effect 0x103cca 0 (.base 5 (.d8 0xf8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[5]
    (.letOp (n := 56) (.exec 0x103cca (fun s => s.RIP = 0x103cca) (leaR64Effect 0x103cca 0 (.base 5 (.d8 0xf8))) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 57) (.exec 0x103cce (StorePre 0x103cce 4 (fun s => AddrMode.addr (.base 5 (.d8 0xd0)) s (0x103cce + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103cce 0 (.base 5 (.d8 0xd0))) (Reg.operands [.gpr 0, .gpr 5] [])) #v[55, 5]
    (.letOp (n := 58) (.out 0x103cd2 (leaR64Effect 0x103cd2 0 (.rip 0xc7)) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 59) (.exec 0x103cd2 (fun s => s.RIP = 0x103cd2) (leaR64Effect 0x103cd2 0 (.rip 0xc7)) (Reg.operands [] [])) #v[]
    (.letOp (n := 60) (.exec 0x103cd9 (StorePre 0x103cd9 4 (fun s => AddrMode.addr (.base 5 (.d8 0xd8)) s (0x103cd9 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103cd9 0 (.base 5 (.d8 0xd8))) (Reg.operands [.gpr 0, .gpr 5] [])) #v[58, 5]
    (.letOp (n := 61) (.out 0x103cdd (leaR64Effect 0x103cdd 2 (.base 5 (.d8 0xf0))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5] []) (.reg (.gpr 2))) #v[5]
    (.letOp (n := 62) (.exec 0x103cdd (fun s => s.RIP = 0x103cdd) (leaR64Effect 0x103cdd 2 (.base 5 (.d8 0xf0))) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 63) (.exec 0x103ce1 (StorePre 0x103ce1 4 (fun s => AddrMode.addr (.base 5 (.d8 0xe0)) s (0x103ce1 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103ce1 2 (.base 5 (.d8 0xe0))) (Reg.operands [.gpr 2, .gpr 5] [])) #v[61, 5]
    (.letOp (n := 64) (.exec 0x103ce5 (StorePre 0x103ce5 4 (fun s => AddrMode.addr (.base 5 (.d8 0xe8)) s (0x103ce5 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103ce5 0 (.base 5 (.d8 0xe8))) (Reg.operands [.gpr 0, .gpr 5] [])) #v[58, 5]
    (.letOp (n := 65) (.out 0x103ce9 (leaR64Effect 0x103ce9 7 (.rip 0xfcbdc)) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 66) (.exec 0x103ce9 (fun s => s.RIP = 0x103ce9) (leaR64Effect 0x103ce9 7 (.rip 0xfcbdc)) (Reg.operands [] [])) #v[]
    (.letOp (n := 67) (.out 0x103cf0 (leaR64Effect 0x103cf0 6 (.base 5 (.d8 0xd0))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[5]
    (.letOp (n := 68) (.exec 0x103cf0 (fun s => s.RIP = 0x103cf0) (leaR64Effect 0x103cf0 6 (.base 5 (.d8 0xd0))) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 69) (.out 0x103cf4 (movR64R64Effect 0x103cf4 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[1]
    (.letOp (n := 70) (.exec 0x103cf4 (fun s => s.RIP = 0x103cf4) (movR64R64Effect 0x103cf4 2 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 71) (.out 0x103cf7 (callEffect (callMemPtr 0x103cf7 (.rip 0xfd513)) (0x103cf7 + BitVec.ofNat 64 (callMemLen (.rip 0xfd513)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 72) (.exec 0x103cf7 (GoesTo (CallMemPre 0x103cf7 (.rip 0xfd513)) (callEffect (callMemPtr 0x103cf7 (.rip 0xfd513)) (0x103cf7 + BitVec.ofNat 64 (callMemLen (.rip 0xfd513)))) 0x103880) (callEffect (callMemPtr 0x103cf7 (.rip 0xfd513)) (0x103cf7 + BitVec.ofNat 64 (callMemLen (.rip 0xfd513)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.const ⟨64, 0x103cfd⟩) #v[]
    (.terminate (.call ⟨.l103880, RegMap.args [(0, 58), (1, 1), (2, 69), (4, 71), (5, 5), (6, 67), (7, 65)] 74⟩ { target := .l103cfd, kept := #v[], arity := rfl, guard := some (Fin.last 73) }))))))))))))))))))))))

def bytes_l103cc2 : List UInt8 :=
  [0x48, 0x89, 0x7D, 0xF8, 0x48, 0x89, 0x75, 0xF0, 0x48, 0x8D, 0x45, 0xF8, 0x48, 0x89, 0x45, 0xD0,
    0x48, 0x8D, 0x05, 0xC7, 0x00, 0x00, 0x00, 0x48, 0x89, 0x45, 0xD8, 0x48, 0x8D, 0x55, 0xF0, 0x48,
    0x89, 0x55, 0xE0, 0x48, 0x89, 0x45, 0xE8, 0x48, 0x8D, 0x3D, 0xDC, 0xCB, 0x0F, 0x00, 0x48, 0x8D,
    0x75, 0xD0, 0x48, 0x89, 0xCA, 0xFF, 0x15, 0x13, 0xD5, 0x0F, 0x00]

theorem code_l103cc2 : ∀ x ∈ codeRange 0x103cc2 bytes_l103cc2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3cc2 59 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103cfd : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x103cfd (StorePre 0x103cfd 4 (fun s => AddrMode.addr (.base 5 (.d8 0xf8)) s (0x103cfd + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103cfd 6 (.base 5 (.d8 0xf8))) (Reg.operands [.gpr 6, .gpr 5] [])) #v[6, 5]
    (.letOp (n := 54) (.exec 0x103d01 (StorePre 0x103d01 4 (fun s => AddrMode.addr (.base 5 (.d8 0xf0)) s (0x103d01 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103d01 2 (.base 5 (.d8 0xf0))) (Reg.operands [.gpr 2, .gpr 5] [])) #v[2, 5]
    (.letOp (n := 55) (.out 0x103d05 (leaR64Effect 0x103d05 0 (.base 5 (.d8 0xf8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[5]
    (.letOp (n := 56) (.exec 0x103d05 (fun s => s.RIP = 0x103d05) (leaR64Effect 0x103d05 0 (.base 5 (.d8 0xf8))) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 57) (.exec 0x103d09 (StorePre 0x103d09 4 (fun s => AddrMode.addr (.base 5 (.d8 0xd0)) s (0x103d09 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103d09 0 (.base 5 (.d8 0xd0))) (Reg.operands [.gpr 0, .gpr 5] [])) #v[55, 5]
    (.letOp (n := 58) (.out 0x103d0d (leaR64Effect 0x103d0d 0 (.rip 0x8c)) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 59) (.exec 0x103d0d (fun s => s.RIP = 0x103d0d) (leaR64Effect 0x103d0d 0 (.rip 0x8c)) (Reg.operands [] [])) #v[]
    (.letOp (n := 60) (.exec 0x103d14 (StorePre 0x103d14 4 (fun s => AddrMode.addr (.base 5 (.d8 0xd8)) s (0x103d14 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103d14 0 (.base 5 (.d8 0xd8))) (Reg.operands [.gpr 0, .gpr 5] [])) #v[58, 5]
    (.letOp (n := 61) (.out 0x103d18 (leaR64Effect 0x103d18 2 (.base 5 (.d8 0xf0))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5] []) (.reg (.gpr 2))) #v[5]
    (.letOp (n := 62) (.exec 0x103d18 (fun s => s.RIP = 0x103d18) (leaR64Effect 0x103d18 2 (.base 5 (.d8 0xf0))) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 63) (.exec 0x103d1c (StorePre 0x103d1c 4 (fun s => AddrMode.addr (.base 5 (.d8 0xe0)) s (0x103d1c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103d1c 2 (.base 5 (.d8 0xe0))) (Reg.operands [.gpr 2, .gpr 5] [])) #v[61, 5]
    (.letOp (n := 64) (.exec 0x103d20 (StorePre 0x103d20 4 (fun s => AddrMode.addr (.base 5 (.d8 0xe8)) s (0x103d20 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103d20 0 (.base 5 (.d8 0xe8))) (Reg.operands [.gpr 0, .gpr 5] [])) #v[58, 5]
    (.letOp (n := 65) (.out 0x103d24 (leaR64Effect 0x103d24 7 (.rip 0xfcb6a)) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 66) (.exec 0x103d24 (fun s => s.RIP = 0x103d24) (leaR64Effect 0x103d24 7 (.rip 0xfcb6a)) (Reg.operands [] [])) #v[]
    (.letOp (n := 67) (.out 0x103d2b (leaR64Effect 0x103d2b 6 (.base 5 (.d8 0xd0))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[5]
    (.letOp (n := 68) (.exec 0x103d2b (fun s => s.RIP = 0x103d2b) (leaR64Effect 0x103d2b 6 (.base 5 (.d8 0xd0))) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 69) (.out 0x103d2f (movR64R64Effect 0x103d2f 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[1]
    (.letOp (n := 70) (.exec 0x103d2f (fun s => s.RIP = 0x103d2f) (movR64R64Effect 0x103d2f 2 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 71) (.out 0x103d32 (callEffect (callMemPtr 0x103d32 (.rip 0xfd4d8)) (0x103d32 + BitVec.ofNat 64 (callMemLen (.rip 0xfd4d8)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 72) (.exec 0x103d32 (GoesTo (CallMemPre 0x103d32 (.rip 0xfd4d8)) (callEffect (callMemPtr 0x103d32 (.rip 0xfd4d8)) (0x103d32 + BitVec.ofNat 64 (callMemLen (.rip 0xfd4d8)))) 0x103880) (callEffect (callMemPtr 0x103d32 (.rip 0xfd4d8)) (0x103d32 + BitVec.ofNat 64 (callMemLen (.rip 0xfd4d8)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.const ⟨64, 0x103d38⟩) #v[]
    (.terminate (.call ⟨.l103880, RegMap.args [(0, 58), (1, 1), (2, 69), (4, 71), (5, 5), (6, 67), (7, 65)] 74⟩ { target := .l103d38, kept := #v[], arity := rfl, guard := some (Fin.last 73) }))))))))))))))))))))))

def bytes_l103cfd : List UInt8 :=
  [0x48, 0x89, 0x75, 0xF8, 0x48, 0x89, 0x55, 0xF0, 0x48, 0x8D, 0x45, 0xF8, 0x48, 0x89, 0x45, 0xD0,
    0x48, 0x8D, 0x05, 0x8C, 0x00, 0x00, 0x00, 0x48, 0x89, 0x45, 0xD8, 0x48, 0x8D, 0x55, 0xF0, 0x48,
    0x89, 0x55, 0xE0, 0x48, 0x89, 0x45, 0xE8, 0x48, 0x8D, 0x3D, 0x6A, 0xCB, 0x0F, 0x00, 0x48, 0x8D,
    0x75, 0xD0, 0x48, 0x89, 0xCA, 0xFF, 0x15, 0xD8, 0xD4, 0x0F, 0x00]

theorem code_l103cfd : ∀ x ∈ codeRange 0x103cfd bytes_l103cfd, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3cfd 59 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103d38 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x103d38 (fun s => s.RIP = 0x103d38) (fun _ => nopEffect 0x103d38 8) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l103d40, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 54⟩))

def bytes_l103d38 : List UInt8 :=
  [0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem code_l103d38 : ∀ x ∈ codeRange 0x103d38 bytes_l103d38, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3d38 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103d40 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103d40 (pushR64Effect 0x103d40 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x103d40 (PushPre 0x103d40 1) (pushR64Effect 0x103d40 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.exec 0x103d41 (fun s => s.RIP = 0x103d41) (movR64R64Effect 0x103d41 5 4) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 56) (.out 0x103d44 (pushR64Effect 0x103d44 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 57) (.exec 0x103d44 (PushPre 0x103d44 2) (pushR64Effect 0x103d44 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 58) (.out 0x103d46 (pushR64Effect 0x103d46 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[56, 14]
    (.letOp (n := 59) (.exec 0x103d46 (PushPre 0x103d46 2) (pushR64Effect 0x103d46 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[56, 14]
    (.letOp (n := 60) (.out 0x103d48 (pushR64Effect 0x103d48 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[58, 12]
    (.letOp (n := 61) (.exec 0x103d48 (PushPre 0x103d48 2) (pushR64Effect 0x103d48 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[58, 12]
    (.letOp (n := 62) (.out 0x103d4a (pushR64Effect 0x103d4a 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[60, 3]
    (.letOp (n := 63) (.exec 0x103d4a (PushPre 0x103d4a 1) (pushR64Effect 0x103d4a 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[60, 3]
    (.letOp (n := 64) (.out 0x103d4b (movR64R64Effect 0x103d4b 3 8) (EffectPart.reads (.reg (.gpr 3)) [.gpr 8] []) (.reg (.gpr 3))) #v[8]
    (.letOp (n := 65) (.exec 0x103d4b (fun s => s.RIP = 0x103d4b) (movR64R64Effect 0x103d4b 3 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 66) (.out 0x103d4e (movR64R64Effect 0x103d4e 14 1) (EffectPart.reads (.reg (.gpr 14)) [.gpr 1] []) (.reg (.gpr 14))) #v[1]
    (.letOp (n := 67) (.exec 0x103d4e (fun s => s.RIP = 0x103d4e) (movR64R64Effect 0x103d4e 14 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 68) (.out 0x103d51 (movR64R64Effect 0x103d51 12 6) (EffectPart.reads (.reg (.gpr 12)) [.gpr 6] []) (.reg (.gpr 12))) #v[6]
    (.letOp (n := 69) (.exec 0x103d51 (fun s => s.RIP = 0x103d51) (movR64R64Effect 0x103d51 12 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 70) (.out 0x103d54 (movR64R64Effect 0x103d54 15 7) (EffectPart.reads (.reg (.gpr 15)) [.gpr 7] []) (.reg (.gpr 15))) #v[7]
    (.letOp (n := 71) (.exec 0x103d54 (fun s => s.RIP = 0x103d54) (movR64R64Effect 0x103d54 15 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 72) (.out 0x103d57 (cmpR32Imm8Effect 0x103d57 3 2 0xff) (EffectPart.reads (.flag .ZF) [.gpr 2] []) (.flag .ZF)) #v[2]
    (.letOp (n := 73) (.exec 0x103d57 (fun s => s.RIP = 0x103d57) (cmpR32Imm8Effect 0x103d57 3 2 0xff) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 74) (.pure (condOp 4)) #v[72]
    (.terminate (.condBr (Fin.last 74) ⟨.l103d6e, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 64), (4, 62), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 68), (13, 13), (14, 66), (15, 70), (19, 72), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ ⟨.l103d5c, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 64), (4, 62), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 68), (13, 13), (14, 66), (15, 70), (19, 72), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩)))))))))))))))))))))))

def bytes_l103d40 : List UInt8 :=
  [0x55, 0x48, 0x89, 0xE5, 0x41, 0x57, 0x41, 0x56, 0x41, 0x54, 0x53, 0x4C, 0x89, 0xC3, 0x49, 0x89,
    0xCE, 0x49, 0x89, 0xF4, 0x49, 0x89, 0xFF, 0x83, 0xFA, 0xFF, 0x74, 0x12]

theorem code_l103d40 : ∀ x ∈ codeRange 0x103d40 bytes_l103d40, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3d40 28 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103d5c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x103d5c (fun s => s.RIP = 0x103d5c) (movR64R64Effect 0x103d5c 7 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 54) (.exec 0x103d5f (fun s => s.RIP = 0x103d5f) (movR32R32Effect 0x103d5f 2 6 2) (Reg.operands [.gpr 2] [])) #v[2]
    (cutBlock 0x103d61))

def bytes_l103d5c : List UInt8 :=
  [0x4C, 0x89, 0xFF, 0x89, 0xD6, 0x41, 0xFF, 0x54, 0x24, 0x20]

theorem code_l103d5c : ∀ x ∈ codeRange 0x103d5c bytes_l103d5c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3d5c 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103d66 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103d66 (movR32R32Effect 0x103d66 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[0]
    (.letOp (n := 54) (.exec 0x103d66 (fun s => s.RIP = 0x103d66) (movR32R32Effect 0x103d66 2 1 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x103d68 (movR8Imm8Effect 0x103d68 2 0 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 56) (.exec 0x103d68 (fun s => s.RIP = 0x103d68) (movR8Imm8Effect 0x103d68 2 0 0x1) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 57) (.out 0x103d6a (testR8R8Effect 0x103d6a 2 1 1) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 1] []) (.flag .ZF)) #v[53, 53]
    (.letOp (n := 58) (.exec 0x103d6a (fun s => s.RIP = 0x103d6a) (testR8R8Effect 0x103d6a 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[53, 53]
    (.letOp (n := 59) (.pure (condOp 5)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l103d8d, RegMap.args [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l103d6e, RegMap.args [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l103d66 : List UInt8 :=
  [0x89, 0xC1, 0xB0, 0x01, 0x84, 0xC9, 0x75, 0x1F]

theorem code_l103d66 : ∀ x ∈ codeRange 0x103d66 bytes_l103d66, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3d66 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103d6e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103d6e (testR64R64Effect 0x103d6e 14 14) (EffectPart.reads (.flag .ZF) [.gpr 14, .gpr 14] []) (.flag .ZF)) #v[14, 14]
    (.letOp (n := 54) (.exec 0x103d6e (fun s => s.RIP = 0x103d6e) (testR64R64Effect 0x103d6e 14 14) (Reg.operands [.gpr 14, .gpr 14] [])) #v[14, 14]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l103d8b, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l103d73, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l103d6e : List UInt8 :=
  [0x4D, 0x85, 0xF6, 0x74, 0x18]

theorem code_l103d6e : ∀ x ∈ codeRange 0x103d6e bytes_l103d6e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3d6e 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103d73 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x103d73 (LoadPre 0x103d73 (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x18)) s (0x103d73 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103d73 0 (.sib 12 none 0 (.d8 0x18))) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 54) (.exec 0x103d78 (fun s => s.RIP = 0x103d78) (movR64R64Effect 0x103d78 7 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.exec 0x103d7b (fun s => s.RIP = 0x103d7b) (movR64R64Effect 0x103d7b 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 56) (.exec 0x103d7e (fun s => s.RIP = 0x103d7e) (movR64R64Effect 0x103d7e 2 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 57) (.out 0x103d81 (popR64Effect 0x103d81 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x103d81 (PopPre 0x103d81) (popR64Effect 0x103d81 1 3) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x103d82 (popR64Effect 0x103d82 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[57]
    (.letOp (n := 60) (.exec 0x103d82 (PopPre 0x103d82) (popR64Effect 0x103d82 2 12) (Reg.operands [.gpr 4] [])) #v[57]
    (.letOp (n := 61) (.out 0x103d84 (popR64Effect 0x103d84 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 62) (.exec 0x103d84 (PopPre 0x103d84) (popR64Effect 0x103d84 2 14) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 63) (.out 0x103d86 (popR64Effect 0x103d86 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 64) (.exec 0x103d86 (PopPre 0x103d86) (popR64Effect 0x103d86 2 15) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 65) (.exec 0x103d88 (PopPre 0x103d88) (popR64Effect 0x103d88 1 5) (Reg.operands [.gpr 4] [])) #v[63]
    (cutBlock 0x103d89)))))))))))))

def bytes_l103d73 : List UInt8 :=
  [0x49, 0x8B, 0x44, 0x24, 0x18, 0x4C, 0x89, 0xFF, 0x4C, 0x89, 0xF6, 0x48, 0x89, 0xDA, 0x5B, 0x41,
    0x5C, 0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xFF, 0xE0]

theorem code_l103d73 : ∀ x ∈ codeRange 0x103d73 bytes_l103d73, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3d73 24 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103d8b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103d8b (xorR32R32Effect 0x103d8b 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[0, 0]
    (.letOp (n := 54) (.exec 0x103d8b (fun s => s.RIP = 0x103d8b) (xorR32R32Effect 0x103d8b 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.terminate (.br ⟨.l103d8d, RegMap.args [(0, 53), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l103d8b : List UInt8 :=
  [0x31, 0xC0]

theorem code_l103d8b : ∀ x ∈ codeRange 0x103d8b bytes_l103d8b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3d8b 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103d8d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103d8d (popR64Effect 0x103d8d 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 54) (.out 0x103d8d (popR64Effect 0x103d8d 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 55) (.exec 0x103d8d (PopPre 0x103d8d) (popR64Effect 0x103d8d 1 3) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x103d8e (popR64Effect 0x103d8e 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[54]
    (.letOp (n := 57) (.out 0x103d8e (popR64Effect 0x103d8e 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[54]
    (.letOp (n := 58) (.exec 0x103d8e (PopPre 0x103d8e) (popR64Effect 0x103d8e 2 12) (Reg.operands [.gpr 4] [])) #v[54]
    (.letOp (n := 59) (.out 0x103d90 (popR64Effect 0x103d90 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[57]
    (.letOp (n := 60) (.out 0x103d90 (popR64Effect 0x103d90 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[57]
    (.letOp (n := 61) (.exec 0x103d90 (PopPre 0x103d90) (popR64Effect 0x103d90 2 14) (Reg.operands [.gpr 4] [])) #v[57]
    (.letOp (n := 62) (.out 0x103d92 (popR64Effect 0x103d92 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[60]
    (.letOp (n := 63) (.out 0x103d92 (popR64Effect 0x103d92 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[60]
    (.letOp (n := 64) (.exec 0x103d92 (PopPre 0x103d92) (popR64Effect 0x103d92 2 15) (Reg.operands [.gpr 4] [])) #v[60]
    (.letOp (n := 65) (.out 0x103d94 (popR64Effect 0x103d94 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[63]
    (.letOp (n := 66) (.out 0x103d94 (popR64Effect 0x103d94 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 67) (.exec 0x103d94 (PopPre 0x103d94) (popR64Effect 0x103d94 1 5) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 68) (.out 0x103d95 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[66]
    (.letOp (n := 69) (.out 0x103d95 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[66]
    (.letOp (n := 70) (.exec 0x103d95 (RetPre 0x103d95) (retEffect) (Reg.operands [.gpr 4] [])) #v[66]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 2), (3, 53), (4, 69), (5, 65), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 56), (13, 13), (14, 59), (15, 62), (22, 22), (39, 39), (50, 50), (51, 51)] 71) (some ⟨68, by decide⟩))))))))))))))))))))

def bytes_l103d8d : List UInt8 :=
  [0x5B, 0x41, 0x5C, 0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l103d8d : ∀ x ∈ codeRange 0x103d8d bytes_l103d8d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3d8d 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103da0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103da0 (pushR64Effect 0x103da0 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x103da0 (PushPre 0x103da0 1) (pushR64Effect 0x103da0 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x103da1 (movR64R64Effect 0x103da1 5 4) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[53]
    (.letOp (n := 56) (.exec 0x103da1 (fun s => s.RIP = 0x103da1) (movR64R64Effect 0x103da1 5 4) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 57) (.out 0x103da4 (pushR64Effect 0x103da4 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[53, 3]
    (.letOp (n := 58) (.exec 0x103da4 (PushPre 0x103da4 1) (pushR64Effect 0x103da4 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[53, 3]
    (.letOp (n := 59) (.out 0x103da5 (subR64Imm8Effect 0x103da5 4 0x18) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[57]
    (.letOp (n := 60) (.exec 0x103da5 (fun s => s.RIP = 0x103da5) (subR64Imm8Effect 0x103da5 4 0x18) (Reg.operands [.gpr 4] [])) #v[57]
    (.letOp (n := 61) (.out 0x103da9 (movR64M64Effect 0x103da9 8 (.base 7 .none)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 7] []) (.reg (.gpr 8))) #v[7]
    (.letOp (n := 62) (.exec 0x103da9 (LoadPre 0x103da9 (fun s => AddrMode.addr (.base 7 .none) s (0x103da9 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x103da9 8 (.base 7 .none)) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 63) (.out 0x103dac (movR32Imm32Effect 0x103dac 5 0 0x14) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 64) (.exec 0x103dac (fun s => s.RIP = 0x103dac) (movR32Imm32Effect 0x103dac 5 0 0x14) (Reg.operands [] [])) #v[]
    (.letOp (n := 65) (.out 0x103db1 (leaR64Effect 0x103db1 7 (.rip 0xfd178)) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 66) (.exec 0x103db1 (fun s => s.RIP = 0x103db1) (leaR64Effect 0x103db1 7 (.rip 0xfd178)) (Reg.operands [] [])) #v[]
    (.letOp (n := 67) (.out 0x103db8 (movR64R64Effect 0x103db8 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8] []) (.reg (.gpr 2))) #v[61]
    (.letOp (n := 68) (.exec 0x103db8 (fun s => s.RIP = 0x103db8) (movR64R64Effect 0x103db8 2 8) (Reg.operands [.gpr 8] [])) #v[61]
    (.letOp (n := 69) (.out 0x103dbb (cmpR64Imm32Effect 0x103dbb 8 0x3e8) (EffectPart.reads (.flag .CF) [.gpr 8] []) (.flag .CF)) #v[61]
    (.letOp (n := 70) (.exec 0x103dbb (fun s => s.RIP = 0x103dbb) (cmpR64Imm32Effect 0x103dbb 8 0x3e8) (Reg.operands [.gpr 8] [])) #v[61]
    (.letOp (n := 71) (.pure (condOp 2)) #v[69]
    (.terminate (.condBr (Fin.last 71) ⟨.l103e31, RegMap.args [(0, 63), (1, 1), (2, 67), (3, 3), (4, 59), (5, 55), (6, 6), (7, 65), (8, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩ ⟨.l103dc4, RegMap.args [(0, 63), (1, 1), (2, 67), (3, 3), (4, 59), (5, 55), (6, 6), (7, 65), (8, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩))))))))))))))))))))

def bytes_l103da0 : List UInt8 :=
  [0x55, 0x48, 0x89, 0xE5, 0x53, 0x48, 0x83, 0xEC, 0x18, 0x4C, 0x8B, 0x07, 0xB8, 0x14, 0x00, 0x00,
    0x00, 0x48, 0x8D, 0x3D, 0x78, 0xD1, 0x0F, 0x00, 0x4C, 0x89, 0xC2, 0x49, 0x81, 0xF8, 0xE8, 0x03,
    0x00, 0x00, 0x72, 0x6D]

theorem code_l103da0 : ∀ x ∈ codeRange 0x103da0 bytes_l103da0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3da0 36 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103dc4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103dc4 (movR64Imm64Effect 0x103dc4 9 0x346dc5d63886594b) (EffectPart.reads (.reg (.gpr 9)) [] []) (.reg (.gpr 9))) #v[]
    (.letOp (n := 54) (.exec 0x103dc4 (fun s => s.RIP = 0x103dc4) (movR64Imm64Effect 0x103dc4 9 0x346dc5d63886594b) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x103dce (movR64R64Effect 0x103dce 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 8] []) (.reg (.gpr 1))) #v[8]
    (.letOp (n := 56) (.exec 0x103dce (fun s => s.RIP = 0x103dce) (movR64R64Effect 0x103dce 1 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 57) (.exec 0x103dd1 (fun s => s.RIP = 0x103dd1) (fun _ => nopEffect 0x103dd1 15) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l103de0, RegMap.args [(0, 0), (1, 55), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l103dc4 : List UInt8 :=
  [0x49, 0xB9, 0x4B, 0x59, 0x86, 0x38, 0xD6, 0xC5, 0x6D, 0x34, 0x4C, 0x89, 0xC1, 0x66, 0x66, 0x66,
    0x66, 0x66, 0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem code_l103dc4 : ∀ x ∈ codeRange 0x103dc4 bytes_l103dc4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3dc4 28 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103de0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103de0 (movR64R64Effect 0x103de0 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[0]
    (.letOp (n := 54) (.exec 0x103de0 (fun s => s.RIP = 0x103de0) (movR64R64Effect 0x103de0 10 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x103de3 (movR64R64Effect 0x103de3 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[1]
    (.letOp (n := 56) (.exec 0x103de3 (fun s => s.RIP = 0x103de3) (movR64R64Effect 0x103de3 0 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 57) (.out 0x103de6 (mulR64Effect 0x103de6 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[9, 55]
    (.letOp (n := 58) (.exec 0x103de6 (fun s => s.RIP = 0x103de6) (mulR64Effect 0x103de6 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[9, 55]
    (.letOp (n := 59) (.out 0x103de9 (shrR64Effect 0x103de9 4 2 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[57]
    (.letOp (n := 60) (.exec 0x103de9 (fun s => s.RIP = 0x103de9) (shrR64Effect 0x103de9 4 2 11) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[57]
    (.letOp (n := 61) (.out 0x103ded (imulR32R32Imm32Effect 0x103ded 6 0 2 0x2710) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[59]
    (.letOp (n := 62) (.exec 0x103ded (fun s => s.RIP = 0x103ded) (imulR32R32Imm32Effect 0x103ded 6 0 2 0x2710) (Reg.operands [.gpr 2] [])) #v[59]
    (.letOp (n := 63) (.out 0x103df3 (movR32R32Effect 0x103df3 3 11 1) (EffectPart.reads (.reg (.gpr 11)) [.gpr 1] []) (.reg (.gpr 11))) #v[1]
    (.letOp (n := 64) (.exec 0x103df3 (fun s => s.RIP = 0x103df3) (movR32R32Effect 0x103df3 3 11 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 65) (.out 0x103df6 (subR32R32Effect 0x103df6 3 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0] []) (.reg (.gpr 11))) #v[63, 61]
    (.letOp (n := 66) (.exec 0x103df6 (fun s => s.RIP = 0x103df6) (subR32R32Effect 0x103df6 3 11 0) (Reg.operands [.gpr 11, .gpr 0] [])) #v[63, 61]
    (.letOp (n := 67) (.out 0x103df9 (imulR32R32Imm32Effect 0x103df9 7 0 11 0x147b) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 68) (.exec 0x103df9 (fun s => s.RIP = 0x103df9) (imulR32R32Imm32Effect 0x103df9 7 0 11 0x147b) (Reg.operands [.gpr 11] [])) #v[65]
    (.letOp (n := 69) (.out 0x103e00 (shrR32Effect 0x103e00 3 0 19) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[67]
    (.letOp (n := 70) (.exec 0x103e00 (fun s => s.RIP = 0x103e00) (shrR32Effect 0x103e00 3 0 19) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[67]
    (.letOp (n := 71) (.out 0x103e03 (imulR32R32Imm8Effect 0x103e03 3 3 0 0x64) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[69]
    (.letOp (n := 72) (.exec 0x103e03 (fun s => s.RIP = 0x103e03) (imulR32R32Imm8Effect 0x103e03 3 3 0 0x64) (Reg.operands [.gpr 0] [])) #v[69]
    (.letOp (n := 73) (.out 0x103e06 (subR32R32Effect 0x103e06 3 11 3) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 3] []) (.reg (.gpr 11))) #v[65, 71]
    (.letOp (n := 74) (.exec 0x103e06 (fun s => s.RIP = 0x103e06) (subR32R32Effect 0x103e06 3 11 3) (Reg.operands [.gpr 11, .gpr 3] [])) #v[65, 71]
    (.letOp (n := 75) (.out 0x103e09 (movzxR32M16Effect 0x103e09 4 0 (.sib 7 (some 0) 1 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[7, 69]
    (.letOp (n := 76) (.exec 0x103e09 (LoadPre 0x103e09 (fun s => AddrMode.addr (.sib 7 (some 0) 1 .none) s (0x103e09 + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x103e09 4 0 (.sib 7 (some 0) 1 .none)) (Reg.operands [.gpr 7, .gpr 0] [])) #v[7, 69]
    (.letOp (n := 77) (.exec 0x103e0d (StorePre 0x103e0d 6 (fun s => AddrMode.addr (.sib 5 (some 10) 0 (.d8 0xe0)) s (0x103e0d + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x103e0d 6 0 (.sib 5 (some 10) 0 (.d8 0xe0))) (Reg.operands [.gpr 0, .gpr 5, .gpr 10] [])) #v[75, 5, 53]
    (.letOp (n := 78) (.out 0x103e13 (movzxR32R16Effect 0x103e13 4 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[73]
    (.letOp (n := 79) (.exec 0x103e13 (fun s => s.RIP = 0x103e13) (movzxR32R16Effect 0x103e13 4 0 11) (Reg.operands [.gpr 11] [])) #v[73]
    (.letOp (n := 80) (.out 0x103e17 (movzxR32M16Effect 0x103e17 4 0 (.sib 7 (some 0) 1 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[7, 78]
    (.letOp (n := 81) (.exec 0x103e17 (LoadPre 0x103e17 (fun s => AddrMode.addr (.sib 7 (some 0) 1 .none) s (0x103e17 + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x103e17 4 0 (.sib 7 (some 0) 1 .none)) (Reg.operands [.gpr 7, .gpr 0] [])) #v[7, 78]
    (.letOp (n := 82) (.exec 0x103e1b (StorePre 0x103e1b 6 (fun s => AddrMode.addr (.sib 5 (some 10) 0 (.d8 0xe2)) s (0x103e1b + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x103e1b 6 0 (.sib 5 (some 10) 0 (.d8 0xe2))) (Reg.operands [.gpr 0, .gpr 5, .gpr 10] [])) #v[80, 5, 53]
    (.letOp (n := 83) (.out 0x103e21 (leaR64Effect 0x103e21 0 (.base 10 (.d8 0xfc))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 84) (.exec 0x103e21 (fun s => s.RIP = 0x103e21) (leaR64Effect 0x103e21 0 (.base 10 (.d8 0xfc))) (Reg.operands [.gpr 10] [])) #v[53]
    (.letOp (n := 85) (.out 0x103e25 (cmpR64Imm32Effect 0x103e25 1 0x98967f) (EffectPart.reads (.flag .CF) [.gpr 1] []) (.flag .CF)) #v[1]
    (.letOp (n := 86) (.out 0x103e25 (cmpR64Imm32Effect 0x103e25 1 0x98967f) (EffectPart.reads (.flag .ZF) [.gpr 1] []) (.flag .ZF)) #v[1]
    (.letOp (n := 87) (.exec 0x103e25 (fun s => s.RIP = 0x103e25) (cmpR64Imm32Effect 0x103e25 1 0x98967f) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 88) (.out 0x103e2c (movR64R64Effect 0x103e2c 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[59]
    (.letOp (n := 89) (.exec 0x103e2c (fun s => s.RIP = 0x103e2c) (movR64R64Effect 0x103e2c 1 2) (Reg.operands [.gpr 2] [])) #v[59]
    (.letOp (n := 90) (.pure (condOp 7)) #v[85, 86]
    (.terminate (.condBr (Fin.last 90) ⟨.l103de0, RegMap.args [(0, 83), (1, 88), (2, 59), (3, 71), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 73), (12, 12), (13, 13), (14, 14), (15, 15), (16, 85), (19, 86), (22, 22), (39, 39), (50, 50), (51, 51)] 91⟩ ⟨.l103e31, RegMap.args [(0, 83), (1, 88), (2, 59), (3, 71), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 73), (12, 12), (13, 13), (14, 14), (15, 15), (16, 85), (19, 86), (22, 22), (39, 39), (50, 50), (51, 51)] 91⟩)))))))))))))))))))))))))))))))))))))))

def bytes_l103de0 : List UInt8 :=
  [0x49, 0x89, 0xC2, 0x48, 0x89, 0xC8, 0x49, 0xF7, 0xE1, 0x48, 0xC1, 0xEA, 0x0B, 0x69, 0xC2, 0x10,
    0x27, 0x00, 0x00, 0x41, 0x89, 0xCB, 0x41, 0x29, 0xC3, 0x41, 0x69, 0xC3, 0x7B, 0x14, 0x00, 0x00,
    0xC1, 0xE8, 0x13, 0x6B, 0xD8, 0x64, 0x41, 0x29, 0xDB, 0x0F, 0xB7, 0x04, 0x47, 0x66, 0x42, 0x89,
    0x44, 0x15, 0xE0, 0x41, 0x0F, 0xB7, 0xC3, 0x0F, 0xB7, 0x04, 0x47, 0x66, 0x42, 0x89, 0x44, 0x15,
    0xE2, 0x49, 0x8D, 0x42, 0xFC, 0x48, 0x81, 0xF9, 0x7F, 0x96, 0x98, 0x00, 0x48, 0x89, 0xD1, 0x77,
    0xAF]

theorem code_l103de0 : ∀ x ∈ codeRange 0x103de0 bytes_l103de0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3de0 81 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103e31 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103e31 (cmpR64Imm8Effect 0x103e31 2 0x9) (EffectPart.reads (.flag .CF) [.gpr 2] []) (.flag .CF)) #v[2]
    (.letOp (n := 54) (.out 0x103e31 (cmpR64Imm8Effect 0x103e31 2 0x9) (EffectPart.reads (.flag .ZF) [.gpr 2] []) (.flag .ZF)) #v[2]
    (.letOp (n := 55) (.exec 0x103e31 (fun s => s.RIP = 0x103e31) (cmpR64Imm8Effect 0x103e31 2 0x9) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 56) (.pure (condOp 6)) #v[53, 54]
    (.terminate (.condBr (Fin.last 56) ⟨.l103e62, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩ ⟨.l103e37, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l103e31 : List UInt8 :=
  [0x48, 0x83, 0xFA, 0x09, 0x76, 0x2B]

theorem code_l103e31 : ∀ x ∈ codeRange 0x103e31 bytes_l103e31, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3e31 6 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103e37 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103e37 (movR32R32Effect 0x103e37 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2]
    (.letOp (n := 54) (.exec 0x103e37 (fun s => s.RIP = 0x103e37) (movR32R32Effect 0x103e37 2 1 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 55) (.out 0x103e39 (shrR32Effect 0x103e39 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 56) (.exec 0x103e39 (fun s => s.RIP = 0x103e39) (shrR32Effect 0x103e39 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 57) (.out 0x103e3c (movzxR32R16Effect 0x103e3c 3 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[55]
    (.letOp (n := 58) (.exec 0x103e3c (fun s => s.RIP = 0x103e3c) (movzxR32R16Effect 0x103e3c 3 1 1) (Reg.operands [.gpr 1] [])) #v[55]
    (.letOp (n := 59) (.out 0x103e3f (imulR32R32Imm32Effect 0x103e3f 6 1 1 0x147b) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[57]
    (.letOp (n := 60) (.exec 0x103e3f (fun s => s.RIP = 0x103e3f) (imulR32R32Imm32Effect 0x103e3f 6 1 1 0x147b) (Reg.operands [.gpr 1] [])) #v[57]
    (.letOp (n := 61) (.out 0x103e45 (shrR32Effect 0x103e45 3 1 17) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[59]
    (.letOp (n := 62) (.exec 0x103e45 (fun s => s.RIP = 0x103e45) (shrR32Effect 0x103e45 3 1 17) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[59]
    (.letOp (n := 63) (.out 0x103e48 (imulR32R32Imm8Effect 0x103e48 4 9 1 0x64) (EffectPart.reads (.reg (.gpr 9)) [.gpr 1] []) (.reg (.gpr 9))) #v[61]
    (.letOp (n := 64) (.exec 0x103e48 (fun s => s.RIP = 0x103e48) (imulR32R32Imm8Effect 0x103e48 4 9 1 0x64) (Reg.operands [.gpr 1] [])) #v[61]
    (.letOp (n := 65) (.out 0x103e4c (subR32R32Effect 0x103e4c 3 2 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 9] []) (.reg (.gpr 2))) #v[2, 63]
    (.letOp (n := 66) (.exec 0x103e4c (fun s => s.RIP = 0x103e4c) (subR32R32Effect 0x103e4c 3 2 9) (Reg.operands [.gpr 2, .gpr 9] [])) #v[2, 63]
    (.letOp (n := 67) (.out 0x103e4f (movzxR32R16Effect 0x103e4f 3 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[65]
    (.letOp (n := 68) (.exec 0x103e4f (fun s => s.RIP = 0x103e4f) (movzxR32R16Effect 0x103e4f 3 2 2) (Reg.operands [.gpr 2] [])) #v[65]
    (.letOp (n := 69) (.out 0x103e52 (movzxR32M16Effect 0x103e52 4 2 (.sib 7 (some 2) 1 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 2] []) (.reg (.gpr 2))) #v[7, 67]
    (.letOp (n := 70) (.exec 0x103e52 (LoadPre 0x103e52 (fun s => AddrMode.addr (.sib 7 (some 2) 1 .none) s (0x103e52 + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x103e52 4 2 (.sib 7 (some 2) 1 .none)) (Reg.operands [.gpr 7, .gpr 2] [])) #v[7, 67]
    (.letOp (n := 71) (.exec 0x103e56 (StorePre 0x103e56 5 (fun s => AddrMode.addr (.sib 5 (some 0) 0 (.d8 0xe2)) s (0x103e56 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x103e56 5 2 (.sib 5 (some 0) 0 (.d8 0xe2))) (Reg.operands [.gpr 2, .gpr 5, .gpr 0] [])) #v[69, 5, 0]
    (.letOp (n := 72) (.out 0x103e5b (addR64Imm8Effect 0x103e5b 0 0xfe) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 73) (.exec 0x103e5b (fun s => s.RIP = 0x103e5b) (addR64Imm8Effect 0x103e5b 0 0xfe) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 74) (.out 0x103e5f (movR64R64Effect 0x103e5f 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[61]
    (.letOp (n := 75) (.exec 0x103e5f (fun s => s.RIP = 0x103e5f) (movR64R64Effect 0x103e5f 2 1) (Reg.operands [.gpr 1] [])) #v[61]
    (.terminate (.br ⟨.l103e62, RegMap.args [(0, 72), (1, 61), (2, 74), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 63), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 76⟩))))))))))))))))))))))))

def bytes_l103e37 : List UInt8 :=
  [0x89, 0xD1, 0xC1, 0xE9, 0x02, 0x0F, 0xB7, 0xC9, 0x69, 0xC9, 0x7B, 0x14, 0x00, 0x00, 0xC1, 0xE9,
    0x11, 0x44, 0x6B, 0xC9, 0x64, 0x44, 0x29, 0xCA, 0x0F, 0xB7, 0xD2, 0x0F, 0xB7, 0x14, 0x57, 0x66,
    0x89, 0x54, 0x05, 0xE2, 0x48, 0x83, 0xC0, 0xFE, 0x48, 0x89, 0xCA]

theorem code_l103e37 : ∀ x ∈ codeRange 0x103e37 bytes_l103e37, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3e37 43 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103e62 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103e62 (testR64R64Effect 0x103e62 8 8) (EffectPart.reads (.flag .ZF) [.gpr 8, .gpr 8] []) (.flag .ZF)) #v[8, 8]
    (.letOp (n := 54) (.exec 0x103e62 (fun s => s.RIP = 0x103e62) (testR64R64Effect 0x103e62 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[8, 8]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l103e6c, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l103e67, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l103e62 : List UInt8 :=
  [0x4D, 0x85, 0xC0, 0x74, 0x05]

theorem code_l103e62 : ∀ x ∈ codeRange 0x103e62 bytes_l103e62, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3e62 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103e67 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103e67 (testR64R64Effect 0x103e67 2 2) (EffectPart.reads (.flag .ZF) [.gpr 2, .gpr 2] []) (.flag .ZF)) #v[2, 2]
    (.letOp (n := 54) (.exec 0x103e67 (fun s => s.RIP = 0x103e67) (testR64R64Effect 0x103e67 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l103e78, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l103e6c, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l103e67 : List UInt8 :=
  [0x48, 0x85, 0xD2, 0x74, 0x0C]

theorem code_l103e67 : ∀ x ∈ codeRange 0x103e67 bytes_l103e67, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3e67 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103e6c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103e6c (movzxR32M8Effect 0x103e6c 5 1 (.sib 7 (some 2) 1 (.d8 0x1))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 7, .gpr 2] []) (.reg (.gpr 1))) #v[7, 2]
    (.letOp (n := 54) (.exec 0x103e6c (LoadPre 0x103e6c (fun s => AddrMode.addr (.sib 7 (some 2) 1 (.d8 0x1)) s (0x103e6c + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x103e6c 5 1 (.sib 7 (some 2) 1 (.d8 0x1))) (Reg.operands [.gpr 7, .gpr 2] [])) #v[7, 2]
    (.letOp (n := 55) (.exec 0x103e71 (StorePre 0x103e71 4 (fun s => AddrMode.addr (.sib 5 (some 0) 0 (.d8 0xe3)) s (0x103e71 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x103e71 4 1 (.sib 5 (some 0) 0 (.d8 0xe3))) (Reg.operands [.gpr 1, .gpr 5, .gpr 0] [])) #v[53, 5, 0]
    (.letOp (n := 56) (.out 0x103e75 (decR64Effect 0x103e75 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 57) (.exec 0x103e75 (fun s => s.RIP = 0x103e75) (decR64Effect 0x103e75 0) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[0]
    (.terminate (.br ⟨.l103e78, RegMap.args [(0, 56), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l103e6c : List UInt8 :=
  [0x0F, 0xB6, 0x4C, 0x57, 0x01, 0x88, 0x4C, 0x05, 0xE3, 0x48, 0xFF, 0xC8]

theorem code_l103e6c : ∀ x ∈ codeRange 0x103e6c bytes_l103e6c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3e6c 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103e78 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103e78 (movR32Imm32Effect 0x103e78 6 9 0x14) (EffectPart.reads (.reg (.gpr 9)) [] []) (.reg (.gpr 9))) #v[]
    (.letOp (n := 54) (.exec 0x103e78 (fun s => s.RIP = 0x103e78) (movR32Imm32Effect 0x103e78 6 9 0x14) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x103e7e (subR64R64Effect 0x103e7e 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0] []) (.reg (.gpr 9))) #v[53, 0]
    (.letOp (n := 56) (.exec 0x103e7e (fun s => s.RIP = 0x103e7e) (subR64R64Effect 0x103e7e 9 0) (Reg.operands [.gpr 9, .gpr 0] [])) #v[53, 0]
    (.letOp (n := 57) (.out 0x103e81 (leaR64Effect 0x103e81 8 (.sib 0 (some 5) 0 .none)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0, .gpr 5] []) (.reg (.gpr 8))) #v[0, 5]
    (.letOp (n := 58) (.exec 0x103e81 (fun s => s.RIP = 0x103e81) (leaR64Effect 0x103e81 8 (.sib 0 (some 5) 0 .none)) (Reg.operands [.gpr 0, .gpr 5] [])) #v[0, 5]
    (.letOp (n := 59) (.out 0x103e85 (addR64Imm8Effect 0x103e85 8 0xe4) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[57]
    (.letOp (n := 60) (.exec 0x103e85 (fun s => s.RIP = 0x103e85) (addR64Imm8Effect 0x103e85 8 0xe4) (Reg.operands [.gpr 8] [])) #v[57]
    (.letOp (n := 61) (.out 0x103e89 (movR32Imm32Effect 0x103e89 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 62) (.exec 0x103e89 (fun s => s.RIP = 0x103e89) (movR32Imm32Effect 0x103e89 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 63) (.out 0x103e8e (movR64R64Effect 0x103e8e 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[6]
    (.letOp (n := 64) (.exec 0x103e8e (fun s => s.RIP = 0x103e8e) (movR64R64Effect 0x103e8e 7 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 65) (.out 0x103e91 (movR32Imm32Effect 0x103e91 5 6 0x1) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 66) (.exec 0x103e91 (fun s => s.RIP = 0x103e91) (movR32Imm32Effect 0x103e91 5 6 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 67) (.out 0x103e96 (xorR32R32Effect 0x103e96 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[1, 1]
    (.letOp (n := 68) (.exec 0x103e96 (fun s => s.RIP = 0x103e96) (xorR32R32Effect 0x103e96 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[1, 1]
    (.letOp (n := 69) (.out 0x103e98 (callEffect (callMemPtr 0x103e98 (.rip 0xfd37a)) (0x103e98 + BitVec.ofNat 64 (callMemLen (.rip 0xfd37a)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 70) (.exec 0x103e98 (GoesTo (CallMemPre 0x103e98 (.rip 0xfd37a)) (callEffect (callMemPtr 0x103e98 (.rip 0xfd37a)) (0x103e98 + BitVec.ofNat 64 (callMemLen (.rip 0xfd37a)))) 0x103520) (callEffect (callMemPtr 0x103e98 (.rip 0xfd37a)) (0x103e98 + BitVec.ofNat 64 (callMemLen (.rip 0xfd37a)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.const ⟨64, 0x103e9e⟩) #v[]
    (.terminate (.call ⟨.l103520, RegMap.args [(0, 0), (1, 67), (2, 61), (3, 3), (4, 69), (5, 5), (6, 65), (7, 63), (8, 59), (9, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩ { target := .l103e9e, kept := #v[], arity := rfl, guard := some (Fin.last 71) }))))))))))))))))))))

def bytes_l103e78 : List UInt8 :=
  [0x41, 0xB9, 0x14, 0x00, 0x00, 0x00, 0x49, 0x29, 0xC1, 0x4C, 0x8D, 0x04, 0x28, 0x49, 0x83, 0xC0,
    0xE4, 0xBA, 0x01, 0x00, 0x00, 0x00, 0x48, 0x89, 0xF7, 0xBE, 0x01, 0x00, 0x00, 0x00, 0x31, 0xC9,
    0xFF, 0x15, 0x7A, 0xD3, 0x0F, 0x00]

theorem code_l103e78 : ∀ x ∈ codeRange 0x103e78 bytes_l103e78, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3e78 38 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103e9e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103e9e (addR64Imm8Effect 0x103e9e 4 0x18) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 54) (.exec 0x103e9e (fun s => s.RIP = 0x103e9e) (addR64Imm8Effect 0x103e9e 4 0x18) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x103ea2 (popR64Effect 0x103ea2 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[53]
    (.letOp (n := 56) (.out 0x103ea2 (popR64Effect 0x103ea2 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[53]
    (.letOp (n := 57) (.exec 0x103ea2 (PopPre 0x103ea2) (popR64Effect 0x103ea2 1 3) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 58) (.out 0x103ea3 (popR64Effect 0x103ea3 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[56]
    (.letOp (n := 59) (.out 0x103ea3 (popR64Effect 0x103ea3 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[56]
    (.letOp (n := 60) (.exec 0x103ea3 (PopPre 0x103ea3) (popR64Effect 0x103ea3 1 5) (Reg.operands [.gpr 4] [])) #v[56]
    (.letOp (n := 61) (.out 0x103ea4 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[59]
    (.letOp (n := 62) (.out 0x103ea4 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 63) (.exec 0x103ea4 (RetPre 0x103ea4) (retEffect) (Reg.operands [.gpr 4] [])) #v[59]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 2), (3, 55), (4, 62), (5, 58), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 64) (some ⟨61, by decide⟩)))))))))))))

def bytes_l103e9e : List UInt8 :=
  [0x48, 0x83, 0xC4, 0x18, 0x5B, 0x5D, 0xC3]

theorem code_l103e9e : ∀ x ∈ codeRange 0x103e9e bytes_l103e9e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3e9e 7 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103eb0_1 : Block Op Label signature Reg.count 94 :=
  .letOp (n := 94) (.out 0x103ef4 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[4]
    (.letOp (n := 95) (.out 0x103ef4 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 96) (.exec 0x103ef4 (RetPre 0x103ef4) (retEffect) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.ret (RegMap.args [(0, 92), (1, 90), (2, 55), (3, 3), (4, 95), (5, 5), (6, 77), (7, 89), (8, 79), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 97) (some ⟨94, by decide⟩)))))

def bytes_l103eb0_1 : List UInt8 :=
  [0xC3]

theorem code_l103eb0_1 : ∀ x ∈ codeRange 0x103ef4 bytes_l103eb0_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3ef4 1 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103eb0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103eb0 (movR64R64Effect 0x103eb0 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[2]
    (.letOp (n := 54) (.exec 0x103eb0 (fun s => s.RIP = 0x103eb0) (movR64R64Effect 0x103eb0 8 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 55) (.out 0x103eb3 (movR64R64Effect 0x103eb3 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7] []) (.reg (.gpr 2))) #v[7]
    (.letOp (n := 56) (.exec 0x103eb3 (fun s => s.RIP = 0x103eb3) (movR64R64Effect 0x103eb3 2 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 57) (.out 0x103eb6 (movzxR32R8Effect 0x103eb6 4 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[6]
    (.letOp (n := 58) (.exec 0x103eb6 (fun s => s.RIP = 0x103eb6) (movzxR32R8Effect 0x103eb6 4 1 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 59) (.out 0x103eba (movR64Imm64Effect 0x103eba 0 0x101010101010101) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 60) (.exec 0x103eba (fun s => s.RIP = 0x103eba) (movR64Imm64Effect 0x103eba 0 0x101010101010101) (Reg.operands [] [])) #v[]
    (.letOp (n := 61) (.out 0x103ec4 (imulR64R64Effect 0x103ec4 4 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[59, 57]
    (.letOp (n := 62) (.exec 0x103ec4 (fun s => s.RIP = 0x103ec4) (imulR64R64Effect 0x103ec4 4 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[59, 57]
    (.letOp (n := 63) (.out 0x103ec8 (movR32R32Effect 0x103ec8 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[55]
    (.letOp (n := 64) (.exec 0x103ec8 (fun s => s.RIP = 0x103ec8) (movR32R32Effect 0x103ec8 2 1 2) (Reg.operands [.gpr 2] [])) #v[55]
    (.letOp (n := 65) (.out 0x103eca (negR32Effect 0x103eca 2 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[63]
    (.letOp (n := 66) (.exec 0x103eca (fun s => s.RIP = 0x103eca) (negR32Effect 0x103eca 2 1) (Reg.operands [.gpr 1] [])) #v[63]
    (.letOp (n := 67) (.out 0x103ecc (andR32Imm8Effect 0x103ecc 3 1 0x7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 68) (.exec 0x103ecc (fun s => s.RIP = 0x103ecc) (andR32Imm8Effect 0x103ecc 3 1 0x7) (Reg.operands [.gpr 1] [])) #v[65]
    (.letOp (n := 69) (.out 0x103ecf (cmpR64R64Effect 0x103ecf 8 1) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 1] []) (.flag .CF)) #v[53, 67]
    (.letOp (n := 70) (.exec 0x103ecf (fun s => s.RIP = 0x103ecf) (cmpR64R64Effect 0x103ecf 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[53, 67]
    (.letOp (n := 71) (.out 0x103ed2 (atFlags (condHolds 2) (cmovR64R64Effect 0x103ed2 4 1 8)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[67, 53, 69]
    (.letOp (n := 72) (.exec 0x103ed2 (fun s => s.RIP = 0x103ed2) (atFlags (condHolds 2) (cmovR64R64Effect 0x103ed2 4 1 8)) (Reg.operands [.gpr 1, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[67, 53, 69]
    (.letOp (n := 73) (.out 0x103ed6 (subR64R64Effect 0x103ed6 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[53, 71]
    (.letOp (n := 74) (.exec 0x103ed6 (fun s => s.RIP = 0x103ed6) (subR64R64Effect 0x103ed6 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[53, 71]
    (.letOp (n := 75) (.out 0x103ed9 (movR64R64Effect 0x103ed9 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 8] []) (.reg (.gpr 6))) #v[73]
    (.letOp (n := 76) (.exec 0x103ed9 (fun s => s.RIP = 0x103ed9) (movR64R64Effect 0x103ed9 6 8) (Reg.operands [.gpr 8] [])) #v[73]
    (.letOp (n := 77) (.out 0x103edc (shrR64Effect 0x103edc 4 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[75]
    (.letOp (n := 78) (.exec 0x103edc (fun s => s.RIP = 0x103edc) (shrR64Effect 0x103edc 4 6 3) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[75]
    (.letOp (n := 79) (.out 0x103ee0 (andR32Imm8Effect 0x103ee0 4 8 0x7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[73]
    (.letOp (n := 80) (.exec 0x103ee0 (fun s => s.RIP = 0x103ee0) (andR32Imm8Effect 0x103ee0 4 8 0x7) (Reg.operands [.gpr 8] [])) #v[73]
    (.letOp (n := 81) (.out 0x103ee4 (repStosbEffect 0x103ee4) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 7))) #v[61, 7, 71, 22]
    (.letOp (n := 82) (.exec 0x103ee4 (RepPre 0x103ee4 (RepStosbPre 0x103ee4)) (repStosbEffect 0x103ee4) (Reg.operands [.gpr 0, .gpr 7, .gpr 1, .df] [])) #v[61, 7, 71, 22]
    (.letOp (n := 83) (.out 0x103ee6 (movR64R64Effect 0x103ee6 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[77]
    (.letOp (n := 84) (.exec 0x103ee6 (fun s => s.RIP = 0x103ee6) (movR64R64Effect 0x103ee6 1 6) (Reg.operands [.gpr 6] [])) #v[77]
    (.letOp (n := 85) (.out 0x103ee9 (repStosqEffect 0x103ee9) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 7))) #v[61, 81, 83, 22]
    (.letOp (n := 86) (.exec 0x103ee9 (RepPre 0x103ee9 (RepStosqPre 0x103ee9)) (repStosqEffect 0x103ee9) (Reg.operands [.gpr 0, .gpr 7, .gpr 1, .df] [])) #v[61, 81, 83, 22]
    (.letOp (n := 87) (.out 0x103eec (movR64R64Effect 0x103eec 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 8] []) (.reg (.gpr 1))) #v[79]
    (.letOp (n := 88) (.exec 0x103eec (fun s => s.RIP = 0x103eec) (movR64R64Effect 0x103eec 1 8) (Reg.operands [.gpr 8] [])) #v[79]
    (.letOp (n := 89) (.out 0x103eef (repStosbEffect 0x103eef) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 7))) #v[61, 85, 87, 22]
    (.letOp (n := 90) (.out 0x103eef (repStosbEffect 0x103eef) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 1))) #v[61, 85, 87, 22]
    (.letOp (n := 91) (.exec 0x103eef (RepPre 0x103eef (RepStosbPre 0x103eef)) (repStosbEffect 0x103eef) (Reg.operands [.gpr 0, .gpr 7, .gpr 1, .df] [])) #v[61, 85, 87, 22]
    (.letOp (n := 92) (.out 0x103ef1 (movR64R64Effect 0x103ef1 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[55]
    (.letOp (n := 93) (.exec 0x103ef1 (fun s => s.RIP = 0x103ef1) (movR64R64Effect 0x103ef1 0 2) (Reg.operands [.gpr 2] [])) #v[55]
    (b_l103eb0_1)))))))))))))))))))))))))))))))))))))))))

def bytes_l103eb0 : List UInt8 :=
  [0x49, 0x89, 0xD0, 0x48, 0x89, 0xFA, 0x40, 0x0F, 0xB6, 0xCE, 0x48, 0xB8, 0x01, 0x01, 0x01, 0x01,
    0x01, 0x01, 0x01, 0x01, 0x48, 0x0F, 0xAF, 0xC1, 0x89, 0xD1, 0xF7, 0xD9, 0x83, 0xE1, 0x07, 0x49,
    0x39, 0xC8, 0x49, 0x0F, 0x42, 0xC8, 0x49, 0x29, 0xC8, 0x4C, 0x89, 0xC6, 0x48, 0xC1, 0xEE, 0x03,
    0x41, 0x83, 0xE0, 0x07, 0xF3, 0xAA, 0x48, 0x89, 0xF1, 0xF3, 0x48, 0xAB, 0x4C, 0x89, 0xC1, 0xF3,
    0xAA, 0x48, 0x89, 0xD0] ++ bytes_l103eb0_1

theorem code_l103eb0 : ∀ x ∈ codeRange 0x103eb0 bytes_l103eb0, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x3eb0 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l103eb0_1

@[cfg_block] def b_l103f00 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103f00 (movR64R64Effect 0x103f00 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 54) (.exec 0x103f00 (fun s => s.RIP = 0x103f00) (movR64R64Effect 0x103f00 0 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 55) (.out 0x103f03 (movR32R32Effect 0x103f03 3 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[53]
    (.letOp (n := 56) (.exec 0x103f03 (fun s => s.RIP = 0x103f03) (movR32R32Effect 0x103f03 3 8 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x103f06 (negR32Effect 0x103f06 3 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[55]
    (.letOp (n := 58) (.exec 0x103f06 (fun s => s.RIP = 0x103f06) (negR32Effect 0x103f06 3 8) (Reg.operands [.gpr 8] [])) #v[55]
    (.letOp (n := 59) (.out 0x103f09 (andR32Imm8Effect 0x103f09 4 8 0x7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[57]
    (.letOp (n := 60) (.exec 0x103f09 (fun s => s.RIP = 0x103f09) (andR32Imm8Effect 0x103f09 4 8 0x7) (Reg.operands [.gpr 8] [])) #v[57]
    (.letOp (n := 61) (.out 0x103f0d (cmpR64R64Effect 0x103f0d 2 8) (EffectPart.reads (.flag .CF) [.gpr 2, .gpr 8] []) (.flag .CF)) #v[2, 59]
    (.letOp (n := 62) (.exec 0x103f0d (fun s => s.RIP = 0x103f0d) (cmpR64R64Effect 0x103f0d 2 8) (Reg.operands [.gpr 2, .gpr 8] [])) #v[2, 59]
    (.letOp (n := 63) (.out 0x103f10 (atFlags (condHolds 2) (cmovR64R64Effect 0x103f10 4 8 2)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[59, 2, 61]
    (.letOp (n := 64) (.exec 0x103f10 (fun s => s.RIP = 0x103f10) (atFlags (condHolds 2) (cmovR64R64Effect 0x103f10 4 8 2)) (Reg.operands [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[59, 2, 61]
    (.letOp (n := 65) (.out 0x103f14 (movR64R64Effect 0x103f14 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 8] []) (.reg (.gpr 1))) #v[63]
    (.letOp (n := 66) (.exec 0x103f14 (fun s => s.RIP = 0x103f14) (movR64R64Effect 0x103f14 1 8) (Reg.operands [.gpr 8] [])) #v[63]
    (.letOp (n := 67) (.out 0x103f17 (repMovsbEffect 0x103f17) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 6))) #v[6, 7, 65, 22]
    (.letOp (n := 68) (.out 0x103f17 (repMovsbEffect 0x103f17) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 7))) #v[6, 7, 65, 22]
    (.letOp (n := 69) (.exec 0x103f17 (RepPre 0x103f17 (RepMovsbPre 0x103f17)) (repMovsbEffect 0x103f17) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[6, 7, 65, 22]
    (.letOp (n := 70) (.out 0x103f19 (subR64R64Effect 0x103f19 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 8] []) (.reg (.gpr 2))) #v[2, 63]
    (.letOp (n := 71) (.exec 0x103f19 (fun s => s.RIP = 0x103f19) (subR64R64Effect 0x103f19 2 8) (Reg.operands [.gpr 2, .gpr 8] [])) #v[2, 63]
    (.letOp (n := 72) (.out 0x103f1c (movR64R64Effect 0x103f1c 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[70]
    (.letOp (n := 73) (.exec 0x103f1c (fun s => s.RIP = 0x103f1c) (movR64R64Effect 0x103f1c 1 2) (Reg.operands [.gpr 2] [])) #v[70]
    (.letOp (n := 74) (.out 0x103f1f (shrR64Effect 0x103f1f 4 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[72]
    (.letOp (n := 75) (.exec 0x103f1f (fun s => s.RIP = 0x103f1f) (shrR64Effect 0x103f1f 4 1 3) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[72]
    (.letOp (n := 76) (.out 0x103f23 (repMovsqEffect 0x103f23) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 6))) #v[67, 68, 74, 22]
    (.letOp (n := 77) (.out 0x103f23 (repMovsqEffect 0x103f23) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 7))) #v[67, 68, 74, 22]
    (.letOp (n := 78) (.exec 0x103f23 (RepPre 0x103f23 (RepMovsqPre 0x103f23)) (repMovsqEffect 0x103f23) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[67, 68, 74, 22]
    (.letOp (n := 79) (.out 0x103f26 (andR32Imm8Effect 0x103f26 3 2 0x7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[70]
    (.letOp (n := 80) (.exec 0x103f26 (fun s => s.RIP = 0x103f26) (andR32Imm8Effect 0x103f26 3 2 0x7) (Reg.operands [.gpr 2] [])) #v[70]
    (.letOp (n := 81) (.out 0x103f29 (movR64R64Effect 0x103f29 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[79]
    (.letOp (n := 82) (.exec 0x103f29 (fun s => s.RIP = 0x103f29) (movR64R64Effect 0x103f29 1 2) (Reg.operands [.gpr 2] [])) #v[79]
    (.letOp (n := 83) (.out 0x103f2c (repMovsbEffect 0x103f2c) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 6))) #v[76, 77, 81, 22]
    (.letOp (n := 84) (.out 0x103f2c (repMovsbEffect 0x103f2c) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 7))) #v[76, 77, 81, 22]
    (.letOp (n := 85) (.out 0x103f2c (repMovsbEffect 0x103f2c) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 1))) #v[76, 77, 81, 22]
    (.letOp (n := 86) (.exec 0x103f2c (RepPre 0x103f2c (RepMovsbPre 0x103f2c)) (repMovsbEffect 0x103f2c) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[76, 77, 81, 22]
    (.letOp (n := 87) (.out 0x103f2e (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[4]
    (.letOp (n := 88) (.out 0x103f2e (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 89) (.exec 0x103f2e (RetPre 0x103f2e) (retEffect) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.ret (RegMap.args [(0, 53), (1, 85), (2, 79), (3, 3), (4, 88), (5, 5), (6, 83), (7, 84), (8, 63), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 90) (some ⟨87, by decide⟩)))))))))))))))))))))))))))))))))))))))

def bytes_l103f00 : List UInt8 :=
  [0x48, 0x89, 0xF8, 0x41, 0x89, 0xC0, 0x41, 0xF7, 0xD8, 0x41, 0x83, 0xE0, 0x07, 0x4C, 0x39, 0xC2,
    0x4C, 0x0F, 0x42, 0xC2, 0x4C, 0x89, 0xC1, 0xF3, 0xA4, 0x4C, 0x29, 0xC2, 0x48, 0x89, 0xD1, 0x48,
    0xC1, 0xE9, 0x03, 0xF3, 0x48, 0xA5, 0x83, 0xE2, 0x07, 0x48, 0x89, 0xD1, 0xF3, 0xA4, 0xC3]

theorem code_l103f00 : ∀ x ∈ codeRange 0x103f00 bytes_l103f00, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3f00 47 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103f30 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103f30 (pushR64Effect 0x103f30 1 0) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 0] []) (.reg (.gpr 4))) #v[4, 0]
    (.letOp (n := 54) (.exec 0x103f30 (PushPre 0x103f30 1) (pushR64Effect 0x103f30 1 0) (Reg.operands [.gpr 4, .gpr 0] [])) #v[4, 0]
    (.letOp (n := 55) (.out 0x103f31 (leaR64Effect 0x103f31 0 (.base 2 (.d8 0x7))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 56) (.exec 0x103f31 (fun s => s.RIP = 0x103f31) (leaR64Effect 0x103f31 0 (.base 2 (.d8 0x7))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 57) (.out 0x103f35 (cmpR64R64Effect 0x103f35 0 6) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 6] []) (.flag .CF)) #v[55, 6]
    (.letOp (n := 58) (.exec 0x103f35 (fun s => s.RIP = 0x103f35) (cmpR64R64Effect 0x103f35 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[55, 6]
    (.letOp (n := 59) (.pure (condOp 3)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l103ffa, RegMap.args [(0, 55), (1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l103f3e, RegMap.args [(0, 55), (1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l103f30 : List UInt8 :=
  [0x50, 0x48, 0x8D, 0x42, 0x07, 0x48, 0x39, 0xF0, 0x0F, 0x83, 0xBC, 0x00, 0x00, 0x00]

theorem code_l103f30 : ∀ x ∈ codeRange 0x103f30 bytes_l103f30, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3f30 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103f3e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103f3e (leaR64Effect 0x103f3e 0 (.base 2 (.d8 0xf))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 54) (.exec 0x103f3e (fun s => s.RIP = 0x103f3e) (leaR64Effect 0x103f3e 0 (.base 2 (.d8 0xf))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 55) (.out 0x103f42 (cmpR64R64Effect 0x103f42 0 6) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 6] []) (.flag .CF)) #v[53, 6]
    (.letOp (n := 56) (.exec 0x103f42 (fun s => s.RIP = 0x103f42) (cmpR64R64Effect 0x103f42 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[53, 6]
    (.letOp (n := 57) (.pure (condOp 3)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l103fe8, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l103f4b, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l103f3e : List UInt8 :=
  [0x48, 0x8D, 0x42, 0x0F, 0x48, 0x39, 0xF0, 0x0F, 0x83, 0x9D, 0x00, 0x00, 0x00]

theorem code_l103f3e : ∀ x ∈ codeRange 0x103f3e bytes_l103f3e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3f3e 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103f4b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103f4b (movzxR32M16Effect 0x103f4b 5 0 (.sib 7 (some 2) 1 (.d8 0xe))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 2] []) (.reg (.gpr 0))) #v[7, 2]
    (.letOp (n := 54) (.exec 0x103f4b (LoadPre 0x103f4b (fun s => AddrMode.addr (.sib 7 (some 2) 1 (.d8 0xe)) s (0x103f4b + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x103f4b 5 0 (.sib 7 (some 2) 1 (.d8 0xe))) (Reg.operands [.gpr 7, .gpr 2] [])) #v[7, 2]
    (.letOp (n := 55) (.exec 0x103f50 (StorePre 0x103f50 5 (fun s => AddrMode.addr (.sib 7 (some 2) 1 (.d8 0x1e)) s (0x103f50 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x103f50 5 0 (.sib 7 (some 2) 1 (.d8 0x1e))) (Reg.operands [.gpr 0, .gpr 7, .gpr 2] [])) #v[53, 7, 2]
    (.letOp (n := 56) (.out 0x103f55 (leaR64Effect 0x103f55 0 (.base 2 (.d8 0x6))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 57) (.exec 0x103f55 (fun s => s.RIP = 0x103f55) (leaR64Effect 0x103f55 0 (.base 2 (.d8 0x6))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 58) (.out 0x103f59 (cmpR64R64Effect 0x103f59 0 6) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 6] []) (.flag .CF)) #v[56, 6]
    (.letOp (n := 59) (.exec 0x103f59 (fun s => s.RIP = 0x103f59) (cmpR64R64Effect 0x103f59 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[56, 6]
    (.letOp (n := 60) (.pure (condOp 3)) #v[58]
    (.terminate (.condBr (Fin.last 60) ⟨.l103ffa, RegMap.args [(0, 56), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩ ⟨.l103f62, RegMap.args [(0, 56), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩)))))))))

def bytes_l103f4b : List UInt8 :=
  [0x0F, 0xB7, 0x44, 0x57, 0x0E, 0x66, 0x89, 0x44, 0x57, 0x1E, 0x48, 0x8D, 0x42, 0x06, 0x48, 0x39,
    0xF0, 0x0F, 0x83, 0x98, 0x00, 0x00, 0x00]

theorem code_l103f4b : ∀ x ∈ codeRange 0x103f4b bytes_l103f4b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3f4b 23 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103f62 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103f62 (movzxR32M16Effect 0x103f62 5 0 (.sib 7 (some 2) 1 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 2] []) (.reg (.gpr 0))) #v[7, 2]
    (.letOp (n := 54) (.exec 0x103f62 (LoadPre 0x103f62 (fun s => AddrMode.addr (.sib 7 (some 2) 1 (.d8 0xc)) s (0x103f62 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x103f62 5 0 (.sib 7 (some 2) 1 (.d8 0xc))) (Reg.operands [.gpr 7, .gpr 2] [])) #v[7, 2]
    (.letOp (n := 55) (.exec 0x103f67 (StorePre 0x103f67 5 (fun s => AddrMode.addr (.sib 7 (some 2) 1 (.d8 0x1c)) s (0x103f67 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x103f67 5 0 (.sib 7 (some 2) 1 (.d8 0x1c))) (Reg.operands [.gpr 0, .gpr 7, .gpr 2] [])) #v[53, 7, 2]
    (.letOp (n := 56) (.out 0x103f6c (leaR64Effect 0x103f6c 0 (.base 2 (.d8 0x5))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 57) (.exec 0x103f6c (fun s => s.RIP = 0x103f6c) (leaR64Effect 0x103f6c 0 (.base 2 (.d8 0x5))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 58) (.out 0x103f70 (cmpR64R64Effect 0x103f70 0 6) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 6] []) (.flag .CF)) #v[56, 6]
    (.letOp (n := 59) (.exec 0x103f70 (fun s => s.RIP = 0x103f70) (cmpR64R64Effect 0x103f70 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[56, 6]
    (.letOp (n := 60) (.pure (condOp 3)) #v[58]
    (.terminate (.condBr (Fin.last 60) ⟨.l103ffa, RegMap.args [(0, 56), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩ ⟨.l103f79, RegMap.args [(0, 56), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩)))))))))

def bytes_l103f62 : List UInt8 :=
  [0x0F, 0xB7, 0x44, 0x57, 0x0C, 0x66, 0x89, 0x44, 0x57, 0x1C, 0x48, 0x8D, 0x42, 0x05, 0x48, 0x39,
    0xF0, 0x0F, 0x83, 0x81, 0x00, 0x00, 0x00]

theorem code_l103f62 : ∀ x ∈ codeRange 0x103f62 bytes_l103f62, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3f62 23 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103f79 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103f79 (movzxR32M16Effect 0x103f79 5 0 (.sib 7 (some 2) 1 (.d8 0xa))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 2] []) (.reg (.gpr 0))) #v[7, 2]
    (.letOp (n := 54) (.exec 0x103f79 (LoadPre 0x103f79 (fun s => AddrMode.addr (.sib 7 (some 2) 1 (.d8 0xa)) s (0x103f79 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x103f79 5 0 (.sib 7 (some 2) 1 (.d8 0xa))) (Reg.operands [.gpr 7, .gpr 2] [])) #v[7, 2]
    (.letOp (n := 55) (.exec 0x103f7e (StorePre 0x103f7e 5 (fun s => AddrMode.addr (.sib 7 (some 2) 1 (.d8 0x1a)) s (0x103f7e + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x103f7e 5 0 (.sib 7 (some 2) 1 (.d8 0x1a))) (Reg.operands [.gpr 0, .gpr 7, .gpr 2] [])) #v[53, 7, 2]
    (.letOp (n := 56) (.out 0x103f83 (leaR64Effect 0x103f83 0 (.base 2 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 57) (.exec 0x103f83 (fun s => s.RIP = 0x103f83) (leaR64Effect 0x103f83 0 (.base 2 (.d8 0x4))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 58) (.out 0x103f87 (cmpR64R64Effect 0x103f87 0 6) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 6] []) (.flag .CF)) #v[56, 6]
    (.letOp (n := 59) (.exec 0x103f87 (fun s => s.RIP = 0x103f87) (cmpR64R64Effect 0x103f87 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[56, 6]
    (.letOp (n := 60) (.pure (condOp 3)) #v[58]
    (.terminate (.condBr (Fin.last 60) ⟨.l103ffa, RegMap.args [(0, 56), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩ ⟨.l103f8c, RegMap.args [(0, 56), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩)))))))))

def bytes_l103f79 : List UInt8 :=
  [0x0F, 0xB7, 0x44, 0x57, 0x0A, 0x66, 0x89, 0x44, 0x57, 0x1A, 0x48, 0x8D, 0x42, 0x04, 0x48, 0x39,
    0xF0, 0x73, 0x6E]

theorem code_l103f79 : ∀ x ∈ codeRange 0x103f79 bytes_l103f79, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3f79 19 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103f8c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103f8c (movzxR32M16Effect 0x103f8c 5 0 (.sib 7 (some 2) 1 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 2] []) (.reg (.gpr 0))) #v[7, 2]
    (.letOp (n := 54) (.exec 0x103f8c (LoadPre 0x103f8c (fun s => AddrMode.addr (.sib 7 (some 2) 1 (.d8 0x8)) s (0x103f8c + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x103f8c 5 0 (.sib 7 (some 2) 1 (.d8 0x8))) (Reg.operands [.gpr 7, .gpr 2] [])) #v[7, 2]
    (.letOp (n := 55) (.exec 0x103f91 (StorePre 0x103f91 5 (fun s => AddrMode.addr (.sib 7 (some 2) 1 (.d8 0x18)) s (0x103f91 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x103f91 5 0 (.sib 7 (some 2) 1 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 7, .gpr 2] [])) #v[53, 7, 2]
    (.letOp (n := 56) (.out 0x103f96 (leaR64Effect 0x103f96 0 (.base 2 (.d8 0x3))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 57) (.exec 0x103f96 (fun s => s.RIP = 0x103f96) (leaR64Effect 0x103f96 0 (.base 2 (.d8 0x3))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 58) (.out 0x103f9a (cmpR64R64Effect 0x103f9a 0 6) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 6] []) (.flag .CF)) #v[56, 6]
    (.letOp (n := 59) (.exec 0x103f9a (fun s => s.RIP = 0x103f9a) (cmpR64R64Effect 0x103f9a 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[56, 6]
    (.letOp (n := 60) (.pure (condOp 3)) #v[58]
    (.terminate (.condBr (Fin.last 60) ⟨.l103ffa, RegMap.args [(0, 56), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩ ⟨.l103f9f, RegMap.args [(0, 56), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩)))))))))

def bytes_l103f8c : List UInt8 :=
  [0x0F, 0xB7, 0x44, 0x57, 0x08, 0x66, 0x89, 0x44, 0x57, 0x18, 0x48, 0x8D, 0x42, 0x03, 0x48, 0x39,
    0xF0, 0x73, 0x5B]

theorem code_l103f8c : ∀ x ∈ codeRange 0x103f8c bytes_l103f8c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3f8c 19 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103f9f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103f9f (movzxR32M16Effect 0x103f9f 5 0 (.sib 7 (some 2) 1 (.d8 0x6))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 2] []) (.reg (.gpr 0))) #v[7, 2]
    (.letOp (n := 54) (.exec 0x103f9f (LoadPre 0x103f9f (fun s => AddrMode.addr (.sib 7 (some 2) 1 (.d8 0x6)) s (0x103f9f + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x103f9f 5 0 (.sib 7 (some 2) 1 (.d8 0x6))) (Reg.operands [.gpr 7, .gpr 2] [])) #v[7, 2]
    (.letOp (n := 55) (.exec 0x103fa4 (StorePre 0x103fa4 5 (fun s => AddrMode.addr (.sib 7 (some 2) 1 (.d8 0x16)) s (0x103fa4 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x103fa4 5 0 (.sib 7 (some 2) 1 (.d8 0x16))) (Reg.operands [.gpr 0, .gpr 7, .gpr 2] [])) #v[53, 7, 2]
    (.letOp (n := 56) (.out 0x103fa9 (leaR64Effect 0x103fa9 0 (.base 2 (.d8 0x2))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 57) (.exec 0x103fa9 (fun s => s.RIP = 0x103fa9) (leaR64Effect 0x103fa9 0 (.base 2 (.d8 0x2))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 58) (.out 0x103fad (cmpR64R64Effect 0x103fad 0 6) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 6] []) (.flag .CF)) #v[56, 6]
    (.letOp (n := 59) (.exec 0x103fad (fun s => s.RIP = 0x103fad) (cmpR64R64Effect 0x103fad 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[56, 6]
    (.letOp (n := 60) (.pure (condOp 3)) #v[58]
    (.terminate (.condBr (Fin.last 60) ⟨.l103ffa, RegMap.args [(0, 56), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩ ⟨.l103fb2, RegMap.args [(0, 56), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩)))))))))

def bytes_l103f9f : List UInt8 :=
  [0x0F, 0xB7, 0x44, 0x57, 0x06, 0x66, 0x89, 0x44, 0x57, 0x16, 0x48, 0x8D, 0x42, 0x02, 0x48, 0x39,
    0xF0, 0x73, 0x48]

theorem code_l103f9f : ∀ x ∈ codeRange 0x103f9f bytes_l103f9f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3f9f 19 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103fb2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103fb2 (movzxR32M16Effect 0x103fb2 5 0 (.sib 7 (some 2) 1 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 2] []) (.reg (.gpr 0))) #v[7, 2]
    (.letOp (n := 54) (.exec 0x103fb2 (LoadPre 0x103fb2 (fun s => AddrMode.addr (.sib 7 (some 2) 1 (.d8 0x4)) s (0x103fb2 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x103fb2 5 0 (.sib 7 (some 2) 1 (.d8 0x4))) (Reg.operands [.gpr 7, .gpr 2] [])) #v[7, 2]
    (.letOp (n := 55) (.exec 0x103fb7 (StorePre 0x103fb7 5 (fun s => AddrMode.addr (.sib 7 (some 2) 1 (.d8 0x14)) s (0x103fb7 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x103fb7 5 0 (.sib 7 (some 2) 1 (.d8 0x14))) (Reg.operands [.gpr 0, .gpr 7, .gpr 2] [])) #v[53, 7, 2]
    (.letOp (n := 56) (.out 0x103fbc (leaR64Effect 0x103fbc 0 (.base 2 (.d8 0x1))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 57) (.exec 0x103fbc (fun s => s.RIP = 0x103fbc) (leaR64Effect 0x103fbc 0 (.base 2 (.d8 0x1))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 58) (.out 0x103fc0 (cmpR64R64Effect 0x103fc0 0 6) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 6] []) (.flag .CF)) #v[56, 6]
    (.letOp (n := 59) (.exec 0x103fc0 (fun s => s.RIP = 0x103fc0) (cmpR64R64Effect 0x103fc0 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[56, 6]
    (.letOp (n := 60) (.pure (condOp 3)) #v[58]
    (.terminate (.condBr (Fin.last 60) ⟨.l103ffa, RegMap.args [(0, 56), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩ ⟨.l103fc5, RegMap.args [(0, 56), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩)))))))))

def bytes_l103fb2 : List UInt8 :=
  [0x0F, 0xB7, 0x44, 0x57, 0x04, 0x66, 0x89, 0x44, 0x57, 0x14, 0x48, 0x8D, 0x42, 0x01, 0x48, 0x39,
    0xF0, 0x73, 0x35]

theorem code_l103fb2 : ∀ x ∈ codeRange 0x103fb2 bytes_l103fb2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3fb2 19 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103fc5 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103fc5 (movzxR32M16Effect 0x103fc5 5 0 (.sib 7 (some 2) 1 (.d8 0x2))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 2] []) (.reg (.gpr 0))) #v[7, 2]
    (.letOp (n := 54) (.exec 0x103fc5 (LoadPre 0x103fc5 (fun s => AddrMode.addr (.sib 7 (some 2) 1 (.d8 0x2)) s (0x103fc5 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x103fc5 5 0 (.sib 7 (some 2) 1 (.d8 0x2))) (Reg.operands [.gpr 7, .gpr 2] [])) #v[7, 2]
    (.letOp (n := 55) (.exec 0x103fca (StorePre 0x103fca 5 (fun s => AddrMode.addr (.sib 7 (some 2) 1 (.d8 0x12)) s (0x103fca + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x103fca 5 0 (.sib 7 (some 2) 1 (.d8 0x12))) (Reg.operands [.gpr 0, .gpr 7, .gpr 2] [])) #v[53, 7, 2]
    (.letOp (n := 56) (.out 0x103fcf (cmpR64R64Effect 0x103fcf 2 6) (EffectPart.reads (.flag .CF) [.gpr 2, .gpr 6] []) (.flag .CF)) #v[2, 6]
    (.letOp (n := 57) (.exec 0x103fcf (fun s => s.RIP = 0x103fcf) (cmpR64R64Effect 0x103fcf 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[2, 6]
    (.letOp (n := 58) (.pure (condOp 3)) #v[56]
    (.terminate (.condBr (Fin.last 58) ⟨.l103ff7, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩ ⟨.l103fd4, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l103fc5 : List UInt8 :=
  [0x0F, 0xB7, 0x44, 0x57, 0x02, 0x66, 0x89, 0x44, 0x57, 0x12, 0x48, 0x39, 0xF2, 0x73, 0x23]

theorem code_l103fc5 : ∀ x ∈ codeRange 0x103fc5 bytes_l103fc5, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3fc5 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103fd4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103fd4 (leaR64Effect 0x103fd4 0 (.base 2 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 54) (.exec 0x103fd4 (fun s => s.RIP = 0x103fd4) (leaR64Effect 0x103fd4 0 (.base 2 (.d8 0x8))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 55) (.out 0x103fd8 (cmpR64R64Effect 0x103fd8 0 6) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 6] []) (.flag .CF)) #v[53, 6]
    (.letOp (n := 56) (.exec 0x103fd8 (fun s => s.RIP = 0x103fd8) (cmpR64R64Effect 0x103fd8 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[53, 6]
    (.letOp (n := 57) (.pure (condOp 3)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l103fe8, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l103fdd, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l103fd4 : List UInt8 :=
  [0x48, 0x8D, 0x42, 0x08, 0x48, 0x39, 0xF0, 0x73, 0x0B]

theorem code_l103fd4 : ∀ x ∈ codeRange 0x103fd4 bytes_l103fd4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3fd4 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103fdd : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103fdd (movzxR32M16Effect 0x103fdd 4 0 (.sib 7 (some 2) 1 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 2] []) (.reg (.gpr 0))) #v[7, 2]
    (.letOp (n := 54) (.exec 0x103fdd (LoadPre 0x103fdd (fun s => AddrMode.addr (.sib 7 (some 2) 1 .none) s (0x103fdd + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x103fdd 4 0 (.sib 7 (some 2) 1 .none)) (Reg.operands [.gpr 7, .gpr 2] [])) #v[7, 2]
    (.letOp (n := 55) (.exec 0x103fe1 (StorePre 0x103fe1 5 (fun s => AddrMode.addr (.sib 7 (some 2) 1 (.d8 0x10)) s (0x103fe1 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x103fe1 5 0 (.sib 7 (some 2) 1 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 7, .gpr 2] [])) #v[53, 7, 2]
    (.letOp (n := 56) (.out 0x103fe6 (popR64Effect 0x103fe6 1 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.out 0x103fe6 (popR64Effect 0x103fe6 1 0) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x103fe6 (PopPre 0x103fe6) (popR64Effect 0x103fe6 1 0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x103fe7 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[57]
    (.letOp (n := 60) (.out 0x103fe7 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[57]
    (.letOp (n := 61) (.exec 0x103fe7 (RetPre 0x103fe7) (retEffect) (Reg.operands [.gpr 4] [])) #v[57]
    (.terminate (.ret (RegMap.args [(0, 56), (1, 1), (2, 2), (3, 3), (4, 60), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62) (some ⟨59, by decide⟩)))))))))))

def bytes_l103fdd : List UInt8 :=
  [0x0F, 0xB7, 0x04, 0x57, 0x66, 0x89, 0x44, 0x57, 0x10, 0x58, 0xC3]

theorem code_l103fdd : ∀ x ∈ codeRange 0x103fdd bytes_l103fdd, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3fdd 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103fe8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103fe8 (movR64R64Effect 0x103fe8 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[0]
    (.letOp (n := 54) (.exec 0x103fe8 (fun s => s.RIP = 0x103fe8) (movR64R64Effect 0x103fe8 7 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x103feb (movR64Imm32Effect 0x103feb 2 0x201010) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 56) (.exec 0x103feb (fun s => s.RIP = 0x103feb) (movR64Imm32Effect 0x103feb 2 0x201010) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x103ff2 (callEffect (fun _ => 0x103837) 0x103ff7) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x103ff2 (PushPre 0x103ff2 5) (callEffect (fun _ => 0x103837) 0x103ff7) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x103ff7⟩) #v[]
    (.terminate (.call ⟨.l103837, RegMap.args [(0, 0), (2, 55), (4, 57), (5, 5), (6, 6), (7, 53)] 60⟩ { target := .l103ff7, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l103fe8 : List UInt8 :=
  [0x48, 0x89, 0xC7, 0x48, 0xC7, 0xC2, 0x10, 0x10, 0x20, 0x00, 0xE8, 0x40, 0xF8, 0xFF, 0xFF]

theorem code_l103fe8 : ∀ x ∈ codeRange 0x103fe8 bytes_l103fe8, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3fe8 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103ff7 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103ff7 (movR64R64Effect 0x103ff7 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 54) (.exec 0x103ff7 (fun s => s.RIP = 0x103ff7) (movR64R64Effect 0x103ff7 0 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.terminate (.br ⟨.l103ffa, RegMap.args [(0, 53), (2, 2), (4, 4), (5, 5), (6, 6)] 55⟩)))

def bytes_l103ff7 : List UInt8 :=
  [0x48, 0x89, 0xD0]

theorem code_l103ff7 : ∀ x ∈ codeRange 0x103ff7 bytes_l103ff7, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3ff7 3 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103ffa : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103ffa (movR64R64Effect 0x103ffa 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[0]
    (.letOp (n := 54) (.exec 0x103ffa (fun s => s.RIP = 0x103ffa) (movR64R64Effect 0x103ffa 7 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x103ffd (movR64Imm32Effect 0x103ffd 2 0x200ff8) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 56) (.exec 0x103ffd (fun s => s.RIP = 0x103ffd) (movR64Imm32Effect 0x103ffd 2 0x200ff8) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x104004 (callEffect (fun _ => 0x103837) 0x104009) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x104004 (PushPre 0x104004 5) (callEffect (fun _ => 0x103837) 0x104009) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x104009⟩) #v[]
    (.terminate (.call ⟨.l103837, RegMap.args [(0, 0), (2, 55), (4, 57), (5, 5), (6, 6), (7, 53)] 60⟩ { target := .l104009, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l103ffa : List UInt8 :=
  [0x48, 0x89, 0xC7, 0x48, 0xC7, 0xC2, 0xF8, 0x0F, 0x20, 0x00, 0xE8, 0x2E, 0xF8, 0xFF, 0xFF]

theorem code_l103ffa : ∀ x ∈ codeRange 0x103ffa bytes_l103ffa, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3ffa 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104009 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x104009 (fun s => s.RIP = 0x104009) (fun _ => nopEffect 0x104009 7) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l104010, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 54⟩))

def bytes_l104009 : List UInt8 :=
  [0x0F, 0x1F, 0x80, 0x00, 0x00, 0x00, 0x00]

theorem code_l104009 : ∀ x ∈ codeRange 0x104009 bytes_l104009, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4009 7 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104010 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x104010 (pushR64Effect 0x104010 1 0) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 0] []) (.reg (.gpr 4))) #v[4, 0]
    (.letOp (n := 54) (.exec 0x104010 (PushPre 0x104010 1) (pushR64Effect 0x104010 1 0) (Reg.operands [.gpr 4, .gpr 0] [])) #v[4, 0]
    (.letOp (n := 55) (.out 0x104011 (movR64R64Effect 0x104011 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[2]
    (.letOp (n := 56) (.exec 0x104011 (fun s => s.RIP = 0x104011) (movR64R64Effect 0x104011 9 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 57) (.out 0x104014 (subR64R64Effect 0x104014 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1] []) (.reg (.gpr 9))) #v[55, 1]
    (.letOp (n := 58) (.exec 0x104014 (fun s => s.RIP = 0x104014) (subR64R64Effect 0x104014 9 1) (Reg.operands [.gpr 9, .gpr 1] [])) #v[55, 1]
    (.letOp (n := 59) (.out 0x104017 (cmpR64R64Effect 0x104017 9 6) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 6] []) (.flag .CF)) #v[57, 6]
    (.letOp (n := 60) (.exec 0x104017 (fun s => s.RIP = 0x104017) (cmpR64R64Effect 0x104017 9 6) (Reg.operands [.gpr 9, .gpr 6] [])) #v[57, 6]
    (.letOp (n := 61) (.pure (condOp 3)) #v[59]
    (.terminate (.condBr (Fin.last 61) ⟨.l10434d, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ ⟨.l104020, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩))))))))))

def bytes_l104010 : List UInt8 :=
  [0x50, 0x49, 0x89, 0xD1, 0x49, 0x29, 0xC9, 0x49, 0x39, 0xF1, 0x0F, 0x83, 0x2D, 0x03, 0x00, 0x00]

theorem code_l104010 : ∀ x ∈ codeRange 0x104010 bytes_l104010, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4010 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104020 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x104020 (cmpR64R64Effect 0x104020 2 6) (EffectPart.reads (.flag .CF) [.gpr 2, .gpr 6] []) (.flag .CF)) #v[2, 6]
    (.letOp (n := 54) (.exec 0x104020 (fun s => s.RIP = 0x104020) (cmpR64R64Effect 0x104020 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[2, 6]
    (.letOp (n := 55) (.pure (condOp 3)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l10435c, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l104029, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l104020 : List UInt8 :=
  [0x48, 0x39, 0xF2, 0x0F, 0x83, 0x33, 0x03, 0x00, 0x00]

theorem code_l104020 : ∀ x ∈ codeRange 0x104020 bytes_l104020, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4020 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104029_1 : Block Op Label signature Reg.count 92 :=
  .letOp (n := 92) (.pure (condOp 3)) #v[90]
    (.terminate (.condBr (Fin.last 92) ⟨.l10434d, RegMap.args [(0, 53), (1, 84), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 88), (10, 63), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 90), (22, 22), (39, 39), (50, 50), (51, 51)] 93⟩ ⟨.l10408b, RegMap.args [(0, 53), (1, 84), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 88), (10, 63), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 90), (22, 22), (39, 39), (50, 50), (51, 51)] 93⟩))

def bytes_l104029_1 : List UInt8 :=
  [0x0F, 0x83, 0xC2, 0x02, 0x00, 0x00]

theorem code_l104029_1 : ∀ x ∈ codeRange 0x104085 bytes_l104029_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4085 6 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104029 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x104029 (movR64R64Effect 0x104029 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[1]
    (.letOp (n := 54) (.exec 0x104029 (fun s => s.RIP = 0x104029) (movR64R64Effect 0x104029 0 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 55) (.out 0x10402c (movzxR32M16Effect 0x10402c 5 10 (.sib 7 (some 2) 1 .none)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 7, .gpr 2] []) (.reg (.gpr 10))) #v[7, 2]
    (.letOp (n := 56) (.exec 0x10402c (LoadPre 0x10402c (fun s => AddrMode.addr (.sib 7 (some 2) 1 .none) s (0x10402c + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x10402c 5 10 (.sib 7 (some 2) 1 .none)) (Reg.operands [.gpr 7, .gpr 2] [])) #v[7, 2]
    (.letOp (n := 57) (.out 0x104031 (movR32R32Effect 0x104031 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 8] []) (.reg (.gpr 1))) #v[8]
    (.letOp (n := 58) (.exec 0x104031 (fun s => s.RIP = 0x104031) (movR32R32Effect 0x104031 3 1 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 59) (.out 0x104034 (rorR16ClEffect 0x104034 4 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[55, 57]
    (.letOp (n := 60) (.exec 0x104034 (fun s => s.RIP = 0x104034) (rorR16ClEffect 0x104034 4 10) (Reg.operands [.gpr 10, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[55, 57]
    (.letOp (n := 61) (.out 0x104038 (andR32Imm32Effect 0x104038 7 10 0x1111) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[59]
    (.letOp (n := 62) (.exec 0x104038 (fun s => s.RIP = 0x104038) (andR32Imm32Effect 0x104038 7 10 0x1111) (Reg.operands [.gpr 10] [])) #v[59]
    (.letOp (n := 63) (.out 0x10403f (xorR16M16Effect 0x10403f 5 10 (.sib 7 (some 9) 1 .none)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 7, .gpr 9] []) (.reg (.gpr 10))) #v[61, 7, 9]
    (.letOp (n := 64) (.exec 0x10403f (LoadPre 0x10403f (fun s => AddrMode.addr (.sib 7 (some 9) 1 .none) s (0x10403f + BitVec.ofNat 64 5)) 2) (xorR16M16Effect 0x10403f 5 10 (.sib 7 (some 9) 1 .none)) (Reg.operands [.gpr 10, .gpr 7, .gpr 9] [])) #v[61, 7, 9]
    (.letOp (n := 65) (.out 0x104044 (leaR32Effect 0x104044 4 1 (.sib 10 (some 10) 0 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 10, .gpr 10] []) (.reg (.gpr 1))) #v[63, 63]
    (.letOp (n := 66) (.exec 0x104044 (fun s => s.RIP = 0x104044) (leaR32Effect 0x104044 4 1 (.sib 10 (some 10) 0 .none)) (Reg.operands [.gpr 10, .gpr 10] [])) #v[63, 63]
    (.letOp (n := 67) (.out 0x104048 (andR32Imm32Effect 0x104048 6 1 0xffffeeee) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 68) (.exec 0x104048 (fun s => s.RIP = 0x104048) (andR32Imm32Effect 0x104048 6 1 0xffffeeee) (Reg.operands [.gpr 1] [])) #v[65]
    (.letOp (n := 69) (.out 0x10404e (leaR32Effect 0x10404e 8 9 (.abs (some 10) 2 0x0)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 10] []) (.reg (.gpr 9))) #v[63]
    (.letOp (n := 70) (.exec 0x10404e (fun s => s.RIP = 0x10404e) (leaR32Effect 0x10404e 8 9 (.abs (some 10) 2 0x0)) (Reg.operands [.gpr 10] [])) #v[63]
    (.letOp (n := 71) (.out 0x104056 (andR32Imm32Effect 0x104056 7 9 0xffffcccc) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[69]
    (.letOp (n := 72) (.exec 0x104056 (fun s => s.RIP = 0x104056) (andR32Imm32Effect 0x104056 7 9 0xffffcccc) (Reg.operands [.gpr 9] [])) #v[69]
    (.letOp (n := 73) (.out 0x10405d (xorR32R32Effect 0x10405d 3 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1] []) (.reg (.gpr 9))) #v[71, 67]
    (.letOp (n := 74) (.exec 0x10405d (fun s => s.RIP = 0x10405d) (xorR32R32Effect 0x10405d 3 9 1) (Reg.operands [.gpr 9, .gpr 1] [])) #v[71, 67]
    (.letOp (n := 75) (.out 0x104060 (leaR32Effect 0x104060 8 1 (.abs (some 10) 3 0x0)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 10] []) (.reg (.gpr 1))) #v[63]
    (.letOp (n := 76) (.exec 0x104060 (fun s => s.RIP = 0x104060) (leaR32Effect 0x104060 8 1 (.abs (some 10) 3 0x0)) (Reg.operands [.gpr 10] [])) #v[63]
    (.letOp (n := 77) (.out 0x104068 (andR32Imm32Effect 0x104068 6 1 0xffff8888) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[75]
    (.letOp (n := 78) (.exec 0x104068 (fun s => s.RIP = 0x104068) (andR32Imm32Effect 0x104068 6 1 0xffff8888) (Reg.operands [.gpr 1] [])) #v[75]
    (.letOp (n := 79) (.out 0x10406e (xorR32R32Effect 0x10406e 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10] []) (.reg (.gpr 1))) #v[77, 63]
    (.letOp (n := 80) (.exec 0x10406e (fun s => s.RIP = 0x10406e) (xorR32R32Effect 0x10406e 3 1 10) (Reg.operands [.gpr 1, .gpr 10] [])) #v[77, 63]
    (.letOp (n := 81) (.out 0x104071 (xorR32R32Effect 0x104071 3 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 9] []) (.reg (.gpr 1))) #v[79, 73]
    (.letOp (n := 82) (.exec 0x104071 (fun s => s.RIP = 0x104071) (xorR32R32Effect 0x104071 3 1 9) (Reg.operands [.gpr 1, .gpr 9] [])) #v[79, 73]
    (.letOp (n := 83) (.exec 0x104074 (StorePre 0x104074 4 (fun s => AddrMode.addr (.sib 7 (some 2) 1 .none) s (0x104074 + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x104074 4 1 (.sib 7 (some 2) 1 .none)) (Reg.operands [.gpr 1, .gpr 7, .gpr 2] [])) #v[81, 7, 2]
    (.letOp (n := 84) (.out 0x104078 (leaR64Effect 0x104078 1 (.base 2 (.d8 0x1))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2]
    (.letOp (n := 85) (.exec 0x104078 (fun s => s.RIP = 0x104078) (leaR64Effect 0x104078 1 (.base 2 (.d8 0x1))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 86) (.out 0x10407c (movR64R64Effect 0x10407c 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 1] []) (.reg (.gpr 9))) #v[84]
    (.letOp (n := 87) (.exec 0x10407c (fun s => s.RIP = 0x10407c) (movR64R64Effect 0x10407c 9 1) (Reg.operands [.gpr 1] [])) #v[84]
    (.letOp (n := 88) (.out 0x10407f (subR64R64Effect 0x10407f 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0] []) (.reg (.gpr 9))) #v[86, 53]
    (.letOp (n := 89) (.exec 0x10407f (fun s => s.RIP = 0x10407f) (subR64R64Effect 0x10407f 9 0) (Reg.operands [.gpr 9, .gpr 0] [])) #v[86, 53]
    (.letOp (n := 90) (.out 0x104082 (cmpR64R64Effect 0x104082 9 6) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 6] []) (.flag .CF)) #v[88, 6]
    (.letOp (n := 91) (.exec 0x104082 (fun s => s.RIP = 0x104082) (cmpR64R64Effect 0x104082 9 6) (Reg.operands [.gpr 9, .gpr 6] [])) #v[88, 6]
    (b_l104029_1)))))))))))))))))))))))))))))))))))))))

def bytes_l104029 : List UInt8 :=
  [0x48, 0x89, 0xC8, 0x44, 0x0F, 0xB7, 0x14, 0x57, 0x44, 0x89, 0xC1, 0x66, 0x41, 0xD3, 0xCA, 0x41,
    0x81, 0xE2, 0x11, 0x11, 0x00, 0x00, 0x66, 0x46, 0x33, 0x14, 0x4F, 0x43, 0x8D, 0x0C, 0x12, 0x81,
    0xE1, 0xEE, 0xEE, 0xFF, 0xFF, 0x46, 0x8D, 0x0C, 0x95, 0x00, 0x00, 0x00, 0x00, 0x41, 0x81, 0xE1,
    0xCC, 0xCC, 0xFF, 0xFF, 0x41, 0x31, 0xC9, 0x42, 0x8D, 0x0C, 0xD5, 0x00, 0x00, 0x00, 0x00, 0x81,
    0xE1, 0x88, 0x88, 0xFF, 0xFF, 0x44, 0x31, 0xD1, 0x44, 0x31, 0xC9, 0x66, 0x89, 0x0C, 0x57, 0x48,
    0x8D, 0x4A, 0x01, 0x49, 0x89, 0xC9, 0x49, 0x29, 0xC1, 0x49, 0x39, 0xF1] ++ bytes_l104029_1

theorem code_l104029 : ∀ x ∈ codeRange 0x104029 bytes_l104029, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x4029 92 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l104029_1

@[cfg_block] def b_l10408b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10408b (cmpR64R64Effect 0x10408b 1 6) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 6] []) (.flag .CF)) #v[1, 6]
    (.letOp (n := 54) (.exec 0x10408b (fun s => s.RIP = 0x10408b) (cmpR64R64Effect 0x10408b 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[1, 6]
    (.letOp (n := 55) (.pure (condOp 3)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l10435f, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l104094, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l10408b : List UInt8 :=
  [0x48, 0x39, 0xF1, 0x0F, 0x83, 0xCB, 0x02, 0x00, 0x00]

theorem code_l10408b : ∀ x ∈ codeRange 0x10408b bytes_l10408b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x408b 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104094 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x104094 (movzxR32M16Effect 0x104094 6 10 (.sib 7 (some 2) 1 (.d8 0x2))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 7, .gpr 2] []) (.reg (.gpr 10))) #v[7, 2]
    (.letOp (n := 54) (.exec 0x104094 (LoadPre 0x104094 (fun s => AddrMode.addr (.sib 7 (some 2) 1 (.d8 0x2)) s (0x104094 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x104094 6 10 (.sib 7 (some 2) 1 (.d8 0x2))) (Reg.operands [.gpr 7, .gpr 2] [])) #v[7, 2]
    (.letOp (n := 55) (.out 0x10409a (movR32R32Effect 0x10409a 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 8] []) (.reg (.gpr 1))) #v[8]
    (.letOp (n := 56) (.exec 0x10409a (fun s => s.RIP = 0x10409a) (movR32R32Effect 0x10409a 3 1 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 57) (.out 0x10409d (rorR16ClEffect 0x10409d 4 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[53, 55]
    (.letOp (n := 58) (.exec 0x10409d (fun s => s.RIP = 0x10409d) (rorR16ClEffect 0x10409d 4 10) (Reg.operands [.gpr 10, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53, 55]
    (.letOp (n := 59) (.out 0x1040a1 (andR32Imm32Effect 0x1040a1 7 10 0x1111) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[57]
    (.letOp (n := 60) (.exec 0x1040a1 (fun s => s.RIP = 0x1040a1) (andR32Imm32Effect 0x1040a1 7 10 0x1111) (Reg.operands [.gpr 10] [])) #v[57]
    (.letOp (n := 61) (.out 0x1040a8 (xorR16M16Effect 0x1040a8 5 10 (.sib 7 (some 9) 1 .none)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 7, .gpr 9] []) (.reg (.gpr 10))) #v[59, 7, 9]
    (.letOp (n := 62) (.exec 0x1040a8 (LoadPre 0x1040a8 (fun s => AddrMode.addr (.sib 7 (some 9) 1 .none) s (0x1040a8 + BitVec.ofNat 64 5)) 2) (xorR16M16Effect 0x1040a8 5 10 (.sib 7 (some 9) 1 .none)) (Reg.operands [.gpr 10, .gpr 7, .gpr 9] [])) #v[59, 7, 9]
    (.letOp (n := 63) (.out 0x1040ad (leaR32Effect 0x1040ad 4 1 (.sib 10 (some 10) 0 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 10, .gpr 10] []) (.reg (.gpr 1))) #v[61, 61]
    (.letOp (n := 64) (.exec 0x1040ad (fun s => s.RIP = 0x1040ad) (leaR32Effect 0x1040ad 4 1 (.sib 10 (some 10) 0 .none)) (Reg.operands [.gpr 10, .gpr 10] [])) #v[61, 61]
    (.letOp (n := 65) (.out 0x1040b1 (andR32Imm32Effect 0x1040b1 6 1 0xffffeeee) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[63]
    (.letOp (n := 66) (.exec 0x1040b1 (fun s => s.RIP = 0x1040b1) (andR32Imm32Effect 0x1040b1 6 1 0xffffeeee) (Reg.operands [.gpr 1] [])) #v[63]
    (.letOp (n := 67) (.out 0x1040b7 (leaR32Effect 0x1040b7 8 9 (.abs (some 10) 2 0x0)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 10] []) (.reg (.gpr 9))) #v[61]
    (.letOp (n := 68) (.exec 0x1040b7 (fun s => s.RIP = 0x1040b7) (leaR32Effect 0x1040b7 8 9 (.abs (some 10) 2 0x0)) (Reg.operands [.gpr 10] [])) #v[61]
    (.letOp (n := 69) (.out 0x1040bf (andR32Imm32Effect 0x1040bf 7 9 0xffffcccc) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[67]
    (.letOp (n := 70) (.exec 0x1040bf (fun s => s.RIP = 0x1040bf) (andR32Imm32Effect 0x1040bf 7 9 0xffffcccc) (Reg.operands [.gpr 9] [])) #v[67]
    (.letOp (n := 71) (.out 0x1040c6 (xorR32R32Effect 0x1040c6 3 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1] []) (.reg (.gpr 9))) #v[69, 65]
    (.letOp (n := 72) (.exec 0x1040c6 (fun s => s.RIP = 0x1040c6) (xorR32R32Effect 0x1040c6 3 9 1) (Reg.operands [.gpr 9, .gpr 1] [])) #v[69, 65]
    (.letOp (n := 73) (.out 0x1040c9 (leaR32Effect 0x1040c9 8 1 (.abs (some 10) 3 0x0)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 10] []) (.reg (.gpr 1))) #v[61]
    (.letOp (n := 74) (.exec 0x1040c9 (fun s => s.RIP = 0x1040c9) (leaR32Effect 0x1040c9 8 1 (.abs (some 10) 3 0x0)) (Reg.operands [.gpr 10] [])) #v[61]
    (.letOp (n := 75) (.out 0x1040d1 (andR32Imm32Effect 0x1040d1 6 1 0xffff8888) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[73]
    (.letOp (n := 76) (.exec 0x1040d1 (fun s => s.RIP = 0x1040d1) (andR32Imm32Effect 0x1040d1 6 1 0xffff8888) (Reg.operands [.gpr 1] [])) #v[73]
    (.letOp (n := 77) (.out 0x1040d7 (xorR32R32Effect 0x1040d7 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10] []) (.reg (.gpr 1))) #v[75, 61]
    (.letOp (n := 78) (.exec 0x1040d7 (fun s => s.RIP = 0x1040d7) (xorR32R32Effect 0x1040d7 3 1 10) (Reg.operands [.gpr 1, .gpr 10] [])) #v[75, 61]
    (.letOp (n := 79) (.out 0x1040da (xorR32R32Effect 0x1040da 3 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 9] []) (.reg (.gpr 1))) #v[77, 71]
    (.letOp (n := 80) (.exec 0x1040da (fun s => s.RIP = 0x1040da) (xorR32R32Effect 0x1040da 3 1 9) (Reg.operands [.gpr 1, .gpr 9] [])) #v[77, 71]
    (.letOp (n := 81) (.exec 0x1040dd (StorePre 0x1040dd 5 (fun s => AddrMode.addr (.sib 7 (some 2) 1 (.d8 0x2)) s (0x1040dd + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1040dd 5 1 (.sib 7 (some 2) 1 (.d8 0x2))) (Reg.operands [.gpr 1, .gpr 7, .gpr 2] [])) #v[79, 7, 2]
    (.letOp (n := 82) (.out 0x1040e2 (leaR64Effect 0x1040e2 1 (.base 2 (.d8 0x2))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2]
    (.letOp (n := 83) (.exec 0x1040e2 (fun s => s.RIP = 0x1040e2) (leaR64Effect 0x1040e2 1 (.base 2 (.d8 0x2))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 84) (.out 0x1040e6 (movR64R64Effect 0x1040e6 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 1] []) (.reg (.gpr 9))) #v[82]
    (.letOp (n := 85) (.exec 0x1040e6 (fun s => s.RIP = 0x1040e6) (movR64R64Effect 0x1040e6 9 1) (Reg.operands [.gpr 1] [])) #v[82]
    (.letOp (n := 86) (.out 0x1040e9 (subR64R64Effect 0x1040e9 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0] []) (.reg (.gpr 9))) #v[84, 0]
    (.letOp (n := 87) (.exec 0x1040e9 (fun s => s.RIP = 0x1040e9) (subR64R64Effect 0x1040e9 9 0) (Reg.operands [.gpr 9, .gpr 0] [])) #v[84, 0]
    (.letOp (n := 88) (.out 0x1040ec (cmpR64R64Effect 0x1040ec 9 6) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 6] []) (.flag .CF)) #v[86, 6]
    (.letOp (n := 89) (.exec 0x1040ec (fun s => s.RIP = 0x1040ec) (cmpR64R64Effect 0x1040ec 9 6) (Reg.operands [.gpr 9, .gpr 6] [])) #v[86, 6]
    (.letOp (n := 90) (.pure (condOp 3)) #v[88]
    (.terminate (.condBr (Fin.last 90) ⟨.l10434d, RegMap.args [(0, 0), (1, 82), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 86), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 88), (22, 22), (39, 39), (50, 50), (51, 51)] 91⟩ ⟨.l1040f5, RegMap.args [(0, 0), (1, 82), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 86), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 88), (22, 22), (39, 39), (50, 50), (51, 51)] 91⟩)))))))))))))))))))))))))))))))))))))))

def bytes_l104094 : List UInt8 :=
  [0x44, 0x0F, 0xB7, 0x54, 0x57, 0x02, 0x44, 0x89, 0xC1, 0x66, 0x41, 0xD3, 0xCA, 0x41, 0x81, 0xE2,
    0x11, 0x11, 0x00, 0x00, 0x66, 0x46, 0x33, 0x14, 0x4F, 0x43, 0x8D, 0x0C, 0x12, 0x81, 0xE1, 0xEE,
    0xEE, 0xFF, 0xFF, 0x46, 0x8D, 0x0C, 0x95, 0x00, 0x00, 0x00, 0x00, 0x41, 0x81, 0xE1, 0xCC, 0xCC,
    0xFF, 0xFF, 0x41, 0x31, 0xC9, 0x42, 0x8D, 0x0C, 0xD5, 0x00, 0x00, 0x00, 0x00, 0x81, 0xE1, 0x88,
    0x88, 0xFF, 0xFF, 0x44, 0x31, 0xD1, 0x44, 0x31, 0xC9, 0x66, 0x89, 0x4C, 0x57, 0x02, 0x48, 0x8D,
    0x4A, 0x02, 0x49, 0x89, 0xC9, 0x49, 0x29, 0xC1, 0x49, 0x39, 0xF1, 0x0F, 0x83, 0x58, 0x02, 0x00,
    0x00]

theorem code_l104094 : ∀ x ∈ codeRange 0x104094 bytes_l104094, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4094 97 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1040f5 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1040f5 (cmpR64R64Effect 0x1040f5 1 6) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 6] []) (.flag .CF)) #v[1, 6]
    (.letOp (n := 54) (.exec 0x1040f5 (fun s => s.RIP = 0x1040f5) (cmpR64R64Effect 0x1040f5 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[1, 6]
    (.letOp (n := 55) (.pure (condOp 3)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l10435f, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l1040fe, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l1040f5 : List UInt8 :=
  [0x48, 0x39, 0xF1, 0x0F, 0x83, 0x61, 0x02, 0x00, 0x00]

theorem code_l1040f5 : ∀ x ∈ codeRange 0x1040f5 bytes_l1040f5, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x40f5 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1040fe : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1040fe (movzxR32M16Effect 0x1040fe 6 10 (.sib 7 (some 2) 1 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 7, .gpr 2] []) (.reg (.gpr 10))) #v[7, 2]
    (.letOp (n := 54) (.exec 0x1040fe (LoadPre 0x1040fe (fun s => AddrMode.addr (.sib 7 (some 2) 1 (.d8 0x4)) s (0x1040fe + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x1040fe 6 10 (.sib 7 (some 2) 1 (.d8 0x4))) (Reg.operands [.gpr 7, .gpr 2] [])) #v[7, 2]
    (.letOp (n := 55) (.out 0x104104 (movR32R32Effect 0x104104 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 8] []) (.reg (.gpr 1))) #v[8]
    (.letOp (n := 56) (.exec 0x104104 (fun s => s.RIP = 0x104104) (movR32R32Effect 0x104104 3 1 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 57) (.out 0x104107 (rorR16ClEffect 0x104107 4 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[53, 55]
    (.letOp (n := 58) (.exec 0x104107 (fun s => s.RIP = 0x104107) (rorR16ClEffect 0x104107 4 10) (Reg.operands [.gpr 10, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53, 55]
    (.letOp (n := 59) (.out 0x10410b (andR32Imm32Effect 0x10410b 7 10 0x1111) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[57]
    (.letOp (n := 60) (.exec 0x10410b (fun s => s.RIP = 0x10410b) (andR32Imm32Effect 0x10410b 7 10 0x1111) (Reg.operands [.gpr 10] [])) #v[57]
    (.letOp (n := 61) (.out 0x104112 (xorR16M16Effect 0x104112 5 10 (.sib 7 (some 9) 1 .none)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 7, .gpr 9] []) (.reg (.gpr 10))) #v[59, 7, 9]
    (.letOp (n := 62) (.exec 0x104112 (LoadPre 0x104112 (fun s => AddrMode.addr (.sib 7 (some 9) 1 .none) s (0x104112 + BitVec.ofNat 64 5)) 2) (xorR16M16Effect 0x104112 5 10 (.sib 7 (some 9) 1 .none)) (Reg.operands [.gpr 10, .gpr 7, .gpr 9] [])) #v[59, 7, 9]
    (.letOp (n := 63) (.out 0x104117 (leaR32Effect 0x104117 4 1 (.sib 10 (some 10) 0 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 10, .gpr 10] []) (.reg (.gpr 1))) #v[61, 61]
    (.letOp (n := 64) (.exec 0x104117 (fun s => s.RIP = 0x104117) (leaR32Effect 0x104117 4 1 (.sib 10 (some 10) 0 .none)) (Reg.operands [.gpr 10, .gpr 10] [])) #v[61, 61]
    (.letOp (n := 65) (.out 0x10411b (andR32Imm32Effect 0x10411b 6 1 0xffffeeee) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[63]
    (.letOp (n := 66) (.exec 0x10411b (fun s => s.RIP = 0x10411b) (andR32Imm32Effect 0x10411b 6 1 0xffffeeee) (Reg.operands [.gpr 1] [])) #v[63]
    (.letOp (n := 67) (.out 0x104121 (leaR32Effect 0x104121 8 9 (.abs (some 10) 2 0x0)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 10] []) (.reg (.gpr 9))) #v[61]
    (.letOp (n := 68) (.exec 0x104121 (fun s => s.RIP = 0x104121) (leaR32Effect 0x104121 8 9 (.abs (some 10) 2 0x0)) (Reg.operands [.gpr 10] [])) #v[61]
    (.letOp (n := 69) (.out 0x104129 (andR32Imm32Effect 0x104129 7 9 0xffffcccc) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[67]
    (.letOp (n := 70) (.exec 0x104129 (fun s => s.RIP = 0x104129) (andR32Imm32Effect 0x104129 7 9 0xffffcccc) (Reg.operands [.gpr 9] [])) #v[67]
    (.letOp (n := 71) (.out 0x104130 (xorR32R32Effect 0x104130 3 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1] []) (.reg (.gpr 9))) #v[69, 65]
    (.letOp (n := 72) (.exec 0x104130 (fun s => s.RIP = 0x104130) (xorR32R32Effect 0x104130 3 9 1) (Reg.operands [.gpr 9, .gpr 1] [])) #v[69, 65]
    (.letOp (n := 73) (.out 0x104133 (leaR32Effect 0x104133 8 1 (.abs (some 10) 3 0x0)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 10] []) (.reg (.gpr 1))) #v[61]
    (.letOp (n := 74) (.exec 0x104133 (fun s => s.RIP = 0x104133) (leaR32Effect 0x104133 8 1 (.abs (some 10) 3 0x0)) (Reg.operands [.gpr 10] [])) #v[61]
    (.letOp (n := 75) (.out 0x10413b (andR32Imm32Effect 0x10413b 6 1 0xffff8888) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[73]
    (.letOp (n := 76) (.exec 0x10413b (fun s => s.RIP = 0x10413b) (andR32Imm32Effect 0x10413b 6 1 0xffff8888) (Reg.operands [.gpr 1] [])) #v[73]
    (.letOp (n := 77) (.out 0x104141 (xorR32R32Effect 0x104141 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10] []) (.reg (.gpr 1))) #v[75, 61]
    (.letOp (n := 78) (.exec 0x104141 (fun s => s.RIP = 0x104141) (xorR32R32Effect 0x104141 3 1 10) (Reg.operands [.gpr 1, .gpr 10] [])) #v[75, 61]
    (.letOp (n := 79) (.out 0x104144 (xorR32R32Effect 0x104144 3 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 9] []) (.reg (.gpr 1))) #v[77, 71]
    (.letOp (n := 80) (.exec 0x104144 (fun s => s.RIP = 0x104144) (xorR32R32Effect 0x104144 3 1 9) (Reg.operands [.gpr 1, .gpr 9] [])) #v[77, 71]
    (.letOp (n := 81) (.exec 0x104147 (StorePre 0x104147 5 (fun s => AddrMode.addr (.sib 7 (some 2) 1 (.d8 0x4)) s (0x104147 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x104147 5 1 (.sib 7 (some 2) 1 (.d8 0x4))) (Reg.operands [.gpr 1, .gpr 7, .gpr 2] [])) #v[79, 7, 2]
    (.letOp (n := 82) (.out 0x10414c (leaR64Effect 0x10414c 1 (.base 2 (.d8 0x3))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2]
    (.letOp (n := 83) (.exec 0x10414c (fun s => s.RIP = 0x10414c) (leaR64Effect 0x10414c 1 (.base 2 (.d8 0x3))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 84) (.out 0x104150 (movR64R64Effect 0x104150 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 1] []) (.reg (.gpr 9))) #v[82]
    (.letOp (n := 85) (.exec 0x104150 (fun s => s.RIP = 0x104150) (movR64R64Effect 0x104150 9 1) (Reg.operands [.gpr 1] [])) #v[82]
    (.letOp (n := 86) (.out 0x104153 (subR64R64Effect 0x104153 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0] []) (.reg (.gpr 9))) #v[84, 0]
    (.letOp (n := 87) (.exec 0x104153 (fun s => s.RIP = 0x104153) (subR64R64Effect 0x104153 9 0) (Reg.operands [.gpr 9, .gpr 0] [])) #v[84, 0]
    (.letOp (n := 88) (.out 0x104156 (cmpR64R64Effect 0x104156 9 6) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 6] []) (.flag .CF)) #v[86, 6]
    (.letOp (n := 89) (.exec 0x104156 (fun s => s.RIP = 0x104156) (cmpR64R64Effect 0x104156 9 6) (Reg.operands [.gpr 9, .gpr 6] [])) #v[86, 6]
    (.letOp (n := 90) (.pure (condOp 3)) #v[88]
    (.terminate (.condBr (Fin.last 90) ⟨.l10434d, RegMap.args [(0, 0), (1, 82), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 86), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 88), (22, 22), (39, 39), (50, 50), (51, 51)] 91⟩ ⟨.l10415f, RegMap.args [(0, 0), (1, 82), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 86), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 88), (22, 22), (39, 39), (50, 50), (51, 51)] 91⟩)))))))))))))))))))))))))))))))))))))))

def bytes_l1040fe : List UInt8 :=
  [0x44, 0x0F, 0xB7, 0x54, 0x57, 0x04, 0x44, 0x89, 0xC1, 0x66, 0x41, 0xD3, 0xCA, 0x41, 0x81, 0xE2,
    0x11, 0x11, 0x00, 0x00, 0x66, 0x46, 0x33, 0x14, 0x4F, 0x43, 0x8D, 0x0C, 0x12, 0x81, 0xE1, 0xEE,
    0xEE, 0xFF, 0xFF, 0x46, 0x8D, 0x0C, 0x95, 0x00, 0x00, 0x00, 0x00, 0x41, 0x81, 0xE1, 0xCC, 0xCC,
    0xFF, 0xFF, 0x41, 0x31, 0xC9, 0x42, 0x8D, 0x0C, 0xD5, 0x00, 0x00, 0x00, 0x00, 0x81, 0xE1, 0x88,
    0x88, 0xFF, 0xFF, 0x44, 0x31, 0xD1, 0x44, 0x31, 0xC9, 0x66, 0x89, 0x4C, 0x57, 0x04, 0x48, 0x8D,
    0x4A, 0x03, 0x49, 0x89, 0xC9, 0x49, 0x29, 0xC1, 0x49, 0x39, 0xF1, 0x0F, 0x83, 0xEE, 0x01, 0x00,
    0x00]

theorem code_l1040fe : ∀ x ∈ codeRange 0x1040fe bytes_l1040fe, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x40fe 97 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10415f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10415f (cmpR64R64Effect 0x10415f 1 6) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 6] []) (.flag .CF)) #v[1, 6]
    (.letOp (n := 54) (.exec 0x10415f (fun s => s.RIP = 0x10415f) (cmpR64R64Effect 0x10415f 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[1, 6]
    (.letOp (n := 55) (.pure (condOp 3)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l10435f, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l104168, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l10415f : List UInt8 :=
  [0x48, 0x39, 0xF1, 0x0F, 0x83, 0xF7, 0x01, 0x00, 0x00]

theorem code_l10415f : ∀ x ∈ codeRange 0x10415f bytes_l10415f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x415f 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104168 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x104168 (movzxR32M16Effect 0x104168 6 10 (.sib 7 (some 2) 1 (.d8 0x6))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 7, .gpr 2] []) (.reg (.gpr 10))) #v[7, 2]
    (.letOp (n := 54) (.exec 0x104168 (LoadPre 0x104168 (fun s => AddrMode.addr (.sib 7 (some 2) 1 (.d8 0x6)) s (0x104168 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x104168 6 10 (.sib 7 (some 2) 1 (.d8 0x6))) (Reg.operands [.gpr 7, .gpr 2] [])) #v[7, 2]
    (.letOp (n := 55) (.out 0x10416e (movR32R32Effect 0x10416e 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 8] []) (.reg (.gpr 1))) #v[8]
    (.letOp (n := 56) (.exec 0x10416e (fun s => s.RIP = 0x10416e) (movR32R32Effect 0x10416e 3 1 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 57) (.out 0x104171 (rorR16ClEffect 0x104171 4 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[53, 55]
    (.letOp (n := 58) (.exec 0x104171 (fun s => s.RIP = 0x104171) (rorR16ClEffect 0x104171 4 10) (Reg.operands [.gpr 10, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53, 55]
    (.letOp (n := 59) (.out 0x104175 (andR32Imm32Effect 0x104175 7 10 0x1111) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[57]
    (.letOp (n := 60) (.exec 0x104175 (fun s => s.RIP = 0x104175) (andR32Imm32Effect 0x104175 7 10 0x1111) (Reg.operands [.gpr 10] [])) #v[57]
    (.letOp (n := 61) (.out 0x10417c (xorR16M16Effect 0x10417c 5 10 (.sib 7 (some 9) 1 .none)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 7, .gpr 9] []) (.reg (.gpr 10))) #v[59, 7, 9]
    (.letOp (n := 62) (.exec 0x10417c (LoadPre 0x10417c (fun s => AddrMode.addr (.sib 7 (some 9) 1 .none) s (0x10417c + BitVec.ofNat 64 5)) 2) (xorR16M16Effect 0x10417c 5 10 (.sib 7 (some 9) 1 .none)) (Reg.operands [.gpr 10, .gpr 7, .gpr 9] [])) #v[59, 7, 9]
    (.letOp (n := 63) (.out 0x104181 (leaR32Effect 0x104181 4 1 (.sib 10 (some 10) 0 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 10, .gpr 10] []) (.reg (.gpr 1))) #v[61, 61]
    (.letOp (n := 64) (.exec 0x104181 (fun s => s.RIP = 0x104181) (leaR32Effect 0x104181 4 1 (.sib 10 (some 10) 0 .none)) (Reg.operands [.gpr 10, .gpr 10] [])) #v[61, 61]
    (.letOp (n := 65) (.out 0x104185 (andR32Imm32Effect 0x104185 6 1 0xffffeeee) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[63]
    (.letOp (n := 66) (.exec 0x104185 (fun s => s.RIP = 0x104185) (andR32Imm32Effect 0x104185 6 1 0xffffeeee) (Reg.operands [.gpr 1] [])) #v[63]
    (.letOp (n := 67) (.out 0x10418b (leaR32Effect 0x10418b 8 9 (.abs (some 10) 2 0x0)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 10] []) (.reg (.gpr 9))) #v[61]
    (.letOp (n := 68) (.exec 0x10418b (fun s => s.RIP = 0x10418b) (leaR32Effect 0x10418b 8 9 (.abs (some 10) 2 0x0)) (Reg.operands [.gpr 10] [])) #v[61]
    (.letOp (n := 69) (.out 0x104193 (andR32Imm32Effect 0x104193 7 9 0xffffcccc) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[67]
    (.letOp (n := 70) (.exec 0x104193 (fun s => s.RIP = 0x104193) (andR32Imm32Effect 0x104193 7 9 0xffffcccc) (Reg.operands [.gpr 9] [])) #v[67]
    (.letOp (n := 71) (.out 0x10419a (xorR32R32Effect 0x10419a 3 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1] []) (.reg (.gpr 9))) #v[69, 65]
    (.letOp (n := 72) (.exec 0x10419a (fun s => s.RIP = 0x10419a) (xorR32R32Effect 0x10419a 3 9 1) (Reg.operands [.gpr 9, .gpr 1] [])) #v[69, 65]
    (.letOp (n := 73) (.out 0x10419d (leaR32Effect 0x10419d 8 1 (.abs (some 10) 3 0x0)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 10] []) (.reg (.gpr 1))) #v[61]
    (.letOp (n := 74) (.exec 0x10419d (fun s => s.RIP = 0x10419d) (leaR32Effect 0x10419d 8 1 (.abs (some 10) 3 0x0)) (Reg.operands [.gpr 10] [])) #v[61]
    (.letOp (n := 75) (.out 0x1041a5 (andR32Imm32Effect 0x1041a5 6 1 0xffff8888) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[73]
    (.letOp (n := 76) (.exec 0x1041a5 (fun s => s.RIP = 0x1041a5) (andR32Imm32Effect 0x1041a5 6 1 0xffff8888) (Reg.operands [.gpr 1] [])) #v[73]
    (.letOp (n := 77) (.out 0x1041ab (xorR32R32Effect 0x1041ab 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10] []) (.reg (.gpr 1))) #v[75, 61]
    (.letOp (n := 78) (.exec 0x1041ab (fun s => s.RIP = 0x1041ab) (xorR32R32Effect 0x1041ab 3 1 10) (Reg.operands [.gpr 1, .gpr 10] [])) #v[75, 61]
    (.letOp (n := 79) (.out 0x1041ae (xorR32R32Effect 0x1041ae 3 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 9] []) (.reg (.gpr 1))) #v[77, 71]
    (.letOp (n := 80) (.exec 0x1041ae (fun s => s.RIP = 0x1041ae) (xorR32R32Effect 0x1041ae 3 1 9) (Reg.operands [.gpr 1, .gpr 9] [])) #v[77, 71]
    (.letOp (n := 81) (.exec 0x1041b1 (StorePre 0x1041b1 5 (fun s => AddrMode.addr (.sib 7 (some 2) 1 (.d8 0x6)) s (0x1041b1 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1041b1 5 1 (.sib 7 (some 2) 1 (.d8 0x6))) (Reg.operands [.gpr 1, .gpr 7, .gpr 2] [])) #v[79, 7, 2]
    (.letOp (n := 82) (.out 0x1041b6 (leaR64Effect 0x1041b6 1 (.base 2 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2]
    (.letOp (n := 83) (.exec 0x1041b6 (fun s => s.RIP = 0x1041b6) (leaR64Effect 0x1041b6 1 (.base 2 (.d8 0x4))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 84) (.out 0x1041ba (movR64R64Effect 0x1041ba 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 1] []) (.reg (.gpr 9))) #v[82]
    (.letOp (n := 85) (.exec 0x1041ba (fun s => s.RIP = 0x1041ba) (movR64R64Effect 0x1041ba 9 1) (Reg.operands [.gpr 1] [])) #v[82]
    (.letOp (n := 86) (.out 0x1041bd (subR64R64Effect 0x1041bd 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0] []) (.reg (.gpr 9))) #v[84, 0]
    (.letOp (n := 87) (.exec 0x1041bd (fun s => s.RIP = 0x1041bd) (subR64R64Effect 0x1041bd 9 0) (Reg.operands [.gpr 9, .gpr 0] [])) #v[84, 0]
    (.letOp (n := 88) (.out 0x1041c0 (cmpR64R64Effect 0x1041c0 9 6) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 6] []) (.flag .CF)) #v[86, 6]
    (.letOp (n := 89) (.exec 0x1041c0 (fun s => s.RIP = 0x1041c0) (cmpR64R64Effect 0x1041c0 9 6) (Reg.operands [.gpr 9, .gpr 6] [])) #v[86, 6]
    (.letOp (n := 90) (.pure (condOp 3)) #v[88]
    (.terminate (.condBr (Fin.last 90) ⟨.l10434d, RegMap.args [(0, 0), (1, 82), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 86), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 88), (22, 22), (39, 39), (50, 50), (51, 51)] 91⟩ ⟨.l1041c9, RegMap.args [(0, 0), (1, 82), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 86), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 88), (22, 22), (39, 39), (50, 50), (51, 51)] 91⟩)))))))))))))))))))))))))))))))))))))))

def bytes_l104168 : List UInt8 :=
  [0x44, 0x0F, 0xB7, 0x54, 0x57, 0x06, 0x44, 0x89, 0xC1, 0x66, 0x41, 0xD3, 0xCA, 0x41, 0x81, 0xE2,
    0x11, 0x11, 0x00, 0x00, 0x66, 0x46, 0x33, 0x14, 0x4F, 0x43, 0x8D, 0x0C, 0x12, 0x81, 0xE1, 0xEE,
    0xEE, 0xFF, 0xFF, 0x46, 0x8D, 0x0C, 0x95, 0x00, 0x00, 0x00, 0x00, 0x41, 0x81, 0xE1, 0xCC, 0xCC,
    0xFF, 0xFF, 0x41, 0x31, 0xC9, 0x42, 0x8D, 0x0C, 0xD5, 0x00, 0x00, 0x00, 0x00, 0x81, 0xE1, 0x88,
    0x88, 0xFF, 0xFF, 0x44, 0x31, 0xD1, 0x44, 0x31, 0xC9, 0x66, 0x89, 0x4C, 0x57, 0x06, 0x48, 0x8D,
    0x4A, 0x04, 0x49, 0x89, 0xC9, 0x49, 0x29, 0xC1, 0x49, 0x39, 0xF1, 0x0F, 0x83, 0x84, 0x01, 0x00,
    0x00]

theorem code_l104168 : ∀ x ∈ codeRange 0x104168 bytes_l104168, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4168 97 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1041c9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1041c9 (cmpR64R64Effect 0x1041c9 1 6) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 6] []) (.flag .CF)) #v[1, 6]
    (.letOp (n := 54) (.exec 0x1041c9 (fun s => s.RIP = 0x1041c9) (cmpR64R64Effect 0x1041c9 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[1, 6]
    (.letOp (n := 55) (.pure (condOp 3)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l10435f, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l1041d2, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l1041c9 : List UInt8 :=
  [0x48, 0x39, 0xF1, 0x0F, 0x83, 0x8D, 0x01, 0x00, 0x00]

theorem code_l1041c9 : ∀ x ∈ codeRange 0x1041c9 bytes_l1041c9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x41c9 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1041d2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1041d2 (movzxR32M16Effect 0x1041d2 6 10 (.sib 7 (some 2) 1 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 7, .gpr 2] []) (.reg (.gpr 10))) #v[7, 2]
    (.letOp (n := 54) (.exec 0x1041d2 (LoadPre 0x1041d2 (fun s => AddrMode.addr (.sib 7 (some 2) 1 (.d8 0x8)) s (0x1041d2 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x1041d2 6 10 (.sib 7 (some 2) 1 (.d8 0x8))) (Reg.operands [.gpr 7, .gpr 2] [])) #v[7, 2]
    (.letOp (n := 55) (.out 0x1041d8 (movR32R32Effect 0x1041d8 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 8] []) (.reg (.gpr 1))) #v[8]
    (.letOp (n := 56) (.exec 0x1041d8 (fun s => s.RIP = 0x1041d8) (movR32R32Effect 0x1041d8 3 1 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 57) (.out 0x1041db (rorR16ClEffect 0x1041db 4 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[53, 55]
    (.letOp (n := 58) (.exec 0x1041db (fun s => s.RIP = 0x1041db) (rorR16ClEffect 0x1041db 4 10) (Reg.operands [.gpr 10, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53, 55]
    (.letOp (n := 59) (.out 0x1041df (andR32Imm32Effect 0x1041df 7 10 0x1111) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[57]
    (.letOp (n := 60) (.exec 0x1041df (fun s => s.RIP = 0x1041df) (andR32Imm32Effect 0x1041df 7 10 0x1111) (Reg.operands [.gpr 10] [])) #v[57]
    (.letOp (n := 61) (.out 0x1041e6 (xorR16M16Effect 0x1041e6 5 10 (.sib 7 (some 9) 1 .none)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 7, .gpr 9] []) (.reg (.gpr 10))) #v[59, 7, 9]
    (.letOp (n := 62) (.exec 0x1041e6 (LoadPre 0x1041e6 (fun s => AddrMode.addr (.sib 7 (some 9) 1 .none) s (0x1041e6 + BitVec.ofNat 64 5)) 2) (xorR16M16Effect 0x1041e6 5 10 (.sib 7 (some 9) 1 .none)) (Reg.operands [.gpr 10, .gpr 7, .gpr 9] [])) #v[59, 7, 9]
    (.letOp (n := 63) (.out 0x1041eb (leaR32Effect 0x1041eb 4 1 (.sib 10 (some 10) 0 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 10, .gpr 10] []) (.reg (.gpr 1))) #v[61, 61]
    (.letOp (n := 64) (.exec 0x1041eb (fun s => s.RIP = 0x1041eb) (leaR32Effect 0x1041eb 4 1 (.sib 10 (some 10) 0 .none)) (Reg.operands [.gpr 10, .gpr 10] [])) #v[61, 61]
    (.letOp (n := 65) (.out 0x1041ef (andR32Imm32Effect 0x1041ef 6 1 0xffffeeee) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[63]
    (.letOp (n := 66) (.exec 0x1041ef (fun s => s.RIP = 0x1041ef) (andR32Imm32Effect 0x1041ef 6 1 0xffffeeee) (Reg.operands [.gpr 1] [])) #v[63]
    (.letOp (n := 67) (.out 0x1041f5 (leaR32Effect 0x1041f5 8 9 (.abs (some 10) 2 0x0)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 10] []) (.reg (.gpr 9))) #v[61]
    (.letOp (n := 68) (.exec 0x1041f5 (fun s => s.RIP = 0x1041f5) (leaR32Effect 0x1041f5 8 9 (.abs (some 10) 2 0x0)) (Reg.operands [.gpr 10] [])) #v[61]
    (.letOp (n := 69) (.out 0x1041fd (andR32Imm32Effect 0x1041fd 7 9 0xffffcccc) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[67]
    (.letOp (n := 70) (.exec 0x1041fd (fun s => s.RIP = 0x1041fd) (andR32Imm32Effect 0x1041fd 7 9 0xffffcccc) (Reg.operands [.gpr 9] [])) #v[67]
    (.letOp (n := 71) (.out 0x104204 (xorR32R32Effect 0x104204 3 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1] []) (.reg (.gpr 9))) #v[69, 65]
    (.letOp (n := 72) (.exec 0x104204 (fun s => s.RIP = 0x104204) (xorR32R32Effect 0x104204 3 9 1) (Reg.operands [.gpr 9, .gpr 1] [])) #v[69, 65]
    (.letOp (n := 73) (.out 0x104207 (leaR32Effect 0x104207 8 1 (.abs (some 10) 3 0x0)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 10] []) (.reg (.gpr 1))) #v[61]
    (.letOp (n := 74) (.exec 0x104207 (fun s => s.RIP = 0x104207) (leaR32Effect 0x104207 8 1 (.abs (some 10) 3 0x0)) (Reg.operands [.gpr 10] [])) #v[61]
    (.letOp (n := 75) (.out 0x10420f (andR32Imm32Effect 0x10420f 6 1 0xffff8888) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[73]
    (.letOp (n := 76) (.exec 0x10420f (fun s => s.RIP = 0x10420f) (andR32Imm32Effect 0x10420f 6 1 0xffff8888) (Reg.operands [.gpr 1] [])) #v[73]
    (.letOp (n := 77) (.out 0x104215 (xorR32R32Effect 0x104215 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10] []) (.reg (.gpr 1))) #v[75, 61]
    (.letOp (n := 78) (.exec 0x104215 (fun s => s.RIP = 0x104215) (xorR32R32Effect 0x104215 3 1 10) (Reg.operands [.gpr 1, .gpr 10] [])) #v[75, 61]
    (.letOp (n := 79) (.out 0x104218 (xorR32R32Effect 0x104218 3 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 9] []) (.reg (.gpr 1))) #v[77, 71]
    (.letOp (n := 80) (.exec 0x104218 (fun s => s.RIP = 0x104218) (xorR32R32Effect 0x104218 3 1 9) (Reg.operands [.gpr 1, .gpr 9] [])) #v[77, 71]
    (.letOp (n := 81) (.exec 0x10421b (StorePre 0x10421b 5 (fun s => AddrMode.addr (.sib 7 (some 2) 1 (.d8 0x8)) s (0x10421b + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x10421b 5 1 (.sib 7 (some 2) 1 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 7, .gpr 2] [])) #v[79, 7, 2]
    (.letOp (n := 82) (.out 0x104220 (leaR64Effect 0x104220 1 (.base 2 (.d8 0x5))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2]
    (.letOp (n := 83) (.exec 0x104220 (fun s => s.RIP = 0x104220) (leaR64Effect 0x104220 1 (.base 2 (.d8 0x5))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 84) (.out 0x104224 (movR64R64Effect 0x104224 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 1] []) (.reg (.gpr 9))) #v[82]
    (.letOp (n := 85) (.exec 0x104224 (fun s => s.RIP = 0x104224) (movR64R64Effect 0x104224 9 1) (Reg.operands [.gpr 1] [])) #v[82]
    (.letOp (n := 86) (.out 0x104227 (subR64R64Effect 0x104227 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0] []) (.reg (.gpr 9))) #v[84, 0]
    (.letOp (n := 87) (.exec 0x104227 (fun s => s.RIP = 0x104227) (subR64R64Effect 0x104227 9 0) (Reg.operands [.gpr 9, .gpr 0] [])) #v[84, 0]
    (.letOp (n := 88) (.out 0x10422a (cmpR64R64Effect 0x10422a 9 6) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 6] []) (.flag .CF)) #v[86, 6]
    (.letOp (n := 89) (.exec 0x10422a (fun s => s.RIP = 0x10422a) (cmpR64R64Effect 0x10422a 9 6) (Reg.operands [.gpr 9, .gpr 6] [])) #v[86, 6]
    (.letOp (n := 90) (.pure (condOp 3)) #v[88]
    (.terminate (.condBr (Fin.last 90) ⟨.l10434d, RegMap.args [(0, 0), (1, 82), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 86), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 88), (22, 22), (39, 39), (50, 50), (51, 51)] 91⟩ ⟨.l104233, RegMap.args [(0, 0), (1, 82), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 86), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 88), (22, 22), (39, 39), (50, 50), (51, 51)] 91⟩)))))))))))))))))))))))))))))))))))))))

def bytes_l1041d2 : List UInt8 :=
  [0x44, 0x0F, 0xB7, 0x54, 0x57, 0x08, 0x44, 0x89, 0xC1, 0x66, 0x41, 0xD3, 0xCA, 0x41, 0x81, 0xE2,
    0x11, 0x11, 0x00, 0x00, 0x66, 0x46, 0x33, 0x14, 0x4F, 0x43, 0x8D, 0x0C, 0x12, 0x81, 0xE1, 0xEE,
    0xEE, 0xFF, 0xFF, 0x46, 0x8D, 0x0C, 0x95, 0x00, 0x00, 0x00, 0x00, 0x41, 0x81, 0xE1, 0xCC, 0xCC,
    0xFF, 0xFF, 0x41, 0x31, 0xC9, 0x42, 0x8D, 0x0C, 0xD5, 0x00, 0x00, 0x00, 0x00, 0x81, 0xE1, 0x88,
    0x88, 0xFF, 0xFF, 0x44, 0x31, 0xD1, 0x44, 0x31, 0xC9, 0x66, 0x89, 0x4C, 0x57, 0x08, 0x48, 0x8D,
    0x4A, 0x05, 0x49, 0x89, 0xC9, 0x49, 0x29, 0xC1, 0x49, 0x39, 0xF1, 0x0F, 0x83, 0x1A, 0x01, 0x00,
    0x00]

theorem code_l1041d2 : ∀ x ∈ codeRange 0x1041d2 bytes_l1041d2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x41d2 97 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104233 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x104233 (cmpR64R64Effect 0x104233 1 6) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 6] []) (.flag .CF)) #v[1, 6]
    (.letOp (n := 54) (.exec 0x104233 (fun s => s.RIP = 0x104233) (cmpR64R64Effect 0x104233 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[1, 6]
    (.letOp (n := 55) (.pure (condOp 3)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l10435f, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l10423c, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l104233 : List UInt8 :=
  [0x48, 0x39, 0xF1, 0x0F, 0x83, 0x23, 0x01, 0x00, 0x00]

theorem code_l104233 : ∀ x ∈ codeRange 0x104233 bytes_l104233, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4233 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10423c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10423c (movzxR32M16Effect 0x10423c 6 10 (.sib 7 (some 2) 1 (.d8 0xa))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 7, .gpr 2] []) (.reg (.gpr 10))) #v[7, 2]
    (.letOp (n := 54) (.exec 0x10423c (LoadPre 0x10423c (fun s => AddrMode.addr (.sib 7 (some 2) 1 (.d8 0xa)) s (0x10423c + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x10423c 6 10 (.sib 7 (some 2) 1 (.d8 0xa))) (Reg.operands [.gpr 7, .gpr 2] [])) #v[7, 2]
    (.letOp (n := 55) (.out 0x104242 (movR32R32Effect 0x104242 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 8] []) (.reg (.gpr 1))) #v[8]
    (.letOp (n := 56) (.exec 0x104242 (fun s => s.RIP = 0x104242) (movR32R32Effect 0x104242 3 1 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 57) (.out 0x104245 (rorR16ClEffect 0x104245 4 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[53, 55]
    (.letOp (n := 58) (.exec 0x104245 (fun s => s.RIP = 0x104245) (rorR16ClEffect 0x104245 4 10) (Reg.operands [.gpr 10, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53, 55]
    (.letOp (n := 59) (.out 0x104249 (andR32Imm32Effect 0x104249 7 10 0x1111) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[57]
    (.letOp (n := 60) (.exec 0x104249 (fun s => s.RIP = 0x104249) (andR32Imm32Effect 0x104249 7 10 0x1111) (Reg.operands [.gpr 10] [])) #v[57]
    (.letOp (n := 61) (.out 0x104250 (xorR16M16Effect 0x104250 5 10 (.sib 7 (some 9) 1 .none)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 7, .gpr 9] []) (.reg (.gpr 10))) #v[59, 7, 9]
    (.letOp (n := 62) (.exec 0x104250 (LoadPre 0x104250 (fun s => AddrMode.addr (.sib 7 (some 9) 1 .none) s (0x104250 + BitVec.ofNat 64 5)) 2) (xorR16M16Effect 0x104250 5 10 (.sib 7 (some 9) 1 .none)) (Reg.operands [.gpr 10, .gpr 7, .gpr 9] [])) #v[59, 7, 9]
    (.letOp (n := 63) (.out 0x104255 (leaR32Effect 0x104255 4 1 (.sib 10 (some 10) 0 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 10, .gpr 10] []) (.reg (.gpr 1))) #v[61, 61]
    (.letOp (n := 64) (.exec 0x104255 (fun s => s.RIP = 0x104255) (leaR32Effect 0x104255 4 1 (.sib 10 (some 10) 0 .none)) (Reg.operands [.gpr 10, .gpr 10] [])) #v[61, 61]
    (.letOp (n := 65) (.out 0x104259 (andR32Imm32Effect 0x104259 6 1 0xffffeeee) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[63]
    (.letOp (n := 66) (.exec 0x104259 (fun s => s.RIP = 0x104259) (andR32Imm32Effect 0x104259 6 1 0xffffeeee) (Reg.operands [.gpr 1] [])) #v[63]
    (.letOp (n := 67) (.out 0x10425f (leaR32Effect 0x10425f 8 9 (.abs (some 10) 2 0x0)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 10] []) (.reg (.gpr 9))) #v[61]
    (.letOp (n := 68) (.exec 0x10425f (fun s => s.RIP = 0x10425f) (leaR32Effect 0x10425f 8 9 (.abs (some 10) 2 0x0)) (Reg.operands [.gpr 10] [])) #v[61]
    (.letOp (n := 69) (.out 0x104267 (andR32Imm32Effect 0x104267 7 9 0xffffcccc) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[67]
    (.letOp (n := 70) (.exec 0x104267 (fun s => s.RIP = 0x104267) (andR32Imm32Effect 0x104267 7 9 0xffffcccc) (Reg.operands [.gpr 9] [])) #v[67]
    (.letOp (n := 71) (.out 0x10426e (xorR32R32Effect 0x10426e 3 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1] []) (.reg (.gpr 9))) #v[69, 65]
    (.letOp (n := 72) (.exec 0x10426e (fun s => s.RIP = 0x10426e) (xorR32R32Effect 0x10426e 3 9 1) (Reg.operands [.gpr 9, .gpr 1] [])) #v[69, 65]
    (.letOp (n := 73) (.out 0x104271 (leaR32Effect 0x104271 8 1 (.abs (some 10) 3 0x0)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 10] []) (.reg (.gpr 1))) #v[61]
    (.letOp (n := 74) (.exec 0x104271 (fun s => s.RIP = 0x104271) (leaR32Effect 0x104271 8 1 (.abs (some 10) 3 0x0)) (Reg.operands [.gpr 10] [])) #v[61]
    (.letOp (n := 75) (.out 0x104279 (andR32Imm32Effect 0x104279 6 1 0xffff8888) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[73]
    (.letOp (n := 76) (.exec 0x104279 (fun s => s.RIP = 0x104279) (andR32Imm32Effect 0x104279 6 1 0xffff8888) (Reg.operands [.gpr 1] [])) #v[73]
    (.letOp (n := 77) (.out 0x10427f (xorR32R32Effect 0x10427f 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10] []) (.reg (.gpr 1))) #v[75, 61]
    (.letOp (n := 78) (.exec 0x10427f (fun s => s.RIP = 0x10427f) (xorR32R32Effect 0x10427f 3 1 10) (Reg.operands [.gpr 1, .gpr 10] [])) #v[75, 61]
    (.letOp (n := 79) (.out 0x104282 (xorR32R32Effect 0x104282 3 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 9] []) (.reg (.gpr 1))) #v[77, 71]
    (.letOp (n := 80) (.exec 0x104282 (fun s => s.RIP = 0x104282) (xorR32R32Effect 0x104282 3 1 9) (Reg.operands [.gpr 1, .gpr 9] [])) #v[77, 71]
    (.letOp (n := 81) (.exec 0x104285 (StorePre 0x104285 5 (fun s => AddrMode.addr (.sib 7 (some 2) 1 (.d8 0xa)) s (0x104285 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x104285 5 1 (.sib 7 (some 2) 1 (.d8 0xa))) (Reg.operands [.gpr 1, .gpr 7, .gpr 2] [])) #v[79, 7, 2]
    (.letOp (n := 82) (.out 0x10428a (leaR64Effect 0x10428a 1 (.base 2 (.d8 0x6))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2]
    (.letOp (n := 83) (.exec 0x10428a (fun s => s.RIP = 0x10428a) (leaR64Effect 0x10428a 1 (.base 2 (.d8 0x6))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 84) (.out 0x10428e (movR64R64Effect 0x10428e 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 1] []) (.reg (.gpr 9))) #v[82]
    (.letOp (n := 85) (.exec 0x10428e (fun s => s.RIP = 0x10428e) (movR64R64Effect 0x10428e 9 1) (Reg.operands [.gpr 1] [])) #v[82]
    (.letOp (n := 86) (.out 0x104291 (subR64R64Effect 0x104291 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0] []) (.reg (.gpr 9))) #v[84, 0]
    (.letOp (n := 87) (.exec 0x104291 (fun s => s.RIP = 0x104291) (subR64R64Effect 0x104291 9 0) (Reg.operands [.gpr 9, .gpr 0] [])) #v[84, 0]
    (.letOp (n := 88) (.out 0x104294 (cmpR64R64Effect 0x104294 9 6) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 6] []) (.flag .CF)) #v[86, 6]
    (.letOp (n := 89) (.exec 0x104294 (fun s => s.RIP = 0x104294) (cmpR64R64Effect 0x104294 9 6) (Reg.operands [.gpr 9, .gpr 6] [])) #v[86, 6]
    (.letOp (n := 90) (.pure (condOp 3)) #v[88]
    (.terminate (.condBr (Fin.last 90) ⟨.l10434d, RegMap.args [(0, 0), (1, 82), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 86), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 88), (22, 22), (39, 39), (50, 50), (51, 51)] 91⟩ ⟨.l10429d, RegMap.args [(0, 0), (1, 82), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 86), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 88), (22, 22), (39, 39), (50, 50), (51, 51)] 91⟩)))))))))))))))))))))))))))))))))))))))

def bytes_l10423c : List UInt8 :=
  [0x44, 0x0F, 0xB7, 0x54, 0x57, 0x0A, 0x44, 0x89, 0xC1, 0x66, 0x41, 0xD3, 0xCA, 0x41, 0x81, 0xE2,
    0x11, 0x11, 0x00, 0x00, 0x66, 0x46, 0x33, 0x14, 0x4F, 0x43, 0x8D, 0x0C, 0x12, 0x81, 0xE1, 0xEE,
    0xEE, 0xFF, 0xFF, 0x46, 0x8D, 0x0C, 0x95, 0x00, 0x00, 0x00, 0x00, 0x41, 0x81, 0xE1, 0xCC, 0xCC,
    0xFF, 0xFF, 0x41, 0x31, 0xC9, 0x42, 0x8D, 0x0C, 0xD5, 0x00, 0x00, 0x00, 0x00, 0x81, 0xE1, 0x88,
    0x88, 0xFF, 0xFF, 0x44, 0x31, 0xD1, 0x44, 0x31, 0xC9, 0x66, 0x89, 0x4C, 0x57, 0x0A, 0x48, 0x8D,
    0x4A, 0x06, 0x49, 0x89, 0xC9, 0x49, 0x29, 0xC1, 0x49, 0x39, 0xF1, 0x0F, 0x83, 0xB0, 0x00, 0x00,
    0x00]

theorem code_l10423c : ∀ x ∈ codeRange 0x10423c bytes_l10423c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x423c 97 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10429d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10429d (cmpR64R64Effect 0x10429d 1 6) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 6] []) (.flag .CF)) #v[1, 6]
    (.letOp (n := 54) (.exec 0x10429d (fun s => s.RIP = 0x10429d) (cmpR64R64Effect 0x10429d 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[1, 6]
    (.letOp (n := 55) (.pure (condOp 3)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l10435f, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l1042a6, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l10429d : List UInt8 :=
  [0x48, 0x39, 0xF1, 0x0F, 0x83, 0xB9, 0x00, 0x00, 0x00]

theorem code_l10429d : ∀ x ∈ codeRange 0x10429d bytes_l10429d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x429d 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1042a6 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1042a6 (movzxR32M16Effect 0x1042a6 6 10 (.sib 7 (some 2) 1 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 7, .gpr 2] []) (.reg (.gpr 10))) #v[7, 2]
    (.letOp (n := 54) (.exec 0x1042a6 (LoadPre 0x1042a6 (fun s => AddrMode.addr (.sib 7 (some 2) 1 (.d8 0xc)) s (0x1042a6 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x1042a6 6 10 (.sib 7 (some 2) 1 (.d8 0xc))) (Reg.operands [.gpr 7, .gpr 2] [])) #v[7, 2]
    (.letOp (n := 55) (.out 0x1042ac (movR32R32Effect 0x1042ac 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 8] []) (.reg (.gpr 1))) #v[8]
    (.letOp (n := 56) (.exec 0x1042ac (fun s => s.RIP = 0x1042ac) (movR32R32Effect 0x1042ac 3 1 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 57) (.out 0x1042af (rorR16ClEffect 0x1042af 4 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[53, 55]
    (.letOp (n := 58) (.exec 0x1042af (fun s => s.RIP = 0x1042af) (rorR16ClEffect 0x1042af 4 10) (Reg.operands [.gpr 10, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53, 55]
    (.letOp (n := 59) (.out 0x1042b3 (andR32Imm32Effect 0x1042b3 7 10 0x1111) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[57]
    (.letOp (n := 60) (.exec 0x1042b3 (fun s => s.RIP = 0x1042b3) (andR32Imm32Effect 0x1042b3 7 10 0x1111) (Reg.operands [.gpr 10] [])) #v[57]
    (.letOp (n := 61) (.out 0x1042ba (xorR16M16Effect 0x1042ba 5 10 (.sib 7 (some 9) 1 .none)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 7, .gpr 9] []) (.reg (.gpr 10))) #v[59, 7, 9]
    (.letOp (n := 62) (.exec 0x1042ba (LoadPre 0x1042ba (fun s => AddrMode.addr (.sib 7 (some 9) 1 .none) s (0x1042ba + BitVec.ofNat 64 5)) 2) (xorR16M16Effect 0x1042ba 5 10 (.sib 7 (some 9) 1 .none)) (Reg.operands [.gpr 10, .gpr 7, .gpr 9] [])) #v[59, 7, 9]
    (.letOp (n := 63) (.out 0x1042bf (leaR32Effect 0x1042bf 4 1 (.sib 10 (some 10) 0 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 10, .gpr 10] []) (.reg (.gpr 1))) #v[61, 61]
    (.letOp (n := 64) (.exec 0x1042bf (fun s => s.RIP = 0x1042bf) (leaR32Effect 0x1042bf 4 1 (.sib 10 (some 10) 0 .none)) (Reg.operands [.gpr 10, .gpr 10] [])) #v[61, 61]
    (.letOp (n := 65) (.out 0x1042c3 (andR32Imm32Effect 0x1042c3 6 1 0xffffeeee) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[63]
    (.letOp (n := 66) (.exec 0x1042c3 (fun s => s.RIP = 0x1042c3) (andR32Imm32Effect 0x1042c3 6 1 0xffffeeee) (Reg.operands [.gpr 1] [])) #v[63]
    (.letOp (n := 67) (.out 0x1042c9 (leaR32Effect 0x1042c9 8 9 (.abs (some 10) 2 0x0)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 10] []) (.reg (.gpr 9))) #v[61]
    (.letOp (n := 68) (.exec 0x1042c9 (fun s => s.RIP = 0x1042c9) (leaR32Effect 0x1042c9 8 9 (.abs (some 10) 2 0x0)) (Reg.operands [.gpr 10] [])) #v[61]
    (.letOp (n := 69) (.out 0x1042d1 (andR32Imm32Effect 0x1042d1 7 9 0xffffcccc) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[67]
    (.letOp (n := 70) (.exec 0x1042d1 (fun s => s.RIP = 0x1042d1) (andR32Imm32Effect 0x1042d1 7 9 0xffffcccc) (Reg.operands [.gpr 9] [])) #v[67]
    (.letOp (n := 71) (.out 0x1042d8 (xorR32R32Effect 0x1042d8 3 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1] []) (.reg (.gpr 9))) #v[69, 65]
    (.letOp (n := 72) (.exec 0x1042d8 (fun s => s.RIP = 0x1042d8) (xorR32R32Effect 0x1042d8 3 9 1) (Reg.operands [.gpr 9, .gpr 1] [])) #v[69, 65]
    (.letOp (n := 73) (.out 0x1042db (leaR32Effect 0x1042db 8 1 (.abs (some 10) 3 0x0)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 10] []) (.reg (.gpr 1))) #v[61]
    (.letOp (n := 74) (.exec 0x1042db (fun s => s.RIP = 0x1042db) (leaR32Effect 0x1042db 8 1 (.abs (some 10) 3 0x0)) (Reg.operands [.gpr 10] [])) #v[61]
    (.letOp (n := 75) (.out 0x1042e3 (andR32Imm32Effect 0x1042e3 6 1 0xffff8888) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[73]
    (.letOp (n := 76) (.exec 0x1042e3 (fun s => s.RIP = 0x1042e3) (andR32Imm32Effect 0x1042e3 6 1 0xffff8888) (Reg.operands [.gpr 1] [])) #v[73]
    (.letOp (n := 77) (.out 0x1042e9 (xorR32R32Effect 0x1042e9 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10] []) (.reg (.gpr 1))) #v[75, 61]
    (.letOp (n := 78) (.exec 0x1042e9 (fun s => s.RIP = 0x1042e9) (xorR32R32Effect 0x1042e9 3 1 10) (Reg.operands [.gpr 1, .gpr 10] [])) #v[75, 61]
    (.letOp (n := 79) (.out 0x1042ec (xorR32R32Effect 0x1042ec 3 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 9] []) (.reg (.gpr 1))) #v[77, 71]
    (.letOp (n := 80) (.exec 0x1042ec (fun s => s.RIP = 0x1042ec) (xorR32R32Effect 0x1042ec 3 1 9) (Reg.operands [.gpr 1, .gpr 9] [])) #v[77, 71]
    (.letOp (n := 81) (.exec 0x1042ef (StorePre 0x1042ef 5 (fun s => AddrMode.addr (.sib 7 (some 2) 1 (.d8 0xc)) s (0x1042ef + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1042ef 5 1 (.sib 7 (some 2) 1 (.d8 0xc))) (Reg.operands [.gpr 1, .gpr 7, .gpr 2] [])) #v[79, 7, 2]
    (.letOp (n := 82) (.out 0x1042f4 (leaR64Effect 0x1042f4 1 (.base 2 (.d8 0x7))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2]
    (.letOp (n := 83) (.exec 0x1042f4 (fun s => s.RIP = 0x1042f4) (leaR64Effect 0x1042f4 1 (.base 2 (.d8 0x7))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 84) (.out 0x1042f8 (movR64R64Effect 0x1042f8 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 1] []) (.reg (.gpr 9))) #v[82]
    (.letOp (n := 85) (.exec 0x1042f8 (fun s => s.RIP = 0x1042f8) (movR64R64Effect 0x1042f8 9 1) (Reg.operands [.gpr 1] [])) #v[82]
    (.letOp (n := 86) (.out 0x1042fb (subR64R64Effect 0x1042fb 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0] []) (.reg (.gpr 9))) #v[84, 0]
    (.letOp (n := 87) (.exec 0x1042fb (fun s => s.RIP = 0x1042fb) (subR64R64Effect 0x1042fb 9 0) (Reg.operands [.gpr 9, .gpr 0] [])) #v[84, 0]
    (.letOp (n := 88) (.out 0x1042fe (cmpR64R64Effect 0x1042fe 9 6) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 6] []) (.flag .CF)) #v[86, 6]
    (.letOp (n := 89) (.exec 0x1042fe (fun s => s.RIP = 0x1042fe) (cmpR64R64Effect 0x1042fe 9 6) (Reg.operands [.gpr 9, .gpr 6] [])) #v[86, 6]
    (.letOp (n := 90) (.pure (condOp 3)) #v[88]
    (.terminate (.condBr (Fin.last 90) ⟨.l10434d, RegMap.args [(0, 0), (1, 82), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 86), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 88), (22, 22), (39, 39), (50, 50), (51, 51)] 91⟩ ⟨.l104303, RegMap.args [(0, 0), (1, 82), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 86), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 88), (22, 22), (39, 39), (50, 50), (51, 51)] 91⟩)))))))))))))))))))))))))))))))))))))))

def bytes_l1042a6 : List UInt8 :=
  [0x44, 0x0F, 0xB7, 0x54, 0x57, 0x0C, 0x44, 0x89, 0xC1, 0x66, 0x41, 0xD3, 0xCA, 0x41, 0x81, 0xE2,
    0x11, 0x11, 0x00, 0x00, 0x66, 0x46, 0x33, 0x14, 0x4F, 0x43, 0x8D, 0x0C, 0x12, 0x81, 0xE1, 0xEE,
    0xEE, 0xFF, 0xFF, 0x46, 0x8D, 0x0C, 0x95, 0x00, 0x00, 0x00, 0x00, 0x41, 0x81, 0xE1, 0xCC, 0xCC,
    0xFF, 0xFF, 0x41, 0x31, 0xC9, 0x42, 0x8D, 0x0C, 0xD5, 0x00, 0x00, 0x00, 0x00, 0x81, 0xE1, 0x88,
    0x88, 0xFF, 0xFF, 0x44, 0x31, 0xD1, 0x44, 0x31, 0xC9, 0x66, 0x89, 0x4C, 0x57, 0x0C, 0x48, 0x8D,
    0x4A, 0x07, 0x49, 0x89, 0xC9, 0x49, 0x29, 0xC1, 0x49, 0x39, 0xF1, 0x73, 0x4A]

theorem code_l1042a6 : ∀ x ∈ codeRange 0x1042a6 bytes_l1042a6, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x42a6 93 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104303 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x104303 (cmpR64R64Effect 0x104303 1 6) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 6] []) (.flag .CF)) #v[1, 6]
    (.letOp (n := 54) (.exec 0x104303 (fun s => s.RIP = 0x104303) (cmpR64R64Effect 0x104303 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[1, 6]
    (.letOp (n := 55) (.pure (condOp 3)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l10435f, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l104308, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l104303 : List UInt8 :=
  [0x48, 0x39, 0xF1, 0x73, 0x57]

theorem code_l104303 : ∀ x ∈ codeRange 0x104303 bytes_l104303, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4303 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104308 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x104308 (movzxR32M16Effect 0x104308 5 0 (.sib 7 (some 2) 1 (.d8 0xe))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 2] []) (.reg (.gpr 0))) #v[7, 2]
    (.letOp (n := 54) (.exec 0x104308 (LoadPre 0x104308 (fun s => AddrMode.addr (.sib 7 (some 2) 1 (.d8 0xe)) s (0x104308 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x104308 5 0 (.sib 7 (some 2) 1 (.d8 0xe))) (Reg.operands [.gpr 7, .gpr 2] [])) #v[7, 2]
    (.letOp (n := 55) (.out 0x10430d (movR32R32Effect 0x10430d 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 8] []) (.reg (.gpr 1))) #v[8]
    (.letOp (n := 56) (.exec 0x10430d (fun s => s.RIP = 0x10430d) (movR32R32Effect 0x10430d 3 1 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 57) (.out 0x104310 (rorR16ClEffect 0x104310 3 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[53, 55]
    (.letOp (n := 58) (.exec 0x104310 (fun s => s.RIP = 0x104310) (rorR16ClEffect 0x104310 3 0) (Reg.operands [.gpr 0, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53, 55]
    (.letOp (n := 59) (.out 0x104313 (andEaxImm32Effect 0x104313 0x1111) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[57]
    (.letOp (n := 60) (.exec 0x104313 (fun s => s.RIP = 0x104313) (andEaxImm32Effect 0x104313 0x1111) (Reg.operands [.gpr 0] [])) #v[57]
    (.letOp (n := 61) (.out 0x104318 (xorR16M16Effect 0x104318 5 0 (.sib 7 (some 9) 1 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7, .gpr 9] []) (.reg (.gpr 0))) #v[59, 7, 9]
    (.letOp (n := 62) (.exec 0x104318 (LoadPre 0x104318 (fun s => AddrMode.addr (.sib 7 (some 9) 1 .none) s (0x104318 + BitVec.ofNat 64 5)) 2) (xorR16M16Effect 0x104318 5 0 (.sib 7 (some 9) 1 .none)) (Reg.operands [.gpr 0, .gpr 7, .gpr 9] [])) #v[59, 7, 9]
    (.letOp (n := 63) (.out 0x10431d (leaR32Effect 0x10431d 3 1 (.sib 0 (some 0) 0 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0, .gpr 0] []) (.reg (.gpr 1))) #v[61, 61]
    (.letOp (n := 64) (.exec 0x10431d (fun s => s.RIP = 0x10431d) (leaR32Effect 0x10431d 3 1 (.sib 0 (some 0) 0 .none)) (Reg.operands [.gpr 0, .gpr 0] [])) #v[61, 61]
    (.letOp (n := 65) (.out 0x104320 (andR32Imm32Effect 0x104320 6 1 0xffffeeee) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[63]
    (.letOp (n := 66) (.exec 0x104320 (fun s => s.RIP = 0x104320) (andR32Imm32Effect 0x104320 6 1 0xffffeeee) (Reg.operands [.gpr 1] [])) #v[63]
    (.letOp (n := 67) (.out 0x104326 (leaR32Effect 0x104326 7 6 (.abs (some 0) 2 0x0)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[61]
    (.letOp (n := 68) (.exec 0x104326 (fun s => s.RIP = 0x104326) (leaR32Effect 0x104326 7 6 (.abs (some 0) 2 0x0)) (Reg.operands [.gpr 0] [])) #v[61]
    (.letOp (n := 69) (.out 0x10432d (andR32Imm32Effect 0x10432d 6 6 0xffffcccc) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[67]
    (.letOp (n := 70) (.exec 0x10432d (fun s => s.RIP = 0x10432d) (andR32Imm32Effect 0x10432d 6 6 0xffffcccc) (Reg.operands [.gpr 6] [])) #v[67]
    (.letOp (n := 71) (.out 0x104333 (xorR32R32Effect 0x104333 2 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[69, 65]
    (.letOp (n := 72) (.exec 0x104333 (fun s => s.RIP = 0x104333) (xorR32R32Effect 0x104333 2 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[69, 65]
    (.letOp (n := 73) (.out 0x104335 (leaR32Effect 0x104335 7 1 (.abs (some 0) 3 0x0)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[61]
    (.letOp (n := 74) (.exec 0x104335 (fun s => s.RIP = 0x104335) (leaR32Effect 0x104335 7 1 (.abs (some 0) 3 0x0)) (Reg.operands [.gpr 0] [])) #v[61]
    (.letOp (n := 75) (.out 0x10433c (andR32Imm32Effect 0x10433c 6 1 0xffff8888) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[73]
    (.letOp (n := 76) (.exec 0x10433c (fun s => s.RIP = 0x10433c) (andR32Imm32Effect 0x10433c 6 1 0xffff8888) (Reg.operands [.gpr 1] [])) #v[73]
    (.letOp (n := 77) (.out 0x104342 (xorR32R32Effect 0x104342 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[75, 61]
    (.letOp (n := 78) (.exec 0x104342 (fun s => s.RIP = 0x104342) (xorR32R32Effect 0x104342 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[75, 61]
    (.letOp (n := 79) (.out 0x104344 (xorR32R32Effect 0x104344 2 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[77, 71]
    (.letOp (n := 80) (.exec 0x104344 (fun s => s.RIP = 0x104344) (xorR32R32Effect 0x104344 2 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[77, 71]
    (.letOp (n := 81) (.exec 0x104346 (StorePre 0x104346 5 (fun s => AddrMode.addr (.sib 7 (some 2) 1 (.d8 0xe)) s (0x104346 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x104346 5 1 (.sib 7 (some 2) 1 (.d8 0xe))) (Reg.operands [.gpr 1, .gpr 7, .gpr 2] [])) #v[79, 7, 2]
    (.letOp (n := 82) (.out 0x10434b (popR64Effect 0x10434b 1 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 83) (.out 0x10434b (popR64Effect 0x10434b 1 0) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 84) (.exec 0x10434b (PopPre 0x10434b) (popR64Effect 0x10434b 1 0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 85) (.out 0x10434c (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[83]
    (.letOp (n := 86) (.out 0x10434c (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[83]
    (.letOp (n := 87) (.exec 0x10434c (RetPre 0x10434c) (retEffect) (Reg.operands [.gpr 4] [])) #v[83]
    (.terminate (.ret (RegMap.args [(0, 82), (1, 79), (2, 2), (3, 3), (4, 86), (5, 5), (6, 71), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 88) (some ⟨85, by decide⟩)))))))))))))))))))))))))))))))))))))

def bytes_l104308 : List UInt8 :=
  [0x0F, 0xB7, 0x44, 0x57, 0x0E, 0x44, 0x89, 0xC1, 0x66, 0xD3, 0xC8, 0x25, 0x11, 0x11, 0x00, 0x00,
    0x66, 0x42, 0x33, 0x04, 0x4F, 0x8D, 0x0C, 0x00, 0x81, 0xE1, 0xEE, 0xEE, 0xFF, 0xFF, 0x8D, 0x34,
    0x85, 0x00, 0x00, 0x00, 0x00, 0x81, 0xE6, 0xCC, 0xCC, 0xFF, 0xFF, 0x31, 0xCE, 0x8D, 0x0C, 0xC5,
    0x00, 0x00, 0x00, 0x00, 0x81, 0xE1, 0x88, 0x88, 0xFF, 0xFF, 0x31, 0xC1, 0x31, 0xF1, 0x66, 0x89,
    0x4C, 0x57, 0x0E, 0x58, 0xC3]

theorem code_l104308 : ∀ x ∈ codeRange 0x104308 bytes_l104308, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4308 69 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10434d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10434d (movR64R64Effect 0x10434d 7 9) (EffectPart.reads (.reg (.gpr 7)) [.gpr 9] []) (.reg (.gpr 7))) #v[9]
    (.letOp (n := 54) (.exec 0x10434d (fun s => s.RIP = 0x10434d) (movR64R64Effect 0x10434d 7 9) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 55) (.out 0x104350 (movR64Imm32Effect 0x104350 2 0x201028) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 56) (.exec 0x104350 (fun s => s.RIP = 0x104350) (movR64Imm32Effect 0x104350 2 0x201028) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x104357 (callEffect (fun _ => 0x103837) 0x10435c) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x104357 (PushPre 0x104357 5) (callEffect (fun _ => 0x103837) 0x10435c) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x10435c⟩) #v[]
    (.terminate (.call ⟨.l103837, RegMap.args [(2, 55), (4, 57), (5, 5), (6, 6), (7, 53), (9, 9)] 60⟩ { target := .l10435c, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l10434d : List UInt8 :=
  [0x4C, 0x89, 0xCF, 0x48, 0xC7, 0xC2, 0x28, 0x10, 0x20, 0x00, 0xE8, 0xDB, 0xF4, 0xFF, 0xFF]

theorem code_l10434d : ∀ x ∈ codeRange 0x10434d bytes_l10434d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x434d 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10435c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10435c (movR64R64Effect 0x10435c 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2]
    (.letOp (n := 54) (.exec 0x10435c (fun s => s.RIP = 0x10435c) (movR64R64Effect 0x10435c 1 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.terminate (.br ⟨.l10435f, RegMap.args [(1, 53), (2, 2), (4, 4), (5, 5), (6, 6)] 55⟩)))

def bytes_l10435c : List UInt8 :=
  [0x48, 0x89, 0xD1]

theorem code_l10435c : ∀ x ∈ codeRange 0x10435c bytes_l10435c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x435c 3 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10435f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10435f (movR64R64Effect 0x10435f 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 1] []) (.reg (.gpr 7))) #v[1]
    (.letOp (n := 54) (.exec 0x10435f (fun s => s.RIP = 0x10435f) (movR64R64Effect 0x10435f 7 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 55) (.out 0x104362 (movR64Imm32Effect 0x104362 2 0x201040) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 56) (.exec 0x104362 (fun s => s.RIP = 0x104362) (movR64Imm32Effect 0x104362 2 0x201040) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x104369 (callEffect (fun _ => 0x103837) 0x10436e) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x104369 (PushPre 0x104369 5) (callEffect (fun _ => 0x103837) 0x10436e) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x10436e⟩) #v[]
    (.terminate (.call ⟨.l103837, RegMap.args [(1, 1), (2, 55), (4, 57), (5, 5), (6, 6), (7, 53)] 60⟩ { target := .l10436e, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l10435f : List UInt8 :=
  [0x48, 0x89, 0xCF, 0x48, 0xC7, 0xC2, 0x40, 0x10, 0x20, 0x00, 0xE8, 0xC9, 0xF4, 0xFF, 0xFF]

theorem code_l10435f : ∀ x ∈ codeRange 0x10435f bytes_l10435f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x435f 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10436e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x10436e (fun s => s.RIP = 0x10436e) (fun _ => nopEffect 0x10436e 2) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l104370, RegMap.args [(3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 54⟩))

def bytes_l10436e : List UInt8 :=
  [0x66, 0x90]

theorem code_l10436e : ∀ x ∈ codeRange 0x10436e bytes_l10436e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x436e 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104370 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x104370 (pushR64Effect 0x104370 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x104370 (PushPre 0x104370 1) (pushR64Effect 0x104370 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x104371 (pushR64Effect 0x104371 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x104371 (PushPre 0x104371 2) (pushR64Effect 0x104371 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x104373 (pushR64Effect 0x104373 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x104373 (PushPre 0x104373 2) (pushR64Effect 0x104373 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x104375 (pushR64Effect 0x104375 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x104375 (PushPre 0x104375 2) (pushR64Effect 0x104375 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x104377 (pushR64Effect 0x104377 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x104377 (PushPre 0x104377 2) (pushR64Effect 0x104377 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x104379 (pushR64Effect 0x104379 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x104379 (PushPre 0x104379 1) (pushR64Effect 0x104379 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x10437a (subR64Imm32Effect 0x10437a 4 0xd8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x10437a (fun s => s.RIP = 0x10437a) (subR64Imm32Effect 0x10437a 4 0xd8) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x104381 (movR64R64Effect 0x104381 12 6) (EffectPart.reads (.reg (.gpr 12)) [.gpr 6] []) (.reg (.gpr 12))) #v[6]
    (.letOp (n := 68) (.exec 0x104381 (fun s => s.RIP = 0x104381) (movR64R64Effect 0x104381 12 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 69) (.exec 0x104384 (StorePre 0x104384 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x104384 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104384 7 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[7, 65]
    (.letOp (n := 70) (.out 0x10438c (leaR64Effect 0x10438c 14 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[65]
    (.letOp (n := 71) (.exec 0x10438c (fun s => s.RIP = 0x10438c) (leaR64Effect 0x10438c 14 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 72) (.out 0x104391 (xorR32R32Effect 0x104391 3 15 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 15] []) (.reg (.gpr 15))) #v[15, 15]
    (.letOp (n := 73) (.exec 0x104391 (fun s => s.RIP = 0x104391) (xorR32R32Effect 0x104391 3 15 15) (Reg.operands [.gpr 15, .gpr 15] [])) #v[15, 15]
    (.letOp (n := 74) (.out 0x104394 (movR32Imm32Effect 0x104394 5 2 0xb0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 75) (.exec 0x104394 (fun s => s.RIP = 0x104394) (movR32Imm32Effect 0x104394 5 2 0xb0) (Reg.operands [] [])) #v[]
    (.letOp (n := 76) (.out 0x104399 (movR64R64Effect 0x104399 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[70]
    (.letOp (n := 77) (.exec 0x104399 (fun s => s.RIP = 0x104399) (movR64R64Effect 0x104399 7 14) (Reg.operands [.gpr 14] [])) #v[70]
    (.letOp (n := 78) (.out 0x10439c (xorR32R32Effect 0x10439c 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[6, 6]
    (.letOp (n := 79) (.exec 0x10439c (fun s => s.RIP = 0x10439c) (xorR32R32Effect 0x10439c 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 80) (.out 0x10439e (callEffect (callMemPtr 0x10439e (.rip 0xfce84)) (0x10439e + BitVec.ofNat 64 (callMemLen (.rip 0xfce84)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 81) (.exec 0x10439e (GoesTo (CallMemPre 0x10439e (.rip 0xfce84)) (callEffect (callMemPtr 0x10439e (.rip 0xfce84)) (0x10439e + BitVec.ofNat 64 (callMemLen (.rip 0xfce84)))) 0x103eb0) (callEffect (callMemPtr 0x10439e (.rip 0xfce84)) (0x10439e + BitVec.ofNat 64 (callMemLen (.rip 0xfce84)))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 82) (.const ⟨64, 0x1043a4⟩) #v[]
    (.terminate (.call ⟨.l103eb0, RegMap.args [(2, 74), (3, 3), (4, 80), (5, 5), (6, 78), (7, 76), (9, 9), (11, 11), (12, 67), (13, 13), (14, 70), (15, 72), (22, 22), (39, 39), (50, 50), (51, 51)] 83⟩ { target := .l1043a4, kept := #v[], arity := rfl, guard := some (Fin.last 82) })))))))))))))))))))))))))))))))

def bytes_l104370 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0xD8, 0x00, 0x00,
    0x00, 0x49, 0x89, 0xF4, 0x48, 0x89, 0xBC, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x4C, 0x8D, 0x74, 0x24,
    0x08, 0x45, 0x31, 0xFF, 0xBA, 0xB0, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF7, 0x31, 0xF6, 0xFF, 0x15,
    0x84, 0xCE, 0x0F, 0x00]

theorem code_l104370 : ∀ x ∈ codeRange 0x104370 bytes_l104370, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4370 52 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1043a4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1043a4 (movR64M64Effect 0x1043a4 0 (.sib 12 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[12]
    (.letOp (n := 54) (.exec 0x1043a4 (LoadPre 0x1043a4 (fun s => AddrMode.addr (.sib 12 none 0 .none) s (0x1043a4 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1043a4 0 (.sib 12 none 0 .none)) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 55) (.out 0x1043a8 (movR64M64Effect 0x1043a8 1 (.sib 12 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 12] []) (.reg (.gpr 1))) #v[12]
    (.letOp (n := 56) (.exec 0x1043a8 (LoadPre 0x1043a8 (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x8)) s (0x1043a8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1043a8 1 (.sib 12 none 0 (.d8 0x8))) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 57) (.exec 0x1043ad (StorePre 0x1043ad 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x1043ad + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1043ad 1 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 58) (.exec 0x1043b5 (StorePre 0x1043b5 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x1043b5 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1043b5 0 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 59) (.out 0x1043bd (leaR64Effect 0x1043bd 2 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 60) (.exec 0x1043bd (fun s => s.RIP = 0x1043bd) (leaR64Effect 0x1043bd 2 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x1043c5 (movR32Imm32Effect 0x1043c5 5 6 0x8) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 62) (.exec 0x1043c5 (fun s => s.RIP = 0x1043c5) (movR32Imm32Effect 0x1043c5 5 6 0x8) (Reg.operands [] [])) #v[]
    (.letOp (n := 63) (.out 0x1043ca (movR64R64Effect 0x1043ca 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 64) (.exec 0x1043ca (fun s => s.RIP = 0x1043ca) (movR64R64Effect 0x1043ca 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 65) (.out 0x1043cd (callEffect (fun _ => 0x109ff0) 0x1043d2) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 66) (.exec 0x1043cd (PushPre 0x1043cd 5) (callEffect (fun _ => 0x109ff0) 0x1043d2) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.const ⟨64, 0x1043d2⟩) #v[]
    (.terminate (.call ⟨.l109ff0, RegMap.args [(0, 53), (1, 55), (2, 59), (3, 3), (4, 65), (5, 5), (6, 61), (7, 63), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 68⟩ { target := .l1043d2, kept := #v[], arity := rfl, guard := some (Fin.last 67) }))))))))))))))))

def bytes_l1043a4 : List UInt8 :=
  [0x49, 0x8B, 0x04, 0x24, 0x49, 0x8B, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x8C, 0x24, 0xD0, 0x00, 0x00,
    0x00, 0x48, 0x89, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x94, 0x24, 0xC8, 0x00, 0x00,
    0x00, 0xBE, 0x08, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF7, 0xE8, 0x1E, 0x5C, 0x00, 0x00]

theorem code_l1043a4 : ∀ x ∈ codeRange 0x1043a4 bytes_l1043a4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x43a4 46 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1043d2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1043d2 (movR32Imm32Effect 0x1043d2 6 12 0x10) (EffectPart.reads (.reg (.gpr 12)) [] []) (.reg (.gpr 12))) #v[]
    (.letOp (n := 54) (.exec 0x1043d2 (fun s => s.RIP = 0x1043d2) (movR32Imm32Effect 0x1043d2 6 12 0x10) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x1043d8 (movR64R64Effect 0x1043d8 13 14) (EffectPart.reads (.reg (.gpr 13)) [.gpr 14] []) (.reg (.gpr 13))) #v[14]
    (.letOp (n := 56) (.exec 0x1043d8 (fun s => s.RIP = 0x1043d8) (movR64R64Effect 0x1043d8 13 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x1043db (xorR32R32Effect 0x1043db 2 5 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 5] []) (.reg (.gpr 5))) #v[5, 5]
    (.letOp (n := 58) (.exec 0x1043db (fun s => s.RIP = 0x1043db) (xorR32R32Effect 0x1043db 2 5 5) (Reg.operands [.gpr 5, .gpr 5] [])) #v[5, 5]
    (.terminate (.br ⟨.l104424, RegMap.args [(0, 0), (1, 1), (3, 3), (4, 4), (5, 57), (8, 8), (9, 9), (11, 11), (12, 53), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l1043d2 : List UInt8 :=
  [0x41, 0xBC, 0x10, 0x00, 0x00, 0x00, 0x4D, 0x89, 0xF5, 0x31, 0xED, 0xEB, 0x45]

theorem code_l1043d2 : ∀ x ∈ codeRange 0x1043d2 bytes_l1043d2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x43d2 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1043e0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1043e0 (StorePre 0x1043e0 5 (fun s => AddrMode.addr (.base 13 (.d8 0x0)) s (0x1043e0 + BitVec.ofNat 64 5)) 1) (xorM8Imm8Effect 0x1043e0 5 (.base 13 (.d8 0x0)) 0x80) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 54) (.exec 0x1043e5 (StorePre 0x1043e5 5 (fun s => AddrMode.addr (.base 13 (.d8 0x2)) s (0x1043e5 + BitVec.ofNat 64 5)) 1) (xorM8Imm8Effect 0x1043e5 5 (.base 13 (.d8 0x2)) 0x80) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 55) (.exec 0x1043ea (StorePre 0x1043ea 5 (fun s => AddrMode.addr (.base 13 (.d8 0x6)) s (0x1043ea + BitVec.ofNat 64 5)) 1) (xorM8Imm8Effect 0x1043ea 5 (.base 13 (.d8 0x6)) 0x80) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 56) (.exec 0x1043ef (StorePre 0x1043ef 5 (fun s => AddrMode.addr (.base 13 (.d8 0x8)) s (0x1043ef + BitVec.ofNat 64 5)) 1) (xorM8Imm8Effect 0x1043ef 5 (.base 13 (.d8 0x8)) 0x80) (Reg.operands [.gpr 13] [])) #v[13]
    (.terminate (.br ⟨.l1043f4, RegMap.args [(0, 0), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l1043e0 : List UInt8 :=
  [0x41, 0x80, 0x75, 0x00, 0x80, 0x41, 0x80, 0x75, 0x02, 0x80, 0x41, 0x80, 0x75, 0x06, 0x80, 0x41,
    0x80, 0x75, 0x08, 0x80]

theorem code_l1043e0 : ∀ x ∈ codeRange 0x1043e0 bytes_l1043e0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x43e0 20 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1043f4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1043f4 (addR64Imm8Effect 0x1043f4 15 0x8) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15] []) (.reg (.gpr 15))) #v[15]
    (.letOp (n := 54) (.exec 0x1043f4 (fun s => s.RIP = 0x1043f4) (addR64Imm8Effect 0x1043f4 15 0x8) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.out 0x1043f8 (movR32Imm32Effect 0x1043f8 5 6 0x58) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 56) (.exec 0x1043f8 (fun s => s.RIP = 0x1043f8) (movR32Imm32Effect 0x1043f8 5 6 0x58) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x1043fd (movR32Imm32Effect 0x1043fd 5 1 0x8) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 58) (.exec 0x1043fd (fun s => s.RIP = 0x1043fd) (movR32Imm32Effect 0x1043fd 5 1 0x8) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x104402 (movR64R64Effect 0x104402 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 60) (.exec 0x104402 (fun s => s.RIP = 0x104402) (movR64R64Effect 0x104402 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 61) (.out 0x104405 (movR64R64Effect 0x104405 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15] []) (.reg (.gpr 2))) #v[53]
    (.letOp (n := 62) (.exec 0x104405 (fun s => s.RIP = 0x104405) (movR64R64Effect 0x104405 2 15) (Reg.operands [.gpr 15] [])) #v[53]
    (.letOp (n := 63) (.out 0x104408 (movR32Imm32Effect 0x104408 6 8 0x7) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 64) (.exec 0x104408 (fun s => s.RIP = 0x104408) (movR32Imm32Effect 0x104408 6 8 0x7) (Reg.operands [] [])) #v[]
    (.letOp (n := 65) (.out 0x10440e (callEffect (fun _ => 0x104010) 0x104413) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 66) (.exec 0x10440e (PushPre 0x10440e 5) (callEffect (fun _ => 0x104010) 0x104413) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.const ⟨64, 0x104413⟩) #v[]
    (.terminate (.call ⟨.l104010, RegMap.args [(0, 0), (1, 57), (2, 61), (3, 3), (4, 65), (5, 5), (6, 55), (7, 59), (8, 63), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 68⟩ { target := .l104413, kept := #v[], arity := rfl, guard := some (Fin.last 67) }))))))))))))))))

def bytes_l1043f4 : List UInt8 :=
  [0x49, 0x83, 0xC7, 0x08, 0xBE, 0x58, 0x00, 0x00, 0x00, 0xB9, 0x08, 0x00, 0x00, 0x00, 0x4C, 0x89,
    0xF7, 0x4C, 0x89, 0xFA, 0x41, 0xB8, 0x07, 0x00, 0x00, 0x00, 0xE8, 0xFD, 0xFB, 0xFF, 0xFF]

theorem code_l1043f4 : ∀ x ∈ codeRange 0x1043f4 bytes_l1043f4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x43f4 31 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104413 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x104413 (addR64Imm8Effect 0x104413 13 0x12) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[13]
    (.letOp (n := 54) (.exec 0x104413 (fun s => s.RIP = 0x104413) (addR64Imm8Effect 0x104413 13 0x12) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 55) (.out 0x104417 (addR64Imm8Effect 0x104417 12 0x10) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[12]
    (.letOp (n := 56) (.exec 0x104417 (fun s => s.RIP = 0x104417) (addR64Imm8Effect 0x104417 12 0x10) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 57) (.out 0x10441b (incR64Effect 0x10441b 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[5]
    (.letOp (n := 58) (.exec 0x10441b (fun s => s.RIP = 0x10441b) (incR64Effect 0x10441b 5) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5]
    (.letOp (n := 59) (.out 0x10441e (cmpR64Imm8Effect 0x10441e 15 0x50) (EffectPart.reads (.flag .ZF) [.gpr 15] []) (.flag .ZF)) #v[15]
    (.letOp (n := 60) (.exec 0x10441e (fun s => s.RIP = 0x10441e) (cmpR64Imm8Effect 0x10441e 15 0x50) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 61) (.pure (condOp 4)) #v[59]
    (.terminate (.condBr (Fin.last 61) ⟨.l10446f, RegMap.args [(0, 0), (1, 1), (3, 3), (4, 4), (5, 57), (8, 8), (9, 9), (11, 11), (12, 55), (13, 53), (14, 14), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ ⟨.l104424, RegMap.args [(0, 0), (1, 1), (3, 3), (4, 4), (5, 57), (8, 8), (9, 9), (11, 11), (12, 55), (13, 53), (14, 14), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩))))))))))

def bytes_l104413 : List UInt8 :=
  [0x49, 0x83, 0xC5, 0x12, 0x49, 0x83, 0xC4, 0x10, 0x48, 0xFF, 0xC5, 0x49, 0x83, 0xFF, 0x50, 0x74,
    0x4B]

theorem code_l104413 : ∀ x ∈ codeRange 0x104413 bytes_l104413, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4413 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104424 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x104424 (movR32Imm32Effect 0x104424 5 6 0x58) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 54) (.exec 0x104424 (fun s => s.RIP = 0x104424) (movR32Imm32Effect 0x104424 5 6 0x58) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x104429 (movR64R64Effect 0x104429 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 56) (.exec 0x104429 (fun s => s.RIP = 0x104429) (movR64R64Effect 0x104429 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x10442c (movR64R64Effect 0x10442c 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15] []) (.reg (.gpr 2))) #v[15]
    (.letOp (n := 58) (.exec 0x10442c (fun s => s.RIP = 0x10442c) (movR64R64Effect 0x10442c 2 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 59) (.out 0x10442f (callEffect (fun _ => 0x103f30) 0x104434) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x10442f (PushPre 0x10442f 5) (callEffect (fun _ => 0x103f30) 0x104434) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x104434⟩) #v[]
    (.terminate (.call ⟨.l103f30, RegMap.args [(0, 0), (1, 1), (2, 57), (3, 3), (4, 59), (5, 5), (6, 53), (7, 55), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l104434, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l104424 : List UInt8 :=
  [0xBE, 0x58, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF7, 0x4C, 0x89, 0xFA, 0xE8, 0xFC, 0xFA, 0xFF, 0xFF]

theorem code_l104424 : ∀ x ∈ codeRange 0x104424 bytes_l104424, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4424 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104434 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x104434 (leaR64Effect 0x104434 7 (.sib 4 (some 12) 0 .none)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4, .gpr 12] []) (.reg (.gpr 7))) #v[4, 12]
    (.letOp (n := 54) (.exec 0x104434 (fun s => s.RIP = 0x104434) (leaR64Effect 0x104434 7 (.sib 4 (some 12) 0 .none)) (Reg.operands [.gpr 4, .gpr 12] [])) #v[4, 12]
    (.letOp (n := 55) (.out 0x104438 (addR64Imm8Effect 0x104438 7 0x8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 56) (.exec 0x104438 (fun s => s.RIP = 0x104438) (addR64Imm8Effect 0x104438 7 0x8) (Reg.operands [.gpr 7] [])) #v[53]
    (.letOp (n := 57) (.out 0x10443c (movR32Imm32Effect 0x10443c 5 6 0x8) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 58) (.exec 0x10443c (fun s => s.RIP = 0x10443c) (movR32Imm32Effect 0x10443c 5 6 0x8) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x104441 (callEffect (fun _ => 0x100b10) 0x104446) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x104441 (PushPre 0x104441 5) (callEffect (fun _ => 0x100b10) 0x104446) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x104446⟩) #v[]
    (.terminate (.call ⟨.l100b10, RegMap.args [(3, 3), (4, 59), (5, 5), (6, 57), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l104446, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l104434 : List UInt8 :=
  [0x4A, 0x8D, 0x3C, 0x24, 0x48, 0x83, 0xC7, 0x08, 0xBE, 0x08, 0x00, 0x00, 0x00, 0xE8, 0xCA, 0xC6,
    0xFF, 0xFF]

theorem code_l104434 : ∀ x ∈ codeRange 0x104434 bytes_l104434, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4434 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104446 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x104446 (StorePre 0x104446 6 (fun s => AddrMode.addr (.sib 4 (some 15) 1 (.d8 0x18)) s (0x104446 + BitVec.ofNat 64 6)) 2) (notMEffect 0x104446 6 16 (.sib 4 (some 15) 1 (.d8 0x18))) (Reg.operands [.gpr 4, .gpr 15] [])) #v[4, 15]
    (.letOp (n := 54) (.exec 0x10444c (StorePre 0x10444c 6 (fun s => AddrMode.addr (.sib 4 (some 15) 1 (.d8 0x1a)) s (0x10444c + BitVec.ofNat 64 6)) 2) (notMEffect 0x10444c 6 16 (.sib 4 (some 15) 1 (.d8 0x1a))) (Reg.operands [.gpr 4, .gpr 15] [])) #v[4, 15]
    (.letOp (n := 55) (.exec 0x104452 (StorePre 0x104452 6 (fun s => AddrMode.addr (.sib 4 (some 15) 1 (.d8 0x22)) s (0x104452 + BitVec.ofNat 64 6)) 2) (notMEffect 0x104452 6 16 (.sib 4 (some 15) 1 (.d8 0x22))) (Reg.operands [.gpr 4, .gpr 15] [])) #v[4, 15]
    (.letOp (n := 56) (.exec 0x104458 (StorePre 0x104458 6 (fun s => AddrMode.addr (.sib 4 (some 15) 1 (.d8 0x24)) s (0x104458 + BitVec.ofNat 64 6)) 2) (notMEffect 0x104458 6 16 (.sib 4 (some 15) 1 (.d8 0x24))) (Reg.operands [.gpr 4, .gpr 15] [])) #v[4, 15]
    (.letOp (n := 57) (.out 0x10445e (cmpR64Imm8Effect 0x10445e 5 0x8) (EffectPart.reads (.flag .CF) [.gpr 5] []) (.flag .CF)) #v[5]
    (.letOp (n := 58) (.exec 0x10445e (fun s => s.RIP = 0x10445e) (cmpR64Imm8Effect 0x10445e 5 0x8) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 59) (.pure (condOp 3)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l1043e0, RegMap.args [(0, 0), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l104468, RegMap.args [(0, 0), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l104446 : List UInt8 :=
  [0x66, 0x42, 0xF7, 0x54, 0x7C, 0x18, 0x66, 0x42, 0xF7, 0x54, 0x7C, 0x1A, 0x66, 0x42, 0xF7, 0x54,
    0x7C, 0x22, 0x66, 0x42, 0xF7, 0x54, 0x7C, 0x24, 0x48, 0x83, 0xFD, 0x08, 0x0F, 0x83, 0x78, 0xFF,
    0xFF, 0xFF]

theorem code_l104446 : ∀ x ∈ codeRange 0x104446 bytes_l104446, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4446 34 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l104468 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x104468 (StorePre 0x104468 5 (fun s => AddrMode.addr (.base 13 (.d8 0x10)) s (0x104468 + BitVec.ofNat 64 5)) 1) (xorM8Imm8Effect 0x104468 5 (.base 13 (.d8 0x10)) 0x80) (Reg.operands [.gpr 13] [])) #v[13]
    (.terminate (.br ⟨.l1043f4, RegMap.args [(0, 0), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 54⟩))

def bytes_l104468 : List UInt8 :=
  [0x41, 0x80, 0x75, 0x10, 0x80, 0xEB, 0x85]

theorem code_l104468 : ∀ x ∈ codeRange 0x104468 bytes_l104468, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4468 7 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

def b_l10446f_41 : Block Op Label signature Reg.count 1617 :=
  .letOp (n := 1617) (.out 0x105090 (notR32Effect 0x105090 2 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1553]
    (.letOp (n := 1618) (.exec 0x105090 (fun s => s.RIP = 0x105090) (notR32Effect 0x105090 2 1) (Reg.operands [.gpr 1] [])) #v[1553]
    (.letOp (n := 1619) (.exec 0x105092 (StorePre 0x105092 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa2)) s (0x105092 + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x105092 8 1 (.sib 4 none 0 (.d32 0xa2))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1617, 4]
    (.letOp (n := 1620) (.out 0x10509a (notR32Effect 0x10509a 2 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[1609]
    (.letOp (n := 1621) (.exec 0x10509a (fun s => s.RIP = 0x10509a) (notR32Effect 0x10509a 2 6) (Reg.operands [.gpr 6] [])) #v[1609]
    (.letOp (n := 1622) (.exec 0x10509c (StorePre 0x10509c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa4)) s (0x10509c + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x10509c 8 6 (.sib 4 none 0 (.d32 0xa4))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[1620, 4]
    (.letOp (n := 1623) (.exec 0x1050a4 (StorePre 0x1050a4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x1050a4 + BitVec.ofNat 64 8)) 2) (notMEffect 0x1050a4 8 16 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1624) (.exec 0x1050ac (StorePre 0x1050ac 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xaa)) s (0x1050ac + BitVec.ofNat 64 8)) 2) (notMEffect 0x1050ac 8 16 (.sib 4 none 0 (.d32 0xaa))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1625) (.exec 0x1050b4 (StorePre 0x1050b4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb2)) s (0x1050b4 + BitVec.ofNat 64 8)) 2) (notMEffect 0x1050b4 8 16 (.sib 4 none 0 (.d32 0xb2))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1626) (.exec 0x1050bc (StorePre 0x1050bc 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb4)) s (0x1050bc + BitVec.ofNat 64 8)) 2) (notMEffect 0x1050bc 8 16 (.sib 4 none 0 (.d32 0xb4))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1627) (.out 0x1050c4 (leaR64Effect 0x1050c4 6 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 1628) (.exec 0x1050c4 (fun s => s.RIP = 0x1050c4) (leaR64Effect 0x1050c4 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1629) (.out 0x1050c9 (movR32Imm32Effect 0x1050c9 5 2 0xb0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 1630) (.exec 0x1050c9 (fun s => s.RIP = 0x1050c9) (movR32Imm32Effect 0x1050c9 5 2 0xb0) (Reg.operands [] [])) #v[]
    (.letOp (n := 1631) (.out 0x1050ce (movR64M64Effect 0x1050ce 3 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 1632) (.exec 0x1050ce (LoadPre 0x1050ce (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x1050ce + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1050ce 3 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1633) (.out 0x1050d6 (movR64R64Effect 0x1050d6 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[1631]
    (.letOp (n := 1634) (.exec 0x1050d6 (fun s => s.RIP = 0x1050d6) (movR64R64Effect 0x1050d6 7 3) (Reg.operands [.gpr 3] [])) #v[1631]
    (.letOp (n := 1635) (.out 0x1050d9 (callEffect (callMemPtr 0x1050d9 (.rip 0xfc129)) (0x1050d9 + BitVec.ofNat 64 (callMemLen (.rip 0xfc129)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 1636) (.exec 0x1050d9 (GoesTo (CallMemPre 0x1050d9 (.rip 0xfc129)) (callEffect (callMemPtr 0x1050d9 (.rip 0xfc129)) (0x1050d9 + BitVec.ofNat 64 (callMemLen (.rip 0xfc129)))) 0x103f00) (callEffect (callMemPtr 0x1050d9 (.rip 0xfc129)) (0x1050d9 + BitVec.ofNat 64 (callMemLen (.rip 0xfc129)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1637) (.const ⟨64, 0x1050df⟩) #v[]
    (.terminate (.call ⟨.l103f00, RegMap.args [(0, 1603), (1, 1617), (2, 1629), (3, 1631), (4, 1635), (5, 1581), (6, 1627), (7, 1633), (8, 1531), (9, 1555), (10, 1575), (11, 1578), (12, 1611), (13, 1519), (14, 1584), (15, 1587), (22, 22), (39, 39), (50, 50), (51, 51)] 1638⟩ { target := .l1050df, kept := #v[], arity := rfl, guard := some (Fin.last 1637) }))))))))))))))))))))))

def bytes_l10446f_41 : List UInt8 :=
  [0xF7, 0xD1, 0x66, 0x89, 0x8C, 0x24, 0xA2, 0x00, 0x00, 0x00, 0xF7, 0xD6, 0x66, 0x89, 0xB4, 0x24,
    0xA4, 0x00, 0x00, 0x00, 0x66, 0xF7, 0x94, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x66, 0xF7, 0x94, 0x24,
    0xAA, 0x00, 0x00, 0x00, 0x66, 0xF7, 0x94, 0x24, 0xB2, 0x00, 0x00, 0x00, 0x66, 0xF7, 0x94, 0x24,
    0xB4, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x74, 0x24, 0x08, 0xBA, 0xB0, 0x00, 0x00, 0x00, 0x48, 0x8B,
    0x9C, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x48, 0x89, 0xDF, 0xFF, 0x15, 0x29, 0xC1, 0x0F, 0x00]

theorem code_l10446f_41 : ∀ x ∈ codeRange 0x105090 bytes_l10446f_41, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5090 79 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

def b_l10446f_40 : Block Op Label signature Reg.count 1587 :=
  .letOp (n := 1587) (.out 0x10502a (notR32Effect 0x10502a 3 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15] []) (.reg (.gpr 15))) #v[1088]
    (.letOp (n := 1588) (.exec 0x10502a (fun s => s.RIP = 0x10502a) (notR32Effect 0x10502a 3 15) (Reg.operands [.gpr 15] [])) #v[1088]
    (.letOp (n := 1589) (.exec 0x10502d (StorePre 0x10502d 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10502d + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x10502d 6 15 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[1587, 4]
    (.letOp (n := 1590) (.exec 0x105033 (StorePre 0x105033 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7a)) s (0x105033 + BitVec.ofNat 64 5)) 2) (notMEffect 0x105033 5 16 (.sib 4 none 0 (.d8 0x7a))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1591) (.out 0x105038 (movR32R32Effect 0x105038 2 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[1571]
    (.letOp (n := 1592) (.exec 0x105038 (fun s => s.RIP = 0x105038) (movR32R32Effect 0x105038 2 6 0) (Reg.operands [.gpr 0] [])) #v[1571]
    (.letOp (n := 1593) (.exec 0x10503a (StorePre 0x10503a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x82)) s (0x10503a + BitVec.ofNat 64 8)) 2) (notMEffect 0x10503a 8 16 (.sib 4 none 0 (.d32 0x82))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1594) (.out 0x105042 (shrR32Effect 0x105042 2 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[1591]
    (.letOp (n := 1595) (.exec 0x105042 (fun s => s.RIP = 0x105042) (shrR32Effect 0x105042 2 6 1) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1591]
    (.letOp (n := 1596) (.exec 0x105044 (StorePre 0x105044 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x84)) s (0x105044 + BitVec.ofNat 64 8)) 2) (notMEffect 0x105044 8 16 (.sib 4 none 0 (.d32 0x84))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1597) (.out 0x10504c (xorR32R32Effect 0x10504c 2 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[1594, 1571]
    (.letOp (n := 1598) (.exec 0x10504c (fun s => s.RIP = 0x10504c) (xorR32R32Effect 0x10504c 2 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[1594, 1571]
    (.letOp (n := 1599) (.exec 0x10504e (StorePre 0x10504e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10504e + BitVec.ofNat 64 8)) 2) (notMEffect 0x10504e 8 16 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1600) (.out 0x105056 (andR32Imm32Effect 0x105056 6 6 0x5050) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[1597]
    (.letOp (n := 1601) (.exec 0x105056 (fun s => s.RIP = 0x105056) (andR32Imm32Effect 0x105056 6 6 0x5050) (Reg.operands [.gpr 6] [])) #v[1597]
    (.letOp (n := 1602) (.exec 0x10505c (StorePre 0x10505c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x8a)) s (0x10505c + BitVec.ofNat 64 8)) 2) (notMEffect 0x10505c 8 16 (.sib 4 none 0 (.d32 0x8a))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1603) (.out 0x105064 (xorR32R32Effect 0x105064 2 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[1571, 1600]
    (.letOp (n := 1604) (.exec 0x105064 (fun s => s.RIP = 0x105064) (xorR32R32Effect 0x105064 2 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[1571, 1600]
    (.letOp (n := 1605) (.exec 0x105066 (StorePre 0x105066 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x92)) s (0x105066 + BitVec.ofNat 64 8)) 2) (notMEffect 0x105066 8 16 (.sib 4 none 0 (.d32 0x92))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1606) (.out 0x10506e (addR32R32Effect 0x10506e 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[1600, 1600]
    (.letOp (n := 1607) (.exec 0x10506e (fun s => s.RIP = 0x10506e) (addR32R32Effect 0x10506e 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[1600, 1600]
    (.letOp (n := 1608) (.exec 0x105070 (StorePre 0x105070 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x94)) s (0x105070 + BitVec.ofNat 64 8)) 2) (notMEffect 0x105070 8 16 (.sib 4 none 0 (.d32 0x94))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1609) (.out 0x105078 (xorR32R32Effect 0x105078 2 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[1606, 1603]
    (.letOp (n := 1610) (.exec 0x105078 (fun s => s.RIP = 0x105078) (xorR32R32Effect 0x105078 2 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[1606, 1603]
    (.letOp (n := 1611) (.out 0x10507a (notR32Effect 0x10507a 3 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[1335]
    (.letOp (n := 1612) (.exec 0x10507a (fun s => s.RIP = 0x10507a) (notR32Effect 0x10507a 3 12) (Reg.operands [.gpr 12] [])) #v[1335]
    (.letOp (n := 1613) (.exec 0x10507d (StorePre 0x10507d 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x10507d + BitVec.ofNat 64 9)) 2) (movM16R16Effect 0x10507d 9 12 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[1611, 4]
    (.letOp (n := 1614) (.out 0x105086 (notR32Effect 0x105086 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[1365]
    (.letOp (n := 1615) (.exec 0x105086 (fun s => s.RIP = 0x105086) (notR32Effect 0x105086 2 2) (Reg.operands [.gpr 2] [])) #v[1365]
    (.letOp (n := 1616) (.exec 0x105088 (StorePre 0x105088 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9a)) s (0x105088 + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x105088 8 2 (.sib 4 none 0 (.d32 0x9a))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[1614, 4]
    (b_l10446f_41))))))))))))))))))))))))))))))

def bytes_l10446f_40 : List UInt8 :=
  [0x41, 0xF7, 0xD7, 0x66, 0x44, 0x89, 0x7C, 0x24, 0x78, 0x66, 0xF7, 0x54, 0x24, 0x7A, 0x89, 0xC6,
    0x66, 0xF7, 0x94, 0x24, 0x82, 0x00, 0x00, 0x00, 0xD1, 0xEE, 0x66, 0xF7, 0x94, 0x24, 0x84, 0x00,
    0x00, 0x00, 0x31, 0xC6, 0x66, 0xF7, 0x94, 0x24, 0x88, 0x00, 0x00, 0x00, 0x81, 0xE6, 0x50, 0x50,
    0x00, 0x00, 0x66, 0xF7, 0x94, 0x24, 0x8A, 0x00, 0x00, 0x00, 0x31, 0xF0, 0x66, 0xF7, 0x94, 0x24,
    0x92, 0x00, 0x00, 0x00, 0x01, 0xF6, 0x66, 0xF7, 0x94, 0x24, 0x94, 0x00, 0x00, 0x00, 0x31, 0xC6,
    0x41, 0xF7, 0xD4, 0x66, 0x44, 0x89, 0xA4, 0x24, 0x98, 0x00, 0x00, 0x00, 0xF7, 0xD2, 0x66, 0x89,
    0x94, 0x24, 0x9A, 0x00, 0x00, 0x00] ++ bytes_l10446f_41

theorem code_l10446f_40 : ∀ x ∈ codeRange 0x10502a bytes_l10446f_40, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x502a 102 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10446f_41

def b_l10446f_39 : Block Op Label signature Reg.count 1555 :=
  .letOp (n := 1555) (.out 0x104fdd (notR32Effect 0x104fdd 3 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[709]
    (.letOp (n := 1556) (.exec 0x104fdd (fun s => s.RIP = 0x104fdd) (notR32Effect 0x104fdd 3 9) (Reg.operands [.gpr 9] [])) #v[709]
    (.letOp (n := 1557) (.exec 0x104fe0 (StorePre 0x104fe0 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x104fe0 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x104fe0 6 9 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[1555, 4]
    (.letOp (n := 1558) (.out 0x104fe6 (movR32R32Effect 0x104fe6 2 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[1492]
    (.letOp (n := 1559) (.exec 0x104fe6 (fun s => s.RIP = 0x104fe6) (movR32R32Effect 0x104fe6 2 0 3) (Reg.operands [.gpr 3] [])) #v[1492]
    (.letOp (n := 1560) (.out 0x104fe8 (shrR32Effect 0x104fe8 3 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[1558]
    (.letOp (n := 1561) (.exec 0x104fe8 (fun s => s.RIP = 0x104fe8) (shrR32Effect 0x104fe8 3 0 2) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1558]
    (.letOp (n := 1562) (.out 0x104feb (xorR32R32Effect 0x104feb 2 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[1560, 1492]
    (.letOp (n := 1563) (.exec 0x104feb (fun s => s.RIP = 0x104feb) (xorR32R32Effect 0x104feb 2 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[1560, 1492]
    (.letOp (n := 1564) (.out 0x104fed (andEaxImm32Effect 0x104fed 0x1320) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[1562]
    (.letOp (n := 1565) (.exec 0x104fed (fun s => s.RIP = 0x104fed) (andEaxImm32Effect 0x104fed 0x1320) (Reg.operands [.gpr 0] [])) #v[1562]
    (.letOp (n := 1566) (.out 0x104ff2 (xorR32R32Effect 0x104ff2 2 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0] []) (.reg (.gpr 3))) #v[1492, 1564]
    (.letOp (n := 1567) (.exec 0x104ff2 (fun s => s.RIP = 0x104ff2) (xorR32R32Effect 0x104ff2 2 3 0) (Reg.operands [.gpr 3, .gpr 0] [])) #v[1492, 1564]
    (.letOp (n := 1568) (.out 0x104ff4 (shlR32Effect 0x104ff4 3 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[1564]
    (.letOp (n := 1569) (.exec 0x104ff4 (fun s => s.RIP = 0x104ff4) (shlR32Effect 0x104ff4 3 0 2) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1564]
    (.letOp (n := 1570) (.exec 0x104ff7 (StorePre 0x104ff7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5a)) s (0x104ff7 + BitVec.ofNat 64 5)) 2) (notMEffect 0x104ff7 5 16 (.sib 4 none 0 (.d8 0x5a))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1571) (.out 0x104ffc (xorR32R32Effect 0x104ffc 2 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[1568, 1566]
    (.letOp (n := 1572) (.exec 0x104ffc (fun s => s.RIP = 0x104ffc) (xorR32R32Effect 0x104ffc 2 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[1568, 1566]
    (.letOp (n := 1573) (.exec 0x104ffe (StorePre 0x104ffe 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x62)) s (0x104ffe + BitVec.ofNat 64 5)) 2) (notMEffect 0x104ffe 5 16 (.sib 4 none 0 (.d8 0x62))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1574) (.exec 0x105003 (StorePre 0x105003 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x64)) s (0x105003 + BitVec.ofNat 64 5)) 2) (notMEffect 0x105003 5 16 (.sib 4 none 0 (.d8 0x64))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1575) (.out 0x105008 (notR32Effect 0x105008 3 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[942]
    (.letOp (n := 1576) (.exec 0x105008 (fun s => s.RIP = 0x105008) (notR32Effect 0x105008 3 10) (Reg.operands [.gpr 10] [])) #v[942]
    (.letOp (n := 1577) (.exec 0x10500b (StorePre 0x10500b 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x10500b + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x10500b 6 10 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[1575, 4]
    (.letOp (n := 1578) (.out 0x105011 (notR32Effect 0x105011 3 11) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11] []) (.reg (.gpr 11))) #v[958]
    (.letOp (n := 1579) (.exec 0x105011 (fun s => s.RIP = 0x105011) (notR32Effect 0x105011 3 11) (Reg.operands [.gpr 11] [])) #v[958]
    (.letOp (n := 1580) (.exec 0x105014 (StorePre 0x105014 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6a)) s (0x105014 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x105014 6 11 (.sib 4 none 0 (.d8 0x6a))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[1578, 4]
    (.letOp (n := 1581) (.out 0x10501a (notR32Effect 0x10501a 2 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5] []) (.reg (.gpr 5))) #v[1025]
    (.letOp (n := 1582) (.exec 0x10501a (fun s => s.RIP = 0x10501a) (notR32Effect 0x10501a 2 5) (Reg.operands [.gpr 5] [])) #v[1025]
    (.letOp (n := 1583) (.exec 0x10501c (StorePre 0x10501c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x72)) s (0x10501c + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x10501c 5 5 (.sib 4 none 0 (.d8 0x72))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[1581, 4]
    (.letOp (n := 1584) (.out 0x105021 (notR32Effect 0x105021 3 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14] []) (.reg (.gpr 14))) #v[1041]
    (.letOp (n := 1585) (.exec 0x105021 (fun s => s.RIP = 0x105021) (notR32Effect 0x105021 3 14) (Reg.operands [.gpr 14] [])) #v[1041]
    (.letOp (n := 1586) (.exec 0x105024 (StorePre 0x105024 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x74)) s (0x105024 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x105024 6 14 (.sib 4 none 0 (.d8 0x74))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[1584, 4]
    (b_l10446f_40))))))))))))))))))))))))))))))))

def bytes_l10446f_39 : List UInt8 :=
  [0x41, 0xF7, 0xD1, 0x66, 0x44, 0x89, 0x4C, 0x24, 0x58, 0x89, 0xD8, 0xC1, 0xE8, 0x02, 0x31, 0xD8,
    0x25, 0x20, 0x13, 0x00, 0x00, 0x31, 0xC3, 0xC1, 0xE0, 0x02, 0x66, 0xF7, 0x54, 0x24, 0x5A, 0x31,
    0xD8, 0x66, 0xF7, 0x54, 0x24, 0x62, 0x66, 0xF7, 0x54, 0x24, 0x64, 0x41, 0xF7, 0xD2, 0x66, 0x44,
    0x89, 0x54, 0x24, 0x68, 0x41, 0xF7, 0xD3, 0x66, 0x44, 0x89, 0x5C, 0x24, 0x6A, 0xF7, 0xD5, 0x66,
    0x89, 0x6C, 0x24, 0x72, 0x41, 0xF7, 0xD6, 0x66, 0x44, 0x89, 0x74, 0x24, 0x74] ++ bytes_l10446f_40

theorem code_l10446f_39 : ∀ x ∈ codeRange 0x104fdd bytes_l10446f_39, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x4fdd 77 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10446f_40

def b_l10446f_38 : Block Op Label signature Reg.count 1525 :=
  .letOp (n := 1525) (.out 0x104f91 (notR32Effect 0x104f91 2 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[399]
    (.letOp (n := 1526) (.exec 0x104f91 (fun s => s.RIP = 0x104f91) (notR32Effect 0x104f91 2 6) (Reg.operands [.gpr 6] [])) #v[399]
    (.letOp (n := 1527) (.exec 0x104f93 (StorePre 0x104f93 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x32)) s (0x104f93 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x104f93 5 6 (.sib 4 none 0 (.d8 0x32))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[1525, 4]
    (.letOp (n := 1528) (.out 0x104f98 (notR32Effect 0x104f98 2 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[415]
    (.letOp (n := 1529) (.exec 0x104f98 (fun s => s.RIP = 0x104f98) (notR32Effect 0x104f98 2 7) (Reg.operands [.gpr 7] [])) #v[415]
    (.letOp (n := 1530) (.exec 0x104f9a (StorePre 0x104f9a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x104f9a + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x104f9a 5 7 (.sib 4 none 0 (.d8 0x34))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[1528, 4]
    (.letOp (n := 1531) (.out 0x104f9f (notR32Effect 0x104f9f 3 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[462]
    (.letOp (n := 1532) (.exec 0x104f9f (fun s => s.RIP = 0x104f9f) (notR32Effect 0x104f9f 3 8) (Reg.operands [.gpr 8] [])) #v[462]
    (.letOp (n := 1533) (.exec 0x104fa2 (StorePre 0x104fa2 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x104fa2 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x104fa2 6 8 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[1531, 4]
    (.letOp (n := 1534) (.exec 0x104fa8 (StorePre 0x104fa8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3a)) s (0x104fa8 + BitVec.ofNat 64 5)) 2) (notMEffect 0x104fa8 5 16 (.sib 4 none 0 (.d8 0x3a))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1535) (.out 0x104fad (movR32R32Effect 0x104fad 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[1513]
    (.letOp (n := 1536) (.exec 0x104fad (fun s => s.RIP = 0x104fad) (movR32R32Effect 0x104fad 2 1 0) (Reg.operands [.gpr 0] [])) #v[1513]
    (.letOp (n := 1537) (.exec 0x104faf (StorePre 0x104faf 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x42)) s (0x104faf + BitVec.ofNat 64 5)) 2) (notMEffect 0x104faf 5 16 (.sib 4 none 0 (.d8 0x42))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1538) (.out 0x104fb4 (shrR32Effect 0x104fb4 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1535]
    (.letOp (n := 1539) (.exec 0x104fb4 (fun s => s.RIP = 0x104fb4) (shrR32Effect 0x104fb4 2 1 1) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1535]
    (.letOp (n := 1540) (.exec 0x104fb6 (StorePre 0x104fb6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x104fb6 + BitVec.ofNat 64 5)) 2) (notMEffect 0x104fb6 5 16 (.sib 4 none 0 (.d8 0x44))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1541) (.out 0x104fbb (xorR32R32Effect 0x104fbb 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1538, 1513]
    (.letOp (n := 1542) (.exec 0x104fbb (fun s => s.RIP = 0x104fbb) (xorR32R32Effect 0x104fbb 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1538, 1513]
    (.letOp (n := 1543) (.exec 0x104fbd (StorePre 0x104fbd 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x104fbd + BitVec.ofNat 64 5)) 2) (notMEffect 0x104fbd 5 16 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1544) (.out 0x104fc2 (andR32Imm32Effect 0x104fc2 6 1 0x5050) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1541]
    (.letOp (n := 1545) (.exec 0x104fc2 (fun s => s.RIP = 0x104fc2) (andR32Imm32Effect 0x104fc2 6 1 0x5050) (Reg.operands [.gpr 1] [])) #v[1541]
    (.letOp (n := 1546) (.exec 0x104fc8 (StorePre 0x104fc8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4a)) s (0x104fc8 + BitVec.ofNat 64 5)) 2) (notMEffect 0x104fc8 5 16 (.sib 4 none 0 (.d8 0x4a))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1547) (.out 0x104fcd (xorR32R32Effect 0x104fcd 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1513, 1544]
    (.letOp (n := 1548) (.exec 0x104fcd (fun s => s.RIP = 0x104fcd) (xorR32R32Effect 0x104fcd 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1513, 1544]
    (.letOp (n := 1549) (.exec 0x104fcf (StorePre 0x104fcf 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x52)) s (0x104fcf + BitVec.ofNat 64 5)) 2) (notMEffect 0x104fcf 5 16 (.sib 4 none 0 (.d8 0x52))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1550) (.out 0x104fd4 (addR32R32Effect 0x104fd4 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[1544, 1544]
    (.letOp (n := 1551) (.exec 0x104fd4 (fun s => s.RIP = 0x104fd4) (addR32R32Effect 0x104fd4 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[1544, 1544]
    (.letOp (n := 1552) (.exec 0x104fd6 (StorePre 0x104fd6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x54)) s (0x104fd6 + BitVec.ofNat 64 5)) 2) (notMEffect 0x104fd6 5 16 (.sib 4 none 0 (.d8 0x54))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1553) (.out 0x104fdb (xorR32R32Effect 0x104fdb 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1550, 1547]
    (.letOp (n := 1554) (.exec 0x104fdb (fun s => s.RIP = 0x104fdb) (xorR32R32Effect 0x104fdb 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1550, 1547]
    (b_l10446f_39))))))))))))))))))))))))))))))

def bytes_l10446f_38 : List UInt8 :=
  [0xF7, 0xD6, 0x66, 0x89, 0x74, 0x24, 0x32, 0xF7, 0xD7, 0x66, 0x89, 0x7C, 0x24, 0x34, 0x41, 0xF7,
    0xD0, 0x66, 0x44, 0x89, 0x44, 0x24, 0x38, 0x66, 0xF7, 0x54, 0x24, 0x3A, 0x89, 0xC1, 0x66, 0xF7,
    0x54, 0x24, 0x42, 0xD1, 0xE9, 0x66, 0xF7, 0x54, 0x24, 0x44, 0x31, 0xC1, 0x66, 0xF7, 0x54, 0x24,
    0x48, 0x81, 0xE1, 0x50, 0x50, 0x00, 0x00, 0x66, 0xF7, 0x54, 0x24, 0x4A, 0x31, 0xC8, 0x66, 0xF7,
    0x54, 0x24, 0x52, 0x01, 0xC9, 0x66, 0xF7, 0x54, 0x24, 0x54, 0x31, 0xC1] ++ bytes_l10446f_39

theorem code_l10446f_38 : ∀ x ∈ codeRange 0x104f91 bytes_l10446f_38, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x4f91 76 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10446f_39

def b_l10446f_37 : Block Op Label signature Reg.count 1492 :=
  .letOp (n := 1492) (.out 0x104f35 (movzxR32M16Effect 0x104f35 8 3 (.sib 4 none 0 (.d32 0xa4))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 1493) (.exec 0x104f35 (LoadPre 0x104f35 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa4)) s (0x104f35 + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x104f35 8 3 (.sib 4 none 0 (.d32 0xa4))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1494) (.exec 0x104f3d (StorePre 0x104f3d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa6)) s (0x104f3d + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x104f3d 8 0 (.sib 4 none 0 (.d32 0xa6))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1488, 4]
    (.letOp (n := 1495) (.out 0x104f45 (movR32M32LowEffect 0x104f45 0 (.sib 4 none 0 (.d32 0xbc))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1496) (.exec 0x104f45 (LoadPre 0x104f45 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xbc)) s (0x104f45 + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x104f45 0 (.sib 4 none 0 (.d32 0xbc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1497) (.out 0x104f4c (notR32Effect 0x104f4c 2 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[1495]
    (.letOp (n := 1498) (.exec 0x104f4c (fun s => s.RIP = 0x104f4c) (notR32Effect 0x104f4c 2 0) (Reg.operands [.gpr 0] [])) #v[1495]
    (.letOp (n := 1499) (.exec 0x104f4e (StorePre 0x104f4e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x104f4e + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x104f4e 5 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1497, 4]
    (.letOp (n := 1500) (.out 0x104f53 (movR32R32Effect 0x104f53 3 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[1490]
    (.letOp (n := 1501) (.exec 0x104f53 (fun s => s.RIP = 0x104f53) (movR32R32Effect 0x104f53 3 0 13) (Reg.operands [.gpr 13] [])) #v[1490]
    (.letOp (n := 1502) (.out 0x104f56 (shrR32Effect 0x104f56 3 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[1500]
    (.letOp (n := 1503) (.exec 0x104f56 (fun s => s.RIP = 0x104f56) (shrR32Effect 0x104f56 3 0 2) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1500]
    (.letOp (n := 1504) (.out 0x104f59 (xorR32R32Effect 0x104f59 3 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 13] []) (.reg (.gpr 0))) #v[1502, 1490]
    (.letOp (n := 1505) (.exec 0x104f59 (fun s => s.RIP = 0x104f59) (xorR32R32Effect 0x104f59 3 0 13) (Reg.operands [.gpr 0, .gpr 13] [])) #v[1502, 1490]
    (.letOp (n := 1506) (.out 0x104f5c (andEaxImm32Effect 0x104f5c 0x1320) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[1504]
    (.letOp (n := 1507) (.exec 0x104f5c (fun s => s.RIP = 0x104f5c) (andEaxImm32Effect 0x104f5c 0x1320) (Reg.operands [.gpr 0] [])) #v[1504]
    (.letOp (n := 1508) (.out 0x104f61 (xorR32R32Effect 0x104f61 3 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 0] []) (.reg (.gpr 13))) #v[1490, 1506]
    (.letOp (n := 1509) (.exec 0x104f61 (fun s => s.RIP = 0x104f61) (xorR32R32Effect 0x104f61 3 13 0) (Reg.operands [.gpr 13, .gpr 0] [])) #v[1490, 1506]
    (.letOp (n := 1510) (.out 0x104f64 (shlR32Effect 0x104f64 3 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[1506]
    (.letOp (n := 1511) (.exec 0x104f64 (fun s => s.RIP = 0x104f64) (shlR32Effect 0x104f64 3 0 2) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1506]
    (.letOp (n := 1512) (.exec 0x104f67 (StorePre 0x104f67 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1a)) s (0x104f67 + BitVec.ofNat 64 5)) 2) (notMEffect 0x104f67 5 16 (.sib 4 none 0 (.d8 0x1a))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1513) (.out 0x104f6c (xorR32R32Effect 0x104f6c 3 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 13] []) (.reg (.gpr 0))) #v[1510, 1508]
    (.letOp (n := 1514) (.exec 0x104f6c (fun s => s.RIP = 0x104f6c) (xorR32R32Effect 0x104f6c 3 0 13) (Reg.operands [.gpr 0, .gpr 13] [])) #v[1510, 1508]
    (.letOp (n := 1515) (.exec 0x104f6f (StorePre 0x104f6f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x22)) s (0x104f6f + BitVec.ofNat 64 5)) 2) (notMEffect 0x104f6f 5 16 (.sib 4 none 0 (.d8 0x22))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1516) (.exec 0x104f74 (StorePre 0x104f74 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x104f74 + BitVec.ofNat 64 5)) 2) (notMEffect 0x104f74 5 16 (.sib 4 none 0 (.d8 0x24))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1517) (.out 0x104f79 (movR32M32Effect 0x104f79 13 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 1518) (.exec 0x104f79 (LoadPre 0x104f79 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x104f79 + BitVec.ofNat 64 8)) 4) (movR32M32Effect 0x104f79 13 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1519) (.out 0x104f81 (notR32Effect 0x104f81 3 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[1517]
    (.letOp (n := 1520) (.exec 0x104f81 (fun s => s.RIP = 0x104f81) (notR32Effect 0x104f81 3 13) (Reg.operands [.gpr 13] [])) #v[1517]
    (.letOp (n := 1521) (.exec 0x104f84 (StorePre 0x104f84 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x104f84 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x104f84 6 13 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[1519, 4]
    (.letOp (n := 1522) (.out 0x104f8a (notR32Effect 0x104f8a 2 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[332]
    (.letOp (n := 1523) (.exec 0x104f8a (fun s => s.RIP = 0x104f8a) (notR32Effect 0x104f8a 2 1) (Reg.operands [.gpr 1] [])) #v[332]
    (.letOp (n := 1524) (.exec 0x104f8c (StorePre 0x104f8c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2a)) s (0x104f8c + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x104f8c 5 1 (.sib 4 none 0 (.d8 0x2a))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1522, 4]
    (b_l10446f_38)))))))))))))))))))))))))))))))))

def bytes_l10446f_37 : List UInt8 :=
  [0x0F, 0xB7, 0x9C, 0x24, 0xA4, 0x00, 0x00, 0x00, 0x66, 0x89, 0x84, 0x24, 0xA6, 0x00, 0x00, 0x00,
    0x8B, 0x84, 0x24, 0xBC, 0x00, 0x00, 0x00, 0xF7, 0xD0, 0x66, 0x89, 0x44, 0x24, 0x18, 0x44, 0x89,
    0xE8, 0xC1, 0xE8, 0x02, 0x44, 0x31, 0xE8, 0x25, 0x20, 0x13, 0x00, 0x00, 0x41, 0x31, 0xC5, 0xC1,
    0xE0, 0x02, 0x66, 0xF7, 0x54, 0x24, 0x1A, 0x44, 0x31, 0xE8, 0x66, 0xF7, 0x54, 0x24, 0x22, 0x66,
    0xF7, 0x54, 0x24, 0x24, 0x44, 0x8B, 0xAC, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x41, 0xF7, 0xD5, 0x66,
    0x44, 0x89, 0x6C, 0x24, 0x28, 0xF7, 0xD1, 0x66, 0x89, 0x4C, 0x24, 0x2A] ++ bytes_l10446f_38

theorem code_l10446f_37 : ∀ x ∈ codeRange 0x104f35 bytes_l10446f_37, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x4f35 92 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10446f_38

def b_l10446f_36 : Block Op Label signature Reg.count 1453 :=
  .letOp (n := 1453) (.out 0x104ee4 (xorR32R32Effect 0x104ee4 3 13 3) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 3] []) (.reg (.gpr 13))) #v[1443, 1451]
    (.letOp (n := 1454) (.exec 0x104ee4 (fun s => s.RIP = 0x104ee4) (xorR32R32Effect 0x104ee4 3 13 3) (Reg.operands [.gpr 13, .gpr 3] [])) #v[1443, 1451]
    (.letOp (n := 1455) (.out 0x104ee7 (addR32R32Effect 0x104ee7 2 3 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 3] []) (.reg (.gpr 3))) #v[1451, 1451]
    (.letOp (n := 1456) (.exec 0x104ee7 (fun s => s.RIP = 0x104ee7) (addR32R32Effect 0x104ee7 2 3 3) (Reg.operands [.gpr 3, .gpr 3] [])) #v[1451, 1451]
    (.letOp (n := 1457) (.out 0x104ee9 (xorR32R32Effect 0x104ee9 3 3 13) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 13] []) (.reg (.gpr 3))) #v[1455, 1453]
    (.letOp (n := 1458) (.exec 0x104ee9 (fun s => s.RIP = 0x104ee9) (xorR32R32Effect 0x104ee9 3 3 13) (Reg.operands [.gpr 3, .gpr 13] [])) #v[1455, 1453]
    (.letOp (n := 1459) (.exec 0x104eec (StorePre 0x104eec 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x104eec + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x104eec 8 3 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[1457, 4]
    (.letOp (n := 1460) (.out 0x104ef4 (movzxR32M16Effect 0x104ef4 8 3 (.sib 4 none 0 (.d32 0xa6))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 1461) (.exec 0x104ef4 (LoadPre 0x104ef4 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa6)) s (0x104ef4 + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x104ef4 8 3 (.sib 4 none 0 (.d32 0xa6))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1462) (.out 0x104efc (movR32R32Effect 0x104efc 3 13 3) (EffectPart.reads (.reg (.gpr 13)) [.gpr 3] []) (.reg (.gpr 13))) #v[1460]
    (.letOp (n := 1463) (.exec 0x104efc (fun s => s.RIP = 0x104efc) (movR32R32Effect 0x104efc 3 13 3) (Reg.operands [.gpr 3] [])) #v[1460]
    (.letOp (n := 1464) (.out 0x104eff (shrR32Effect 0x104eff 4 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[1462]
    (.letOp (n := 1465) (.exec 0x104eff (fun s => s.RIP = 0x104eff) (shrR32Effect 0x104eff 4 13 2) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1462]
    (.letOp (n := 1466) (.out 0x104f03 (xorR32R32Effect 0x104f03 3 13 3) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 3] []) (.reg (.gpr 13))) #v[1464, 1460]
    (.letOp (n := 1467) (.exec 0x104f03 (fun s => s.RIP = 0x104f03) (xorR32R32Effect 0x104f03 3 13 3) (Reg.operands [.gpr 13, .gpr 3] [])) #v[1464, 1460]
    (.letOp (n := 1468) (.out 0x104f06 (andR32Imm32Effect 0x104f06 7 13 0x1320) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[1466]
    (.letOp (n := 1469) (.exec 0x104f06 (fun s => s.RIP = 0x104f06) (andR32Imm32Effect 0x104f06 7 13 0x1320) (Reg.operands [.gpr 13] [])) #v[1466]
    (.letOp (n := 1470) (.out 0x104f0d (xorR32R32Effect 0x104f0d 3 3 13) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 13] []) (.reg (.gpr 3))) #v[1460, 1468]
    (.letOp (n := 1471) (.exec 0x104f0d (fun s => s.RIP = 0x104f0d) (xorR32R32Effect 0x104f0d 3 3 13) (Reg.operands [.gpr 3, .gpr 13] [])) #v[1460, 1468]
    (.letOp (n := 1472) (.out 0x104f10 (shlR32Effect 0x104f10 4 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[1468]
    (.letOp (n := 1473) (.exec 0x104f10 (fun s => s.RIP = 0x104f10) (shlR32Effect 0x104f10 4 13 2) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1468]
    (.letOp (n := 1474) (.out 0x104f14 (xorR32R32Effect 0x104f14 3 13 3) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 3] []) (.reg (.gpr 13))) #v[1472, 1470]
    (.letOp (n := 1475) (.exec 0x104f14 (fun s => s.RIP = 0x104f14) (xorR32R32Effect 0x104f14 3 13 3) (Reg.operands [.gpr 13, .gpr 3] [])) #v[1472, 1470]
    (.letOp (n := 1476) (.out 0x104f17 (movR32R32Effect 0x104f17 3 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[1474]
    (.letOp (n := 1477) (.exec 0x104f17 (fun s => s.RIP = 0x104f17) (movR32R32Effect 0x104f17 3 0 13) (Reg.operands [.gpr 13] [])) #v[1474]
    (.letOp (n := 1478) (.out 0x104f1a (shrR32Effect 0x104f1a 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[1476]
    (.letOp (n := 1479) (.exec 0x104f1a (fun s => s.RIP = 0x104f1a) (shrR32Effect 0x104f1a 2 0 1) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1476]
    (.letOp (n := 1480) (.out 0x104f1c (xorR32R32Effect 0x104f1c 3 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 13] []) (.reg (.gpr 0))) #v[1478, 1474]
    (.letOp (n := 1481) (.exec 0x104f1c (fun s => s.RIP = 0x104f1c) (xorR32R32Effect 0x104f1c 3 0 13) (Reg.operands [.gpr 0, .gpr 13] [])) #v[1478, 1474]
    (.letOp (n := 1482) (.out 0x104f1f (andEaxImm32Effect 0x104f1f 0x5050) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[1480]
    (.letOp (n := 1483) (.exec 0x104f1f (fun s => s.RIP = 0x104f1f) (andEaxImm32Effect 0x104f1f 0x5050) (Reg.operands [.gpr 0] [])) #v[1480]
    (.letOp (n := 1484) (.out 0x104f24 (xorR32R32Effect 0x104f24 3 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 0] []) (.reg (.gpr 13))) #v[1474, 1482]
    (.letOp (n := 1485) (.exec 0x104f24 (fun s => s.RIP = 0x104f24) (xorR32R32Effect 0x104f24 3 13 0) (Reg.operands [.gpr 13, .gpr 0] [])) #v[1474, 1482]
    (.letOp (n := 1486) (.out 0x104f27 (addR32R32Effect 0x104f27 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[1482, 1482]
    (.letOp (n := 1487) (.exec 0x104f27 (fun s => s.RIP = 0x104f27) (addR32R32Effect 0x104f27 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[1482, 1482]
    (.letOp (n := 1488) (.out 0x104f29 (xorR32R32Effect 0x104f29 3 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 13] []) (.reg (.gpr 0))) #v[1486, 1484]
    (.letOp (n := 1489) (.exec 0x104f29 (fun s => s.RIP = 0x104f29) (xorR32R32Effect 0x104f29 3 0 13) (Reg.operands [.gpr 0, .gpr 13] [])) #v[1486, 1484]
    (.letOp (n := 1490) (.out 0x104f2c (movzxR32M16Effect 0x104f2c 9 13 (.sib 4 none 0 (.d32 0xa2))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 1491) (.exec 0x104f2c (LoadPre 0x104f2c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa2)) s (0x104f2c + BitVec.ofNat 64 9)) 2) (movzxR32M16Effect 0x104f2c 9 13 (.sib 4 none 0 (.d32 0xa2))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l10446f_37)))))))))))))))))))))))))))))))))))))))

def bytes_l10446f_36 : List UInt8 :=
  [0x41, 0x31, 0xDD, 0x01, 0xDB, 0x44, 0x31, 0xEB, 0x66, 0x89, 0x9C, 0x24, 0xA0, 0x00, 0x00, 0x00,
    0x0F, 0xB7, 0x9C, 0x24, 0xA6, 0x00, 0x00, 0x00, 0x41, 0x89, 0xDD, 0x41, 0xC1, 0xED, 0x02, 0x41,
    0x31, 0xDD, 0x41, 0x81, 0xE5, 0x20, 0x13, 0x00, 0x00, 0x44, 0x31, 0xEB, 0x41, 0xC1, 0xE5, 0x02,
    0x41, 0x31, 0xDD, 0x44, 0x89, 0xE8, 0xD1, 0xE8, 0x44, 0x31, 0xE8, 0x25, 0x50, 0x50, 0x00, 0x00,
    0x41, 0x31, 0xC5, 0x01, 0xC0, 0x44, 0x31, 0xE8, 0x44, 0x0F, 0xB7, 0xAC, 0x24, 0xA2, 0x00, 0x00,
    0x00] ++ bytes_l10446f_37

theorem code_l10446f_36 : ∀ x ∈ codeRange 0x104ee4 bytes_l10446f_36, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x4ee4 81 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10446f_37

def b_l10446f_35 : Block Op Label signature Reg.count 1414 :=
  .letOp (n := 1414) (.out 0x104e95 (movR32R32Effect 0x104e95 3 3 13) (EffectPart.reads (.reg (.gpr 3)) [.gpr 13] []) (.reg (.gpr 3))) #v[1412]
    (.letOp (n := 1415) (.exec 0x104e95 (fun s => s.RIP = 0x104e95) (movR32R32Effect 0x104e95 3 3 13) (Reg.operands [.gpr 13] [])) #v[1412]
    (.letOp (n := 1416) (.out 0x104e98 (shrR32Effect 0x104e98 2 3 1) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[1414]
    (.letOp (n := 1417) (.exec 0x104e98 (fun s => s.RIP = 0x104e98) (shrR32Effect 0x104e98 2 3 1) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1414]
    (.letOp (n := 1418) (.out 0x104e9a (xorR32R32Effect 0x104e9a 3 3 13) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 13] []) (.reg (.gpr 3))) #v[1416, 1412]
    (.letOp (n := 1419) (.exec 0x104e9a (fun s => s.RIP = 0x104e9a) (xorR32R32Effect 0x104e9a 3 3 13) (Reg.operands [.gpr 3, .gpr 13] [])) #v[1416, 1412]
    (.letOp (n := 1420) (.out 0x104e9d (andR32Imm32Effect 0x104e9d 6 3 0x5050) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[1418]
    (.letOp (n := 1421) (.exec 0x104e9d (fun s => s.RIP = 0x104e9d) (andR32Imm32Effect 0x104e9d 6 3 0x5050) (Reg.operands [.gpr 3] [])) #v[1418]
    (.letOp (n := 1422) (.out 0x104ea3 (xorR32R32Effect 0x104ea3 3 13 3) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 3] []) (.reg (.gpr 13))) #v[1412, 1420]
    (.letOp (n := 1423) (.exec 0x104ea3 (fun s => s.RIP = 0x104ea3) (xorR32R32Effect 0x104ea3 3 13 3) (Reg.operands [.gpr 13, .gpr 3] [])) #v[1412, 1420]
    (.letOp (n := 1424) (.out 0x104ea6 (addR32R32Effect 0x104ea6 2 3 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 3] []) (.reg (.gpr 3))) #v[1420, 1420]
    (.letOp (n := 1425) (.exec 0x104ea6 (fun s => s.RIP = 0x104ea6) (addR32R32Effect 0x104ea6 2 3 3) (Reg.operands [.gpr 3, .gpr 3] [])) #v[1420, 1420]
    (.letOp (n := 1426) (.out 0x104ea8 (xorR32R32Effect 0x104ea8 3 3 13) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 13] []) (.reg (.gpr 3))) #v[1424, 1422]
    (.letOp (n := 1427) (.exec 0x104ea8 (fun s => s.RIP = 0x104ea8) (xorR32R32Effect 0x104ea8 3 3 13) (Reg.operands [.gpr 3, .gpr 13] [])) #v[1424, 1422]
    (.letOp (n := 1428) (.exec 0x104eab (StorePre 0x104eab 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9e)) s (0x104eab + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x104eab 8 3 (.sib 4 none 0 (.d32 0x9e))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[1426, 4]
    (.letOp (n := 1429) (.out 0x104eb3 (movzxR32M16Effect 0x104eb3 8 3 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 1430) (.exec 0x104eb3 (LoadPre 0x104eb3 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x104eb3 + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x104eb3 8 3 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1431) (.out 0x104ebb (movR32R32Effect 0x104ebb 3 13 3) (EffectPart.reads (.reg (.gpr 13)) [.gpr 3] []) (.reg (.gpr 13))) #v[1429]
    (.letOp (n := 1432) (.exec 0x104ebb (fun s => s.RIP = 0x104ebb) (movR32R32Effect 0x104ebb 3 13 3) (Reg.operands [.gpr 3] [])) #v[1429]
    (.letOp (n := 1433) (.out 0x104ebe (shrR32Effect 0x104ebe 4 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[1431]
    (.letOp (n := 1434) (.exec 0x104ebe (fun s => s.RIP = 0x104ebe) (shrR32Effect 0x104ebe 4 13 2) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1431]
    (.letOp (n := 1435) (.out 0x104ec2 (xorR32R32Effect 0x104ec2 3 13 3) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 3] []) (.reg (.gpr 13))) #v[1433, 1429]
    (.letOp (n := 1436) (.exec 0x104ec2 (fun s => s.RIP = 0x104ec2) (xorR32R32Effect 0x104ec2 3 13 3) (Reg.operands [.gpr 13, .gpr 3] [])) #v[1433, 1429]
    (.letOp (n := 1437) (.out 0x104ec5 (andR32Imm32Effect 0x104ec5 7 13 0x1320) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[1435]
    (.letOp (n := 1438) (.exec 0x104ec5 (fun s => s.RIP = 0x104ec5) (andR32Imm32Effect 0x104ec5 7 13 0x1320) (Reg.operands [.gpr 13] [])) #v[1435]
    (.letOp (n := 1439) (.out 0x104ecc (xorR32R32Effect 0x104ecc 3 3 13) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 13] []) (.reg (.gpr 3))) #v[1429, 1437]
    (.letOp (n := 1440) (.exec 0x104ecc (fun s => s.RIP = 0x104ecc) (xorR32R32Effect 0x104ecc 3 3 13) (Reg.operands [.gpr 3, .gpr 13] [])) #v[1429, 1437]
    (.letOp (n := 1441) (.out 0x104ecf (shlR32Effect 0x104ecf 4 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[1437]
    (.letOp (n := 1442) (.exec 0x104ecf (fun s => s.RIP = 0x104ecf) (shlR32Effect 0x104ecf 4 13 2) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1437]
    (.letOp (n := 1443) (.out 0x104ed3 (xorR32R32Effect 0x104ed3 3 13 3) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 3] []) (.reg (.gpr 13))) #v[1441, 1439]
    (.letOp (n := 1444) (.exec 0x104ed3 (fun s => s.RIP = 0x104ed3) (xorR32R32Effect 0x104ed3 3 13 3) (Reg.operands [.gpr 13, .gpr 3] [])) #v[1441, 1439]
    (.letOp (n := 1445) (.out 0x104ed6 (movR32R32Effect 0x104ed6 3 3 13) (EffectPart.reads (.reg (.gpr 3)) [.gpr 13] []) (.reg (.gpr 3))) #v[1443]
    (.letOp (n := 1446) (.exec 0x104ed6 (fun s => s.RIP = 0x104ed6) (movR32R32Effect 0x104ed6 3 3 13) (Reg.operands [.gpr 13] [])) #v[1443]
    (.letOp (n := 1447) (.out 0x104ed9 (shrR32Effect 0x104ed9 2 3 1) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[1445]
    (.letOp (n := 1448) (.exec 0x104ed9 (fun s => s.RIP = 0x104ed9) (shrR32Effect 0x104ed9 2 3 1) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1445]
    (.letOp (n := 1449) (.out 0x104edb (xorR32R32Effect 0x104edb 3 3 13) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 13] []) (.reg (.gpr 3))) #v[1447, 1443]
    (.letOp (n := 1450) (.exec 0x104edb (fun s => s.RIP = 0x104edb) (xorR32R32Effect 0x104edb 3 3 13) (Reg.operands [.gpr 3, .gpr 13] [])) #v[1447, 1443]
    (.letOp (n := 1451) (.out 0x104ede (andR32Imm32Effect 0x104ede 6 3 0x5050) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[1449]
    (.letOp (n := 1452) (.exec 0x104ede (fun s => s.RIP = 0x104ede) (andR32Imm32Effect 0x104ede 6 3 0x5050) (Reg.operands [.gpr 3] [])) #v[1449]
    (b_l10446f_36)))))))))))))))))))))))))))))))))))))))

def bytes_l10446f_35 : List UInt8 :=
  [0x44, 0x89, 0xEB, 0xD1, 0xEB, 0x44, 0x31, 0xEB, 0x81, 0xE3, 0x50, 0x50, 0x00, 0x00, 0x41, 0x31,
    0xDD, 0x01, 0xDB, 0x44, 0x31, 0xEB, 0x66, 0x89, 0x9C, 0x24, 0x9E, 0x00, 0x00, 0x00, 0x0F, 0xB7,
    0x9C, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x41, 0x89, 0xDD, 0x41, 0xC1, 0xED, 0x02, 0x41, 0x31, 0xDD,
    0x41, 0x81, 0xE5, 0x20, 0x13, 0x00, 0x00, 0x44, 0x31, 0xEB, 0x41, 0xC1, 0xE5, 0x02, 0x41, 0x31,
    0xDD, 0x44, 0x89, 0xEB, 0xD1, 0xEB, 0x44, 0x31, 0xEB, 0x81, 0xE3, 0x50, 0x50, 0x00, 0x00] ++ bytes_l10446f_36

theorem code_l10446f_35 : ∀ x ∈ codeRange 0x104e95 bytes_l10446f_35, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x4e95 79 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10446f_36

def b_l10446f_34 : Block Op Label signature Reg.count 1375 :=
  .letOp (n := 1375) (.out 0x104e43 (andR32Imm32Effect 0x104e43 7 13 0x1320) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[1373]
    (.letOp (n := 1376) (.exec 0x104e43 (fun s => s.RIP = 0x104e43) (andR32Imm32Effect 0x104e43 7 13 0x1320) (Reg.operands [.gpr 13] [])) #v[1373]
    (.letOp (n := 1377) (.out 0x104e4a (xorR32R32Effect 0x104e4a 3 3 13) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 13] []) (.reg (.gpr 3))) #v[1367, 1375]
    (.letOp (n := 1378) (.exec 0x104e4a (fun s => s.RIP = 0x104e4a) (xorR32R32Effect 0x104e4a 3 3 13) (Reg.operands [.gpr 3, .gpr 13] [])) #v[1367, 1375]
    (.letOp (n := 1379) (.out 0x104e4d (shlR32Effect 0x104e4d 4 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[1375]
    (.letOp (n := 1380) (.exec 0x104e4d (fun s => s.RIP = 0x104e4d) (shlR32Effect 0x104e4d 4 13 2) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1375]
    (.letOp (n := 1381) (.out 0x104e51 (xorR32R32Effect 0x104e51 3 13 3) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 3] []) (.reg (.gpr 13))) #v[1379, 1377]
    (.letOp (n := 1382) (.exec 0x104e51 (fun s => s.RIP = 0x104e51) (xorR32R32Effect 0x104e51 3 13 3) (Reg.operands [.gpr 13, .gpr 3] [])) #v[1379, 1377]
    (.letOp (n := 1383) (.out 0x104e54 (movR32R32Effect 0x104e54 3 3 13) (EffectPart.reads (.reg (.gpr 3)) [.gpr 13] []) (.reg (.gpr 3))) #v[1381]
    (.letOp (n := 1384) (.exec 0x104e54 (fun s => s.RIP = 0x104e54) (movR32R32Effect 0x104e54 3 3 13) (Reg.operands [.gpr 13] [])) #v[1381]
    (.letOp (n := 1385) (.out 0x104e57 (shrR32Effect 0x104e57 2 3 1) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[1383]
    (.letOp (n := 1386) (.exec 0x104e57 (fun s => s.RIP = 0x104e57) (shrR32Effect 0x104e57 2 3 1) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1383]
    (.letOp (n := 1387) (.out 0x104e59 (xorR32R32Effect 0x104e59 3 3 13) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 13] []) (.reg (.gpr 3))) #v[1385, 1381]
    (.letOp (n := 1388) (.exec 0x104e59 (fun s => s.RIP = 0x104e59) (xorR32R32Effect 0x104e59 3 3 13) (Reg.operands [.gpr 3, .gpr 13] [])) #v[1385, 1381]
    (.letOp (n := 1389) (.out 0x104e5c (andR32Imm32Effect 0x104e5c 6 3 0x5050) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[1387]
    (.letOp (n := 1390) (.exec 0x104e5c (fun s => s.RIP = 0x104e5c) (andR32Imm32Effect 0x104e5c 6 3 0x5050) (Reg.operands [.gpr 3] [])) #v[1387]
    (.letOp (n := 1391) (.out 0x104e62 (xorR32R32Effect 0x104e62 3 13 3) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 3] []) (.reg (.gpr 13))) #v[1381, 1389]
    (.letOp (n := 1392) (.exec 0x104e62 (fun s => s.RIP = 0x104e62) (xorR32R32Effect 0x104e62 3 13 3) (Reg.operands [.gpr 13, .gpr 3] [])) #v[1381, 1389]
    (.letOp (n := 1393) (.out 0x104e65 (addR32R32Effect 0x104e65 2 3 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 3] []) (.reg (.gpr 3))) #v[1389, 1389]
    (.letOp (n := 1394) (.exec 0x104e65 (fun s => s.RIP = 0x104e65) (addR32R32Effect 0x104e65 2 3 3) (Reg.operands [.gpr 3, .gpr 3] [])) #v[1389, 1389]
    (.letOp (n := 1395) (.out 0x104e67 (xorR32R32Effect 0x104e67 3 3 13) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 13] []) (.reg (.gpr 3))) #v[1393, 1391]
    (.letOp (n := 1396) (.exec 0x104e67 (fun s => s.RIP = 0x104e67) (xorR32R32Effect 0x104e67 3 3 13) (Reg.operands [.gpr 3, .gpr 13] [])) #v[1393, 1391]
    (.letOp (n := 1397) (.exec 0x104e6a (StorePre 0x104e6a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9c)) s (0x104e6a + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x104e6a 8 3 (.sib 4 none 0 (.d32 0x9c))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[1395, 4]
    (.letOp (n := 1398) (.out 0x104e72 (movzxR32M16Effect 0x104e72 8 3 (.sib 4 none 0 (.d32 0x9e))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 1399) (.exec 0x104e72 (LoadPre 0x104e72 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9e)) s (0x104e72 + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x104e72 8 3 (.sib 4 none 0 (.d32 0x9e))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1400) (.out 0x104e7a (movR32R32Effect 0x104e7a 3 13 3) (EffectPart.reads (.reg (.gpr 13)) [.gpr 3] []) (.reg (.gpr 13))) #v[1398]
    (.letOp (n := 1401) (.exec 0x104e7a (fun s => s.RIP = 0x104e7a) (movR32R32Effect 0x104e7a 3 13 3) (Reg.operands [.gpr 3] [])) #v[1398]
    (.letOp (n := 1402) (.out 0x104e7d (shrR32Effect 0x104e7d 4 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[1400]
    (.letOp (n := 1403) (.exec 0x104e7d (fun s => s.RIP = 0x104e7d) (shrR32Effect 0x104e7d 4 13 2) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1400]
    (.letOp (n := 1404) (.out 0x104e81 (xorR32R32Effect 0x104e81 3 13 3) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 3] []) (.reg (.gpr 13))) #v[1402, 1398]
    (.letOp (n := 1405) (.exec 0x104e81 (fun s => s.RIP = 0x104e81) (xorR32R32Effect 0x104e81 3 13 3) (Reg.operands [.gpr 13, .gpr 3] [])) #v[1402, 1398]
    (.letOp (n := 1406) (.out 0x104e84 (andR32Imm32Effect 0x104e84 7 13 0x1320) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[1404]
    (.letOp (n := 1407) (.exec 0x104e84 (fun s => s.RIP = 0x104e84) (andR32Imm32Effect 0x104e84 7 13 0x1320) (Reg.operands [.gpr 13] [])) #v[1404]
    (.letOp (n := 1408) (.out 0x104e8b (xorR32R32Effect 0x104e8b 3 3 13) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 13] []) (.reg (.gpr 3))) #v[1398, 1406]
    (.letOp (n := 1409) (.exec 0x104e8b (fun s => s.RIP = 0x104e8b) (xorR32R32Effect 0x104e8b 3 3 13) (Reg.operands [.gpr 3, .gpr 13] [])) #v[1398, 1406]
    (.letOp (n := 1410) (.out 0x104e8e (shlR32Effect 0x104e8e 4 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[1406]
    (.letOp (n := 1411) (.exec 0x104e8e (fun s => s.RIP = 0x104e8e) (shlR32Effect 0x104e8e 4 13 2) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1406]
    (.letOp (n := 1412) (.out 0x104e92 (xorR32R32Effect 0x104e92 3 13 3) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 3] []) (.reg (.gpr 13))) #v[1410, 1408]
    (.letOp (n := 1413) (.exec 0x104e92 (fun s => s.RIP = 0x104e92) (xorR32R32Effect 0x104e92 3 13 3) (Reg.operands [.gpr 13, .gpr 3] [])) #v[1410, 1408]
    (b_l10446f_35)))))))))))))))))))))))))))))))))))))))

def bytes_l10446f_34 : List UInt8 :=
  [0x41, 0x81, 0xE5, 0x20, 0x13, 0x00, 0x00, 0x44, 0x31, 0xEB, 0x41, 0xC1, 0xE5, 0x02, 0x41, 0x31,
    0xDD, 0x44, 0x89, 0xEB, 0xD1, 0xEB, 0x44, 0x31, 0xEB, 0x81, 0xE3, 0x50, 0x50, 0x00, 0x00, 0x41,
    0x31, 0xDD, 0x01, 0xDB, 0x44, 0x31, 0xEB, 0x66, 0x89, 0x9C, 0x24, 0x9C, 0x00, 0x00, 0x00, 0x0F,
    0xB7, 0x9C, 0x24, 0x9E, 0x00, 0x00, 0x00, 0x41, 0x89, 0xDD, 0x41, 0xC1, 0xED, 0x02, 0x41, 0x31,
    0xDD, 0x41, 0x81, 0xE5, 0x20, 0x13, 0x00, 0x00, 0x44, 0x31, 0xEB, 0x41, 0xC1, 0xE5, 0x02, 0x41,
    0x31, 0xDD] ++ bytes_l10446f_35

theorem code_l10446f_34 : ∀ x ∈ codeRange 0x104e43 bytes_l10446f_34, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x4e43 82 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10446f_35

def b_l10446f_33 : Block Op Label signature Reg.count 1335 :=
  .letOp (n := 1335) (.out 0x104df5 (xorR32R32Effect 0x104df5 3 12 13) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 13] []) (.reg (.gpr 12))) #v[1333, 1331]
    (.letOp (n := 1336) (.exec 0x104df5 (fun s => s.RIP = 0x104df5) (xorR32R32Effect 0x104df5 3 12 13) (Reg.operands [.gpr 12, .gpr 13] [])) #v[1333, 1331]
    (.letOp (n := 1337) (.out 0x104df8 (movzxR32M16Effect 0x104df8 8 3 (.sib 4 none 0 (.d32 0x9a))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 1338) (.exec 0x104df8 (LoadPre 0x104df8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9a)) s (0x104df8 + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x104df8 8 3 (.sib 4 none 0 (.d32 0x9a))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1339) (.out 0x104e00 (movR32R32Effect 0x104e00 3 13 3) (EffectPart.reads (.reg (.gpr 13)) [.gpr 3] []) (.reg (.gpr 13))) #v[1337]
    (.letOp (n := 1340) (.exec 0x104e00 (fun s => s.RIP = 0x104e00) (movR32R32Effect 0x104e00 3 13 3) (Reg.operands [.gpr 3] [])) #v[1337]
    (.letOp (n := 1341) (.out 0x104e03 (shrR32Effect 0x104e03 4 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[1339]
    (.letOp (n := 1342) (.exec 0x104e03 (fun s => s.RIP = 0x104e03) (shrR32Effect 0x104e03 4 13 2) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1339]
    (.letOp (n := 1343) (.out 0x104e07 (xorR32R32Effect 0x104e07 3 13 3) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 3] []) (.reg (.gpr 13))) #v[1341, 1337]
    (.letOp (n := 1344) (.exec 0x104e07 (fun s => s.RIP = 0x104e07) (xorR32R32Effect 0x104e07 3 13 3) (Reg.operands [.gpr 13, .gpr 3] [])) #v[1341, 1337]
    (.letOp (n := 1345) (.out 0x104e0a (andR32Imm32Effect 0x104e0a 7 13 0x1320) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[1343]
    (.letOp (n := 1346) (.exec 0x104e0a (fun s => s.RIP = 0x104e0a) (andR32Imm32Effect 0x104e0a 7 13 0x1320) (Reg.operands [.gpr 13] [])) #v[1343]
    (.letOp (n := 1347) (.out 0x104e11 (xorR32R32Effect 0x104e11 3 3 13) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 13] []) (.reg (.gpr 3))) #v[1337, 1345]
    (.letOp (n := 1348) (.exec 0x104e11 (fun s => s.RIP = 0x104e11) (xorR32R32Effect 0x104e11 3 3 13) (Reg.operands [.gpr 3, .gpr 13] [])) #v[1337, 1345]
    (.letOp (n := 1349) (.out 0x104e14 (shlR32Effect 0x104e14 4 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[1345]
    (.letOp (n := 1350) (.exec 0x104e14 (fun s => s.RIP = 0x104e14) (shlR32Effect 0x104e14 4 13 2) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1345]
    (.letOp (n := 1351) (.out 0x104e18 (xorR32R32Effect 0x104e18 3 13 3) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 3] []) (.reg (.gpr 13))) #v[1349, 1347]
    (.letOp (n := 1352) (.exec 0x104e18 (fun s => s.RIP = 0x104e18) (xorR32R32Effect 0x104e18 3 13 3) (Reg.operands [.gpr 13, .gpr 3] [])) #v[1349, 1347]
    (.letOp (n := 1353) (.out 0x104e1b (movR32R32Effect 0x104e1b 3 2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13] []) (.reg (.gpr 2))) #v[1351]
    (.letOp (n := 1354) (.exec 0x104e1b (fun s => s.RIP = 0x104e1b) (movR32R32Effect 0x104e1b 3 2 13) (Reg.operands [.gpr 13] [])) #v[1351]
    (.letOp (n := 1355) (.out 0x104e1e (shrR32Effect 0x104e1e 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[1353]
    (.letOp (n := 1356) (.exec 0x104e1e (fun s => s.RIP = 0x104e1e) (shrR32Effect 0x104e1e 2 2 1) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1353]
    (.letOp (n := 1357) (.out 0x104e20 (xorR32R32Effect 0x104e20 3 2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 13] []) (.reg (.gpr 2))) #v[1355, 1351]
    (.letOp (n := 1358) (.exec 0x104e20 (fun s => s.RIP = 0x104e20) (xorR32R32Effect 0x104e20 3 2 13) (Reg.operands [.gpr 2, .gpr 13] [])) #v[1355, 1351]
    (.letOp (n := 1359) (.out 0x104e23 (andR32Imm32Effect 0x104e23 6 2 0x5050) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[1357]
    (.letOp (n := 1360) (.exec 0x104e23 (fun s => s.RIP = 0x104e23) (andR32Imm32Effect 0x104e23 6 2 0x5050) (Reg.operands [.gpr 2] [])) #v[1357]
    (.letOp (n := 1361) (.out 0x104e29 (xorR32R32Effect 0x104e29 3 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 2] []) (.reg (.gpr 13))) #v[1351, 1359]
    (.letOp (n := 1362) (.exec 0x104e29 (fun s => s.RIP = 0x104e29) (xorR32R32Effect 0x104e29 3 13 2) (Reg.operands [.gpr 13, .gpr 2] [])) #v[1351, 1359]
    (.letOp (n := 1363) (.out 0x104e2c (addR32R32Effect 0x104e2c 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[1359, 1359]
    (.letOp (n := 1364) (.exec 0x104e2c (fun s => s.RIP = 0x104e2c) (addR32R32Effect 0x104e2c 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[1359, 1359]
    (.letOp (n := 1365) (.out 0x104e2e (xorR32R32Effect 0x104e2e 3 2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 13] []) (.reg (.gpr 2))) #v[1363, 1361]
    (.letOp (n := 1366) (.exec 0x104e2e (fun s => s.RIP = 0x104e2e) (xorR32R32Effect 0x104e2e 3 2 13) (Reg.operands [.gpr 2, .gpr 13] [])) #v[1363, 1361]
    (.letOp (n := 1367) (.out 0x104e31 (movzxR32M16Effect 0x104e31 8 3 (.sib 4 none 0 (.d32 0x9c))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 1368) (.exec 0x104e31 (LoadPre 0x104e31 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9c)) s (0x104e31 + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x104e31 8 3 (.sib 4 none 0 (.d32 0x9c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1369) (.out 0x104e39 (movR32R32Effect 0x104e39 3 13 3) (EffectPart.reads (.reg (.gpr 13)) [.gpr 3] []) (.reg (.gpr 13))) #v[1367]
    (.letOp (n := 1370) (.exec 0x104e39 (fun s => s.RIP = 0x104e39) (movR32R32Effect 0x104e39 3 13 3) (Reg.operands [.gpr 3] [])) #v[1367]
    (.letOp (n := 1371) (.out 0x104e3c (shrR32Effect 0x104e3c 4 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[1369]
    (.letOp (n := 1372) (.exec 0x104e3c (fun s => s.RIP = 0x104e3c) (shrR32Effect 0x104e3c 4 13 2) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1369]
    (.letOp (n := 1373) (.out 0x104e40 (xorR32R32Effect 0x104e40 3 13 3) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 3] []) (.reg (.gpr 13))) #v[1371, 1367]
    (.letOp (n := 1374) (.exec 0x104e40 (fun s => s.RIP = 0x104e40) (xorR32R32Effect 0x104e40 3 13 3) (Reg.operands [.gpr 13, .gpr 3] [])) #v[1371, 1367]
    (b_l10446f_34))))))))))))))))))))))))))))))))))))))))

def bytes_l10446f_33 : List UInt8 :=
  [0x45, 0x31, 0xEC, 0x0F, 0xB7, 0x9C, 0x24, 0x9A, 0x00, 0x00, 0x00, 0x41, 0x89, 0xDD, 0x41, 0xC1,
    0xED, 0x02, 0x41, 0x31, 0xDD, 0x41, 0x81, 0xE5, 0x20, 0x13, 0x00, 0x00, 0x44, 0x31, 0xEB, 0x41,
    0xC1, 0xE5, 0x02, 0x41, 0x31, 0xDD, 0x44, 0x89, 0xEA, 0xD1, 0xEA, 0x44, 0x31, 0xEA, 0x81, 0xE2,
    0x50, 0x50, 0x00, 0x00, 0x41, 0x31, 0xD5, 0x01, 0xD2, 0x44, 0x31, 0xEA, 0x0F, 0xB7, 0x9C, 0x24,
    0x9C, 0x00, 0x00, 0x00, 0x41, 0x89, 0xDD, 0x41, 0xC1, 0xED, 0x02, 0x41, 0x31, 0xDD] ++ bytes_l10446f_34

theorem code_l10446f_33 : ∀ x ∈ codeRange 0x104df5 bytes_l10446f_33, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x4df5 78 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10446f_34

def b_l10446f_32 : Block Op Label signature Reg.count 1296 :=
  .letOp (n := 1296) (.out 0x104da3 (xorR32R32Effect 0x104da3 3 3 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 12] []) (.reg (.gpr 3))) #v[1294, 1290]
    (.letOp (n := 1297) (.exec 0x104da3 (fun s => s.RIP = 0x104da3) (xorR32R32Effect 0x104da3 3 3 12) (Reg.operands [.gpr 3, .gpr 12] [])) #v[1294, 1290]
    (.letOp (n := 1298) (.out 0x104da6 (andR32Imm32Effect 0x104da6 6 3 0x5050) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[1296]
    (.letOp (n := 1299) (.exec 0x104da6 (fun s => s.RIP = 0x104da6) (andR32Imm32Effect 0x104da6 6 3 0x5050) (Reg.operands [.gpr 3] [])) #v[1296]
    (.letOp (n := 1300) (.out 0x104dac (xorR32R32Effect 0x104dac 3 12 3) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 3] []) (.reg (.gpr 12))) #v[1290, 1298]
    (.letOp (n := 1301) (.exec 0x104dac (fun s => s.RIP = 0x104dac) (xorR32R32Effect 0x104dac 3 12 3) (Reg.operands [.gpr 12, .gpr 3] [])) #v[1290, 1298]
    (.letOp (n := 1302) (.out 0x104daf (addR32R32Effect 0x104daf 2 3 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 3] []) (.reg (.gpr 3))) #v[1298, 1298]
    (.letOp (n := 1303) (.exec 0x104daf (fun s => s.RIP = 0x104daf) (addR32R32Effect 0x104daf 2 3 3) (Reg.operands [.gpr 3, .gpr 3] [])) #v[1298, 1298]
    (.letOp (n := 1304) (.out 0x104db1 (xorR32R32Effect 0x104db1 3 3 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 12] []) (.reg (.gpr 3))) #v[1302, 1300]
    (.letOp (n := 1305) (.exec 0x104db1 (fun s => s.RIP = 0x104db1) (xorR32R32Effect 0x104db1 3 3 12) (Reg.operands [.gpr 3, .gpr 12] [])) #v[1302, 1300]
    (.letOp (n := 1306) (.exec 0x104db4 (StorePre 0x104db4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x86)) s (0x104db4 + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x104db4 8 3 (.sib 4 none 0 (.d32 0x86))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[1304, 4]
    (.letOp (n := 1307) (.out 0x104dbc (movzxR32M16Effect 0x104dbc 8 3 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 1308) (.exec 0x104dbc (LoadPre 0x104dbc (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x104dbc + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x104dbc 8 3 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1309) (.out 0x104dc4 (movR32R32Effect 0x104dc4 3 13 3) (EffectPart.reads (.reg (.gpr 13)) [.gpr 3] []) (.reg (.gpr 13))) #v[1307]
    (.letOp (n := 1310) (.exec 0x104dc4 (fun s => s.RIP = 0x104dc4) (movR32R32Effect 0x104dc4 3 13 3) (Reg.operands [.gpr 3] [])) #v[1307]
    (.letOp (n := 1311) (.out 0x104dc7 (shrR32Effect 0x104dc7 4 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[1309]
    (.letOp (n := 1312) (.exec 0x104dc7 (fun s => s.RIP = 0x104dc7) (shrR32Effect 0x104dc7 4 13 2) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1309]
    (.letOp (n := 1313) (.out 0x104dcb (xorR32R32Effect 0x104dcb 3 13 3) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 3] []) (.reg (.gpr 13))) #v[1311, 1307]
    (.letOp (n := 1314) (.exec 0x104dcb (fun s => s.RIP = 0x104dcb) (xorR32R32Effect 0x104dcb 3 13 3) (Reg.operands [.gpr 13, .gpr 3] [])) #v[1311, 1307]
    (.letOp (n := 1315) (.out 0x104dce (andR32Imm32Effect 0x104dce 7 13 0x1320) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[1313]
    (.letOp (n := 1316) (.exec 0x104dce (fun s => s.RIP = 0x104dce) (andR32Imm32Effect 0x104dce 7 13 0x1320) (Reg.operands [.gpr 13] [])) #v[1313]
    (.letOp (n := 1317) (.out 0x104dd5 (xorR32R32Effect 0x104dd5 3 3 13) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 13] []) (.reg (.gpr 3))) #v[1307, 1315]
    (.letOp (n := 1318) (.exec 0x104dd5 (fun s => s.RIP = 0x104dd5) (xorR32R32Effect 0x104dd5 3 3 13) (Reg.operands [.gpr 3, .gpr 13] [])) #v[1307, 1315]
    (.letOp (n := 1319) (.out 0x104dd8 (shlR32Effect 0x104dd8 4 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[1315]
    (.letOp (n := 1320) (.exec 0x104dd8 (fun s => s.RIP = 0x104dd8) (shlR32Effect 0x104dd8 4 13 2) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1315]
    (.letOp (n := 1321) (.out 0x104ddc (xorR32R32Effect 0x104ddc 3 13 3) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 3] []) (.reg (.gpr 13))) #v[1319, 1317]
    (.letOp (n := 1322) (.exec 0x104ddc (fun s => s.RIP = 0x104ddc) (xorR32R32Effect 0x104ddc 3 13 3) (Reg.operands [.gpr 13, .gpr 3] [])) #v[1319, 1317]
    (.letOp (n := 1323) (.out 0x104ddf (movR32R32Effect 0x104ddf 3 12 13) (EffectPart.reads (.reg (.gpr 12)) [.gpr 13] []) (.reg (.gpr 12))) #v[1321]
    (.letOp (n := 1324) (.exec 0x104ddf (fun s => s.RIP = 0x104ddf) (movR32R32Effect 0x104ddf 3 12 13) (Reg.operands [.gpr 13] [])) #v[1321]
    (.letOp (n := 1325) (.out 0x104de2 (shrR32Effect 0x104de2 3 12 1) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[1323]
    (.letOp (n := 1326) (.exec 0x104de2 (fun s => s.RIP = 0x104de2) (shrR32Effect 0x104de2 3 12 1) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1323]
    (.letOp (n := 1327) (.out 0x104de5 (xorR32R32Effect 0x104de5 3 12 13) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 13] []) (.reg (.gpr 12))) #v[1325, 1321]
    (.letOp (n := 1328) (.exec 0x104de5 (fun s => s.RIP = 0x104de5) (xorR32R32Effect 0x104de5 3 12 13) (Reg.operands [.gpr 12, .gpr 13] [])) #v[1325, 1321]
    (.letOp (n := 1329) (.out 0x104de8 (andR32Imm32Effect 0x104de8 7 12 0x5050) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[1327]
    (.letOp (n := 1330) (.exec 0x104de8 (fun s => s.RIP = 0x104de8) (andR32Imm32Effect 0x104de8 7 12 0x5050) (Reg.operands [.gpr 12] [])) #v[1327]
    (.letOp (n := 1331) (.out 0x104def (xorR32R32Effect 0x104def 3 13 12) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 12] []) (.reg (.gpr 13))) #v[1321, 1329]
    (.letOp (n := 1332) (.exec 0x104def (fun s => s.RIP = 0x104def) (xorR32R32Effect 0x104def 3 13 12) (Reg.operands [.gpr 13, .gpr 12] [])) #v[1321, 1329]
    (.letOp (n := 1333) (.out 0x104df2 (addR32R32Effect 0x104df2 3 12 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 12] []) (.reg (.gpr 12))) #v[1329, 1329]
    (.letOp (n := 1334) (.exec 0x104df2 (fun s => s.RIP = 0x104df2) (addR32R32Effect 0x104df2 3 12 12) (Reg.operands [.gpr 12, .gpr 12] [])) #v[1329, 1329]
    (b_l10446f_33)))))))))))))))))))))))))))))))))))))))

def bytes_l10446f_32 : List UInt8 :=
  [0x44, 0x31, 0xE3, 0x81, 0xE3, 0x50, 0x50, 0x00, 0x00, 0x41, 0x31, 0xDC, 0x01, 0xDB, 0x44, 0x31,
    0xE3, 0x66, 0x89, 0x9C, 0x24, 0x86, 0x00, 0x00, 0x00, 0x0F, 0xB7, 0x9C, 0x24, 0x98, 0x00, 0x00,
    0x00, 0x41, 0x89, 0xDD, 0x41, 0xC1, 0xED, 0x02, 0x41, 0x31, 0xDD, 0x41, 0x81, 0xE5, 0x20, 0x13,
    0x00, 0x00, 0x44, 0x31, 0xEB, 0x41, 0xC1, 0xE5, 0x02, 0x41, 0x31, 0xDD, 0x45, 0x89, 0xEC, 0x41,
    0xD1, 0xEC, 0x45, 0x31, 0xEC, 0x41, 0x81, 0xE4, 0x50, 0x50, 0x00, 0x00, 0x45, 0x31, 0xE5, 0x45,
    0x01, 0xE4] ++ bytes_l10446f_33

theorem code_l10446f_32 : ∀ x ∈ codeRange 0x104da3 bytes_l10446f_32, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x4da3 82 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10446f_33

def b_l10446f_31 : Block Op Label signature Reg.count 1257 :=
  .letOp (n := 1257) (.out 0x104d56 (shlR32Effect 0x104d56 4 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[1253]
    (.letOp (n := 1258) (.exec 0x104d56 (fun s => s.RIP = 0x104d56) (shlR32Effect 0x104d56 4 12 2) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1253]
    (.letOp (n := 1259) (.out 0x104d5a (xorR32R32Effect 0x104d5a 3 12 3) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 3] []) (.reg (.gpr 12))) #v[1257, 1255]
    (.letOp (n := 1260) (.exec 0x104d5a (fun s => s.RIP = 0x104d5a) (xorR32R32Effect 0x104d5a 3 12 3) (Reg.operands [.gpr 12, .gpr 3] [])) #v[1257, 1255]
    (.letOp (n := 1261) (.out 0x104d5d (movR32R32Effect 0x104d5d 3 3 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 12] []) (.reg (.gpr 3))) #v[1259]
    (.letOp (n := 1262) (.exec 0x104d5d (fun s => s.RIP = 0x104d5d) (movR32R32Effect 0x104d5d 3 3 12) (Reg.operands [.gpr 12] [])) #v[1259]
    (.letOp (n := 1263) (.out 0x104d60 (shrR32Effect 0x104d60 2 3 1) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[1261]
    (.letOp (n := 1264) (.exec 0x104d60 (fun s => s.RIP = 0x104d60) (shrR32Effect 0x104d60 2 3 1) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1261]
    (.letOp (n := 1265) (.out 0x104d62 (xorR32R32Effect 0x104d62 3 3 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 12] []) (.reg (.gpr 3))) #v[1263, 1259]
    (.letOp (n := 1266) (.exec 0x104d62 (fun s => s.RIP = 0x104d62) (xorR32R32Effect 0x104d62 3 3 12) (Reg.operands [.gpr 3, .gpr 12] [])) #v[1263, 1259]
    (.letOp (n := 1267) (.out 0x104d65 (andR32Imm32Effect 0x104d65 6 3 0x5050) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[1265]
    (.letOp (n := 1268) (.exec 0x104d65 (fun s => s.RIP = 0x104d65) (andR32Imm32Effect 0x104d65 6 3 0x5050) (Reg.operands [.gpr 3] [])) #v[1265]
    (.letOp (n := 1269) (.out 0x104d6b (xorR32R32Effect 0x104d6b 3 12 3) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 3] []) (.reg (.gpr 12))) #v[1259, 1267]
    (.letOp (n := 1270) (.exec 0x104d6b (fun s => s.RIP = 0x104d6b) (xorR32R32Effect 0x104d6b 3 12 3) (Reg.operands [.gpr 12, .gpr 3] [])) #v[1259, 1267]
    (.letOp (n := 1271) (.out 0x104d6e (addR32R32Effect 0x104d6e 2 3 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 3] []) (.reg (.gpr 3))) #v[1267, 1267]
    (.letOp (n := 1272) (.exec 0x104d6e (fun s => s.RIP = 0x104d6e) (addR32R32Effect 0x104d6e 2 3 3) (Reg.operands [.gpr 3, .gpr 3] [])) #v[1267, 1267]
    (.letOp (n := 1273) (.out 0x104d70 (xorR32R32Effect 0x104d70 3 3 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 12] []) (.reg (.gpr 3))) #v[1271, 1269]
    (.letOp (n := 1274) (.exec 0x104d70 (fun s => s.RIP = 0x104d70) (xorR32R32Effect 0x104d70 3 3 12) (Reg.operands [.gpr 3, .gpr 12] [])) #v[1271, 1269]
    (.letOp (n := 1275) (.exec 0x104d73 (StorePre 0x104d73 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x84)) s (0x104d73 + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x104d73 8 3 (.sib 4 none 0 (.d32 0x84))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[1273, 4]
    (.letOp (n := 1276) (.out 0x104d7b (movzxR32M16Effect 0x104d7b 8 3 (.sib 4 none 0 (.d32 0x86))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 1277) (.exec 0x104d7b (LoadPre 0x104d7b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x86)) s (0x104d7b + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x104d7b 8 3 (.sib 4 none 0 (.d32 0x86))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1278) (.out 0x104d83 (movR32R32Effect 0x104d83 3 12 3) (EffectPart.reads (.reg (.gpr 12)) [.gpr 3] []) (.reg (.gpr 12))) #v[1276]
    (.letOp (n := 1279) (.exec 0x104d83 (fun s => s.RIP = 0x104d83) (movR32R32Effect 0x104d83 3 12 3) (Reg.operands [.gpr 3] [])) #v[1276]
    (.letOp (n := 1280) (.out 0x104d86 (shrR32Effect 0x104d86 4 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[1278]
    (.letOp (n := 1281) (.exec 0x104d86 (fun s => s.RIP = 0x104d86) (shrR32Effect 0x104d86 4 12 2) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1278]
    (.letOp (n := 1282) (.out 0x104d8a (xorR32R32Effect 0x104d8a 3 12 3) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 3] []) (.reg (.gpr 12))) #v[1280, 1276]
    (.letOp (n := 1283) (.exec 0x104d8a (fun s => s.RIP = 0x104d8a) (xorR32R32Effect 0x104d8a 3 12 3) (Reg.operands [.gpr 12, .gpr 3] [])) #v[1280, 1276]
    (.letOp (n := 1284) (.out 0x104d8d (andR32Imm32Effect 0x104d8d 7 12 0x2310) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[1282]
    (.letOp (n := 1285) (.exec 0x104d8d (fun s => s.RIP = 0x104d8d) (andR32Imm32Effect 0x104d8d 7 12 0x2310) (Reg.operands [.gpr 12] [])) #v[1282]
    (.letOp (n := 1286) (.out 0x104d94 (xorR32R32Effect 0x104d94 3 3 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 12] []) (.reg (.gpr 3))) #v[1276, 1284]
    (.letOp (n := 1287) (.exec 0x104d94 (fun s => s.RIP = 0x104d94) (xorR32R32Effect 0x104d94 3 3 12) (Reg.operands [.gpr 3, .gpr 12] [])) #v[1276, 1284]
    (.letOp (n := 1288) (.out 0x104d97 (shlR32Effect 0x104d97 4 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[1284]
    (.letOp (n := 1289) (.exec 0x104d97 (fun s => s.RIP = 0x104d97) (shlR32Effect 0x104d97 4 12 2) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1284]
    (.letOp (n := 1290) (.out 0x104d9b (xorR32R32Effect 0x104d9b 3 12 3) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 3] []) (.reg (.gpr 12))) #v[1288, 1286]
    (.letOp (n := 1291) (.exec 0x104d9b (fun s => s.RIP = 0x104d9b) (xorR32R32Effect 0x104d9b 3 12 3) (Reg.operands [.gpr 12, .gpr 3] [])) #v[1288, 1286]
    (.letOp (n := 1292) (.out 0x104d9e (movR32R32Effect 0x104d9e 3 3 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 12] []) (.reg (.gpr 3))) #v[1290]
    (.letOp (n := 1293) (.exec 0x104d9e (fun s => s.RIP = 0x104d9e) (movR32R32Effect 0x104d9e 3 3 12) (Reg.operands [.gpr 12] [])) #v[1290]
    (.letOp (n := 1294) (.out 0x104da1 (shrR32Effect 0x104da1 2 3 1) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[1292]
    (.letOp (n := 1295) (.exec 0x104da1 (fun s => s.RIP = 0x104da1) (shrR32Effect 0x104da1 2 3 1) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1292]
    (b_l10446f_32)))))))))))))))))))))))))))))))))))))))

def bytes_l10446f_31 : List UInt8 :=
  [0x41, 0xC1, 0xE4, 0x02, 0x41, 0x31, 0xDC, 0x44, 0x89, 0xE3, 0xD1, 0xEB, 0x44, 0x31, 0xE3, 0x81,
    0xE3, 0x50, 0x50, 0x00, 0x00, 0x41, 0x31, 0xDC, 0x01, 0xDB, 0x44, 0x31, 0xE3, 0x66, 0x89, 0x9C,
    0x24, 0x84, 0x00, 0x00, 0x00, 0x0F, 0xB7, 0x9C, 0x24, 0x86, 0x00, 0x00, 0x00, 0x41, 0x89, 0xDC,
    0x41, 0xC1, 0xEC, 0x02, 0x41, 0x31, 0xDC, 0x41, 0x81, 0xE4, 0x10, 0x23, 0x00, 0x00, 0x44, 0x31,
    0xE3, 0x41, 0xC1, 0xE4, 0x02, 0x41, 0x31, 0xDC, 0x44, 0x89, 0xE3, 0xD1, 0xEB] ++ bytes_l10446f_32

theorem code_l10446f_31 : ∀ x ∈ codeRange 0x104d56 bytes_l10446f_31, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x4d56 77 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10446f_32

def b_l10446f_30 : Block Op Label signature Reg.count 1218 :=
  .letOp (n := 1218) (.out 0x104d04 (shrR32Effect 0x104d04 4 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[1216]
    (.letOp (n := 1219) (.exec 0x104d04 (fun s => s.RIP = 0x104d04) (shrR32Effect 0x104d04 4 12 2) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1216]
    (.letOp (n := 1220) (.out 0x104d08 (xorR32R32Effect 0x104d08 3 12 3) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 3] []) (.reg (.gpr 12))) #v[1218, 1214]
    (.letOp (n := 1221) (.exec 0x104d08 (fun s => s.RIP = 0x104d08) (xorR32R32Effect 0x104d08 3 12 3) (Reg.operands [.gpr 12, .gpr 3] [])) #v[1218, 1214]
    (.letOp (n := 1222) (.out 0x104d0b (andR32Imm32Effect 0x104d0b 7 12 0x2310) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[1220]
    (.letOp (n := 1223) (.exec 0x104d0b (fun s => s.RIP = 0x104d0b) (andR32Imm32Effect 0x104d0b 7 12 0x2310) (Reg.operands [.gpr 12] [])) #v[1220]
    (.letOp (n := 1224) (.out 0x104d12 (xorR32R32Effect 0x104d12 3 3 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 12] []) (.reg (.gpr 3))) #v[1214, 1222]
    (.letOp (n := 1225) (.exec 0x104d12 (fun s => s.RIP = 0x104d12) (xorR32R32Effect 0x104d12 3 3 12) (Reg.operands [.gpr 3, .gpr 12] [])) #v[1214, 1222]
    (.letOp (n := 1226) (.out 0x104d15 (shlR32Effect 0x104d15 4 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[1222]
    (.letOp (n := 1227) (.exec 0x104d15 (fun s => s.RIP = 0x104d15) (shlR32Effect 0x104d15 4 12 2) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1222]
    (.letOp (n := 1228) (.out 0x104d19 (xorR32R32Effect 0x104d19 3 12 3) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 3] []) (.reg (.gpr 12))) #v[1226, 1224]
    (.letOp (n := 1229) (.exec 0x104d19 (fun s => s.RIP = 0x104d19) (xorR32R32Effect 0x104d19 3 12 3) (Reg.operands [.gpr 12, .gpr 3] [])) #v[1226, 1224]
    (.letOp (n := 1230) (.out 0x104d1c (movR32R32Effect 0x104d1c 3 3 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 12] []) (.reg (.gpr 3))) #v[1228]
    (.letOp (n := 1231) (.exec 0x104d1c (fun s => s.RIP = 0x104d1c) (movR32R32Effect 0x104d1c 3 3 12) (Reg.operands [.gpr 12] [])) #v[1228]
    (.letOp (n := 1232) (.out 0x104d1f (shrR32Effect 0x104d1f 2 3 1) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[1230]
    (.letOp (n := 1233) (.exec 0x104d1f (fun s => s.RIP = 0x104d1f) (shrR32Effect 0x104d1f 2 3 1) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1230]
    (.letOp (n := 1234) (.out 0x104d21 (xorR32R32Effect 0x104d21 3 3 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 12] []) (.reg (.gpr 3))) #v[1232, 1228]
    (.letOp (n := 1235) (.exec 0x104d21 (fun s => s.RIP = 0x104d21) (xorR32R32Effect 0x104d21 3 3 12) (Reg.operands [.gpr 3, .gpr 12] [])) #v[1232, 1228]
    (.letOp (n := 1236) (.out 0x104d24 (andR32Imm32Effect 0x104d24 6 3 0x5050) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[1234]
    (.letOp (n := 1237) (.exec 0x104d24 (fun s => s.RIP = 0x104d24) (andR32Imm32Effect 0x104d24 6 3 0x5050) (Reg.operands [.gpr 3] [])) #v[1234]
    (.letOp (n := 1238) (.out 0x104d2a (xorR32R32Effect 0x104d2a 3 12 3) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 3] []) (.reg (.gpr 12))) #v[1228, 1236]
    (.letOp (n := 1239) (.exec 0x104d2a (fun s => s.RIP = 0x104d2a) (xorR32R32Effect 0x104d2a 3 12 3) (Reg.operands [.gpr 12, .gpr 3] [])) #v[1228, 1236]
    (.letOp (n := 1240) (.out 0x104d2d (addR32R32Effect 0x104d2d 2 3 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 3] []) (.reg (.gpr 3))) #v[1236, 1236]
    (.letOp (n := 1241) (.exec 0x104d2d (fun s => s.RIP = 0x104d2d) (addR32R32Effect 0x104d2d 2 3 3) (Reg.operands [.gpr 3, .gpr 3] [])) #v[1236, 1236]
    (.letOp (n := 1242) (.out 0x104d2f (xorR32R32Effect 0x104d2f 3 3 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 12] []) (.reg (.gpr 3))) #v[1240, 1238]
    (.letOp (n := 1243) (.exec 0x104d2f (fun s => s.RIP = 0x104d2f) (xorR32R32Effect 0x104d2f 3 3 12) (Reg.operands [.gpr 3, .gpr 12] [])) #v[1240, 1238]
    (.letOp (n := 1244) (.exec 0x104d32 (StorePre 0x104d32 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x82)) s (0x104d32 + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x104d32 8 3 (.sib 4 none 0 (.d32 0x82))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[1242, 4]
    (.letOp (n := 1245) (.out 0x104d3a (movzxR32M16Effect 0x104d3a 8 3 (.sib 4 none 0 (.d32 0x84))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 1246) (.exec 0x104d3a (LoadPre 0x104d3a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x84)) s (0x104d3a + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x104d3a 8 3 (.sib 4 none 0 (.d32 0x84))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1247) (.out 0x104d42 (movR32R32Effect 0x104d42 3 12 3) (EffectPart.reads (.reg (.gpr 12)) [.gpr 3] []) (.reg (.gpr 12))) #v[1245]
    (.letOp (n := 1248) (.exec 0x104d42 (fun s => s.RIP = 0x104d42) (movR32R32Effect 0x104d42 3 12 3) (Reg.operands [.gpr 3] [])) #v[1245]
    (.letOp (n := 1249) (.out 0x104d45 (shrR32Effect 0x104d45 4 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[1247]
    (.letOp (n := 1250) (.exec 0x104d45 (fun s => s.RIP = 0x104d45) (shrR32Effect 0x104d45 4 12 2) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1247]
    (.letOp (n := 1251) (.out 0x104d49 (xorR32R32Effect 0x104d49 3 12 3) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 3] []) (.reg (.gpr 12))) #v[1249, 1245]
    (.letOp (n := 1252) (.exec 0x104d49 (fun s => s.RIP = 0x104d49) (xorR32R32Effect 0x104d49 3 12 3) (Reg.operands [.gpr 12, .gpr 3] [])) #v[1249, 1245]
    (.letOp (n := 1253) (.out 0x104d4c (andR32Imm32Effect 0x104d4c 7 12 0x2310) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[1251]
    (.letOp (n := 1254) (.exec 0x104d4c (fun s => s.RIP = 0x104d4c) (andR32Imm32Effect 0x104d4c 7 12 0x2310) (Reg.operands [.gpr 12] [])) #v[1251]
    (.letOp (n := 1255) (.out 0x104d53 (xorR32R32Effect 0x104d53 3 3 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 12] []) (.reg (.gpr 3))) #v[1245, 1253]
    (.letOp (n := 1256) (.exec 0x104d53 (fun s => s.RIP = 0x104d53) (xorR32R32Effect 0x104d53 3 3 12) (Reg.operands [.gpr 3, .gpr 12] [])) #v[1245, 1253]
    (b_l10446f_31)))))))))))))))))))))))))))))))))))))))

def bytes_l10446f_30 : List UInt8 :=
  [0x41, 0xC1, 0xEC, 0x02, 0x41, 0x31, 0xDC, 0x41, 0x81, 0xE4, 0x10, 0x23, 0x00, 0x00, 0x44, 0x31,
    0xE3, 0x41, 0xC1, 0xE4, 0x02, 0x41, 0x31, 0xDC, 0x44, 0x89, 0xE3, 0xD1, 0xEB, 0x44, 0x31, 0xE3,
    0x81, 0xE3, 0x50, 0x50, 0x00, 0x00, 0x41, 0x31, 0xDC, 0x01, 0xDB, 0x44, 0x31, 0xE3, 0x66, 0x89,
    0x9C, 0x24, 0x82, 0x00, 0x00, 0x00, 0x0F, 0xB7, 0x9C, 0x24, 0x84, 0x00, 0x00, 0x00, 0x41, 0x89,
    0xDC, 0x41, 0xC1, 0xEC, 0x02, 0x41, 0x31, 0xDC, 0x41, 0x81, 0xE4, 0x10, 0x23, 0x00, 0x00, 0x44,
    0x31, 0xE3] ++ bytes_l10446f_31

theorem code_l10446f_30 : ∀ x ∈ codeRange 0x104d04 bytes_l10446f_30, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x4d04 82 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10446f_31

def b_l10446f_29 : Block Op Label signature Reg.count 1180 :=
  .letOp (n := 1180) (.out 0x104cb0 (xorR32R32Effect 0x104cb0 3 3 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 12] []) (.reg (.gpr 3))) #v[1178, 1176]
    (.letOp (n := 1181) (.exec 0x104cb0 (fun s => s.RIP = 0x104cb0) (xorR32R32Effect 0x104cb0 3 3 12) (Reg.operands [.gpr 3, .gpr 12] [])) #v[1178, 1176]
    (.letOp (n := 1182) (.exec 0x104cb3 (StorePre 0x104cb3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7e)) s (0x104cb3 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x104cb3 5 3 (.sib 4 none 0 (.d8 0x7e))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[1180, 4]
    (.letOp (n := 1183) (.out 0x104cb8 (movzxR32M16Effect 0x104cb8 8 3 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 1184) (.exec 0x104cb8 (LoadPre 0x104cb8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x104cb8 + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x104cb8 8 3 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1185) (.out 0x104cc0 (movR32R32Effect 0x104cc0 3 12 3) (EffectPart.reads (.reg (.gpr 12)) [.gpr 3] []) (.reg (.gpr 12))) #v[1183]
    (.letOp (n := 1186) (.exec 0x104cc0 (fun s => s.RIP = 0x104cc0) (movR32R32Effect 0x104cc0 3 12 3) (Reg.operands [.gpr 3] [])) #v[1183]
    (.letOp (n := 1187) (.out 0x104cc3 (shrR32Effect 0x104cc3 4 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[1185]
    (.letOp (n := 1188) (.exec 0x104cc3 (fun s => s.RIP = 0x104cc3) (shrR32Effect 0x104cc3 4 12 2) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1185]
    (.letOp (n := 1189) (.out 0x104cc7 (xorR32R32Effect 0x104cc7 3 12 3) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 3] []) (.reg (.gpr 12))) #v[1187, 1183]
    (.letOp (n := 1190) (.exec 0x104cc7 (fun s => s.RIP = 0x104cc7) (xorR32R32Effect 0x104cc7 3 12 3) (Reg.operands [.gpr 12, .gpr 3] [])) #v[1187, 1183]
    (.letOp (n := 1191) (.out 0x104cca (andR32Imm32Effect 0x104cca 7 12 0x2310) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[1189]
    (.letOp (n := 1192) (.exec 0x104cca (fun s => s.RIP = 0x104cca) (andR32Imm32Effect 0x104cca 7 12 0x2310) (Reg.operands [.gpr 12] [])) #v[1189]
    (.letOp (n := 1193) (.out 0x104cd1 (xorR32R32Effect 0x104cd1 3 3 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 12] []) (.reg (.gpr 3))) #v[1183, 1191]
    (.letOp (n := 1194) (.exec 0x104cd1 (fun s => s.RIP = 0x104cd1) (xorR32R32Effect 0x104cd1 3 3 12) (Reg.operands [.gpr 3, .gpr 12] [])) #v[1183, 1191]
    (.letOp (n := 1195) (.out 0x104cd4 (shlR32Effect 0x104cd4 4 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[1191]
    (.letOp (n := 1196) (.exec 0x104cd4 (fun s => s.RIP = 0x104cd4) (shlR32Effect 0x104cd4 4 12 2) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1191]
    (.letOp (n := 1197) (.out 0x104cd8 (xorR32R32Effect 0x104cd8 3 12 3) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 3] []) (.reg (.gpr 12))) #v[1195, 1193]
    (.letOp (n := 1198) (.exec 0x104cd8 (fun s => s.RIP = 0x104cd8) (xorR32R32Effect 0x104cd8 3 12 3) (Reg.operands [.gpr 12, .gpr 3] [])) #v[1195, 1193]
    (.letOp (n := 1199) (.out 0x104cdb (movR32R32Effect 0x104cdb 3 3 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 12] []) (.reg (.gpr 3))) #v[1197]
    (.letOp (n := 1200) (.exec 0x104cdb (fun s => s.RIP = 0x104cdb) (movR32R32Effect 0x104cdb 3 3 12) (Reg.operands [.gpr 12] [])) #v[1197]
    (.letOp (n := 1201) (.out 0x104cde (shrR32Effect 0x104cde 2 3 1) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[1199]
    (.letOp (n := 1202) (.exec 0x104cde (fun s => s.RIP = 0x104cde) (shrR32Effect 0x104cde 2 3 1) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1199]
    (.letOp (n := 1203) (.out 0x104ce0 (xorR32R32Effect 0x104ce0 3 3 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 12] []) (.reg (.gpr 3))) #v[1201, 1197]
    (.letOp (n := 1204) (.exec 0x104ce0 (fun s => s.RIP = 0x104ce0) (xorR32R32Effect 0x104ce0 3 3 12) (Reg.operands [.gpr 3, .gpr 12] [])) #v[1201, 1197]
    (.letOp (n := 1205) (.out 0x104ce3 (andR32Imm32Effect 0x104ce3 6 3 0x5050) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[1203]
    (.letOp (n := 1206) (.exec 0x104ce3 (fun s => s.RIP = 0x104ce3) (andR32Imm32Effect 0x104ce3 6 3 0x5050) (Reg.operands [.gpr 3] [])) #v[1203]
    (.letOp (n := 1207) (.out 0x104ce9 (xorR32R32Effect 0x104ce9 3 12 3) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 3] []) (.reg (.gpr 12))) #v[1197, 1205]
    (.letOp (n := 1208) (.exec 0x104ce9 (fun s => s.RIP = 0x104ce9) (xorR32R32Effect 0x104ce9 3 12 3) (Reg.operands [.gpr 12, .gpr 3] [])) #v[1197, 1205]
    (.letOp (n := 1209) (.out 0x104cec (addR32R32Effect 0x104cec 2 3 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 3] []) (.reg (.gpr 3))) #v[1205, 1205]
    (.letOp (n := 1210) (.exec 0x104cec (fun s => s.RIP = 0x104cec) (addR32R32Effect 0x104cec 2 3 3) (Reg.operands [.gpr 3, .gpr 3] [])) #v[1205, 1205]
    (.letOp (n := 1211) (.out 0x104cee (xorR32R32Effect 0x104cee 3 3 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 12] []) (.reg (.gpr 3))) #v[1209, 1207]
    (.letOp (n := 1212) (.exec 0x104cee (fun s => s.RIP = 0x104cee) (xorR32R32Effect 0x104cee 3 3 12) (Reg.operands [.gpr 3, .gpr 12] [])) #v[1209, 1207]
    (.letOp (n := 1213) (.exec 0x104cf1 (StorePre 0x104cf1 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x104cf1 + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x104cf1 8 3 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[1211, 4]
    (.letOp (n := 1214) (.out 0x104cf9 (movzxR32M16Effect 0x104cf9 8 3 (.sib 4 none 0 (.d32 0x82))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 1215) (.exec 0x104cf9 (LoadPre 0x104cf9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x82)) s (0x104cf9 + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x104cf9 8 3 (.sib 4 none 0 (.d32 0x82))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1216) (.out 0x104d01 (movR32R32Effect 0x104d01 3 12 3) (EffectPart.reads (.reg (.gpr 12)) [.gpr 3] []) (.reg (.gpr 12))) #v[1214]
    (.letOp (n := 1217) (.exec 0x104d01 (fun s => s.RIP = 0x104d01) (movR32R32Effect 0x104d01 3 12 3) (Reg.operands [.gpr 3] [])) #v[1214]
    (b_l10446f_30))))))))))))))))))))))))))))))))))))))

def bytes_l10446f_29 : List UInt8 :=
  [0x44, 0x31, 0xE3, 0x66, 0x89, 0x5C, 0x24, 0x7E, 0x0F, 0xB7, 0x9C, 0x24, 0x80, 0x00, 0x00, 0x00,
    0x41, 0x89, 0xDC, 0x41, 0xC1, 0xEC, 0x02, 0x41, 0x31, 0xDC, 0x41, 0x81, 0xE4, 0x10, 0x23, 0x00,
    0x00, 0x44, 0x31, 0xE3, 0x41, 0xC1, 0xE4, 0x02, 0x41, 0x31, 0xDC, 0x44, 0x89, 0xE3, 0xD1, 0xEB,
    0x44, 0x31, 0xE3, 0x81, 0xE3, 0x50, 0x50, 0x00, 0x00, 0x41, 0x31, 0xDC, 0x01, 0xDB, 0x44, 0x31,
    0xE3, 0x66, 0x89, 0x9C, 0x24, 0x80, 0x00, 0x00, 0x00, 0x0F, 0xB7, 0x9C, 0x24, 0x82, 0x00, 0x00,
    0x00, 0x41, 0x89, 0xDC] ++ bytes_l10446f_30

theorem code_l10446f_29 : ∀ x ∈ codeRange 0x104cb0 bytes_l10446f_29, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x4cb0 84 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10446f_30

def b_l10446f_28 : Block Op Label signature Reg.count 1141 :=
  .letOp (n := 1141) (.out 0x104c67 (xorR32R32Effect 0x104c67 3 3 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 12] []) (.reg (.gpr 3))) #v[1139, 1135]
    (.letOp (n := 1142) (.exec 0x104c67 (fun s => s.RIP = 0x104c67) (xorR32R32Effect 0x104c67 3 3 12) (Reg.operands [.gpr 3, .gpr 12] [])) #v[1139, 1135]
    (.letOp (n := 1143) (.out 0x104c6a (andR32Imm32Effect 0x104c6a 6 3 0x5050) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[1141]
    (.letOp (n := 1144) (.exec 0x104c6a (fun s => s.RIP = 0x104c6a) (andR32Imm32Effect 0x104c6a 6 3 0x5050) (Reg.operands [.gpr 3] [])) #v[1141]
    (.letOp (n := 1145) (.out 0x104c70 (xorR32R32Effect 0x104c70 3 12 3) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 3] []) (.reg (.gpr 12))) #v[1135, 1143]
    (.letOp (n := 1146) (.exec 0x104c70 (fun s => s.RIP = 0x104c70) (xorR32R32Effect 0x104c70 3 12 3) (Reg.operands [.gpr 12, .gpr 3] [])) #v[1135, 1143]
    (.letOp (n := 1147) (.out 0x104c73 (addR32R32Effect 0x104c73 2 3 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 3] []) (.reg (.gpr 3))) #v[1143, 1143]
    (.letOp (n := 1148) (.exec 0x104c73 (fun s => s.RIP = 0x104c73) (addR32R32Effect 0x104c73 2 3 3) (Reg.operands [.gpr 3, .gpr 3] [])) #v[1143, 1143]
    (.letOp (n := 1149) (.out 0x104c75 (xorR32R32Effect 0x104c75 3 3 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 12] []) (.reg (.gpr 3))) #v[1147, 1145]
    (.letOp (n := 1150) (.exec 0x104c75 (fun s => s.RIP = 0x104c75) (xorR32R32Effect 0x104c75 3 3 12) (Reg.operands [.gpr 3, .gpr 12] [])) #v[1147, 1145]
    (.letOp (n := 1151) (.exec 0x104c78 (StorePre 0x104c78 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7c)) s (0x104c78 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x104c78 5 3 (.sib 4 none 0 (.d8 0x7c))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[1149, 4]
    (.letOp (n := 1152) (.out 0x104c7d (movzxR32M16Effect 0x104c7d 5 3 (.sib 4 none 0 (.d8 0x7e))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 1153) (.exec 0x104c7d (LoadPre 0x104c7d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7e)) s (0x104c7d + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x104c7d 5 3 (.sib 4 none 0 (.d8 0x7e))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1154) (.out 0x104c82 (movR32R32Effect 0x104c82 3 12 3) (EffectPart.reads (.reg (.gpr 12)) [.gpr 3] []) (.reg (.gpr 12))) #v[1152]
    (.letOp (n := 1155) (.exec 0x104c82 (fun s => s.RIP = 0x104c82) (movR32R32Effect 0x104c82 3 12 3) (Reg.operands [.gpr 3] [])) #v[1152]
    (.letOp (n := 1156) (.out 0x104c85 (shrR32Effect 0x104c85 4 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[1154]
    (.letOp (n := 1157) (.exec 0x104c85 (fun s => s.RIP = 0x104c85) (shrR32Effect 0x104c85 4 12 2) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1154]
    (.letOp (n := 1158) (.out 0x104c89 (xorR32R32Effect 0x104c89 3 12 3) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 3] []) (.reg (.gpr 12))) #v[1156, 1152]
    (.letOp (n := 1159) (.exec 0x104c89 (fun s => s.RIP = 0x104c89) (xorR32R32Effect 0x104c89 3 12 3) (Reg.operands [.gpr 12, .gpr 3] [])) #v[1156, 1152]
    (.letOp (n := 1160) (.out 0x104c8c (andR32Imm32Effect 0x104c8c 7 12 0x2310) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[1158]
    (.letOp (n := 1161) (.exec 0x104c8c (fun s => s.RIP = 0x104c8c) (andR32Imm32Effect 0x104c8c 7 12 0x2310) (Reg.operands [.gpr 12] [])) #v[1158]
    (.letOp (n := 1162) (.out 0x104c93 (xorR32R32Effect 0x104c93 3 3 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 12] []) (.reg (.gpr 3))) #v[1152, 1160]
    (.letOp (n := 1163) (.exec 0x104c93 (fun s => s.RIP = 0x104c93) (xorR32R32Effect 0x104c93 3 3 12) (Reg.operands [.gpr 3, .gpr 12] [])) #v[1152, 1160]
    (.letOp (n := 1164) (.out 0x104c96 (shlR32Effect 0x104c96 4 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[1160]
    (.letOp (n := 1165) (.exec 0x104c96 (fun s => s.RIP = 0x104c96) (shlR32Effect 0x104c96 4 12 2) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1160]
    (.letOp (n := 1166) (.out 0x104c9a (xorR32R32Effect 0x104c9a 3 12 3) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 3] []) (.reg (.gpr 12))) #v[1164, 1162]
    (.letOp (n := 1167) (.exec 0x104c9a (fun s => s.RIP = 0x104c9a) (xorR32R32Effect 0x104c9a 3 12 3) (Reg.operands [.gpr 12, .gpr 3] [])) #v[1164, 1162]
    (.letOp (n := 1168) (.out 0x104c9d (movR32R32Effect 0x104c9d 3 3 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 12] []) (.reg (.gpr 3))) #v[1166]
    (.letOp (n := 1169) (.exec 0x104c9d (fun s => s.RIP = 0x104c9d) (movR32R32Effect 0x104c9d 3 3 12) (Reg.operands [.gpr 12] [])) #v[1166]
    (.letOp (n := 1170) (.out 0x104ca0 (shrR32Effect 0x104ca0 2 3 1) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[1168]
    (.letOp (n := 1171) (.exec 0x104ca0 (fun s => s.RIP = 0x104ca0) (shrR32Effect 0x104ca0 2 3 1) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1168]
    (.letOp (n := 1172) (.out 0x104ca2 (xorR32R32Effect 0x104ca2 3 3 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 12] []) (.reg (.gpr 3))) #v[1170, 1166]
    (.letOp (n := 1173) (.exec 0x104ca2 (fun s => s.RIP = 0x104ca2) (xorR32R32Effect 0x104ca2 3 3 12) (Reg.operands [.gpr 3, .gpr 12] [])) #v[1170, 1166]
    (.letOp (n := 1174) (.out 0x104ca5 (andR32Imm32Effect 0x104ca5 6 3 0x5050) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[1172]
    (.letOp (n := 1175) (.exec 0x104ca5 (fun s => s.RIP = 0x104ca5) (andR32Imm32Effect 0x104ca5 6 3 0x5050) (Reg.operands [.gpr 3] [])) #v[1172]
    (.letOp (n := 1176) (.out 0x104cab (xorR32R32Effect 0x104cab 3 12 3) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 3] []) (.reg (.gpr 12))) #v[1166, 1174]
    (.letOp (n := 1177) (.exec 0x104cab (fun s => s.RIP = 0x104cab) (xorR32R32Effect 0x104cab 3 12 3) (Reg.operands [.gpr 12, .gpr 3] [])) #v[1166, 1174]
    (.letOp (n := 1178) (.out 0x104cae (addR32R32Effect 0x104cae 2 3 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 3] []) (.reg (.gpr 3))) #v[1174, 1174]
    (.letOp (n := 1179) (.exec 0x104cae (fun s => s.RIP = 0x104cae) (addR32R32Effect 0x104cae 2 3 3) (Reg.operands [.gpr 3, .gpr 3] [])) #v[1174, 1174]
    (b_l10446f_29)))))))))))))))))))))))))))))))))))))))

def bytes_l10446f_28 : List UInt8 :=
  [0x44, 0x31, 0xE3, 0x81, 0xE3, 0x50, 0x50, 0x00, 0x00, 0x41, 0x31, 0xDC, 0x01, 0xDB, 0x44, 0x31,
    0xE3, 0x66, 0x89, 0x5C, 0x24, 0x7C, 0x0F, 0xB7, 0x5C, 0x24, 0x7E, 0x41, 0x89, 0xDC, 0x41, 0xC1,
    0xEC, 0x02, 0x41, 0x31, 0xDC, 0x41, 0x81, 0xE4, 0x10, 0x23, 0x00, 0x00, 0x44, 0x31, 0xE3, 0x41,
    0xC1, 0xE4, 0x02, 0x41, 0x31, 0xDC, 0x44, 0x89, 0xE3, 0xD1, 0xEB, 0x44, 0x31, 0xE3, 0x81, 0xE3,
    0x50, 0x50, 0x00, 0x00, 0x41, 0x31, 0xDC, 0x01, 0xDB] ++ bytes_l10446f_29

theorem code_l10446f_28 : ∀ x ∈ codeRange 0x104c67 bytes_l10446f_28, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x4c67 73 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10446f_29

def b_l10446f_27 : Block Op Label signature Reg.count 1102 :=
  .letOp (n := 1102) (.out 0x104c20 (shlR32Effect 0x104c20 4 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[1098]
    (.letOp (n := 1103) (.exec 0x104c20 (fun s => s.RIP = 0x104c20) (shlR32Effect 0x104c20 4 12 2) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1098]
    (.letOp (n := 1104) (.out 0x104c24 (xorR32R32Effect 0x104c24 3 12 3) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 3] []) (.reg (.gpr 12))) #v[1102, 1100]
    (.letOp (n := 1105) (.exec 0x104c24 (fun s => s.RIP = 0x104c24) (xorR32R32Effect 0x104c24 3 12 3) (Reg.operands [.gpr 12, .gpr 3] [])) #v[1102, 1100]
    (.letOp (n := 1106) (.out 0x104c27 (movR32R32Effect 0x104c27 3 3 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 12] []) (.reg (.gpr 3))) #v[1104]
    (.letOp (n := 1107) (.exec 0x104c27 (fun s => s.RIP = 0x104c27) (movR32R32Effect 0x104c27 3 3 12) (Reg.operands [.gpr 12] [])) #v[1104]
    (.letOp (n := 1108) (.out 0x104c2a (shrR32Effect 0x104c2a 2 3 1) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[1106]
    (.letOp (n := 1109) (.exec 0x104c2a (fun s => s.RIP = 0x104c2a) (shrR32Effect 0x104c2a 2 3 1) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1106]
    (.letOp (n := 1110) (.out 0x104c2c (xorR32R32Effect 0x104c2c 3 3 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 12] []) (.reg (.gpr 3))) #v[1108, 1104]
    (.letOp (n := 1111) (.exec 0x104c2c (fun s => s.RIP = 0x104c2c) (xorR32R32Effect 0x104c2c 3 3 12) (Reg.operands [.gpr 3, .gpr 12] [])) #v[1108, 1104]
    (.letOp (n := 1112) (.out 0x104c2f (andR32Imm32Effect 0x104c2f 6 3 0x5050) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[1110]
    (.letOp (n := 1113) (.exec 0x104c2f (fun s => s.RIP = 0x104c2f) (andR32Imm32Effect 0x104c2f 6 3 0x5050) (Reg.operands [.gpr 3] [])) #v[1110]
    (.letOp (n := 1114) (.out 0x104c35 (xorR32R32Effect 0x104c35 3 12 3) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 3] []) (.reg (.gpr 12))) #v[1104, 1112]
    (.letOp (n := 1115) (.exec 0x104c35 (fun s => s.RIP = 0x104c35) (xorR32R32Effect 0x104c35 3 12 3) (Reg.operands [.gpr 12, .gpr 3] [])) #v[1104, 1112]
    (.letOp (n := 1116) (.out 0x104c38 (addR32R32Effect 0x104c38 2 3 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 3] []) (.reg (.gpr 3))) #v[1112, 1112]
    (.letOp (n := 1117) (.exec 0x104c38 (fun s => s.RIP = 0x104c38) (addR32R32Effect 0x104c38 2 3 3) (Reg.operands [.gpr 3, .gpr 3] [])) #v[1112, 1112]
    (.letOp (n := 1118) (.out 0x104c3a (xorR32R32Effect 0x104c3a 3 3 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 12] []) (.reg (.gpr 3))) #v[1116, 1114]
    (.letOp (n := 1119) (.exec 0x104c3a (fun s => s.RIP = 0x104c3a) (xorR32R32Effect 0x104c3a 3 3 12) (Reg.operands [.gpr 3, .gpr 12] [])) #v[1116, 1114]
    (.letOp (n := 1120) (.exec 0x104c3d (StorePre 0x104c3d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7a)) s (0x104c3d + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x104c3d 5 3 (.sib 4 none 0 (.d8 0x7a))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[1118, 4]
    (.letOp (n := 1121) (.out 0x104c42 (movzxR32M16Effect 0x104c42 5 3 (.sib 4 none 0 (.d8 0x7c))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 1122) (.exec 0x104c42 (LoadPre 0x104c42 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7c)) s (0x104c42 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x104c42 5 3 (.sib 4 none 0 (.d8 0x7c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1123) (.out 0x104c47 (movR32R32Effect 0x104c47 3 12 3) (EffectPart.reads (.reg (.gpr 12)) [.gpr 3] []) (.reg (.gpr 12))) #v[1121]
    (.letOp (n := 1124) (.exec 0x104c47 (fun s => s.RIP = 0x104c47) (movR32R32Effect 0x104c47 3 12 3) (Reg.operands [.gpr 3] [])) #v[1121]
    (.letOp (n := 1125) (.out 0x104c4a (shrR32Effect 0x104c4a 4 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[1123]
    (.letOp (n := 1126) (.exec 0x104c4a (fun s => s.RIP = 0x104c4a) (shrR32Effect 0x104c4a 4 12 2) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1123]
    (.letOp (n := 1127) (.out 0x104c4e (xorR32R32Effect 0x104c4e 3 12 3) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 3] []) (.reg (.gpr 12))) #v[1125, 1121]
    (.letOp (n := 1128) (.exec 0x104c4e (fun s => s.RIP = 0x104c4e) (xorR32R32Effect 0x104c4e 3 12 3) (Reg.operands [.gpr 12, .gpr 3] [])) #v[1125, 1121]
    (.letOp (n := 1129) (.out 0x104c51 (andR32Imm32Effect 0x104c51 7 12 0x2310) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[1127]
    (.letOp (n := 1130) (.exec 0x104c51 (fun s => s.RIP = 0x104c51) (andR32Imm32Effect 0x104c51 7 12 0x2310) (Reg.operands [.gpr 12] [])) #v[1127]
    (.letOp (n := 1131) (.out 0x104c58 (xorR32R32Effect 0x104c58 3 3 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 12] []) (.reg (.gpr 3))) #v[1121, 1129]
    (.letOp (n := 1132) (.exec 0x104c58 (fun s => s.RIP = 0x104c58) (xorR32R32Effect 0x104c58 3 3 12) (Reg.operands [.gpr 3, .gpr 12] [])) #v[1121, 1129]
    (.letOp (n := 1133) (.out 0x104c5b (shlR32Effect 0x104c5b 4 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[1129]
    (.letOp (n := 1134) (.exec 0x104c5b (fun s => s.RIP = 0x104c5b) (shlR32Effect 0x104c5b 4 12 2) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1129]
    (.letOp (n := 1135) (.out 0x104c5f (xorR32R32Effect 0x104c5f 3 12 3) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 3] []) (.reg (.gpr 12))) #v[1133, 1131]
    (.letOp (n := 1136) (.exec 0x104c5f (fun s => s.RIP = 0x104c5f) (xorR32R32Effect 0x104c5f 3 12 3) (Reg.operands [.gpr 12, .gpr 3] [])) #v[1133, 1131]
    (.letOp (n := 1137) (.out 0x104c62 (movR32R32Effect 0x104c62 3 3 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 12] []) (.reg (.gpr 3))) #v[1135]
    (.letOp (n := 1138) (.exec 0x104c62 (fun s => s.RIP = 0x104c62) (movR32R32Effect 0x104c62 3 3 12) (Reg.operands [.gpr 12] [])) #v[1135]
    (.letOp (n := 1139) (.out 0x104c65 (shrR32Effect 0x104c65 2 3 1) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[1137]
    (.letOp (n := 1140) (.exec 0x104c65 (fun s => s.RIP = 0x104c65) (shrR32Effect 0x104c65 2 3 1) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1137]
    (b_l10446f_28)))))))))))))))))))))))))))))))))))))))

def bytes_l10446f_27 : List UInt8 :=
  [0x41, 0xC1, 0xE4, 0x02, 0x41, 0x31, 0xDC, 0x44, 0x89, 0xE3, 0xD1, 0xEB, 0x44, 0x31, 0xE3, 0x81,
    0xE3, 0x50, 0x50, 0x00, 0x00, 0x41, 0x31, 0xDC, 0x01, 0xDB, 0x44, 0x31, 0xE3, 0x66, 0x89, 0x5C,
    0x24, 0x7A, 0x0F, 0xB7, 0x5C, 0x24, 0x7C, 0x41, 0x89, 0xDC, 0x41, 0xC1, 0xEC, 0x02, 0x41, 0x31,
    0xDC, 0x41, 0x81, 0xE4, 0x10, 0x23, 0x00, 0x00, 0x44, 0x31, 0xE3, 0x41, 0xC1, 0xE4, 0x02, 0x41,
    0x31, 0xDC, 0x44, 0x89, 0xE3, 0xD1, 0xEB] ++ bytes_l10446f_28

theorem code_l10446f_27 : ∀ x ∈ codeRange 0x104c20 bytes_l10446f_27, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x4c20 71 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10446f_28

def b_l10446f_26 : Block Op Label signature Reg.count 1062 :=
  .letOp (n := 1062) (.out 0x104bd3 (movR32R32Effect 0x104bd3 3 12 3) (EffectPart.reads (.reg (.gpr 12)) [.gpr 3] []) (.reg (.gpr 12))) #v[1060]
    (.letOp (n := 1063) (.exec 0x104bd3 (fun s => s.RIP = 0x104bd3) (movR32R32Effect 0x104bd3 3 12 3) (Reg.operands [.gpr 3] [])) #v[1060]
    (.letOp (n := 1064) (.out 0x104bd6 (shrR32Effect 0x104bd6 4 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[1062]
    (.letOp (n := 1065) (.exec 0x104bd6 (fun s => s.RIP = 0x104bd6) (shrR32Effect 0x104bd6 4 12 2) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1062]
    (.letOp (n := 1066) (.out 0x104bda (xorR32R32Effect 0x104bda 3 12 3) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 3] []) (.reg (.gpr 12))) #v[1064, 1060]
    (.letOp (n := 1067) (.exec 0x104bda (fun s => s.RIP = 0x104bda) (xorR32R32Effect 0x104bda 3 12 3) (Reg.operands [.gpr 12, .gpr 3] [])) #v[1064, 1060]
    (.letOp (n := 1068) (.out 0x104bdd (andR32Imm32Effect 0x104bdd 7 12 0x2310) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[1066]
    (.letOp (n := 1069) (.exec 0x104bdd (fun s => s.RIP = 0x104bdd) (andR32Imm32Effect 0x104bdd 7 12 0x2310) (Reg.operands [.gpr 12] [])) #v[1066]
    (.letOp (n := 1070) (.out 0x104be4 (xorR32R32Effect 0x104be4 3 3 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 12] []) (.reg (.gpr 3))) #v[1060, 1068]
    (.letOp (n := 1071) (.exec 0x104be4 (fun s => s.RIP = 0x104be4) (xorR32R32Effect 0x104be4 3 3 12) (Reg.operands [.gpr 3, .gpr 12] [])) #v[1060, 1068]
    (.letOp (n := 1072) (.out 0x104be7 (shlR32Effect 0x104be7 4 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[1068]
    (.letOp (n := 1073) (.exec 0x104be7 (fun s => s.RIP = 0x104be7) (shlR32Effect 0x104be7 4 12 2) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1068]
    (.letOp (n := 1074) (.out 0x104beb (xorR32R32Effect 0x104beb 3 12 3) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 3] []) (.reg (.gpr 12))) #v[1072, 1070]
    (.letOp (n := 1075) (.exec 0x104beb (fun s => s.RIP = 0x104beb) (xorR32R32Effect 0x104beb 3 12 3) (Reg.operands [.gpr 12, .gpr 3] [])) #v[1072, 1070]
    (.letOp (n := 1076) (.out 0x104bee (movR32R32Effect 0x104bee 3 15 12) (EffectPart.reads (.reg (.gpr 15)) [.gpr 12] []) (.reg (.gpr 15))) #v[1074]
    (.letOp (n := 1077) (.exec 0x104bee (fun s => s.RIP = 0x104bee) (movR32R32Effect 0x104bee 3 15 12) (Reg.operands [.gpr 12] [])) #v[1074]
    (.letOp (n := 1078) (.out 0x104bf1 (shrR32Effect 0x104bf1 3 15 1) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[1076]
    (.letOp (n := 1079) (.exec 0x104bf1 (fun s => s.RIP = 0x104bf1) (shrR32Effect 0x104bf1 3 15 1) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1076]
    (.letOp (n := 1080) (.out 0x104bf4 (xorR32R32Effect 0x104bf4 3 15 12) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 12] []) (.reg (.gpr 15))) #v[1078, 1074]
    (.letOp (n := 1081) (.exec 0x104bf4 (fun s => s.RIP = 0x104bf4) (xorR32R32Effect 0x104bf4 3 15 12) (Reg.operands [.gpr 15, .gpr 12] [])) #v[1078, 1074]
    (.letOp (n := 1082) (.out 0x104bf7 (andR32Imm32Effect 0x104bf7 7 15 0x5050) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15] []) (.reg (.gpr 15))) #v[1080]
    (.letOp (n := 1083) (.exec 0x104bf7 (fun s => s.RIP = 0x104bf7) (andR32Imm32Effect 0x104bf7 7 15 0x5050) (Reg.operands [.gpr 15] [])) #v[1080]
    (.letOp (n := 1084) (.out 0x104bfe (xorR32R32Effect 0x104bfe 3 12 15) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 15] []) (.reg (.gpr 12))) #v[1074, 1082]
    (.letOp (n := 1085) (.exec 0x104bfe (fun s => s.RIP = 0x104bfe) (xorR32R32Effect 0x104bfe 3 12 15) (Reg.operands [.gpr 12, .gpr 15] [])) #v[1074, 1082]
    (.letOp (n := 1086) (.out 0x104c01 (addR32R32Effect 0x104c01 3 15 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 15] []) (.reg (.gpr 15))) #v[1082, 1082]
    (.letOp (n := 1087) (.exec 0x104c01 (fun s => s.RIP = 0x104c01) (addR32R32Effect 0x104c01 3 15 15) (Reg.operands [.gpr 15, .gpr 15] [])) #v[1082, 1082]
    (.letOp (n := 1088) (.out 0x104c04 (xorR32R32Effect 0x104c04 3 15 12) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 12] []) (.reg (.gpr 15))) #v[1086, 1084]
    (.letOp (n := 1089) (.exec 0x104c04 (fun s => s.RIP = 0x104c04) (xorR32R32Effect 0x104c04 3 15 12) (Reg.operands [.gpr 15, .gpr 12] [])) #v[1086, 1084]
    (.letOp (n := 1090) (.out 0x104c07 (movzxR32M16Effect 0x104c07 5 3 (.sib 4 none 0 (.d8 0x7a))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 1091) (.exec 0x104c07 (LoadPre 0x104c07 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7a)) s (0x104c07 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x104c07 5 3 (.sib 4 none 0 (.d8 0x7a))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1092) (.out 0x104c0c (movR32R32Effect 0x104c0c 3 12 3) (EffectPart.reads (.reg (.gpr 12)) [.gpr 3] []) (.reg (.gpr 12))) #v[1090]
    (.letOp (n := 1093) (.exec 0x104c0c (fun s => s.RIP = 0x104c0c) (movR32R32Effect 0x104c0c 3 12 3) (Reg.operands [.gpr 3] [])) #v[1090]
    (.letOp (n := 1094) (.out 0x104c0f (shrR32Effect 0x104c0f 4 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[1092]
    (.letOp (n := 1095) (.exec 0x104c0f (fun s => s.RIP = 0x104c0f) (shrR32Effect 0x104c0f 4 12 2) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1092]
    (.letOp (n := 1096) (.out 0x104c13 (xorR32R32Effect 0x104c13 3 12 3) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 3] []) (.reg (.gpr 12))) #v[1094, 1090]
    (.letOp (n := 1097) (.exec 0x104c13 (fun s => s.RIP = 0x104c13) (xorR32R32Effect 0x104c13 3 12 3) (Reg.operands [.gpr 12, .gpr 3] [])) #v[1094, 1090]
    (.letOp (n := 1098) (.out 0x104c16 (andR32Imm32Effect 0x104c16 7 12 0x2310) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[1096]
    (.letOp (n := 1099) (.exec 0x104c16 (fun s => s.RIP = 0x104c16) (andR32Imm32Effect 0x104c16 7 12 0x2310) (Reg.operands [.gpr 12] [])) #v[1096]
    (.letOp (n := 1100) (.out 0x104c1d (xorR32R32Effect 0x104c1d 3 3 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 12] []) (.reg (.gpr 3))) #v[1090, 1098]
    (.letOp (n := 1101) (.exec 0x104c1d (fun s => s.RIP = 0x104c1d) (xorR32R32Effect 0x104c1d 3 3 12) (Reg.operands [.gpr 3, .gpr 12] [])) #v[1090, 1098]
    (b_l10446f_27))))))))))))))))))))))))))))))))))))))))

def bytes_l10446f_26 : List UInt8 :=
  [0x41, 0x89, 0xDC, 0x41, 0xC1, 0xEC, 0x02, 0x41, 0x31, 0xDC, 0x41, 0x81, 0xE4, 0x10, 0x23, 0x00,
    0x00, 0x44, 0x31, 0xE3, 0x41, 0xC1, 0xE4, 0x02, 0x41, 0x31, 0xDC, 0x45, 0x89, 0xE7, 0x41, 0xD1,
    0xEF, 0x45, 0x31, 0xE7, 0x41, 0x81, 0xE7, 0x50, 0x50, 0x00, 0x00, 0x45, 0x31, 0xFC, 0x45, 0x01,
    0xFF, 0x45, 0x31, 0xE7, 0x0F, 0xB7, 0x5C, 0x24, 0x7A, 0x41, 0x89, 0xDC, 0x41, 0xC1, 0xEC, 0x02,
    0x41, 0x31, 0xDC, 0x41, 0x81, 0xE4, 0x10, 0x23, 0x00, 0x00, 0x44, 0x31, 0xE3] ++ bytes_l10446f_27

theorem code_l10446f_26 : ∀ x ∈ codeRange 0x104bd3 bytes_l10446f_26, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x4bd3 77 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10446f_27

def b_l10446f_25 : Block Op Label signature Reg.count 1023 :=
  .letOp (n := 1023) (.out 0x104b83 (shlR32Effect 0x104b83 3 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[1019]
    (.letOp (n := 1024) (.exec 0x104b83 (fun s => s.RIP = 0x104b83) (shlR32Effect 0x104b83 3 5 2) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1019]
    (.letOp (n := 1025) (.out 0x104b86 (xorR32R32Effect 0x104b86 2 5 3) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 3] []) (.reg (.gpr 5))) #v[1023, 1021]
    (.letOp (n := 1026) (.exec 0x104b86 (fun s => s.RIP = 0x104b86) (xorR32R32Effect 0x104b86 2 5 3) (Reg.operands [.gpr 5, .gpr 3] [])) #v[1023, 1021]
    (.letOp (n := 1027) (.out 0x104b88 (movzxR32M16Effect 0x104b88 5 3 (.sib 4 none 0 (.d8 0x74))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 1028) (.exec 0x104b88 (LoadPre 0x104b88 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x74)) s (0x104b88 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x104b88 5 3 (.sib 4 none 0 (.d8 0x74))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1029) (.out 0x104b8d (movR32R32Effect 0x104b8d 3 14 3) (EffectPart.reads (.reg (.gpr 14)) [.gpr 3] []) (.reg (.gpr 14))) #v[1027]
    (.letOp (n := 1030) (.exec 0x104b8d (fun s => s.RIP = 0x104b8d) (movR32R32Effect 0x104b8d 3 14 3) (Reg.operands [.gpr 3] [])) #v[1027]
    (.letOp (n := 1031) (.out 0x104b90 (shrR32Effect 0x104b90 4 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[1029]
    (.letOp (n := 1032) (.exec 0x104b90 (fun s => s.RIP = 0x104b90) (shrR32Effect 0x104b90 4 14 2) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1029]
    (.letOp (n := 1033) (.out 0x104b94 (xorR32R32Effect 0x104b94 3 14 3) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 3] []) (.reg (.gpr 14))) #v[1031, 1027]
    (.letOp (n := 1034) (.exec 0x104b94 (fun s => s.RIP = 0x104b94) (xorR32R32Effect 0x104b94 3 14 3) (Reg.operands [.gpr 14, .gpr 3] [])) #v[1031, 1027]
    (.letOp (n := 1035) (.out 0x104b97 (andR32Imm32Effect 0x104b97 7 14 0x3030) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14] []) (.reg (.gpr 14))) #v[1033]
    (.letOp (n := 1036) (.exec 0x104b97 (fun s => s.RIP = 0x104b97) (andR32Imm32Effect 0x104b97 7 14 0x3030) (Reg.operands [.gpr 14] [])) #v[1033]
    (.letOp (n := 1037) (.out 0x104b9e (xorR32R32Effect 0x104b9e 3 3 14) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 14] []) (.reg (.gpr 3))) #v[1027, 1035]
    (.letOp (n := 1038) (.exec 0x104b9e (fun s => s.RIP = 0x104b9e) (xorR32R32Effect 0x104b9e 3 3 14) (Reg.operands [.gpr 3, .gpr 14] [])) #v[1027, 1035]
    (.letOp (n := 1039) (.out 0x104ba1 (shlR32Effect 0x104ba1 4 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[1035]
    (.letOp (n := 1040) (.exec 0x104ba1 (fun s => s.RIP = 0x104ba1) (shlR32Effect 0x104ba1 4 14 2) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1035]
    (.letOp (n := 1041) (.out 0x104ba5 (xorR32R32Effect 0x104ba5 3 14 3) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 3] []) (.reg (.gpr 14))) #v[1039, 1037]
    (.letOp (n := 1042) (.exec 0x104ba5 (fun s => s.RIP = 0x104ba5) (xorR32R32Effect 0x104ba5 3 14 3) (Reg.operands [.gpr 14, .gpr 3] [])) #v[1039, 1037]
    (.letOp (n := 1043) (.out 0x104ba8 (movzxR32M16Effect 0x104ba8 5 3 (.sib 4 none 0 (.d8 0x76))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 1044) (.exec 0x104ba8 (LoadPre 0x104ba8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x76)) s (0x104ba8 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x104ba8 5 3 (.sib 4 none 0 (.d8 0x76))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1045) (.out 0x104bad (movR32R32Effect 0x104bad 3 15 3) (EffectPart.reads (.reg (.gpr 15)) [.gpr 3] []) (.reg (.gpr 15))) #v[1043]
    (.letOp (n := 1046) (.exec 0x104bad (fun s => s.RIP = 0x104bad) (movR32R32Effect 0x104bad 3 15 3) (Reg.operands [.gpr 3] [])) #v[1043]
    (.letOp (n := 1047) (.out 0x104bb0 (shrR32Effect 0x104bb0 4 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[1045]
    (.letOp (n := 1048) (.exec 0x104bb0 (fun s => s.RIP = 0x104bb0) (shrR32Effect 0x104bb0 4 15 2) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1045]
    (.letOp (n := 1049) (.out 0x104bb4 (xorR32R32Effect 0x104bb4 3 15 3) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 3] []) (.reg (.gpr 15))) #v[1047, 1043]
    (.letOp (n := 1050) (.exec 0x104bb4 (fun s => s.RIP = 0x104bb4) (xorR32R32Effect 0x104bb4 3 15 3) (Reg.operands [.gpr 15, .gpr 3] [])) #v[1047, 1043]
    (.letOp (n := 1051) (.out 0x104bb7 (andR32Imm32Effect 0x104bb7 7 15 0x3030) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15] []) (.reg (.gpr 15))) #v[1049]
    (.letOp (n := 1052) (.exec 0x104bb7 (fun s => s.RIP = 0x104bb7) (andR32Imm32Effect 0x104bb7 7 15 0x3030) (Reg.operands [.gpr 15] [])) #v[1049]
    (.letOp (n := 1053) (.out 0x104bbe (xorR32R32Effect 0x104bbe 3 3 15) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 15] []) (.reg (.gpr 3))) #v[1043, 1051]
    (.letOp (n := 1054) (.exec 0x104bbe (fun s => s.RIP = 0x104bbe) (xorR32R32Effect 0x104bbe 3 3 15) (Reg.operands [.gpr 3, .gpr 15] [])) #v[1043, 1051]
    (.letOp (n := 1055) (.out 0x104bc1 (shlR32Effect 0x104bc1 4 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[1051]
    (.letOp (n := 1056) (.exec 0x104bc1 (fun s => s.RIP = 0x104bc1) (shlR32Effect 0x104bc1 4 15 2) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1051]
    (.letOp (n := 1057) (.out 0x104bc5 (xorR32R32Effect 0x104bc5 3 15 3) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 3] []) (.reg (.gpr 15))) #v[1055, 1053]
    (.letOp (n := 1058) (.exec 0x104bc5 (fun s => s.RIP = 0x104bc5) (xorR32R32Effect 0x104bc5 3 15 3) (Reg.operands [.gpr 15, .gpr 3] [])) #v[1055, 1053]
    (.letOp (n := 1059) (.exec 0x104bc8 (StorePre 0x104bc8 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x76)) s (0x104bc8 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x104bc8 6 15 (.sib 4 none 0 (.d8 0x76))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[1057, 4]
    (.letOp (n := 1060) (.out 0x104bce (movzxR32M16Effect 0x104bce 5 3 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 1061) (.exec 0x104bce (LoadPre 0x104bce (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x104bce + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x104bce 5 3 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l10446f_26)))))))))))))))))))))))))))))))))))))))

def bytes_l10446f_25 : List UInt8 :=
  [0xC1, 0xE5, 0x02, 0x31, 0xDD, 0x0F, 0xB7, 0x5C, 0x24, 0x74, 0x41, 0x89, 0xDE, 0x41, 0xC1, 0xEE,
    0x02, 0x41, 0x31, 0xDE, 0x41, 0x81, 0xE6, 0x30, 0x30, 0x00, 0x00, 0x44, 0x31, 0xF3, 0x41, 0xC1,
    0xE6, 0x02, 0x41, 0x31, 0xDE, 0x0F, 0xB7, 0x5C, 0x24, 0x76, 0x41, 0x89, 0xDF, 0x41, 0xC1, 0xEF,
    0x02, 0x41, 0x31, 0xDF, 0x41, 0x81, 0xE7, 0x30, 0x30, 0x00, 0x00, 0x44, 0x31, 0xFB, 0x41, 0xC1,
    0xE7, 0x02, 0x41, 0x31, 0xDF, 0x66, 0x44, 0x89, 0x7C, 0x24, 0x76, 0x0F, 0xB7, 0x5C, 0x24, 0x78] ++ bytes_l10446f_26

theorem code_l10446f_25 : ∀ x ∈ codeRange 0x104b83 bytes_l10446f_25, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x4b83 80 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10446f_26

def b_l10446f_24 : Block Op Label signature Reg.count 985 :=
  .letOp (n := 985) (.out 0x104b3f (andR32Imm32Effect 0x104b3f 6 5 0x3030) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5] []) (.reg (.gpr 5))) #v[983]
    (.letOp (n := 986) (.exec 0x104b3f (fun s => s.RIP = 0x104b3f) (andR32Imm32Effect 0x104b3f 6 5 0x3030) (Reg.operands [.gpr 5] [])) #v[983]
    (.letOp (n := 987) (.out 0x104b45 (xorR32R32Effect 0x104b45 2 3 5) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 5] []) (.reg (.gpr 3))) #v[977, 985]
    (.letOp (n := 988) (.exec 0x104b45 (fun s => s.RIP = 0x104b45) (xorR32R32Effect 0x104b45 2 3 5) (Reg.operands [.gpr 3, .gpr 5] [])) #v[977, 985]
    (.letOp (n := 989) (.out 0x104b47 (shlR32Effect 0x104b47 3 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[985]
    (.letOp (n := 990) (.exec 0x104b47 (fun s => s.RIP = 0x104b47) (shlR32Effect 0x104b47 3 5 2) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[985]
    (.letOp (n := 991) (.out 0x104b4a (xorR32R32Effect 0x104b4a 2 5 3) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 3] []) (.reg (.gpr 5))) #v[989, 987]
    (.letOp (n := 992) (.exec 0x104b4a (fun s => s.RIP = 0x104b4a) (xorR32R32Effect 0x104b4a 2 5 3) (Reg.operands [.gpr 5, .gpr 3] [])) #v[989, 987]
    (.letOp (n := 993) (.exec 0x104b4c (StorePre 0x104b4c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6e)) s (0x104b4c + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x104b4c 5 5 (.sib 4 none 0 (.d8 0x6e))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[991, 4]
    (.letOp (n := 994) (.out 0x104b51 (movzxR32M16Effect 0x104b51 5 3 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 995) (.exec 0x104b51 (LoadPre 0x104b51 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x104b51 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x104b51 5 3 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 996) (.out 0x104b56 (movR32R32Effect 0x104b56 2 5 3) (EffectPart.reads (.reg (.gpr 5)) [.gpr 3] []) (.reg (.gpr 5))) #v[994]
    (.letOp (n := 997) (.exec 0x104b56 (fun s => s.RIP = 0x104b56) (movR32R32Effect 0x104b56 2 5 3) (Reg.operands [.gpr 3] [])) #v[994]
    (.letOp (n := 998) (.out 0x104b58 (shrR32Effect 0x104b58 3 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[996]
    (.letOp (n := 999) (.exec 0x104b58 (fun s => s.RIP = 0x104b58) (shrR32Effect 0x104b58 3 5 2) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[996]
    (.letOp (n := 1000) (.out 0x104b5b (xorR32R32Effect 0x104b5b 2 5 3) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 3] []) (.reg (.gpr 5))) #v[998, 994]
    (.letOp (n := 1001) (.exec 0x104b5b (fun s => s.RIP = 0x104b5b) (xorR32R32Effect 0x104b5b 2 5 3) (Reg.operands [.gpr 5, .gpr 3] [])) #v[998, 994]
    (.letOp (n := 1002) (.out 0x104b5d (andR32Imm32Effect 0x104b5d 6 5 0x3030) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5] []) (.reg (.gpr 5))) #v[1000]
    (.letOp (n := 1003) (.exec 0x104b5d (fun s => s.RIP = 0x104b5d) (andR32Imm32Effect 0x104b5d 6 5 0x3030) (Reg.operands [.gpr 5] [])) #v[1000]
    (.letOp (n := 1004) (.out 0x104b63 (xorR32R32Effect 0x104b63 2 3 5) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 5] []) (.reg (.gpr 3))) #v[994, 1002]
    (.letOp (n := 1005) (.exec 0x104b63 (fun s => s.RIP = 0x104b63) (xorR32R32Effect 0x104b63 2 3 5) (Reg.operands [.gpr 3, .gpr 5] [])) #v[994, 1002]
    (.letOp (n := 1006) (.out 0x104b65 (shlR32Effect 0x104b65 3 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[1002]
    (.letOp (n := 1007) (.exec 0x104b65 (fun s => s.RIP = 0x104b65) (shlR32Effect 0x104b65 3 5 2) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1002]
    (.letOp (n := 1008) (.out 0x104b68 (xorR32R32Effect 0x104b68 2 5 3) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 3] []) (.reg (.gpr 5))) #v[1006, 1004]
    (.letOp (n := 1009) (.exec 0x104b68 (fun s => s.RIP = 0x104b68) (xorR32R32Effect 0x104b68 2 5 3) (Reg.operands [.gpr 5, .gpr 3] [])) #v[1006, 1004]
    (.letOp (n := 1010) (.exec 0x104b6a (StorePre 0x104b6a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x104b6a + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x104b6a 5 5 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[1008, 4]
    (.letOp (n := 1011) (.out 0x104b6f (movzxR32M16Effect 0x104b6f 5 3 (.sib 4 none 0 (.d8 0x72))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 1012) (.exec 0x104b6f (LoadPre 0x104b6f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x72)) s (0x104b6f + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x104b6f 5 3 (.sib 4 none 0 (.d8 0x72))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1013) (.out 0x104b74 (movR32R32Effect 0x104b74 2 5 3) (EffectPart.reads (.reg (.gpr 5)) [.gpr 3] []) (.reg (.gpr 5))) #v[1011]
    (.letOp (n := 1014) (.exec 0x104b74 (fun s => s.RIP = 0x104b74) (movR32R32Effect 0x104b74 2 5 3) (Reg.operands [.gpr 3] [])) #v[1011]
    (.letOp (n := 1015) (.out 0x104b76 (shrR32Effect 0x104b76 3 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[1013]
    (.letOp (n := 1016) (.exec 0x104b76 (fun s => s.RIP = 0x104b76) (shrR32Effect 0x104b76 3 5 2) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1013]
    (.letOp (n := 1017) (.out 0x104b79 (xorR32R32Effect 0x104b79 2 5 3) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 3] []) (.reg (.gpr 5))) #v[1015, 1011]
    (.letOp (n := 1018) (.exec 0x104b79 (fun s => s.RIP = 0x104b79) (xorR32R32Effect 0x104b79 2 5 3) (Reg.operands [.gpr 5, .gpr 3] [])) #v[1015, 1011]
    (.letOp (n := 1019) (.out 0x104b7b (andR32Imm32Effect 0x104b7b 6 5 0x3030) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5] []) (.reg (.gpr 5))) #v[1017]
    (.letOp (n := 1020) (.exec 0x104b7b (fun s => s.RIP = 0x104b7b) (andR32Imm32Effect 0x104b7b 6 5 0x3030) (Reg.operands [.gpr 5] [])) #v[1017]
    (.letOp (n := 1021) (.out 0x104b81 (xorR32R32Effect 0x104b81 2 3 5) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 5] []) (.reg (.gpr 3))) #v[1011, 1019]
    (.letOp (n := 1022) (.exec 0x104b81 (fun s => s.RIP = 0x104b81) (xorR32R32Effect 0x104b81 2 3 5) (Reg.operands [.gpr 3, .gpr 5] [])) #v[1011, 1019]
    (b_l10446f_25))))))))))))))))))))))))))))))))))))))

def bytes_l10446f_24 : List UInt8 :=
  [0x81, 0xE5, 0x30, 0x30, 0x00, 0x00, 0x31, 0xEB, 0xC1, 0xE5, 0x02, 0x31, 0xDD, 0x66, 0x89, 0x6C,
    0x24, 0x6E, 0x0F, 0xB7, 0x5C, 0x24, 0x70, 0x89, 0xDD, 0xC1, 0xED, 0x02, 0x31, 0xDD, 0x81, 0xE5,
    0x30, 0x30, 0x00, 0x00, 0x31, 0xEB, 0xC1, 0xE5, 0x02, 0x31, 0xDD, 0x66, 0x89, 0x6C, 0x24, 0x70,
    0x0F, 0xB7, 0x5C, 0x24, 0x72, 0x89, 0xDD, 0xC1, 0xED, 0x02, 0x31, 0xDD, 0x81, 0xE5, 0x30, 0x30,
    0x00, 0x00, 0x31, 0xEB] ++ bytes_l10446f_25

theorem code_l10446f_24 : ∀ x ∈ codeRange 0x104b3f bytes_l10446f_24, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x4b3f 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10446f_25

def b_l10446f_23 : Block Op Label signature Reg.count 946 :=
  .letOp (n := 946) (.out 0x104afa (movR32R32Effect 0x104afa 3 11 3) (EffectPart.reads (.reg (.gpr 11)) [.gpr 3] []) (.reg (.gpr 11))) #v[944]
    (.letOp (n := 947) (.exec 0x104afa (fun s => s.RIP = 0x104afa) (movR32R32Effect 0x104afa 3 11 3) (Reg.operands [.gpr 3] [])) #v[944]
    (.letOp (n := 948) (.out 0x104afd (shrR32Effect 0x104afd 4 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[946]
    (.letOp (n := 949) (.exec 0x104afd (fun s => s.RIP = 0x104afd) (shrR32Effect 0x104afd 4 11 2) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[946]
    (.letOp (n := 950) (.out 0x104b01 (xorR32R32Effect 0x104b01 3 11 3) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 3] []) (.reg (.gpr 11))) #v[948, 944]
    (.letOp (n := 951) (.exec 0x104b01 (fun s => s.RIP = 0x104b01) (xorR32R32Effect 0x104b01 3 11 3) (Reg.operands [.gpr 11, .gpr 3] [])) #v[948, 944]
    (.letOp (n := 952) (.out 0x104b04 (andR32Imm32Effect 0x104b04 7 11 0x3030) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11] []) (.reg (.gpr 11))) #v[950]
    (.letOp (n := 953) (.exec 0x104b04 (fun s => s.RIP = 0x104b04) (andR32Imm32Effect 0x104b04 7 11 0x3030) (Reg.operands [.gpr 11] [])) #v[950]
    (.letOp (n := 954) (.out 0x104b0b (xorR32R32Effect 0x104b0b 3 3 11) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 11] []) (.reg (.gpr 3))) #v[944, 952]
    (.letOp (n := 955) (.exec 0x104b0b (fun s => s.RIP = 0x104b0b) (xorR32R32Effect 0x104b0b 3 3 11) (Reg.operands [.gpr 3, .gpr 11] [])) #v[944, 952]
    (.letOp (n := 956) (.out 0x104b0e (shlR32Effect 0x104b0e 4 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[952]
    (.letOp (n := 957) (.exec 0x104b0e (fun s => s.RIP = 0x104b0e) (shlR32Effect 0x104b0e 4 11 2) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[952]
    (.letOp (n := 958) (.out 0x104b12 (xorR32R32Effect 0x104b12 3 11 3) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 3] []) (.reg (.gpr 11))) #v[956, 954]
    (.letOp (n := 959) (.exec 0x104b12 (fun s => s.RIP = 0x104b12) (xorR32R32Effect 0x104b12 3 11 3) (Reg.operands [.gpr 11, .gpr 3] [])) #v[956, 954]
    (.letOp (n := 960) (.out 0x104b15 (movzxR32M16Effect 0x104b15 5 3 (.sib 4 none 0 (.d8 0x6c))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 961) (.exec 0x104b15 (LoadPre 0x104b15 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6c)) s (0x104b15 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x104b15 5 3 (.sib 4 none 0 (.d8 0x6c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 962) (.out 0x104b1a (movR32R32Effect 0x104b1a 2 5 3) (EffectPart.reads (.reg (.gpr 5)) [.gpr 3] []) (.reg (.gpr 5))) #v[960]
    (.letOp (n := 963) (.exec 0x104b1a (fun s => s.RIP = 0x104b1a) (movR32R32Effect 0x104b1a 2 5 3) (Reg.operands [.gpr 3] [])) #v[960]
    (.letOp (n := 964) (.out 0x104b1c (shrR32Effect 0x104b1c 3 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[962]
    (.letOp (n := 965) (.exec 0x104b1c (fun s => s.RIP = 0x104b1c) (shrR32Effect 0x104b1c 3 5 2) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[962]
    (.letOp (n := 966) (.out 0x104b1f (xorR32R32Effect 0x104b1f 2 5 3) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 3] []) (.reg (.gpr 5))) #v[964, 960]
    (.letOp (n := 967) (.exec 0x104b1f (fun s => s.RIP = 0x104b1f) (xorR32R32Effect 0x104b1f 2 5 3) (Reg.operands [.gpr 5, .gpr 3] [])) #v[964, 960]
    (.letOp (n := 968) (.out 0x104b21 (andR32Imm32Effect 0x104b21 6 5 0x3030) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5] []) (.reg (.gpr 5))) #v[966]
    (.letOp (n := 969) (.exec 0x104b21 (fun s => s.RIP = 0x104b21) (andR32Imm32Effect 0x104b21 6 5 0x3030) (Reg.operands [.gpr 5] [])) #v[966]
    (.letOp (n := 970) (.out 0x104b27 (xorR32R32Effect 0x104b27 2 3 5) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 5] []) (.reg (.gpr 3))) #v[960, 968]
    (.letOp (n := 971) (.exec 0x104b27 (fun s => s.RIP = 0x104b27) (xorR32R32Effect 0x104b27 2 3 5) (Reg.operands [.gpr 3, .gpr 5] [])) #v[960, 968]
    (.letOp (n := 972) (.out 0x104b29 (shlR32Effect 0x104b29 3 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[968]
    (.letOp (n := 973) (.exec 0x104b29 (fun s => s.RIP = 0x104b29) (shlR32Effect 0x104b29 3 5 2) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[968]
    (.letOp (n := 974) (.out 0x104b2c (xorR32R32Effect 0x104b2c 2 5 3) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 3] []) (.reg (.gpr 5))) #v[972, 970]
    (.letOp (n := 975) (.exec 0x104b2c (fun s => s.RIP = 0x104b2c) (xorR32R32Effect 0x104b2c 2 5 3) (Reg.operands [.gpr 5, .gpr 3] [])) #v[972, 970]
    (.letOp (n := 976) (.exec 0x104b2e (StorePre 0x104b2e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6c)) s (0x104b2e + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x104b2e 5 5 (.sib 4 none 0 (.d8 0x6c))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[974, 4]
    (.letOp (n := 977) (.out 0x104b33 (movzxR32M16Effect 0x104b33 5 3 (.sib 4 none 0 (.d8 0x6e))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 978) (.exec 0x104b33 (LoadPre 0x104b33 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6e)) s (0x104b33 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x104b33 5 3 (.sib 4 none 0 (.d8 0x6e))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 979) (.out 0x104b38 (movR32R32Effect 0x104b38 2 5 3) (EffectPart.reads (.reg (.gpr 5)) [.gpr 3] []) (.reg (.gpr 5))) #v[977]
    (.letOp (n := 980) (.exec 0x104b38 (fun s => s.RIP = 0x104b38) (movR32R32Effect 0x104b38 2 5 3) (Reg.operands [.gpr 3] [])) #v[977]
    (.letOp (n := 981) (.out 0x104b3a (shrR32Effect 0x104b3a 3 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[979]
    (.letOp (n := 982) (.exec 0x104b3a (fun s => s.RIP = 0x104b3a) (shrR32Effect 0x104b3a 3 5 2) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[979]
    (.letOp (n := 983) (.out 0x104b3d (xorR32R32Effect 0x104b3d 2 5 3) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 3] []) (.reg (.gpr 5))) #v[981, 977]
    (.letOp (n := 984) (.exec 0x104b3d (fun s => s.RIP = 0x104b3d) (xorR32R32Effect 0x104b3d 2 5 3) (Reg.operands [.gpr 5, .gpr 3] [])) #v[981, 977]
    (b_l10446f_24)))))))))))))))))))))))))))))))))))))))

def bytes_l10446f_23 : List UInt8 :=
  [0x41, 0x89, 0xDB, 0x41, 0xC1, 0xEB, 0x02, 0x41, 0x31, 0xDB, 0x41, 0x81, 0xE3, 0x30, 0x30, 0x00,
    0x00, 0x44, 0x31, 0xDB, 0x41, 0xC1, 0xE3, 0x02, 0x41, 0x31, 0xDB, 0x0F, 0xB7, 0x5C, 0x24, 0x6C,
    0x89, 0xDD, 0xC1, 0xED, 0x02, 0x31, 0xDD, 0x81, 0xE5, 0x30, 0x30, 0x00, 0x00, 0x31, 0xEB, 0xC1,
    0xE5, 0x02, 0x31, 0xDD, 0x66, 0x89, 0x6C, 0x24, 0x6C, 0x0F, 0xB7, 0x5C, 0x24, 0x6E, 0x89, 0xDD,
    0xC1, 0xED, 0x02, 0x31, 0xDD] ++ bytes_l10446f_24

theorem code_l10446f_23 : ∀ x ∈ codeRange 0x104afa bytes_l10446f_23, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x4afa 69 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10446f_24

def b_l10446f_22 : Block Op Label signature Reg.count 907 :=
  .letOp (n := 907) (.out 0x104aab (xorR32R32Effect 0x104aab 3 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 11] []) (.reg (.gpr 10))) #v[897, 905]
    (.letOp (n := 908) (.exec 0x104aab (fun s => s.RIP = 0x104aab) (xorR32R32Effect 0x104aab 3 10 11) (Reg.operands [.gpr 10, .gpr 11] [])) #v[897, 905]
    (.letOp (n := 909) (.out 0x104aae (shlR32Effect 0x104aae 4 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[905]
    (.letOp (n := 910) (.exec 0x104aae (fun s => s.RIP = 0x104aae) (shlR32Effect 0x104aae 4 11 2) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[905]
    (.letOp (n := 911) (.out 0x104ab2 (xorR32R32Effect 0x104ab2 3 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 10] []) (.reg (.gpr 11))) #v[909, 907]
    (.letOp (n := 912) (.exec 0x104ab2 (fun s => s.RIP = 0x104ab2) (xorR32R32Effect 0x104ab2 3 11 10) (Reg.operands [.gpr 11, .gpr 10] [])) #v[909, 907]
    (.letOp (n := 913) (.out 0x104ab5 (movR32R32Effect 0x104ab5 3 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 11] []) (.reg (.gpr 10))) #v[911]
    (.letOp (n := 914) (.exec 0x104ab5 (fun s => s.RIP = 0x104ab5) (movR32R32Effect 0x104ab5 3 10 11) (Reg.operands [.gpr 11] [])) #v[911]
    (.letOp (n := 915) (.out 0x104ab8 (shrR32Effect 0x104ab8 3 10 1) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[913]
    (.letOp (n := 916) (.exec 0x104ab8 (fun s => s.RIP = 0x104ab8) (shrR32Effect 0x104ab8 3 10 1) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[913]
    (.letOp (n := 917) (.out 0x104abb (xorR32R32Effect 0x104abb 3 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 11] []) (.reg (.gpr 10))) #v[915, 911]
    (.letOp (n := 918) (.exec 0x104abb (fun s => s.RIP = 0x104abb) (xorR32R32Effect 0x104abb 3 10 11) (Reg.operands [.gpr 10, .gpr 11] [])) #v[915, 911]
    (.letOp (n := 919) (.out 0x104abe (andR32Imm32Effect 0x104abe 7 10 0x5050) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[917]
    (.letOp (n := 920) (.exec 0x104abe (fun s => s.RIP = 0x104abe) (andR32Imm32Effect 0x104abe 7 10 0x5050) (Reg.operands [.gpr 10] [])) #v[917]
    (.letOp (n := 921) (.out 0x104ac5 (xorR32R32Effect 0x104ac5 3 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 10] []) (.reg (.gpr 11))) #v[911, 919]
    (.letOp (n := 922) (.exec 0x104ac5 (fun s => s.RIP = 0x104ac5) (xorR32R32Effect 0x104ac5 3 11 10) (Reg.operands [.gpr 11, .gpr 10] [])) #v[911, 919]
    (.letOp (n := 923) (.out 0x104ac8 (addR32R32Effect 0x104ac8 3 10 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 10] []) (.reg (.gpr 10))) #v[919, 919]
    (.letOp (n := 924) (.exec 0x104ac8 (fun s => s.RIP = 0x104ac8) (addR32R32Effect 0x104ac8 3 10 10) (Reg.operands [.gpr 10, .gpr 10] [])) #v[919, 919]
    (.letOp (n := 925) (.out 0x104acb (xorR32R32Effect 0x104acb 3 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 11] []) (.reg (.gpr 10))) #v[923, 921]
    (.letOp (n := 926) (.exec 0x104acb (fun s => s.RIP = 0x104acb) (xorR32R32Effect 0x104acb 3 10 11) (Reg.operands [.gpr 10, .gpr 11] [])) #v[923, 921]
    (.letOp (n := 927) (.exec 0x104ace (StorePre 0x104ace 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x66)) s (0x104ace + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x104ace 6 10 (.sib 4 none 0 (.d8 0x66))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[925, 4]
    (.letOp (n := 928) (.out 0x104ad4 (movzxR32M16Effect 0x104ad4 6 11 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 929) (.exec 0x104ad4 (LoadPre 0x104ad4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x104ad4 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x104ad4 6 11 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 930) (.out 0x104ada (movR32R32Effect 0x104ada 3 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 11] []) (.reg (.gpr 10))) #v[928]
    (.letOp (n := 931) (.exec 0x104ada (fun s => s.RIP = 0x104ada) (movR32R32Effect 0x104ada 3 10 11) (Reg.operands [.gpr 11] [])) #v[928]
    (.letOp (n := 932) (.out 0x104add (shrR32Effect 0x104add 4 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[930]
    (.letOp (n := 933) (.exec 0x104add (fun s => s.RIP = 0x104add) (shrR32Effect 0x104add 4 10 2) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[930]
    (.letOp (n := 934) (.out 0x104ae1 (xorR32R32Effect 0x104ae1 3 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 11] []) (.reg (.gpr 10))) #v[932, 928]
    (.letOp (n := 935) (.exec 0x104ae1 (fun s => s.RIP = 0x104ae1) (xorR32R32Effect 0x104ae1 3 10 11) (Reg.operands [.gpr 10, .gpr 11] [])) #v[932, 928]
    (.letOp (n := 936) (.out 0x104ae4 (andR32Imm32Effect 0x104ae4 7 10 0x3030) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[934]
    (.letOp (n := 937) (.exec 0x104ae4 (fun s => s.RIP = 0x104ae4) (andR32Imm32Effect 0x104ae4 7 10 0x3030) (Reg.operands [.gpr 10] [])) #v[934]
    (.letOp (n := 938) (.out 0x104aeb (xorR32R32Effect 0x104aeb 3 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 10] []) (.reg (.gpr 11))) #v[928, 936]
    (.letOp (n := 939) (.exec 0x104aeb (fun s => s.RIP = 0x104aeb) (xorR32R32Effect 0x104aeb 3 11 10) (Reg.operands [.gpr 11, .gpr 10] [])) #v[928, 936]
    (.letOp (n := 940) (.out 0x104aee (shlR32Effect 0x104aee 4 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[936]
    (.letOp (n := 941) (.exec 0x104aee (fun s => s.RIP = 0x104aee) (shlR32Effect 0x104aee 4 10 2) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[936]
    (.letOp (n := 942) (.out 0x104af2 (xorR32R32Effect 0x104af2 3 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 11] []) (.reg (.gpr 10))) #v[940, 938]
    (.letOp (n := 943) (.exec 0x104af2 (fun s => s.RIP = 0x104af2) (xorR32R32Effect 0x104af2 3 10 11) (Reg.operands [.gpr 10, .gpr 11] [])) #v[940, 938]
    (.letOp (n := 944) (.out 0x104af5 (movzxR32M16Effect 0x104af5 5 3 (.sib 4 none 0 (.d8 0x6a))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 945) (.exec 0x104af5 (LoadPre 0x104af5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6a)) s (0x104af5 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x104af5 5 3 (.sib 4 none 0 (.d8 0x6a))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l10446f_23)))))))))))))))))))))))))))))))))))))))

def bytes_l10446f_22 : List UInt8 :=
  [0x45, 0x31, 0xDA, 0x41, 0xC1, 0xE3, 0x02, 0x45, 0x31, 0xD3, 0x45, 0x89, 0xDA, 0x41, 0xD1, 0xEA,
    0x45, 0x31, 0xDA, 0x41, 0x81, 0xE2, 0x50, 0x50, 0x00, 0x00, 0x45, 0x31, 0xD3, 0x45, 0x01, 0xD2,
    0x45, 0x31, 0xDA, 0x66, 0x44, 0x89, 0x54, 0x24, 0x66, 0x44, 0x0F, 0xB7, 0x5C, 0x24, 0x68, 0x45,
    0x89, 0xDA, 0x41, 0xC1, 0xEA, 0x02, 0x45, 0x31, 0xDA, 0x41, 0x81, 0xE2, 0x30, 0x30, 0x00, 0x00,
    0x45, 0x31, 0xD3, 0x41, 0xC1, 0xE2, 0x02, 0x45, 0x31, 0xDA, 0x0F, 0xB7, 0x5C, 0x24, 0x6A] ++ bytes_l10446f_23

theorem code_l10446f_22 : ∀ x ∈ codeRange 0x104aab bytes_l10446f_22, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x4aab 79 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10446f_23

def b_l10446f_21 : Block Op Label signature Reg.count 868 :=
  .letOp (n := 868) (.out 0x104a5a (movR32R32Effect 0x104a5a 3 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 10] []) (.reg (.gpr 11))) #v[866]
    (.letOp (n := 869) (.exec 0x104a5a (fun s => s.RIP = 0x104a5a) (movR32R32Effect 0x104a5a 3 11 10) (Reg.operands [.gpr 10] [])) #v[866]
    (.letOp (n := 870) (.out 0x104a5d (shrR32Effect 0x104a5d 4 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[868]
    (.letOp (n := 871) (.exec 0x104a5d (fun s => s.RIP = 0x104a5d) (shrR32Effect 0x104a5d 4 11 2) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[868]
    (.letOp (n := 872) (.out 0x104a61 (xorR32R32Effect 0x104a61 3 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 10] []) (.reg (.gpr 11))) #v[870, 866]
    (.letOp (n := 873) (.exec 0x104a61 (fun s => s.RIP = 0x104a61) (xorR32R32Effect 0x104a61 3 11 10) (Reg.operands [.gpr 11, .gpr 10] [])) #v[870, 866]
    (.letOp (n := 874) (.out 0x104a64 (andR32Imm32Effect 0x104a64 7 11 0x1320) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11] []) (.reg (.gpr 11))) #v[872]
    (.letOp (n := 875) (.exec 0x104a64 (fun s => s.RIP = 0x104a64) (andR32Imm32Effect 0x104a64 7 11 0x1320) (Reg.operands [.gpr 11] [])) #v[872]
    (.letOp (n := 876) (.out 0x104a6b (xorR32R32Effect 0x104a6b 3 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 11] []) (.reg (.gpr 10))) #v[866, 874]
    (.letOp (n := 877) (.exec 0x104a6b (fun s => s.RIP = 0x104a6b) (xorR32R32Effect 0x104a6b 3 10 11) (Reg.operands [.gpr 10, .gpr 11] [])) #v[866, 874]
    (.letOp (n := 878) (.out 0x104a6e (shlR32Effect 0x104a6e 4 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[874]
    (.letOp (n := 879) (.exec 0x104a6e (fun s => s.RIP = 0x104a6e) (shlR32Effect 0x104a6e 4 11 2) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[874]
    (.letOp (n := 880) (.out 0x104a72 (xorR32R32Effect 0x104a72 3 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 10] []) (.reg (.gpr 11))) #v[878, 876]
    (.letOp (n := 881) (.exec 0x104a72 (fun s => s.RIP = 0x104a72) (xorR32R32Effect 0x104a72 3 11 10) (Reg.operands [.gpr 11, .gpr 10] [])) #v[878, 876]
    (.letOp (n := 882) (.out 0x104a75 (movR32R32Effect 0x104a75 3 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 11] []) (.reg (.gpr 10))) #v[880]
    (.letOp (n := 883) (.exec 0x104a75 (fun s => s.RIP = 0x104a75) (movR32R32Effect 0x104a75 3 10 11) (Reg.operands [.gpr 11] [])) #v[880]
    (.letOp (n := 884) (.out 0x104a78 (shrR32Effect 0x104a78 3 10 1) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[882]
    (.letOp (n := 885) (.exec 0x104a78 (fun s => s.RIP = 0x104a78) (shrR32Effect 0x104a78 3 10 1) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[882]
    (.letOp (n := 886) (.out 0x104a7b (xorR32R32Effect 0x104a7b 3 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 11] []) (.reg (.gpr 10))) #v[884, 880]
    (.letOp (n := 887) (.exec 0x104a7b (fun s => s.RIP = 0x104a7b) (xorR32R32Effect 0x104a7b 3 10 11) (Reg.operands [.gpr 10, .gpr 11] [])) #v[884, 880]
    (.letOp (n := 888) (.out 0x104a7e (andR32Imm32Effect 0x104a7e 7 10 0x5050) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[886]
    (.letOp (n := 889) (.exec 0x104a7e (fun s => s.RIP = 0x104a7e) (andR32Imm32Effect 0x104a7e 7 10 0x5050) (Reg.operands [.gpr 10] [])) #v[886]
    (.letOp (n := 890) (.out 0x104a85 (xorR32R32Effect 0x104a85 3 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 10] []) (.reg (.gpr 11))) #v[880, 888]
    (.letOp (n := 891) (.exec 0x104a85 (fun s => s.RIP = 0x104a85) (xorR32R32Effect 0x104a85 3 11 10) (Reg.operands [.gpr 11, .gpr 10] [])) #v[880, 888]
    (.letOp (n := 892) (.out 0x104a88 (addR32R32Effect 0x104a88 3 10 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 10] []) (.reg (.gpr 10))) #v[888, 888]
    (.letOp (n := 893) (.exec 0x104a88 (fun s => s.RIP = 0x104a88) (addR32R32Effect 0x104a88 3 10 10) (Reg.operands [.gpr 10, .gpr 10] [])) #v[888, 888]
    (.letOp (n := 894) (.out 0x104a8b (xorR32R32Effect 0x104a8b 3 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 11] []) (.reg (.gpr 10))) #v[892, 890]
    (.letOp (n := 895) (.exec 0x104a8b (fun s => s.RIP = 0x104a8b) (xorR32R32Effect 0x104a8b 3 10 11) (Reg.operands [.gpr 10, .gpr 11] [])) #v[892, 890]
    (.letOp (n := 896) (.exec 0x104a8e (StorePre 0x104a8e 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x64)) s (0x104a8e + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x104a8e 6 10 (.sib 4 none 0 (.d8 0x64))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[894, 4]
    (.letOp (n := 897) (.out 0x104a94 (movzxR32M16Effect 0x104a94 6 10 (.sib 4 none 0 (.d8 0x66))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 898) (.exec 0x104a94 (LoadPre 0x104a94 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x66)) s (0x104a94 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x104a94 6 10 (.sib 4 none 0 (.d8 0x66))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 899) (.out 0x104a9a (movR32R32Effect 0x104a9a 3 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 10] []) (.reg (.gpr 11))) #v[897]
    (.letOp (n := 900) (.exec 0x104a9a (fun s => s.RIP = 0x104a9a) (movR32R32Effect 0x104a9a 3 11 10) (Reg.operands [.gpr 10] [])) #v[897]
    (.letOp (n := 901) (.out 0x104a9d (shrR32Effect 0x104a9d 4 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[899]
    (.letOp (n := 902) (.exec 0x104a9d (fun s => s.RIP = 0x104a9d) (shrR32Effect 0x104a9d 4 11 2) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[899]
    (.letOp (n := 903) (.out 0x104aa1 (xorR32R32Effect 0x104aa1 3 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 10] []) (.reg (.gpr 11))) #v[901, 897]
    (.letOp (n := 904) (.exec 0x104aa1 (fun s => s.RIP = 0x104aa1) (xorR32R32Effect 0x104aa1 3 11 10) (Reg.operands [.gpr 11, .gpr 10] [])) #v[901, 897]
    (.letOp (n := 905) (.out 0x104aa4 (andR32Imm32Effect 0x104aa4 7 11 0x1320) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11] []) (.reg (.gpr 11))) #v[903]
    (.letOp (n := 906) (.exec 0x104aa4 (fun s => s.RIP = 0x104aa4) (andR32Imm32Effect 0x104aa4 7 11 0x1320) (Reg.operands [.gpr 11] [])) #v[903]
    (b_l10446f_22)))))))))))))))))))))))))))))))))))))))

def bytes_l10446f_21 : List UInt8 :=
  [0x45, 0x89, 0xD3, 0x41, 0xC1, 0xEB, 0x02, 0x45, 0x31, 0xD3, 0x41, 0x81, 0xE3, 0x20, 0x13, 0x00,
    0x00, 0x45, 0x31, 0xDA, 0x41, 0xC1, 0xE3, 0x02, 0x45, 0x31, 0xD3, 0x45, 0x89, 0xDA, 0x41, 0xD1,
    0xEA, 0x45, 0x31, 0xDA, 0x41, 0x81, 0xE2, 0x50, 0x50, 0x00, 0x00, 0x45, 0x31, 0xD3, 0x45, 0x01,
    0xD2, 0x45, 0x31, 0xDA, 0x66, 0x44, 0x89, 0x54, 0x24, 0x64, 0x44, 0x0F, 0xB7, 0x54, 0x24, 0x66,
    0x45, 0x89, 0xD3, 0x41, 0xC1, 0xEB, 0x02, 0x45, 0x31, 0xD3, 0x41, 0x81, 0xE3, 0x20, 0x13, 0x00,
    0x00] ++ bytes_l10446f_22

theorem code_l10446f_21 : ∀ x ∈ codeRange 0x104a5a bytes_l10446f_21, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x4a5a 81 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10446f_22

def b_l10446f_20 : Block Op Label signature Reg.count 830 :=
  .letOp (n := 830) (.out 0x104a08 (addR32R32Effect 0x104a08 3 10 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 10] []) (.reg (.gpr 10))) #v[826, 826]
    (.letOp (n := 831) (.exec 0x104a08 (fun s => s.RIP = 0x104a08) (addR32R32Effect 0x104a08 3 10 10) (Reg.operands [.gpr 10, .gpr 10] [])) #v[826, 826]
    (.letOp (n := 832) (.out 0x104a0b (xorR32R32Effect 0x104a0b 3 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 11] []) (.reg (.gpr 10))) #v[830, 828]
    (.letOp (n := 833) (.exec 0x104a0b (fun s => s.RIP = 0x104a0b) (xorR32R32Effect 0x104a0b 3 10 11) (Reg.operands [.gpr 10, .gpr 11] [])) #v[830, 828]
    (.letOp (n := 834) (.exec 0x104a0e (StorePre 0x104a0e 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x104a0e + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x104a0e 6 10 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[832, 4]
    (.letOp (n := 835) (.out 0x104a14 (movzxR32M16Effect 0x104a14 6 10 (.sib 4 none 0 (.d8 0x62))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 836) (.exec 0x104a14 (LoadPre 0x104a14 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x62)) s (0x104a14 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x104a14 6 10 (.sib 4 none 0 (.d8 0x62))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 837) (.out 0x104a1a (movR32R32Effect 0x104a1a 3 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 10] []) (.reg (.gpr 11))) #v[835]
    (.letOp (n := 838) (.exec 0x104a1a (fun s => s.RIP = 0x104a1a) (movR32R32Effect 0x104a1a 3 11 10) (Reg.operands [.gpr 10] [])) #v[835]
    (.letOp (n := 839) (.out 0x104a1d (shrR32Effect 0x104a1d 4 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[837]
    (.letOp (n := 840) (.exec 0x104a1d (fun s => s.RIP = 0x104a1d) (shrR32Effect 0x104a1d 4 11 2) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[837]
    (.letOp (n := 841) (.out 0x104a21 (xorR32R32Effect 0x104a21 3 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 10] []) (.reg (.gpr 11))) #v[839, 835]
    (.letOp (n := 842) (.exec 0x104a21 (fun s => s.RIP = 0x104a21) (xorR32R32Effect 0x104a21 3 11 10) (Reg.operands [.gpr 11, .gpr 10] [])) #v[839, 835]
    (.letOp (n := 843) (.out 0x104a24 (andR32Imm32Effect 0x104a24 7 11 0x1320) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11] []) (.reg (.gpr 11))) #v[841]
    (.letOp (n := 844) (.exec 0x104a24 (fun s => s.RIP = 0x104a24) (andR32Imm32Effect 0x104a24 7 11 0x1320) (Reg.operands [.gpr 11] [])) #v[841]
    (.letOp (n := 845) (.out 0x104a2b (xorR32R32Effect 0x104a2b 3 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 11] []) (.reg (.gpr 10))) #v[835, 843]
    (.letOp (n := 846) (.exec 0x104a2b (fun s => s.RIP = 0x104a2b) (xorR32R32Effect 0x104a2b 3 10 11) (Reg.operands [.gpr 10, .gpr 11] [])) #v[835, 843]
    (.letOp (n := 847) (.out 0x104a2e (shlR32Effect 0x104a2e 4 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[843]
    (.letOp (n := 848) (.exec 0x104a2e (fun s => s.RIP = 0x104a2e) (shlR32Effect 0x104a2e 4 11 2) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[843]
    (.letOp (n := 849) (.out 0x104a32 (xorR32R32Effect 0x104a32 3 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 10] []) (.reg (.gpr 11))) #v[847, 845]
    (.letOp (n := 850) (.exec 0x104a32 (fun s => s.RIP = 0x104a32) (xorR32R32Effect 0x104a32 3 11 10) (Reg.operands [.gpr 11, .gpr 10] [])) #v[847, 845]
    (.letOp (n := 851) (.out 0x104a35 (movR32R32Effect 0x104a35 3 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 11] []) (.reg (.gpr 10))) #v[849]
    (.letOp (n := 852) (.exec 0x104a35 (fun s => s.RIP = 0x104a35) (movR32R32Effect 0x104a35 3 10 11) (Reg.operands [.gpr 11] [])) #v[849]
    (.letOp (n := 853) (.out 0x104a38 (shrR32Effect 0x104a38 3 10 1) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[851]
    (.letOp (n := 854) (.exec 0x104a38 (fun s => s.RIP = 0x104a38) (shrR32Effect 0x104a38 3 10 1) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[851]
    (.letOp (n := 855) (.out 0x104a3b (xorR32R32Effect 0x104a3b 3 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 11] []) (.reg (.gpr 10))) #v[853, 849]
    (.letOp (n := 856) (.exec 0x104a3b (fun s => s.RIP = 0x104a3b) (xorR32R32Effect 0x104a3b 3 10 11) (Reg.operands [.gpr 10, .gpr 11] [])) #v[853, 849]
    (.letOp (n := 857) (.out 0x104a3e (andR32Imm32Effect 0x104a3e 7 10 0x5050) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[855]
    (.letOp (n := 858) (.exec 0x104a3e (fun s => s.RIP = 0x104a3e) (andR32Imm32Effect 0x104a3e 7 10 0x5050) (Reg.operands [.gpr 10] [])) #v[855]
    (.letOp (n := 859) (.out 0x104a45 (xorR32R32Effect 0x104a45 3 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 10] []) (.reg (.gpr 11))) #v[849, 857]
    (.letOp (n := 860) (.exec 0x104a45 (fun s => s.RIP = 0x104a45) (xorR32R32Effect 0x104a45 3 11 10) (Reg.operands [.gpr 11, .gpr 10] [])) #v[849, 857]
    (.letOp (n := 861) (.out 0x104a48 (addR32R32Effect 0x104a48 3 10 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 10] []) (.reg (.gpr 10))) #v[857, 857]
    (.letOp (n := 862) (.exec 0x104a48 (fun s => s.RIP = 0x104a48) (addR32R32Effect 0x104a48 3 10 10) (Reg.operands [.gpr 10, .gpr 10] [])) #v[857, 857]
    (.letOp (n := 863) (.out 0x104a4b (xorR32R32Effect 0x104a4b 3 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 11] []) (.reg (.gpr 10))) #v[861, 859]
    (.letOp (n := 864) (.exec 0x104a4b (fun s => s.RIP = 0x104a4b) (xorR32R32Effect 0x104a4b 3 10 11) (Reg.operands [.gpr 10, .gpr 11] [])) #v[861, 859]
    (.letOp (n := 865) (.exec 0x104a4e (StorePre 0x104a4e 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x62)) s (0x104a4e + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x104a4e 6 10 (.sib 4 none 0 (.d8 0x62))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[863, 4]
    (.letOp (n := 866) (.out 0x104a54 (movzxR32M16Effect 0x104a54 6 10 (.sib 4 none 0 (.d8 0x64))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 867) (.exec 0x104a54 (LoadPre 0x104a54 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x64)) s (0x104a54 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x104a54 6 10 (.sib 4 none 0 (.d8 0x64))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l10446f_21))))))))))))))))))))))))))))))))))))))

def bytes_l10446f_20 : List UInt8 :=
  [0x45, 0x01, 0xD2, 0x45, 0x31, 0xDA, 0x66, 0x44, 0x89, 0x54, 0x24, 0x60, 0x44, 0x0F, 0xB7, 0x54,
    0x24, 0x62, 0x45, 0x89, 0xD3, 0x41, 0xC1, 0xEB, 0x02, 0x45, 0x31, 0xD3, 0x41, 0x81, 0xE3, 0x20,
    0x13, 0x00, 0x00, 0x45, 0x31, 0xDA, 0x41, 0xC1, 0xE3, 0x02, 0x45, 0x31, 0xD3, 0x45, 0x89, 0xDA,
    0x41, 0xD1, 0xEA, 0x45, 0x31, 0xDA, 0x41, 0x81, 0xE2, 0x50, 0x50, 0x00, 0x00, 0x45, 0x31, 0xD3,
    0x45, 0x01, 0xD2, 0x45, 0x31, 0xDA, 0x66, 0x44, 0x89, 0x54, 0x24, 0x62, 0x44, 0x0F, 0xB7, 0x54,
    0x24, 0x64] ++ bytes_l10446f_21

theorem code_l10446f_20 : ∀ x ∈ codeRange 0x104a08 bytes_l10446f_20, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x4a08 82 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10446f_21

def b_l10446f_19 : Block Op Label signature Reg.count 791 :=
  .letOp (n := 791) (.out 0x1049b8 (shrR32Effect 0x1049b8 3 10 1) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[789]
    (.letOp (n := 792) (.exec 0x1049b8 (fun s => s.RIP = 0x1049b8) (shrR32Effect 0x1049b8 3 10 1) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[789]
    (.letOp (n := 793) (.out 0x1049bb (xorR32R32Effect 0x1049bb 3 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 11] []) (.reg (.gpr 10))) #v[791, 787]
    (.letOp (n := 794) (.exec 0x1049bb (fun s => s.RIP = 0x1049bb) (xorR32R32Effect 0x1049bb 3 10 11) (Reg.operands [.gpr 10, .gpr 11] [])) #v[791, 787]
    (.letOp (n := 795) (.out 0x1049be (andR32Imm32Effect 0x1049be 7 10 0x5050) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[793]
    (.letOp (n := 796) (.exec 0x1049be (fun s => s.RIP = 0x1049be) (andR32Imm32Effect 0x1049be 7 10 0x5050) (Reg.operands [.gpr 10] [])) #v[793]
    (.letOp (n := 797) (.out 0x1049c5 (xorR32R32Effect 0x1049c5 3 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 10] []) (.reg (.gpr 11))) #v[787, 795]
    (.letOp (n := 798) (.exec 0x1049c5 (fun s => s.RIP = 0x1049c5) (xorR32R32Effect 0x1049c5 3 11 10) (Reg.operands [.gpr 11, .gpr 10] [])) #v[787, 795]
    (.letOp (n := 799) (.out 0x1049c8 (addR32R32Effect 0x1049c8 3 10 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 10] []) (.reg (.gpr 10))) #v[795, 795]
    (.letOp (n := 800) (.exec 0x1049c8 (fun s => s.RIP = 0x1049c8) (addR32R32Effect 0x1049c8 3 10 10) (Reg.operands [.gpr 10, .gpr 10] [])) #v[795, 795]
    (.letOp (n := 801) (.out 0x1049cb (xorR32R32Effect 0x1049cb 3 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 11] []) (.reg (.gpr 10))) #v[799, 797]
    (.letOp (n := 802) (.exec 0x1049cb (fun s => s.RIP = 0x1049cb) (xorR32R32Effect 0x1049cb 3 10 11) (Reg.operands [.gpr 10, .gpr 11] [])) #v[799, 797]
    (.letOp (n := 803) (.exec 0x1049ce (StorePre 0x1049ce 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5e)) s (0x1049ce + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x1049ce 6 10 (.sib 4 none 0 (.d8 0x5e))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[801, 4]
    (.letOp (n := 804) (.out 0x1049d4 (movzxR32M16Effect 0x1049d4 6 10 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 805) (.exec 0x1049d4 (LoadPre 0x1049d4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1049d4 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x1049d4 6 10 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 806) (.out 0x1049da (movR32R32Effect 0x1049da 3 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 10] []) (.reg (.gpr 11))) #v[804]
    (.letOp (n := 807) (.exec 0x1049da (fun s => s.RIP = 0x1049da) (movR32R32Effect 0x1049da 3 11 10) (Reg.operands [.gpr 10] [])) #v[804]
    (.letOp (n := 808) (.out 0x1049dd (shrR32Effect 0x1049dd 4 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[806]
    (.letOp (n := 809) (.exec 0x1049dd (fun s => s.RIP = 0x1049dd) (shrR32Effect 0x1049dd 4 11 2) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[806]
    (.letOp (n := 810) (.out 0x1049e1 (xorR32R32Effect 0x1049e1 3 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 10] []) (.reg (.gpr 11))) #v[808, 804]
    (.letOp (n := 811) (.exec 0x1049e1 (fun s => s.RIP = 0x1049e1) (xorR32R32Effect 0x1049e1 3 11 10) (Reg.operands [.gpr 11, .gpr 10] [])) #v[808, 804]
    (.letOp (n := 812) (.out 0x1049e4 (andR32Imm32Effect 0x1049e4 7 11 0x1320) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11] []) (.reg (.gpr 11))) #v[810]
    (.letOp (n := 813) (.exec 0x1049e4 (fun s => s.RIP = 0x1049e4) (andR32Imm32Effect 0x1049e4 7 11 0x1320) (Reg.operands [.gpr 11] [])) #v[810]
    (.letOp (n := 814) (.out 0x1049eb (xorR32R32Effect 0x1049eb 3 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 11] []) (.reg (.gpr 10))) #v[804, 812]
    (.letOp (n := 815) (.exec 0x1049eb (fun s => s.RIP = 0x1049eb) (xorR32R32Effect 0x1049eb 3 10 11) (Reg.operands [.gpr 10, .gpr 11] [])) #v[804, 812]
    (.letOp (n := 816) (.out 0x1049ee (shlR32Effect 0x1049ee 4 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[812]
    (.letOp (n := 817) (.exec 0x1049ee (fun s => s.RIP = 0x1049ee) (shlR32Effect 0x1049ee 4 11 2) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[812]
    (.letOp (n := 818) (.out 0x1049f2 (xorR32R32Effect 0x1049f2 3 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 10] []) (.reg (.gpr 11))) #v[816, 814]
    (.letOp (n := 819) (.exec 0x1049f2 (fun s => s.RIP = 0x1049f2) (xorR32R32Effect 0x1049f2 3 11 10) (Reg.operands [.gpr 11, .gpr 10] [])) #v[816, 814]
    (.letOp (n := 820) (.out 0x1049f5 (movR32R32Effect 0x1049f5 3 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 11] []) (.reg (.gpr 10))) #v[818]
    (.letOp (n := 821) (.exec 0x1049f5 (fun s => s.RIP = 0x1049f5) (movR32R32Effect 0x1049f5 3 10 11) (Reg.operands [.gpr 11] [])) #v[818]
    (.letOp (n := 822) (.out 0x1049f8 (shrR32Effect 0x1049f8 3 10 1) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[820]
    (.letOp (n := 823) (.exec 0x1049f8 (fun s => s.RIP = 0x1049f8) (shrR32Effect 0x1049f8 3 10 1) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[820]
    (.letOp (n := 824) (.out 0x1049fb (xorR32R32Effect 0x1049fb 3 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 11] []) (.reg (.gpr 10))) #v[822, 818]
    (.letOp (n := 825) (.exec 0x1049fb (fun s => s.RIP = 0x1049fb) (xorR32R32Effect 0x1049fb 3 10 11) (Reg.operands [.gpr 10, .gpr 11] [])) #v[822, 818]
    (.letOp (n := 826) (.out 0x1049fe (andR32Imm32Effect 0x1049fe 7 10 0x5050) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[824]
    (.letOp (n := 827) (.exec 0x1049fe (fun s => s.RIP = 0x1049fe) (andR32Imm32Effect 0x1049fe 7 10 0x5050) (Reg.operands [.gpr 10] [])) #v[824]
    (.letOp (n := 828) (.out 0x104a05 (xorR32R32Effect 0x104a05 3 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 10] []) (.reg (.gpr 11))) #v[818, 826]
    (.letOp (n := 829) (.exec 0x104a05 (fun s => s.RIP = 0x104a05) (xorR32R32Effect 0x104a05 3 11 10) (Reg.operands [.gpr 11, .gpr 10] [])) #v[818, 826]
    (b_l10446f_20)))))))))))))))))))))))))))))))))))))))

def bytes_l10446f_19 : List UInt8 :=
  [0x41, 0xD1, 0xEA, 0x45, 0x31, 0xDA, 0x41, 0x81, 0xE2, 0x50, 0x50, 0x00, 0x00, 0x45, 0x31, 0xD3,
    0x45, 0x01, 0xD2, 0x45, 0x31, 0xDA, 0x66, 0x44, 0x89, 0x54, 0x24, 0x5E, 0x44, 0x0F, 0xB7, 0x54,
    0x24, 0x60, 0x45, 0x89, 0xD3, 0x41, 0xC1, 0xEB, 0x02, 0x45, 0x31, 0xD3, 0x41, 0x81, 0xE3, 0x20,
    0x13, 0x00, 0x00, 0x45, 0x31, 0xDA, 0x41, 0xC1, 0xE3, 0x02, 0x45, 0x31, 0xD3, 0x45, 0x89, 0xDA,
    0x41, 0xD1, 0xEA, 0x45, 0x31, 0xDA, 0x41, 0x81, 0xE2, 0x50, 0x50, 0x00, 0x00, 0x45, 0x31, 0xD3] ++ bytes_l10446f_20

theorem code_l10446f_19 : ∀ x ∈ codeRange 0x1049b8 bytes_l10446f_19, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x49b8 80 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10446f_20

def b_l10446f_18 : Block Op Label signature Reg.count 752 :=
  .letOp (n := 752) (.out 0x10496b (xorR32R32Effect 0x10496b 3 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 11] []) (.reg (.gpr 10))) #v[742, 750]
    (.letOp (n := 753) (.exec 0x10496b (fun s => s.RIP = 0x10496b) (xorR32R32Effect 0x10496b 3 10 11) (Reg.operands [.gpr 10, .gpr 11] [])) #v[742, 750]
    (.letOp (n := 754) (.out 0x10496e (shlR32Effect 0x10496e 4 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[750]
    (.letOp (n := 755) (.exec 0x10496e (fun s => s.RIP = 0x10496e) (shlR32Effect 0x10496e 4 11 2) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[750]
    (.letOp (n := 756) (.out 0x104972 (xorR32R32Effect 0x104972 3 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 10] []) (.reg (.gpr 11))) #v[754, 752]
    (.letOp (n := 757) (.exec 0x104972 (fun s => s.RIP = 0x104972) (xorR32R32Effect 0x104972 3 11 10) (Reg.operands [.gpr 11, .gpr 10] [])) #v[754, 752]
    (.letOp (n := 758) (.out 0x104975 (movR32R32Effect 0x104975 3 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 11] []) (.reg (.gpr 10))) #v[756]
    (.letOp (n := 759) (.exec 0x104975 (fun s => s.RIP = 0x104975) (movR32R32Effect 0x104975 3 10 11) (Reg.operands [.gpr 11] [])) #v[756]
    (.letOp (n := 760) (.out 0x104978 (shrR32Effect 0x104978 3 10 1) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[758]
    (.letOp (n := 761) (.exec 0x104978 (fun s => s.RIP = 0x104978) (shrR32Effect 0x104978 3 10 1) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[758]
    (.letOp (n := 762) (.out 0x10497b (xorR32R32Effect 0x10497b 3 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 11] []) (.reg (.gpr 10))) #v[760, 756]
    (.letOp (n := 763) (.exec 0x10497b (fun s => s.RIP = 0x10497b) (xorR32R32Effect 0x10497b 3 10 11) (Reg.operands [.gpr 10, .gpr 11] [])) #v[760, 756]
    (.letOp (n := 764) (.out 0x10497e (andR32Imm32Effect 0x10497e 7 10 0x5050) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[762]
    (.letOp (n := 765) (.exec 0x10497e (fun s => s.RIP = 0x10497e) (andR32Imm32Effect 0x10497e 7 10 0x5050) (Reg.operands [.gpr 10] [])) #v[762]
    (.letOp (n := 766) (.out 0x104985 (xorR32R32Effect 0x104985 3 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 10] []) (.reg (.gpr 11))) #v[756, 764]
    (.letOp (n := 767) (.exec 0x104985 (fun s => s.RIP = 0x104985) (xorR32R32Effect 0x104985 3 11 10) (Reg.operands [.gpr 11, .gpr 10] [])) #v[756, 764]
    (.letOp (n := 768) (.out 0x104988 (addR32R32Effect 0x104988 3 10 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 10] []) (.reg (.gpr 10))) #v[764, 764]
    (.letOp (n := 769) (.exec 0x104988 (fun s => s.RIP = 0x104988) (addR32R32Effect 0x104988 3 10 10) (Reg.operands [.gpr 10, .gpr 10] [])) #v[764, 764]
    (.letOp (n := 770) (.out 0x10498b (xorR32R32Effect 0x10498b 3 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 11] []) (.reg (.gpr 10))) #v[768, 766]
    (.letOp (n := 771) (.exec 0x10498b (fun s => s.RIP = 0x10498b) (xorR32R32Effect 0x10498b 3 10 11) (Reg.operands [.gpr 10, .gpr 11] [])) #v[768, 766]
    (.letOp (n := 772) (.exec 0x10498e (StorePre 0x10498e 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5c)) s (0x10498e + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x10498e 6 10 (.sib 4 none 0 (.d8 0x5c))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[770, 4]
    (.letOp (n := 773) (.out 0x104994 (movzxR32M16Effect 0x104994 6 10 (.sib 4 none 0 (.d8 0x5e))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 774) (.exec 0x104994 (LoadPre 0x104994 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5e)) s (0x104994 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x104994 6 10 (.sib 4 none 0 (.d8 0x5e))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 775) (.out 0x10499a (movR32R32Effect 0x10499a 3 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 10] []) (.reg (.gpr 11))) #v[773]
    (.letOp (n := 776) (.exec 0x10499a (fun s => s.RIP = 0x10499a) (movR32R32Effect 0x10499a 3 11 10) (Reg.operands [.gpr 10] [])) #v[773]
    (.letOp (n := 777) (.out 0x10499d (shrR32Effect 0x10499d 4 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[775]
    (.letOp (n := 778) (.exec 0x10499d (fun s => s.RIP = 0x10499d) (shrR32Effect 0x10499d 4 11 2) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[775]
    (.letOp (n := 779) (.out 0x1049a1 (xorR32R32Effect 0x1049a1 3 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 10] []) (.reg (.gpr 11))) #v[777, 773]
    (.letOp (n := 780) (.exec 0x1049a1 (fun s => s.RIP = 0x1049a1) (xorR32R32Effect 0x1049a1 3 11 10) (Reg.operands [.gpr 11, .gpr 10] [])) #v[777, 773]
    (.letOp (n := 781) (.out 0x1049a4 (andR32Imm32Effect 0x1049a4 7 11 0x1320) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11] []) (.reg (.gpr 11))) #v[779]
    (.letOp (n := 782) (.exec 0x1049a4 (fun s => s.RIP = 0x1049a4) (andR32Imm32Effect 0x1049a4 7 11 0x1320) (Reg.operands [.gpr 11] [])) #v[779]
    (.letOp (n := 783) (.out 0x1049ab (xorR32R32Effect 0x1049ab 3 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 11] []) (.reg (.gpr 10))) #v[773, 781]
    (.letOp (n := 784) (.exec 0x1049ab (fun s => s.RIP = 0x1049ab) (xorR32R32Effect 0x1049ab 3 10 11) (Reg.operands [.gpr 10, .gpr 11] [])) #v[773, 781]
    (.letOp (n := 785) (.out 0x1049ae (shlR32Effect 0x1049ae 4 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[781]
    (.letOp (n := 786) (.exec 0x1049ae (fun s => s.RIP = 0x1049ae) (shlR32Effect 0x1049ae 4 11 2) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[781]
    (.letOp (n := 787) (.out 0x1049b2 (xorR32R32Effect 0x1049b2 3 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 10] []) (.reg (.gpr 11))) #v[785, 783]
    (.letOp (n := 788) (.exec 0x1049b2 (fun s => s.RIP = 0x1049b2) (xorR32R32Effect 0x1049b2 3 11 10) (Reg.operands [.gpr 11, .gpr 10] [])) #v[785, 783]
    (.letOp (n := 789) (.out 0x1049b5 (movR32R32Effect 0x1049b5 3 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 11] []) (.reg (.gpr 10))) #v[787]
    (.letOp (n := 790) (.exec 0x1049b5 (fun s => s.RIP = 0x1049b5) (movR32R32Effect 0x1049b5 3 10 11) (Reg.operands [.gpr 11] [])) #v[787]
    (b_l10446f_19)))))))))))))))))))))))))))))))))))))))

def bytes_l10446f_18 : List UInt8 :=
  [0x45, 0x31, 0xDA, 0x41, 0xC1, 0xE3, 0x02, 0x45, 0x31, 0xD3, 0x45, 0x89, 0xDA, 0x41, 0xD1, 0xEA,
    0x45, 0x31, 0xDA, 0x41, 0x81, 0xE2, 0x50, 0x50, 0x00, 0x00, 0x45, 0x31, 0xD3, 0x45, 0x01, 0xD2,
    0x45, 0x31, 0xDA, 0x66, 0x44, 0x89, 0x54, 0x24, 0x5C, 0x44, 0x0F, 0xB7, 0x54, 0x24, 0x5E, 0x45,
    0x89, 0xD3, 0x41, 0xC1, 0xEB, 0x02, 0x45, 0x31, 0xD3, 0x41, 0x81, 0xE3, 0x20, 0x13, 0x00, 0x00,
    0x45, 0x31, 0xDA, 0x41, 0xC1, 0xE3, 0x02, 0x45, 0x31, 0xD3, 0x45, 0x89, 0xDA] ++ bytes_l10446f_19

theorem code_l10446f_18 : ∀ x ∈ codeRange 0x10496b bytes_l10446f_18, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x496b 77 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10446f_19

def b_l10446f_17 : Block Op Label signature Reg.count 713 :=
  .letOp (n := 713) (.out 0x10491a (movR32R32Effect 0x10491a 3 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 10] []) (.reg (.gpr 11))) #v[711]
    (.letOp (n := 714) (.exec 0x10491a (fun s => s.RIP = 0x10491a) (movR32R32Effect 0x10491a 3 11 10) (Reg.operands [.gpr 10] [])) #v[711]
    (.letOp (n := 715) (.out 0x10491d (shrR32Effect 0x10491d 4 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[713]
    (.letOp (n := 716) (.exec 0x10491d (fun s => s.RIP = 0x10491d) (shrR32Effect 0x10491d 4 11 2) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[713]
    (.letOp (n := 717) (.out 0x104921 (xorR32R32Effect 0x104921 3 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 10] []) (.reg (.gpr 11))) #v[715, 711]
    (.letOp (n := 718) (.exec 0x104921 (fun s => s.RIP = 0x104921) (xorR32R32Effect 0x104921 3 11 10) (Reg.operands [.gpr 11, .gpr 10] [])) #v[715, 711]
    (.letOp (n := 719) (.out 0x104924 (andR32Imm32Effect 0x104924 7 11 0x1320) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11] []) (.reg (.gpr 11))) #v[717]
    (.letOp (n := 720) (.exec 0x104924 (fun s => s.RIP = 0x104924) (andR32Imm32Effect 0x104924 7 11 0x1320) (Reg.operands [.gpr 11] [])) #v[717]
    (.letOp (n := 721) (.out 0x10492b (xorR32R32Effect 0x10492b 3 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 11] []) (.reg (.gpr 10))) #v[711, 719]
    (.letOp (n := 722) (.exec 0x10492b (fun s => s.RIP = 0x10492b) (xorR32R32Effect 0x10492b 3 10 11) (Reg.operands [.gpr 10, .gpr 11] [])) #v[711, 719]
    (.letOp (n := 723) (.out 0x10492e (shlR32Effect 0x10492e 4 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[719]
    (.letOp (n := 724) (.exec 0x10492e (fun s => s.RIP = 0x10492e) (shlR32Effect 0x10492e 4 11 2) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[719]
    (.letOp (n := 725) (.out 0x104932 (xorR32R32Effect 0x104932 3 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 10] []) (.reg (.gpr 11))) #v[723, 721]
    (.letOp (n := 726) (.exec 0x104932 (fun s => s.RIP = 0x104932) (xorR32R32Effect 0x104932 3 11 10) (Reg.operands [.gpr 11, .gpr 10] [])) #v[723, 721]
    (.letOp (n := 727) (.out 0x104935 (movR32R32Effect 0x104935 3 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 11] []) (.reg (.gpr 10))) #v[725]
    (.letOp (n := 728) (.exec 0x104935 (fun s => s.RIP = 0x104935) (movR32R32Effect 0x104935 3 10 11) (Reg.operands [.gpr 11] [])) #v[725]
    (.letOp (n := 729) (.out 0x104938 (shrR32Effect 0x104938 3 10 1) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[727]
    (.letOp (n := 730) (.exec 0x104938 (fun s => s.RIP = 0x104938) (shrR32Effect 0x104938 3 10 1) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[727]
    (.letOp (n := 731) (.out 0x10493b (xorR32R32Effect 0x10493b 3 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 11] []) (.reg (.gpr 10))) #v[729, 725]
    (.letOp (n := 732) (.exec 0x10493b (fun s => s.RIP = 0x10493b) (xorR32R32Effect 0x10493b 3 10 11) (Reg.operands [.gpr 10, .gpr 11] [])) #v[729, 725]
    (.letOp (n := 733) (.out 0x10493e (andR32Imm32Effect 0x10493e 7 10 0x5050) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[731]
    (.letOp (n := 734) (.exec 0x10493e (fun s => s.RIP = 0x10493e) (andR32Imm32Effect 0x10493e 7 10 0x5050) (Reg.operands [.gpr 10] [])) #v[731]
    (.letOp (n := 735) (.out 0x104945 (xorR32R32Effect 0x104945 3 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 10] []) (.reg (.gpr 11))) #v[725, 733]
    (.letOp (n := 736) (.exec 0x104945 (fun s => s.RIP = 0x104945) (xorR32R32Effect 0x104945 3 11 10) (Reg.operands [.gpr 11, .gpr 10] [])) #v[725, 733]
    (.letOp (n := 737) (.out 0x104948 (addR32R32Effect 0x104948 3 10 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 10] []) (.reg (.gpr 10))) #v[733, 733]
    (.letOp (n := 738) (.exec 0x104948 (fun s => s.RIP = 0x104948) (addR32R32Effect 0x104948 3 10 10) (Reg.operands [.gpr 10, .gpr 10] [])) #v[733, 733]
    (.letOp (n := 739) (.out 0x10494b (xorR32R32Effect 0x10494b 3 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 11] []) (.reg (.gpr 10))) #v[737, 735]
    (.letOp (n := 740) (.exec 0x10494b (fun s => s.RIP = 0x10494b) (xorR32R32Effect 0x10494b 3 10 11) (Reg.operands [.gpr 10, .gpr 11] [])) #v[737, 735]
    (.letOp (n := 741) (.exec 0x10494e (StorePre 0x10494e 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5a)) s (0x10494e + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x10494e 6 10 (.sib 4 none 0 (.d8 0x5a))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[739, 4]
    (.letOp (n := 742) (.out 0x104954 (movzxR32M16Effect 0x104954 6 10 (.sib 4 none 0 (.d8 0x5c))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 743) (.exec 0x104954 (LoadPre 0x104954 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5c)) s (0x104954 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x104954 6 10 (.sib 4 none 0 (.d8 0x5c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 744) (.out 0x10495a (movR32R32Effect 0x10495a 3 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 10] []) (.reg (.gpr 11))) #v[742]
    (.letOp (n := 745) (.exec 0x10495a (fun s => s.RIP = 0x10495a) (movR32R32Effect 0x10495a 3 11 10) (Reg.operands [.gpr 10] [])) #v[742]
    (.letOp (n := 746) (.out 0x10495d (shrR32Effect 0x10495d 4 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[744]
    (.letOp (n := 747) (.exec 0x10495d (fun s => s.RIP = 0x10495d) (shrR32Effect 0x10495d 4 11 2) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[744]
    (.letOp (n := 748) (.out 0x104961 (xorR32R32Effect 0x104961 3 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 10] []) (.reg (.gpr 11))) #v[746, 742]
    (.letOp (n := 749) (.exec 0x104961 (fun s => s.RIP = 0x104961) (xorR32R32Effect 0x104961 3 11 10) (Reg.operands [.gpr 11, .gpr 10] [])) #v[746, 742]
    (.letOp (n := 750) (.out 0x104964 (andR32Imm32Effect 0x104964 7 11 0x1320) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11] []) (.reg (.gpr 11))) #v[748]
    (.letOp (n := 751) (.exec 0x104964 (fun s => s.RIP = 0x104964) (andR32Imm32Effect 0x104964 7 11 0x1320) (Reg.operands [.gpr 11] [])) #v[748]
    (b_l10446f_18)))))))))))))))))))))))))))))))))))))))

def bytes_l10446f_17 : List UInt8 :=
  [0x45, 0x89, 0xD3, 0x41, 0xC1, 0xEB, 0x02, 0x45, 0x31, 0xD3, 0x41, 0x81, 0xE3, 0x20, 0x13, 0x00,
    0x00, 0x45, 0x31, 0xDA, 0x41, 0xC1, 0xE3, 0x02, 0x45, 0x31, 0xD3, 0x45, 0x89, 0xDA, 0x41, 0xD1,
    0xEA, 0x45, 0x31, 0xDA, 0x41, 0x81, 0xE2, 0x50, 0x50, 0x00, 0x00, 0x45, 0x31, 0xD3, 0x45, 0x01,
    0xD2, 0x45, 0x31, 0xDA, 0x66, 0x44, 0x89, 0x54, 0x24, 0x5A, 0x44, 0x0F, 0xB7, 0x54, 0x24, 0x5C,
    0x45, 0x89, 0xD3, 0x41, 0xC1, 0xEB, 0x02, 0x45, 0x31, 0xD3, 0x41, 0x81, 0xE3, 0x20, 0x13, 0x00,
    0x00] ++ bytes_l10446f_18

theorem code_l10446f_17 : ∀ x ∈ codeRange 0x10491a bytes_l10446f_17, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x491a 81 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10446f_18

def b_l10446f_16 : Block Op Label signature Reg.count 674 :=
  .letOp (n := 674) (.out 0x1048cb (xorR32R32Effect 0x1048cb 3 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9] []) (.reg (.gpr 10))) #v[664, 672]
    (.letOp (n := 675) (.exec 0x1048cb (fun s => s.RIP = 0x1048cb) (xorR32R32Effect 0x1048cb 3 10 9) (Reg.operands [.gpr 10, .gpr 9] [])) #v[664, 672]
    (.letOp (n := 676) (.out 0x1048ce (addR32R32Effect 0x1048ce 3 9 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 9] []) (.reg (.gpr 9))) #v[672, 672]
    (.letOp (n := 677) (.exec 0x1048ce (fun s => s.RIP = 0x1048ce) (addR32R32Effect 0x1048ce 3 9 9) (Reg.operands [.gpr 9, .gpr 9] [])) #v[672, 672]
    (.letOp (n := 678) (.out 0x1048d1 (xorR32R32Effect 0x1048d1 3 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[676, 674]
    (.letOp (n := 679) (.exec 0x1048d1 (fun s => s.RIP = 0x1048d1) (xorR32R32Effect 0x1048d1 3 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[676, 674]
    (.letOp (n := 680) (.exec 0x1048d4 (StorePre 0x1048d4 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x46)) s (0x1048d4 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x1048d4 6 9 (.sib 4 none 0 (.d8 0x46))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[678, 4]
    (.letOp (n := 681) (.out 0x1048da (movzxR32M16Effect 0x1048da 6 9 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 682) (.exec 0x1048da (LoadPre 0x1048da (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1048da + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x1048da 6 9 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 683) (.out 0x1048e0 (movR32R32Effect 0x1048e0 3 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 9] []) (.reg (.gpr 10))) #v[681]
    (.letOp (n := 684) (.exec 0x1048e0 (fun s => s.RIP = 0x1048e0) (movR32R32Effect 0x1048e0 3 10 9) (Reg.operands [.gpr 9] [])) #v[681]
    (.letOp (n := 685) (.out 0x1048e3 (shrR32Effect 0x1048e3 4 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[683]
    (.letOp (n := 686) (.exec 0x1048e3 (fun s => s.RIP = 0x1048e3) (shrR32Effect 0x1048e3 4 10 2) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[683]
    (.letOp (n := 687) (.out 0x1048e7 (xorR32R32Effect 0x1048e7 3 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9] []) (.reg (.gpr 10))) #v[685, 681]
    (.letOp (n := 688) (.exec 0x1048e7 (fun s => s.RIP = 0x1048e7) (xorR32R32Effect 0x1048e7 3 10 9) (Reg.operands [.gpr 10, .gpr 9] [])) #v[685, 681]
    (.letOp (n := 689) (.out 0x1048ea (andR32Imm32Effect 0x1048ea 7 10 0x1320) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[687]
    (.letOp (n := 690) (.exec 0x1048ea (fun s => s.RIP = 0x1048ea) (andR32Imm32Effect 0x1048ea 7 10 0x1320) (Reg.operands [.gpr 10] [])) #v[687]
    (.letOp (n := 691) (.out 0x1048f1 (xorR32R32Effect 0x1048f1 3 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[681, 689]
    (.letOp (n := 692) (.exec 0x1048f1 (fun s => s.RIP = 0x1048f1) (xorR32R32Effect 0x1048f1 3 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[681, 689]
    (.letOp (n := 693) (.out 0x1048f4 (shlR32Effect 0x1048f4 4 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[689]
    (.letOp (n := 694) (.exec 0x1048f4 (fun s => s.RIP = 0x1048f4) (shlR32Effect 0x1048f4 4 10 2) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[689]
    (.letOp (n := 695) (.out 0x1048f8 (xorR32R32Effect 0x1048f8 3 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9] []) (.reg (.gpr 10))) #v[693, 691]
    (.letOp (n := 696) (.exec 0x1048f8 (fun s => s.RIP = 0x1048f8) (xorR32R32Effect 0x1048f8 3 10 9) (Reg.operands [.gpr 10, .gpr 9] [])) #v[693, 691]
    (.letOp (n := 697) (.out 0x1048fb (movR32R32Effect 0x1048fb 3 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 10] []) (.reg (.gpr 9))) #v[695]
    (.letOp (n := 698) (.exec 0x1048fb (fun s => s.RIP = 0x1048fb) (movR32R32Effect 0x1048fb 3 9 10) (Reg.operands [.gpr 10] [])) #v[695]
    (.letOp (n := 699) (.out 0x1048fe (shrR32Effect 0x1048fe 3 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[697]
    (.letOp (n := 700) (.exec 0x1048fe (fun s => s.RIP = 0x1048fe) (shrR32Effect 0x1048fe 3 9 1) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[697]
    (.letOp (n := 701) (.out 0x104901 (xorR32R32Effect 0x104901 3 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[699, 695]
    (.letOp (n := 702) (.exec 0x104901 (fun s => s.RIP = 0x104901) (xorR32R32Effect 0x104901 3 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[699, 695]
    (.letOp (n := 703) (.out 0x104904 (andR32Imm32Effect 0x104904 7 9 0x5050) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[701]
    (.letOp (n := 704) (.exec 0x104904 (fun s => s.RIP = 0x104904) (andR32Imm32Effect 0x104904 7 9 0x5050) (Reg.operands [.gpr 9] [])) #v[701]
    (.letOp (n := 705) (.out 0x10490b (xorR32R32Effect 0x10490b 3 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9] []) (.reg (.gpr 10))) #v[695, 703]
    (.letOp (n := 706) (.exec 0x10490b (fun s => s.RIP = 0x10490b) (xorR32R32Effect 0x10490b 3 10 9) (Reg.operands [.gpr 10, .gpr 9] [])) #v[695, 703]
    (.letOp (n := 707) (.out 0x10490e (addR32R32Effect 0x10490e 3 9 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 9] []) (.reg (.gpr 9))) #v[703, 703]
    (.letOp (n := 708) (.exec 0x10490e (fun s => s.RIP = 0x10490e) (addR32R32Effect 0x10490e 3 9 9) (Reg.operands [.gpr 9, .gpr 9] [])) #v[703, 703]
    (.letOp (n := 709) (.out 0x104911 (xorR32R32Effect 0x104911 3 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[707, 705]
    (.letOp (n := 710) (.exec 0x104911 (fun s => s.RIP = 0x104911) (xorR32R32Effect 0x104911 3 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[707, 705]
    (.letOp (n := 711) (.out 0x104914 (movzxR32M16Effect 0x104914 6 10 (.sib 4 none 0 (.d8 0x5a))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 712) (.exec 0x104914 (LoadPre 0x104914 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5a)) s (0x104914 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x104914 6 10 (.sib 4 none 0 (.d8 0x5a))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l10446f_17)))))))))))))))))))))))))))))))))))))))

def bytes_l10446f_16 : List UInt8 :=
  [0x45, 0x31, 0xCA, 0x45, 0x01, 0xC9, 0x45, 0x31, 0xD1, 0x66, 0x44, 0x89, 0x4C, 0x24, 0x46, 0x44,
    0x0F, 0xB7, 0x4C, 0x24, 0x58, 0x45, 0x89, 0xCA, 0x41, 0xC1, 0xEA, 0x02, 0x45, 0x31, 0xCA, 0x41,
    0x81, 0xE2, 0x20, 0x13, 0x00, 0x00, 0x45, 0x31, 0xD1, 0x41, 0xC1, 0xE2, 0x02, 0x45, 0x31, 0xCA,
    0x45, 0x89, 0xD1, 0x41, 0xD1, 0xE9, 0x45, 0x31, 0xD1, 0x41, 0x81, 0xE1, 0x50, 0x50, 0x00, 0x00,
    0x45, 0x31, 0xCA, 0x45, 0x01, 0xC9, 0x45, 0x31, 0xD1, 0x44, 0x0F, 0xB7, 0x54, 0x24, 0x5A] ++ bytes_l10446f_17

theorem code_l10446f_16 : ∀ x ∈ codeRange 0x1048cb bytes_l10446f_16, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x48cb 79 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10446f_17

def b_l10446f_15 : Block Op Label signature Reg.count 635 :=
  .letOp (n := 635) (.out 0x10487b (movR32R32Effect 0x10487b 3 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 10] []) (.reg (.gpr 9))) #v[633]
    (.letOp (n := 636) (.exec 0x10487b (fun s => s.RIP = 0x10487b) (movR32R32Effect 0x10487b 3 9 10) (Reg.operands [.gpr 10] [])) #v[633]
    (.letOp (n := 637) (.out 0x10487e (shrR32Effect 0x10487e 3 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[635]
    (.letOp (n := 638) (.exec 0x10487e (fun s => s.RIP = 0x10487e) (shrR32Effect 0x10487e 3 9 1) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[635]
    (.letOp (n := 639) (.out 0x104881 (xorR32R32Effect 0x104881 3 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[637, 633]
    (.letOp (n := 640) (.exec 0x104881 (fun s => s.RIP = 0x104881) (xorR32R32Effect 0x104881 3 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[637, 633]
    (.letOp (n := 641) (.out 0x104884 (andR32Imm32Effect 0x104884 7 9 0x5050) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[639]
    (.letOp (n := 642) (.exec 0x104884 (fun s => s.RIP = 0x104884) (andR32Imm32Effect 0x104884 7 9 0x5050) (Reg.operands [.gpr 9] [])) #v[639]
    (.letOp (n := 643) (.out 0x10488b (xorR32R32Effect 0x10488b 3 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9] []) (.reg (.gpr 10))) #v[633, 641]
    (.letOp (n := 644) (.exec 0x10488b (fun s => s.RIP = 0x10488b) (xorR32R32Effect 0x10488b 3 10 9) (Reg.operands [.gpr 10, .gpr 9] [])) #v[633, 641]
    (.letOp (n := 645) (.out 0x10488e (addR32R32Effect 0x10488e 3 9 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 9] []) (.reg (.gpr 9))) #v[641, 641]
    (.letOp (n := 646) (.exec 0x10488e (fun s => s.RIP = 0x10488e) (addR32R32Effect 0x10488e 3 9 9) (Reg.operands [.gpr 9, .gpr 9] [])) #v[641, 641]
    (.letOp (n := 647) (.out 0x104891 (xorR32R32Effect 0x104891 3 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[645, 643]
    (.letOp (n := 648) (.exec 0x104891 (fun s => s.RIP = 0x104891) (xorR32R32Effect 0x104891 3 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[645, 643]
    (.letOp (n := 649) (.exec 0x104894 (StorePre 0x104894 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x104894 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x104894 6 9 (.sib 4 none 0 (.d8 0x44))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[647, 4]
    (.letOp (n := 650) (.out 0x10489a (movzxR32M16Effect 0x10489a 6 9 (.sib 4 none 0 (.d8 0x46))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 651) (.exec 0x10489a (LoadPre 0x10489a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x46)) s (0x10489a + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x10489a 6 9 (.sib 4 none 0 (.d8 0x46))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 652) (.out 0x1048a0 (movR32R32Effect 0x1048a0 3 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 9] []) (.reg (.gpr 10))) #v[650]
    (.letOp (n := 653) (.exec 0x1048a0 (fun s => s.RIP = 0x1048a0) (movR32R32Effect 0x1048a0 3 10 9) (Reg.operands [.gpr 9] [])) #v[650]
    (.letOp (n := 654) (.out 0x1048a3 (shrR32Effect 0x1048a3 4 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[652]
    (.letOp (n := 655) (.exec 0x1048a3 (fun s => s.RIP = 0x1048a3) (shrR32Effect 0x1048a3 4 10 2) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[652]
    (.letOp (n := 656) (.out 0x1048a7 (xorR32R32Effect 0x1048a7 3 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9] []) (.reg (.gpr 10))) #v[654, 650]
    (.letOp (n := 657) (.exec 0x1048a7 (fun s => s.RIP = 0x1048a7) (xorR32R32Effect 0x1048a7 3 10 9) (Reg.operands [.gpr 10, .gpr 9] [])) #v[654, 650]
    (.letOp (n := 658) (.out 0x1048aa (andR32Imm32Effect 0x1048aa 7 10 0x2310) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[656]
    (.letOp (n := 659) (.exec 0x1048aa (fun s => s.RIP = 0x1048aa) (andR32Imm32Effect 0x1048aa 7 10 0x2310) (Reg.operands [.gpr 10] [])) #v[656]
    (.letOp (n := 660) (.out 0x1048b1 (xorR32R32Effect 0x1048b1 3 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[650, 658]
    (.letOp (n := 661) (.exec 0x1048b1 (fun s => s.RIP = 0x1048b1) (xorR32R32Effect 0x1048b1 3 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[650, 658]
    (.letOp (n := 662) (.out 0x1048b4 (shlR32Effect 0x1048b4 4 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[658]
    (.letOp (n := 663) (.exec 0x1048b4 (fun s => s.RIP = 0x1048b4) (shlR32Effect 0x1048b4 4 10 2) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[658]
    (.letOp (n := 664) (.out 0x1048b8 (xorR32R32Effect 0x1048b8 3 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9] []) (.reg (.gpr 10))) #v[662, 660]
    (.letOp (n := 665) (.exec 0x1048b8 (fun s => s.RIP = 0x1048b8) (xorR32R32Effect 0x1048b8 3 10 9) (Reg.operands [.gpr 10, .gpr 9] [])) #v[662, 660]
    (.letOp (n := 666) (.out 0x1048bb (movR32R32Effect 0x1048bb 3 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 10] []) (.reg (.gpr 9))) #v[664]
    (.letOp (n := 667) (.exec 0x1048bb (fun s => s.RIP = 0x1048bb) (movR32R32Effect 0x1048bb 3 9 10) (Reg.operands [.gpr 10] [])) #v[664]
    (.letOp (n := 668) (.out 0x1048be (shrR32Effect 0x1048be 3 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[666]
    (.letOp (n := 669) (.exec 0x1048be (fun s => s.RIP = 0x1048be) (shrR32Effect 0x1048be 3 9 1) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[666]
    (.letOp (n := 670) (.out 0x1048c1 (xorR32R32Effect 0x1048c1 3 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[668, 664]
    (.letOp (n := 671) (.exec 0x1048c1 (fun s => s.RIP = 0x1048c1) (xorR32R32Effect 0x1048c1 3 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[668, 664]
    (.letOp (n := 672) (.out 0x1048c4 (andR32Imm32Effect 0x1048c4 7 9 0x5050) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[670]
    (.letOp (n := 673) (.exec 0x1048c4 (fun s => s.RIP = 0x1048c4) (andR32Imm32Effect 0x1048c4 7 9 0x5050) (Reg.operands [.gpr 9] [])) #v[670]
    (b_l10446f_16)))))))))))))))))))))))))))))))))))))))

def bytes_l10446f_15 : List UInt8 :=
  [0x45, 0x89, 0xD1, 0x41, 0xD1, 0xE9, 0x45, 0x31, 0xD1, 0x41, 0x81, 0xE1, 0x50, 0x50, 0x00, 0x00,
    0x45, 0x31, 0xCA, 0x45, 0x01, 0xC9, 0x45, 0x31, 0xD1, 0x66, 0x44, 0x89, 0x4C, 0x24, 0x44, 0x44,
    0x0F, 0xB7, 0x4C, 0x24, 0x46, 0x45, 0x89, 0xCA, 0x41, 0xC1, 0xEA, 0x02, 0x45, 0x31, 0xCA, 0x41,
    0x81, 0xE2, 0x10, 0x23, 0x00, 0x00, 0x45, 0x31, 0xD1, 0x41, 0xC1, 0xE2, 0x02, 0x45, 0x31, 0xCA,
    0x45, 0x89, 0xD1, 0x41, 0xD1, 0xE9, 0x45, 0x31, 0xD1, 0x41, 0x81, 0xE1, 0x50, 0x50, 0x00, 0x00] ++ bytes_l10446f_16

theorem code_l10446f_15 : ∀ x ∈ codeRange 0x10487b bytes_l10446f_15, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x487b 80 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10446f_16

def b_l10446f_14 : Block Op Label signature Reg.count 596 :=
  .letOp (n := 596) (.out 0x10482a (andR32Imm32Effect 0x10482a 7 10 0x2310) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[594]
    (.letOp (n := 597) (.exec 0x10482a (fun s => s.RIP = 0x10482a) (andR32Imm32Effect 0x10482a 7 10 0x2310) (Reg.operands [.gpr 10] [])) #v[594]
    (.letOp (n := 598) (.out 0x104831 (xorR32R32Effect 0x104831 3 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[588, 596]
    (.letOp (n := 599) (.exec 0x104831 (fun s => s.RIP = 0x104831) (xorR32R32Effect 0x104831 3 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[588, 596]
    (.letOp (n := 600) (.out 0x104834 (shlR32Effect 0x104834 4 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[596]
    (.letOp (n := 601) (.exec 0x104834 (fun s => s.RIP = 0x104834) (shlR32Effect 0x104834 4 10 2) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[596]
    (.letOp (n := 602) (.out 0x104838 (xorR32R32Effect 0x104838 3 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9] []) (.reg (.gpr 10))) #v[600, 598]
    (.letOp (n := 603) (.exec 0x104838 (fun s => s.RIP = 0x104838) (xorR32R32Effect 0x104838 3 10 9) (Reg.operands [.gpr 10, .gpr 9] [])) #v[600, 598]
    (.letOp (n := 604) (.out 0x10483b (movR32R32Effect 0x10483b 3 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 10] []) (.reg (.gpr 9))) #v[602]
    (.letOp (n := 605) (.exec 0x10483b (fun s => s.RIP = 0x10483b) (movR32R32Effect 0x10483b 3 9 10) (Reg.operands [.gpr 10] [])) #v[602]
    (.letOp (n := 606) (.out 0x10483e (shrR32Effect 0x10483e 3 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[604]
    (.letOp (n := 607) (.exec 0x10483e (fun s => s.RIP = 0x10483e) (shrR32Effect 0x10483e 3 9 1) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[604]
    (.letOp (n := 608) (.out 0x104841 (xorR32R32Effect 0x104841 3 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[606, 602]
    (.letOp (n := 609) (.exec 0x104841 (fun s => s.RIP = 0x104841) (xorR32R32Effect 0x104841 3 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[606, 602]
    (.letOp (n := 610) (.out 0x104844 (andR32Imm32Effect 0x104844 7 9 0x5050) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[608]
    (.letOp (n := 611) (.exec 0x104844 (fun s => s.RIP = 0x104844) (andR32Imm32Effect 0x104844 7 9 0x5050) (Reg.operands [.gpr 9] [])) #v[608]
    (.letOp (n := 612) (.out 0x10484b (xorR32R32Effect 0x10484b 3 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9] []) (.reg (.gpr 10))) #v[602, 610]
    (.letOp (n := 613) (.exec 0x10484b (fun s => s.RIP = 0x10484b) (xorR32R32Effect 0x10484b 3 10 9) (Reg.operands [.gpr 10, .gpr 9] [])) #v[602, 610]
    (.letOp (n := 614) (.out 0x10484e (addR32R32Effect 0x10484e 3 9 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 9] []) (.reg (.gpr 9))) #v[610, 610]
    (.letOp (n := 615) (.exec 0x10484e (fun s => s.RIP = 0x10484e) (addR32R32Effect 0x10484e 3 9 9) (Reg.operands [.gpr 9, .gpr 9] [])) #v[610, 610]
    (.letOp (n := 616) (.out 0x104851 (xorR32R32Effect 0x104851 3 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[614, 612]
    (.letOp (n := 617) (.exec 0x104851 (fun s => s.RIP = 0x104851) (xorR32R32Effect 0x104851 3 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[614, 612]
    (.letOp (n := 618) (.exec 0x104854 (StorePre 0x104854 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x42)) s (0x104854 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x104854 6 9 (.sib 4 none 0 (.d8 0x42))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[616, 4]
    (.letOp (n := 619) (.out 0x10485a (movzxR32M16Effect 0x10485a 6 9 (.sib 4 none 0 (.d8 0x44))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 620) (.exec 0x10485a (LoadPre 0x10485a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x10485a + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x10485a 6 9 (.sib 4 none 0 (.d8 0x44))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 621) (.out 0x104860 (movR32R32Effect 0x104860 3 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 9] []) (.reg (.gpr 10))) #v[619]
    (.letOp (n := 622) (.exec 0x104860 (fun s => s.RIP = 0x104860) (movR32R32Effect 0x104860 3 10 9) (Reg.operands [.gpr 9] [])) #v[619]
    (.letOp (n := 623) (.out 0x104863 (shrR32Effect 0x104863 4 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[621]
    (.letOp (n := 624) (.exec 0x104863 (fun s => s.RIP = 0x104863) (shrR32Effect 0x104863 4 10 2) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[621]
    (.letOp (n := 625) (.out 0x104867 (xorR32R32Effect 0x104867 3 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9] []) (.reg (.gpr 10))) #v[623, 619]
    (.letOp (n := 626) (.exec 0x104867 (fun s => s.RIP = 0x104867) (xorR32R32Effect 0x104867 3 10 9) (Reg.operands [.gpr 10, .gpr 9] [])) #v[623, 619]
    (.letOp (n := 627) (.out 0x10486a (andR32Imm32Effect 0x10486a 7 10 0x2310) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[625]
    (.letOp (n := 628) (.exec 0x10486a (fun s => s.RIP = 0x10486a) (andR32Imm32Effect 0x10486a 7 10 0x2310) (Reg.operands [.gpr 10] [])) #v[625]
    (.letOp (n := 629) (.out 0x104871 (xorR32R32Effect 0x104871 3 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[619, 627]
    (.letOp (n := 630) (.exec 0x104871 (fun s => s.RIP = 0x104871) (xorR32R32Effect 0x104871 3 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[619, 627]
    (.letOp (n := 631) (.out 0x104874 (shlR32Effect 0x104874 4 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[627]
    (.letOp (n := 632) (.exec 0x104874 (fun s => s.RIP = 0x104874) (shlR32Effect 0x104874 4 10 2) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[627]
    (.letOp (n := 633) (.out 0x104878 (xorR32R32Effect 0x104878 3 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9] []) (.reg (.gpr 10))) #v[631, 629]
    (.letOp (n := 634) (.exec 0x104878 (fun s => s.RIP = 0x104878) (xorR32R32Effect 0x104878 3 10 9) (Reg.operands [.gpr 10, .gpr 9] [])) #v[631, 629]
    (b_l10446f_15)))))))))))))))))))))))))))))))))))))))

def bytes_l10446f_14 : List UInt8 :=
  [0x41, 0x81, 0xE2, 0x10, 0x23, 0x00, 0x00, 0x45, 0x31, 0xD1, 0x41, 0xC1, 0xE2, 0x02, 0x45, 0x31,
    0xCA, 0x45, 0x89, 0xD1, 0x41, 0xD1, 0xE9, 0x45, 0x31, 0xD1, 0x41, 0x81, 0xE1, 0x50, 0x50, 0x00,
    0x00, 0x45, 0x31, 0xCA, 0x45, 0x01, 0xC9, 0x45, 0x31, 0xD1, 0x66, 0x44, 0x89, 0x4C, 0x24, 0x42,
    0x44, 0x0F, 0xB7, 0x4C, 0x24, 0x44, 0x45, 0x89, 0xCA, 0x41, 0xC1, 0xEA, 0x02, 0x45, 0x31, 0xCA,
    0x41, 0x81, 0xE2, 0x10, 0x23, 0x00, 0x00, 0x45, 0x31, 0xD1, 0x41, 0xC1, 0xE2, 0x02, 0x45, 0x31,
    0xCA] ++ bytes_l10446f_15

theorem code_l10446f_14 : ∀ x ∈ codeRange 0x10482a bytes_l10446f_14, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x482a 81 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10446f_15

def b_l10446f_13 : Block Op Label signature Reg.count 557 :=
  .letOp (n := 557) (.out 0x1047da (movzxR32M16Effect 0x1047da 6 9 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 558) (.exec 0x1047da (LoadPre 0x1047da (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1047da + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x1047da 6 9 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 559) (.out 0x1047e0 (movR32R32Effect 0x1047e0 3 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 9] []) (.reg (.gpr 10))) #v[557]
    (.letOp (n := 560) (.exec 0x1047e0 (fun s => s.RIP = 0x1047e0) (movR32R32Effect 0x1047e0 3 10 9) (Reg.operands [.gpr 9] [])) #v[557]
    (.letOp (n := 561) (.out 0x1047e3 (shrR32Effect 0x1047e3 4 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[559]
    (.letOp (n := 562) (.exec 0x1047e3 (fun s => s.RIP = 0x1047e3) (shrR32Effect 0x1047e3 4 10 2) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[559]
    (.letOp (n := 563) (.out 0x1047e7 (xorR32R32Effect 0x1047e7 3 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9] []) (.reg (.gpr 10))) #v[561, 557]
    (.letOp (n := 564) (.exec 0x1047e7 (fun s => s.RIP = 0x1047e7) (xorR32R32Effect 0x1047e7 3 10 9) (Reg.operands [.gpr 10, .gpr 9] [])) #v[561, 557]
    (.letOp (n := 565) (.out 0x1047ea (andR32Imm32Effect 0x1047ea 7 10 0x2310) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[563]
    (.letOp (n := 566) (.exec 0x1047ea (fun s => s.RIP = 0x1047ea) (andR32Imm32Effect 0x1047ea 7 10 0x2310) (Reg.operands [.gpr 10] [])) #v[563]
    (.letOp (n := 567) (.out 0x1047f1 (xorR32R32Effect 0x1047f1 3 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[557, 565]
    (.letOp (n := 568) (.exec 0x1047f1 (fun s => s.RIP = 0x1047f1) (xorR32R32Effect 0x1047f1 3 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[557, 565]
    (.letOp (n := 569) (.out 0x1047f4 (shlR32Effect 0x1047f4 4 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[565]
    (.letOp (n := 570) (.exec 0x1047f4 (fun s => s.RIP = 0x1047f4) (shlR32Effect 0x1047f4 4 10 2) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[565]
    (.letOp (n := 571) (.out 0x1047f8 (xorR32R32Effect 0x1047f8 3 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9] []) (.reg (.gpr 10))) #v[569, 567]
    (.letOp (n := 572) (.exec 0x1047f8 (fun s => s.RIP = 0x1047f8) (xorR32R32Effect 0x1047f8 3 10 9) (Reg.operands [.gpr 10, .gpr 9] [])) #v[569, 567]
    (.letOp (n := 573) (.out 0x1047fb (movR32R32Effect 0x1047fb 3 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 10] []) (.reg (.gpr 9))) #v[571]
    (.letOp (n := 574) (.exec 0x1047fb (fun s => s.RIP = 0x1047fb) (movR32R32Effect 0x1047fb 3 9 10) (Reg.operands [.gpr 10] [])) #v[571]
    (.letOp (n := 575) (.out 0x1047fe (shrR32Effect 0x1047fe 3 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[573]
    (.letOp (n := 576) (.exec 0x1047fe (fun s => s.RIP = 0x1047fe) (shrR32Effect 0x1047fe 3 9 1) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[573]
    (.letOp (n := 577) (.out 0x104801 (xorR32R32Effect 0x104801 3 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[575, 571]
    (.letOp (n := 578) (.exec 0x104801 (fun s => s.RIP = 0x104801) (xorR32R32Effect 0x104801 3 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[575, 571]
    (.letOp (n := 579) (.out 0x104804 (andR32Imm32Effect 0x104804 7 9 0x5050) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[577]
    (.letOp (n := 580) (.exec 0x104804 (fun s => s.RIP = 0x104804) (andR32Imm32Effect 0x104804 7 9 0x5050) (Reg.operands [.gpr 9] [])) #v[577]
    (.letOp (n := 581) (.out 0x10480b (xorR32R32Effect 0x10480b 3 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9] []) (.reg (.gpr 10))) #v[571, 579]
    (.letOp (n := 582) (.exec 0x10480b (fun s => s.RIP = 0x10480b) (xorR32R32Effect 0x10480b 3 10 9) (Reg.operands [.gpr 10, .gpr 9] [])) #v[571, 579]
    (.letOp (n := 583) (.out 0x10480e (addR32R32Effect 0x10480e 3 9 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 9] []) (.reg (.gpr 9))) #v[579, 579]
    (.letOp (n := 584) (.exec 0x10480e (fun s => s.RIP = 0x10480e) (addR32R32Effect 0x10480e 3 9 9) (Reg.operands [.gpr 9, .gpr 9] [])) #v[579, 579]
    (.letOp (n := 585) (.out 0x104811 (xorR32R32Effect 0x104811 3 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[583, 581]
    (.letOp (n := 586) (.exec 0x104811 (fun s => s.RIP = 0x104811) (xorR32R32Effect 0x104811 3 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[583, 581]
    (.letOp (n := 587) (.exec 0x104814 (StorePre 0x104814 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x104814 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x104814 6 9 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[585, 4]
    (.letOp (n := 588) (.out 0x10481a (movzxR32M16Effect 0x10481a 6 9 (.sib 4 none 0 (.d8 0x42))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 589) (.exec 0x10481a (LoadPre 0x10481a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x42)) s (0x10481a + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x10481a 6 9 (.sib 4 none 0 (.d8 0x42))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 590) (.out 0x104820 (movR32R32Effect 0x104820 3 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 9] []) (.reg (.gpr 10))) #v[588]
    (.letOp (n := 591) (.exec 0x104820 (fun s => s.RIP = 0x104820) (movR32R32Effect 0x104820 3 10 9) (Reg.operands [.gpr 9] [])) #v[588]
    (.letOp (n := 592) (.out 0x104823 (shrR32Effect 0x104823 4 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[590]
    (.letOp (n := 593) (.exec 0x104823 (fun s => s.RIP = 0x104823) (shrR32Effect 0x104823 4 10 2) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[590]
    (.letOp (n := 594) (.out 0x104827 (xorR32R32Effect 0x104827 3 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9] []) (.reg (.gpr 10))) #v[592, 588]
    (.letOp (n := 595) (.exec 0x104827 (fun s => s.RIP = 0x104827) (xorR32R32Effect 0x104827 3 10 9) (Reg.operands [.gpr 10, .gpr 9] [])) #v[592, 588]
    (b_l10446f_14)))))))))))))))))))))))))))))))))))))))

def bytes_l10446f_13 : List UInt8 :=
  [0x44, 0x0F, 0xB7, 0x4C, 0x24, 0x40, 0x45, 0x89, 0xCA, 0x41, 0xC1, 0xEA, 0x02, 0x45, 0x31, 0xCA,
    0x41, 0x81, 0xE2, 0x10, 0x23, 0x00, 0x00, 0x45, 0x31, 0xD1, 0x41, 0xC1, 0xE2, 0x02, 0x45, 0x31,
    0xCA, 0x45, 0x89, 0xD1, 0x41, 0xD1, 0xE9, 0x45, 0x31, 0xD1, 0x41, 0x81, 0xE1, 0x50, 0x50, 0x00,
    0x00, 0x45, 0x31, 0xCA, 0x45, 0x01, 0xC9, 0x45, 0x31, 0xD1, 0x66, 0x44, 0x89, 0x4C, 0x24, 0x40,
    0x44, 0x0F, 0xB7, 0x4C, 0x24, 0x42, 0x45, 0x89, 0xCA, 0x41, 0xC1, 0xEA, 0x02, 0x45, 0x31, 0xCA] ++ bytes_l10446f_14

theorem code_l10446f_13 : ∀ x ∈ codeRange 0x1047da bytes_l10446f_13, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x47da 80 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10446f_14

def b_l10446f_12 : Block Op Label signature Reg.count 519 :=
  .letOp (n := 519) (.out 0x10478b (xorR32R32Effect 0x10478b 3 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9] []) (.reg (.gpr 10))) #v[509, 517]
    (.letOp (n := 520) (.exec 0x10478b (fun s => s.RIP = 0x10478b) (xorR32R32Effect 0x10478b 3 10 9) (Reg.operands [.gpr 10, .gpr 9] [])) #v[509, 517]
    (.letOp (n := 521) (.out 0x10478e (addR32R32Effect 0x10478e 3 9 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 9] []) (.reg (.gpr 9))) #v[517, 517]
    (.letOp (n := 522) (.exec 0x10478e (fun s => s.RIP = 0x10478e) (addR32R32Effect 0x10478e 3 9 9) (Reg.operands [.gpr 9, .gpr 9] [])) #v[517, 517]
    (.letOp (n := 523) (.out 0x104791 (xorR32R32Effect 0x104791 3 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[521, 519]
    (.letOp (n := 524) (.exec 0x104791 (fun s => s.RIP = 0x104791) (xorR32R32Effect 0x104791 3 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[521, 519]
    (.letOp (n := 525) (.exec 0x104794 (StorePre 0x104794 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x104794 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x104794 6 9 (.sib 4 none 0 (.d8 0x3c))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[523, 4]
    (.letOp (n := 526) (.out 0x10479a (movzxR32M16Effect 0x10479a 6 9 (.sib 4 none 0 (.d8 0x3e))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 527) (.exec 0x10479a (LoadPre 0x10479a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3e)) s (0x10479a + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x10479a 6 9 (.sib 4 none 0 (.d8 0x3e))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 528) (.out 0x1047a0 (movR32R32Effect 0x1047a0 3 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 9] []) (.reg (.gpr 10))) #v[526]
    (.letOp (n := 529) (.exec 0x1047a0 (fun s => s.RIP = 0x1047a0) (movR32R32Effect 0x1047a0 3 10 9) (Reg.operands [.gpr 9] [])) #v[526]
    (.letOp (n := 530) (.out 0x1047a3 (shrR32Effect 0x1047a3 4 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[528]
    (.letOp (n := 531) (.exec 0x1047a3 (fun s => s.RIP = 0x1047a3) (shrR32Effect 0x1047a3 4 10 2) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[528]
    (.letOp (n := 532) (.out 0x1047a7 (xorR32R32Effect 0x1047a7 3 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9] []) (.reg (.gpr 10))) #v[530, 526]
    (.letOp (n := 533) (.exec 0x1047a7 (fun s => s.RIP = 0x1047a7) (xorR32R32Effect 0x1047a7 3 10 9) (Reg.operands [.gpr 10, .gpr 9] [])) #v[530, 526]
    (.letOp (n := 534) (.out 0x1047aa (andR32Imm32Effect 0x1047aa 7 10 0x2310) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[532]
    (.letOp (n := 535) (.exec 0x1047aa (fun s => s.RIP = 0x1047aa) (andR32Imm32Effect 0x1047aa 7 10 0x2310) (Reg.operands [.gpr 10] [])) #v[532]
    (.letOp (n := 536) (.out 0x1047b1 (xorR32R32Effect 0x1047b1 3 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[526, 534]
    (.letOp (n := 537) (.exec 0x1047b1 (fun s => s.RIP = 0x1047b1) (xorR32R32Effect 0x1047b1 3 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[526, 534]
    (.letOp (n := 538) (.out 0x1047b4 (shlR32Effect 0x1047b4 4 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[534]
    (.letOp (n := 539) (.exec 0x1047b4 (fun s => s.RIP = 0x1047b4) (shlR32Effect 0x1047b4 4 10 2) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[534]
    (.letOp (n := 540) (.out 0x1047b8 (xorR32R32Effect 0x1047b8 3 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9] []) (.reg (.gpr 10))) #v[538, 536]
    (.letOp (n := 541) (.exec 0x1047b8 (fun s => s.RIP = 0x1047b8) (xorR32R32Effect 0x1047b8 3 10 9) (Reg.operands [.gpr 10, .gpr 9] [])) #v[538, 536]
    (.letOp (n := 542) (.out 0x1047bb (movR32R32Effect 0x1047bb 3 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 10] []) (.reg (.gpr 9))) #v[540]
    (.letOp (n := 543) (.exec 0x1047bb (fun s => s.RIP = 0x1047bb) (movR32R32Effect 0x1047bb 3 9 10) (Reg.operands [.gpr 10] [])) #v[540]
    (.letOp (n := 544) (.out 0x1047be (shrR32Effect 0x1047be 3 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[542]
    (.letOp (n := 545) (.exec 0x1047be (fun s => s.RIP = 0x1047be) (shrR32Effect 0x1047be 3 9 1) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[542]
    (.letOp (n := 546) (.out 0x1047c1 (xorR32R32Effect 0x1047c1 3 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[544, 540]
    (.letOp (n := 547) (.exec 0x1047c1 (fun s => s.RIP = 0x1047c1) (xorR32R32Effect 0x1047c1 3 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[544, 540]
    (.letOp (n := 548) (.out 0x1047c4 (andR32Imm32Effect 0x1047c4 7 9 0x5050) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[546]
    (.letOp (n := 549) (.exec 0x1047c4 (fun s => s.RIP = 0x1047c4) (andR32Imm32Effect 0x1047c4 7 9 0x5050) (Reg.operands [.gpr 9] [])) #v[546]
    (.letOp (n := 550) (.out 0x1047cb (xorR32R32Effect 0x1047cb 3 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9] []) (.reg (.gpr 10))) #v[540, 548]
    (.letOp (n := 551) (.exec 0x1047cb (fun s => s.RIP = 0x1047cb) (xorR32R32Effect 0x1047cb 3 10 9) (Reg.operands [.gpr 10, .gpr 9] [])) #v[540, 548]
    (.letOp (n := 552) (.out 0x1047ce (addR32R32Effect 0x1047ce 3 9 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 9] []) (.reg (.gpr 9))) #v[548, 548]
    (.letOp (n := 553) (.exec 0x1047ce (fun s => s.RIP = 0x1047ce) (addR32R32Effect 0x1047ce 3 9 9) (Reg.operands [.gpr 9, .gpr 9] [])) #v[548, 548]
    (.letOp (n := 554) (.out 0x1047d1 (xorR32R32Effect 0x1047d1 3 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[552, 550]
    (.letOp (n := 555) (.exec 0x1047d1 (fun s => s.RIP = 0x1047d1) (xorR32R32Effect 0x1047d1 3 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[552, 550]
    (.letOp (n := 556) (.exec 0x1047d4 (StorePre 0x1047d4 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3e)) s (0x1047d4 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x1047d4 6 9 (.sib 4 none 0 (.d8 0x3e))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[554, 4]
    (b_l10446f_13))))))))))))))))))))))))))))))))))))))

def bytes_l10446f_12 : List UInt8 :=
  [0x45, 0x31, 0xCA, 0x45, 0x01, 0xC9, 0x45, 0x31, 0xD1, 0x66, 0x44, 0x89, 0x4C, 0x24, 0x3C, 0x44,
    0x0F, 0xB7, 0x4C, 0x24, 0x3E, 0x45, 0x89, 0xCA, 0x41, 0xC1, 0xEA, 0x02, 0x45, 0x31, 0xCA, 0x41,
    0x81, 0xE2, 0x10, 0x23, 0x00, 0x00, 0x45, 0x31, 0xD1, 0x41, 0xC1, 0xE2, 0x02, 0x45, 0x31, 0xCA,
    0x45, 0x89, 0xD1, 0x41, 0xD1, 0xE9, 0x45, 0x31, 0xD1, 0x41, 0x81, 0xE1, 0x50, 0x50, 0x00, 0x00,
    0x45, 0x31, 0xCA, 0x45, 0x01, 0xC9, 0x45, 0x31, 0xD1, 0x66, 0x44, 0x89, 0x4C, 0x24, 0x3E] ++ bytes_l10446f_13

theorem code_l10446f_12 : ∀ x ∈ codeRange 0x10478b bytes_l10446f_12, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x478b 79 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10446f_13

def b_l10446f_11 : Block Op Label signature Reg.count 480 :=
  .letOp (n := 480) (.out 0x10473b (movR32R32Effect 0x10473b 3 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 10] []) (.reg (.gpr 9))) #v[478]
    (.letOp (n := 481) (.exec 0x10473b (fun s => s.RIP = 0x10473b) (movR32R32Effect 0x10473b 3 9 10) (Reg.operands [.gpr 10] [])) #v[478]
    (.letOp (n := 482) (.out 0x10473e (shrR32Effect 0x10473e 3 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[480]
    (.letOp (n := 483) (.exec 0x10473e (fun s => s.RIP = 0x10473e) (shrR32Effect 0x10473e 3 9 1) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[480]
    (.letOp (n := 484) (.out 0x104741 (xorR32R32Effect 0x104741 3 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[482, 478]
    (.letOp (n := 485) (.exec 0x104741 (fun s => s.RIP = 0x104741) (xorR32R32Effect 0x104741 3 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[482, 478]
    (.letOp (n := 486) (.out 0x104744 (andR32Imm32Effect 0x104744 7 9 0x5050) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[484]
    (.letOp (n := 487) (.exec 0x104744 (fun s => s.RIP = 0x104744) (andR32Imm32Effect 0x104744 7 9 0x5050) (Reg.operands [.gpr 9] [])) #v[484]
    (.letOp (n := 488) (.out 0x10474b (xorR32R32Effect 0x10474b 3 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9] []) (.reg (.gpr 10))) #v[478, 486]
    (.letOp (n := 489) (.exec 0x10474b (fun s => s.RIP = 0x10474b) (xorR32R32Effect 0x10474b 3 10 9) (Reg.operands [.gpr 10, .gpr 9] [])) #v[478, 486]
    (.letOp (n := 490) (.out 0x10474e (addR32R32Effect 0x10474e 3 9 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 9] []) (.reg (.gpr 9))) #v[486, 486]
    (.letOp (n := 491) (.exec 0x10474e (fun s => s.RIP = 0x10474e) (addR32R32Effect 0x10474e 3 9 9) (Reg.operands [.gpr 9, .gpr 9] [])) #v[486, 486]
    (.letOp (n := 492) (.out 0x104751 (xorR32R32Effect 0x104751 3 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[490, 488]
    (.letOp (n := 493) (.exec 0x104751 (fun s => s.RIP = 0x104751) (xorR32R32Effect 0x104751 3 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[490, 488]
    (.letOp (n := 494) (.exec 0x104754 (StorePre 0x104754 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3a)) s (0x104754 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x104754 6 9 (.sib 4 none 0 (.d8 0x3a))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[492, 4]
    (.letOp (n := 495) (.out 0x10475a (movzxR32M16Effect 0x10475a 6 9 (.sib 4 none 0 (.d8 0x3c))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 496) (.exec 0x10475a (LoadPre 0x10475a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x10475a + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x10475a 6 9 (.sib 4 none 0 (.d8 0x3c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 497) (.out 0x104760 (movR32R32Effect 0x104760 3 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 9] []) (.reg (.gpr 10))) #v[495]
    (.letOp (n := 498) (.exec 0x104760 (fun s => s.RIP = 0x104760) (movR32R32Effect 0x104760 3 10 9) (Reg.operands [.gpr 9] [])) #v[495]
    (.letOp (n := 499) (.out 0x104763 (shrR32Effect 0x104763 4 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[497]
    (.letOp (n := 500) (.exec 0x104763 (fun s => s.RIP = 0x104763) (shrR32Effect 0x104763 4 10 2) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[497]
    (.letOp (n := 501) (.out 0x104767 (xorR32R32Effect 0x104767 3 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9] []) (.reg (.gpr 10))) #v[499, 495]
    (.letOp (n := 502) (.exec 0x104767 (fun s => s.RIP = 0x104767) (xorR32R32Effect 0x104767 3 10 9) (Reg.operands [.gpr 10, .gpr 9] [])) #v[499, 495]
    (.letOp (n := 503) (.out 0x10476a (andR32Imm32Effect 0x10476a 7 10 0x2310) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[501]
    (.letOp (n := 504) (.exec 0x10476a (fun s => s.RIP = 0x10476a) (andR32Imm32Effect 0x10476a 7 10 0x2310) (Reg.operands [.gpr 10] [])) #v[501]
    (.letOp (n := 505) (.out 0x104771 (xorR32R32Effect 0x104771 3 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[495, 503]
    (.letOp (n := 506) (.exec 0x104771 (fun s => s.RIP = 0x104771) (xorR32R32Effect 0x104771 3 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[495, 503]
    (.letOp (n := 507) (.out 0x104774 (shlR32Effect 0x104774 4 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[503]
    (.letOp (n := 508) (.exec 0x104774 (fun s => s.RIP = 0x104774) (shlR32Effect 0x104774 4 10 2) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[503]
    (.letOp (n := 509) (.out 0x104778 (xorR32R32Effect 0x104778 3 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9] []) (.reg (.gpr 10))) #v[507, 505]
    (.letOp (n := 510) (.exec 0x104778 (fun s => s.RIP = 0x104778) (xorR32R32Effect 0x104778 3 10 9) (Reg.operands [.gpr 10, .gpr 9] [])) #v[507, 505]
    (.letOp (n := 511) (.out 0x10477b (movR32R32Effect 0x10477b 3 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 10] []) (.reg (.gpr 9))) #v[509]
    (.letOp (n := 512) (.exec 0x10477b (fun s => s.RIP = 0x10477b) (movR32R32Effect 0x10477b 3 9 10) (Reg.operands [.gpr 10] [])) #v[509]
    (.letOp (n := 513) (.out 0x10477e (shrR32Effect 0x10477e 3 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[511]
    (.letOp (n := 514) (.exec 0x10477e (fun s => s.RIP = 0x10477e) (shrR32Effect 0x10477e 3 9 1) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[511]
    (.letOp (n := 515) (.out 0x104781 (xorR32R32Effect 0x104781 3 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[513, 509]
    (.letOp (n := 516) (.exec 0x104781 (fun s => s.RIP = 0x104781) (xorR32R32Effect 0x104781 3 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[513, 509]
    (.letOp (n := 517) (.out 0x104784 (andR32Imm32Effect 0x104784 7 9 0x5050) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[515]
    (.letOp (n := 518) (.exec 0x104784 (fun s => s.RIP = 0x104784) (andR32Imm32Effect 0x104784 7 9 0x5050) (Reg.operands [.gpr 9] [])) #v[515]
    (b_l10446f_12)))))))))))))))))))))))))))))))))))))))

def bytes_l10446f_11 : List UInt8 :=
  [0x45, 0x89, 0xD1, 0x41, 0xD1, 0xE9, 0x45, 0x31, 0xD1, 0x41, 0x81, 0xE1, 0x50, 0x50, 0x00, 0x00,
    0x45, 0x31, 0xCA, 0x45, 0x01, 0xC9, 0x45, 0x31, 0xD1, 0x66, 0x44, 0x89, 0x4C, 0x24, 0x3A, 0x44,
    0x0F, 0xB7, 0x4C, 0x24, 0x3C, 0x45, 0x89, 0xCA, 0x41, 0xC1, 0xEA, 0x02, 0x45, 0x31, 0xCA, 0x41,
    0x81, 0xE2, 0x10, 0x23, 0x00, 0x00, 0x45, 0x31, 0xD1, 0x41, 0xC1, 0xE2, 0x02, 0x45, 0x31, 0xCA,
    0x45, 0x89, 0xD1, 0x41, 0xD1, 0xE9, 0x45, 0x31, 0xD1, 0x41, 0x81, 0xE1, 0x50, 0x50, 0x00, 0x00] ++ bytes_l10446f_12

theorem code_l10446f_11 : ∀ x ∈ codeRange 0x10473b bytes_l10446f_11, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x473b 80 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10446f_12

def b_l10446f_10 : Block Op Label signature Reg.count 440 :=
  .letOp (n := 440) (.out 0x1046ed (xorR32R32Effect 0x1046ed 3 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8] []) (.reg (.gpr 9))) #v[438, 434]
    (.letOp (n := 441) (.exec 0x1046ed (fun s => s.RIP = 0x1046ed) (xorR32R32Effect 0x1046ed 3 9 8) (Reg.operands [.gpr 9, .gpr 8] [])) #v[438, 434]
    (.letOp (n := 442) (.out 0x1046f0 (andR32Imm32Effect 0x1046f0 7 9 0x2310) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[440]
    (.letOp (n := 443) (.exec 0x1046f0 (fun s => s.RIP = 0x1046f0) (andR32Imm32Effect 0x1046f0 7 9 0x2310) (Reg.operands [.gpr 9] [])) #v[440]
    (.letOp (n := 444) (.out 0x1046f7 (xorR32R32Effect 0x1046f7 3 8 9) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 9] []) (.reg (.gpr 8))) #v[434, 442]
    (.letOp (n := 445) (.exec 0x1046f7 (fun s => s.RIP = 0x1046f7) (xorR32R32Effect 0x1046f7 3 8 9) (Reg.operands [.gpr 8, .gpr 9] [])) #v[434, 442]
    (.letOp (n := 446) (.out 0x1046fa (shlR32Effect 0x1046fa 4 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[442]
    (.letOp (n := 447) (.exec 0x1046fa (fun s => s.RIP = 0x1046fa) (shlR32Effect 0x1046fa 4 9 2) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[442]
    (.letOp (n := 448) (.out 0x1046fe (xorR32R32Effect 0x1046fe 3 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8] []) (.reg (.gpr 9))) #v[446, 444]
    (.letOp (n := 449) (.exec 0x1046fe (fun s => s.RIP = 0x1046fe) (xorR32R32Effect 0x1046fe 3 9 8) (Reg.operands [.gpr 9, .gpr 8] [])) #v[446, 444]
    (.letOp (n := 450) (.out 0x104701 (movR32R32Effect 0x104701 3 8 9) (EffectPart.reads (.reg (.gpr 8)) [.gpr 9] []) (.reg (.gpr 8))) #v[448]
    (.letOp (n := 451) (.exec 0x104701 (fun s => s.RIP = 0x104701) (movR32R32Effect 0x104701 3 8 9) (Reg.operands [.gpr 9] [])) #v[448]
    (.letOp (n := 452) (.out 0x104704 (shrR32Effect 0x104704 3 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[450]
    (.letOp (n := 453) (.exec 0x104704 (fun s => s.RIP = 0x104704) (shrR32Effect 0x104704 3 8 1) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[450]
    (.letOp (n := 454) (.out 0x104707 (xorR32R32Effect 0x104707 3 8 9) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 9] []) (.reg (.gpr 8))) #v[452, 448]
    (.letOp (n := 455) (.exec 0x104707 (fun s => s.RIP = 0x104707) (xorR32R32Effect 0x104707 3 8 9) (Reg.operands [.gpr 8, .gpr 9] [])) #v[452, 448]
    (.letOp (n := 456) (.out 0x10470a (andR32Imm32Effect 0x10470a 7 8 0x5050) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[454]
    (.letOp (n := 457) (.exec 0x10470a (fun s => s.RIP = 0x10470a) (andR32Imm32Effect 0x10470a 7 8 0x5050) (Reg.operands [.gpr 8] [])) #v[454]
    (.letOp (n := 458) (.out 0x104711 (xorR32R32Effect 0x104711 3 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8] []) (.reg (.gpr 9))) #v[448, 456]
    (.letOp (n := 459) (.exec 0x104711 (fun s => s.RIP = 0x104711) (xorR32R32Effect 0x104711 3 9 8) (Reg.operands [.gpr 9, .gpr 8] [])) #v[448, 456]
    (.letOp (n := 460) (.out 0x104714 (addR32R32Effect 0x104714 3 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 8] []) (.reg (.gpr 8))) #v[456, 456]
    (.letOp (n := 461) (.exec 0x104714 (fun s => s.RIP = 0x104714) (addR32R32Effect 0x104714 3 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[456, 456]
    (.letOp (n := 462) (.out 0x104717 (xorR32R32Effect 0x104717 3 8 9) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 9] []) (.reg (.gpr 8))) #v[460, 458]
    (.letOp (n := 463) (.exec 0x104717 (fun s => s.RIP = 0x104717) (xorR32R32Effect 0x104717 3 8 9) (Reg.operands [.gpr 8, .gpr 9] [])) #v[460, 458]
    (.letOp (n := 464) (.out 0x10471a (movzxR32M16Effect 0x10471a 6 9 (.sib 4 none 0 (.d8 0x3a))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 465) (.exec 0x10471a (LoadPre 0x10471a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3a)) s (0x10471a + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x10471a 6 9 (.sib 4 none 0 (.d8 0x3a))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 466) (.out 0x104720 (movR32R32Effect 0x104720 3 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 9] []) (.reg (.gpr 10))) #v[464]
    (.letOp (n := 467) (.exec 0x104720 (fun s => s.RIP = 0x104720) (movR32R32Effect 0x104720 3 10 9) (Reg.operands [.gpr 9] [])) #v[464]
    (.letOp (n := 468) (.out 0x104723 (shrR32Effect 0x104723 4 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[466]
    (.letOp (n := 469) (.exec 0x104723 (fun s => s.RIP = 0x104723) (shrR32Effect 0x104723 4 10 2) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[466]
    (.letOp (n := 470) (.out 0x104727 (xorR32R32Effect 0x104727 3 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9] []) (.reg (.gpr 10))) #v[468, 464]
    (.letOp (n := 471) (.exec 0x104727 (fun s => s.RIP = 0x104727) (xorR32R32Effect 0x104727 3 10 9) (Reg.operands [.gpr 10, .gpr 9] [])) #v[468, 464]
    (.letOp (n := 472) (.out 0x10472a (andR32Imm32Effect 0x10472a 7 10 0x2310) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[470]
    (.letOp (n := 473) (.exec 0x10472a (fun s => s.RIP = 0x10472a) (andR32Imm32Effect 0x10472a 7 10 0x2310) (Reg.operands [.gpr 10] [])) #v[470]
    (.letOp (n := 474) (.out 0x104731 (xorR32R32Effect 0x104731 3 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[464, 472]
    (.letOp (n := 475) (.exec 0x104731 (fun s => s.RIP = 0x104731) (xorR32R32Effect 0x104731 3 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[464, 472]
    (.letOp (n := 476) (.out 0x104734 (shlR32Effect 0x104734 4 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[472]
    (.letOp (n := 477) (.exec 0x104734 (fun s => s.RIP = 0x104734) (shlR32Effect 0x104734 4 10 2) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[472]
    (.letOp (n := 478) (.out 0x104738 (xorR32R32Effect 0x104738 3 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9] []) (.reg (.gpr 10))) #v[476, 474]
    (.letOp (n := 479) (.exec 0x104738 (fun s => s.RIP = 0x104738) (xorR32R32Effect 0x104738 3 10 9) (Reg.operands [.gpr 10, .gpr 9] [])) #v[476, 474]
    (b_l10446f_11))))))))))))))))))))))))))))))))))))))))

def bytes_l10446f_10 : List UInt8 :=
  [0x45, 0x31, 0xC1, 0x41, 0x81, 0xE1, 0x10, 0x23, 0x00, 0x00, 0x45, 0x31, 0xC8, 0x41, 0xC1, 0xE1,
    0x02, 0x45, 0x31, 0xC1, 0x45, 0x89, 0xC8, 0x41, 0xD1, 0xE8, 0x45, 0x31, 0xC8, 0x41, 0x81, 0xE0,
    0x50, 0x50, 0x00, 0x00, 0x45, 0x31, 0xC1, 0x45, 0x01, 0xC0, 0x45, 0x31, 0xC8, 0x44, 0x0F, 0xB7,
    0x4C, 0x24, 0x3A, 0x45, 0x89, 0xCA, 0x41, 0xC1, 0xEA, 0x02, 0x45, 0x31, 0xCA, 0x41, 0x81, 0xE2,
    0x10, 0x23, 0x00, 0x00, 0x45, 0x31, 0xD1, 0x41, 0xC1, 0xE2, 0x02, 0x45, 0x31, 0xCA] ++ bytes_l10446f_11

theorem code_l10446f_10 : ∀ x ∈ codeRange 0x1046ed bytes_l10446f_10, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x46ed 78 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10446f_11

def b_l10446f_9 : Block Op Label signature Reg.count 401 :=
  .letOp (n := 401) (.out 0x10469b (movzxR32M16Effect 0x10469b 6 8 (.sib 4 none 0 (.d8 0x34))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 402) (.exec 0x10469b (LoadPre 0x10469b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x10469b + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x10469b 6 8 (.sib 4 none 0 (.d8 0x34))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 403) (.out 0x1046a1 (movR32R32Effect 0x1046a1 3 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 8] []) (.reg (.gpr 7))) #v[401]
    (.letOp (n := 404) (.exec 0x1046a1 (fun s => s.RIP = 0x1046a1) (movR32R32Effect 0x1046a1 3 7 8) (Reg.operands [.gpr 8] [])) #v[401]
    (.letOp (n := 405) (.out 0x1046a4 (shrR32Effect 0x1046a4 3 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[403]
    (.letOp (n := 406) (.exec 0x1046a4 (fun s => s.RIP = 0x1046a4) (shrR32Effect 0x1046a4 3 7 2) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[403]
    (.letOp (n := 407) (.out 0x1046a7 (xorR32R32Effect 0x1046a7 3 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 8] []) (.reg (.gpr 7))) #v[405, 401]
    (.letOp (n := 408) (.exec 0x1046a7 (fun s => s.RIP = 0x1046a7) (xorR32R32Effect 0x1046a7 3 7 8) (Reg.operands [.gpr 7, .gpr 8] [])) #v[405, 401]
    (.letOp (n := 409) (.out 0x1046aa (andR32Imm32Effect 0x1046aa 6 7 0x3030) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[407]
    (.letOp (n := 410) (.exec 0x1046aa (fun s => s.RIP = 0x1046aa) (andR32Imm32Effect 0x1046aa 6 7 0x3030) (Reg.operands [.gpr 7] [])) #v[407]
    (.letOp (n := 411) (.out 0x1046b0 (xorR32R32Effect 0x1046b0 3 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 7] []) (.reg (.gpr 8))) #v[401, 409]
    (.letOp (n := 412) (.exec 0x1046b0 (fun s => s.RIP = 0x1046b0) (xorR32R32Effect 0x1046b0 3 8 7) (Reg.operands [.gpr 8, .gpr 7] [])) #v[401, 409]
    (.letOp (n := 413) (.out 0x1046b3 (shlR32Effect 0x1046b3 3 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[409]
    (.letOp (n := 414) (.exec 0x1046b3 (fun s => s.RIP = 0x1046b3) (shlR32Effect 0x1046b3 3 7 2) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[409]
    (.letOp (n := 415) (.out 0x1046b6 (xorR32R32Effect 0x1046b6 3 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 8] []) (.reg (.gpr 7))) #v[413, 411]
    (.letOp (n := 416) (.exec 0x1046b6 (fun s => s.RIP = 0x1046b6) (xorR32R32Effect 0x1046b6 3 7 8) (Reg.operands [.gpr 7, .gpr 8] [])) #v[413, 411]
    (.letOp (n := 417) (.out 0x1046b9 (movzxR32M16Effect 0x1046b9 6 8 (.sib 4 none 0 (.d8 0x36))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 418) (.exec 0x1046b9 (LoadPre 0x1046b9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x36)) s (0x1046b9 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x1046b9 6 8 (.sib 4 none 0 (.d8 0x36))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 419) (.out 0x1046bf (movR32R32Effect 0x1046bf 3 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 8] []) (.reg (.gpr 9))) #v[417]
    (.letOp (n := 420) (.exec 0x1046bf (fun s => s.RIP = 0x1046bf) (movR32R32Effect 0x1046bf 3 9 8) (Reg.operands [.gpr 8] [])) #v[417]
    (.letOp (n := 421) (.out 0x1046c2 (shrR32Effect 0x1046c2 4 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[419]
    (.letOp (n := 422) (.exec 0x1046c2 (fun s => s.RIP = 0x1046c2) (shrR32Effect 0x1046c2 4 9 2) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[419]
    (.letOp (n := 423) (.out 0x1046c6 (xorR32R32Effect 0x1046c6 3 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8] []) (.reg (.gpr 9))) #v[421, 417]
    (.letOp (n := 424) (.exec 0x1046c6 (fun s => s.RIP = 0x1046c6) (xorR32R32Effect 0x1046c6 3 9 8) (Reg.operands [.gpr 9, .gpr 8] [])) #v[421, 417]
    (.letOp (n := 425) (.out 0x1046c9 (andR32Imm32Effect 0x1046c9 7 9 0x3030) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[423]
    (.letOp (n := 426) (.exec 0x1046c9 (fun s => s.RIP = 0x1046c9) (andR32Imm32Effect 0x1046c9 7 9 0x3030) (Reg.operands [.gpr 9] [])) #v[423]
    (.letOp (n := 427) (.out 0x1046d0 (xorR32R32Effect 0x1046d0 3 8 9) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 9] []) (.reg (.gpr 8))) #v[417, 425]
    (.letOp (n := 428) (.exec 0x1046d0 (fun s => s.RIP = 0x1046d0) (xorR32R32Effect 0x1046d0 3 8 9) (Reg.operands [.gpr 8, .gpr 9] [])) #v[417, 425]
    (.letOp (n := 429) (.out 0x1046d3 (shlR32Effect 0x1046d3 4 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[425]
    (.letOp (n := 430) (.exec 0x1046d3 (fun s => s.RIP = 0x1046d3) (shlR32Effect 0x1046d3 4 9 2) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[425]
    (.letOp (n := 431) (.out 0x1046d7 (xorR32R32Effect 0x1046d7 3 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8] []) (.reg (.gpr 9))) #v[429, 427]
    (.letOp (n := 432) (.exec 0x1046d7 (fun s => s.RIP = 0x1046d7) (xorR32R32Effect 0x1046d7 3 9 8) (Reg.operands [.gpr 9, .gpr 8] [])) #v[429, 427]
    (.letOp (n := 433) (.exec 0x1046da (StorePre 0x1046da 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x36)) s (0x1046da + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x1046da 6 9 (.sib 4 none 0 (.d8 0x36))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[431, 4]
    (.letOp (n := 434) (.out 0x1046e0 (movzxR32M16Effect 0x1046e0 6 8 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 435) (.exec 0x1046e0 (LoadPre 0x1046e0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1046e0 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x1046e0 6 8 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 436) (.out 0x1046e6 (movR32R32Effect 0x1046e6 3 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 8] []) (.reg (.gpr 9))) #v[434]
    (.letOp (n := 437) (.exec 0x1046e6 (fun s => s.RIP = 0x1046e6) (movR32R32Effect 0x1046e6 3 9 8) (Reg.operands [.gpr 8] [])) #v[434]
    (.letOp (n := 438) (.out 0x1046e9 (shrR32Effect 0x1046e9 4 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[436]
    (.letOp (n := 439) (.exec 0x1046e9 (fun s => s.RIP = 0x1046e9) (shrR32Effect 0x1046e9 4 9 2) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[436]
    (b_l10446f_10)))))))))))))))))))))))))))))))))))))))

def bytes_l10446f_9 : List UInt8 :=
  [0x44, 0x0F, 0xB7, 0x44, 0x24, 0x34, 0x44, 0x89, 0xC7, 0xC1, 0xEF, 0x02, 0x44, 0x31, 0xC7, 0x81,
    0xE7, 0x30, 0x30, 0x00, 0x00, 0x41, 0x31, 0xF8, 0xC1, 0xE7, 0x02, 0x44, 0x31, 0xC7, 0x44, 0x0F,
    0xB7, 0x44, 0x24, 0x36, 0x45, 0x89, 0xC1, 0x41, 0xC1, 0xE9, 0x02, 0x45, 0x31, 0xC1, 0x41, 0x81,
    0xE1, 0x30, 0x30, 0x00, 0x00, 0x45, 0x31, 0xC8, 0x41, 0xC1, 0xE1, 0x02, 0x45, 0x31, 0xC1, 0x66,
    0x44, 0x89, 0x4C, 0x24, 0x36, 0x44, 0x0F, 0xB7, 0x44, 0x24, 0x38, 0x45, 0x89, 0xC1, 0x41, 0xC1,
    0xE9, 0x02] ++ bytes_l10446f_10

theorem code_l10446f_9 : ∀ x ∈ codeRange 0x10469b bytes_l10446f_9, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x469b 82 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10446f_10

def b_l10446f_8 : Block Op Label signature Reg.count 363 :=
  .letOp (n := 363) (.out 0x10465a (shlR32Effect 0x10465a 3 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[359]
    (.letOp (n := 364) (.exec 0x10465a (fun s => s.RIP = 0x10465a) (shlR32Effect 0x10465a 3 7 2) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[359]
    (.letOp (n := 365) (.out 0x10465d (xorR32R32Effect 0x10465d 2 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[363, 361]
    (.letOp (n := 366) (.exec 0x10465d (fun s => s.RIP = 0x10465d) (xorR32R32Effect 0x10465d 2 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[363, 361]
    (.letOp (n := 367) (.exec 0x10465f (StorePre 0x10465f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2e)) s (0x10465f + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x10465f 5 7 (.sib 4 none 0 (.d8 0x2e))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[365, 4]
    (.letOp (n := 368) (.out 0x104664 (movzxR32M16Effect 0x104664 5 6 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 369) (.exec 0x104664 (LoadPre 0x104664 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x104664 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x104664 5 6 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 370) (.out 0x104669 (movR32R32Effect 0x104669 2 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[368]
    (.letOp (n := 371) (.exec 0x104669 (fun s => s.RIP = 0x104669) (movR32R32Effect 0x104669 2 7 6) (Reg.operands [.gpr 6] [])) #v[368]
    (.letOp (n := 372) (.out 0x10466b (shrR32Effect 0x10466b 3 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[370]
    (.letOp (n := 373) (.exec 0x10466b (fun s => s.RIP = 0x10466b) (shrR32Effect 0x10466b 3 7 2) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[370]
    (.letOp (n := 374) (.out 0x10466e (xorR32R32Effect 0x10466e 2 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[372, 368]
    (.letOp (n := 375) (.exec 0x10466e (fun s => s.RIP = 0x10466e) (xorR32R32Effect 0x10466e 2 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[372, 368]
    (.letOp (n := 376) (.out 0x104670 (andR32Imm32Effect 0x104670 6 7 0x3030) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[374]
    (.letOp (n := 377) (.exec 0x104670 (fun s => s.RIP = 0x104670) (andR32Imm32Effect 0x104670 6 7 0x3030) (Reg.operands [.gpr 7] [])) #v[374]
    (.letOp (n := 378) (.out 0x104676 (xorR32R32Effect 0x104676 2 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7] []) (.reg (.gpr 6))) #v[368, 376]
    (.letOp (n := 379) (.exec 0x104676 (fun s => s.RIP = 0x104676) (xorR32R32Effect 0x104676 2 6 7) (Reg.operands [.gpr 6, .gpr 7] [])) #v[368, 376]
    (.letOp (n := 380) (.out 0x104678 (shlR32Effect 0x104678 3 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[376]
    (.letOp (n := 381) (.exec 0x104678 (fun s => s.RIP = 0x104678) (shlR32Effect 0x104678 3 7 2) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[376]
    (.letOp (n := 382) (.out 0x10467b (xorR32R32Effect 0x10467b 2 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[380, 378]
    (.letOp (n := 383) (.exec 0x10467b (fun s => s.RIP = 0x10467b) (xorR32R32Effect 0x10467b 2 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[380, 378]
    (.letOp (n := 384) (.exec 0x10467d (StorePre 0x10467d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10467d + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x10467d 5 7 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[382, 4]
    (.letOp (n := 385) (.out 0x104682 (movzxR32M16Effect 0x104682 5 7 (.sib 4 none 0 (.d8 0x32))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 386) (.exec 0x104682 (LoadPre 0x104682 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x32)) s (0x104682 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x104682 5 7 (.sib 4 none 0 (.d8 0x32))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 387) (.out 0x104687 (movR32R32Effect 0x104687 2 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 7] []) (.reg (.gpr 6))) #v[385]
    (.letOp (n := 388) (.exec 0x104687 (fun s => s.RIP = 0x104687) (movR32R32Effect 0x104687 2 6 7) (Reg.operands [.gpr 7] [])) #v[385]
    (.letOp (n := 389) (.out 0x104689 (shrR32Effect 0x104689 3 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[387]
    (.letOp (n := 390) (.exec 0x104689 (fun s => s.RIP = 0x104689) (shrR32Effect 0x104689 3 6 2) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[387]
    (.letOp (n := 391) (.out 0x10468c (xorR32R32Effect 0x10468c 2 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7] []) (.reg (.gpr 6))) #v[389, 385]
    (.letOp (n := 392) (.exec 0x10468c (fun s => s.RIP = 0x10468c) (xorR32R32Effect 0x10468c 2 6 7) (Reg.operands [.gpr 6, .gpr 7] [])) #v[389, 385]
    (.letOp (n := 393) (.out 0x10468e (andR32Imm32Effect 0x10468e 6 6 0x3030) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[391]
    (.letOp (n := 394) (.exec 0x10468e (fun s => s.RIP = 0x10468e) (andR32Imm32Effect 0x10468e 6 6 0x3030) (Reg.operands [.gpr 6] [])) #v[391]
    (.letOp (n := 395) (.out 0x104694 (xorR32R32Effect 0x104694 2 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[385, 393]
    (.letOp (n := 396) (.exec 0x104694 (fun s => s.RIP = 0x104694) (xorR32R32Effect 0x104694 2 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[385, 393]
    (.letOp (n := 397) (.out 0x104696 (shlR32Effect 0x104696 3 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[393]
    (.letOp (n := 398) (.exec 0x104696 (fun s => s.RIP = 0x104696) (shlR32Effect 0x104696 3 6 2) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[393]
    (.letOp (n := 399) (.out 0x104699 (xorR32R32Effect 0x104699 2 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7] []) (.reg (.gpr 6))) #v[397, 395]
    (.letOp (n := 400) (.exec 0x104699 (fun s => s.RIP = 0x104699) (xorR32R32Effect 0x104699 2 6 7) (Reg.operands [.gpr 6, .gpr 7] [])) #v[397, 395]
    (b_l10446f_9))))))))))))))))))))))))))))))))))))))

def bytes_l10446f_8 : List UInt8 :=
  [0xC1, 0xE7, 0x02, 0x31, 0xF7, 0x66, 0x89, 0x7C, 0x24, 0x2E, 0x0F, 0xB7, 0x74, 0x24, 0x30, 0x89,
    0xF7, 0xC1, 0xEF, 0x02, 0x31, 0xF7, 0x81, 0xE7, 0x30, 0x30, 0x00, 0x00, 0x31, 0xFE, 0xC1, 0xE7,
    0x02, 0x31, 0xF7, 0x66, 0x89, 0x7C, 0x24, 0x30, 0x0F, 0xB7, 0x7C, 0x24, 0x32, 0x89, 0xFE, 0xC1,
    0xEE, 0x02, 0x31, 0xFE, 0x81, 0xE6, 0x30, 0x30, 0x00, 0x00, 0x31, 0xF7, 0xC1, 0xE6, 0x02, 0x31,
    0xFE] ++ bytes_l10446f_9

theorem code_l10446f_8 : ∀ x ∈ codeRange 0x10465a bytes_l10446f_8, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x465a 65 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10446f_9

def b_l10446f_7 : Block Op Label signature Reg.count 324 :=
  .letOp (n := 324) (.out 0x104619 (xorR32R32Effect 0x104619 2 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[322, 318]
    (.letOp (n := 325) (.exec 0x104619 (fun s => s.RIP = 0x104619) (xorR32R32Effect 0x104619 2 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[322, 318]
    (.letOp (n := 326) (.out 0x10461b (andR32Imm32Effect 0x10461b 6 1 0x3030) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[324]
    (.letOp (n := 327) (.exec 0x10461b (fun s => s.RIP = 0x10461b) (andR32Imm32Effect 0x10461b 6 1 0x3030) (Reg.operands [.gpr 1] [])) #v[324]
    (.letOp (n := 328) (.out 0x104621 (xorR32R32Effect 0x104621 2 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[318, 326]
    (.letOp (n := 329) (.exec 0x104621 (fun s => s.RIP = 0x104621) (xorR32R32Effect 0x104621 2 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[318, 326]
    (.letOp (n := 330) (.out 0x104623 (shlR32Effect 0x104623 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[326]
    (.letOp (n := 331) (.exec 0x104623 (fun s => s.RIP = 0x104623) (shlR32Effect 0x104623 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[326]
    (.letOp (n := 332) (.out 0x104626 (xorR32R32Effect 0x104626 2 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[330, 328]
    (.letOp (n := 333) (.exec 0x104626 (fun s => s.RIP = 0x104626) (xorR32R32Effect 0x104626 2 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[330, 328]
    (.letOp (n := 334) (.out 0x104628 (movzxR32M16Effect 0x104628 5 6 (.sib 4 none 0 (.d8 0x2c))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 335) (.exec 0x104628 (LoadPre 0x104628 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x104628 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x104628 5 6 (.sib 4 none 0 (.d8 0x2c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 336) (.out 0x10462d (movR32R32Effect 0x10462d 2 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[334]
    (.letOp (n := 337) (.exec 0x10462d (fun s => s.RIP = 0x10462d) (movR32R32Effect 0x10462d 2 7 6) (Reg.operands [.gpr 6] [])) #v[334]
    (.letOp (n := 338) (.out 0x10462f (shrR32Effect 0x10462f 3 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[336]
    (.letOp (n := 339) (.exec 0x10462f (fun s => s.RIP = 0x10462f) (shrR32Effect 0x10462f 3 7 2) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[336]
    (.letOp (n := 340) (.out 0x104632 (xorR32R32Effect 0x104632 2 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[338, 334]
    (.letOp (n := 341) (.exec 0x104632 (fun s => s.RIP = 0x104632) (xorR32R32Effect 0x104632 2 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[338, 334]
    (.letOp (n := 342) (.out 0x104634 (andR32Imm32Effect 0x104634 6 7 0x3030) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[340]
    (.letOp (n := 343) (.exec 0x104634 (fun s => s.RIP = 0x104634) (andR32Imm32Effect 0x104634 6 7 0x3030) (Reg.operands [.gpr 7] [])) #v[340]
    (.letOp (n := 344) (.out 0x10463a (xorR32R32Effect 0x10463a 2 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7] []) (.reg (.gpr 6))) #v[334, 342]
    (.letOp (n := 345) (.exec 0x10463a (fun s => s.RIP = 0x10463a) (xorR32R32Effect 0x10463a 2 6 7) (Reg.operands [.gpr 6, .gpr 7] [])) #v[334, 342]
    (.letOp (n := 346) (.out 0x10463c (shlR32Effect 0x10463c 3 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[342]
    (.letOp (n := 347) (.exec 0x10463c (fun s => s.RIP = 0x10463c) (shlR32Effect 0x10463c 3 7 2) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[342]
    (.letOp (n := 348) (.out 0x10463f (xorR32R32Effect 0x10463f 2 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[346, 344]
    (.letOp (n := 349) (.exec 0x10463f (fun s => s.RIP = 0x10463f) (xorR32R32Effect 0x10463f 2 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[346, 344]
    (.letOp (n := 350) (.exec 0x104641 (StorePre 0x104641 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x104641 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x104641 5 7 (.sib 4 none 0 (.d8 0x2c))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[348, 4]
    (.letOp (n := 351) (.out 0x104646 (movzxR32M16Effect 0x104646 5 6 (.sib 4 none 0 (.d8 0x2e))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 352) (.exec 0x104646 (LoadPre 0x104646 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2e)) s (0x104646 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x104646 5 6 (.sib 4 none 0 (.d8 0x2e))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 353) (.out 0x10464b (movR32R32Effect 0x10464b 2 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[351]
    (.letOp (n := 354) (.exec 0x10464b (fun s => s.RIP = 0x10464b) (movR32R32Effect 0x10464b 2 7 6) (Reg.operands [.gpr 6] [])) #v[351]
    (.letOp (n := 355) (.out 0x10464d (shrR32Effect 0x10464d 3 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[353]
    (.letOp (n := 356) (.exec 0x10464d (fun s => s.RIP = 0x10464d) (shrR32Effect 0x10464d 3 7 2) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[353]
    (.letOp (n := 357) (.out 0x104650 (xorR32R32Effect 0x104650 2 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[355, 351]
    (.letOp (n := 358) (.exec 0x104650 (fun s => s.RIP = 0x104650) (xorR32R32Effect 0x104650 2 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[355, 351]
    (.letOp (n := 359) (.out 0x104652 (andR32Imm32Effect 0x104652 6 7 0x3030) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[357]
    (.letOp (n := 360) (.exec 0x104652 (fun s => s.RIP = 0x104652) (andR32Imm32Effect 0x104652 6 7 0x3030) (Reg.operands [.gpr 7] [])) #v[357]
    (.letOp (n := 361) (.out 0x104658 (xorR32R32Effect 0x104658 2 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7] []) (.reg (.gpr 6))) #v[351, 359]
    (.letOp (n := 362) (.exec 0x104658 (fun s => s.RIP = 0x104658) (xorR32R32Effect 0x104658 2 6 7) (Reg.operands [.gpr 6, .gpr 7] [])) #v[351, 359]
    (b_l10446f_8)))))))))))))))))))))))))))))))))))))))

def bytes_l10446f_7 : List UInt8 :=
  [0x31, 0xF1, 0x81, 0xE1, 0x30, 0x30, 0x00, 0x00, 0x31, 0xCE, 0xC1, 0xE1, 0x02, 0x31, 0xF1, 0x0F,
    0xB7, 0x74, 0x24, 0x2C, 0x89, 0xF7, 0xC1, 0xEF, 0x02, 0x31, 0xF7, 0x81, 0xE7, 0x30, 0x30, 0x00,
    0x00, 0x31, 0xFE, 0xC1, 0xE7, 0x02, 0x31, 0xF7, 0x66, 0x89, 0x7C, 0x24, 0x2C, 0x0F, 0xB7, 0x74,
    0x24, 0x2E, 0x89, 0xF7, 0xC1, 0xEF, 0x02, 0x31, 0xF7, 0x81, 0xE7, 0x30, 0x30, 0x00, 0x00, 0x31,
    0xFE] ++ bytes_l10446f_8

theorem code_l10446f_7 : ∀ x ∈ codeRange 0x104619 bytes_l10446f_7, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x4619 65 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10446f_8

def b_l10446f_6 : Block Op Label signature Reg.count 286 :=
  .letOp (n := 286) (.out 0x1045d9 (movR32R32Effect 0x1045d9 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[284]
    (.letOp (n := 287) (.exec 0x1045d9 (fun s => s.RIP = 0x1045d9) (movR32R32Effect 0x1045d9 2 1 2) (Reg.operands [.gpr 2] [])) #v[284]
    (.letOp (n := 288) (.out 0x1045db (shrR32Effect 0x1045db 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[286]
    (.letOp (n := 289) (.exec 0x1045db (fun s => s.RIP = 0x1045db) (shrR32Effect 0x1045db 2 1 1) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[286]
    (.letOp (n := 290) (.out 0x1045dd (xorR32R32Effect 0x1045dd 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[288, 284]
    (.letOp (n := 291) (.exec 0x1045dd (fun s => s.RIP = 0x1045dd) (xorR32R32Effect 0x1045dd 2 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[288, 284]
    (.letOp (n := 292) (.out 0x1045df (andR32Imm32Effect 0x1045df 6 1 0x5050) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[290]
    (.letOp (n := 293) (.exec 0x1045df (fun s => s.RIP = 0x1045df) (andR32Imm32Effect 0x1045df 6 1 0x5050) (Reg.operands [.gpr 1] [])) #v[290]
    (.letOp (n := 294) (.out 0x1045e5 (xorR32R32Effect 0x1045e5 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[284, 292]
    (.letOp (n := 295) (.exec 0x1045e5 (fun s => s.RIP = 0x1045e5) (xorR32R32Effect 0x1045e5 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[284, 292]
    (.letOp (n := 296) (.out 0x1045e7 (addR32R32Effect 0x1045e7 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[292, 292]
    (.letOp (n := 297) (.exec 0x1045e7 (fun s => s.RIP = 0x1045e7) (addR32R32Effect 0x1045e7 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[292, 292]
    (.letOp (n := 298) (.out 0x1045e9 (xorR32R32Effect 0x1045e9 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[296, 294]
    (.letOp (n := 299) (.exec 0x1045e9 (fun s => s.RIP = 0x1045e9) (xorR32R32Effect 0x1045e9 2 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[296, 294]
    (.letOp (n := 300) (.exec 0x1045eb (StorePre 0x1045eb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x26)) s (0x1045eb + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1045eb 5 1 (.sib 4 none 0 (.d8 0x26))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[298, 4]
    (.letOp (n := 301) (.out 0x1045f0 (movzxR32M16Effect 0x1045f0 5 2 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 302) (.exec 0x1045f0 (LoadPre 0x1045f0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1045f0 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x1045f0 5 2 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 303) (.out 0x1045f5 (movR32R32Effect 0x1045f5 2 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[301]
    (.letOp (n := 304) (.exec 0x1045f5 (fun s => s.RIP = 0x1045f5) (movR32R32Effect 0x1045f5 2 0 2) (Reg.operands [.gpr 2] [])) #v[301]
    (.letOp (n := 305) (.out 0x1045f7 (shrR32Effect 0x1045f7 3 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[303]
    (.letOp (n := 306) (.exec 0x1045f7 (fun s => s.RIP = 0x1045f7) (shrR32Effect 0x1045f7 3 0 2) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[303]
    (.letOp (n := 307) (.out 0x1045fa (xorR32R32Effect 0x1045fa 2 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[305, 301]
    (.letOp (n := 308) (.exec 0x1045fa (fun s => s.RIP = 0x1045fa) (xorR32R32Effect 0x1045fa 2 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[305, 301]
    (.letOp (n := 309) (.out 0x1045fc (andEaxImm32Effect 0x1045fc 0x3030) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[307]
    (.letOp (n := 310) (.exec 0x1045fc (fun s => s.RIP = 0x1045fc) (andEaxImm32Effect 0x1045fc 0x3030) (Reg.operands [.gpr 0] [])) #v[307]
    (.letOp (n := 311) (.out 0x104601 (xorR32R32Effect 0x104601 2 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[301, 309]
    (.letOp (n := 312) (.exec 0x104601 (fun s => s.RIP = 0x104601) (xorR32R32Effect 0x104601 2 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[301, 309]
    (.letOp (n := 313) (.out 0x104603 (shlR32Effect 0x104603 3 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[309]
    (.letOp (n := 314) (.exec 0x104603 (fun s => s.RIP = 0x104603) (shlR32Effect 0x104603 3 0 2) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[309]
    (.letOp (n := 315) (.out 0x104606 (xorR32R32Effect 0x104606 2 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[313, 311]
    (.letOp (n := 316) (.exec 0x104606 (fun s => s.RIP = 0x104606) (xorR32R32Effect 0x104606 2 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[313, 311]
    (.letOp (n := 317) (.exec 0x104608 (StorePre 0x104608 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x104608 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x104608 0 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[315, 4]
    (.letOp (n := 318) (.out 0x10460f (movzxR32M16Effect 0x10460f 5 6 (.sib 4 none 0 (.d8 0x2a))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 319) (.exec 0x10460f (LoadPre 0x10460f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2a)) s (0x10460f + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x10460f 5 6 (.sib 4 none 0 (.d8 0x2a))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 320) (.out 0x104614 (movR32R32Effect 0x104614 2 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[318]
    (.letOp (n := 321) (.exec 0x104614 (fun s => s.RIP = 0x104614) (movR32R32Effect 0x104614 2 1 6) (Reg.operands [.gpr 6] [])) #v[318]
    (.letOp (n := 322) (.out 0x104616 (shrR32Effect 0x104616 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[320]
    (.letOp (n := 323) (.exec 0x104616 (fun s => s.RIP = 0x104616) (shrR32Effect 0x104616 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[320]
    (b_l10446f_7))))))))))))))))))))))))))))))))))))))

def bytes_l10446f_6 : List UInt8 :=
  [0x89, 0xD1, 0xD1, 0xE9, 0x31, 0xD1, 0x81, 0xE1, 0x50, 0x50, 0x00, 0x00, 0x31, 0xCA, 0x01, 0xC9,
    0x31, 0xD1, 0x66, 0x89, 0x4C, 0x24, 0x26, 0x0F, 0xB7, 0x54, 0x24, 0x28, 0x89, 0xD0, 0xC1, 0xE8,
    0x02, 0x31, 0xD0, 0x25, 0x30, 0x30, 0x00, 0x00, 0x31, 0xC2, 0xC1, 0xE0, 0x02, 0x31, 0xD0, 0x89,
    0x84, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x0F, 0xB7, 0x74, 0x24, 0x2A, 0x89, 0xF1, 0xC1, 0xE9, 0x02] ++ bytes_l10446f_7

theorem code_l10446f_6 : ∀ x ∈ codeRange 0x1045d9 bytes_l10446f_6, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x45d9 64 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10446f_7

def b_l10446f_5 : Block Op Label signature Reg.count 247 :=
  .letOp (n := 247) (.out 0x10459c (andR32Imm32Effect 0x10459c 6 2 0x1320) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[245]
    (.letOp (n := 248) (.exec 0x10459c (fun s => s.RIP = 0x10459c) (andR32Imm32Effect 0x10459c 6 2 0x1320) (Reg.operands [.gpr 2] [])) #v[245]
    (.letOp (n := 249) (.out 0x1045a2 (xorR32R32Effect 0x1045a2 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[239, 247]
    (.letOp (n := 250) (.exec 0x1045a2 (fun s => s.RIP = 0x1045a2) (xorR32R32Effect 0x1045a2 2 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[239, 247]
    (.letOp (n := 251) (.out 0x1045a4 (shlR32Effect 0x1045a4 3 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[247]
    (.letOp (n := 252) (.exec 0x1045a4 (fun s => s.RIP = 0x1045a4) (shlR32Effect 0x1045a4 3 2 2) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[247]
    (.letOp (n := 253) (.out 0x1045a7 (xorR32R32Effect 0x1045a7 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[251, 249]
    (.letOp (n := 254) (.exec 0x1045a7 (fun s => s.RIP = 0x1045a7) (xorR32R32Effect 0x1045a7 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[251, 249]
    (.letOp (n := 255) (.out 0x1045a9 (movR32R32Effect 0x1045a9 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[253]
    (.letOp (n := 256) (.exec 0x1045a9 (fun s => s.RIP = 0x1045a9) (movR32R32Effect 0x1045a9 2 1 2) (Reg.operands [.gpr 2] [])) #v[253]
    (.letOp (n := 257) (.out 0x1045ab (shrR32Effect 0x1045ab 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[255]
    (.letOp (n := 258) (.exec 0x1045ab (fun s => s.RIP = 0x1045ab) (shrR32Effect 0x1045ab 2 1 1) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[255]
    (.letOp (n := 259) (.out 0x1045ad (xorR32R32Effect 0x1045ad 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[257, 253]
    (.letOp (n := 260) (.exec 0x1045ad (fun s => s.RIP = 0x1045ad) (xorR32R32Effect 0x1045ad 2 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[257, 253]
    (.letOp (n := 261) (.out 0x1045af (andR32Imm32Effect 0x1045af 6 1 0x5050) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[259]
    (.letOp (n := 262) (.exec 0x1045af (fun s => s.RIP = 0x1045af) (andR32Imm32Effect 0x1045af 6 1 0x5050) (Reg.operands [.gpr 1] [])) #v[259]
    (.letOp (n := 263) (.out 0x1045b5 (xorR32R32Effect 0x1045b5 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[253, 261]
    (.letOp (n := 264) (.exec 0x1045b5 (fun s => s.RIP = 0x1045b5) (xorR32R32Effect 0x1045b5 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[253, 261]
    (.letOp (n := 265) (.out 0x1045b7 (addR32R32Effect 0x1045b7 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[261, 261]
    (.letOp (n := 266) (.exec 0x1045b7 (fun s => s.RIP = 0x1045b7) (addR32R32Effect 0x1045b7 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[261, 261]
    (.letOp (n := 267) (.out 0x1045b9 (xorR32R32Effect 0x1045b9 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[265, 263]
    (.letOp (n := 268) (.exec 0x1045b9 (fun s => s.RIP = 0x1045b9) (xorR32R32Effect 0x1045b9 2 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[265, 263]
    (.letOp (n := 269) (.exec 0x1045bb (StorePre 0x1045bb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x1045bb + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1045bb 5 1 (.sib 4 none 0 (.d8 0x24))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[267, 4]
    (.letOp (n := 270) (.out 0x1045c0 (movzxR32M16Effect 0x1045c0 5 1 (.sib 4 none 0 (.d8 0x26))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 271) (.exec 0x1045c0 (LoadPre 0x1045c0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x26)) s (0x1045c0 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x1045c0 5 1 (.sib 4 none 0 (.d8 0x26))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 272) (.out 0x1045c5 (movR32R32Effect 0x1045c5 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[270]
    (.letOp (n := 273) (.exec 0x1045c5 (fun s => s.RIP = 0x1045c5) (movR32R32Effect 0x1045c5 2 2 1) (Reg.operands [.gpr 1] [])) #v[270]
    (.letOp (n := 274) (.out 0x1045c7 (shrR32Effect 0x1045c7 3 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[272]
    (.letOp (n := 275) (.exec 0x1045c7 (fun s => s.RIP = 0x1045c7) (shrR32Effect 0x1045c7 3 2 2) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[272]
    (.letOp (n := 276) (.out 0x1045ca (xorR32R32Effect 0x1045ca 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[274, 270]
    (.letOp (n := 277) (.exec 0x1045ca (fun s => s.RIP = 0x1045ca) (xorR32R32Effect 0x1045ca 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[274, 270]
    (.letOp (n := 278) (.out 0x1045cc (andR32Imm32Effect 0x1045cc 6 2 0x1320) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[276]
    (.letOp (n := 279) (.exec 0x1045cc (fun s => s.RIP = 0x1045cc) (andR32Imm32Effect 0x1045cc 6 2 0x1320) (Reg.operands [.gpr 2] [])) #v[276]
    (.letOp (n := 280) (.out 0x1045d2 (xorR32R32Effect 0x1045d2 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[270, 278]
    (.letOp (n := 281) (.exec 0x1045d2 (fun s => s.RIP = 0x1045d2) (xorR32R32Effect 0x1045d2 2 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[270, 278]
    (.letOp (n := 282) (.out 0x1045d4 (shlR32Effect 0x1045d4 3 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[278]
    (.letOp (n := 283) (.exec 0x1045d4 (fun s => s.RIP = 0x1045d4) (shlR32Effect 0x1045d4 3 2 2) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[278]
    (.letOp (n := 284) (.out 0x1045d7 (xorR32R32Effect 0x1045d7 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[282, 280]
    (.letOp (n := 285) (.exec 0x1045d7 (fun s => s.RIP = 0x1045d7) (xorR32R32Effect 0x1045d7 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[282, 280]
    (b_l10446f_6)))))))))))))))))))))))))))))))))))))))

def bytes_l10446f_5 : List UInt8 :=
  [0x81, 0xE2, 0x20, 0x13, 0x00, 0x00, 0x31, 0xD1, 0xC1, 0xE2, 0x02, 0x31, 0xCA, 0x89, 0xD1, 0xD1,
    0xE9, 0x31, 0xD1, 0x81, 0xE1, 0x50, 0x50, 0x00, 0x00, 0x31, 0xCA, 0x01, 0xC9, 0x31, 0xD1, 0x66,
    0x89, 0x4C, 0x24, 0x24, 0x0F, 0xB7, 0x4C, 0x24, 0x26, 0x89, 0xCA, 0xC1, 0xEA, 0x02, 0x31, 0xCA,
    0x81, 0xE2, 0x20, 0x13, 0x00, 0x00, 0x31, 0xD1, 0xC1, 0xE2, 0x02, 0x31, 0xCA] ++ bytes_l10446f_6

theorem code_l10446f_5 : ∀ x ∈ codeRange 0x10459c bytes_l10446f_5, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x459c 61 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10446f_6

def b_l10446f_4 : Block Op Label signature Reg.count 208 :=
  .letOp (n := 208) (.out 0x104560 (movzxR32M16Effect 0x104560 5 1 (.sib 4 none 0 (.d8 0x22))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 209) (.exec 0x104560 (LoadPre 0x104560 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x22)) s (0x104560 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x104560 5 1 (.sib 4 none 0 (.d8 0x22))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 210) (.out 0x104565 (movR32R32Effect 0x104565 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[208]
    (.letOp (n := 211) (.exec 0x104565 (fun s => s.RIP = 0x104565) (movR32R32Effect 0x104565 2 2 1) (Reg.operands [.gpr 1] [])) #v[208]
    (.letOp (n := 212) (.out 0x104567 (shrR32Effect 0x104567 3 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[210]
    (.letOp (n := 213) (.exec 0x104567 (fun s => s.RIP = 0x104567) (shrR32Effect 0x104567 3 2 2) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[210]
    (.letOp (n := 214) (.out 0x10456a (xorR32R32Effect 0x10456a 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[212, 208]
    (.letOp (n := 215) (.exec 0x10456a (fun s => s.RIP = 0x10456a) (xorR32R32Effect 0x10456a 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[212, 208]
    (.letOp (n := 216) (.out 0x10456c (andR32Imm32Effect 0x10456c 6 2 0x1320) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[214]
    (.letOp (n := 217) (.exec 0x10456c (fun s => s.RIP = 0x10456c) (andR32Imm32Effect 0x10456c 6 2 0x1320) (Reg.operands [.gpr 2] [])) #v[214]
    (.letOp (n := 218) (.out 0x104572 (xorR32R32Effect 0x104572 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[208, 216]
    (.letOp (n := 219) (.exec 0x104572 (fun s => s.RIP = 0x104572) (xorR32R32Effect 0x104572 2 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[208, 216]
    (.letOp (n := 220) (.out 0x104574 (shlR32Effect 0x104574 3 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[216]
    (.letOp (n := 221) (.exec 0x104574 (fun s => s.RIP = 0x104574) (shlR32Effect 0x104574 3 2 2) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[216]
    (.letOp (n := 222) (.out 0x104577 (xorR32R32Effect 0x104577 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[220, 218]
    (.letOp (n := 223) (.exec 0x104577 (fun s => s.RIP = 0x104577) (xorR32R32Effect 0x104577 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[220, 218]
    (.letOp (n := 224) (.out 0x104579 (movR32R32Effect 0x104579 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[222]
    (.letOp (n := 225) (.exec 0x104579 (fun s => s.RIP = 0x104579) (movR32R32Effect 0x104579 2 1 2) (Reg.operands [.gpr 2] [])) #v[222]
    (.letOp (n := 226) (.out 0x10457b (shrR32Effect 0x10457b 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[224]
    (.letOp (n := 227) (.exec 0x10457b (fun s => s.RIP = 0x10457b) (shrR32Effect 0x10457b 2 1 1) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[224]
    (.letOp (n := 228) (.out 0x10457d (xorR32R32Effect 0x10457d 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[226, 222]
    (.letOp (n := 229) (.exec 0x10457d (fun s => s.RIP = 0x10457d) (xorR32R32Effect 0x10457d 2 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[226, 222]
    (.letOp (n := 230) (.out 0x10457f (andR32Imm32Effect 0x10457f 6 1 0x5050) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[228]
    (.letOp (n := 231) (.exec 0x10457f (fun s => s.RIP = 0x10457f) (andR32Imm32Effect 0x10457f 6 1 0x5050) (Reg.operands [.gpr 1] [])) #v[228]
    (.letOp (n := 232) (.out 0x104585 (xorR32R32Effect 0x104585 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[222, 230]
    (.letOp (n := 233) (.exec 0x104585 (fun s => s.RIP = 0x104585) (xorR32R32Effect 0x104585 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[222, 230]
    (.letOp (n := 234) (.out 0x104587 (addR32R32Effect 0x104587 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[230, 230]
    (.letOp (n := 235) (.exec 0x104587 (fun s => s.RIP = 0x104587) (addR32R32Effect 0x104587 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[230, 230]
    (.letOp (n := 236) (.out 0x104589 (xorR32R32Effect 0x104589 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[234, 232]
    (.letOp (n := 237) (.exec 0x104589 (fun s => s.RIP = 0x104589) (xorR32R32Effect 0x104589 2 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[234, 232]
    (.letOp (n := 238) (.exec 0x10458b (StorePre 0x10458b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x22)) s (0x10458b + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x10458b 5 1 (.sib 4 none 0 (.d8 0x22))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[236, 4]
    (.letOp (n := 239) (.out 0x104590 (movzxR32M16Effect 0x104590 5 1 (.sib 4 none 0 (.d8 0x24))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 240) (.exec 0x104590 (LoadPre 0x104590 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x104590 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x104590 5 1 (.sib 4 none 0 (.d8 0x24))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 241) (.out 0x104595 (movR32R32Effect 0x104595 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[239]
    (.letOp (n := 242) (.exec 0x104595 (fun s => s.RIP = 0x104595) (movR32R32Effect 0x104595 2 2 1) (Reg.operands [.gpr 1] [])) #v[239]
    (.letOp (n := 243) (.out 0x104597 (shrR32Effect 0x104597 3 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[241]
    (.letOp (n := 244) (.exec 0x104597 (fun s => s.RIP = 0x104597) (shrR32Effect 0x104597 3 2 2) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[241]
    (.letOp (n := 245) (.out 0x10459a (xorR32R32Effect 0x10459a 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[243, 239]
    (.letOp (n := 246) (.exec 0x10459a (fun s => s.RIP = 0x10459a) (xorR32R32Effect 0x10459a 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[243, 239]
    (b_l10446f_5)))))))))))))))))))))))))))))))))))))))

def bytes_l10446f_4 : List UInt8 :=
  [0x0F, 0xB7, 0x4C, 0x24, 0x22, 0x89, 0xCA, 0xC1, 0xEA, 0x02, 0x31, 0xCA, 0x81, 0xE2, 0x20, 0x13,
    0x00, 0x00, 0x31, 0xD1, 0xC1, 0xE2, 0x02, 0x31, 0xCA, 0x89, 0xD1, 0xD1, 0xE9, 0x31, 0xD1, 0x81,
    0xE1, 0x50, 0x50, 0x00, 0x00, 0x31, 0xCA, 0x01, 0xC9, 0x31, 0xD1, 0x66, 0x89, 0x4C, 0x24, 0x22,
    0x0F, 0xB7, 0x4C, 0x24, 0x24, 0x89, 0xCA, 0xC1, 0xEA, 0x02, 0x31, 0xCA] ++ bytes_l10446f_5

theorem code_l10446f_4 : ∀ x ∈ codeRange 0x104560 bytes_l10446f_4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x4560 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10446f_5

def b_l10446f_3 : Block Op Label signature Reg.count 170 :=
  .letOp (n := 170) (.out 0x104525 (xorR32R32Effect 0x104525 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[160, 168]
    (.letOp (n := 171) (.exec 0x104525 (fun s => s.RIP = 0x104525) (xorR32R32Effect 0x104525 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[160, 168]
    (.letOp (n := 172) (.out 0x104527 (addR32R32Effect 0x104527 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[168, 168]
    (.letOp (n := 173) (.exec 0x104527 (fun s => s.RIP = 0x104527) (addR32R32Effect 0x104527 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[168, 168]
    (.letOp (n := 174) (.out 0x104529 (xorR32R32Effect 0x104529 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[172, 170]
    (.letOp (n := 175) (.exec 0x104529 (fun s => s.RIP = 0x104529) (xorR32R32Effect 0x104529 2 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[172, 170]
    (.letOp (n := 176) (.exec 0x10452b (StorePre 0x10452b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1e)) s (0x10452b + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x10452b 5 1 (.sib 4 none 0 (.d8 0x1e))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[174, 4]
    (.letOp (n := 177) (.out 0x104530 (movzxR32M16Effect 0x104530 5 1 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 178) (.exec 0x104530 (LoadPre 0x104530 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x104530 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x104530 5 1 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 179) (.out 0x104535 (movR32R32Effect 0x104535 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[177]
    (.letOp (n := 180) (.exec 0x104535 (fun s => s.RIP = 0x104535) (movR32R32Effect 0x104535 2 2 1) (Reg.operands [.gpr 1] [])) #v[177]
    (.letOp (n := 181) (.out 0x104537 (shrR32Effect 0x104537 3 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[179]
    (.letOp (n := 182) (.exec 0x104537 (fun s => s.RIP = 0x104537) (shrR32Effect 0x104537 3 2 2) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[179]
    (.letOp (n := 183) (.out 0x10453a (xorR32R32Effect 0x10453a 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[181, 177]
    (.letOp (n := 184) (.exec 0x10453a (fun s => s.RIP = 0x10453a) (xorR32R32Effect 0x10453a 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[181, 177]
    (.letOp (n := 185) (.out 0x10453c (andR32Imm32Effect 0x10453c 6 2 0x1320) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[183]
    (.letOp (n := 186) (.exec 0x10453c (fun s => s.RIP = 0x10453c) (andR32Imm32Effect 0x10453c 6 2 0x1320) (Reg.operands [.gpr 2] [])) #v[183]
    (.letOp (n := 187) (.out 0x104542 (xorR32R32Effect 0x104542 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[177, 185]
    (.letOp (n := 188) (.exec 0x104542 (fun s => s.RIP = 0x104542) (xorR32R32Effect 0x104542 2 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[177, 185]
    (.letOp (n := 189) (.out 0x104544 (shlR32Effect 0x104544 3 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[185]
    (.letOp (n := 190) (.exec 0x104544 (fun s => s.RIP = 0x104544) (shlR32Effect 0x104544 3 2 2) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[185]
    (.letOp (n := 191) (.out 0x104547 (xorR32R32Effect 0x104547 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[189, 187]
    (.letOp (n := 192) (.exec 0x104547 (fun s => s.RIP = 0x104547) (xorR32R32Effect 0x104547 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[189, 187]
    (.letOp (n := 193) (.out 0x104549 (movR32R32Effect 0x104549 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[191]
    (.letOp (n := 194) (.exec 0x104549 (fun s => s.RIP = 0x104549) (movR32R32Effect 0x104549 2 1 2) (Reg.operands [.gpr 2] [])) #v[191]
    (.letOp (n := 195) (.out 0x10454b (shrR32Effect 0x10454b 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[193]
    (.letOp (n := 196) (.exec 0x10454b (fun s => s.RIP = 0x10454b) (shrR32Effect 0x10454b 2 1 1) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[193]
    (.letOp (n := 197) (.out 0x10454d (xorR32R32Effect 0x10454d 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[195, 191]
    (.letOp (n := 198) (.exec 0x10454d (fun s => s.RIP = 0x10454d) (xorR32R32Effect 0x10454d 2 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[195, 191]
    (.letOp (n := 199) (.out 0x10454f (andR32Imm32Effect 0x10454f 6 1 0x5050) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[197]
    (.letOp (n := 200) (.exec 0x10454f (fun s => s.RIP = 0x10454f) (andR32Imm32Effect 0x10454f 6 1 0x5050) (Reg.operands [.gpr 1] [])) #v[197]
    (.letOp (n := 201) (.out 0x104555 (xorR32R32Effect 0x104555 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[191, 199]
    (.letOp (n := 202) (.exec 0x104555 (fun s => s.RIP = 0x104555) (xorR32R32Effect 0x104555 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[191, 199]
    (.letOp (n := 203) (.out 0x104557 (addR32R32Effect 0x104557 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[199, 199]
    (.letOp (n := 204) (.exec 0x104557 (fun s => s.RIP = 0x104557) (addR32R32Effect 0x104557 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[199, 199]
    (.letOp (n := 205) (.out 0x104559 (xorR32R32Effect 0x104559 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[203, 201]
    (.letOp (n := 206) (.exec 0x104559 (fun s => s.RIP = 0x104559) (xorR32R32Effect 0x104559 2 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[203, 201]
    (.letOp (n := 207) (.exec 0x10455b (StorePre 0x10455b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10455b + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x10455b 5 1 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[205, 4]
    (b_l10446f_4))))))))))))))))))))))))))))))))))))))

def bytes_l10446f_3 : List UInt8 :=
  [0x31, 0xCA, 0x01, 0xC9, 0x31, 0xD1, 0x66, 0x89, 0x4C, 0x24, 0x1E, 0x0F, 0xB7, 0x4C, 0x24, 0x20,
    0x89, 0xCA, 0xC1, 0xEA, 0x02, 0x31, 0xCA, 0x81, 0xE2, 0x20, 0x13, 0x00, 0x00, 0x31, 0xD1, 0xC1,
    0xE2, 0x02, 0x31, 0xCA, 0x89, 0xD1, 0xD1, 0xE9, 0x31, 0xD1, 0x81, 0xE1, 0x50, 0x50, 0x00, 0x00,
    0x31, 0xCA, 0x01, 0xC9, 0x31, 0xD1, 0x66, 0x89, 0x4C, 0x24, 0x20] ++ bytes_l10446f_4

theorem code_l10446f_3 : ∀ x ∈ codeRange 0x104525 bytes_l10446f_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x4525 59 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10446f_4

def b_l10446f_2 : Block Op Label signature Reg.count 131 :=
  .letOp (n := 131) (.out 0x1044e9 (movR32R32Effect 0x1044e9 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[129]
    (.letOp (n := 132) (.exec 0x1044e9 (fun s => s.RIP = 0x1044e9) (movR32R32Effect 0x1044e9 2 1 2) (Reg.operands [.gpr 2] [])) #v[129]
    (.letOp (n := 133) (.out 0x1044eb (shrR32Effect 0x1044eb 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[131]
    (.letOp (n := 134) (.exec 0x1044eb (fun s => s.RIP = 0x1044eb) (shrR32Effect 0x1044eb 2 1 1) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[131]
    (.letOp (n := 135) (.out 0x1044ed (xorR32R32Effect 0x1044ed 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[133, 129]
    (.letOp (n := 136) (.exec 0x1044ed (fun s => s.RIP = 0x1044ed) (xorR32R32Effect 0x1044ed 2 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[133, 129]
    (.letOp (n := 137) (.out 0x1044ef (andR32Imm32Effect 0x1044ef 6 1 0x5050) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[135]
    (.letOp (n := 138) (.exec 0x1044ef (fun s => s.RIP = 0x1044ef) (andR32Imm32Effect 0x1044ef 6 1 0x5050) (Reg.operands [.gpr 1] [])) #v[135]
    (.letOp (n := 139) (.out 0x1044f5 (xorR32R32Effect 0x1044f5 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[129, 137]
    (.letOp (n := 140) (.exec 0x1044f5 (fun s => s.RIP = 0x1044f5) (xorR32R32Effect 0x1044f5 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[129, 137]
    (.letOp (n := 141) (.out 0x1044f7 (addR32R32Effect 0x1044f7 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[137, 137]
    (.letOp (n := 142) (.exec 0x1044f7 (fun s => s.RIP = 0x1044f7) (addR32R32Effect 0x1044f7 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[137, 137]
    (.letOp (n := 143) (.out 0x1044f9 (xorR32R32Effect 0x1044f9 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[141, 139]
    (.letOp (n := 144) (.exec 0x1044f9 (fun s => s.RIP = 0x1044f9) (xorR32R32Effect 0x1044f9 2 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[141, 139]
    (.letOp (n := 145) (.exec 0x1044fb (StorePre 0x1044fb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x1044fb + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1044fb 5 1 (.sib 4 none 0 (.d8 0x1c))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[143, 4]
    (.letOp (n := 146) (.out 0x104500 (movzxR32M16Effect 0x104500 5 1 (.sib 4 none 0 (.d8 0x1e))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 147) (.exec 0x104500 (LoadPre 0x104500 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1e)) s (0x104500 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x104500 5 1 (.sib 4 none 0 (.d8 0x1e))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 148) (.out 0x104505 (movR32R32Effect 0x104505 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[146]
    (.letOp (n := 149) (.exec 0x104505 (fun s => s.RIP = 0x104505) (movR32R32Effect 0x104505 2 2 1) (Reg.operands [.gpr 1] [])) #v[146]
    (.letOp (n := 150) (.out 0x104507 (shrR32Effect 0x104507 3 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[148]
    (.letOp (n := 151) (.exec 0x104507 (fun s => s.RIP = 0x104507) (shrR32Effect 0x104507 3 2 2) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[148]
    (.letOp (n := 152) (.out 0x10450a (xorR32R32Effect 0x10450a 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[150, 146]
    (.letOp (n := 153) (.exec 0x10450a (fun s => s.RIP = 0x10450a) (xorR32R32Effect 0x10450a 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[150, 146]
    (.letOp (n := 154) (.out 0x10450c (andR32Imm32Effect 0x10450c 6 2 0x1320) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[152]
    (.letOp (n := 155) (.exec 0x10450c (fun s => s.RIP = 0x10450c) (andR32Imm32Effect 0x10450c 6 2 0x1320) (Reg.operands [.gpr 2] [])) #v[152]
    (.letOp (n := 156) (.out 0x104512 (xorR32R32Effect 0x104512 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[146, 154]
    (.letOp (n := 157) (.exec 0x104512 (fun s => s.RIP = 0x104512) (xorR32R32Effect 0x104512 2 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[146, 154]
    (.letOp (n := 158) (.out 0x104514 (shlR32Effect 0x104514 3 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[154]
    (.letOp (n := 159) (.exec 0x104514 (fun s => s.RIP = 0x104514) (shlR32Effect 0x104514 3 2 2) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[154]
    (.letOp (n := 160) (.out 0x104517 (xorR32R32Effect 0x104517 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[158, 156]
    (.letOp (n := 161) (.exec 0x104517 (fun s => s.RIP = 0x104517) (xorR32R32Effect 0x104517 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[158, 156]
    (.letOp (n := 162) (.out 0x104519 (movR32R32Effect 0x104519 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[160]
    (.letOp (n := 163) (.exec 0x104519 (fun s => s.RIP = 0x104519) (movR32R32Effect 0x104519 2 1 2) (Reg.operands [.gpr 2] [])) #v[160]
    (.letOp (n := 164) (.out 0x10451b (shrR32Effect 0x10451b 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[162]
    (.letOp (n := 165) (.exec 0x10451b (fun s => s.RIP = 0x10451b) (shrR32Effect 0x10451b 2 1 1) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[162]
    (.letOp (n := 166) (.out 0x10451d (xorR32R32Effect 0x10451d 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[164, 160]
    (.letOp (n := 167) (.exec 0x10451d (fun s => s.RIP = 0x10451d) (xorR32R32Effect 0x10451d 2 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[164, 160]
    (.letOp (n := 168) (.out 0x10451f (andR32Imm32Effect 0x10451f 6 1 0x5050) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[166]
    (.letOp (n := 169) (.exec 0x10451f (fun s => s.RIP = 0x10451f) (andR32Imm32Effect 0x10451f 6 1 0x5050) (Reg.operands [.gpr 1] [])) #v[166]
    (b_l10446f_3)))))))))))))))))))))))))))))))))))))))

def bytes_l10446f_2 : List UInt8 :=
  [0x89, 0xD1, 0xD1, 0xE9, 0x31, 0xD1, 0x81, 0xE1, 0x50, 0x50, 0x00, 0x00, 0x31, 0xCA, 0x01, 0xC9,
    0x31, 0xD1, 0x66, 0x89, 0x4C, 0x24, 0x1C, 0x0F, 0xB7, 0x4C, 0x24, 0x1E, 0x89, 0xCA, 0xC1, 0xEA,
    0x02, 0x31, 0xCA, 0x81, 0xE2, 0x20, 0x13, 0x00, 0x00, 0x31, 0xD1, 0xC1, 0xE2, 0x02, 0x31, 0xCA,
    0x89, 0xD1, 0xD1, 0xE9, 0x31, 0xD1, 0x81, 0xE1, 0x50, 0x50, 0x00, 0x00] ++ bytes_l10446f_3

theorem code_l10446f_2 : ∀ x ∈ codeRange 0x1044e9 bytes_l10446f_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x44e9 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10446f_3

def b_l10446f_1 : Block Op Label signature Reg.count 92 :=
  .letOp (n := 92) (.out 0x1044ac (andR32Imm32Effect 0x1044ac 6 2 0x1320) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[90]
    (.letOp (n := 93) (.exec 0x1044ac (fun s => s.RIP = 0x1044ac) (andR32Imm32Effect 0x1044ac 6 2 0x1320) (Reg.operands [.gpr 2] [])) #v[90]
    (.letOp (n := 94) (.out 0x1044b2 (xorR32R32Effect 0x1044b2 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[84, 92]
    (.letOp (n := 95) (.exec 0x1044b2 (fun s => s.RIP = 0x1044b2) (xorR32R32Effect 0x1044b2 2 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[84, 92]
    (.letOp (n := 96) (.out 0x1044b4 (shlR32Effect 0x1044b4 3 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[92]
    (.letOp (n := 97) (.exec 0x1044b4 (fun s => s.RIP = 0x1044b4) (shlR32Effect 0x1044b4 3 2 2) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[92]
    (.letOp (n := 98) (.out 0x1044b7 (xorR32R32Effect 0x1044b7 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[96, 94]
    (.letOp (n := 99) (.exec 0x1044b7 (fun s => s.RIP = 0x1044b7) (xorR32R32Effect 0x1044b7 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[96, 94]
    (.letOp (n := 100) (.out 0x1044b9 (movR32R32Effect 0x1044b9 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[98]
    (.letOp (n := 101) (.exec 0x1044b9 (fun s => s.RIP = 0x1044b9) (movR32R32Effect 0x1044b9 2 1 2) (Reg.operands [.gpr 2] [])) #v[98]
    (.letOp (n := 102) (.out 0x1044bb (shrR32Effect 0x1044bb 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[100]
    (.letOp (n := 103) (.exec 0x1044bb (fun s => s.RIP = 0x1044bb) (shrR32Effect 0x1044bb 2 1 1) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[100]
    (.letOp (n := 104) (.out 0x1044bd (xorR32R32Effect 0x1044bd 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[102, 98]
    (.letOp (n := 105) (.exec 0x1044bd (fun s => s.RIP = 0x1044bd) (xorR32R32Effect 0x1044bd 2 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[102, 98]
    (.letOp (n := 106) (.out 0x1044bf (andR32Imm32Effect 0x1044bf 6 1 0x5050) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[104]
    (.letOp (n := 107) (.exec 0x1044bf (fun s => s.RIP = 0x1044bf) (andR32Imm32Effect 0x1044bf 6 1 0x5050) (Reg.operands [.gpr 1] [])) #v[104]
    (.letOp (n := 108) (.out 0x1044c5 (xorR32R32Effect 0x1044c5 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[98, 106]
    (.letOp (n := 109) (.exec 0x1044c5 (fun s => s.RIP = 0x1044c5) (xorR32R32Effect 0x1044c5 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[98, 106]
    (.letOp (n := 110) (.out 0x1044c7 (addR32R32Effect 0x1044c7 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[106, 106]
    (.letOp (n := 111) (.exec 0x1044c7 (fun s => s.RIP = 0x1044c7) (addR32R32Effect 0x1044c7 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[106, 106]
    (.letOp (n := 112) (.out 0x1044c9 (xorR32R32Effect 0x1044c9 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[110, 108]
    (.letOp (n := 113) (.exec 0x1044c9 (fun s => s.RIP = 0x1044c9) (xorR32R32Effect 0x1044c9 2 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[110, 108]
    (.letOp (n := 114) (.exec 0x1044cb (StorePre 0x1044cb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1a)) s (0x1044cb + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1044cb 5 1 (.sib 4 none 0 (.d8 0x1a))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[112, 4]
    (.letOp (n := 115) (.out 0x1044d0 (movzxR32M16Effect 0x1044d0 5 1 (.sib 4 none 0 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 116) (.exec 0x1044d0 (LoadPre 0x1044d0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x1044d0 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x1044d0 5 1 (.sib 4 none 0 (.d8 0x1c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 117) (.out 0x1044d5 (movR32R32Effect 0x1044d5 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[115]
    (.letOp (n := 118) (.exec 0x1044d5 (fun s => s.RIP = 0x1044d5) (movR32R32Effect 0x1044d5 2 2 1) (Reg.operands [.gpr 1] [])) #v[115]
    (.letOp (n := 119) (.out 0x1044d7 (shrR32Effect 0x1044d7 3 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[117]
    (.letOp (n := 120) (.exec 0x1044d7 (fun s => s.RIP = 0x1044d7) (shrR32Effect 0x1044d7 3 2 2) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[117]
    (.letOp (n := 121) (.out 0x1044da (xorR32R32Effect 0x1044da 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[119, 115]
    (.letOp (n := 122) (.exec 0x1044da (fun s => s.RIP = 0x1044da) (xorR32R32Effect 0x1044da 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[119, 115]
    (.letOp (n := 123) (.out 0x1044dc (andR32Imm32Effect 0x1044dc 6 2 0x1320) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[121]
    (.letOp (n := 124) (.exec 0x1044dc (fun s => s.RIP = 0x1044dc) (andR32Imm32Effect 0x1044dc 6 2 0x1320) (Reg.operands [.gpr 2] [])) #v[121]
    (.letOp (n := 125) (.out 0x1044e2 (xorR32R32Effect 0x1044e2 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[115, 123]
    (.letOp (n := 126) (.exec 0x1044e2 (fun s => s.RIP = 0x1044e2) (xorR32R32Effect 0x1044e2 2 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[115, 123]
    (.letOp (n := 127) (.out 0x1044e4 (shlR32Effect 0x1044e4 3 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[123]
    (.letOp (n := 128) (.exec 0x1044e4 (fun s => s.RIP = 0x1044e4) (shlR32Effect 0x1044e4 3 2 2) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[123]
    (.letOp (n := 129) (.out 0x1044e7 (xorR32R32Effect 0x1044e7 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[127, 125]
    (.letOp (n := 130) (.exec 0x1044e7 (fun s => s.RIP = 0x1044e7) (xorR32R32Effect 0x1044e7 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[127, 125]
    (b_l10446f_2)))))))))))))))))))))))))))))))))))))))

def bytes_l10446f_1 : List UInt8 :=
  [0x81, 0xE2, 0x20, 0x13, 0x00, 0x00, 0x31, 0xD1, 0xC1, 0xE2, 0x02, 0x31, 0xCA, 0x89, 0xD1, 0xD1,
    0xE9, 0x31, 0xD1, 0x81, 0xE1, 0x50, 0x50, 0x00, 0x00, 0x31, 0xCA, 0x01, 0xC9, 0x31, 0xD1, 0x66,
    0x89, 0x4C, 0x24, 0x1A, 0x0F, 0xB7, 0x4C, 0x24, 0x1C, 0x89, 0xCA, 0xC1, 0xEA, 0x02, 0x31, 0xCA,
    0x81, 0xE2, 0x20, 0x13, 0x00, 0x00, 0x31, 0xD1, 0xC1, 0xE2, 0x02, 0x31, 0xCA] ++ bytes_l10446f_2

theorem code_l10446f_1 : ∀ x ∈ codeRange 0x1044ac bytes_l10446f_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x44ac 61 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10446f_2

def b_l10446f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10446f (movzxR32M16Effect 0x10446f 5 0 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x10446f (LoadPre 0x10446f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10446f + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x10446f 5 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x104474 (movR32R32Effect 0x104474 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 56) (.exec 0x104474 (fun s => s.RIP = 0x104474) (movR32R32Effect 0x104474 2 1 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x104476 (shrR32Effect 0x104476 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[55]
    (.letOp (n := 58) (.exec 0x104476 (fun s => s.RIP = 0x104476) (shrR32Effect 0x104476 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[55]
    (.letOp (n := 59) (.out 0x104479 (xorR32R32Effect 0x104479 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[57, 53]
    (.letOp (n := 60) (.exec 0x104479 (fun s => s.RIP = 0x104479) (xorR32R32Effect 0x104479 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[57, 53]
    (.letOp (n := 61) (.out 0x10447b (andR32Imm32Effect 0x10447b 6 1 0x1320) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[59]
    (.letOp (n := 62) (.exec 0x10447b (fun s => s.RIP = 0x10447b) (andR32Imm32Effect 0x10447b 6 1 0x1320) (Reg.operands [.gpr 1] [])) #v[59]
    (.letOp (n := 63) (.out 0x104481 (xorR32R32Effect 0x104481 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[53, 61]
    (.letOp (n := 64) (.exec 0x104481 (fun s => s.RIP = 0x104481) (xorR32R32Effect 0x104481 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[53, 61]
    (.letOp (n := 65) (.out 0x104483 (shlR32Effect 0x104483 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[61]
    (.letOp (n := 66) (.exec 0x104483 (fun s => s.RIP = 0x104483) (shlR32Effect 0x104483 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[61]
    (.letOp (n := 67) (.out 0x104486 (xorR32R32Effect 0x104486 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[65, 63]
    (.letOp (n := 68) (.exec 0x104486 (fun s => s.RIP = 0x104486) (xorR32R32Effect 0x104486 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[65, 63]
    (.letOp (n := 69) (.out 0x104488 (movR32R32Effect 0x104488 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[67]
    (.letOp (n := 70) (.exec 0x104488 (fun s => s.RIP = 0x104488) (movR32R32Effect 0x104488 2 0 1) (Reg.operands [.gpr 1] [])) #v[67]
    (.letOp (n := 71) (.out 0x10448a (shrR32Effect 0x10448a 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[69]
    (.letOp (n := 72) (.exec 0x10448a (fun s => s.RIP = 0x10448a) (shrR32Effect 0x10448a 2 0 1) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[69]
    (.letOp (n := 73) (.out 0x10448c (xorR32R32Effect 0x10448c 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[71, 67]
    (.letOp (n := 74) (.exec 0x10448c (fun s => s.RIP = 0x10448c) (xorR32R32Effect 0x10448c 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[71, 67]
    (.letOp (n := 75) (.out 0x10448e (andEaxImm32Effect 0x10448e 0x5050) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[73]
    (.letOp (n := 76) (.exec 0x10448e (fun s => s.RIP = 0x10448e) (andEaxImm32Effect 0x10448e 0x5050) (Reg.operands [.gpr 0] [])) #v[73]
    (.letOp (n := 77) (.out 0x104493 (xorR32R32Effect 0x104493 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[67, 75]
    (.letOp (n := 78) (.exec 0x104493 (fun s => s.RIP = 0x104493) (xorR32R32Effect 0x104493 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[67, 75]
    (.letOp (n := 79) (.out 0x104495 (addR32R32Effect 0x104495 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[75, 75]
    (.letOp (n := 80) (.exec 0x104495 (fun s => s.RIP = 0x104495) (addR32R32Effect 0x104495 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[75, 75]
    (.letOp (n := 81) (.out 0x104497 (xorR32R32Effect 0x104497 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[79, 77]
    (.letOp (n := 82) (.exec 0x104497 (fun s => s.RIP = 0x104497) (xorR32R32Effect 0x104497 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[79, 77]
    (.letOp (n := 83) (.exec 0x104499 (StorePre 0x104499 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xbc)) s (0x104499 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x104499 0 (.sib 4 none 0 (.d32 0xbc))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[81, 4]
    (.letOp (n := 84) (.out 0x1044a0 (movzxR32M16Effect 0x1044a0 5 1 (.sib 4 none 0 (.d8 0x1a))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 85) (.exec 0x1044a0 (LoadPre 0x1044a0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1a)) s (0x1044a0 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x1044a0 5 1 (.sib 4 none 0 (.d8 0x1a))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 86) (.out 0x1044a5 (movR32R32Effect 0x1044a5 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[84]
    (.letOp (n := 87) (.exec 0x1044a5 (fun s => s.RIP = 0x1044a5) (movR32R32Effect 0x1044a5 2 2 1) (Reg.operands [.gpr 1] [])) #v[84]
    (.letOp (n := 88) (.out 0x1044a7 (shrR32Effect 0x1044a7 3 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[86]
    (.letOp (n := 89) (.exec 0x1044a7 (fun s => s.RIP = 0x1044a7) (shrR32Effect 0x1044a7 3 2 2) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[86]
    (.letOp (n := 90) (.out 0x1044aa (xorR32R32Effect 0x1044aa 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[88, 84]
    (.letOp (n := 91) (.exec 0x1044aa (fun s => s.RIP = 0x1044aa) (xorR32R32Effect 0x1044aa 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[88, 84]
    (b_l10446f_1)))))))))))))))))))))))))))))))))))))))

def bytes_l10446f : List UInt8 :=
  [0x0F, 0xB7, 0x44, 0x24, 0x18, 0x89, 0xC1, 0xC1, 0xE9, 0x02, 0x31, 0xC1, 0x81, 0xE1, 0x20, 0x13,
    0x00, 0x00, 0x31, 0xC8, 0xC1, 0xE1, 0x02, 0x31, 0xC1, 0x89, 0xC8, 0xD1, 0xE8, 0x31, 0xC8, 0x25,
    0x50, 0x50, 0x00, 0x00, 0x31, 0xC1, 0x01, 0xC0, 0x31, 0xC8, 0x89, 0x84, 0x24, 0xBC, 0x00, 0x00,
    0x00, 0x0F, 0xB7, 0x4C, 0x24, 0x1A, 0x89, 0xCA, 0xC1, 0xEA, 0x02, 0x31, 0xCA] ++ bytes_l10446f_1

theorem code_l10446f : ∀ x ∈ codeRange 0x10446f bytes_l10446f, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x446f 61 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10446f_1

@[cfg_block] def b_l1050df : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1050df (movR64R64Effect 0x1050df 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 54) (.exec 0x1050df (fun s => s.RIP = 0x1050df) (movR64R64Effect 0x1050df 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x1050e2 (addR64Imm32Effect 0x1050e2 4 0xd8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 56) (.exec 0x1050e2 (fun s => s.RIP = 0x1050e2) (addR64Imm32Effect 0x1050e2 4 0xd8) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1050e9 (popR64Effect 0x1050e9 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[55]
    (.letOp (n := 58) (.out 0x1050e9 (popR64Effect 0x1050e9 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[55]
    (.letOp (n := 59) (.exec 0x1050e9 (PopPre 0x1050e9) (popR64Effect 0x1050e9 1 3) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 60) (.out 0x1050ea (popR64Effect 0x1050ea 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[58]
    (.letOp (n := 61) (.out 0x1050ea (popR64Effect 0x1050ea 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[58]
    (.letOp (n := 62) (.exec 0x1050ea (PopPre 0x1050ea) (popR64Effect 0x1050ea 2 12) (Reg.operands [.gpr 4] [])) #v[58]
    (.letOp (n := 63) (.out 0x1050ec (popR64Effect 0x1050ec 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[61]
    (.letOp (n := 64) (.out 0x1050ec (popR64Effect 0x1050ec 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 65) (.exec 0x1050ec (PopPre 0x1050ec) (popR64Effect 0x1050ec 2 13) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 66) (.out 0x1050ee (popR64Effect 0x1050ee 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[64]
    (.letOp (n := 67) (.out 0x1050ee (popR64Effect 0x1050ee 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[64]
    (.letOp (n := 68) (.exec 0x1050ee (PopPre 0x1050ee) (popR64Effect 0x1050ee 2 14) (Reg.operands [.gpr 4] [])) #v[64]
    (.letOp (n := 69) (.out 0x1050f0 (popR64Effect 0x1050f0 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[67]
    (.letOp (n := 70) (.out 0x1050f0 (popR64Effect 0x1050f0 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[67]
    (.letOp (n := 71) (.exec 0x1050f0 (PopPre 0x1050f0) (popR64Effect 0x1050f0 2 15) (Reg.operands [.gpr 4] [])) #v[67]
    (.letOp (n := 72) (.out 0x1050f2 (popR64Effect 0x1050f2 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[70]
    (.letOp (n := 73) (.out 0x1050f2 (popR64Effect 0x1050f2 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[70]
    (.letOp (n := 74) (.exec 0x1050f2 (PopPre 0x1050f2) (popR64Effect 0x1050f2 1 5) (Reg.operands [.gpr 4] [])) #v[70]
    (.letOp (n := 75) (.out 0x1050f3 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[73]
    (.letOp (n := 76) (.out 0x1050f3 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[73]
    (.letOp (n := 77) (.exec 0x1050f3 (RetPre 0x1050f3) (retEffect) (Reg.operands [.gpr 4] [])) #v[73]
    (.terminate (.ret (RegMap.args [(0, 53), (1, 1), (2, 2), (3, 57), (4, 76), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 78) (some ⟨75, by decide⟩)))))))))))))))))))))))))))

def bytes_l1050df : List UInt8 :=
  [0x48, 0x89, 0xD8, 0x48, 0x81, 0xC4, 0xD8, 0x00, 0x00, 0x00, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41,
    0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l1050df : ∀ x ∈ codeRange 0x1050df bytes_l1050df, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x50df 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105100 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x105100 (pushR64Effect 0x105100 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x105100 (PushPre 0x105100 1) (pushR64Effect 0x105100 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x105101 (pushR64Effect 0x105101 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x105101 (PushPre 0x105101 2) (pushR64Effect 0x105101 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x105103 (pushR64Effect 0x105103 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x105103 (PushPre 0x105103 2) (pushR64Effect 0x105103 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x105105 (pushR64Effect 0x105105 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x105105 (PushPre 0x105105 2) (pushR64Effect 0x105105 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x105107 (pushR64Effect 0x105107 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x105107 (PushPre 0x105107 2) (pushR64Effect 0x105107 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x105109 (pushR64Effect 0x105109 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x105109 (PushPre 0x105109 1) (pushR64Effect 0x105109 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x10510a (subR64Imm8Effect 0x10510a 4 0x38) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x10510a (fun s => s.RIP = 0x10510a) (subR64Imm8Effect 0x10510a 4 0x38) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x10510e (movR64R64Effect 0x10510e 3 6) (EffectPart.reads (.reg (.gpr 3)) [.gpr 6] []) (.reg (.gpr 3))) #v[6]
    (.letOp (n := 68) (.exec 0x10510e (fun s => s.RIP = 0x10510e) (movR64R64Effect 0x10510e 3 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 69) (.exec 0x105111 (StorePre 0x105111 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x105111 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x105111 7 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[7, 65]
    (.letOp (n := 70) (.exec 0x105116 (StorePre 0x105116 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x105116 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x105116 (.sib 4 none 0 (.d8 0x8)) 0x0) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 71) (.exec 0x10511f (StorePre 0x10511f 8 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10511f + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x10511f (.sib 4 none 0 .none) 0x0) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 72) (.out 0x105127 (movR64R64Effect 0x105127 7 4) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[65]
    (.letOp (n := 73) (.exec 0x105127 (fun s => s.RIP = 0x105127) (movR64R64Effect 0x105127 7 4) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 74) (.out 0x10512a (movR32Imm32Effect 0x10512a 5 6 0x8) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 75) (.exec 0x10512a (fun s => s.RIP = 0x10512a) (movR32Imm32Effect 0x10512a 5 6 0x8) (Reg.operands [] [])) #v[]
    (.letOp (n := 76) (.out 0x10512f (callEffect (fun _ => 0x109ff0) 0x105134) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 77) (.exec 0x10512f (PushPre 0x10512f 5) (callEffect (fun _ => 0x109ff0) 0x105134) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 78) (.const ⟨64, 0x105134⟩) #v[]
    (.terminate (.call ⟨.l109ff0, RegMap.args [(2, 2), (3, 67), (4, 76), (5, 5), (6, 74), (7, 72), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 79⟩ { target := .l105134, kept := #v[], arity := rfl, guard := some (Fin.last 78) })))))))))))))))))))))))))))

def bytes_l105100 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x83, 0xEC, 0x38, 0x48, 0x89,
    0xF3, 0x48, 0x89, 0x7C, 0x24, 0x30, 0x48, 0xC7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00, 0x48,
    0xC7, 0x04, 0x24, 0x00, 0x00, 0x00, 0x00, 0x48, 0x89, 0xE7, 0xBE, 0x08, 0x00, 0x00, 0x00, 0xE8,
    0xBC, 0x4E, 0x00, 0x00]

theorem code_l105100 : ∀ x ∈ codeRange 0x105100 bytes_l105100, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5100 52 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105134 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x105134 (movzxR32M16Effect 0x105134 3 0 (.base 3 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 54) (.exec 0x105134 (LoadPre 0x105134 (fun s => AddrMode.addr (.base 3 .none) s (0x105134 + BitVec.ofNat 64 3)) 2) (movzxR32M16Effect 0x105134 3 0 (.base 3 .none)) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.exec 0x105137 (StorePre 0x105137 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x105137 + BitVec.ofNat 64 4)) 2) (xorMREffect 0x105137 4 16 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x10513b (movzxR32M16Effect 0x10513b 4 0 (.base 3 (.d8 0x2))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 57) (.exec 0x10513b (LoadPre 0x10513b (fun s => AddrMode.addr (.base 3 (.d8 0x2)) s (0x10513b + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x10513b 4 0 (.base 3 (.d8 0x2))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 58) (.exec 0x10513f (StorePre 0x10513f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2)) s (0x10513f + BitVec.ofNat 64 5)) 2) (xorMREffect 0x10513f 5 16 0 (.sib 4 none 0 (.d8 0x2))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x105144 (movzxR32M16Effect 0x105144 4 0 (.base 3 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 60) (.exec 0x105144 (LoadPre 0x105144 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x105144 + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x105144 4 0 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 61) (.exec 0x105148 (StorePre 0x105148 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x105148 + BitVec.ofNat 64 5)) 2) (xorMREffect 0x105148 5 16 0 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x10514d (movzxR32M16Effect 0x10514d 4 0 (.base 3 (.d8 0x6))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 63) (.exec 0x10514d (LoadPre 0x10514d (fun s => AddrMode.addr (.base 3 (.d8 0x6)) s (0x10514d + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x10514d 4 0 (.base 3 (.d8 0x6))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 64) (.exec 0x105151 (StorePre 0x105151 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6)) s (0x105151 + BitVec.ofNat 64 5)) 2) (xorMREffect 0x105151 5 16 0 (.sib 4 none 0 (.d8 0x6))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x105156 (movzxR32M16Effect 0x105156 4 0 (.base 3 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 66) (.exec 0x105156 (LoadPre 0x105156 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x105156 + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x105156 4 0 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 67) (.exec 0x10515a (StorePre 0x10515a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10515a + BitVec.ofNat 64 5)) 2) (xorMREffect 0x10515a 5 16 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x10515f (movzxR32M16Effect 0x10515f 4 0 (.base 3 (.d8 0xa))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 69) (.exec 0x10515f (LoadPre 0x10515f (fun s => AddrMode.addr (.base 3 (.d8 0xa)) s (0x10515f + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x10515f 4 0 (.base 3 (.d8 0xa))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.exec 0x105163 (StorePre 0x105163 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xa)) s (0x105163 + BitVec.ofNat 64 5)) 2) (xorMREffect 0x105163 5 16 0 (.sib 4 none 0 (.d8 0xa))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[68, 4]
    (.letOp (n := 71) (.exec 0x105168 (StorePre 0x105168 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x105168 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x105168 3 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[3, 4]
    (.letOp (n := 72) (.out 0x10516d (movzxR32M16Effect 0x10516d 4 0 (.base 3 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 73) (.exec 0x10516d (LoadPre 0x10516d (fun s => AddrMode.addr (.base 3 (.d8 0xc)) s (0x10516d + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x10516d 4 0 (.base 3 (.d8 0xc))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 74) (.exec 0x105171 (StorePre 0x105171 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x105171 + BitVec.ofNat 64 5)) 2) (xorMREffect 0x105171 5 16 0 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[72, 4]
    (.letOp (n := 75) (.out 0x105176 (xorR32R32Effect 0x105176 3 12 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 12] []) (.reg (.gpr 12))) #v[12, 12]
    (.letOp (n := 76) (.exec 0x105176 (fun s => s.RIP = 0x105176) (xorR32R32Effect 0x105176 3 12 12) (Reg.operands [.gpr 12, .gpr 12] [])) #v[12, 12]
    (.letOp (n := 77) (.out 0x105179 (movzxR32M16Effect 0x105179 5 0 (.sib 4 none 0 (.d8 0xe))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 78) (.exec 0x105179 (LoadPre 0x105179 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x105179 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105179 5 0 (.sib 4 none 0 (.d8 0xe))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.exec 0x10517e (fun s => s.RIP = 0x10517e) (fun _ => nopEffect 0x10517e 2) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l105180, RegMap.args [(0, 77), (3, 3), (4, 4), (5, 5), (12, 75), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 80⟩))))))))))))))))))))))))))))

def bytes_l105134 : List UInt8 :=
  [0x0F, 0xB7, 0x03, 0x66, 0x31, 0x04, 0x24, 0x0F, 0xB7, 0x43, 0x02, 0x66, 0x31, 0x44, 0x24, 0x02,
    0x0F, 0xB7, 0x43, 0x04, 0x66, 0x31, 0x44, 0x24, 0x04, 0x0F, 0xB7, 0x43, 0x06, 0x66, 0x31, 0x44,
    0x24, 0x06, 0x0F, 0xB7, 0x43, 0x08, 0x66, 0x31, 0x44, 0x24, 0x08, 0x0F, 0xB7, 0x43, 0x0A, 0x66,
    0x31, 0x44, 0x24, 0x0A, 0x48, 0x89, 0x5C, 0x24, 0x28, 0x0F, 0xB7, 0x43, 0x0C, 0x66, 0x31, 0x44,
    0x24, 0x0C, 0x45, 0x31, 0xE4, 0x0F, 0xB7, 0x44, 0x24, 0x0E, 0x66, 0x90]

theorem code_l105134 : ∀ x ∈ codeRange 0x105134 bytes_l105134, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5134 76 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105180 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x105180 (movR64M64Effect 0x105180 3 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 54) (.exec 0x105180 (LoadPre 0x105180 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x105180 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x105180 3 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x105185 (xorR16M16Effect 0x105185 6 0 (.sib 3 (some 12) 1 (.d8 0xe))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3, .gpr 12] []) (.reg (.gpr 0))) #v[0, 53, 12]
    (.letOp (n := 56) (.exec 0x105185 (LoadPre 0x105185 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0xe)) s (0x105185 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x105185 6 0 (.sib 3 (some 12) 1 (.d8 0xe))) (Reg.operands [.gpr 0, .gpr 3, .gpr 12] [])) #v[0, 53, 12]
    (.letOp (n := 57) (.exec 0x10518b (StorePre 0x10518b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x10518b + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x10518b 5 0 (.sib 4 none 0 (.d8 0xe))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 58) (.out 0x105190 (movR32Imm32Effect 0x105190 5 6 0x8) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 59) (.exec 0x105190 (fun s => s.RIP = 0x105190) (movR32Imm32Effect 0x105190 5 6 0x8) (Reg.operands [] [])) #v[]
    (.letOp (n := 60) (.out 0x105195 (movR64R64Effect 0x105195 14 4) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 61) (.exec 0x105195 (fun s => s.RIP = 0x105195) (movR64R64Effect 0x105195 14 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.out 0x105198 (movR64R64Effect 0x105198 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[60]
    (.letOp (n := 63) (.exec 0x105198 (fun s => s.RIP = 0x105198) (movR64R64Effect 0x105198 7 14) (Reg.operands [.gpr 14] [])) #v[60]
    (.letOp (n := 64) (.out 0x10519b (callEffect (fun _ => 0x100b10) 0x1051a0) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 65) (.exec 0x10519b (PushPre 0x10519b 5) (callEffect (fun _ => 0x100b10) 0x1051a0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.const ⟨64, 0x1051a0⟩) #v[]
    (.terminate (.call ⟨.l100b10, RegMap.args [(0, 55), (3, 53), (4, 64), (5, 5), (6, 58), (7, 62), (12, 12), (13, 13), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩ { target := .l1051a0, kept := #v[], arity := rfl, guard := some (Fin.last 66) })))))))))))))))

def bytes_l105180 : List UInt8 :=
  [0x48, 0x8B, 0x5C, 0x24, 0x28, 0x66, 0x42, 0x33, 0x44, 0x63, 0x0E, 0x66, 0x89, 0x44, 0x24, 0x0E,
    0xBE, 0x08, 0x00, 0x00, 0x00, 0x49, 0x89, 0xE6, 0x4C, 0x89, 0xF7, 0xE8, 0x70, 0xB9, 0xFF, 0xFF]

theorem code_l105180 : ∀ x ∈ codeRange 0x105180 bytes_l105180, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5180 32 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1051a0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1051a0 (movR64R64Effect 0x1051a0 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 54) (.exec 0x1051a0 (fun s => s.RIP = 0x1051a0) (movR64R64Effect 0x1051a0 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 55) (.out 0x1051a3 (callEffect (fun _ => 0x100000) 0x1051a8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 56) (.exec 0x1051a3 (PushPre 0x1051a3 5) (callEffect (fun _ => 0x100000) 0x1051a8) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.const ⟨64, 0x1051a8⟩) #v[]
    (.terminate (.call ⟨.l100000, RegMap.args [(3, 3), (4, 55), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ { target := .l1051a8, kept := #v[], arity := rfl, guard := some (Fin.last 57) }))))))

def bytes_l1051a0 : List UInt8 :=
  [0x4C, 0x89, 0xF7, 0xE8, 0x58, 0xAE, 0xFF, 0xFF]

theorem code_l1051a0 : ∀ x ∈ codeRange 0x1051a0 bytes_l1051a0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x51a0 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1051a8_1 : Block Op Label signature Reg.count 87 :=
  .letOp (n := 87) (.exec 0x105217 (StorePre 0x105217 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x105217 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105217 5 1 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[85, 4]
    (.letOp (n := 88) (.out 0x10521c (movzxR32M16Effect 0x10521c 5 0 (.sib 4 none 0 (.d8 0xe))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 89) (.exec 0x10521c (LoadPre 0x10521c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x10521c + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x10521c 5 0 (.sib 4 none 0 (.d8 0xe))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 90) (.out 0x105221 (xorR16M16Effect 0x105221 6 0 (.sib 3 (some 12) 1 (.d8 0x1e))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3, .gpr 12] []) (.reg (.gpr 0))) #v[88, 3, 12]
    (.letOp (n := 91) (.exec 0x105221 (LoadPre 0x105221 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x1e)) s (0x105221 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x105221 6 0 (.sib 3 (some 12) 1 (.d8 0x1e))) (Reg.operands [.gpr 0, .gpr 3, .gpr 12] [])) #v[88, 3, 12]
    (.letOp (n := 92) (.exec 0x105227 (StorePre 0x105227 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x105227 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105227 5 0 (.sib 4 none 0 (.d8 0xe))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[90, 4]
    (.letOp (n := 93) (.out 0x10522c (cmpR64Imm8Effect 0x10522c 12 0x40) (EffectPart.reads (.flag .ZF) [.gpr 12] []) (.flag .ZF)) #v[12]
    (.letOp (n := 94) (.exec 0x10522c (fun s => s.RIP = 0x10522c) (cmpR64Imm8Effect 0x10522c 12 0x40) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 95) (.pure (condOp 4)) #v[93]
    (.terminate (.condBr (Fin.last 95) ⟨.l105636, RegMap.args [(0, 90), (1, 85), (2, 80), (3, 3), (4, 4), (5, 5), (6, 75), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (19, 93), (22, 22), (39, 39), (50, 50), (51, 51)] 96⟩ ⟨.l105236, RegMap.args [(0, 90), (1, 85), (2, 80), (3, 3), (4, 4), (5, 5), (6, 75), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (19, 93), (22, 22), (39, 39), (50, 50), (51, 51)] 96⟩))))))))))

def bytes_l1051a8_1 : List UInt8 :=
  [0x66, 0x89, 0x4C, 0x24, 0x0C, 0x0F, 0xB7, 0x44, 0x24, 0x0E, 0x66, 0x42, 0x33, 0x44, 0x63, 0x1E,
    0x66, 0x89, 0x44, 0x24, 0x0E, 0x49, 0x83, 0xFC, 0x40, 0x0F, 0x84, 0x00, 0x04, 0x00, 0x00]

theorem code_l1051a8_1 : ∀ x ∈ codeRange 0x105217 bytes_l1051a8_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5217 31 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1051a8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1051a8 (movzxR32M16Effect 0x1051a8 5 10 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 54) (.exec 0x1051a8 (LoadPre 0x1051a8 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1051a8 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x1051a8 5 10 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1051ad (movzxR32M16Effect 0x1051ad 6 9 (.sib 4 none 0 (.d8 0x2))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 56) (.exec 0x1051ad (LoadPre 0x1051ad (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2)) s (0x1051ad + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x1051ad 6 9 (.sib 4 none 0 (.d8 0x2))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1051b3 (xorR16M16Effect 0x1051b3 6 10 (.sib 3 (some 12) 1 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 3, .gpr 12] []) (.reg (.gpr 10))) #v[53, 3, 12]
    (.letOp (n := 58) (.exec 0x1051b3 (LoadPre 0x1051b3 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x10)) s (0x1051b3 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x1051b3 6 10 (.sib 3 (some 12) 1 (.d8 0x10))) (Reg.operands [.gpr 10, .gpr 3, .gpr 12] [])) #v[53, 3, 12]
    (.letOp (n := 59) (.exec 0x1051b9 (StorePre 0x1051b9 5 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1051b9 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1051b9 5 10 (.sib 4 none 0 .none)) (Reg.operands [.gpr 10, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 60) (.out 0x1051be (xorR16M16Effect 0x1051be 6 9 (.sib 3 (some 12) 1 (.d8 0x12))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 3, .gpr 12] []) (.reg (.gpr 9))) #v[55, 3, 12]
    (.letOp (n := 61) (.exec 0x1051be (LoadPre 0x1051be (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x12)) s (0x1051be + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x1051be 6 9 (.sib 3 (some 12) 1 (.d8 0x12))) (Reg.operands [.gpr 9, .gpr 3, .gpr 12] [])) #v[55, 3, 12]
    (.letOp (n := 62) (.exec 0x1051c4 (StorePre 0x1051c4 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2)) s (0x1051c4 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x1051c4 6 9 (.sib 4 none 0 (.d8 0x2))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[60, 4]
    (.letOp (n := 63) (.out 0x1051ca (movzxR32M16Effect 0x1051ca 6 8 (.sib 4 none 0 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 64) (.exec 0x1051ca (LoadPre 0x1051ca (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x1051ca + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x1051ca 6 8 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x1051d0 (xorR16M16Effect 0x1051d0 6 8 (.sib 3 (some 12) 1 (.d8 0x14))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 3, .gpr 12] []) (.reg (.gpr 8))) #v[63, 3, 12]
    (.letOp (n := 66) (.exec 0x1051d0 (LoadPre 0x1051d0 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x14)) s (0x1051d0 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x1051d0 6 8 (.sib 3 (some 12) 1 (.d8 0x14))) (Reg.operands [.gpr 8, .gpr 3, .gpr 12] [])) #v[63, 3, 12]
    (.letOp (n := 67) (.exec 0x1051d6 (StorePre 0x1051d6 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x1051d6 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x1051d6 6 8 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x1051dc (movzxR32M16Effect 0x1051dc 5 7 (.sib 4 none 0 (.d8 0x6))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 69) (.exec 0x1051dc (LoadPre 0x1051dc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6)) s (0x1051dc + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x1051dc 5 7 (.sib 4 none 0 (.d8 0x6))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.out 0x1051e1 (xorR16M16Effect 0x1051e1 6 7 (.sib 3 (some 12) 1 (.d8 0x16))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 3, .gpr 12] []) (.reg (.gpr 7))) #v[68, 3, 12]
    (.letOp (n := 71) (.exec 0x1051e1 (LoadPre 0x1051e1 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x16)) s (0x1051e1 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x1051e1 6 7 (.sib 3 (some 12) 1 (.d8 0x16))) (Reg.operands [.gpr 7, .gpr 3, .gpr 12] [])) #v[68, 3, 12]
    (.letOp (n := 72) (.exec 0x1051e7 (StorePre 0x1051e7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6)) s (0x1051e7 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1051e7 5 7 (.sib 4 none 0 (.d8 0x6))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[70, 4]
    (.letOp (n := 73) (.out 0x1051ec (movzxR32M16Effect 0x1051ec 5 6 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 74) (.exec 0x1051ec (LoadPre 0x1051ec (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1051ec + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x1051ec 5 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.out 0x1051f1 (xorR16M16Effect 0x1051f1 6 6 (.sib 3 (some 12) 1 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 3, .gpr 12] []) (.reg (.gpr 6))) #v[73, 3, 12]
    (.letOp (n := 76) (.exec 0x1051f1 (LoadPre 0x1051f1 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x18)) s (0x1051f1 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x1051f1 6 6 (.sib 3 (some 12) 1 (.d8 0x18))) (Reg.operands [.gpr 6, .gpr 3, .gpr 12] [])) #v[73, 3, 12]
    (.letOp (n := 77) (.exec 0x1051f7 (StorePre 0x1051f7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1051f7 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1051f7 5 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[75, 4]
    (.letOp (n := 78) (.out 0x1051fc (movzxR32M16Effect 0x1051fc 5 2 (.sib 4 none 0 (.d8 0xa))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 79) (.exec 0x1051fc (LoadPre 0x1051fc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xa)) s (0x1051fc + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x1051fc 5 2 (.sib 4 none 0 (.d8 0xa))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 80) (.out 0x105201 (xorR16M16Effect 0x105201 6 2 (.sib 3 (some 12) 1 (.d8 0x1a))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 3, .gpr 12] []) (.reg (.gpr 2))) #v[78, 3, 12]
    (.letOp (n := 81) (.exec 0x105201 (LoadPre 0x105201 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x1a)) s (0x105201 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x105201 6 2 (.sib 3 (some 12) 1 (.d8 0x1a))) (Reg.operands [.gpr 2, .gpr 3, .gpr 12] [])) #v[78, 3, 12]
    (.letOp (n := 82) (.exec 0x105207 (StorePre 0x105207 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xa)) s (0x105207 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105207 5 2 (.sib 4 none 0 (.d8 0xa))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[80, 4]
    (.letOp (n := 83) (.out 0x10520c (movzxR32M16Effect 0x10520c 5 1 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 84) (.exec 0x10520c (LoadPre 0x10520c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x10520c + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x10520c 5 1 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 85) (.out 0x105211 (xorR16M16Effect 0x105211 6 1 (.sib 3 (some 12) 1 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 3, .gpr 12] []) (.reg (.gpr 1))) #v[83, 3, 12]
    (.letOp (n := 86) (.exec 0x105211 (LoadPre 0x105211 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x1c)) s (0x105211 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x105211 6 1 (.sib 3 (some 12) 1 (.d8 0x1c))) (Reg.operands [.gpr 1, .gpr 3, .gpr 12] [])) #v[83, 3, 12]
    (b_l1051a8_1))))))))))))))))))))))))))))))))))

def bytes_l1051a8 : List UInt8 :=
  [0x44, 0x0F, 0xB7, 0x14, 0x24, 0x44, 0x0F, 0xB7, 0x4C, 0x24, 0x02, 0x66, 0x46, 0x33, 0x54, 0x63,
    0x10, 0x66, 0x44, 0x89, 0x14, 0x24, 0x66, 0x46, 0x33, 0x4C, 0x63, 0x12, 0x66, 0x44, 0x89, 0x4C,
    0x24, 0x02, 0x44, 0x0F, 0xB7, 0x44, 0x24, 0x04, 0x66, 0x46, 0x33, 0x44, 0x63, 0x14, 0x66, 0x44,
    0x89, 0x44, 0x24, 0x04, 0x0F, 0xB7, 0x7C, 0x24, 0x06, 0x66, 0x42, 0x33, 0x7C, 0x63, 0x16, 0x66,
    0x89, 0x7C, 0x24, 0x06, 0x0F, 0xB7, 0x74, 0x24, 0x08, 0x66, 0x42, 0x33, 0x74, 0x63, 0x18, 0x66,
    0x89, 0x74, 0x24, 0x08, 0x0F, 0xB7, 0x54, 0x24, 0x0A, 0x66, 0x42, 0x33, 0x54, 0x63, 0x1A, 0x66,
    0x89, 0x54, 0x24, 0x0A, 0x0F, 0xB7, 0x4C, 0x24, 0x0C, 0x66, 0x42, 0x33, 0x4C, 0x63, 0x1C] ++ bytes_l1051a8_1

theorem code_l1051a8 : ∀ x ∈ codeRange 0x1051a8 bytes_l1051a8, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x51a8 111 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1051a8_1

@[cfg_block] def b_l105236 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x105236 (movR32Imm32Effect 0x105236 5 6 0x8) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 54) (.exec 0x105236 (fun s => s.RIP = 0x105236) (movR32Imm32Effect 0x105236 5 6 0x8) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x10523b (movR64R64Effect 0x10523b 7 4) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 56) (.exec 0x10523b (fun s => s.RIP = 0x10523b) (movR64R64Effect 0x10523b 7 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x10523e (callEffect (fun _ => 0x100b10) 0x105243) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x10523e (PushPre 0x10523e 5) (callEffect (fun _ => 0x100b10) 0x105243) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x105243⟩) #v[]
    (.terminate (.call ⟨.l100b10, RegMap.args [(3, 3), (4, 57), (5, 5), (6, 53), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ { target := .l105243, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l105236 : List UInt8 :=
  [0xBE, 0x08, 0x00, 0x00, 0x00, 0x48, 0x89, 0xE7, 0xE8, 0xCD, 0xB8, 0xFF, 0xFF]

theorem code_l105236 : ∀ x ∈ codeRange 0x105236 bytes_l105236, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5236 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105243_6 : Block Op Label signature Reg.count 283 :=
  .letOp (n := 283) (.out 0x105426 (movR32M32LowEffect 0x105426 2 (.sib 4 none 0 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 284) (.exec 0x105426 (LoadPre 0x105426 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x105426 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x105426 2 (.sib 4 none 0 (.d8 0x1c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 285) (.out 0x10542a (xorR32R32Effect 0x10542a 3 2 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 11] []) (.reg (.gpr 2))) #v[283, 165]
    (.letOp (n := 286) (.exec 0x10542a (fun s => s.RIP = 0x10542a) (xorR32R32Effect 0x10542a 3 2 11) (Reg.operands [.gpr 2, .gpr 11] [])) #v[283, 165]
    (.letOp (n := 287) (.out 0x10542d (xorR32R32Effect 0x10542d 3 6 11) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 11] []) (.reg (.gpr 6))) #v[270, 165]
    (.letOp (n := 288) (.exec 0x10542d (fun s => s.RIP = 0x10542d) (xorR32R32Effect 0x10542d 3 6 11) (Reg.operands [.gpr 6, .gpr 11] [])) #v[270, 165]
    (.letOp (n := 289) (.out 0x105430 (movR32R32Effect 0x105430 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[285]
    (.letOp (n := 290) (.exec 0x105430 (fun s => s.RIP = 0x105430) (movR32R32Effect 0x105430 2 1 2) (Reg.operands [.gpr 2] [])) #v[285]
    (.letOp (n := 291) (.out 0x105432 (rolR16Effect 0x105432 4 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[289]
    (.letOp (n := 292) (.exec 0x105432 (fun s => s.RIP = 0x105432) (rolR16Effect 0x105432 4 1 8) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[289]
    (.letOp (n := 293) (.out 0x105436 (xorR16M16Effect 0x105436 6 1 (.sib 3 (some 12) 1 (.d8 0x2c))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 3, .gpr 12] []) (.reg (.gpr 1))) #v[291, 191, 12]
    (.letOp (n := 294) (.exec 0x105436 (LoadPre 0x105436 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x2c)) s (0x105436 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x105436 6 1 (.sib 3 (some 12) 1 (.d8 0x2c))) (Reg.operands [.gpr 1, .gpr 3, .gpr 12] [])) #v[291, 191, 12]
    (.letOp (n := 295) (.out 0x10543c (xorR32R32Effect 0x10543c 2 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[287, 293]
    (.letOp (n := 296) (.exec 0x10543c (fun s => s.RIP = 0x10543c) (xorR32R32Effect 0x10543c 2 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[287, 293]
    (.letOp (n := 297) (.exec 0x10543e (StorePre 0x10543e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x10543e + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x10543e 5 6 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[295, 4]
    (.letOp (n := 298) (.out 0x105443 (movR32R32Effect 0x105443 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[285]
    (.letOp (n := 299) (.exec 0x105443 (fun s => s.RIP = 0x105443) (movR32R32Effect 0x105443 2 1 2) (Reg.operands [.gpr 2] [])) #v[285]
    (.letOp (n := 300) (.out 0x105445 (xorR32R32Effect 0x105445 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[298, 181]
    (.letOp (n := 301) (.exec 0x105445 (fun s => s.RIP = 0x105445) (xorR32R32Effect 0x105445 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[298, 181]
    (.letOp (n := 302) (.out 0x105447 (rolR16Effect 0x105447 5 14 8) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[185]
    (.letOp (n := 303) (.exec 0x105447 (fun s => s.RIP = 0x105447) (rolR16Effect 0x105447 5 14 8) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[185]
    (.letOp (n := 304) (.out 0x10544c (xorR16M16Effect 0x10544c 6 14 (.sib 3 (some 12) 1 (.d8 0x2e))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 3, .gpr 12] []) (.reg (.gpr 14))) #v[302, 191, 12]
    (.letOp (n := 305) (.exec 0x10544c (LoadPre 0x10544c (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x2e)) s (0x10544c + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x10544c 6 14 (.sib 3 (some 12) 1 (.d8 0x2e))) (Reg.operands [.gpr 14, .gpr 3, .gpr 12] [])) #v[302, 191, 12]
    (.letOp (n := 306) (.out 0x105452 (xorR32R32Effect 0x105452 3 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 14] []) (.reg (.gpr 1))) #v[300, 304]
    (.letOp (n := 307) (.exec 0x105452 (fun s => s.RIP = 0x105452) (xorR32R32Effect 0x105452 3 1 14) (Reg.operands [.gpr 1, .gpr 14] [])) #v[300, 304]
    (.letOp (n := 308) (.exec 0x105455 (StorePre 0x105455 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x105455 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105455 5 1 (.sib 4 none 0 (.d8 0xe))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[306, 4]
    (.letOp (n := 309) (.out 0x10545a (movR32Imm32Effect 0x10545a 5 6 0x8) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 310) (.exec 0x10545a (fun s => s.RIP = 0x10545a) (movR32Imm32Effect 0x10545a 5 6 0x8) (Reg.operands [] [])) #v[]
    (.letOp (n := 311) (.out 0x10545f (movR64R64Effect 0x10545f 14 4) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 312) (.exec 0x10545f (fun s => s.RIP = 0x10545f) (movR64R64Effect 0x10545f 14 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 313) (.out 0x105462 (movR64R64Effect 0x105462 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[311]
    (.letOp (n := 314) (.exec 0x105462 (fun s => s.RIP = 0x105462) (movR64R64Effect 0x105462 7 14) (Reg.operands [.gpr 14] [])) #v[311]
    (.letOp (n := 315) (.out 0x105465 (callEffect (fun _ => 0x100b10) 0x10546a) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 316) (.exec 0x105465 (PushPre 0x105465 5) (callEffect (fun _ => 0x100b10) 0x10546a) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 317) (.const ⟨64, 0x10546a⟩) #v[]
    (.terminate (.call ⟨.l100b10, RegMap.args [(0, 181), (1, 306), (2, 285), (3, 191), (4, 315), (5, 197), (6, 309), (7, 313), (8, 263), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 311), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)] 318⟩ { target := .l10546a, kept := #v[], arity := rfl, guard := some (Fin.last 317) }))))))))))))))))))))))))))))))))))))

def bytes_l105243_6 : List UInt8 :=
  [0x8B, 0x54, 0x24, 0x1C, 0x44, 0x31, 0xDA, 0x44, 0x31, 0xDE, 0x89, 0xD1, 0x66, 0xC1, 0xC1, 0x08,
    0x66, 0x42, 0x33, 0x4C, 0x63, 0x2C, 0x31, 0xCE, 0x66, 0x89, 0x74, 0x24, 0x0C, 0x89, 0xD1, 0x31,
    0xC1, 0x66, 0x41, 0xC1, 0xC6, 0x08, 0x66, 0x46, 0x33, 0x74, 0x63, 0x2E, 0x44, 0x31, 0xF1, 0x66,
    0x89, 0x4C, 0x24, 0x0E, 0xBE, 0x08, 0x00, 0x00, 0x00, 0x49, 0x89, 0xE6, 0x4C, 0x89, 0xF7, 0xE8,
    0xA6, 0xB6, 0xFF, 0xFF]

theorem code_l105243_6 : ∀ x ∈ codeRange 0x105426 bytes_l105243_6, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5426 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105243_5 : Block Op Label signature Reg.count 246 :=
  .letOp (n := 246) (.exec 0x1053de (StorePre 0x1053de 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6)) s (0x1053de + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1053de 5 7 (.sib 4 none 0 (.d8 0x6))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[240, 4]
    (.letOp (n := 247) (.out 0x1053e3 (movR32R32Effect 0x1053e3 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[244]
    (.letOp (n := 248) (.exec 0x1053e3 (fun s => s.RIP = 0x1053e3) (movR32R32Effect 0x1053e3 2 2 1) (Reg.operands [.gpr 1] [])) #v[244]
    (.letOp (n := 249) (.out 0x1053e5 (movR32R32Effect 0x1053e5 2 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 1] []) (.reg (.gpr 7))) #v[244]
    (.letOp (n := 250) (.exec 0x1053e5 (fun s => s.RIP = 0x1053e5) (movR32R32Effect 0x1053e5 2 7 1) (Reg.operands [.gpr 1] [])) #v[244]
    (.letOp (n := 251) (.out 0x1053e7 (rolR16Effect 0x1053e7 4 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[247]
    (.letOp (n := 252) (.exec 0x1053e7 (fun s => s.RIP = 0x1053e7) (rolR16Effect 0x1053e7 4 2 8) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[247]
    (.letOp (n := 253) (.out 0x1053eb (xorR32R32Effect 0x1053eb 3 15 13) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 13] []) (.reg (.gpr 15))) #v[227, 134]
    (.letOp (n := 254) (.exec 0x1053eb (fun s => s.RIP = 0x1053eb) (xorR32R32Effect 0x1053eb 3 15 13) (Reg.operands [.gpr 15, .gpr 13] [])) #v[227, 134]
    (.letOp (n := 255) (.out 0x1053ee (xorR16M16Effect 0x1053ee 6 2 (.sib 3 (some 12) 1 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 3, .gpr 12] []) (.reg (.gpr 2))) #v[251, 191, 12]
    (.letOp (n := 256) (.exec 0x1053ee (LoadPre 0x1053ee (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x28)) s (0x1053ee + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x1053ee 6 2 (.sib 3 (some 12) 1 (.d8 0x28))) (Reg.operands [.gpr 2, .gpr 3, .gpr 12] [])) #v[251, 191, 12]
    (.letOp (n := 257) (.out 0x1053f4 (xorR32R32Effect 0x1053f4 3 15 14) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 14] []) (.reg (.gpr 15))) #v[253, 185]
    (.letOp (n := 258) (.exec 0x1053f4 (fun s => s.RIP = 0x1053f4) (xorR32R32Effect 0x1053f4 3 15 14) (Reg.operands [.gpr 15, .gpr 14] [])) #v[253, 185]
    (.letOp (n := 259) (.out 0x1053f7 (xorR32R32Effect 0x1053f7 3 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 2] []) (.reg (.gpr 15))) #v[257, 255]
    (.letOp (n := 260) (.exec 0x1053f7 (fun s => s.RIP = 0x1053f7) (xorR32R32Effect 0x1053f7 3 15 2) (Reg.operands [.gpr 15, .gpr 2] [])) #v[257, 255]
    (.letOp (n := 261) (.out 0x1053fa (movR32M32LowEffect 0x1053fa 1 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 262) (.exec 0x1053fa (LoadPre 0x1053fa (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1053fa + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1053fa 1 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 263) (.out 0x1053fe (movR32M32Effect 0x1053fe 8 (.sib 4 none 0 (.d8 0x14))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 264) (.exec 0x1053fe (LoadPre 0x1053fe (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x1053fe + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x1053fe 8 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 265) (.out 0x105403 (xorR32R32Effect 0x105403 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8] []) (.reg (.gpr 1))) #v[261, 263]
    (.letOp (n := 266) (.exec 0x105403 (fun s => s.RIP = 0x105403) (xorR32R32Effect 0x105403 3 1 8) (Reg.operands [.gpr 1, .gpr 8] [])) #v[261, 263]
    (.letOp (n := 267) (.exec 0x105406 (StorePre 0x105406 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x105406 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x105406 6 15 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[259, 4]
    (.letOp (n := 268) (.out 0x10540c (movR32R32Effect 0x10540c 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[265]
    (.letOp (n := 269) (.exec 0x10540c (fun s => s.RIP = 0x10540c) (movR32R32Effect 0x10540c 2 2 1) (Reg.operands [.gpr 1] [])) #v[265]
    (.letOp (n := 270) (.out 0x10540e (movR32R32Effect 0x10540e 2 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 1] []) (.reg (.gpr 6))) #v[265]
    (.letOp (n := 271) (.exec 0x10540e (fun s => s.RIP = 0x10540e) (movR32R32Effect 0x10540e 2 6 1) (Reg.operands [.gpr 1] [])) #v[265]
    (.letOp (n := 272) (.out 0x105410 (rolR16Effect 0x105410 4 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[268]
    (.letOp (n := 273) (.exec 0x105410 (fun s => s.RIP = 0x105410) (rolR16Effect 0x105410 4 2 8) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[268]
    (.letOp (n := 274) (.out 0x105414 (xorR16M16Effect 0x105414 6 2 (.sib 3 (some 12) 1 (.d8 0x2a))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 3, .gpr 12] []) (.reg (.gpr 2))) #v[272, 191, 12]
    (.letOp (n := 275) (.exec 0x105414 (LoadPre 0x105414 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x2a)) s (0x105414 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x105414 6 2 (.sib 3 (some 12) 1 (.d8 0x2a))) (Reg.operands [.gpr 2, .gpr 3, .gpr 12] [])) #v[272, 191, 12]
    (.letOp (n := 276) (.out 0x10541a (movR32R32Effect 0x10541a 2 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 7] []) (.reg (.gpr 1))) #v[249]
    (.letOp (n := 277) (.exec 0x10541a (fun s => s.RIP = 0x10541a) (movR32R32Effect 0x10541a 2 1 7) (Reg.operands [.gpr 7] [])) #v[249]
    (.letOp (n := 278) (.out 0x10541c (xorR32R32Effect 0x10541c 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8] []) (.reg (.gpr 1))) #v[276, 263]
    (.letOp (n := 279) (.exec 0x10541c (fun s => s.RIP = 0x10541c) (xorR32R32Effect 0x10541c 3 1 8) (Reg.operands [.gpr 1, .gpr 8] [])) #v[276, 263]
    (.letOp (n := 280) (.out 0x10541f (xorR32R32Effect 0x10541f 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[278, 274]
    (.letOp (n := 281) (.exec 0x10541f (fun s => s.RIP = 0x10541f) (xorR32R32Effect 0x10541f 2 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[278, 274]
    (.letOp (n := 282) (.exec 0x105421 (StorePre 0x105421 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xa)) s (0x105421 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105421 5 1 (.sib 4 none 0 (.d8 0xa))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[280, 4]
    (b_l105243_6)))))))))))))))))))))))))))))))))))))

def bytes_l105243_5 : List UInt8 :=
  [0x66, 0x89, 0x7C, 0x24, 0x06, 0x89, 0xCA, 0x89, 0xCF, 0x66, 0xC1, 0xC2, 0x08, 0x45, 0x31, 0xEF,
    0x66, 0x42, 0x33, 0x54, 0x63, 0x28, 0x45, 0x31, 0xF7, 0x41, 0x31, 0xD7, 0x8B, 0x4C, 0x24, 0x18,
    0x44, 0x8B, 0x44, 0x24, 0x14, 0x44, 0x31, 0xC1, 0x66, 0x44, 0x89, 0x7C, 0x24, 0x08, 0x89, 0xCA,
    0x89, 0xCE, 0x66, 0xC1, 0xC2, 0x08, 0x66, 0x42, 0x33, 0x54, 0x63, 0x2A, 0x89, 0xF9, 0x44, 0x31,
    0xC1, 0x31, 0xD1, 0x66, 0x89, 0x4C, 0x24, 0x0A] ++ bytes_l105243_6

theorem code_l105243_5 : ∀ x ∈ codeRange 0x1053de bytes_l105243_5, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x53de 72 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l105243_6

@[cfg_block] def b_l105243_4 : Block Op Label signature Reg.count 208 :=
  .letOp (n := 208) (.out 0x105394 (xorR16M16Effect 0x105394 6 8 (.sib 3 (some 12) 1 (.d8 0x22))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 3, .gpr 12] []) (.reg (.gpr 8))) #v[206, 191, 12]
    (.letOp (n := 209) (.exec 0x105394 (LoadPre 0x105394 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x22)) s (0x105394 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x105394 6 8 (.sib 3 (some 12) 1 (.d8 0x22))) (Reg.operands [.gpr 8, .gpr 3, .gpr 12] [])) #v[206, 191, 12]
    (.letOp (n := 210) (.out 0x10539a (xorR32R32Effect 0x10539a 3 9 14) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 14] []) (.reg (.gpr 9))) #v[202, 185]
    (.letOp (n := 211) (.exec 0x10539a (fun s => s.RIP = 0x10539a) (xorR32R32Effect 0x10539a 3 9 14) (Reg.operands [.gpr 9, .gpr 14] [])) #v[202, 185]
    (.letOp (n := 212) (.out 0x10539d (xorR32R32Effect 0x10539d 3 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8] []) (.reg (.gpr 9))) #v[210, 208]
    (.letOp (n := 213) (.exec 0x10539d (fun s => s.RIP = 0x10539d) (xorR32R32Effect 0x10539d 3 9 8) (Reg.operands [.gpr 9, .gpr 8] [])) #v[210, 208]
    (.letOp (n := 214) (.exec 0x1053a0 (StorePre 0x1053a0 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2)) s (0x1053a0 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x1053a0 6 9 (.sib 4 none 0 (.d8 0x2))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[212, 4]
    (.letOp (n := 215) (.out 0x1053a6 (xorR32R32Effect 0x1053a6 2 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1] []) (.reg (.gpr 7))) #v[55, 107]
    (.letOp (n := 216) (.exec 0x1053a6 (fun s => s.RIP = 0x1053a6) (xorR32R32Effect 0x1053a6 2 7 1) (Reg.operands [.gpr 7, .gpr 1] [])) #v[55, 107]
    (.letOp (n := 217) (.out 0x1053a8 (xorR32R32Effect 0x1053a8 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[200, 107]
    (.letOp (n := 218) (.exec 0x1053a8 (fun s => s.RIP = 0x1053a8) (xorR32R32Effect 0x1053a8 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[200, 107]
    (.letOp (n := 219) (.out 0x1053aa (movR32R32Effect 0x1053aa 3 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 7] []) (.reg (.gpr 8))) #v[215]
    (.letOp (n := 220) (.exec 0x1053aa (fun s => s.RIP = 0x1053aa) (movR32R32Effect 0x1053aa 3 8 7) (Reg.operands [.gpr 7] [])) #v[215]
    (.letOp (n := 221) (.out 0x1053ad (rolR16Effect 0x1053ad 5 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[219]
    (.letOp (n := 222) (.exec 0x1053ad (fun s => s.RIP = 0x1053ad) (rolR16Effect 0x1053ad 5 8 8) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[219]
    (.letOp (n := 223) (.out 0x1053b2 (xorR16M16Effect 0x1053b2 6 8 (.sib 3 (some 12) 1 (.d8 0x24))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 3, .gpr 12] []) (.reg (.gpr 8))) #v[221, 191, 12]
    (.letOp (n := 224) (.exec 0x1053b2 (LoadPre 0x1053b2 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x24)) s (0x1053b2 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x1053b2 6 8 (.sib 3 (some 12) 1 (.d8 0x24))) (Reg.operands [.gpr 8, .gpr 3, .gpr 12] [])) #v[221, 191, 12]
    (.letOp (n := 225) (.out 0x1053b8 (xorR32R32Effect 0x1053b8 3 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 8] []) (.reg (.gpr 2))) #v[217, 223]
    (.letOp (n := 226) (.exec 0x1053b8 (fun s => s.RIP = 0x1053b8) (xorR32R32Effect 0x1053b8 3 2 8) (Reg.operands [.gpr 2, .gpr 8] [])) #v[217, 223]
    (.letOp (n := 227) (.out 0x1053bb (xorR32R32Effect 0x1053bb 3 15 6) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 6] []) (.reg (.gpr 15))) #v[59, 121]
    (.letOp (n := 228) (.exec 0x1053bb (fun s => s.RIP = 0x1053bb) (xorR32R32Effect 0x1053bb 3 15 6) (Reg.operands [.gpr 15, .gpr 6] [])) #v[59, 121]
    (.letOp (n := 229) (.exec 0x1053be (StorePre 0x1053be 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x1053be + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1053be 5 2 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[225, 4]
    (.letOp (n := 230) (.out 0x1053c3 (movR32R32Effect 0x1053c3 3 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15] []) (.reg (.gpr 2))) #v[227]
    (.letOp (n := 231) (.exec 0x1053c3 (fun s => s.RIP = 0x1053c3) (movR32R32Effect 0x1053c3 3 2 15) (Reg.operands [.gpr 15] [])) #v[227]
    (.letOp (n := 232) (.out 0x1053c6 (rolR16Effect 0x1053c6 4 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[230]
    (.letOp (n := 233) (.exec 0x1053c6 (fun s => s.RIP = 0x1053c6) (rolR16Effect 0x1053c6 4 2 8) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[230]
    (.letOp (n := 234) (.out 0x1053ca (xorR16M16Effect 0x1053ca 6 2 (.sib 3 (some 12) 1 (.d8 0x26))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 3, .gpr 12] []) (.reg (.gpr 2))) #v[232, 191, 12]
    (.letOp (n := 235) (.exec 0x1053ca (LoadPre 0x1053ca (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x26)) s (0x1053ca + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x1053ca 6 2 (.sib 3 (some 12) 1 (.d8 0x26))) (Reg.operands [.gpr 2, .gpr 3, .gpr 12] [])) #v[232, 191, 12]
    (.letOp (n := 236) (.out 0x1053d0 (xorR32R32Effect 0x1053d0 2 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[215, 121]
    (.letOp (n := 237) (.exec 0x1053d0 (fun s => s.RIP = 0x1053d0) (xorR32R32Effect 0x1053d0 2 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[215, 121]
    (.letOp (n := 238) (.out 0x1053d2 (xorR32R32Effect 0x1053d2 3 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 14] []) (.reg (.gpr 7))) #v[236, 185]
    (.letOp (n := 239) (.exec 0x1053d2 (fun s => s.RIP = 0x1053d2) (xorR32R32Effect 0x1053d2 3 7 14) (Reg.operands [.gpr 7, .gpr 14] [])) #v[236, 185]
    (.letOp (n := 240) (.out 0x1053d5 (xorR32R32Effect 0x1053d5 2 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2] []) (.reg (.gpr 7))) #v[238, 234]
    (.letOp (n := 241) (.exec 0x1053d5 (fun s => s.RIP = 0x1053d5) (xorR32R32Effect 0x1053d5 2 7 2) (Reg.operands [.gpr 7, .gpr 2] [])) #v[238, 234]
    (.letOp (n := 242) (.out 0x1053d7 (movR32M32LowEffect 0x1053d7 1 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 243) (.exec 0x1053d7 (LoadPre 0x1053d7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1053d7 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1053d7 1 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 244) (.out 0x1053db (xorR32R32Effect 0x1053db 3 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 13] []) (.reg (.gpr 1))) #v[242, 134]
    (.letOp (n := 245) (.exec 0x1053db (fun s => s.RIP = 0x1053db) (xorR32R32Effect 0x1053db 3 1 13) (Reg.operands [.gpr 1, .gpr 13] [])) #v[242, 134]
    (b_l105243_5))))))))))))))))))))))))))))))))))))))

def bytes_l105243_4 : List UInt8 :=
  [0x66, 0x46, 0x33, 0x44, 0x63, 0x22, 0x45, 0x31, 0xF1, 0x45, 0x31, 0xC1, 0x66, 0x44, 0x89, 0x4C,
    0x24, 0x02, 0x31, 0xCF, 0x31, 0xCA, 0x41, 0x89, 0xF8, 0x66, 0x41, 0xC1, 0xC0, 0x08, 0x66, 0x46,
    0x33, 0x44, 0x63, 0x24, 0x44, 0x31, 0xC2, 0x41, 0x31, 0xF7, 0x66, 0x89, 0x54, 0x24, 0x04, 0x44,
    0x89, 0xFA, 0x66, 0xC1, 0xC2, 0x08, 0x66, 0x42, 0x33, 0x54, 0x63, 0x26, 0x31, 0xF7, 0x44, 0x31,
    0xF7, 0x31, 0xD7, 0x8B, 0x4C, 0x24, 0x20, 0x44, 0x31, 0xE9] ++ bytes_l105243_5

theorem code_l105243_4 : ∀ x ∈ codeRange 0x105394 bytes_l105243_4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x5394 74 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l105243_5

@[cfg_block] def b_l105243_3 : Block Op Label signature Reg.count 169 :=
  .letOp (n := 169) (.out 0x105345 (movR32R32Effect 0x105345 3 10 14) (EffectPart.reads (.reg (.gpr 10)) [.gpr 14] []) (.reg (.gpr 10))) #v[167]
    (.letOp (n := 170) (.exec 0x105345 (fun s => s.RIP = 0x105345) (movR32R32Effect 0x105345 3 10 14) (Reg.operands [.gpr 14] [])) #v[167]
    (.letOp (n := 171) (.out 0x105348 (rolR16Effect 0x105348 5 10 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[169]
    (.letOp (n := 172) (.exec 0x105348 (fun s => s.RIP = 0x105348) (rolR16Effect 0x105348 5 10 10) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[169]
    (.letOp (n := 173) (.out 0x10534d (andR32Imm32Effect 0x10534d 7 10 0x3333) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[171]
    (.letOp (n := 174) (.exec 0x10534d (fun s => s.RIP = 0x10534d) (andR32Imm32Effect 0x10534d 7 10 0x3333) (Reg.operands [.gpr 10] [])) #v[171]
    (.letOp (n := 175) (.out 0x105354 (movR32R32Effect 0x105354 3 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[167]
    (.letOp (n := 176) (.exec 0x105354 (fun s => s.RIP = 0x105354) (movR32R32Effect 0x105354 3 0 14) (Reg.operands [.gpr 14] [])) #v[167]
    (.letOp (n := 177) (.out 0x105357 (rolR16Effect 0x105357 4 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[175]
    (.letOp (n := 178) (.exec 0x105357 (fun s => s.RIP = 0x105357) (rolR16Effect 0x105357 4 0 14) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[175]
    (.letOp (n := 179) (.out 0x10535b (andEaxImm32Effect 0x10535b 0xffffcccc) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[177]
    (.letOp (n := 180) (.exec 0x10535b (fun s => s.RIP = 0x10535b) (andEaxImm32Effect 0x10535b 0xffffcccc) (Reg.operands [.gpr 0] [])) #v[177]
    (.letOp (n := 181) (.out 0x105360 (orR32R32Effect 0x105360 3 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[179, 173]
    (.letOp (n := 182) (.exec 0x105360 (fun s => s.RIP = 0x105360) (orR32R32Effect 0x105360 3 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[179, 173]
    (.letOp (n := 183) (.out 0x105363 (xorR32R32Effect 0x105363 3 9 5) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 5] []) (.reg (.gpr 9))) #v[53, 79]
    (.letOp (n := 184) (.exec 0x105363 (fun s => s.RIP = 0x105363) (xorR32R32Effect 0x105363 3 9 5) (Reg.operands [.gpr 9, .gpr 5] [])) #v[53, 79]
    (.letOp (n := 185) (.out 0x105366 (xorR32R32Effect 0x105366 3 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 0] []) (.reg (.gpr 14))) #v[167, 181]
    (.letOp (n := 186) (.exec 0x105366 (fun s => s.RIP = 0x105366) (xorR32R32Effect 0x105366 3 14 0) (Reg.operands [.gpr 14, .gpr 0] [])) #v[167, 181]
    (.letOp (n := 187) (.out 0x105369 (movR32R32Effect 0x105369 3 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 9] []) (.reg (.gpr 10))) #v[183]
    (.letOp (n := 188) (.exec 0x105369 (fun s => s.RIP = 0x105369) (movR32R32Effect 0x105369 3 10 9) (Reg.operands [.gpr 9] [])) #v[183]
    (.letOp (n := 189) (.out 0x10536c (rolR16Effect 0x10536c 5 10 8) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[187]
    (.letOp (n := 190) (.exec 0x10536c (fun s => s.RIP = 0x10536c) (rolR16Effect 0x10536c 5 10 8) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[187]
    (.letOp (n := 191) (.out 0x105371 (movR64M64Effect 0x105371 3 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 192) (.exec 0x105371 (LoadPre 0x105371 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x105371 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x105371 3 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 193) (.out 0x105376 (xorR16M16Effect 0x105376 6 10 (.sib 3 (some 12) 1 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 3, .gpr 12] []) (.reg (.gpr 10))) #v[189, 191, 12]
    (.letOp (n := 194) (.exec 0x105376 (LoadPre 0x105376 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x20)) s (0x105376 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x105376 6 10 (.sib 3 (some 12) 1 (.d8 0x20))) (Reg.operands [.gpr 10, .gpr 3, .gpr 12] [])) #v[189, 191, 12]
    (.letOp (n := 195) (.out 0x10537c (xorR32R32Effect 0x10537c 3 5 14) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 14] []) (.reg (.gpr 5))) #v[79, 185]
    (.letOp (n := 196) (.exec 0x10537c (fun s => s.RIP = 0x10537c) (xorR32R32Effect 0x10537c 3 5 14) (Reg.operands [.gpr 5, .gpr 14] [])) #v[79, 185]
    (.letOp (n := 197) (.out 0x10537f (xorR32R32Effect 0x10537f 3 5 10) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 10] []) (.reg (.gpr 5))) #v[195, 193]
    (.letOp (n := 198) (.exec 0x10537f (fun s => s.RIP = 0x10537f) (xorR32R32Effect 0x10537f 3 5 10) (Reg.operands [.gpr 5, .gpr 10] [])) #v[195, 193]
    (.letOp (n := 199) (.exec 0x105382 (StorePre 0x105382 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x105382 + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x105382 4 5 (.sib 4 none 0 .none)) (Reg.operands [.gpr 5, .gpr 4] [])) #v[197, 4]
    (.letOp (n := 200) (.out 0x105386 (xorR32R32Effect 0x105386 3 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 8] []) (.reg (.gpr 2))) #v[57, 97]
    (.letOp (n := 201) (.exec 0x105386 (fun s => s.RIP = 0x105386) (xorR32R32Effect 0x105386 3 2 8) (Reg.operands [.gpr 2, .gpr 8] [])) #v[57, 97]
    (.letOp (n := 202) (.out 0x105389 (xorR32R32Effect 0x105389 3 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8] []) (.reg (.gpr 9))) #v[183, 97]
    (.letOp (n := 203) (.exec 0x105389 (fun s => s.RIP = 0x105389) (xorR32R32Effect 0x105389 3 9 8) (Reg.operands [.gpr 9, .gpr 8] [])) #v[183, 97]
    (.letOp (n := 204) (.out 0x10538c (movR32R32Effect 0x10538c 3 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[200]
    (.letOp (n := 205) (.exec 0x10538c (fun s => s.RIP = 0x10538c) (movR32R32Effect 0x10538c 3 8 2) (Reg.operands [.gpr 2] [])) #v[200]
    (.letOp (n := 206) (.out 0x10538f (rolR16Effect 0x10538f 5 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[204]
    (.letOp (n := 207) (.exec 0x10538f (fun s => s.RIP = 0x10538f) (rolR16Effect 0x10538f 5 8 8) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[204]
    (b_l105243_4)))))))))))))))))))))))))))))))))))))))

def bytes_l105243_3 : List UInt8 :=
  [0x45, 0x89, 0xF2, 0x66, 0x41, 0xC1, 0xC2, 0x0A, 0x41, 0x81, 0xE2, 0x33, 0x33, 0x00, 0x00, 0x44,
    0x89, 0xF0, 0x66, 0xC1, 0xC0, 0x0E, 0x25, 0xCC, 0xCC, 0xFF, 0xFF, 0x44, 0x09, 0xD0, 0x41, 0x31,
    0xE9, 0x41, 0x31, 0xC6, 0x45, 0x89, 0xCA, 0x66, 0x41, 0xC1, 0xC2, 0x08, 0x48, 0x8B, 0x5C, 0x24,
    0x28, 0x66, 0x46, 0x33, 0x54, 0x63, 0x20, 0x44, 0x31, 0xF5, 0x44, 0x31, 0xD5, 0x66, 0x89, 0x2C,
    0x24, 0x44, 0x31, 0xC2, 0x45, 0x31, 0xC1, 0x41, 0x89, 0xD0, 0x66, 0x41, 0xC1, 0xC0, 0x08] ++ bytes_l105243_4

theorem code_l105243_3 : ∀ x ∈ codeRange 0x105345 bytes_l105243_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x5345 79 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l105243_4

@[cfg_block] def b_l105243_2 : Block Op Label signature Reg.count 132 :=
  .letOp (n := 132) (.out 0x1052e8 (andR32Imm32Effect 0x1052e8 7 13 0xffffcccc) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[130]
    (.letOp (n := 133) (.exec 0x1052e8 (fun s => s.RIP = 0x1052e8) (andR32Imm32Effect 0x1052e8 7 13 0xffffcccc) (Reg.operands [.gpr 13] [])) #v[130]
    (.letOp (n := 134) (.out 0x1052ef (orR32R32Effect 0x1052ef 3 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 0] []) (.reg (.gpr 13))) #v[132, 128]
    (.letOp (n := 135) (.exec 0x1052ef (fun s => s.RIP = 0x1052ef) (orR32R32Effect 0x1052ef 3 13 0) (Reg.operands [.gpr 13, .gpr 0] [])) #v[132, 128]
    (.letOp (n := 136) (.exec 0x1052f2 (StorePre 0x1052f2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1052f2 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x1052f2 10 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[63, 4]
    (.letOp (n := 137) (.out 0x1052f7 (movR32R32Effect 0x1052f7 3 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[63]
    (.letOp (n := 138) (.exec 0x1052f7 (fun s => s.RIP = 0x1052f7) (movR32R32Effect 0x1052f7 3 0 10) (Reg.operands [.gpr 10] [])) #v[63]
    (.letOp (n := 139) (.out 0x1052fa (rolR16Effect 0x1052fa 4 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[137]
    (.letOp (n := 140) (.exec 0x1052fa (fun s => s.RIP = 0x1052fa) (rolR16Effect 0x1052fa 4 0 10) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[137]
    (.letOp (n := 141) (.out 0x1052fe (andEaxImm32Effect 0x1052fe 0x3333) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[139]
    (.letOp (n := 142) (.exec 0x1052fe (fun s => s.RIP = 0x1052fe) (andEaxImm32Effect 0x1052fe 0x3333) (Reg.operands [.gpr 0] [])) #v[139]
    (.letOp (n := 143) (.out 0x105303 (movR32R32Effect 0x105303 3 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 10] []) (.reg (.gpr 11))) #v[63]
    (.letOp (n := 144) (.exec 0x105303 (fun s => s.RIP = 0x105303) (movR32R32Effect 0x105303 3 11 10) (Reg.operands [.gpr 10] [])) #v[63]
    (.letOp (n := 145) (.out 0x105306 (rolR16Effect 0x105306 5 11 14) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[143]
    (.letOp (n := 146) (.exec 0x105306 (fun s => s.RIP = 0x105306) (rolR16Effect 0x105306 5 11 14) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[143]
    (.letOp (n := 147) (.out 0x10530b (andR32Imm32Effect 0x10530b 7 11 0xffffcccc) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11] []) (.reg (.gpr 11))) #v[145]
    (.letOp (n := 148) (.exec 0x10530b (fun s => s.RIP = 0x10530b) (andR32Imm32Effect 0x10530b 7 11 0xffffcccc) (Reg.operands [.gpr 11] [])) #v[145]
    (.letOp (n := 149) (.exec 0x105312 (StorePre 0x105312 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x105312 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x105312 3 (.sib 4 none 0 (.d8 0x1c))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 150) (.out 0x105316 (movR32R32Effect 0x105316 3 10 3) (EffectPart.reads (.reg (.gpr 10)) [.gpr 3] []) (.reg (.gpr 10))) #v[65]
    (.letOp (n := 151) (.exec 0x105316 (fun s => s.RIP = 0x105316) (movR32R32Effect 0x105316 3 10 3) (Reg.operands [.gpr 3] [])) #v[65]
    (.letOp (n := 152) (.out 0x105319 (rolR16Effect 0x105319 5 10 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[150]
    (.letOp (n := 153) (.exec 0x105319 (fun s => s.RIP = 0x105319) (rolR16Effect 0x105319 5 10 10) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[150]
    (.letOp (n := 154) (.out 0x10531e (orR32R32Effect 0x10531e 3 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0] []) (.reg (.gpr 11))) #v[147, 141]
    (.letOp (n := 155) (.exec 0x10531e (fun s => s.RIP = 0x10531e) (orR32R32Effect 0x10531e 3 11 0) (Reg.operands [.gpr 11, .gpr 0] [])) #v[147, 141]
    (.letOp (n := 156) (.exec 0x105321 (StorePre 0x105321 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x105321 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x105321 11 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[154, 4]
    (.letOp (n := 157) (.out 0x105326 (movR32R32Effect 0x105326 3 11 3) (EffectPart.reads (.reg (.gpr 11)) [.gpr 3] []) (.reg (.gpr 11))) #v[65]
    (.letOp (n := 158) (.exec 0x105326 (fun s => s.RIP = 0x105326) (movR32R32Effect 0x105326 3 11 3) (Reg.operands [.gpr 3] [])) #v[65]
    (.letOp (n := 159) (.out 0x105329 (rolR16Effect 0x105329 5 11 14) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[157]
    (.letOp (n := 160) (.exec 0x105329 (fun s => s.RIP = 0x105329) (rolR16Effect 0x105329 5 11 14) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[157]
    (.letOp (n := 161) (.out 0x10532e (andR32Imm32Effect 0x10532e 7 10 0x3333) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[152]
    (.letOp (n := 162) (.exec 0x10532e (fun s => s.RIP = 0x10532e) (andR32Imm32Effect 0x10532e 7 10 0x3333) (Reg.operands [.gpr 10] [])) #v[152]
    (.letOp (n := 163) (.out 0x105335 (andR32Imm32Effect 0x105335 7 11 0xffffcccc) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11] []) (.reg (.gpr 11))) #v[159]
    (.letOp (n := 164) (.exec 0x105335 (fun s => s.RIP = 0x105335) (andR32Imm32Effect 0x105335 7 11 0xffffcccc) (Reg.operands [.gpr 11] [])) #v[159]
    (.letOp (n := 165) (.out 0x10533c (orR32R32Effect 0x10533c 3 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 10] []) (.reg (.gpr 11))) #v[163, 161]
    (.letOp (n := 166) (.exec 0x10533c (fun s => s.RIP = 0x10533c) (orR32R32Effect 0x10533c 3 11 10) (Reg.operands [.gpr 11, .gpr 10] [])) #v[163, 161]
    (.letOp (n := 167) (.out 0x10533f (movzxR32M16Effect 0x10533f 6 14 (.sib 4 none 0 (.d8 0xe))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 168) (.exec 0x10533f (LoadPre 0x10533f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x10533f + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x10533f 6 14 (.sib 4 none 0 (.d8 0xe))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l105243_3)))))))))))))))))))))))))))))))))))))

def bytes_l105243_2 : List UInt8 :=
  [0x41, 0x81, 0xE5, 0xCC, 0xCC, 0xFF, 0xFF, 0x41, 0x09, 0xC5, 0x44, 0x89, 0x54, 0x24, 0x18, 0x44,
    0x89, 0xD0, 0x66, 0xC1, 0xC0, 0x0A, 0x25, 0x33, 0x33, 0x00, 0x00, 0x45, 0x89, 0xD3, 0x66, 0x41,
    0xC1, 0xC3, 0x0E, 0x41, 0x81, 0xE3, 0xCC, 0xCC, 0xFF, 0xFF, 0x89, 0x5C, 0x24, 0x1C, 0x41, 0x89,
    0xDA, 0x66, 0x41, 0xC1, 0xC2, 0x0A, 0x41, 0x09, 0xC3, 0x44, 0x89, 0x5C, 0x24, 0x14, 0x41, 0x89,
    0xDB, 0x66, 0x41, 0xC1, 0xC3, 0x0E, 0x41, 0x81, 0xE2, 0x33, 0x33, 0x00, 0x00, 0x41, 0x81, 0xE3,
    0xCC, 0xCC, 0xFF, 0xFF, 0x45, 0x09, 0xD3, 0x44, 0x0F, 0xB7, 0x74, 0x24, 0x0E] ++ bytes_l105243_3

theorem code_l105243_2 : ∀ x ∈ codeRange 0x1052e8 bytes_l105243_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x52e8 93 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l105243_3

@[cfg_block] def b_l105243_1 : Block Op Label signature Reg.count 93 :=
  .letOp (n := 93) (.out 0x10529a (movR32R32Effect 0x10529a 2 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 7] []) (.reg (.gpr 6))) #v[55]
    (.letOp (n := 94) (.exec 0x10529a (fun s => s.RIP = 0x10529a) (movR32R32Effect 0x10529a 2 6 7) (Reg.operands [.gpr 7] [])) #v[55]
    (.letOp (n := 95) (.out 0x10529c (rolR16Effect 0x10529c 4 6 10) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[93]
    (.letOp (n := 96) (.exec 0x10529c (fun s => s.RIP = 0x10529c) (rolR16Effect 0x10529c 4 6 10) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[93]
    (.letOp (n := 97) (.out 0x1052a0 (orR32R32Effect 0x1052a0 3 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[91, 85]
    (.letOp (n := 98) (.exec 0x1052a0 (fun s => s.RIP = 0x1052a0) (orR32R32Effect 0x1052a0 3 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[91, 85]
    (.letOp (n := 99) (.out 0x1052a3 (movR32R32Effect 0x1052a3 2 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 7] []) (.reg (.gpr 1))) #v[55]
    (.letOp (n := 100) (.exec 0x1052a3 (fun s => s.RIP = 0x1052a3) (movR32R32Effect 0x1052a3 2 1 7) (Reg.operands [.gpr 7] [])) #v[55]
    (.letOp (n := 101) (.out 0x1052a5 (rolR16Effect 0x1052a5 4 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[99]
    (.letOp (n := 102) (.exec 0x1052a5 (fun s => s.RIP = 0x1052a5) (rolR16Effect 0x1052a5 4 1 14) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[99]
    (.letOp (n := 103) (.out 0x1052a9 (andR32Imm32Effect 0x1052a9 6 6 0x3333) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[95]
    (.letOp (n := 104) (.exec 0x1052a9 (fun s => s.RIP = 0x1052a9) (andR32Imm32Effect 0x1052a9 6 6 0x3333) (Reg.operands [.gpr 6] [])) #v[95]
    (.letOp (n := 105) (.out 0x1052af (andR32Imm32Effect 0x1052af 6 1 0xffffcccc) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[101]
    (.letOp (n := 106) (.exec 0x1052af (fun s => s.RIP = 0x1052af) (andR32Imm32Effect 0x1052af 6 1 0xffffcccc) (Reg.operands [.gpr 1] [])) #v[101]
    (.letOp (n := 107) (.out 0x1052b5 (orR32R32Effect 0x1052b5 2 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[105, 103]
    (.letOp (n := 108) (.exec 0x1052b5 (fun s => s.RIP = 0x1052b5) (orR32R32Effect 0x1052b5 2 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[105, 103]
    (.letOp (n := 109) (.out 0x1052b7 (movR32R32Effect 0x1052b7 3 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[59]
    (.letOp (n := 110) (.exec 0x1052b7 (fun s => s.RIP = 0x1052b7) (movR32R32Effect 0x1052b7 3 0 15) (Reg.operands [.gpr 15] [])) #v[59]
    (.letOp (n := 111) (.out 0x1052ba (rolR16Effect 0x1052ba 4 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[109]
    (.letOp (n := 112) (.exec 0x1052ba (fun s => s.RIP = 0x1052ba) (rolR16Effect 0x1052ba 4 0 10) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[109]
    (.letOp (n := 113) (.out 0x1052be (andEaxImm32Effect 0x1052be 0x3333) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[111]
    (.letOp (n := 114) (.exec 0x1052be (fun s => s.RIP = 0x1052be) (andEaxImm32Effect 0x1052be 0x3333) (Reg.operands [.gpr 0] [])) #v[111]
    (.letOp (n := 115) (.out 0x1052c3 (movR32R32Effect 0x1052c3 3 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[59]
    (.letOp (n := 116) (.exec 0x1052c3 (fun s => s.RIP = 0x1052c3) (movR32R32Effect 0x1052c3 3 6 15) (Reg.operands [.gpr 15] [])) #v[59]
    (.letOp (n := 117) (.out 0x1052c6 (rolR16Effect 0x1052c6 4 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[115]
    (.letOp (n := 118) (.exec 0x1052c6 (fun s => s.RIP = 0x1052c6) (rolR16Effect 0x1052c6 4 6 14) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[115]
    (.letOp (n := 119) (.out 0x1052ca (andR32Imm32Effect 0x1052ca 6 6 0xffffcccc) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[117]
    (.letOp (n := 120) (.exec 0x1052ca (fun s => s.RIP = 0x1052ca) (andR32Imm32Effect 0x1052ca 6 6 0xffffcccc) (Reg.operands [.gpr 6] [])) #v[117]
    (.letOp (n := 121) (.out 0x1052d0 (orR32R32Effect 0x1052d0 2 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[119, 113]
    (.letOp (n := 122) (.exec 0x1052d0 (fun s => s.RIP = 0x1052d0) (orR32R32Effect 0x1052d0 2 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[119, 113]
    (.letOp (n := 123) (.exec 0x1052d2 (StorePre 0x1052d2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1052d2 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x1052d2 13 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 124) (.out 0x1052d7 (movR32R32Effect 0x1052d7 3 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[61]
    (.letOp (n := 125) (.exec 0x1052d7 (fun s => s.RIP = 0x1052d7) (movR32R32Effect 0x1052d7 3 0 13) (Reg.operands [.gpr 13] [])) #v[61]
    (.letOp (n := 126) (.out 0x1052da (rolR16Effect 0x1052da 4 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[124]
    (.letOp (n := 127) (.exec 0x1052da (fun s => s.RIP = 0x1052da) (rolR16Effect 0x1052da 4 0 10) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[124]
    (.letOp (n := 128) (.out 0x1052de (andEaxImm32Effect 0x1052de 0x3333) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[126]
    (.letOp (n := 129) (.exec 0x1052de (fun s => s.RIP = 0x1052de) (andEaxImm32Effect 0x1052de 0x3333) (Reg.operands [.gpr 0] [])) #v[126]
    (.letOp (n := 130) (.out 0x1052e3 (rolR16Effect 0x1052e3 5 13 14) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[61]
    (.letOp (n := 131) (.exec 0x1052e3 (fun s => s.RIP = 0x1052e3) (rolR16Effect 0x1052e3 5 13 14) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[61]
    (b_l105243_2)))))))))))))))))))))))))))))))))))))))

def bytes_l105243_1 : List UInt8 :=
  [0x89, 0xFE, 0x66, 0xC1, 0xC6, 0x0A, 0x41, 0x09, 0xC0, 0x89, 0xF9, 0x66, 0xC1, 0xC1, 0x0E, 0x81,
    0xE6, 0x33, 0x33, 0x00, 0x00, 0x81, 0xE1, 0xCC, 0xCC, 0xFF, 0xFF, 0x09, 0xF1, 0x44, 0x89, 0xF8,
    0x66, 0xC1, 0xC0, 0x0A, 0x25, 0x33, 0x33, 0x00, 0x00, 0x44, 0x89, 0xFE, 0x66, 0xC1, 0xC6, 0x0E,
    0x81, 0xE6, 0xCC, 0xCC, 0xFF, 0xFF, 0x09, 0xC6, 0x44, 0x89, 0x6C, 0x24, 0x20, 0x44, 0x89, 0xE8,
    0x66, 0xC1, 0xC0, 0x0A, 0x25, 0x33, 0x33, 0x00, 0x00, 0x66, 0x41, 0xC1, 0xC5, 0x0E] ++ bytes_l105243_2

theorem code_l105243_1 : ∀ x ∈ codeRange 0x10529a bytes_l105243_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x529a 78 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l105243_2

@[cfg_block] def b_l105243 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x105243 (movR32M32Effect 0x105243 9 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 54) (.exec 0x105243 (LoadPre 0x105243 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x105243 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x105243 9 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x105247 (movR32M32LowEffect 0x105247 7 (.sib 4 none 0 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 56) (.exec 0x105247 (LoadPre 0x105247 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x105247 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x105247 7 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x10524b (movzxR32M16Effect 0x10524b 5 2 (.sib 4 none 0 (.d8 0x2))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 58) (.exec 0x10524b (LoadPre 0x10524b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2)) s (0x10524b + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x10524b 5 2 (.sib 4 none 0 (.d8 0x2))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x105250 (movzxR32M16Effect 0x105250 6 15 (.sib 4 none 0 (.d8 0x6))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 60) (.exec 0x105250 (LoadPre 0x105250 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6)) s (0x105250 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x105250 6 15 (.sib 4 none 0 (.d8 0x6))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x105256 (movR32M32Effect 0x105256 13 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 62) (.exec 0x105256 (LoadPre 0x105256 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x105256 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x105256 13 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x10525b (movzxR32M16Effect 0x10525b 6 10 (.sib 4 none 0 (.d8 0xa))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 64) (.exec 0x10525b (LoadPre 0x10525b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xa)) s (0x10525b + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x10525b 6 10 (.sib 4 none 0 (.d8 0xa))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x105261 (movR32M32LowEffect 0x105261 3 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 66) (.exec 0x105261 (LoadPre 0x105261 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x105261 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x105261 3 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x105265 (movR32R32Effect 0x105265 3 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 68) (.exec 0x105265 (fun s => s.RIP = 0x105265) (movR32R32Effect 0x105265 3 0 9) (Reg.operands [.gpr 9] [])) #v[53]
    (.letOp (n := 69) (.out 0x105268 (rolR16Effect 0x105268 4 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[67]
    (.letOp (n := 70) (.exec 0x105268 (fun s => s.RIP = 0x105268) (rolR16Effect 0x105268 4 0 10) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[67]
    (.letOp (n := 71) (.out 0x10526c (andEaxImm32Effect 0x10526c 0x3333) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[69]
    (.letOp (n := 72) (.exec 0x10526c (fun s => s.RIP = 0x10526c) (andEaxImm32Effect 0x10526c 0x3333) (Reg.operands [.gpr 0] [])) #v[69]
    (.letOp (n := 73) (.out 0x105271 (movR32R32Effect 0x105271 3 5 9) (EffectPart.reads (.reg (.gpr 5)) [.gpr 9] []) (.reg (.gpr 5))) #v[53]
    (.letOp (n := 74) (.exec 0x105271 (fun s => s.RIP = 0x105271) (movR32R32Effect 0x105271 3 5 9) (Reg.operands [.gpr 9] [])) #v[53]
    (.letOp (n := 75) (.out 0x105274 (rolR16Effect 0x105274 4 5 14) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[73]
    (.letOp (n := 76) (.exec 0x105274 (fun s => s.RIP = 0x105274) (rolR16Effect 0x105274 4 5 14) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[73]
    (.letOp (n := 77) (.out 0x105278 (andR32Imm32Effect 0x105278 6 5 0xffffcccc) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5] []) (.reg (.gpr 5))) #v[75]
    (.letOp (n := 78) (.exec 0x105278 (fun s => s.RIP = 0x105278) (andR32Imm32Effect 0x105278 6 5 0xffffcccc) (Reg.operands [.gpr 5] [])) #v[75]
    (.letOp (n := 79) (.out 0x10527e (orR32R32Effect 0x10527e 2 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 0] []) (.reg (.gpr 5))) #v[77, 71]
    (.letOp (n := 80) (.exec 0x10527e (fun s => s.RIP = 0x10527e) (orR32R32Effect 0x10527e 2 5 0) (Reg.operands [.gpr 5, .gpr 0] [])) #v[77, 71]
    (.letOp (n := 81) (.out 0x105280 (movR32R32Effect 0x105280 2 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[57]
    (.letOp (n := 82) (.exec 0x105280 (fun s => s.RIP = 0x105280) (movR32R32Effect 0x105280 2 0 2) (Reg.operands [.gpr 2] [])) #v[57]
    (.letOp (n := 83) (.out 0x105282 (rolR16Effect 0x105282 4 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[81]
    (.letOp (n := 84) (.exec 0x105282 (fun s => s.RIP = 0x105282) (rolR16Effect 0x105282 4 0 10) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[81]
    (.letOp (n := 85) (.out 0x105286 (andEaxImm32Effect 0x105286 0x3333) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[83]
    (.letOp (n := 86) (.exec 0x105286 (fun s => s.RIP = 0x105286) (andEaxImm32Effect 0x105286 0x3333) (Reg.operands [.gpr 0] [])) #v[83]
    (.letOp (n := 87) (.out 0x10528b (movR32R32Effect 0x10528b 3 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[57]
    (.letOp (n := 88) (.exec 0x10528b (fun s => s.RIP = 0x10528b) (movR32R32Effect 0x10528b 3 8 2) (Reg.operands [.gpr 2] [])) #v[57]
    (.letOp (n := 89) (.out 0x10528e (rolR16Effect 0x10528e 5 8 14) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[87]
    (.letOp (n := 90) (.exec 0x10528e (fun s => s.RIP = 0x10528e) (rolR16Effect 0x10528e 5 8 14) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[87]
    (.letOp (n := 91) (.out 0x105293 (andR32Imm32Effect 0x105293 7 8 0xffffcccc) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[89]
    (.letOp (n := 92) (.exec 0x105293 (fun s => s.RIP = 0x105293) (andR32Imm32Effect 0x105293 7 8 0xffffcccc) (Reg.operands [.gpr 8] [])) #v[89]
    (b_l105243_1))))))))))))))))))))))))))))))))))))))))

def bytes_l105243 : List UInt8 :=
  [0x44, 0x8B, 0x0C, 0x24, 0x8B, 0x7C, 0x24, 0x04, 0x0F, 0xB7, 0x54, 0x24, 0x02, 0x44, 0x0F, 0xB7,
    0x7C, 0x24, 0x06, 0x44, 0x8B, 0x6C, 0x24, 0x08, 0x44, 0x0F, 0xB7, 0x54, 0x24, 0x0A, 0x8B, 0x5C,
    0x24, 0x0C, 0x44, 0x89, 0xC8, 0x66, 0xC1, 0xC0, 0x0A, 0x25, 0x33, 0x33, 0x00, 0x00, 0x44, 0x89,
    0xCD, 0x66, 0xC1, 0xC5, 0x0E, 0x81, 0xE5, 0xCC, 0xCC, 0xFF, 0xFF, 0x09, 0xC5, 0x89, 0xD0, 0x66,
    0xC1, 0xC0, 0x0A, 0x25, 0x33, 0x33, 0x00, 0x00, 0x41, 0x89, 0xD0, 0x66, 0x41, 0xC1, 0xC0, 0x0E,
    0x41, 0x81, 0xE0, 0xCC, 0xCC, 0xFF, 0xFF] ++ bytes_l105243_1

theorem code_l105243 : ∀ x ∈ codeRange 0x105243 bytes_l105243, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x5243 87 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l105243_1

@[cfg_block] def b_l10546a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10546a (movR64R64Effect 0x10546a 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 54) (.exec 0x10546a (fun s => s.RIP = 0x10546a) (movR64R64Effect 0x10546a 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 55) (.out 0x10546d (callEffect (fun _ => 0x100580) 0x105472) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 56) (.exec 0x10546d (PushPre 0x10546d 5) (callEffect (fun _ => 0x100580) 0x105472) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.const ⟨64, 0x105472⟩) #v[]
    (.terminate (.call ⟨.l100580, RegMap.args [(3, 3), (4, 55), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ { target := .l105472, kept := #v[], arity := rfl, guard := some (Fin.last 57) }))))))

def bytes_l10546a : List UInt8 :=
  [0x4C, 0x89, 0xF7, 0xE8, 0x0E, 0xB1, 0xFF, 0xFF]

theorem code_l10546a : ∀ x ∈ codeRange 0x10546a bytes_l10546a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x546a 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105472 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x105472 (movzxR32M16Effect 0x105472 6 0 (.sib 3 (some 12) 1 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 12] []) (.reg (.gpr 0))) #v[3, 12]
    (.letOp (n := 54) (.exec 0x105472 (LoadPre 0x105472 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x30)) s (0x105472 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x105472 6 0 (.sib 3 (some 12) 1 (.d8 0x30))) (Reg.operands [.gpr 3, .gpr 12] [])) #v[3, 12]
    (.letOp (n := 55) (.exec 0x105478 (StorePre 0x105478 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x105478 + BitVec.ofNat 64 4)) 2) (xorMREffect 0x105478 4 16 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x10547c (movzxR32M16Effect 0x10547c 6 0 (.sib 3 (some 12) 1 (.d8 0x32))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 12] []) (.reg (.gpr 0))) #v[3, 12]
    (.letOp (n := 57) (.exec 0x10547c (LoadPre 0x10547c (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x32)) s (0x10547c + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x10547c 6 0 (.sib 3 (some 12) 1 (.d8 0x32))) (Reg.operands [.gpr 3, .gpr 12] [])) #v[3, 12]
    (.letOp (n := 58) (.exec 0x105482 (StorePre 0x105482 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2)) s (0x105482 + BitVec.ofNat 64 5)) 2) (xorMREffect 0x105482 5 16 0 (.sib 4 none 0 (.d8 0x2))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x105487 (movzxR32M16Effect 0x105487 6 0 (.sib 3 (some 12) 1 (.d8 0x34))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 12] []) (.reg (.gpr 0))) #v[3, 12]
    (.letOp (n := 60) (.exec 0x105487 (LoadPre 0x105487 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x34)) s (0x105487 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x105487 6 0 (.sib 3 (some 12) 1 (.d8 0x34))) (Reg.operands [.gpr 3, .gpr 12] [])) #v[3, 12]
    (.letOp (n := 61) (.exec 0x10548d (StorePre 0x10548d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x10548d + BitVec.ofNat 64 5)) 2) (xorMREffect 0x10548d 5 16 0 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x105492 (movzxR32M16Effect 0x105492 6 0 (.sib 3 (some 12) 1 (.d8 0x36))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 12] []) (.reg (.gpr 0))) #v[3, 12]
    (.letOp (n := 63) (.exec 0x105492 (LoadPre 0x105492 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x36)) s (0x105492 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x105492 6 0 (.sib 3 (some 12) 1 (.d8 0x36))) (Reg.operands [.gpr 3, .gpr 12] [])) #v[3, 12]
    (.letOp (n := 64) (.exec 0x105498 (StorePre 0x105498 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6)) s (0x105498 + BitVec.ofNat 64 5)) 2) (xorMREffect 0x105498 5 16 0 (.sib 4 none 0 (.d8 0x6))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x10549d (movzxR32M16Effect 0x10549d 6 0 (.sib 3 (some 12) 1 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 12] []) (.reg (.gpr 0))) #v[3, 12]
    (.letOp (n := 66) (.exec 0x10549d (LoadPre 0x10549d (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x38)) s (0x10549d + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x10549d 6 0 (.sib 3 (some 12) 1 (.d8 0x38))) (Reg.operands [.gpr 3, .gpr 12] [])) #v[3, 12]
    (.letOp (n := 67) (.exec 0x1054a3 (StorePre 0x1054a3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1054a3 + BitVec.ofNat 64 5)) 2) (xorMREffect 0x1054a3 5 16 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x1054a8 (movzxR32M16Effect 0x1054a8 6 0 (.sib 3 (some 12) 1 (.d8 0x3a))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 12] []) (.reg (.gpr 0))) #v[3, 12]
    (.letOp (n := 69) (.exec 0x1054a8 (LoadPre 0x1054a8 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x3a)) s (0x1054a8 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x1054a8 6 0 (.sib 3 (some 12) 1 (.d8 0x3a))) (Reg.operands [.gpr 3, .gpr 12] [])) #v[3, 12]
    (.letOp (n := 70) (.exec 0x1054ae (StorePre 0x1054ae 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xa)) s (0x1054ae + BitVec.ofNat 64 5)) 2) (xorMREffect 0x1054ae 5 16 0 (.sib 4 none 0 (.d8 0xa))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[68, 4]
    (.letOp (n := 71) (.out 0x1054b3 (movzxR32M16Effect 0x1054b3 6 0 (.sib 3 (some 12) 1 (.d8 0x3c))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 12] []) (.reg (.gpr 0))) #v[3, 12]
    (.letOp (n := 72) (.exec 0x1054b3 (LoadPre 0x1054b3 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x3c)) s (0x1054b3 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x1054b3 6 0 (.sib 3 (some 12) 1 (.d8 0x3c))) (Reg.operands [.gpr 3, .gpr 12] [])) #v[3, 12]
    (.letOp (n := 73) (.exec 0x1054b9 (StorePre 0x1054b9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x1054b9 + BitVec.ofNat 64 5)) 2) (xorMREffect 0x1054b9 5 16 0 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[71, 4]
    (.letOp (n := 74) (.out 0x1054be (movzxR32M16Effect 0x1054be 6 0 (.sib 3 (some 12) 1 (.d8 0x3e))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 12] []) (.reg (.gpr 0))) #v[3, 12]
    (.letOp (n := 75) (.exec 0x1054be (LoadPre 0x1054be (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x3e)) s (0x1054be + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x1054be 6 0 (.sib 3 (some 12) 1 (.d8 0x3e))) (Reg.operands [.gpr 3, .gpr 12] [])) #v[3, 12]
    (.letOp (n := 76) (.exec 0x1054c4 (StorePre 0x1054c4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x1054c4 + BitVec.ofNat 64 5)) 2) (xorMREffect 0x1054c4 5 16 0 (.sib 4 none 0 (.d8 0xe))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[74, 4]
    (.letOp (n := 77) (.out 0x1054c9 (movR32Imm32Effect 0x1054c9 5 6 0x8) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 78) (.exec 0x1054c9 (fun s => s.RIP = 0x1054c9) (movR32Imm32Effect 0x1054c9 5 6 0x8) (Reg.operands [] [])) #v[]
    (.letOp (n := 79) (.out 0x1054ce (movR64R64Effect 0x1054ce 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 80) (.exec 0x1054ce (fun s => s.RIP = 0x1054ce) (movR64R64Effect 0x1054ce 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 81) (.out 0x1054d1 (callEffect (fun _ => 0x100b10) 0x1054d6) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 82) (.exec 0x1054d1 (PushPre 0x1054d1 5) (callEffect (fun _ => 0x100b10) 0x1054d6) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 83) (.const ⟨64, 0x1054d6⟩) #v[]
    (.terminate (.call ⟨.l100b10, RegMap.args [(0, 74), (3, 3), (4, 81), (5, 5), (6, 77), (7, 79), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 84⟩ { target := .l1054d6, kept := #v[], arity := rfl, guard := some (Fin.last 83) }))))))))))))))))))))))))))))))))

def bytes_l105472 : List UInt8 :=
  [0x42, 0x0F, 0xB7, 0x44, 0x63, 0x30, 0x66, 0x31, 0x04, 0x24, 0x42, 0x0F, 0xB7, 0x44, 0x63, 0x32,
    0x66, 0x31, 0x44, 0x24, 0x02, 0x42, 0x0F, 0xB7, 0x44, 0x63, 0x34, 0x66, 0x31, 0x44, 0x24, 0x04,
    0x42, 0x0F, 0xB7, 0x44, 0x63, 0x36, 0x66, 0x31, 0x44, 0x24, 0x06, 0x42, 0x0F, 0xB7, 0x44, 0x63,
    0x38, 0x66, 0x31, 0x44, 0x24, 0x08, 0x42, 0x0F, 0xB7, 0x44, 0x63, 0x3A, 0x66, 0x31, 0x44, 0x24,
    0x0A, 0x42, 0x0F, 0xB7, 0x44, 0x63, 0x3C, 0x66, 0x31, 0x44, 0x24, 0x0C, 0x42, 0x0F, 0xB7, 0x44,
    0x63, 0x3E, 0x66, 0x31, 0x44, 0x24, 0x0E, 0xBE, 0x08, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF7, 0xE8,
    0x3A, 0xB6, 0xFF, 0xFF]

theorem code_l105472 : ∀ x ∈ codeRange 0x105472 bytes_l105472, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5472 100 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1054d6_4 : Block Op Label signature Reg.count 203 :=
  .letOp (n := 203) (.out 0x105603 (movR32R32Effect 0x105603 2 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 7] []) (.reg (.gpr 1))) #v[199]
    (.letOp (n := 204) (.exec 0x105603 (fun s => s.RIP = 0x105603) (movR32R32Effect 0x105603 2 1 7) (Reg.operands [.gpr 7] [])) #v[199]
    (.letOp (n := 205) (.out 0x105605 (rolR16Effect 0x105605 4 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[203]
    (.letOp (n := 206) (.exec 0x105605 (fun s => s.RIP = 0x105605) (rolR16Effect 0x105605 4 1 8) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[203]
    (.letOp (n := 207) (.out 0x105609 (xorR16M16Effect 0x105609 6 1 (.sib 3 (some 12) 1 (.d8 0x4a))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 3, .gpr 12] []) (.reg (.gpr 1))) #v[205, 3, 117]
    (.letOp (n := 208) (.exec 0x105609 (LoadPre 0x105609 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x4a)) s (0x105609 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x105609 6 1 (.sib 3 (some 12) 1 (.d8 0x4a))) (Reg.operands [.gpr 1, .gpr 3, .gpr 12] [])) #v[205, 3, 117]
    (.letOp (n := 209) (.out 0x10560f (xorR32R32Effect 0x10560f 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[201, 207]
    (.letOp (n := 210) (.exec 0x10560f (fun s => s.RIP = 0x10560f) (xorR32R32Effect 0x10560f 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[201, 207]
    (.letOp (n := 211) (.exec 0x105611 (StorePre 0x105611 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xa)) s (0x105611 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105611 5 2 (.sib 4 none 0 (.d8 0xa))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[209, 4]
    (.letOp (n := 212) (.out 0x105616 (rolR16Effect 0x105616 5 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[121]
    (.letOp (n := 213) (.exec 0x105616 (fun s => s.RIP = 0x105616) (rolR16Effect 0x105616 5 8 8) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[121]
    (.letOp (n := 214) (.out 0x10561b (xorR16M16Effect 0x10561b 6 8 (.sib 3 (some 12) 1 (.d8 0x4c))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 3, .gpr 12] []) (.reg (.gpr 8))) #v[212, 3, 117]
    (.letOp (n := 215) (.exec 0x10561b (LoadPre 0x10561b (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x4c)) s (0x10561b + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x10561b 6 8 (.sib 3 (some 12) 1 (.d8 0x4c))) (Reg.operands [.gpr 8, .gpr 3, .gpr 12] [])) #v[212, 3, 117]
    (.letOp (n := 216) (.out 0x105621 (xorR32M32LowEffect 0x105621 7 (.sib 4 none 0 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 4] []) (.reg (.gpr 7))) #v[199, 4]
    (.letOp (n := 217) (.exec 0x105621 (LoadPre 0x105621 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x105621 + BitVec.ofNat 64 4)) 4) (xorR32M32LowEffect 0x105621 7 (.sib 4 none 0 (.d8 0x1c))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[199, 4]
    (.letOp (n := 218) (.out 0x105625 (xorR32R32Effect 0x105625 3 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 8] []) (.reg (.gpr 7))) #v[216, 214]
    (.letOp (n := 219) (.exec 0x105625 (fun s => s.RIP = 0x105625) (xorR32R32Effect 0x105625 3 7 8) (Reg.operands [.gpr 7, .gpr 8] [])) #v[216, 214]
    (.letOp (n := 220) (.exec 0x105628 (StorePre 0x105628 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x105628 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105628 5 7 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[218, 4]
    (.letOp (n := 221) (.out 0x10562d (addR64Imm8Effect 0x10562d 12 0x20) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[117]
    (.letOp (n := 222) (.exec 0x10562d (fun s => s.RIP = 0x10562d) (addR64Imm8Effect 0x10562d 12 0x20) (Reg.operands [.gpr 12] [])) #v[117]
    (.terminate (.br ⟨.l105180, RegMap.args [(0, 151), (1, 207), (2, 209), (3, 3), (4, 4), (5, 147), (6, 108), (7, 218), (8, 214), (9, 192), (10, 153), (11, 165), (12, 221), (13, 170), (14, 174), (15, 179), (22, 22), (39, 39), (50, 50), (51, 51)] 223⟩)))))))))))))))))))))

def bytes_l1054d6_4 : List UInt8 :=
  [0x89, 0xF9, 0x66, 0xC1, 0xC1, 0x08, 0x66, 0x42, 0x33, 0x4C, 0x63, 0x4A, 0x31, 0xCA, 0x66, 0x89,
    0x54, 0x24, 0x0A, 0x66, 0x41, 0xC1, 0xC0, 0x08, 0x66, 0x46, 0x33, 0x44, 0x63, 0x4C, 0x33, 0x7C,
    0x24, 0x1C, 0x44, 0x31, 0xC7, 0x66, 0x89, 0x7C, 0x24, 0x0C, 0x49, 0x83, 0xC4, 0x20, 0xE9, 0x4A,
    0xFB, 0xFF, 0xFF]

theorem code_l1054d6_4 : ∀ x ∈ codeRange 0x105603 bytes_l1054d6_4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5603 51 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1054d6_3 : Block Op Label signature Reg.count 167 :=
  .letOp (n := 167) (.exec 0x1055ae (StorePre 0x1055ae 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2)) s (0x1055ae + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x1055ae 6 11 (.sib 4 none 0 (.d8 0x2))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[165, 4]
    (.letOp (n := 168) (.out 0x1055b4 (rolR16Effect 0x1055b4 5 13 8) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[129]
    (.letOp (n := 169) (.exec 0x1055b4 (fun s => s.RIP = 0x1055b4) (rolR16Effect 0x1055b4 5 13 8) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[129]
    (.letOp (n := 170) (.out 0x1055b9 (xorR16M16Effect 0x1055b9 6 13 (.sib 3 (some 12) 1 (.d8 0x44))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 3, .gpr 12] []) (.reg (.gpr 13))) #v[168, 3, 117]
    (.letOp (n := 171) (.exec 0x1055b9 (LoadPre 0x1055b9 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x44)) s (0x1055b9 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x1055b9 6 13 (.sib 3 (some 12) 1 (.d8 0x44))) (Reg.operands [.gpr 13, .gpr 3, .gpr 12] [])) #v[168, 3, 117]
    (.letOp (n := 172) (.out 0x1055bf (xorR32M32Effect 0x1055bf 14 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 4] []) (.reg (.gpr 14))) #v[102, 4]
    (.letOp (n := 173) (.exec 0x1055bf (LoadPre 0x1055bf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1055bf + BitVec.ofNat 64 5)) 4) (xorR32M32Effect 0x1055bf 14 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[102, 4]
    (.letOp (n := 174) (.out 0x1055c4 (xorR32R32Effect 0x1055c4 3 14 13) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 13] []) (.reg (.gpr 14))) #v[172, 170]
    (.letOp (n := 175) (.exec 0x1055c4 (fun s => s.RIP = 0x1055c4) (xorR32R32Effect 0x1055c4 3 14 13) (Reg.operands [.gpr 14, .gpr 13] [])) #v[172, 170]
    (.letOp (n := 176) (.out 0x1055c7 (rolR16Effect 0x1055c7 5 15 8) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[133]
    (.letOp (n := 177) (.exec 0x1055c7 (fun s => s.RIP = 0x1055c7) (rolR16Effect 0x1055c7 5 15 8) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[133]
    (.letOp (n := 178) (.exec 0x1055cc (StorePre 0x1055cc 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x1055cc + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x1055cc 6 14 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[174, 4]
    (.letOp (n := 179) (.out 0x1055d2 (xorR16M16Effect 0x1055d2 6 15 (.sib 3 (some 12) 1 (.d8 0x46))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 3, .gpr 12] []) (.reg (.gpr 15))) #v[176, 3, 117]
    (.letOp (n := 180) (.exec 0x1055d2 (LoadPre 0x1055d2 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x46)) s (0x1055d2 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x1055d2 6 15 (.sib 3 (some 12) 1 (.d8 0x46))) (Reg.operands [.gpr 15, .gpr 3, .gpr 12] [])) #v[176, 3, 117]
    (.letOp (n := 181) (.out 0x1055d8 (xorR32R32Effect 0x1055d8 3 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 15] []) (.reg (.gpr 2))) #v[143, 179]
    (.letOp (n := 182) (.exec 0x1055d8 (fun s => s.RIP = 0x1055d8) (xorR32R32Effect 0x1055d8 3 2 15) (Reg.operands [.gpr 2, .gpr 15] [])) #v[143, 179]
    (.letOp (n := 183) (.exec 0x1055db (StorePre 0x1055db 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6)) s (0x1055db + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1055db 5 2 (.sib 4 none 0 (.d8 0x6))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[181, 4]
    (.letOp (n := 184) (.out 0x1055e0 (movR32M32LowEffect 0x1055e0 2 (.sib 4 none 0 (.d8 0x14))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 185) (.exec 0x1055e0 (LoadPre 0x1055e0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x1055e0 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1055e0 2 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 186) (.out 0x1055e4 (movR32R32Effect 0x1055e4 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[184]
    (.letOp (n := 187) (.exec 0x1055e4 (fun s => s.RIP = 0x1055e4) (movR32R32Effect 0x1055e4 2 1 2) (Reg.operands [.gpr 2] [])) #v[184]
    (.letOp (n := 188) (.out 0x1055e6 (rolR16Effect 0x1055e6 4 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[186]
    (.letOp (n := 189) (.exec 0x1055e6 (fun s => s.RIP = 0x1055e6) (rolR16Effect 0x1055e6 4 1 8) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[186]
    (.letOp (n := 190) (.out 0x1055ea (xorR16M16Effect 0x1055ea 6 1 (.sib 3 (some 12) 1 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 3, .gpr 12] []) (.reg (.gpr 1))) #v[188, 3, 117]
    (.letOp (n := 191) (.exec 0x1055ea (LoadPre 0x1055ea (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x48)) s (0x1055ea + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x1055ea 6 1 (.sib 3 (some 12) 1 (.d8 0x48))) (Reg.operands [.gpr 1, .gpr 3, .gpr 12] [])) #v[188, 3, 117]
    (.letOp (n := 192) (.out 0x1055f0 (xorR32R32Effect 0x1055f0 3 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1] []) (.reg (.gpr 9))) #v[145, 190]
    (.letOp (n := 193) (.exec 0x1055f0 (fun s => s.RIP = 0x1055f0) (xorR32R32Effect 0x1055f0 3 9 1) (Reg.operands [.gpr 9, .gpr 1] [])) #v[145, 190]
    (.letOp (n := 194) (.exec 0x1055f3 (StorePre 0x1055f3 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1055f3 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x1055f3 6 9 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[192, 4]
    (.letOp (n := 195) (.out 0x1055f9 (movR32R32Effect 0x1055f9 2 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 7] []) (.reg (.gpr 1))) #v[155]
    (.letOp (n := 196) (.exec 0x1055f9 (fun s => s.RIP = 0x1055f9) (movR32R32Effect 0x1055f9 2 1 7) (Reg.operands [.gpr 7] [])) #v[155]
    (.letOp (n := 197) (.out 0x1055fb (rolR16Effect 0x1055fb 4 1 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[195]
    (.letOp (n := 198) (.exec 0x1055fb (fun s => s.RIP = 0x1055fb) (rolR16Effect 0x1055fb 4 1 12) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[195]
    (.letOp (n := 199) (.out 0x1055ff (xorR32R32Effect 0x1055ff 2 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1] []) (.reg (.gpr 7))) #v[155, 197]
    (.letOp (n := 200) (.exec 0x1055ff (fun s => s.RIP = 0x1055ff) (xorR32R32Effect 0x1055ff 2 7 1) (Reg.operands [.gpr 7, .gpr 1] [])) #v[155, 197]
    (.letOp (n := 201) (.out 0x105601 (xorR32R32Effect 0x105601 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[184, 197]
    (.letOp (n := 202) (.exec 0x105601 (fun s => s.RIP = 0x105601) (xorR32R32Effect 0x105601 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[184, 197]
    (b_l1054d6_4))))))))))))))))))))))))))))))))))))

def bytes_l1054d6_3 : List UInt8 :=
  [0x66, 0x44, 0x89, 0x5C, 0x24, 0x02, 0x66, 0x41, 0xC1, 0xC5, 0x08, 0x66, 0x46, 0x33, 0x6C, 0x63,
    0x44, 0x44, 0x33, 0x74, 0x24, 0x18, 0x45, 0x31, 0xEE, 0x66, 0x41, 0xC1, 0xC7, 0x08, 0x66, 0x44,
    0x89, 0x74, 0x24, 0x04, 0x66, 0x46, 0x33, 0x7C, 0x63, 0x46, 0x44, 0x31, 0xFA, 0x66, 0x89, 0x54,
    0x24, 0x06, 0x8B, 0x54, 0x24, 0x14, 0x89, 0xD1, 0x66, 0xC1, 0xC1, 0x08, 0x66, 0x42, 0x33, 0x4C,
    0x63, 0x48, 0x41, 0x31, 0xC9, 0x66, 0x44, 0x89, 0x4C, 0x24, 0x08, 0x89, 0xF9, 0x66, 0xC1, 0xC1,
    0x0C, 0x31, 0xCF, 0x31, 0xCA] ++ bytes_l1054d6_4

theorem code_l1054d6_3 : ∀ x ∈ codeRange 0x1055ae bytes_l1054d6_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x55ae 85 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1054d6_4

@[cfg_block] def b_l1054d6_2 : Block Op Label signature Reg.count 129 :=
  .letOp (n := 129) (.out 0x105566 (movR32R32Effect 0x105566 3 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[104]
    (.letOp (n := 130) (.exec 0x105566 (fun s => s.RIP = 0x105566) (movR32R32Effect 0x105566 3 13 2) (Reg.operands [.gpr 2] [])) #v[104]
    (.letOp (n := 131) (.out 0x105569 (xorR32R32Effect 0x105569 2 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[104, 108]
    (.letOp (n := 132) (.exec 0x105569 (fun s => s.RIP = 0x105569) (xorR32R32Effect 0x105569 2 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[104, 108]
    (.letOp (n := 133) (.out 0x10556b (movR32R32Effect 0x10556b 3 15 9) (EffectPart.reads (.reg (.gpr 15)) [.gpr 9] []) (.reg (.gpr 15))) #v[106]
    (.letOp (n := 134) (.exec 0x10556b (fun s => s.RIP = 0x10556b) (movR32R32Effect 0x10556b 3 15 9) (Reg.operands [.gpr 9] [])) #v[106]
    (.letOp (n := 135) (.out 0x10556e (xorR32R32Effect 0x10556e 3 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1] []) (.reg (.gpr 9))) #v[106, 110]
    (.letOp (n := 136) (.exec 0x10556e (fun s => s.RIP = 0x10556e) (xorR32R32Effect 0x10556e 3 9 1) (Reg.operands [.gpr 9, .gpr 1] [])) #v[106, 110]
    (.letOp (n := 137) (.out 0x105571 (rolR16Effect 0x105571 4 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[125]
    (.letOp (n := 138) (.exec 0x105571 (fun s => s.RIP = 0x105571) (rolR16Effect 0x105571 4 7 8) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[125]
    (.letOp (n := 139) (.out 0x105575 (xorR32R32Effect 0x105575 3 10 5) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 5] []) (.reg (.gpr 10))) #v[61, 119]
    (.letOp (n := 140) (.exec 0x105575 (fun s => s.RIP = 0x105575) (xorR32R32Effect 0x105575 3 10 5) (Reg.operands [.gpr 10, .gpr 5] [])) #v[61, 119]
    (.letOp (n := 141) (.out 0x105578 (xorR32R32Effect 0x105578 3 11 5) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 5] []) (.reg (.gpr 11))) #v[127, 119]
    (.letOp (n := 142) (.exec 0x105578 (fun s => s.RIP = 0x105578) (xorR32R32Effect 0x105578 3 11 5) (Reg.operands [.gpr 11, .gpr 5] [])) #v[127, 119]
    (.letOp (n := 143) (.out 0x10557b (xorR32R32Effect 0x10557b 2 2 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 5] []) (.reg (.gpr 2))) #v[131, 119]
    (.letOp (n := 144) (.exec 0x10557b (fun s => s.RIP = 0x10557b) (xorR32R32Effect 0x10557b 2 2 5) (Reg.operands [.gpr 2, .gpr 5] [])) #v[131, 119]
    (.letOp (n := 145) (.out 0x10557d (xorR32R32Effect 0x10557d 3 9 5) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 5] []) (.reg (.gpr 9))) #v[135, 119]
    (.letOp (n := 146) (.exec 0x10557d (fun s => s.RIP = 0x10557d) (xorR32R32Effect 0x10557d 3 9 5) (Reg.operands [.gpr 9, .gpr 5] [])) #v[135, 119]
    (.letOp (n := 147) (.out 0x105580 (rolR16Effect 0x105580 4 5 8) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[119]
    (.letOp (n := 148) (.exec 0x105580 (fun s => s.RIP = 0x105580) (rolR16Effect 0x105580 4 5 8) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[119]
    (.letOp (n := 149) (.out 0x105584 (xorR16M16Effect 0x105584 6 7 (.sib 3 (some 12) 1 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 3, .gpr 12] []) (.reg (.gpr 7))) #v[137, 3, 117]
    (.letOp (n := 150) (.exec 0x105584 (LoadPre 0x105584 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x40)) s (0x105584 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x105584 6 7 (.sib 3 (some 12) 1 (.d8 0x40))) (Reg.operands [.gpr 7, .gpr 3, .gpr 12] [])) #v[137, 3, 117]
    (.letOp (n := 151) (.out 0x10558a (xorR32R32Effect 0x10558a 2 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[123, 147]
    (.letOp (n := 152) (.exec 0x10558a (fun s => s.RIP = 0x10558a) (xorR32R32Effect 0x10558a 2 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[123, 147]
    (.letOp (n := 153) (.out 0x10558c (xorR32R32Effect 0x10558c 3 10 7) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 7] []) (.reg (.gpr 10))) #v[139, 149]
    (.letOp (n := 154) (.exec 0x10558c (fun s => s.RIP = 0x10558c) (xorR32R32Effect 0x10558c 3 10 7) (Reg.operands [.gpr 10, .gpr 7] [])) #v[139, 149]
    (.letOp (n := 155) (.out 0x10558f (movzxR32M16Effect 0x10558f 5 7 (.sib 4 none 0 (.d8 0xa))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 156) (.exec 0x10558f (LoadPre 0x10558f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xa)) s (0x10558f + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x10558f 5 7 (.sib 4 none 0 (.d8 0xa))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 157) (.exec 0x105594 (StorePre 0x105594 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x105594 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105594 5 0 (.sib 4 none 0 (.d8 0xe))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[151, 4]
    (.letOp (n := 158) (.exec 0x105599 (StorePre 0x105599 5 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x105599 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105599 5 10 (.sib 4 none 0 .none)) (Reg.operands [.gpr 10, .gpr 4] [])) #v[153, 4]
    (.letOp (n := 159) (.out 0x10559e (movR32R32Effect 0x10559e 3 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[102]
    (.letOp (n := 160) (.exec 0x10559e (fun s => s.RIP = 0x10559e) (movR32R32Effect 0x10559e 3 1 14) (Reg.operands [.gpr 14] [])) #v[102]
    (.letOp (n := 161) (.out 0x1055a1 (rolR16Effect 0x1055a1 4 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[159]
    (.letOp (n := 162) (.exec 0x1055a1 (fun s => s.RIP = 0x1055a1) (rolR16Effect 0x1055a1 4 1 8) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[159]
    (.letOp (n := 163) (.out 0x1055a5 (xorR16M16Effect 0x1055a5 6 1 (.sib 3 (some 12) 1 (.d8 0x42))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 3, .gpr 12] []) (.reg (.gpr 1))) #v[161, 3, 117]
    (.letOp (n := 164) (.exec 0x1055a5 (LoadPre 0x1055a5 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x42)) s (0x1055a5 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x1055a5 6 1 (.sib 3 (some 12) 1 (.d8 0x42))) (Reg.operands [.gpr 1, .gpr 3, .gpr 12] [])) #v[161, 3, 117]
    (.letOp (n := 165) (.out 0x1055ab (xorR32R32Effect 0x1055ab 3 11 1) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 1] []) (.reg (.gpr 11))) #v[141, 163]
    (.letOp (n := 166) (.exec 0x1055ab (fun s => s.RIP = 0x1055ab) (xorR32R32Effect 0x1055ab 3 11 1) (Reg.operands [.gpr 11, .gpr 1] [])) #v[141, 163]
    (b_l1054d6_3))))))))))))))))))))))))))))))))))))))

def bytes_l1054d6_2 : List UInt8 :=
  [0x41, 0x89, 0xD5, 0x31, 0xF2, 0x45, 0x89, 0xCF, 0x41, 0x31, 0xC9, 0x66, 0xC1, 0xC7, 0x08, 0x41,
    0x31, 0xEA, 0x41, 0x31, 0xEB, 0x31, 0xEA, 0x41, 0x31, 0xE9, 0x66, 0xC1, 0xC5, 0x08, 0x66, 0x42,
    0x33, 0x7C, 0x63, 0x40, 0x31, 0xE8, 0x41, 0x31, 0xFA, 0x0F, 0xB7, 0x7C, 0x24, 0x0A, 0x66, 0x89,
    0x44, 0x24, 0x0E, 0x66, 0x44, 0x89, 0x14, 0x24, 0x44, 0x89, 0xF1, 0x66, 0xC1, 0xC1, 0x08, 0x66,
    0x42, 0x33, 0x4C, 0x63, 0x42, 0x41, 0x31, 0xCB] ++ bytes_l1054d6_3

theorem code_l1054d6_2 : ∀ x ∈ codeRange 0x105566 bytes_l1054d6_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x5566 72 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1054d6_3

@[cfg_block] def b_l1054d6_1 : Block Op Label signature Reg.count 92 :=
  .letOp (n := 92) (.exec 0x105527 (StorePre 0x105527 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x105527 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x105527 12 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[12, 4]
    (.letOp (n := 93) (.out 0x10552c (movR32R32Effect 0x10552c 3 12 7) (EffectPart.reads (.reg (.gpr 12)) [.gpr 7] []) (.reg (.gpr 12))) #v[90]
    (.letOp (n := 94) (.exec 0x10552c (fun s => s.RIP = 0x10552c) (movR32R32Effect 0x10552c 3 12 7) (Reg.operands [.gpr 7] [])) #v[90]
    (.letOp (n := 95) (.exec 0x10552f (StorePre 0x10552f 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x10552f + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x10552f 7 (.sib 4 none 0 (.d8 0x1c))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[90, 4]
    (.letOp (n := 96) (.out 0x105533 (movR32R32Effect 0x105533 2 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[82]
    (.letOp (n := 97) (.exec 0x105533 (fun s => s.RIP = 0x105533) (movR32R32Effect 0x105533 2 7 5) (Reg.operands [.gpr 5] [])) #v[82]
    (.letOp (n := 98) (.out 0x105535 (rolR16Effect 0x105535 4 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[96]
    (.letOp (n := 99) (.exec 0x105535 (fun s => s.RIP = 0x105535) (rolR16Effect 0x105535 4 7 12) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[96]
    (.letOp (n := 100) (.out 0x105539 (xorR32R32Effect 0x105539 3 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 10] []) (.reg (.gpr 11))) #v[53, 61]
    (.letOp (n := 101) (.exec 0x105539 (fun s => s.RIP = 0x105539) (xorR32R32Effect 0x105539 3 11 10) (Reg.operands [.gpr 11, .gpr 10] [])) #v[53, 61]
    (.letOp (n := 102) (.out 0x10553c (xorR32R32Effect 0x10553c 3 14 13) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 13] []) (.reg (.gpr 14))) #v[57, 67]
    (.letOp (n := 103) (.exec 0x10553c (fun s => s.RIP = 0x10553c) (xorR32R32Effect 0x10553c 3 14 13) (Reg.operands [.gpr 14, .gpr 13] [])) #v[57, 67]
    (.letOp (n := 104) (.out 0x10553f (xorR32R32Effect 0x10553f 2 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[55, 73]
    (.letOp (n := 105) (.exec 0x10553f (fun s => s.RIP = 0x10553f) (xorR32R32Effect 0x10553f 2 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[55, 73]
    (.letOp (n := 106) (.out 0x105541 (xorR32R32Effect 0x105541 3 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1] []) (.reg (.gpr 9))) #v[63, 80]
    (.letOp (n := 107) (.exec 0x105541 (fun s => s.RIP = 0x105541) (xorR32R32Effect 0x105541 3 9 1) (Reg.operands [.gpr 9, .gpr 1] [])) #v[63, 80]
    (.letOp (n := 108) (.out 0x105544 (movR32R32Effect 0x105544 2 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 1] []) (.reg (.gpr 6))) #v[80]
    (.letOp (n := 109) (.exec 0x105544 (fun s => s.RIP = 0x105544) (movR32R32Effect 0x105544 2 6 1) (Reg.operands [.gpr 1] [])) #v[80]
    (.letOp (n := 110) (.out 0x105546 (movR32R32Effect 0x105546 3 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 15] []) (.reg (.gpr 1))) #v[86]
    (.letOp (n := 111) (.exec 0x105546 (fun s => s.RIP = 0x105546) (movR32R32Effect 0x105546 3 1 15) (Reg.operands [.gpr 15] [])) #v[86]
    (.letOp (n := 112) (.out 0x105549 (xorR32R32Effect 0x105549 3 8 15) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 15] []) (.reg (.gpr 8))) #v[69, 86]
    (.letOp (n := 113) (.exec 0x105549 (fun s => s.RIP = 0x105549) (xorR32R32Effect 0x105549 3 8 15) (Reg.operands [.gpr 8, .gpr 15] [])) #v[69, 86]
    (.letOp (n := 114) (.exec 0x10554c (StorePre 0x10554c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x10554c + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x10554c 8 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[112, 4]
    (.letOp (n := 115) (.out 0x105551 (xorR32R32Effect 0x105551 3 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 12] []) (.reg (.gpr 0))) #v[76, 93]
    (.letOp (n := 116) (.exec 0x105551 (fun s => s.RIP = 0x105551) (xorR32R32Effect 0x105551 3 0 12) (Reg.operands [.gpr 0, .gpr 12] [])) #v[76, 93]
    (.letOp (n := 117) (.out 0x105554 (movR64M64Effect 0x105554 12 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 118) (.exec 0x105554 (LoadPre 0x105554 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x105554 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x105554 12 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 119) (.out 0x105559 (xorR32R32Effect 0x105559 2 5 7) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 7] []) (.reg (.gpr 5))) #v[82, 98]
    (.letOp (n := 120) (.exec 0x105559 (fun s => s.RIP = 0x105559) (xorR32R32Effect 0x105559 2 5 7) (Reg.operands [.gpr 5, .gpr 7] [])) #v[82, 98]
    (.letOp (n := 121) (.out 0x10555b (movR32R32Effect 0x10555b 3 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[115]
    (.letOp (n := 122) (.exec 0x10555b (fun s => s.RIP = 0x10555b) (movR32R32Effect 0x10555b 3 8 0) (Reg.operands [.gpr 0] [])) #v[115]
    (.letOp (n := 123) (.out 0x10555e (xorR32R32Effect 0x10555e 2 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[115, 98]
    (.letOp (n := 124) (.exec 0x10555e (fun s => s.RIP = 0x10555e) (xorR32R32Effect 0x10555e 2 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[115, 98]
    (.letOp (n := 125) (.out 0x105560 (movR32R32Effect 0x105560 3 7 11) (EffectPart.reads (.reg (.gpr 7)) [.gpr 11] []) (.reg (.gpr 7))) #v[100]
    (.letOp (n := 126) (.exec 0x105560 (fun s => s.RIP = 0x105560) (movR32R32Effect 0x105560 3 7 11) (Reg.operands [.gpr 11] [])) #v[100]
    (.letOp (n := 127) (.out 0x105563 (xorR32R32Effect 0x105563 3 11 13) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 13] []) (.reg (.gpr 11))) #v[100, 67]
    (.letOp (n := 128) (.exec 0x105563 (fun s => s.RIP = 0x105563) (xorR32R32Effect 0x105563 3 11 13) (Reg.operands [.gpr 11, .gpr 13] [])) #v[100, 67]
    (b_l1054d6_2)))))))))))))))))))))))))))))))))))))

def bytes_l1054d6_1 : List UInt8 :=
  [0x4C, 0x89, 0x64, 0x24, 0x20, 0x41, 0x89, 0xFC, 0x89, 0x7C, 0x24, 0x1C, 0x89, 0xEF, 0x66, 0xC1,
    0xC7, 0x0C, 0x45, 0x31, 0xD3, 0x45, 0x31, 0xEE, 0x31, 0xF2, 0x41, 0x31, 0xC9, 0x89, 0xCE, 0x44,
    0x89, 0xF9, 0x45, 0x31, 0xF8, 0x44, 0x89, 0x44, 0x24, 0x14, 0x44, 0x31, 0xE0, 0x4C, 0x8B, 0x64,
    0x24, 0x20, 0x31, 0xFD, 0x41, 0x89, 0xC0, 0x31, 0xF8, 0x44, 0x89, 0xDF, 0x45, 0x31, 0xEB] ++ bytes_l1054d6_2

theorem code_l1054d6_1 : ∀ x ∈ codeRange 0x105527 bytes_l1054d6_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x5527 63 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1054d6_2

@[cfg_block] def b_l1054d6 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1054d6 (movR32M32Effect 0x1054d6 11 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 54) (.exec 0x1054d6 (LoadPre 0x1054d6 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1054d6 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x1054d6 11 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1054da (movR32M32LowEffect 0x1054da 2 (.sib 4 none 0 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 56) (.exec 0x1054da (LoadPre 0x1054da (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x1054da + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1054da 2 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1054de (movzxR32M16Effect 0x1054de 6 14 (.sib 4 none 0 (.d8 0x2))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 58) (.exec 0x1054de (LoadPre 0x1054de (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2)) s (0x1054de + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x1054de 6 14 (.sib 4 none 0 (.d8 0x2))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x1054e4 (movR32R32Effect 0x1054e4 3 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 11] []) (.reg (.gpr 10))) #v[53]
    (.letOp (n := 60) (.exec 0x1054e4 (fun s => s.RIP = 0x1054e4) (movR32R32Effect 0x1054e4 3 10 11) (Reg.operands [.gpr 11] [])) #v[53]
    (.letOp (n := 61) (.out 0x1054e7 (rolR16Effect 0x1054e7 5 10 12) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[59]
    (.letOp (n := 62) (.exec 0x1054e7 (fun s => s.RIP = 0x1054e7) (rolR16Effect 0x1054e7 5 10 12) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[59]
    (.letOp (n := 63) (.out 0x1054ec (movzxR32M16Effect 0x1054ec 6 9 (.sib 4 none 0 (.d8 0x6))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 64) (.exec 0x1054ec (LoadPre 0x1054ec (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6)) s (0x1054ec + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x1054ec 6 9 (.sib 4 none 0 (.d8 0x6))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x1054f2 (movR32R32Effect 0x1054f2 3 13 14) (EffectPart.reads (.reg (.gpr 13)) [.gpr 14] []) (.reg (.gpr 13))) #v[57]
    (.letOp (n := 66) (.exec 0x1054f2 (fun s => s.RIP = 0x1054f2) (movR32R32Effect 0x1054f2 3 13 14) (Reg.operands [.gpr 14] [])) #v[57]
    (.letOp (n := 67) (.out 0x1054f5 (rolR16Effect 0x1054f5 5 13 12) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[65]
    (.letOp (n := 68) (.exec 0x1054f5 (fun s => s.RIP = 0x1054f5) (rolR16Effect 0x1054f5 5 13 12) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[65]
    (.letOp (n := 69) (.out 0x1054fa (movR32M32Effect 0x1054fa 8 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 70) (.exec 0x1054fa (LoadPre 0x1054fa (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1054fa + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x1054fa 8 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.out 0x1054ff (movR32R32Effect 0x1054ff 2 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[55]
    (.letOp (n := 72) (.exec 0x1054ff (fun s => s.RIP = 0x1054ff) (movR32R32Effect 0x1054ff 2 6 2) (Reg.operands [.gpr 2] [])) #v[55]
    (.letOp (n := 73) (.out 0x105501 (rolR16Effect 0x105501 4 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[71]
    (.letOp (n := 74) (.exec 0x105501 (fun s => s.RIP = 0x105501) (rolR16Effect 0x105501 4 6 12) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[71]
    (.letOp (n := 75) (.exec 0x105505 (StorePre 0x105505 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x105505 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x105505 6 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[73, 4]
    (.letOp (n := 76) (.out 0x105509 (movR32M32LowEffect 0x105509 0 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 77) (.exec 0x105509 (LoadPre 0x105509 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x105509 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x105509 0 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 78) (.out 0x10550d (movR32R32Effect 0x10550d 3 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 9] []) (.reg (.gpr 1))) #v[63]
    (.letOp (n := 79) (.exec 0x10550d (fun s => s.RIP = 0x10550d) (movR32R32Effect 0x10550d 3 1 9) (Reg.operands [.gpr 9] [])) #v[63]
    (.letOp (n := 80) (.out 0x105510 (rolR16Effect 0x105510 4 1 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[78]
    (.letOp (n := 81) (.exec 0x105510 (fun s => s.RIP = 0x105510) (rolR16Effect 0x105510 4 1 12) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[78]
    (.letOp (n := 82) (.out 0x105514 (movzxR32M16Effect 0x105514 5 5 (.sib 4 none 0 (.d8 0xe))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 83) (.exec 0x105514 (LoadPre 0x105514 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x105514 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105514 5 5 (.sib 4 none 0 (.d8 0xe))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 84) (.out 0x105519 (movR32R32Effect 0x105519 3 15 8) (EffectPart.reads (.reg (.gpr 15)) [.gpr 8] []) (.reg (.gpr 15))) #v[69]
    (.letOp (n := 85) (.exec 0x105519 (fun s => s.RIP = 0x105519) (movR32R32Effect 0x105519 3 15 8) (Reg.operands [.gpr 8] [])) #v[69]
    (.letOp (n := 86) (.out 0x10551c (rolR16Effect 0x10551c 5 15 12) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[84]
    (.letOp (n := 87) (.exec 0x10551c (fun s => s.RIP = 0x10551c) (rolR16Effect 0x10551c 5 15 12) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[84]
    (.letOp (n := 88) (.out 0x105521 (movR32R32Effect 0x105521 2 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[76]
    (.letOp (n := 89) (.exec 0x105521 (fun s => s.RIP = 0x105521) (movR32R32Effect 0x105521 2 7 0) (Reg.operands [.gpr 0] [])) #v[76]
    (.letOp (n := 90) (.out 0x105523 (rolR16Effect 0x105523 4 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[88]
    (.letOp (n := 91) (.exec 0x105523 (fun s => s.RIP = 0x105523) (rolR16Effect 0x105523 4 7 12) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[88]
    (b_l1054d6_1)))))))))))))))))))))))))))))))))))))))

def bytes_l1054d6 : List UInt8 :=
  [0x44, 0x8B, 0x1C, 0x24, 0x8B, 0x54, 0x24, 0x04, 0x44, 0x0F, 0xB7, 0x74, 0x24, 0x02, 0x45, 0x89,
    0xDA, 0x66, 0x41, 0xC1, 0xC2, 0x0C, 0x44, 0x0F, 0xB7, 0x4C, 0x24, 0x06, 0x45, 0x89, 0xF5, 0x66,
    0x41, 0xC1, 0xC5, 0x0C, 0x44, 0x8B, 0x44, 0x24, 0x08, 0x89, 0xD6, 0x66, 0xC1, 0xC6, 0x0C, 0x89,
    0x74, 0x24, 0x18, 0x8B, 0x44, 0x24, 0x0C, 0x44, 0x89, 0xC9, 0x66, 0xC1, 0xC1, 0x0C, 0x0F, 0xB7,
    0x6C, 0x24, 0x0E, 0x45, 0x89, 0xC7, 0x66, 0x41, 0xC1, 0xC7, 0x0C, 0x89, 0xC7, 0x66, 0xC1, 0xC7,
    0x0C] ++ bytes_l1054d6_1

theorem code_l1054d6 : ∀ x ∈ codeRange 0x1054d6 bytes_l1054d6, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x54d6 81 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1054d6_1

end AesGcm.Proofs.Machine.LIR
