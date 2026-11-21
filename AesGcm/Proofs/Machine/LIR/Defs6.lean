import AesGcm.Proofs.Machine.Instructions.Memory16
import AesGcm.Proofs.Machine.Instructions.HighByteStore
import AesGcm.Proofs.Machine.LIR.Labels
import AesGcm.Proofs.Copied.X86Proofs.CFG.EvalAttr
import AesGcm.Proofs.Copied.X86Proofs.Lift.Generated.Footprints

namespace AesGcm.Proofs.Machine.LIR

open AesGcm.Proofs.Machine.Instructions
open X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift

@[cfg_block] def b_l1099cc : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1099cc (movR64R64Effect 0x1099cc 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 54) (.exec 0x1099cc (fun s => s.RIP = 0x1099cc) (movR64R64Effect 0x1099cc 6 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.out 0x1099cf (addR64Imm8Effect 0x1099cf 5 0xc0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5] []) (.reg (.gpr 5))) #v[5]
    (.letOp (n := 56) (.out 0x1099cf (addR64Imm8Effect 0x1099cf 5 0xc0) (EffectPart.reads (.flag .ZF) [.gpr 5] []) (.flag .ZF)) #v[5]
    (.letOp (n := 57) (.exec 0x1099cf (fun s => s.RIP = 0x1099cf) (addR64Imm8Effect 0x1099cf 5 0xc0) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 58) (.pure (condOp 5)) #v[56]
    (.terminate (.condBr (Fin.last 58) ⟨.l1099c0, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (6, 53), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩ ⟨.l1099d5, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (6, 53), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l1099cc : List UInt8 :=
  [0x4C, 0x89, 0xFE, 0x48, 0x83, 0xC5, 0xC0, 0x75, 0xEB]

theorem code_l1099cc : ∀ x ∈ codeRange 0x1099cc bytes_l1099cc, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x99cc 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1099d5 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1099d5 (andR64Imm8Effect 0x1099d5 13 0x30) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[13]
    (.letOp (n := 54) (.out 0x1099d5 (andR64Imm8Effect 0x1099d5 13 0x30) (EffectPart.reads (.flag .ZF) [.gpr 13] []) (.flag .ZF)) #v[13]
    (.letOp (n := 55) (.exec 0x1099d5 (fun s => s.RIP = 0x1099d5) (andR64Imm8Effect 0x1099d5 13 0x30) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 56) (.pure (condOp 4)) #v[54]
    (.terminate (.condBr (Fin.last 56) ⟨.l109aaa, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 53), (14, 14), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩ ⟨.l1099df, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 53), (14, 14), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l1099d5 : List UInt8 :=
  [0x49, 0x83, 0xE5, 0x30, 0x0F, 0x84, 0xCB, 0x00, 0x00, 0x00]

theorem code_l1099d5 : ∀ x ∈ codeRange 0x1099d5 bytes_l1099d5, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x99d5 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1099df : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1099df (movR64Imm64Effect 0x1099df 0 0x7fffffffffffffc) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 54) (.exec 0x1099df (fun s => s.RIP = 0x1099df) (movR64Imm64Effect 0x1099df 0 0x7fffffffffffffc) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x1099e9 (movR64M64Effect 0x1099e9 1 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x1099e9 (LoadPre 0x1099e9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1099e9 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1099e9 1 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1099ee (andR64R64Effect 0x1099ee 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[55, 53]
    (.letOp (n := 58) (.exec 0x1099ee (fun s => s.RIP = 0x1099ee) (andR64R64Effect 0x1099ee 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[55, 53]
    (.letOp (n := 59) (.out 0x1099f1 (shlR64Effect 0x1099f1 4 1 4) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[57]
    (.letOp (n := 60) (.exec 0x1099f1 (fun s => s.RIP = 0x1099f1) (shlR64Effect 0x1099f1 4 1 4) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[57]
    (.letOp (n := 61) (.out 0x1099f5 (addR64R64Effect 0x1099f5 3 1) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 1] []) (.reg (.gpr 3))) #v[3, 59]
    (.letOp (n := 62) (.exec 0x1099f5 (fun s => s.RIP = 0x1099f5) (addR64R64Effect 0x1099f5 3 1) (Reg.operands [.gpr 3, .gpr 1] [])) #v[3, 59]
    (.letOp (n := 63) (.out 0x1099f8 (xorR32R32Effect 0x1099f8 3 12 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 12] []) (.reg (.gpr 12))) #v[12, 12]
    (.letOp (n := 64) (.exec 0x1099f8 (fun s => s.RIP = 0x1099f8) (xorR32R32Effect 0x1099f8 3 12 12) (Reg.operands [.gpr 12, .gpr 12] [])) #v[12, 12]
    (.letOp (n := 65) (.out 0x1099fb (leaR64Effect 0x1099fb 15 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 66) (.exec 0x1099fb (fun s => s.RIP = 0x1099fb) (leaR64Effect 0x1099fb 15 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.br ⟨.l109a00, RegMap.args [(0, 53), (1, 59), (3, 61), (4, 4), (5, 5), (12, 63), (13, 13), (14, 14), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩)))))))))))))))

def bytes_l1099df : List UInt8 :=
  [0x48, 0xB8, 0xFC, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x07, 0x48, 0x8B, 0x4C, 0x24, 0x18, 0x48,
    0x21, 0xC1, 0x48, 0xC1, 0xE1, 0x04, 0x48, 0x01, 0xCB, 0x45, 0x31, 0xE4, 0x4C, 0x8D, 0x7C, 0x24,
    0x08]

theorem code_l1099df : ∀ x ∈ codeRange 0x1099df bytes_l1099df, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x99df 33 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109a00_1 : Block Op Label signature Reg.count 83 :=
  .letOp (n := 83) (.out 0x109a5b (movzxR32M8Effect 0x109a5b 5 1 (.sib 4 none 0 (.d8 0x13))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 84) (.exec 0x109a5b (LoadPre 0x109a5b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x13)) s (0x109a5b + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109a5b 5 1 (.sib 4 none 0 (.d8 0x13))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 85) (.exec 0x109a60 (StorePre 0x109a60 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x109a60 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109a60 4 1 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[83, 4]
    (.letOp (n := 86) (.exec 0x109a64 (StorePre 0x109a64 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x13)) s (0x109a64 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109a64 4 0 (.sib 4 none 0 (.d8 0x13))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[81, 4]
    (.letOp (n := 87) (.out 0x109a68 (movzxR32M8Effect 0x109a68 5 0 (.sib 4 none 0 (.d8 0xd))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 88) (.exec 0x109a68 (LoadPre 0x109a68 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xd)) s (0x109a68 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109a68 5 0 (.sib 4 none 0 (.d8 0xd))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 89) (.out 0x109a6d (movzxR32M8Effect 0x109a6d 5 1 (.sib 4 none 0 (.d8 0x12))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 90) (.exec 0x109a6d (LoadPre 0x109a6d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x12)) s (0x109a6d + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109a6d 5 1 (.sib 4 none 0 (.d8 0x12))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 91) (.exec 0x109a72 (StorePre 0x109a72 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xd)) s (0x109a72 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109a72 4 1 (.sib 4 none 0 (.d8 0xd))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[89, 4]
    (.letOp (n := 92) (.exec 0x109a76 (StorePre 0x109a76 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x12)) s (0x109a76 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109a76 4 0 (.sib 4 none 0 (.d8 0x12))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[87, 4]
    (.letOp (n := 93) (.out 0x109a7a (movzxR32M8Effect 0x109a7a 5 0 (.sib 4 none 0 (.d8 0xe))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 94) (.exec 0x109a7a (LoadPre 0x109a7a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x109a7a + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109a7a 5 0 (.sib 4 none 0 (.d8 0xe))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 95) (.out 0x109a7f (movzxR32M8Effect 0x109a7f 5 1 (.sib 4 none 0 (.d8 0x11))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 96) (.exec 0x109a7f (LoadPre 0x109a7f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x11)) s (0x109a7f + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109a7f 5 1 (.sib 4 none 0 (.d8 0x11))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 97) (.exec 0x109a84 (StorePre 0x109a84 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x109a84 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109a84 4 1 (.sib 4 none 0 (.d8 0xe))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[95, 4]
    (.letOp (n := 98) (.exec 0x109a88 (StorePre 0x109a88 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x11)) s (0x109a88 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109a88 4 0 (.sib 4 none 0 (.d8 0x11))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[93, 4]
    (.letOp (n := 99) (.exec 0x109a8c (StorePre 0x109a8c 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x109a8c + BitVec.ofNat 64 6)) 2) (rolMEffect 0x109a8c 6 16 (.sib 4 none 0 (.d8 0xf)) 8) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [])) #v[4]
    (.letOp (n := 100) (.out 0x109a92 (movR64R64Effect 0x109a92 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 101) (.exec 0x109a92 (fun s => s.RIP = 0x109a92) (movR64R64Effect 0x109a92 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 102) (.out 0x109a95 (movR64R64Effect 0x109a95 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 103) (.exec 0x109a95 (fun s => s.RIP = 0x109a95) (movR64R64Effect 0x109a95 6 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 104) (.out 0x109a98 (callEffect (fun _ => 0x1034c0) 0x109a9d) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 105) (.exec 0x109a98 (PushPre 0x109a98 5) (callEffect (fun _ => 0x1034c0) 0x109a9d) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 106) (.const ⟨64, 0x109a9d⟩) #v[]
    (.terminate (.call ⟨.l1034c0, RegMap.args [(0, 93), (1, 95), (2, 67), (3, 3), (4, 104), (5, 5), (6, 102), (7, 100), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 107⟩ { target := .l109a9d, kept := #v[], arity := rfl, guard := some (Fin.last 106) })))))))))))))))))))))))))

def bytes_l109a00_1 : List UInt8 :=
  [0x0F, 0xB6, 0x4C, 0x24, 0x13, 0x88, 0x4C, 0x24, 0x0C, 0x88, 0x44, 0x24, 0x13, 0x0F, 0xB6, 0x44,
    0x24, 0x0D, 0x0F, 0xB6, 0x4C, 0x24, 0x12, 0x88, 0x4C, 0x24, 0x0D, 0x88, 0x44, 0x24, 0x12, 0x0F,
    0xB6, 0x44, 0x24, 0x0E, 0x0F, 0xB6, 0x4C, 0x24, 0x11, 0x88, 0x4C, 0x24, 0x0E, 0x88, 0x44, 0x24,
    0x11, 0x66, 0xC1, 0x44, 0x24, 0x0F, 0x08, 0x4C, 0x89, 0xF7, 0x4C, 0x89, 0xFE, 0xE8, 0x23, 0x9A,
    0xFF, 0xFF]

theorem code_l109a00_1 : ∀ x ∈ codeRange 0x109a5b bytes_l109a00_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9a5b 66 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109a00 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x109a00 (movR64M64Effect 0x109a00 0 (.sib 3 (some 12) 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 12] []) (.reg (.gpr 0))) #v[3, 12]
    (.letOp (n := 54) (.exec 0x109a00 (LoadPre 0x109a00 (fun s => AddrMode.addr (.sib 3 (some 12) 0 .none) s (0x109a00 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109a00 0 (.sib 3 (some 12) 0 .none)) (Reg.operands [.gpr 3, .gpr 12] [])) #v[3, 12]
    (.letOp (n := 55) (.out 0x109a04 (movR64M64Effect 0x109a04 1 (.sib 3 (some 12) 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 3, .gpr 12] []) (.reg (.gpr 1))) #v[3, 12]
    (.letOp (n := 56) (.exec 0x109a04 (LoadPre 0x109a04 (fun s => AddrMode.addr (.sib 3 (some 12) 0 (.d8 0x8)) s (0x109a04 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109a04 1 (.sib 3 (some 12) 0 (.d8 0x8))) (Reg.operands [.gpr 3, .gpr 12] [])) #v[3, 12]
    (.letOp (n := 57) (.exec 0x109a09 (StorePre 0x109a09 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x109a09 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109a09 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 58) (.exec 0x109a0e (StorePre 0x109a0e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109a0e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109a0e 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 59) (.out 0x109a13 (movzxR32M8Effect 0x109a13 5 1 (.sib 4 none 0 (.d8 0x17))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 60) (.exec 0x109a13 (LoadPre 0x109a13 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x17)) s (0x109a13 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109a13 5 1 (.sib 4 none 0 (.d8 0x17))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x109a18 (StorePre 0x109a18 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109a18 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109a18 4 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.exec 0x109a1c (StorePre 0x109a1c 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x17)) s (0x109a1c + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109a1c 4 0 (.sib 4 none 0 (.d8 0x17))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 63) (.out 0x109a20 (movzxR32M8Effect 0x109a20 5 0 (.sib 4 none 0 (.d8 0x16))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 64) (.exec 0x109a20 (LoadPre 0x109a20 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x16)) s (0x109a20 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109a20 5 0 (.sib 4 none 0 (.d8 0x16))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x109a25 (movzxR32M8Effect 0x109a25 5 1 (.sib 4 none 0 (.d8 0x9))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 66) (.exec 0x109a25 (LoadPre 0x109a25 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x9)) s (0x109a25 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109a25 5 1 (.sib 4 none 0 (.d8 0x9))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x109a2a (movzxR32M8Effect 0x109a2a 5 2 (.sib 4 none 0 (.d8 0xa))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 68) (.exec 0x109a2a (LoadPre 0x109a2a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xa)) s (0x109a2a + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109a2a 5 2 (.sib 4 none 0 (.d8 0xa))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.exec 0x109a2f (StorePre 0x109a2f 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x9)) s (0x109a2f + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109a2f 4 0 (.sib 4 none 0 (.d8 0x9))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[63, 4]
    (.letOp (n := 70) (.exec 0x109a33 (StorePre 0x109a33 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x16)) s (0x109a33 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109a33 4 1 (.sib 4 none 0 (.d8 0x16))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 71) (.out 0x109a37 (movzxR32M8Effect 0x109a37 5 0 (.sib 4 none 0 (.d8 0x14))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 72) (.exec 0x109a37 (LoadPre 0x109a37 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x109a37 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109a37 5 0 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.out 0x109a3c (movzxR32M8Effect 0x109a3c 5 1 (.sib 4 none 0 (.d8 0x15))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 74) (.exec 0x109a3c (LoadPre 0x109a3c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x15)) s (0x109a3c + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109a3c 5 1 (.sib 4 none 0 (.d8 0x15))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.exec 0x109a41 (StorePre 0x109a41 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xa)) s (0x109a41 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109a41 4 1 (.sib 4 none 0 (.d8 0xa))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[73, 4]
    (.letOp (n := 76) (.exec 0x109a45 (StorePre 0x109a45 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x15)) s (0x109a45 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109a45 4 2 (.sib 4 none 0 (.d8 0x15))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[67, 4]
    (.letOp (n := 77) (.out 0x109a49 (movzxR32M8Effect 0x109a49 5 1 (.sib 4 none 0 (.d8 0xb))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 78) (.exec 0x109a49 (LoadPre 0x109a49 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xb)) s (0x109a49 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109a49 5 1 (.sib 4 none 0 (.d8 0xb))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.exec 0x109a4e (StorePre 0x109a4e 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xb)) s (0x109a4e + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109a4e 4 0 (.sib 4 none 0 (.d8 0xb))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[71, 4]
    (.letOp (n := 80) (.exec 0x109a52 (StorePre 0x109a52 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x109a52 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109a52 4 1 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[77, 4]
    (.letOp (n := 81) (.out 0x109a56 (movzxR32M8Effect 0x109a56 5 0 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 82) (.exec 0x109a56 (LoadPre 0x109a56 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x109a56 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109a56 5 0 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l109a00_1))))))))))))))))))))))))))))))

def bytes_l109a00 : List UInt8 :=
  [0x4A, 0x8B, 0x04, 0x23, 0x4A, 0x8B, 0x4C, 0x23, 0x08, 0x48, 0x89, 0x4C, 0x24, 0x10, 0x48, 0x89,
    0x44, 0x24, 0x08, 0x0F, 0xB6, 0x4C, 0x24, 0x17, 0x88, 0x4C, 0x24, 0x08, 0x88, 0x44, 0x24, 0x17,
    0x0F, 0xB6, 0x44, 0x24, 0x16, 0x0F, 0xB6, 0x4C, 0x24, 0x09, 0x0F, 0xB6, 0x54, 0x24, 0x0A, 0x88,
    0x44, 0x24, 0x09, 0x88, 0x4C, 0x24, 0x16, 0x0F, 0xB6, 0x44, 0x24, 0x14, 0x0F, 0xB6, 0x4C, 0x24,
    0x15, 0x88, 0x4C, 0x24, 0x0A, 0x88, 0x54, 0x24, 0x15, 0x0F, 0xB6, 0x4C, 0x24, 0x0B, 0x88, 0x44,
    0x24, 0x0B, 0x88, 0x4C, 0x24, 0x14, 0x0F, 0xB6, 0x44, 0x24, 0x0C] ++ bytes_l109a00_1

theorem code_l109a00 : ∀ x ∈ codeRange 0x109a00 bytes_l109a00, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x9a00 91 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l109a00_1

@[cfg_block] def b_l109a9d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x109a9d (addR64Imm8Effect 0x109a9d 12 0x10) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[12]
    (.letOp (n := 54) (.exec 0x109a9d (fun s => s.RIP = 0x109a9d) (addR64Imm8Effect 0x109a9d 12 0x10) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 55) (.out 0x109aa1 (cmpR64R64Effect 0x109aa1 13 12) (EffectPart.reads (.flag .ZF) [.gpr 13, .gpr 12] []) (.flag .ZF)) #v[13, 53]
    (.letOp (n := 56) (.exec 0x109aa1 (fun s => s.RIP = 0x109aa1) (cmpR64R64Effect 0x109aa1 13 12) (Reg.operands [.gpr 13, .gpr 12] [])) #v[13, 53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l109a00, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 53), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l109aaa, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 53), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l109a9d : List UInt8 :=
  [0x49, 0x83, 0xC4, 0x10, 0x4D, 0x39, 0xE5, 0x0F, 0x85, 0x56, 0xFF, 0xFF, 0xFF]

theorem code_l109a9d : ∀ x ∈ codeRange 0x109a9d bytes_l109a9d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9a9d 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109aaa : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x109aaa (addR64Imm8Effect 0x109aaa 4 0x28) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 54) (.exec 0x109aaa (fun s => s.RIP = 0x109aaa) (addR64Imm8Effect 0x109aaa 4 0x28) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x109aae (popR64Effect 0x109aae 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[53]
    (.letOp (n := 56) (.out 0x109aae (popR64Effect 0x109aae 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[53]
    (.letOp (n := 57) (.exec 0x109aae (PopPre 0x109aae) (popR64Effect 0x109aae 1 3) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 58) (.out 0x109aaf (popR64Effect 0x109aaf 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[56]
    (.letOp (n := 59) (.out 0x109aaf (popR64Effect 0x109aaf 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[56]
    (.letOp (n := 60) (.exec 0x109aaf (PopPre 0x109aaf) (popR64Effect 0x109aaf 2 12) (Reg.operands [.gpr 4] [])) #v[56]
    (.letOp (n := 61) (.out 0x109ab1 (popR64Effect 0x109ab1 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[59]
    (.letOp (n := 62) (.out 0x109ab1 (popR64Effect 0x109ab1 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 63) (.exec 0x109ab1 (PopPre 0x109ab1) (popR64Effect 0x109ab1 2 13) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 64) (.out 0x109ab3 (popR64Effect 0x109ab3 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[62]
    (.letOp (n := 65) (.out 0x109ab3 (popR64Effect 0x109ab3 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[62]
    (.letOp (n := 66) (.exec 0x109ab3 (PopPre 0x109ab3) (popR64Effect 0x109ab3 2 14) (Reg.operands [.gpr 4] [])) #v[62]
    (.letOp (n := 67) (.out 0x109ab5 (popR64Effect 0x109ab5 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[65]
    (.letOp (n := 68) (.out 0x109ab5 (popR64Effect 0x109ab5 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 69) (.exec 0x109ab5 (PopPre 0x109ab5) (popR64Effect 0x109ab5 2 15) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 70) (.out 0x109ab7 (popR64Effect 0x109ab7 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[68]
    (.letOp (n := 71) (.out 0x109ab7 (popR64Effect 0x109ab7 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[68]
    (.letOp (n := 72) (.exec 0x109ab7 (PopPre 0x109ab7) (popR64Effect 0x109ab7 1 5) (Reg.operands [.gpr 4] [])) #v[68]
    (.letOp (n := 73) (.out 0x109ab8 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[71]
    (.letOp (n := 74) (.out 0x109ab8 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[71]
    (.letOp (n := 75) (.exec 0x109ab8 (RetPre 0x109ab8) (retEffect) (Reg.operands [.gpr 4] [])) #v[71]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 2), (3, 55), (4, 74), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 76) (some ⟨73, by decide⟩)))))))))))))))))))))))))

def bytes_l109aaa : List UInt8 :=
  [0x48, 0x83, 0xC4, 0x28, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l109aaa : ∀ x ∈ codeRange 0x109aaa bytes_l109aaa, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9aaa 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109ac0_7 : Block Op Label signature Reg.count 262 :=
  .letOp (n := 262) (.out 0x109d4a (movzxR32M8Effect 0x109d4a 5 0 (.sib 4 none 0 (.d8 0x3d))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 263) (.exec 0x109d4a (LoadPre 0x109d4a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3d)) s (0x109d4a + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109d4a 5 0 (.sib 4 none 0 (.d8 0x3d))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 264) (.out 0x109d4f (movzxR32M8Effect 0x109d4f 5 1 (.sib 4 none 0 (.d8 0x42))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 265) (.exec 0x109d4f (LoadPre 0x109d4f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x42)) s (0x109d4f + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109d4f 5 1 (.sib 4 none 0 (.d8 0x42))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 266) (.exec 0x109d54 (StorePre 0x109d54 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3d)) s (0x109d54 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109d54 4 1 (.sib 4 none 0 (.d8 0x3d))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[264, 53]
    (.letOp (n := 267) (.exec 0x109d58 (StorePre 0x109d58 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x42)) s (0x109d58 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109d58 4 0 (.sib 4 none 0 (.d8 0x42))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[262, 53]
    (.letOp (n := 268) (.out 0x109d5c (movzxR32M8Effect 0x109d5c 5 0 (.sib 4 none 0 (.d8 0x3e))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 269) (.exec 0x109d5c (LoadPre 0x109d5c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3e)) s (0x109d5c + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109d5c 5 0 (.sib 4 none 0 (.d8 0x3e))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 270) (.out 0x109d61 (movzxR32M8Effect 0x109d61 5 1 (.sib 4 none 0 (.d8 0x41))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 271) (.exec 0x109d61 (LoadPre 0x109d61 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x41)) s (0x109d61 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109d61 5 1 (.sib 4 none 0 (.d8 0x41))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 272) (.exec 0x109d66 (StorePre 0x109d66 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3e)) s (0x109d66 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109d66 4 1 (.sib 4 none 0 (.d8 0x3e))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[270, 53]
    (.letOp (n := 273) (.exec 0x109d6a (StorePre 0x109d6a 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x41)) s (0x109d6a + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109d6a 4 0 (.sib 4 none 0 (.d8 0x41))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[268, 53]
    (.letOp (n := 274) (.exec 0x109d6e (StorePre 0x109d6e 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3f)) s (0x109d6e + BitVec.ofNat 64 6)) 2) (rolMEffect 0x109d6e 6 16 (.sib 4 none 0 (.d8 0x3f)) 8) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [])) #v[53]
    (.letOp (n := 275) (.out 0x109d74 (movR64M64Effect 0x109d74 7 (.base 7 .none)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[7]
    (.letOp (n := 276) (.exec 0x109d74 (LoadPre 0x109d74 (fun s => AddrMode.addr (.base 7 .none) s (0x109d74 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x109d74 7 (.base 7 .none)) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 277) (.out 0x109d77 (leaR64Effect 0x109d77 6 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[53]
    (.letOp (n := 278) (.exec 0x109d77 (fun s => s.RIP = 0x109d77) (leaR64Effect 0x109d77 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 279) (.out 0x109d7c (callEffect (fun _ => 0x1034d0) 0x109d81) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[53]
    (.letOp (n := 280) (.exec 0x109d7c (PushPre 0x109d7c 5) (callEffect (fun _ => 0x1034d0) 0x109d81) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 281) (.const ⟨64, 0x109d81⟩) #v[]
    (.terminate (.call ⟨.l1034d0, RegMap.args [(0, 268), (1, 270), (3, 3), (4, 279), (5, 5), (6, 277), (7, 275), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 282⟩ { target := .l109d81, kept := #v[], arity := rfl, guard := some (Fin.last 281) })))))))))))))))))))))

def bytes_l109ac0_7 : List UInt8 :=
  [0x0F, 0xB6, 0x44, 0x24, 0x3D, 0x0F, 0xB6, 0x4C, 0x24, 0x42, 0x88, 0x4C, 0x24, 0x3D, 0x88, 0x44,
    0x24, 0x42, 0x0F, 0xB6, 0x44, 0x24, 0x3E, 0x0F, 0xB6, 0x4C, 0x24, 0x41, 0x88, 0x4C, 0x24, 0x3E,
    0x88, 0x44, 0x24, 0x41, 0x66, 0xC1, 0x44, 0x24, 0x3F, 0x08, 0x48, 0x8B, 0x3F, 0x48, 0x8D, 0x74,
    0x24, 0x08, 0xE8, 0x4F, 0x97, 0xFF, 0xFF]

theorem code_l109ac0_7 : ∀ x ∈ codeRange 0x109d4a bytes_l109ac0_7, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9d4a 55 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109ac0_6 : Block Op Label signature Reg.count 232 :=
  .letOp (n := 232) (.out 0x109cf0 (movzxR32M8Effect 0x109cf0 5 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 233) (.exec 0x109cf0 (LoadPre 0x109cf0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x109cf0 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109cf0 5 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 234) (.out 0x109cf5 (movzxR32M8Effect 0x109cf5 5 1 (.sib 4 none 0 (.d8 0x47))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 235) (.exec 0x109cf5 (LoadPre 0x109cf5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x47)) s (0x109cf5 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109cf5 5 1 (.sib 4 none 0 (.d8 0x47))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 236) (.exec 0x109cfa (StorePre 0x109cfa 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x109cfa + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109cfa 4 1 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[234, 53]
    (.letOp (n := 237) (.exec 0x109cfe (StorePre 0x109cfe 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x47)) s (0x109cfe + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109cfe 4 0 (.sib 4 none 0 (.d8 0x47))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[232, 53]
    (.letOp (n := 238) (.out 0x109d02 (movzxR32M8Effect 0x109d02 5 0 (.sib 4 none 0 (.d8 0x39))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 239) (.exec 0x109d02 (LoadPre 0x109d02 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x39)) s (0x109d02 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109d02 5 0 (.sib 4 none 0 (.d8 0x39))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 240) (.out 0x109d07 (movzxR32M8Effect 0x109d07 5 1 (.sib 4 none 0 (.d8 0x46))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 241) (.exec 0x109d07 (LoadPre 0x109d07 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x46)) s (0x109d07 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109d07 5 1 (.sib 4 none 0 (.d8 0x46))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 242) (.exec 0x109d0c (StorePre 0x109d0c 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x39)) s (0x109d0c + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109d0c 4 1 (.sib 4 none 0 (.d8 0x39))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[240, 53]
    (.letOp (n := 243) (.exec 0x109d10 (StorePre 0x109d10 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x46)) s (0x109d10 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109d10 4 0 (.sib 4 none 0 (.d8 0x46))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[238, 53]
    (.letOp (n := 244) (.out 0x109d14 (movzxR32M8Effect 0x109d14 5 0 (.sib 4 none 0 (.d8 0x3a))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 245) (.exec 0x109d14 (LoadPre 0x109d14 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3a)) s (0x109d14 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109d14 5 0 (.sib 4 none 0 (.d8 0x3a))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 246) (.out 0x109d19 (movzxR32M8Effect 0x109d19 5 1 (.sib 4 none 0 (.d8 0x45))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 247) (.exec 0x109d19 (LoadPre 0x109d19 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x45)) s (0x109d19 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109d19 5 1 (.sib 4 none 0 (.d8 0x45))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 248) (.exec 0x109d1e (StorePre 0x109d1e 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3a)) s (0x109d1e + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109d1e 4 1 (.sib 4 none 0 (.d8 0x3a))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[246, 53]
    (.letOp (n := 249) (.exec 0x109d22 (StorePre 0x109d22 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x45)) s (0x109d22 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109d22 4 0 (.sib 4 none 0 (.d8 0x45))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[244, 53]
    (.letOp (n := 250) (.out 0x109d26 (movzxR32M8Effect 0x109d26 5 0 (.sib 4 none 0 (.d8 0x3b))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 251) (.exec 0x109d26 (LoadPre 0x109d26 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3b)) s (0x109d26 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109d26 5 0 (.sib 4 none 0 (.d8 0x3b))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 252) (.out 0x109d2b (movzxR32M8Effect 0x109d2b 5 1 (.sib 4 none 0 (.d8 0x44))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 253) (.exec 0x109d2b (LoadPre 0x109d2b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x109d2b + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109d2b 5 1 (.sib 4 none 0 (.d8 0x44))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 254) (.exec 0x109d30 (StorePre 0x109d30 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3b)) s (0x109d30 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109d30 4 1 (.sib 4 none 0 (.d8 0x3b))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[252, 53]
    (.letOp (n := 255) (.exec 0x109d34 (StorePre 0x109d34 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x109d34 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109d34 4 0 (.sib 4 none 0 (.d8 0x44))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[250, 53]
    (.letOp (n := 256) (.out 0x109d38 (movzxR32M8Effect 0x109d38 5 0 (.sib 4 none 0 (.d8 0x3c))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 257) (.exec 0x109d38 (LoadPre 0x109d38 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x109d38 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109d38 5 0 (.sib 4 none 0 (.d8 0x3c))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 258) (.out 0x109d3d (movzxR32M8Effect 0x109d3d 5 1 (.sib 4 none 0 (.d8 0x43))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 259) (.exec 0x109d3d (LoadPre 0x109d3d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x43)) s (0x109d3d + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109d3d 5 1 (.sib 4 none 0 (.d8 0x43))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 260) (.exec 0x109d42 (StorePre 0x109d42 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x109d42 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109d42 4 1 (.sib 4 none 0 (.d8 0x3c))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[258, 53]
    (.letOp (n := 261) (.exec 0x109d46 (StorePre 0x109d46 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x43)) s (0x109d46 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109d46 4 0 (.sib 4 none 0 (.d8 0x43))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[256, 53]
    (b_l109ac0_7))))))))))))))))))))))))))))))

def bytes_l109ac0_6 : List UInt8 :=
  [0x0F, 0xB6, 0x44, 0x24, 0x38, 0x0F, 0xB6, 0x4C, 0x24, 0x47, 0x88, 0x4C, 0x24, 0x38, 0x88, 0x44,
    0x24, 0x47, 0x0F, 0xB6, 0x44, 0x24, 0x39, 0x0F, 0xB6, 0x4C, 0x24, 0x46, 0x88, 0x4C, 0x24, 0x39,
    0x88, 0x44, 0x24, 0x46, 0x0F, 0xB6, 0x44, 0x24, 0x3A, 0x0F, 0xB6, 0x4C, 0x24, 0x45, 0x88, 0x4C,
    0x24, 0x3A, 0x88, 0x44, 0x24, 0x45, 0x0F, 0xB6, 0x44, 0x24, 0x3B, 0x0F, 0xB6, 0x4C, 0x24, 0x44,
    0x88, 0x4C, 0x24, 0x3B, 0x88, 0x44, 0x24, 0x44, 0x0F, 0xB6, 0x44, 0x24, 0x3C, 0x0F, 0xB6, 0x4C,
    0x24, 0x43, 0x88, 0x4C, 0x24, 0x3C, 0x88, 0x44, 0x24, 0x43] ++ bytes_l109ac0_7

theorem code_l109ac0_6 : ∀ x ∈ codeRange 0x109cf0 bytes_l109ac0_6, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x9cf0 90 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l109ac0_7

@[cfg_block] def b_l109ac0_5 : Block Op Label signature Reg.count 203 :=
  .letOp (n := 203) (.out 0x109c95 (movzxR32M8Effect 0x109c95 5 1 (.sib 4 none 0 (.d8 0x35))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 204) (.exec 0x109c95 (LoadPre 0x109c95 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x35)) s (0x109c95 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109c95 5 1 (.sib 4 none 0 (.d8 0x35))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 205) (.exec 0x109c9a (StorePre 0x109c9a 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2a)) s (0x109c9a + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109c9a 4 1 (.sib 4 none 0 (.d8 0x2a))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[203, 53]
    (.letOp (n := 206) (.exec 0x109c9e (StorePre 0x109c9e 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x35)) s (0x109c9e + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109c9e 4 0 (.sib 4 none 0 (.d8 0x35))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[201, 53]
    (.letOp (n := 207) (.out 0x109ca2 (movzxR32M8Effect 0x109ca2 5 0 (.sib 4 none 0 (.d8 0x2b))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 208) (.exec 0x109ca2 (LoadPre 0x109ca2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2b)) s (0x109ca2 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109ca2 5 0 (.sib 4 none 0 (.d8 0x2b))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 209) (.out 0x109ca7 (movzxR32M8Effect 0x109ca7 5 1 (.sib 4 none 0 (.d8 0x34))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 210) (.exec 0x109ca7 (LoadPre 0x109ca7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x109ca7 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109ca7 5 1 (.sib 4 none 0 (.d8 0x34))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 211) (.exec 0x109cac (StorePre 0x109cac 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2b)) s (0x109cac + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109cac 4 1 (.sib 4 none 0 (.d8 0x2b))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[209, 53]
    (.letOp (n := 212) (.exec 0x109cb0 (StorePre 0x109cb0 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x109cb0 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109cb0 4 0 (.sib 4 none 0 (.d8 0x34))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[207, 53]
    (.letOp (n := 213) (.out 0x109cb4 (movzxR32M8Effect 0x109cb4 5 0 (.sib 4 none 0 (.d8 0x2c))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 214) (.exec 0x109cb4 (LoadPre 0x109cb4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x109cb4 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109cb4 5 0 (.sib 4 none 0 (.d8 0x2c))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 215) (.out 0x109cb9 (movzxR32M8Effect 0x109cb9 5 1 (.sib 4 none 0 (.d8 0x33))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 216) (.exec 0x109cb9 (LoadPre 0x109cb9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x33)) s (0x109cb9 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109cb9 5 1 (.sib 4 none 0 (.d8 0x33))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 217) (.exec 0x109cbe (StorePre 0x109cbe 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x109cbe + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109cbe 4 1 (.sib 4 none 0 (.d8 0x2c))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[215, 53]
    (.letOp (n := 218) (.exec 0x109cc2 (StorePre 0x109cc2 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x33)) s (0x109cc2 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109cc2 4 0 (.sib 4 none 0 (.d8 0x33))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[213, 53]
    (.letOp (n := 219) (.out 0x109cc6 (movzxR32M8Effect 0x109cc6 5 0 (.sib 4 none 0 (.d8 0x2d))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 220) (.exec 0x109cc6 (LoadPre 0x109cc6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2d)) s (0x109cc6 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109cc6 5 0 (.sib 4 none 0 (.d8 0x2d))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 221) (.out 0x109ccb (movzxR32M8Effect 0x109ccb 5 1 (.sib 4 none 0 (.d8 0x32))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 222) (.exec 0x109ccb (LoadPre 0x109ccb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x32)) s (0x109ccb + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109ccb 5 1 (.sib 4 none 0 (.d8 0x32))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 223) (.exec 0x109cd0 (StorePre 0x109cd0 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2d)) s (0x109cd0 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109cd0 4 1 (.sib 4 none 0 (.d8 0x2d))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[221, 53]
    (.letOp (n := 224) (.exec 0x109cd4 (StorePre 0x109cd4 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x32)) s (0x109cd4 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109cd4 4 0 (.sib 4 none 0 (.d8 0x32))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[219, 53]
    (.letOp (n := 225) (.out 0x109cd8 (movzxR32M8Effect 0x109cd8 5 0 (.sib 4 none 0 (.d8 0x2e))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 226) (.exec 0x109cd8 (LoadPre 0x109cd8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2e)) s (0x109cd8 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109cd8 5 0 (.sib 4 none 0 (.d8 0x2e))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 227) (.out 0x109cdd (movzxR32M8Effect 0x109cdd 5 1 (.sib 4 none 0 (.d8 0x31))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 228) (.exec 0x109cdd (LoadPre 0x109cdd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x31)) s (0x109cdd + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109cdd 5 1 (.sib 4 none 0 (.d8 0x31))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 229) (.exec 0x109ce2 (StorePre 0x109ce2 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2e)) s (0x109ce2 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109ce2 4 1 (.sib 4 none 0 (.d8 0x2e))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[227, 53]
    (.letOp (n := 230) (.exec 0x109ce6 (StorePre 0x109ce6 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x31)) s (0x109ce6 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109ce6 4 0 (.sib 4 none 0 (.d8 0x31))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[225, 53]
    (.letOp (n := 231) (.exec 0x109cea (StorePre 0x109cea 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2f)) s (0x109cea + BitVec.ofNat 64 6)) 2) (rolMEffect 0x109cea 6 16 (.sib 4 none 0 (.d8 0x2f)) 8) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [])) #v[53]
    (b_l109ac0_6)))))))))))))))))))))))))))))

def bytes_l109ac0_5 : List UInt8 :=
  [0x0F, 0xB6, 0x4C, 0x24, 0x35, 0x88, 0x4C, 0x24, 0x2A, 0x88, 0x44, 0x24, 0x35, 0x0F, 0xB6, 0x44,
    0x24, 0x2B, 0x0F, 0xB6, 0x4C, 0x24, 0x34, 0x88, 0x4C, 0x24, 0x2B, 0x88, 0x44, 0x24, 0x34, 0x0F,
    0xB6, 0x44, 0x24, 0x2C, 0x0F, 0xB6, 0x4C, 0x24, 0x33, 0x88, 0x4C, 0x24, 0x2C, 0x88, 0x44, 0x24,
    0x33, 0x0F, 0xB6, 0x44, 0x24, 0x2D, 0x0F, 0xB6, 0x4C, 0x24, 0x32, 0x88, 0x4C, 0x24, 0x2D, 0x88,
    0x44, 0x24, 0x32, 0x0F, 0xB6, 0x44, 0x24, 0x2E, 0x0F, 0xB6, 0x4C, 0x24, 0x31, 0x88, 0x4C, 0x24,
    0x2E, 0x88, 0x44, 0x24, 0x31, 0x66, 0xC1, 0x44, 0x24, 0x2F, 0x08] ++ bytes_l109ac0_6

theorem code_l109ac0_5 : ∀ x ∈ codeRange 0x109c95 bytes_l109ac0_5, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x9c95 91 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l109ac0_6

@[cfg_block] def b_l109ac0_4 : Block Op Label signature Reg.count 174 :=
  .letOp (n := 174) (.exec 0x109c3a (StorePre 0x109c3a 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x109c3a + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109c3a 4 1 (.sib 4 none 0 (.d8 0x1c))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[172, 53]
    (.letOp (n := 175) (.exec 0x109c3e (StorePre 0x109c3e 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x23)) s (0x109c3e + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109c3e 4 0 (.sib 4 none 0 (.d8 0x23))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[170, 53]
    (.letOp (n := 176) (.out 0x109c42 (movzxR32M8Effect 0x109c42 5 0 (.sib 4 none 0 (.d8 0x1d))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 177) (.exec 0x109c42 (LoadPre 0x109c42 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1d)) s (0x109c42 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109c42 5 0 (.sib 4 none 0 (.d8 0x1d))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 178) (.out 0x109c47 (movzxR32M8Effect 0x109c47 5 1 (.sib 4 none 0 (.d8 0x22))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 179) (.exec 0x109c47 (LoadPre 0x109c47 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x22)) s (0x109c47 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109c47 5 1 (.sib 4 none 0 (.d8 0x22))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 180) (.exec 0x109c4c (StorePre 0x109c4c 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1d)) s (0x109c4c + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109c4c 4 1 (.sib 4 none 0 (.d8 0x1d))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[178, 53]
    (.letOp (n := 181) (.exec 0x109c50 (StorePre 0x109c50 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x22)) s (0x109c50 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109c50 4 0 (.sib 4 none 0 (.d8 0x22))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[176, 53]
    (.letOp (n := 182) (.out 0x109c54 (movzxR32M8Effect 0x109c54 5 0 (.sib 4 none 0 (.d8 0x1e))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 183) (.exec 0x109c54 (LoadPre 0x109c54 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1e)) s (0x109c54 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109c54 5 0 (.sib 4 none 0 (.d8 0x1e))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 184) (.out 0x109c59 (movzxR32M8Effect 0x109c59 5 1 (.sib 4 none 0 (.d8 0x21))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 185) (.exec 0x109c59 (LoadPre 0x109c59 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x21)) s (0x109c59 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109c59 5 1 (.sib 4 none 0 (.d8 0x21))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 186) (.exec 0x109c5e (StorePre 0x109c5e 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1e)) s (0x109c5e + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109c5e 4 1 (.sib 4 none 0 (.d8 0x1e))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[184, 53]
    (.letOp (n := 187) (.exec 0x109c62 (StorePre 0x109c62 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x21)) s (0x109c62 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109c62 4 0 (.sib 4 none 0 (.d8 0x21))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[182, 53]
    (.letOp (n := 188) (.exec 0x109c66 (StorePre 0x109c66 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1f)) s (0x109c66 + BitVec.ofNat 64 6)) 2) (rolMEffect 0x109c66 6 16 (.sib 4 none 0 (.d8 0x1f)) 8) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [])) #v[53]
    (.letOp (n := 189) (.out 0x109c6c (movzxR32M8Effect 0x109c6c 5 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 190) (.exec 0x109c6c (LoadPre 0x109c6c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x109c6c + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109c6c 5 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 191) (.out 0x109c71 (movzxR32M8Effect 0x109c71 5 1 (.sib 4 none 0 (.d8 0x37))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 192) (.exec 0x109c71 (LoadPre 0x109c71 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x37)) s (0x109c71 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109c71 5 1 (.sib 4 none 0 (.d8 0x37))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 193) (.exec 0x109c76 (StorePre 0x109c76 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x109c76 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109c76 4 1 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[191, 53]
    (.letOp (n := 194) (.exec 0x109c7a (StorePre 0x109c7a 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x37)) s (0x109c7a + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109c7a 4 0 (.sib 4 none 0 (.d8 0x37))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[189, 53]
    (.letOp (n := 195) (.out 0x109c7e (movzxR32M8Effect 0x109c7e 5 0 (.sib 4 none 0 (.d8 0x29))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 196) (.exec 0x109c7e (LoadPre 0x109c7e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x29)) s (0x109c7e + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109c7e 5 0 (.sib 4 none 0 (.d8 0x29))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 197) (.out 0x109c83 (movzxR32M8Effect 0x109c83 5 1 (.sib 4 none 0 (.d8 0x36))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 198) (.exec 0x109c83 (LoadPre 0x109c83 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x36)) s (0x109c83 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109c83 5 1 (.sib 4 none 0 (.d8 0x36))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 199) (.exec 0x109c88 (StorePre 0x109c88 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x29)) s (0x109c88 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109c88 4 1 (.sib 4 none 0 (.d8 0x29))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[197, 53]
    (.letOp (n := 200) (.exec 0x109c8c (StorePre 0x109c8c 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x36)) s (0x109c8c + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109c8c 4 0 (.sib 4 none 0 (.d8 0x36))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[195, 53]
    (.letOp (n := 201) (.out 0x109c90 (movzxR32M8Effect 0x109c90 5 0 (.sib 4 none 0 (.d8 0x2a))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 202) (.exec 0x109c90 (LoadPre 0x109c90 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2a)) s (0x109c90 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109c90 5 0 (.sib 4 none 0 (.d8 0x2a))) (Reg.operands [.gpr 4] [])) #v[53]
    (b_l109ac0_5)))))))))))))))))))))))))))))

def bytes_l109ac0_4 : List UInt8 :=
  [0x88, 0x4C, 0x24, 0x1C, 0x88, 0x44, 0x24, 0x23, 0x0F, 0xB6, 0x44, 0x24, 0x1D, 0x0F, 0xB6, 0x4C,
    0x24, 0x22, 0x88, 0x4C, 0x24, 0x1D, 0x88, 0x44, 0x24, 0x22, 0x0F, 0xB6, 0x44, 0x24, 0x1E, 0x0F,
    0xB6, 0x4C, 0x24, 0x21, 0x88, 0x4C, 0x24, 0x1E, 0x88, 0x44, 0x24, 0x21, 0x66, 0xC1, 0x44, 0x24,
    0x1F, 0x08, 0x0F, 0xB6, 0x44, 0x24, 0x28, 0x0F, 0xB6, 0x4C, 0x24, 0x37, 0x88, 0x4C, 0x24, 0x28,
    0x88, 0x44, 0x24, 0x37, 0x0F, 0xB6, 0x44, 0x24, 0x29, 0x0F, 0xB6, 0x4C, 0x24, 0x36, 0x88, 0x4C,
    0x24, 0x29, 0x88, 0x44, 0x24, 0x36, 0x0F, 0xB6, 0x44, 0x24, 0x2A] ++ bytes_l109ac0_5

theorem code_l109ac0_4 : ∀ x ∈ codeRange 0x109c3a bytes_l109ac0_4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x9c3a 91 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l109ac0_5

@[cfg_block] def b_l109ac0_3 : Block Op Label signature Reg.count 144 :=
  .letOp (n := 144) (.exec 0x109bde (StorePre 0x109bde 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x11)) s (0x109bde + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109bde 4 0 (.sib 4 none 0 (.d8 0x11))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[139, 53]
    (.letOp (n := 145) (.exec 0x109be2 (StorePre 0x109be2 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x109be2 + BitVec.ofNat 64 6)) 2) (rolMEffect 0x109be2 6 16 (.sib 4 none 0 (.d8 0xf)) 8) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [])) #v[53]
    (.letOp (n := 146) (.out 0x109be8 (movzxR32M8Effect 0x109be8 5 0 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 147) (.exec 0x109be8 (LoadPre 0x109be8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x109be8 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109be8 5 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 148) (.out 0x109bed (movzxR32M8Effect 0x109bed 5 1 (.sib 4 none 0 (.d8 0x27))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 149) (.exec 0x109bed (LoadPre 0x109bed (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x27)) s (0x109bed + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109bed 5 1 (.sib 4 none 0 (.d8 0x27))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 150) (.exec 0x109bf2 (StorePre 0x109bf2 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x109bf2 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109bf2 4 1 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[148, 53]
    (.letOp (n := 151) (.exec 0x109bf6 (StorePre 0x109bf6 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x27)) s (0x109bf6 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109bf6 4 0 (.sib 4 none 0 (.d8 0x27))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[146, 53]
    (.letOp (n := 152) (.out 0x109bfa (movzxR32M8Effect 0x109bfa 5 0 (.sib 4 none 0 (.d8 0x19))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 153) (.exec 0x109bfa (LoadPre 0x109bfa (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x19)) s (0x109bfa + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109bfa 5 0 (.sib 4 none 0 (.d8 0x19))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 154) (.out 0x109bff (movzxR32M8Effect 0x109bff 5 1 (.sib 4 none 0 (.d8 0x26))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 155) (.exec 0x109bff (LoadPre 0x109bff (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x26)) s (0x109bff + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109bff 5 1 (.sib 4 none 0 (.d8 0x26))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 156) (.exec 0x109c04 (StorePre 0x109c04 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x19)) s (0x109c04 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109c04 4 1 (.sib 4 none 0 (.d8 0x19))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[154, 53]
    (.letOp (n := 157) (.exec 0x109c08 (StorePre 0x109c08 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x26)) s (0x109c08 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109c08 4 0 (.sib 4 none 0 (.d8 0x26))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[152, 53]
    (.letOp (n := 158) (.out 0x109c0c (movzxR32M8Effect 0x109c0c 5 0 (.sib 4 none 0 (.d8 0x1a))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 159) (.exec 0x109c0c (LoadPre 0x109c0c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1a)) s (0x109c0c + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109c0c 5 0 (.sib 4 none 0 (.d8 0x1a))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 160) (.out 0x109c11 (movzxR32M8Effect 0x109c11 5 1 (.sib 4 none 0 (.d8 0x25))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 161) (.exec 0x109c11 (LoadPre 0x109c11 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x25)) s (0x109c11 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109c11 5 1 (.sib 4 none 0 (.d8 0x25))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 162) (.exec 0x109c16 (StorePre 0x109c16 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1a)) s (0x109c16 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109c16 4 1 (.sib 4 none 0 (.d8 0x1a))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[160, 53]
    (.letOp (n := 163) (.exec 0x109c1a (StorePre 0x109c1a 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x25)) s (0x109c1a + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109c1a 4 0 (.sib 4 none 0 (.d8 0x25))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[158, 53]
    (.letOp (n := 164) (.out 0x109c1e (movzxR32M8Effect 0x109c1e 5 0 (.sib 4 none 0 (.d8 0x1b))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 165) (.exec 0x109c1e (LoadPre 0x109c1e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1b)) s (0x109c1e + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109c1e 5 0 (.sib 4 none 0 (.d8 0x1b))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 166) (.out 0x109c23 (movzxR32M8Effect 0x109c23 5 1 (.sib 4 none 0 (.d8 0x24))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 167) (.exec 0x109c23 (LoadPre 0x109c23 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x109c23 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109c23 5 1 (.sib 4 none 0 (.d8 0x24))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 168) (.exec 0x109c28 (StorePre 0x109c28 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1b)) s (0x109c28 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109c28 4 1 (.sib 4 none 0 (.d8 0x1b))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[166, 53]
    (.letOp (n := 169) (.exec 0x109c2c (StorePre 0x109c2c 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x109c2c + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109c2c 4 0 (.sib 4 none 0 (.d8 0x24))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[164, 53]
    (.letOp (n := 170) (.out 0x109c30 (movzxR32M8Effect 0x109c30 5 0 (.sib 4 none 0 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 171) (.exec 0x109c30 (LoadPre 0x109c30 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x109c30 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109c30 5 0 (.sib 4 none 0 (.d8 0x1c))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 172) (.out 0x109c35 (movzxR32M8Effect 0x109c35 5 1 (.sib 4 none 0 (.d8 0x23))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 173) (.exec 0x109c35 (LoadPre 0x109c35 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x23)) s (0x109c35 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109c35 5 1 (.sib 4 none 0 (.d8 0x23))) (Reg.operands [.gpr 4] [])) #v[53]
    (b_l109ac0_4))))))))))))))))))))))))))))))

def bytes_l109ac0_3 : List UInt8 :=
  [0x88, 0x44, 0x24, 0x11, 0x66, 0xC1, 0x44, 0x24, 0x0F, 0x08, 0x0F, 0xB6, 0x44, 0x24, 0x18, 0x0F,
    0xB6, 0x4C, 0x24, 0x27, 0x88, 0x4C, 0x24, 0x18, 0x88, 0x44, 0x24, 0x27, 0x0F, 0xB6, 0x44, 0x24,
    0x19, 0x0F, 0xB6, 0x4C, 0x24, 0x26, 0x88, 0x4C, 0x24, 0x19, 0x88, 0x44, 0x24, 0x26, 0x0F, 0xB6,
    0x44, 0x24, 0x1A, 0x0F, 0xB6, 0x4C, 0x24, 0x25, 0x88, 0x4C, 0x24, 0x1A, 0x88, 0x44, 0x24, 0x25,
    0x0F, 0xB6, 0x44, 0x24, 0x1B, 0x0F, 0xB6, 0x4C, 0x24, 0x24, 0x88, 0x4C, 0x24, 0x1B, 0x88, 0x44,
    0x24, 0x24, 0x0F, 0xB6, 0x44, 0x24, 0x1C, 0x0F, 0xB6, 0x4C, 0x24, 0x23] ++ bytes_l109ac0_4

theorem code_l109ac0_3 : ∀ x ∈ codeRange 0x109bde bytes_l109ac0_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x9bde 92 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l109ac0_4

@[cfg_block] def b_l109ac0_2 : Block Op Label signature Reg.count 114 :=
  .letOp (n := 114) (.exec 0x109b84 (StorePre 0x109b84 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x16)) s (0x109b84 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109b84 4 0 (.sib 4 none 0 (.d8 0x16))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[109, 53]
    (.letOp (n := 115) (.out 0x109b88 (movzxR32M8Effect 0x109b88 5 0 (.sib 4 none 0 (.d8 0xa))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 116) (.exec 0x109b88 (LoadPre 0x109b88 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xa)) s (0x109b88 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109b88 5 0 (.sib 4 none 0 (.d8 0xa))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 117) (.out 0x109b8d (movzxR32M8Effect 0x109b8d 5 1 (.sib 4 none 0 (.d8 0x15))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 118) (.exec 0x109b8d (LoadPre 0x109b8d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x15)) s (0x109b8d + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109b8d 5 1 (.sib 4 none 0 (.d8 0x15))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 119) (.exec 0x109b92 (StorePre 0x109b92 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xa)) s (0x109b92 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109b92 4 1 (.sib 4 none 0 (.d8 0xa))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[117, 53]
    (.letOp (n := 120) (.exec 0x109b96 (StorePre 0x109b96 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x15)) s (0x109b96 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109b96 4 0 (.sib 4 none 0 (.d8 0x15))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[115, 53]
    (.letOp (n := 121) (.out 0x109b9a (movzxR32M8Effect 0x109b9a 5 0 (.sib 4 none 0 (.d8 0xb))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 122) (.exec 0x109b9a (LoadPre 0x109b9a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xb)) s (0x109b9a + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109b9a 5 0 (.sib 4 none 0 (.d8 0xb))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 123) (.out 0x109b9f (movzxR32M8Effect 0x109b9f 5 1 (.sib 4 none 0 (.d8 0x14))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 124) (.exec 0x109b9f (LoadPre 0x109b9f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x109b9f + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109b9f 5 1 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 125) (.exec 0x109ba4 (StorePre 0x109ba4 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xb)) s (0x109ba4 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109ba4 4 1 (.sib 4 none 0 (.d8 0xb))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[123, 53]
    (.letOp (n := 126) (.exec 0x109ba8 (StorePre 0x109ba8 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x109ba8 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109ba8 4 0 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[121, 53]
    (.letOp (n := 127) (.out 0x109bac (movzxR32M8Effect 0x109bac 5 0 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 128) (.exec 0x109bac (LoadPre 0x109bac (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x109bac + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109bac 5 0 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 129) (.out 0x109bb1 (movzxR32M8Effect 0x109bb1 5 1 (.sib 4 none 0 (.d8 0x13))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 130) (.exec 0x109bb1 (LoadPre 0x109bb1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x13)) s (0x109bb1 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109bb1 5 1 (.sib 4 none 0 (.d8 0x13))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 131) (.exec 0x109bb6 (StorePre 0x109bb6 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x109bb6 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109bb6 4 1 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[129, 53]
    (.letOp (n := 132) (.exec 0x109bba (StorePre 0x109bba 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x13)) s (0x109bba + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109bba 4 0 (.sib 4 none 0 (.d8 0x13))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[127, 53]
    (.letOp (n := 133) (.out 0x109bbe (movzxR32M8Effect 0x109bbe 5 0 (.sib 4 none 0 (.d8 0xd))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 134) (.exec 0x109bbe (LoadPre 0x109bbe (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xd)) s (0x109bbe + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109bbe 5 0 (.sib 4 none 0 (.d8 0xd))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 135) (.out 0x109bc3 (movzxR32M8Effect 0x109bc3 5 1 (.sib 4 none 0 (.d8 0x12))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 136) (.exec 0x109bc3 (LoadPre 0x109bc3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x12)) s (0x109bc3 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109bc3 5 1 (.sib 4 none 0 (.d8 0x12))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 137) (.exec 0x109bc8 (StorePre 0x109bc8 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xd)) s (0x109bc8 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109bc8 4 1 (.sib 4 none 0 (.d8 0xd))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[135, 53]
    (.letOp (n := 138) (.exec 0x109bcc (StorePre 0x109bcc 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x12)) s (0x109bcc + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109bcc 4 0 (.sib 4 none 0 (.d8 0x12))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[133, 53]
    (.letOp (n := 139) (.out 0x109bd0 (movzxR32M8Effect 0x109bd0 5 0 (.sib 4 none 0 (.d8 0xe))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 140) (.exec 0x109bd0 (LoadPre 0x109bd0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x109bd0 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109bd0 5 0 (.sib 4 none 0 (.d8 0xe))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 141) (.out 0x109bd5 (movzxR32M8Effect 0x109bd5 5 1 (.sib 4 none 0 (.d8 0x11))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 142) (.exec 0x109bd5 (LoadPre 0x109bd5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x11)) s (0x109bd5 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109bd5 5 1 (.sib 4 none 0 (.d8 0x11))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 143) (.exec 0x109bda (StorePre 0x109bda 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x109bda + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109bda 4 1 (.sib 4 none 0 (.d8 0xe))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[141, 53]
    (b_l109ac0_3))))))))))))))))))))))))))))))

def bytes_l109ac0_2 : List UInt8 :=
  [0x88, 0x44, 0x24, 0x16, 0x0F, 0xB6, 0x44, 0x24, 0x0A, 0x0F, 0xB6, 0x4C, 0x24, 0x15, 0x88, 0x4C,
    0x24, 0x0A, 0x88, 0x44, 0x24, 0x15, 0x0F, 0xB6, 0x44, 0x24, 0x0B, 0x0F, 0xB6, 0x4C, 0x24, 0x14,
    0x88, 0x4C, 0x24, 0x0B, 0x88, 0x44, 0x24, 0x14, 0x0F, 0xB6, 0x44, 0x24, 0x0C, 0x0F, 0xB6, 0x4C,
    0x24, 0x13, 0x88, 0x4C, 0x24, 0x0C, 0x88, 0x44, 0x24, 0x13, 0x0F, 0xB6, 0x44, 0x24, 0x0D, 0x0F,
    0xB6, 0x4C, 0x24, 0x12, 0x88, 0x4C, 0x24, 0x0D, 0x88, 0x44, 0x24, 0x12, 0x0F, 0xB6, 0x44, 0x24,
    0x0E, 0x0F, 0xB6, 0x4C, 0x24, 0x11, 0x88, 0x4C, 0x24, 0x0E] ++ bytes_l109ac0_3

theorem code_l109ac0_2 : ∀ x ∈ codeRange 0x109b84 bytes_l109ac0_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x9b84 90 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l109ac0_3

@[cfg_block] def b_l109ac0_1 : Block Op Label signature Reg.count 84 :=
  .letOp (n := 84) (.exec 0x109b20 (StorePre 0x109b20 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x109b20 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109b20 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[81, 53]
    (.letOp (n := 85) (.out 0x109b25 (movR64M64Effect 0x109b25 0 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 86) (.exec 0x109b25 (LoadPre 0x109b25 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x109b25 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109b25 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 87) (.exec 0x109b2a (StorePre 0x109b2a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x109b2a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109b2a 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[85, 53]
    (.letOp (n := 88) (.out 0x109b2f (movR64M64Effect 0x109b2f 0 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 89) (.exec 0x109b2f (LoadPre 0x109b2f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x109b2f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109b2f 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 90) (.exec 0x109b34 (StorePre 0x109b34 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x109b34 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109b34 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[88, 53]
    (.letOp (n := 91) (.out 0x109b39 (movR64M64Effect 0x109b39 0 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 92) (.exec 0x109b39 (LoadPre 0x109b39 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x109b39 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109b39 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 93) (.exec 0x109b3e (StorePre 0x109b3e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x109b3e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109b3e 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[91, 53]
    (.letOp (n := 94) (.out 0x109b43 (movR64M64Effect 0x109b43 0 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 95) (.exec 0x109b43 (LoadPre 0x109b43 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x109b43 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109b43 0 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 96) (.exec 0x109b48 (StorePre 0x109b48 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x109b48 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109b48 0 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[94, 53]
    (.letOp (n := 97) (.out 0x109b4d (movR64M64Effect 0x109b4d 0 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 98) (.exec 0x109b4d (LoadPre 0x109b4d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x109b4d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109b4d 0 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 99) (.exec 0x109b52 (StorePre 0x109b52 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x109b52 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109b52 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[97, 53]
    (.letOp (n := 100) (.out 0x109b57 (movR64M64Effect 0x109b57 0 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 101) (.exec 0x109b57 (LoadPre 0x109b57 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x109b57 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x109b57 0 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 102) (.exec 0x109b5f (StorePre 0x109b5f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x109b5f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109b5f 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[100, 53]
    (.letOp (n := 103) (.out 0x109b64 (movzxR32M8Effect 0x109b64 5 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 104) (.exec 0x109b64 (LoadPre 0x109b64 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109b64 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109b64 5 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 105) (.out 0x109b69 (movzxR32M8Effect 0x109b69 5 1 (.sib 4 none 0 (.d8 0x17))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 106) (.exec 0x109b69 (LoadPre 0x109b69 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x17)) s (0x109b69 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109b69 5 1 (.sib 4 none 0 (.d8 0x17))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 107) (.exec 0x109b6e (StorePre 0x109b6e 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109b6e + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109b6e 4 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[105, 53]
    (.letOp (n := 108) (.exec 0x109b72 (StorePre 0x109b72 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x17)) s (0x109b72 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109b72 4 0 (.sib 4 none 0 (.d8 0x17))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[103, 53]
    (.letOp (n := 109) (.out 0x109b76 (movzxR32M8Effect 0x109b76 5 0 (.sib 4 none 0 (.d8 0x9))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 110) (.exec 0x109b76 (LoadPre 0x109b76 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x9)) s (0x109b76 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109b76 5 0 (.sib 4 none 0 (.d8 0x9))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 111) (.out 0x109b7b (movzxR32M8Effect 0x109b7b 5 1 (.sib 4 none 0 (.d8 0x16))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 112) (.exec 0x109b7b (LoadPre 0x109b7b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x16)) s (0x109b7b + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109b7b 5 1 (.sib 4 none 0 (.d8 0x16))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 113) (.exec 0x109b80 (StorePre 0x109b80 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x9)) s (0x109b80 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109b80 4 1 (.sib 4 none 0 (.d8 0x9))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[111, 53]
    (b_l109ac0_2))))))))))))))))))))))))))))))

def bytes_l109ac0_1 : List UInt8 :=
  [0x48, 0x89, 0x4C, 0x24, 0x10, 0x48, 0x8B, 0x44, 0x24, 0x58, 0x48, 0x89, 0x44, 0x24, 0x18, 0x48,
    0x8B, 0x44, 0x24, 0x60, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x68, 0x48, 0x89,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x44, 0x24, 0x70, 0x48, 0x89, 0x44, 0x24, 0x30, 0x48, 0x8B, 0x44,
    0x24, 0x78, 0x48, 0x89, 0x44, 0x24, 0x38, 0x48, 0x8B, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48,
    0x89, 0x44, 0x24, 0x40, 0x0F, 0xB6, 0x44, 0x24, 0x08, 0x0F, 0xB6, 0x4C, 0x24, 0x17, 0x88, 0x4C,
    0x24, 0x08, 0x88, 0x44, 0x24, 0x17, 0x0F, 0xB6, 0x44, 0x24, 0x09, 0x0F, 0xB6, 0x4C, 0x24, 0x16,
    0x88, 0x4C, 0x24, 0x09] ++ bytes_l109ac0_2

theorem code_l109ac0_1 : ∀ x ∈ codeRange 0x109b20 bytes_l109ac0_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x9b20 100 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l109ac0_2

@[cfg_block] def b_l109ac0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x109ac0 (subR64Imm32Effect 0x109ac0 4 0x88) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 54) (.exec 0x109ac0 (fun s => s.RIP = 0x109ac0) (subR64Imm32Effect 0x109ac0 4 0x88) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x109ac7 (movR64M64Effect 0x109ac7 0 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 56) (.exec 0x109ac7 (LoadPre 0x109ac7 (fun s => AddrMode.addr (.base 6 .none) s (0x109ac7 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x109ac7 0 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 57) (.out 0x109aca (movR64M64Effect 0x109aca 1 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[6]
    (.letOp (n := 58) (.exec 0x109aca (LoadPre 0x109aca (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x109aca + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109aca 1 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 59) (.exec 0x109ace (StorePre 0x109ace 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x109ace + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109ace 1 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[57, 53]
    (.letOp (n := 60) (.exec 0x109ad3 (StorePre 0x109ad3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x109ad3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109ad3 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 53]
    (.letOp (n := 61) (.out 0x109ad8 (movR64M64Effect 0x109ad8 0 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 62) (.exec 0x109ad8 (LoadPre 0x109ad8 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x109ad8 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109ad8 0 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 63) (.out 0x109adc (movR64M64Effect 0x109adc 1 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[6]
    (.letOp (n := 64) (.exec 0x109adc (LoadPre 0x109adc (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x109adc + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109adc 1 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 65) (.exec 0x109ae0 (StorePre 0x109ae0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x109ae0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109ae0 1 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[63, 53]
    (.letOp (n := 66) (.exec 0x109ae5 (StorePre 0x109ae5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x109ae5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109ae5 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[61, 53]
    (.letOp (n := 67) (.out 0x109aea (movR64M64Effect 0x109aea 0 (.base 6 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 68) (.exec 0x109aea (LoadPre 0x109aea (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x109aea + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109aea 0 (.base 6 (.d8 0x20))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 69) (.out 0x109aee (movR64M64Effect 0x109aee 1 (.base 6 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[6]
    (.letOp (n := 70) (.exec 0x109aee (LoadPre 0x109aee (fun s => AddrMode.addr (.base 6 (.d8 0x28)) s (0x109aee + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109aee 1 (.base 6 (.d8 0x28))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 71) (.exec 0x109af2 (StorePre 0x109af2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x109af2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109af2 1 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[69, 53]
    (.letOp (n := 72) (.exec 0x109af7 (StorePre 0x109af7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x109af7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109af7 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[67, 53]
    (.letOp (n := 73) (.out 0x109afc (movR64M64Effect 0x109afc 0 (.base 6 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 74) (.exec 0x109afc (LoadPre 0x109afc (fun s => AddrMode.addr (.base 6 (.d8 0x30)) s (0x109afc + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109afc 0 (.base 6 (.d8 0x30))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 75) (.out 0x109b00 (movR64M64Effect 0x109b00 1 (.base 6 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[6]
    (.letOp (n := 76) (.exec 0x109b00 (LoadPre 0x109b00 (fun s => AddrMode.addr (.base 6 (.d8 0x38)) s (0x109b00 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109b00 1 (.base 6 (.d8 0x38))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 77) (.exec 0x109b04 (StorePre 0x109b04 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x109b04 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109b04 0 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[73, 53]
    (.letOp (n := 78) (.exec 0x109b09 (StorePre 0x109b09 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x109b09 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x109b09 1 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[75, 53]
    (.letOp (n := 79) (.out 0x109b11 (movR64M64Effect 0x109b11 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 80) (.exec 0x109b11 (LoadPre 0x109b11 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x109b11 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109b11 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 81) (.out 0x109b16 (movR64M64Effect 0x109b16 1 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 82) (.exec 0x109b16 (LoadPre 0x109b16 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x109b16 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109b16 1 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 83) (.exec 0x109b1b (StorePre 0x109b1b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109b1b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109b1b 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[79, 53]
    (b_l109ac0_1)))))))))))))))))))))))))))))))

def bytes_l109ac0 : List UInt8 :=
  [0x48, 0x81, 0xEC, 0x88, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x06, 0x48, 0x8B, 0x4E, 0x08, 0x48, 0x89,
    0x4C, 0x24, 0x50, 0x48, 0x89, 0x44, 0x24, 0x48, 0x48, 0x8B, 0x46, 0x10, 0x48, 0x8B, 0x4E, 0x18,
    0x48, 0x89, 0x4C, 0x24, 0x60, 0x48, 0x89, 0x44, 0x24, 0x58, 0x48, 0x8B, 0x46, 0x20, 0x48, 0x8B,
    0x4E, 0x28, 0x48, 0x89, 0x4C, 0x24, 0x70, 0x48, 0x89, 0x44, 0x24, 0x68, 0x48, 0x8B, 0x46, 0x30,
    0x48, 0x8B, 0x4E, 0x38, 0x48, 0x89, 0x44, 0x24, 0x78, 0x48, 0x89, 0x8C, 0x24, 0x80, 0x00, 0x00,
    0x00, 0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x8B, 0x4C, 0x24, 0x50, 0x48, 0x89, 0x44, 0x24, 0x08] ++ bytes_l109ac0_1

theorem code_l109ac0 : ∀ x ∈ codeRange 0x109ac0 bytes_l109ac0, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x9ac0 96 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l109ac0_1

@[cfg_block] def b_l109d81 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x109d81 (addR64Imm32Effect 0x109d81 4 0x88) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 54) (.exec 0x109d81 (fun s => s.RIP = 0x109d81) (addR64Imm32Effect 0x109d81 4 0x88) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x109d88 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[53]
    (.letOp (n := 56) (.out 0x109d88 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[53]
    (.letOp (n := 57) (.exec 0x109d88 (RetPre 0x109d88) (retEffect) (Reg.operands [.gpr 4] [])) #v[53]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 56), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 58) (some ⟨55, by decide⟩)))))))

def bytes_l109d81 : List UInt8 :=
  [0x48, 0x81, 0xC4, 0x88, 0x00, 0x00, 0x00, 0xC3]

theorem code_l109d81 : ∀ x ∈ codeRange 0x109d81 bytes_l109d81, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9d81 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109d90 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x109d90 (pushR64Effect 0x109d90 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x109d90 (PushPre 0x109d90 1) (pushR64Effect 0x109d90 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x109d91 (pushR64Effect 0x109d91 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[53, 3]
    (.letOp (n := 56) (.exec 0x109d91 (PushPre 0x109d91 1) (pushR64Effect 0x109d91 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[53, 3]
    (.letOp (n := 57) (.out 0x109d92 (pushR64Effect 0x109d92 1 0) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 0] []) (.reg (.gpr 4))) #v[55, 0]
    (.letOp (n := 58) (.exec 0x109d92 (PushPre 0x109d92 1) (pushR64Effect 0x109d92 1 0) (Reg.operands [.gpr 4, .gpr 0] [])) #v[55, 0]
    (.letOp (n := 59) (.out 0x109d93 (testR64R64Effect 0x109d93 2 2) (EffectPart.reads (.flag .ZF) [.gpr 2, .gpr 2] []) (.flag .ZF)) #v[2, 2]
    (.letOp (n := 60) (.exec 0x109d93 (fun s => s.RIP = 0x109d93) (testR64R64Effect 0x109d93 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 61) (.pure (condOp 4)) #v[59]
    (.terminate (.condBr (Fin.last 61) ⟨.l109f41, RegMap.args [(0, 0), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ ⟨.l109d9c, RegMap.args [(0, 0), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩))))))))))

def bytes_l109d90 : List UInt8 :=
  [0x55, 0x53, 0x50, 0x48, 0x85, 0xD2, 0x0F, 0x84, 0xA5, 0x01, 0x00, 0x00]

theorem code_l109d90 : ∀ x ∈ codeRange 0x109d90 bytes_l109d90, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9d90 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109d9c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x109d9c (cmpR64Imm8Effect 0x109d9c 2 0x1) (EffectPart.reads (.flag .ZF) [.gpr 2] []) (.flag .ZF)) #v[2]
    (.letOp (n := 54) (.exec 0x109d9c (fun s => s.RIP = 0x109d9c) (cmpR64Imm8Effect 0x109d9c 2 0x1) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l109f51, RegMap.args [(2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l109da6, RegMap.args [(2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l109d9c : List UInt8 :=
  [0x48, 0x83, 0xFA, 0x01, 0x0F, 0x84, 0xAB, 0x01, 0x00, 0x00]

theorem code_l109d9c : ∀ x ∈ codeRange 0x109d9c bytes_l109d9c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9d9c 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109da6 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x109da6 (cmpR64Imm8Effect 0x109da6 2 0x2) (EffectPart.reads (.flag .CF) [.gpr 2] []) (.flag .CF)) #v[2]
    (.letOp (n := 54) (.out 0x109da6 (cmpR64Imm8Effect 0x109da6 2 0x2) (EffectPart.reads (.flag .ZF) [.gpr 2] []) (.flag .ZF)) #v[2]
    (.letOp (n := 55) (.exec 0x109da6 (fun s => s.RIP = 0x109da6) (cmpR64Imm8Effect 0x109da6 2 0x2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 56) (.pure (condOp 6)) #v[53, 54]
    (.terminate (.condBr (Fin.last 56) ⟨.l109f67, RegMap.args [(2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩ ⟨.l109db0, RegMap.args [(2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l109da6 : List UInt8 :=
  [0x48, 0x83, 0xFA, 0x02, 0x0F, 0x86, 0xB7, 0x01, 0x00, 0x00]

theorem code_l109da6 : ∀ x ∈ codeRange 0x109da6 bytes_l109da6, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9da6 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109db0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x109db0 (cmpR64Imm8Effect 0x109db0 2 0x3) (EffectPart.reads (.flag .ZF) [.gpr 2] []) (.flag .ZF)) #v[2]
    (.letOp (n := 54) (.exec 0x109db0 (fun s => s.RIP = 0x109db0) (cmpR64Imm8Effect 0x109db0 2 0x3) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l109f7d, RegMap.args [(2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l109dba, RegMap.args [(2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l109db0 : List UInt8 :=
  [0x48, 0x83, 0xFA, 0x03, 0x0F, 0x84, 0xC3, 0x01, 0x00, 0x00]

theorem code_l109db0 : ∀ x ∈ codeRange 0x109db0 bytes_l109db0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9db0 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109dba : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x109dba (cmpR64Imm8Effect 0x109dba 2 0x4) (EffectPart.reads (.flag .CF) [.gpr 2] []) (.flag .CF)) #v[2]
    (.letOp (n := 54) (.out 0x109dba (cmpR64Imm8Effect 0x109dba 2 0x4) (EffectPart.reads (.flag .ZF) [.gpr 2] []) (.flag .ZF)) #v[2]
    (.letOp (n := 55) (.exec 0x109dba (fun s => s.RIP = 0x109dba) (cmpR64Imm8Effect 0x109dba 2 0x4) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 56) (.pure (condOp 6)) #v[53, 54]
    (.terminate (.condBr (Fin.last 56) ⟨.l109f93, RegMap.args [(2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩ ⟨.l109dc4, RegMap.args [(2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l109dba : List UInt8 :=
  [0x48, 0x83, 0xFA, 0x04, 0x0F, 0x86, 0xCF, 0x01, 0x00, 0x00]

theorem code_l109dba : ∀ x ∈ codeRange 0x109dba bytes_l109dba, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9dba 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109dc4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x109dc4 (cmpR64Imm8Effect 0x109dc4 2 0x5) (EffectPart.reads (.flag .ZF) [.gpr 2] []) (.flag .ZF)) #v[2]
    (.letOp (n := 54) (.exec 0x109dc4 (fun s => s.RIP = 0x109dc4) (cmpR64Imm8Effect 0x109dc4 2 0x5) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l109fa9, RegMap.args [(2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l109dce, RegMap.args [(2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l109dc4 : List UInt8 :=
  [0x48, 0x83, 0xFA, 0x05, 0x0F, 0x84, 0xDB, 0x01, 0x00, 0x00]

theorem code_l109dc4 : ∀ x ∈ codeRange 0x109dc4 bytes_l109dc4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9dc4 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109dce : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x109dce (cmpR64Imm8Effect 0x109dce 2 0x6) (EffectPart.reads (.flag .CF) [.gpr 2] []) (.flag .CF)) #v[2]
    (.letOp (n := 54) (.out 0x109dce (cmpR64Imm8Effect 0x109dce 2 0x6) (EffectPart.reads (.flag .ZF) [.gpr 2] []) (.flag .ZF)) #v[2]
    (.letOp (n := 55) (.exec 0x109dce (fun s => s.RIP = 0x109dce) (cmpR64Imm8Effect 0x109dce 2 0x6) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 56) (.pure (condOp 6)) #v[53, 54]
    (.terminate (.condBr (Fin.last 56) ⟨.l109fbf, RegMap.args [(2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩ ⟨.l109dd8, RegMap.args [(2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l109dce : List UInt8 :=
  [0x48, 0x83, 0xFA, 0x06, 0x0F, 0x86, 0xE7, 0x01, 0x00, 0x00]

theorem code_l109dce : ∀ x ∈ codeRange 0x109dce bytes_l109dce, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9dce 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109dd8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x109dd8 (cmpR64Imm8Effect 0x109dd8 2 0x7) (EffectPart.reads (.flag .ZF) [.gpr 2] []) (.flag .ZF)) #v[2]
    (.letOp (n := 54) (.exec 0x109dd8 (fun s => s.RIP = 0x109dd8) (cmpR64Imm8Effect 0x109dd8 2 0x7) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l109fd5, RegMap.args [(2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l109de2, RegMap.args [(2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l109dd8 : List UInt8 :=
  [0x48, 0x83, 0xFA, 0x07, 0x0F, 0x84, 0xF3, 0x01, 0x00, 0x00]

theorem code_l109dd8 : ∀ x ∈ codeRange 0x109dd8 bytes_l109dd8, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9dd8 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109de2_5 : Block Op Label signature Reg.count 241 :=
  .letOp (n := 241) (.out 0x109f1b (andEaxImm32Effect 0x109f1b 0xf0f) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[239]
    (.letOp (n := 242) (.exec 0x109f1b (fun s => s.RIP = 0x109f1b) (andEaxImm32Effect 0x109f1b 0xf0f) (Reg.operands [.gpr 0] [])) #v[239]
    (.letOp (n := 243) (.out 0x109f20 (xorR32R32Effect 0x109f20 2 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 0] []) (.reg (.gpr 5))) #v[193, 241]
    (.letOp (n := 244) (.exec 0x109f20 (fun s => s.RIP = 0x109f20) (xorR32R32Effect 0x109f20 2 5 0) (Reg.operands [.gpr 5, .gpr 0] [])) #v[193, 241]
    (.letOp (n := 245) (.out 0x109f22 (shlR32Effect 0x109f22 3 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[241]
    (.letOp (n := 246) (.exec 0x109f22 (fun s => s.RIP = 0x109f22) (shlR32Effect 0x109f22 3 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[241]
    (.letOp (n := 247) (.out 0x109f25 (xorR32R32Effect 0x109f25 3 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[245, 178]
    (.letOp (n := 248) (.exec 0x109f25 (fun s => s.RIP = 0x109f25) (xorR32R32Effect 0x109f25 3 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[245, 178]
    (.letOp (n := 249) (.exec 0x109f28 (StorePre 0x109f28 3 (fun s => AddrMode.addr (.base 7 (.d8 0xc)) s (0x109f28 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x109f28 3 0 (.base 7 (.d8 0xc))) (Reg.operands [.gpr 0, .gpr 7] [])) #v[247, 7]
    (.letOp (n := 250) (.exec 0x109f2b (StorePre 0x109f2b 4 (fun s => AddrMode.addr (.base 7 (.d8 0xd)) s (0x109f2b + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109f2b 4 5 (.base 7 (.d8 0xd))) (Reg.operands [.gpr 5, .gpr 7] [])) #v[243, 7]
    (.letOp (n := 251) (.out 0x109f2f (movR32R32Effect 0x109f2f 2 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[243]
    (.letOp (n := 252) (.exec 0x109f2f (fun s => s.RIP = 0x109f2f) (movR32R32Effect 0x109f2f 2 1 5) (Reg.operands [.gpr 5] [])) #v[243]
    (.letOp (n := 253) (.exec 0x109f31 (StorePre 0x109f31 3 (fun s => AddrMode.addr (.base 7 (.d8 0xe)) s (0x109f31 + BitVec.ofNat 64 3)) 1) (movM8R8NoRexEffect 0x109f31 3 4 (.base 7 (.d8 0xe))) (Reg.operands [.gpr 0, .gpr 7] [])) #v[247, 7]
    (.letOp (n := 254) (.exec 0x109f34 (StorePre 0x109f34 3 (fun s => AddrMode.addr (.base 7 (.d8 0xf)) s (0x109f34 + BitVec.ofNat 64 3)) 1) (movM8R8NoRexEffect 0x109f34 3 5 (.base 7 (.d8 0xf))) (Reg.operands [.gpr 1, .gpr 7] [])) #v[251, 7]
    (.letOp (n := 255) (.out 0x109f37 (movR64R64Effect 0x109f37 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 256) (.exec 0x109f37 (fun s => s.RIP = 0x109f37) (movR64R64Effect 0x109f37 0 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 257) (.out 0x109f3a (addR64Imm8Effect 0x109f3a 4 0x8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 258) (.exec 0x109f3a (fun s => s.RIP = 0x109f3a) (addR64Imm8Effect 0x109f3a 4 0x8) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 259) (.out 0x109f3e (popR64Effect 0x109f3e 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[257]
    (.letOp (n := 260) (.out 0x109f3e (popR64Effect 0x109f3e 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[257]
    (.letOp (n := 261) (.exec 0x109f3e (PopPre 0x109f3e) (popR64Effect 0x109f3e 1 3) (Reg.operands [.gpr 4] [])) #v[257]
    (.letOp (n := 262) (.out 0x109f3f (popR64Effect 0x109f3f 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[260]
    (.letOp (n := 263) (.out 0x109f3f (popR64Effect 0x109f3f 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[260]
    (.letOp (n := 264) (.exec 0x109f3f (PopPre 0x109f3f) (popR64Effect 0x109f3f 1 5) (Reg.operands [.gpr 4] [])) #v[260]
    (.letOp (n := 265) (.out 0x109f40 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[263]
    (.letOp (n := 266) (.out 0x109f40 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[263]
    (.letOp (n := 267) (.exec 0x109f40 (RetPre 0x109f40) (retEffect) (Reg.operands [.gpr 4] [])) #v[263]
    (.terminate (.ret (RegMap.args [(0, 255), (1, 251), (2, 133), (3, 259), (4, 266), (5, 262), (6, 182), (7, 7), (8, 105), (9, 77), (10, 178), (11, 137), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 268) (some ⟨265, by decide⟩)))))))))))))))))))))))))))))

def bytes_l109de2_5 : List UInt8 :=
  [0x25, 0x0F, 0x0F, 0x00, 0x00, 0x31, 0xC5, 0xC1, 0xE0, 0x04, 0x44, 0x31, 0xD0, 0x88, 0x47, 0x0C,
    0x40, 0x88, 0x6F, 0x0D, 0x89, 0xE9, 0x88, 0x67, 0x0E, 0x88, 0x6F, 0x0F, 0x48, 0x89, 0xF8, 0x48,
    0x83, 0xC4, 0x08, 0x5B, 0x5D, 0xC3]

theorem code_l109de2_5 : ∀ x ∈ codeRange 0x109f1b bytes_l109de2_5, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9f1b 38 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109de2_4 : Block Op Label signature Reg.count 209 :=
  .letOp (n := 209) (.out 0x109ee3 (shlR32Effect 0x109ee3 3 1 4) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[205]
    (.letOp (n := 210) (.exec 0x109ee3 (fun s => s.RIP = 0x109ee3) (shlR32Effect 0x109ee3 3 1 4) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[205]
    (.letOp (n := 211) (.out 0x109ee6 (xorR32R32Effect 0x109ee6 2 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[209, 182]
    (.letOp (n := 212) (.exec 0x109ee6 (fun s => s.RIP = 0x109ee6) (xorR32R32Effect 0x109ee6 2 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[209, 182]
    (.letOp (n := 213) (.exec 0x109ee8 (StorePre 0x109ee8 3 (fun s => AddrMode.addr (.base 7 (.d8 0x4)) s (0x109ee8 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x109ee8 3 1 (.base 7 (.d8 0x4))) (Reg.operands [.gpr 1, .gpr 7] [])) #v[211, 7]
    (.letOp (n := 214) (.exec 0x109eeb (StorePre 0x109eeb 3 (fun s => AddrMode.addr (.base 7 (.d8 0x5)) s (0x109eeb + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x109eeb 3 0 (.base 7 (.d8 0x5))) (Reg.operands [.gpr 0, .gpr 7] [])) #v[207, 7]
    (.letOp (n := 215) (.exec 0x109eee (StorePre 0x109eee 3 (fun s => AddrMode.addr (.base 7 (.d8 0x6)) s (0x109eee + BitVec.ofNat 64 3)) 1) (movM8R8NoRexEffect 0x109eee 3 5 (.base 7 (.d8 0x6))) (Reg.operands [.gpr 1, .gpr 7] [])) #v[211, 7]
    (.letOp (n := 216) (.exec 0x109ef1 (StorePre 0x109ef1 3 (fun s => AddrMode.addr (.base 7 (.d8 0x7)) s (0x109ef1 + BitVec.ofNat 64 3)) 1) (movM8R8NoRexEffect 0x109ef1 3 4 (.base 7 (.d8 0x7))) (Reg.operands [.gpr 0, .gpr 7] [])) #v[207, 7]
    (.letOp (n := 217) (.out 0x109ef4 (movR32R32Effect 0x109ef4 2 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[133]
    (.letOp (n := 218) (.exec 0x109ef4 (fun s => s.RIP = 0x109ef4) (movR32R32Effect 0x109ef4 2 0 2) (Reg.operands [.gpr 2] [])) #v[133]
    (.letOp (n := 219) (.out 0x109ef6 (shrR32Effect 0x109ef6 3 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[217]
    (.letOp (n := 220) (.exec 0x109ef6 (fun s => s.RIP = 0x109ef6) (shrR32Effect 0x109ef6 3 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[217]
    (.letOp (n := 221) (.out 0x109ef9 (xorR32R32Effect 0x109ef9 2 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[219, 147]
    (.letOp (n := 222) (.exec 0x109ef9 (fun s => s.RIP = 0x109ef9) (xorR32R32Effect 0x109ef9 2 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[219, 147]
    (.letOp (n := 223) (.out 0x109efb (andEaxImm32Effect 0x109efb 0xf0f) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[221]
    (.letOp (n := 224) (.exec 0x109efb (fun s => s.RIP = 0x109efb) (andEaxImm32Effect 0x109efb 0xf0f) (Reg.operands [.gpr 0] [])) #v[221]
    (.letOp (n := 225) (.out 0x109f00 (xorR32R32Effect 0x109f00 2 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0] []) (.reg (.gpr 3))) #v[147, 223]
    (.letOp (n := 226) (.exec 0x109f00 (fun s => s.RIP = 0x109f00) (xorR32R32Effect 0x109f00 2 3 0) (Reg.operands [.gpr 3, .gpr 0] [])) #v[147, 223]
    (.letOp (n := 227) (.out 0x109f02 (shlR32Effect 0x109f02 3 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[223]
    (.letOp (n := 228) (.exec 0x109f02 (fun s => s.RIP = 0x109f02) (shlR32Effect 0x109f02 3 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[223]
    (.letOp (n := 229) (.out 0x109f05 (xorR32R32Effect 0x109f05 2 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[227, 133]
    (.letOp (n := 230) (.exec 0x109f05 (fun s => s.RIP = 0x109f05) (xorR32R32Effect 0x109f05 2 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[227, 133]
    (.letOp (n := 231) (.exec 0x109f07 (StorePre 0x109f07 3 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x109f07 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x109f07 3 0 (.base 7 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 7] [])) #v[229, 7]
    (.letOp (n := 232) (.exec 0x109f0a (StorePre 0x109f0a 3 (fun s => AddrMode.addr (.base 7 (.d8 0x9)) s (0x109f0a + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x109f0a 3 3 (.base 7 (.d8 0x9))) (Reg.operands [.gpr 3, .gpr 7] [])) #v[225, 7]
    (.letOp (n := 233) (.exec 0x109f0d (StorePre 0x109f0d 3 (fun s => AddrMode.addr (.base 7 (.d8 0xa)) s (0x109f0d + BitVec.ofNat 64 3)) 1) (movM8R8NoRexEffect 0x109f0d 3 4 (.base 7 (.d8 0xa))) (Reg.operands [.gpr 0, .gpr 7] [])) #v[229, 7]
    (.letOp (n := 234) (.exec 0x109f10 (StorePre 0x109f10 3 (fun s => AddrMode.addr (.base 7 (.d8 0xb)) s (0x109f10 + BitVec.ofNat 64 3)) 1) (movM8R8NoRexEffect 0x109f10 3 7 (.base 7 (.d8 0xb))) (Reg.operands [.gpr 3, .gpr 7] [])) #v[225, 7]
    (.letOp (n := 235) (.out 0x109f13 (movR32R32Effect 0x109f13 3 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[178]
    (.letOp (n := 236) (.exec 0x109f13 (fun s => s.RIP = 0x109f13) (movR32R32Effect 0x109f13 3 0 10) (Reg.operands [.gpr 10] [])) #v[178]
    (.letOp (n := 237) (.out 0x109f16 (shrR32Effect 0x109f16 3 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[235]
    (.letOp (n := 238) (.exec 0x109f16 (fun s => s.RIP = 0x109f16) (shrR32Effect 0x109f16 3 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[235]
    (.letOp (n := 239) (.out 0x109f19 (xorR32R32Effect 0x109f19 2 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[237, 193]
    (.letOp (n := 240) (.exec 0x109f19 (fun s => s.RIP = 0x109f19) (xorR32R32Effect 0x109f19 2 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[237, 193]
    (b_l109de2_5))))))))))))))))))))))))))))))))

def bytes_l109de2_4 : List UInt8 :=
  [0xC1, 0xE1, 0x04, 0x31, 0xF1, 0x88, 0x4F, 0x04, 0x88, 0x47, 0x05, 0x88, 0x6F, 0x06, 0x88, 0x67,
    0x07, 0x89, 0xD0, 0xC1, 0xE8, 0x04, 0x31, 0xD8, 0x25, 0x0F, 0x0F, 0x00, 0x00, 0x31, 0xC3, 0xC1,
    0xE0, 0x04, 0x31, 0xD0, 0x88, 0x47, 0x08, 0x88, 0x5F, 0x09, 0x88, 0x67, 0x0A, 0x88, 0x7F, 0x0B,
    0x44, 0x89, 0xD0, 0xC1, 0xE8, 0x04, 0x31, 0xE8] ++ bytes_l109de2_5

theorem code_l109de2_4 : ∀ x ∈ codeRange 0x109ee3 bytes_l109de2_4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x9ee3 56 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l109de2_5

@[cfg_block] def b_l109de2_3 : Block Op Label signature Reg.count 170 :=
  .letOp (n := 170) (.out 0x109ea4 (movR32R32Effect 0x109ea4 3 6 9) (EffectPart.reads (.reg (.gpr 6)) [.gpr 9] []) (.reg (.gpr 6))) #v[77]
    (.letOp (n := 171) (.exec 0x109ea4 (fun s => s.RIP = 0x109ea4) (movR32R32Effect 0x109ea4 3 6 9) (Reg.operands [.gpr 9] [])) #v[77]
    (.letOp (n := 172) (.out 0x109ea7 (shrR32Effect 0x109ea7 3 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[170]
    (.letOp (n := 173) (.exec 0x109ea7 (fun s => s.RIP = 0x109ea7) (shrR32Effect 0x109ea7 3 6 2) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[170]
    (.letOp (n := 174) (.out 0x109eaa (xorR32R32Effect 0x109eaa 3 6 10) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 10] []) (.reg (.gpr 6))) #v[172, 91]
    (.letOp (n := 175) (.exec 0x109eaa (fun s => s.RIP = 0x109eaa) (xorR32R32Effect 0x109eaa 3 6 10) (Reg.operands [.gpr 6, .gpr 10] [])) #v[172, 91]
    (.letOp (n := 176) (.out 0x109ead (andR32Imm32Effect 0x109ead 6 6 0x3333) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[174]
    (.letOp (n := 177) (.exec 0x109ead (fun s => s.RIP = 0x109ead) (andR32Imm32Effect 0x109ead 6 6 0x3333) (Reg.operands [.gpr 6] [])) #v[174]
    (.letOp (n := 178) (.out 0x109eb3 (xorR32R32Effect 0x109eb3 3 10 6) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 6] []) (.reg (.gpr 10))) #v[91, 176]
    (.letOp (n := 179) (.exec 0x109eb3 (fun s => s.RIP = 0x109eb3) (xorR32R32Effect 0x109eb3 3 10 6) (Reg.operands [.gpr 10, .gpr 6] [])) #v[91, 176]
    (.letOp (n := 180) (.out 0x109eb6 (shlR32Effect 0x109eb6 3 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[176]
    (.letOp (n := 181) (.exec 0x109eb6 (fun s => s.RIP = 0x109eb6) (shlR32Effect 0x109eb6 3 6 2) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[176]
    (.letOp (n := 182) (.out 0x109eb9 (xorR32R32Effect 0x109eb9 3 6 9) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 9] []) (.reg (.gpr 6))) #v[180, 77]
    (.letOp (n := 183) (.exec 0x109eb9 (fun s => s.RIP = 0x109eb9) (xorR32R32Effect 0x109eb9 3 6 9) (Reg.operands [.gpr 6, .gpr 9] [])) #v[180, 77]
    (.letOp (n := 184) (.exec 0x109ebc (StorePre 0x109ebc 3 (fun s => AddrMode.addr (.base 7 (.d8 0x3)) s (0x109ebc + BitVec.ofNat 64 3)) 1) (movM8R8NoRexEffect 0x109ebc 3 5 (.base 7 (.d8 0x3))) (Reg.operands [.gpr 1, .gpr 7] [])) #v[161, 7]
    (.letOp (n := 185) (.out 0x109ebf (movR32R32Effect 0x109ebf 3 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[105]
    (.letOp (n := 186) (.exec 0x109ebf (fun s => s.RIP = 0x109ebf) (movR32R32Effect 0x109ebf 3 0 8) (Reg.operands [.gpr 8] [])) #v[105]
    (.letOp (n := 187) (.out 0x109ec2 (shrR32Effect 0x109ec2 3 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[185]
    (.letOp (n := 188) (.exec 0x109ec2 (fun s => s.RIP = 0x109ec2) (shrR32Effect 0x109ec2 3 0 2) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[185]
    (.letOp (n := 189) (.out 0x109ec5 (xorR32R32Effect 0x109ec5 2 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[187, 119]
    (.letOp (n := 190) (.exec 0x109ec5 (fun s => s.RIP = 0x109ec5) (xorR32R32Effect 0x109ec5 2 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[187, 119]
    (.letOp (n := 191) (.out 0x109ec7 (andEaxImm32Effect 0x109ec7 0x3333) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[189]
    (.letOp (n := 192) (.exec 0x109ec7 (fun s => s.RIP = 0x109ec7) (andEaxImm32Effect 0x109ec7 0x3333) (Reg.operands [.gpr 0] [])) #v[189]
    (.letOp (n := 193) (.out 0x109ecc (xorR32R32Effect 0x109ecc 2 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 0] []) (.reg (.gpr 5))) #v[119, 191]
    (.letOp (n := 194) (.exec 0x109ecc (fun s => s.RIP = 0x109ecc) (xorR32R32Effect 0x109ecc 2 5 0) (Reg.operands [.gpr 5, .gpr 0] [])) #v[119, 191]
    (.letOp (n := 195) (.out 0x109ece (shlR32Effect 0x109ece 3 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[191]
    (.letOp (n := 196) (.exec 0x109ece (fun s => s.RIP = 0x109ece) (shlR32Effect 0x109ece 3 0 2) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[191]
    (.letOp (n := 197) (.out 0x109ed1 (xorR32R32Effect 0x109ed1 3 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 8] []) (.reg (.gpr 0))) #v[195, 105]
    (.letOp (n := 198) (.exec 0x109ed1 (fun s => s.RIP = 0x109ed1) (xorR32R32Effect 0x109ed1 3 0 8) (Reg.operands [.gpr 0, .gpr 8] [])) #v[195, 105]
    (.letOp (n := 199) (.out 0x109ed4 (movR32R32Effect 0x109ed4 2 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[182]
    (.letOp (n := 200) (.exec 0x109ed4 (fun s => s.RIP = 0x109ed4) (movR32R32Effect 0x109ed4 2 1 6) (Reg.operands [.gpr 6] [])) #v[182]
    (.letOp (n := 201) (.out 0x109ed6 (shrR32Effect 0x109ed6 3 1 4) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[199]
    (.letOp (n := 202) (.exec 0x109ed6 (fun s => s.RIP = 0x109ed6) (shrR32Effect 0x109ed6 3 1 4) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[199]
    (.letOp (n := 203) (.out 0x109ed9 (xorR32R32Effect 0x109ed9 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[201, 197]
    (.letOp (n := 204) (.exec 0x109ed9 (fun s => s.RIP = 0x109ed9) (xorR32R32Effect 0x109ed9 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[201, 197]
    (.letOp (n := 205) (.out 0x109edb (andR32Imm32Effect 0x109edb 6 1 0xf0f) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[203]
    (.letOp (n := 206) (.exec 0x109edb (fun s => s.RIP = 0x109edb) (andR32Imm32Effect 0x109edb 6 1 0xf0f) (Reg.operands [.gpr 1] [])) #v[203]
    (.letOp (n := 207) (.out 0x109ee1 (xorR32R32Effect 0x109ee1 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[197, 205]
    (.letOp (n := 208) (.exec 0x109ee1 (fun s => s.RIP = 0x109ee1) (xorR32R32Effect 0x109ee1 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[197, 205]
    (b_l109de2_4)))))))))))))))))))))))))))))))))))))))

def bytes_l109de2_3 : List UInt8 :=
  [0x44, 0x89, 0xCE, 0xC1, 0xEE, 0x02, 0x44, 0x31, 0xD6, 0x81, 0xE6, 0x33, 0x33, 0x00, 0x00, 0x41,
    0x31, 0xF2, 0xC1, 0xE6, 0x02, 0x44, 0x31, 0xCE, 0x88, 0x6F, 0x03, 0x44, 0x89, 0xC0, 0xC1, 0xE8,
    0x02, 0x31, 0xE8, 0x25, 0x33, 0x33, 0x00, 0x00, 0x31, 0xC5, 0xC1, 0xE0, 0x02, 0x44, 0x31, 0xC0,
    0x89, 0xF1, 0xC1, 0xE9, 0x04, 0x31, 0xC1, 0x81, 0xE1, 0x0F, 0x0F, 0x00, 0x00, 0x31, 0xC8] ++ bytes_l109de2_4

theorem code_l109de2_3 : ∀ x ∈ codeRange 0x109ea4 bytes_l109de2_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x9ea4 63 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l109de2_4

@[cfg_block] def b_l109de2_2 : Block Op Label signature Reg.count 133 :=
  .letOp (n := 133) (.out 0x109e69 (xorR32R32Effect 0x109e69 3 2 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 11] []) (.reg (.gpr 2))) #v[95, 131]
    (.letOp (n := 134) (.exec 0x109e69 (fun s => s.RIP = 0x109e69) (xorR32R32Effect 0x109e69 3 2 11) (Reg.operands [.gpr 2, .gpr 11] [])) #v[95, 131]
    (.letOp (n := 135) (.out 0x109e6c (shlR32Effect 0x109e6c 4 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[131]
    (.letOp (n := 136) (.exec 0x109e6c (fun s => s.RIP = 0x109e6c) (shlR32Effect 0x109e6c 4 11 2) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[131]
    (.letOp (n := 137) (.out 0x109e70 (xorR32R32Effect 0x109e70 3 11 1) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 1] []) (.reg (.gpr 11))) #v[135, 81]
    (.letOp (n := 138) (.exec 0x109e70 (fun s => s.RIP = 0x109e70) (xorR32R32Effect 0x109e70 3 11 1) (Reg.operands [.gpr 11, .gpr 1] [])) #v[135, 81]
    (.letOp (n := 139) (.out 0x109e73 (movR32R32Effect 0x109e73 2 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[109]
    (.letOp (n := 140) (.exec 0x109e73 (fun s => s.RIP = 0x109e73) (movR32R32Effect 0x109e73 2 1 6) (Reg.operands [.gpr 6] [])) #v[109]
    (.letOp (n := 141) (.out 0x109e75 (shrR32Effect 0x109e75 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[139]
    (.letOp (n := 142) (.exec 0x109e75 (fun s => s.RIP = 0x109e75) (shrR32Effect 0x109e75 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[139]
    (.letOp (n := 143) (.out 0x109e78 (xorR32R32Effect 0x109e78 2 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 3] []) (.reg (.gpr 1))) #v[141, 123]
    (.letOp (n := 144) (.exec 0x109e78 (fun s => s.RIP = 0x109e78) (xorR32R32Effect 0x109e78 2 1 3) (Reg.operands [.gpr 1, .gpr 3] [])) #v[141, 123]
    (.letOp (n := 145) (.out 0x109e7a (andR32Imm32Effect 0x109e7a 6 1 0x3333) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[143]
    (.letOp (n := 146) (.exec 0x109e7a (fun s => s.RIP = 0x109e7a) (andR32Imm32Effect 0x109e7a 6 1 0x3333) (Reg.operands [.gpr 1] [])) #v[143]
    (.letOp (n := 147) (.out 0x109e80 (xorR32R32Effect 0x109e80 2 3 1) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 1] []) (.reg (.gpr 3))) #v[123, 145]
    (.letOp (n := 148) (.exec 0x109e80 (fun s => s.RIP = 0x109e80) (xorR32R32Effect 0x109e80 2 3 1) (Reg.operands [.gpr 3, .gpr 1] [])) #v[123, 145]
    (.letOp (n := 149) (.out 0x109e82 (shlR32Effect 0x109e82 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[145]
    (.letOp (n := 150) (.exec 0x109e82 (fun s => s.RIP = 0x109e82) (shlR32Effect 0x109e82 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[145]
    (.letOp (n := 151) (.out 0x109e85 (xorR32R32Effect 0x109e85 2 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[149, 109]
    (.letOp (n := 152) (.exec 0x109e85 (fun s => s.RIP = 0x109e85) (xorR32R32Effect 0x109e85 2 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[149, 109]
    (.letOp (n := 153) (.out 0x109e87 (movR32R32Effect 0x109e87 3 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[137]
    (.letOp (n := 154) (.exec 0x109e87 (fun s => s.RIP = 0x109e87) (movR32R32Effect 0x109e87 3 0 11) (Reg.operands [.gpr 11] [])) #v[137]
    (.letOp (n := 155) (.out 0x109e8a (shrR32Effect 0x109e8a 3 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[153]
    (.letOp (n := 156) (.exec 0x109e8a (fun s => s.RIP = 0x109e8a) (shrR32Effect 0x109e8a 3 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[153]
    (.letOp (n := 157) (.out 0x109e8d (xorR32R32Effect 0x109e8d 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[155, 151]
    (.letOp (n := 158) (.exec 0x109e8d (fun s => s.RIP = 0x109e8d) (xorR32R32Effect 0x109e8d 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[155, 151]
    (.letOp (n := 159) (.out 0x109e8f (andEaxImm32Effect 0x109e8f 0xf0f) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[157]
    (.letOp (n := 160) (.exec 0x109e8f (fun s => s.RIP = 0x109e8f) (andEaxImm32Effect 0x109e8f 0xf0f) (Reg.operands [.gpr 0] [])) #v[157]
    (.letOp (n := 161) (.out 0x109e94 (xorR32R32Effect 0x109e94 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[151, 159]
    (.letOp (n := 162) (.exec 0x109e94 (fun s => s.RIP = 0x109e94) (xorR32R32Effect 0x109e94 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[151, 159]
    (.letOp (n := 163) (.out 0x109e96 (shlR32Effect 0x109e96 3 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[159]
    (.letOp (n := 164) (.exec 0x109e96 (fun s => s.RIP = 0x109e96) (shlR32Effect 0x109e96 3 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[159]
    (.letOp (n := 165) (.out 0x109e99 (xorR32R32Effect 0x109e99 3 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[163, 137]
    (.letOp (n := 166) (.exec 0x109e99 (fun s => s.RIP = 0x109e99) (xorR32R32Effect 0x109e99 3 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[163, 137]
    (.letOp (n := 167) (.exec 0x109e9c (StorePre 0x109e9c 2 (fun s => AddrMode.addr (.base 7 .none) s (0x109e9c + BitVec.ofNat 64 2)) 1) (movM8R8Effect 0x109e9c 2 0 (.base 7 .none)) (Reg.operands [.gpr 0, .gpr 7] [])) #v[165, 7]
    (.letOp (n := 168) (.exec 0x109e9e (StorePre 0x109e9e 3 (fun s => AddrMode.addr (.base 7 (.d8 0x1)) s (0x109e9e + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x109e9e 3 1 (.base 7 (.d8 0x1))) (Reg.operands [.gpr 1, .gpr 7] [])) #v[161, 7]
    (.letOp (n := 169) (.exec 0x109ea1 (StorePre 0x109ea1 3 (fun s => AddrMode.addr (.base 7 (.d8 0x2)) s (0x109ea1 + BitVec.ofNat 64 3)) 1) (movM8R8NoRexEffect 0x109ea1 3 4 (.base 7 (.d8 0x2))) (Reg.operands [.gpr 0, .gpr 7] [])) #v[165, 7]
    (b_l109de2_3)))))))))))))))))))))))))))))))))))))

def bytes_l109de2_2 : List UInt8 :=
  [0x44, 0x31, 0xDA, 0x41, 0xC1, 0xE3, 0x02, 0x41, 0x31, 0xCB, 0x89, 0xF1, 0xC1, 0xE9, 0x02, 0x31,
    0xD9, 0x81, 0xE1, 0x33, 0x33, 0x00, 0x00, 0x31, 0xCB, 0xC1, 0xE1, 0x02, 0x31, 0xF1, 0x44, 0x89,
    0xD8, 0xC1, 0xE8, 0x04, 0x31, 0xC8, 0x25, 0x0F, 0x0F, 0x00, 0x00, 0x31, 0xC1, 0xC1, 0xE0, 0x04,
    0x44, 0x31, 0xD8, 0x88, 0x07, 0x88, 0x4F, 0x01, 0x88, 0x67, 0x02] ++ bytes_l109de2_3

theorem code_l109de2_2 : ∀ x ∈ codeRange 0x109e69 bytes_l109de2_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x9e69 59 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l109de2_3

@[cfg_block] def b_l109de2_1 : Block Op Label signature Reg.count 93 :=
  .letOp (n := 93) (.out 0x109e2b (addR32R32Effect 0x109e2b 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[89, 89]
    (.letOp (n := 94) (.exec 0x109e2b (fun s => s.RIP = 0x109e2b) (addR32R32Effect 0x109e2b 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[89, 89]
    (.letOp (n := 95) (.out 0x109e2d (xorR32R32Effect 0x109e2d 2 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 3] []) (.reg (.gpr 2))) #v[93, 57]
    (.letOp (n := 96) (.exec 0x109e2d (fun s => s.RIP = 0x109e2d) (xorR32R32Effect 0x109e2d 2 2 3) (Reg.operands [.gpr 2, .gpr 3] [])) #v[93, 57]
    (.letOp (n := 97) (.out 0x109e2f (movzxR32R16Effect 0x109e2f 4 6 11) (EffectPart.reads (.reg (.gpr 6)) [.gpr 11] []) (.reg (.gpr 6))) #v[61]
    (.letOp (n := 98) (.exec 0x109e2f (fun s => s.RIP = 0x109e2f) (movzxR32R16Effect 0x109e2f 4 6 11) (Reg.operands [.gpr 11] [])) #v[61]
    (.letOp (n := 99) (.out 0x109e33 (shrR32Effect 0x109e33 2 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[97]
    (.letOp (n := 100) (.exec 0x109e33 (fun s => s.RIP = 0x109e33) (shrR32Effect 0x109e33 2 6 1) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[97]
    (.letOp (n := 101) (.out 0x109e35 (xorR32R32Effect 0x109e35 3 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 8] []) (.reg (.gpr 6))) #v[99, 63]
    (.letOp (n := 102) (.exec 0x109e35 (fun s => s.RIP = 0x109e35) (xorR32R32Effect 0x109e35 3 6 8) (Reg.operands [.gpr 6, .gpr 8] [])) #v[99, 63]
    (.letOp (n := 103) (.out 0x109e38 (andR32Imm32Effect 0x109e38 6 6 0x5555) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[101]
    (.letOp (n := 104) (.exec 0x109e38 (fun s => s.RIP = 0x109e38) (andR32Imm32Effect 0x109e38 6 6 0x5555) (Reg.operands [.gpr 6] [])) #v[101]
    (.letOp (n := 105) (.out 0x109e3e (xorR32R32Effect 0x109e3e 3 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6] []) (.reg (.gpr 8))) #v[63, 103]
    (.letOp (n := 106) (.exec 0x109e3e (fun s => s.RIP = 0x109e3e) (xorR32R32Effect 0x109e3e 3 8 6) (Reg.operands [.gpr 8, .gpr 6] [])) #v[63, 103]
    (.letOp (n := 107) (.out 0x109e41 (addR32R32Effect 0x109e41 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[103, 103]
    (.letOp (n := 108) (.exec 0x109e41 (fun s => s.RIP = 0x109e41) (addR32R32Effect 0x109e41 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[103, 103]
    (.letOp (n := 109) (.out 0x109e43 (xorR32R32Effect 0x109e43 3 6 11) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 11] []) (.reg (.gpr 6))) #v[107, 61]
    (.letOp (n := 110) (.exec 0x109e43 (fun s => s.RIP = 0x109e43) (xorR32R32Effect 0x109e43 3 6 11) (Reg.operands [.gpr 6, .gpr 11] [])) #v[107, 61]
    (.letOp (n := 111) (.out 0x109e46 (movR32R32Effect 0x109e46 2 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[65]
    (.letOp (n := 112) (.exec 0x109e46 (fun s => s.RIP = 0x109e46) (movR32R32Effect 0x109e46 2 3 0) (Reg.operands [.gpr 0] [])) #v[65]
    (.letOp (n := 113) (.out 0x109e48 (shrR32Effect 0x109e48 2 3 1) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[111]
    (.letOp (n := 114) (.exec 0x109e48 (fun s => s.RIP = 0x109e48) (shrR32Effect 0x109e48 2 3 1) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[111]
    (.letOp (n := 115) (.out 0x109e4a (xorR32R32Effect 0x109e4a 2 3 5) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 5] []) (.reg (.gpr 3))) #v[113, 67]
    (.letOp (n := 116) (.exec 0x109e4a (fun s => s.RIP = 0x109e4a) (xorR32R32Effect 0x109e4a 2 3 5) (Reg.operands [.gpr 3, .gpr 5] [])) #v[113, 67]
    (.letOp (n := 117) (.out 0x109e4c (andR32Imm32Effect 0x109e4c 6 3 0x5555) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[115]
    (.letOp (n := 118) (.exec 0x109e4c (fun s => s.RIP = 0x109e4c) (andR32Imm32Effect 0x109e4c 6 3 0x5555) (Reg.operands [.gpr 3] [])) #v[115]
    (.letOp (n := 119) (.out 0x109e52 (xorR32R32Effect 0x109e52 2 5 3) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 3] []) (.reg (.gpr 5))) #v[67, 117]
    (.letOp (n := 120) (.exec 0x109e52 (fun s => s.RIP = 0x109e52) (xorR32R32Effect 0x109e52 2 5 3) (Reg.operands [.gpr 5, .gpr 3] [])) #v[67, 117]
    (.letOp (n := 121) (.out 0x109e54 (addR32R32Effect 0x109e54 2 3 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 3] []) (.reg (.gpr 3))) #v[117, 117]
    (.letOp (n := 122) (.exec 0x109e54 (fun s => s.RIP = 0x109e54) (addR32R32Effect 0x109e54 2 3 3) (Reg.operands [.gpr 3, .gpr 3] [])) #v[117, 117]
    (.letOp (n := 123) (.out 0x109e56 (xorR32R32Effect 0x109e56 2 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0] []) (.reg (.gpr 3))) #v[121, 65]
    (.letOp (n := 124) (.exec 0x109e56 (fun s => s.RIP = 0x109e56) (xorR32R32Effect 0x109e56 2 3 0) (Reg.operands [.gpr 3, .gpr 0] [])) #v[121, 65]
    (.letOp (n := 125) (.out 0x109e58 (movR32R32Effect 0x109e58 3 11 1) (EffectPart.reads (.reg (.gpr 11)) [.gpr 1] []) (.reg (.gpr 11))) #v[81]
    (.letOp (n := 126) (.exec 0x109e58 (fun s => s.RIP = 0x109e58) (movR32R32Effect 0x109e58 3 11 1) (Reg.operands [.gpr 1] [])) #v[81]
    (.letOp (n := 127) (.out 0x109e5b (shrR32Effect 0x109e5b 4 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[125]
    (.letOp (n := 128) (.exec 0x109e5b (fun s => s.RIP = 0x109e5b) (shrR32Effect 0x109e5b 4 11 2) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[125]
    (.letOp (n := 129) (.out 0x109e5f (xorR32R32Effect 0x109e5f 3 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 2] []) (.reg (.gpr 11))) #v[127, 95]
    (.letOp (n := 130) (.exec 0x109e5f (fun s => s.RIP = 0x109e5f) (xorR32R32Effect 0x109e5f 3 11 2) (Reg.operands [.gpr 11, .gpr 2] [])) #v[127, 95]
    (.letOp (n := 131) (.out 0x109e62 (andR32Imm32Effect 0x109e62 7 11 0x3333) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11] []) (.reg (.gpr 11))) #v[129]
    (.letOp (n := 132) (.exec 0x109e62 (fun s => s.RIP = 0x109e62) (andR32Imm32Effect 0x109e62 7 11 0x3333) (Reg.operands [.gpr 11] [])) #v[129]
    (b_l109de2_2))))))))))))))))))))))))))))))))))))))))

def bytes_l109de2_1 : List UInt8 :=
  [0x01, 0xD2, 0x31, 0xDA, 0x41, 0x0F, 0xB7, 0xF3, 0xD1, 0xEE, 0x44, 0x31, 0xC6, 0x81, 0xE6, 0x55,
    0x55, 0x00, 0x00, 0x41, 0x31, 0xF0, 0x01, 0xF6, 0x44, 0x31, 0xDE, 0x89, 0xC3, 0xD1, 0xEB, 0x31,
    0xEB, 0x81, 0xE3, 0x55, 0x55, 0x00, 0x00, 0x31, 0xDD, 0x01, 0xDB, 0x31, 0xC3, 0x41, 0x89, 0xCB,
    0x41, 0xC1, 0xEB, 0x02, 0x41, 0x31, 0xD3, 0x41, 0x81, 0xE3, 0x33, 0x33, 0x00, 0x00] ++ bytes_l109de2_2

theorem code_l109de2_1 : ∀ x ∈ codeRange 0x109e2b bytes_l109de2_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x9e2b 62 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l109de2_2

@[cfg_block] def b_l109de2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x109de2 (movzxR32M16Effect 0x109de2 3 2 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6] []) (.reg (.gpr 2))) #v[6]
    (.letOp (n := 54) (.exec 0x109de2 (LoadPre 0x109de2 (fun s => AddrMode.addr (.base 6 .none) s (0x109de2 + BitVec.ofNat 64 3)) 2) (movzxR32M16Effect 0x109de2 3 2 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 55) (.out 0x109de5 (movzxR32M16Effect 0x109de5 5 9 (.base 6 (.d8 0x2))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 6] []) (.reg (.gpr 9))) #v[6]
    (.letOp (n := 56) (.exec 0x109de5 (LoadPre 0x109de5 (fun s => AddrMode.addr (.base 6 (.d8 0x2)) s (0x109de5 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x109de5 5 9 (.base 6 (.d8 0x2))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 57) (.out 0x109dea (movzxR32M16Effect 0x109dea 4 3 (.base 6 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 6] []) (.reg (.gpr 3))) #v[6]
    (.letOp (n := 58) (.exec 0x109dea (LoadPre 0x109dea (fun s => AddrMode.addr (.base 6 (.d8 0x4)) s (0x109dea + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x109dea 4 3 (.base 6 (.d8 0x4))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 59) (.out 0x109dee (movzxR32M16Effect 0x109dee 5 10 (.base 6 (.d8 0x6))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 6] []) (.reg (.gpr 10))) #v[6]
    (.letOp (n := 60) (.exec 0x109dee (LoadPre 0x109dee (fun s => AddrMode.addr (.base 6 (.d8 0x6)) s (0x109dee + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x109dee 5 10 (.base 6 (.d8 0x6))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 61) (.out 0x109df3 (movzxR32M16Effect 0x109df3 5 11 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 6] []) (.reg (.gpr 11))) #v[6]
    (.letOp (n := 62) (.exec 0x109df3 (LoadPre 0x109df3 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x109df3 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x109df3 5 11 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 63) (.out 0x109df8 (movzxR32M16Effect 0x109df8 5 8 (.base 6 (.d8 0xa))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 6] []) (.reg (.gpr 8))) #v[6]
    (.letOp (n := 64) (.exec 0x109df8 (LoadPre 0x109df8 (fun s => AddrMode.addr (.base 6 (.d8 0xa)) s (0x109df8 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x109df8 5 8 (.base 6 (.d8 0xa))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 65) (.out 0x109dfd (movzxR32M16Effect 0x109dfd 4 0 (.base 6 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 66) (.exec 0x109dfd (LoadPre 0x109dfd (fun s => AddrMode.addr (.base 6 (.d8 0xc)) s (0x109dfd + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x109dfd 4 0 (.base 6 (.d8 0xc))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 67) (.out 0x109e01 (movzxR32M16Effect 0x109e01 4 5 (.base 6 (.d8 0xe))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 6] []) (.reg (.gpr 5))) #v[6]
    (.letOp (n := 68) (.exec 0x109e01 (LoadPre 0x109e01 (fun s => AddrMode.addr (.base 6 (.d8 0xe)) s (0x109e01 + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x109e01 4 5 (.base 6 (.d8 0xe))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 69) (.out 0x109e05 (movzxR32R16Effect 0x109e05 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 70) (.exec 0x109e05 (fun s => s.RIP = 0x109e05) (movzxR32R16Effect 0x109e05 3 1 2) (Reg.operands [.gpr 2] [])) #v[53]
    (.letOp (n := 71) (.out 0x109e08 (shrR32Effect 0x109e08 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[69]
    (.letOp (n := 72) (.exec 0x109e08 (fun s => s.RIP = 0x109e08) (shrR32Effect 0x109e08 2 1 1) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[69]
    (.letOp (n := 73) (.out 0x109e0a (xorR32R32Effect 0x109e0a 3 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 9] []) (.reg (.gpr 1))) #v[71, 55]
    (.letOp (n := 74) (.exec 0x109e0a (fun s => s.RIP = 0x109e0a) (xorR32R32Effect 0x109e0a 3 1 9) (Reg.operands [.gpr 1, .gpr 9] [])) #v[71, 55]
    (.letOp (n := 75) (.out 0x109e0d (andR32Imm32Effect 0x109e0d 6 1 0x5555) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[73]
    (.letOp (n := 76) (.exec 0x109e0d (fun s => s.RIP = 0x109e0d) (andR32Imm32Effect 0x109e0d 6 1 0x5555) (Reg.operands [.gpr 1] [])) #v[73]
    (.letOp (n := 77) (.out 0x109e13 (xorR32R32Effect 0x109e13 3 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1] []) (.reg (.gpr 9))) #v[55, 75]
    (.letOp (n := 78) (.exec 0x109e13 (fun s => s.RIP = 0x109e13) (xorR32R32Effect 0x109e13 3 9 1) (Reg.operands [.gpr 9, .gpr 1] [])) #v[55, 75]
    (.letOp (n := 79) (.out 0x109e16 (addR32R32Effect 0x109e16 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[75, 75]
    (.letOp (n := 80) (.exec 0x109e16 (fun s => s.RIP = 0x109e16) (addR32R32Effect 0x109e16 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[75, 75]
    (.letOp (n := 81) (.out 0x109e18 (xorR32R32Effect 0x109e18 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[79, 53]
    (.letOp (n := 82) (.exec 0x109e18 (fun s => s.RIP = 0x109e18) (xorR32R32Effect 0x109e18 2 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[79, 53]
    (.letOp (n := 83) (.out 0x109e1a (movzxR32R16Effect 0x109e1a 3 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3] []) (.reg (.gpr 2))) #v[57]
    (.letOp (n := 84) (.exec 0x109e1a (fun s => s.RIP = 0x109e1a) (movzxR32R16Effect 0x109e1a 3 2 3) (Reg.operands [.gpr 3] [])) #v[57]
    (.letOp (n := 85) (.out 0x109e1d (shrR32Effect 0x109e1d 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[83]
    (.letOp (n := 86) (.exec 0x109e1d (fun s => s.RIP = 0x109e1d) (shrR32Effect 0x109e1d 2 2 1) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[83]
    (.letOp (n := 87) (.out 0x109e1f (xorR32R32Effect 0x109e1f 3 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 10] []) (.reg (.gpr 2))) #v[85, 59]
    (.letOp (n := 88) (.exec 0x109e1f (fun s => s.RIP = 0x109e1f) (xorR32R32Effect 0x109e1f 3 2 10) (Reg.operands [.gpr 2, .gpr 10] [])) #v[85, 59]
    (.letOp (n := 89) (.out 0x109e22 (andR32Imm32Effect 0x109e22 6 2 0x5555) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[87]
    (.letOp (n := 90) (.exec 0x109e22 (fun s => s.RIP = 0x109e22) (andR32Imm32Effect 0x109e22 6 2 0x5555) (Reg.operands [.gpr 2] [])) #v[87]
    (.letOp (n := 91) (.out 0x109e28 (xorR32R32Effect 0x109e28 3 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2] []) (.reg (.gpr 10))) #v[59, 89]
    (.letOp (n := 92) (.exec 0x109e28 (fun s => s.RIP = 0x109e28) (xorR32R32Effect 0x109e28 3 10 2) (Reg.operands [.gpr 10, .gpr 2] [])) #v[59, 89]
    (b_l109de2_1))))))))))))))))))))))))))))))))))))))))

def bytes_l109de2 : List UInt8 :=
  [0x0F, 0xB7, 0x16, 0x44, 0x0F, 0xB7, 0x4E, 0x02, 0x0F, 0xB7, 0x5E, 0x04, 0x44, 0x0F, 0xB7, 0x56,
    0x06, 0x44, 0x0F, 0xB7, 0x5E, 0x08, 0x44, 0x0F, 0xB7, 0x46, 0x0A, 0x0F, 0xB7, 0x46, 0x0C, 0x0F,
    0xB7, 0x6E, 0x0E, 0x0F, 0xB7, 0xCA, 0xD1, 0xE9, 0x44, 0x31, 0xC9, 0x81, 0xE1, 0x55, 0x55, 0x00,
    0x00, 0x41, 0x31, 0xC9, 0x01, 0xC9, 0x31, 0xD1, 0x0F, 0xB7, 0xD3, 0xD1, 0xEA, 0x44, 0x31, 0xD2,
    0x81, 0xE2, 0x55, 0x55, 0x00, 0x00, 0x41, 0x31, 0xD2] ++ bytes_l109de2_1

theorem code_l109de2 : ∀ x ∈ codeRange 0x109de2 bytes_l109de2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x9de2 73 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l109de2_1

@[cfg_block] def b_l109f41 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x109f41 (xorR32R32Effect 0x109f41 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[7, 7]
    (.letOp (n := 54) (.exec 0x109f41 (fun s => s.RIP = 0x109f41) (xorR32R32Effect 0x109f41 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[7, 7]
    (.letOp (n := 55) (.out 0x109f43 (xorR32R32Effect 0x109f43 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[6, 6]
    (.letOp (n := 56) (.exec 0x109f43 (fun s => s.RIP = 0x109f43) (xorR32R32Effect 0x109f43 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 57) (.out 0x109f45 (movR64Imm32Effect 0x109f45 2 0x201058) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x109f45 (fun s => s.RIP = 0x109f45) (movR64Imm32Effect 0x109f45 2 0x201058) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x109f4c (callEffect (fun _ => 0x103837) 0x109f51) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x109f4c (PushPre 0x109f4c 5) (callEffect (fun _ => 0x103837) 0x109f51) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x109f51⟩) #v[]
    (.terminate (.call ⟨.l103837, RegMap.args [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)] 62⟩ { target := .l109f51, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l109f41 : List UInt8 :=
  [0x31, 0xFF, 0x31, 0xF6, 0x48, 0xC7, 0xC2, 0x58, 0x10, 0x20, 0x00, 0xE8, 0xE6, 0x98, 0xFF, 0xFF]

theorem code_l109f41 : ∀ x ∈ codeRange 0x109f41 bytes_l109f41, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9f41 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109f51 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x109f51 (movR32Imm32Effect 0x109f51 5 7 0x1) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 54) (.exec 0x109f51 (fun s => s.RIP = 0x109f51) (movR32Imm32Effect 0x109f51 5 7 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x109f56 (movR32Imm32Effect 0x109f56 5 6 0x1) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 56) (.exec 0x109f56 (fun s => s.RIP = 0x109f56) (movR32Imm32Effect 0x109f56 5 6 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x109f5b (movR64Imm32Effect 0x109f5b 2 0x201070) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x109f5b (fun s => s.RIP = 0x109f5b) (movR64Imm32Effect 0x109f5b 2 0x201070) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x109f62 (callEffect (fun _ => 0x103837) 0x109f67) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x109f62 (PushPre 0x109f62 5) (callEffect (fun _ => 0x103837) 0x109f67) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x109f67⟩) #v[]
    (.terminate (.call ⟨.l103837, RegMap.args [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)] 62⟩ { target := .l109f67, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l109f51 : List UInt8 :=
  [0xBF, 0x01, 0x00, 0x00, 0x00, 0xBE, 0x01, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC2, 0x70, 0x10, 0x20,
    0x00, 0xE8, 0xD0, 0x98, 0xFF, 0xFF]

theorem code_l109f51 : ∀ x ∈ codeRange 0x109f51 bytes_l109f51, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9f51 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109f67 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x109f67 (movR32Imm32Effect 0x109f67 5 7 0x2) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 54) (.exec 0x109f67 (fun s => s.RIP = 0x109f67) (movR32Imm32Effect 0x109f67 5 7 0x2) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x109f6c (movR32Imm32Effect 0x109f6c 5 6 0x2) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 56) (.exec 0x109f6c (fun s => s.RIP = 0x109f6c) (movR32Imm32Effect 0x109f6c 5 6 0x2) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x109f71 (movR64Imm32Effect 0x109f71 2 0x201088) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x109f71 (fun s => s.RIP = 0x109f71) (movR64Imm32Effect 0x109f71 2 0x201088) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x109f78 (callEffect (fun _ => 0x103837) 0x109f7d) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x109f78 (PushPre 0x109f78 5) (callEffect (fun _ => 0x103837) 0x109f7d) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x109f7d⟩) #v[]
    (.terminate (.call ⟨.l103837, RegMap.args [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)] 62⟩ { target := .l109f7d, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l109f67 : List UInt8 :=
  [0xBF, 0x02, 0x00, 0x00, 0x00, 0xBE, 0x02, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC2, 0x88, 0x10, 0x20,
    0x00, 0xE8, 0xBA, 0x98, 0xFF, 0xFF]

theorem code_l109f67 : ∀ x ∈ codeRange 0x109f67 bytes_l109f67, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9f67 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109f7d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x109f7d (movR32Imm32Effect 0x109f7d 5 7 0x3) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 54) (.exec 0x109f7d (fun s => s.RIP = 0x109f7d) (movR32Imm32Effect 0x109f7d 5 7 0x3) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x109f82 (movR32Imm32Effect 0x109f82 5 6 0x3) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 56) (.exec 0x109f82 (fun s => s.RIP = 0x109f82) (movR32Imm32Effect 0x109f82 5 6 0x3) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x109f87 (movR64Imm32Effect 0x109f87 2 0x2010a0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x109f87 (fun s => s.RIP = 0x109f87) (movR64Imm32Effect 0x109f87 2 0x2010a0) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x109f8e (callEffect (fun _ => 0x103837) 0x109f93) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x109f8e (PushPre 0x109f8e 5) (callEffect (fun _ => 0x103837) 0x109f93) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x109f93⟩) #v[]
    (.terminate (.call ⟨.l103837, RegMap.args [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)] 62⟩ { target := .l109f93, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l109f7d : List UInt8 :=
  [0xBF, 0x03, 0x00, 0x00, 0x00, 0xBE, 0x03, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC2, 0xA0, 0x10, 0x20,
    0x00, 0xE8, 0xA4, 0x98, 0xFF, 0xFF]

theorem code_l109f7d : ∀ x ∈ codeRange 0x109f7d bytes_l109f7d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9f7d 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109f93 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x109f93 (movR32Imm32Effect 0x109f93 5 7 0x4) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 54) (.exec 0x109f93 (fun s => s.RIP = 0x109f93) (movR32Imm32Effect 0x109f93 5 7 0x4) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x109f98 (movR32Imm32Effect 0x109f98 5 6 0x4) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 56) (.exec 0x109f98 (fun s => s.RIP = 0x109f98) (movR32Imm32Effect 0x109f98 5 6 0x4) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x109f9d (movR64Imm32Effect 0x109f9d 2 0x2010b8) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x109f9d (fun s => s.RIP = 0x109f9d) (movR64Imm32Effect 0x109f9d 2 0x2010b8) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x109fa4 (callEffect (fun _ => 0x103837) 0x109fa9) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x109fa4 (PushPre 0x109fa4 5) (callEffect (fun _ => 0x103837) 0x109fa9) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x109fa9⟩) #v[]
    (.terminate (.call ⟨.l103837, RegMap.args [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)] 62⟩ { target := .l109fa9, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l109f93 : List UInt8 :=
  [0xBF, 0x04, 0x00, 0x00, 0x00, 0xBE, 0x04, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC2, 0xB8, 0x10, 0x20,
    0x00, 0xE8, 0x8E, 0x98, 0xFF, 0xFF]

theorem code_l109f93 : ∀ x ∈ codeRange 0x109f93 bytes_l109f93, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9f93 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109fa9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x109fa9 (movR32Imm32Effect 0x109fa9 5 7 0x5) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 54) (.exec 0x109fa9 (fun s => s.RIP = 0x109fa9) (movR32Imm32Effect 0x109fa9 5 7 0x5) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x109fae (movR32Imm32Effect 0x109fae 5 6 0x5) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 56) (.exec 0x109fae (fun s => s.RIP = 0x109fae) (movR32Imm32Effect 0x109fae 5 6 0x5) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x109fb3 (movR64Imm32Effect 0x109fb3 2 0x2010d0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x109fb3 (fun s => s.RIP = 0x109fb3) (movR64Imm32Effect 0x109fb3 2 0x2010d0) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x109fba (callEffect (fun _ => 0x103837) 0x109fbf) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x109fba (PushPre 0x109fba 5) (callEffect (fun _ => 0x103837) 0x109fbf) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x109fbf⟩) #v[]
    (.terminate (.call ⟨.l103837, RegMap.args [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)] 62⟩ { target := .l109fbf, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l109fa9 : List UInt8 :=
  [0xBF, 0x05, 0x00, 0x00, 0x00, 0xBE, 0x05, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC2, 0xD0, 0x10, 0x20,
    0x00, 0xE8, 0x78, 0x98, 0xFF, 0xFF]

theorem code_l109fa9 : ∀ x ∈ codeRange 0x109fa9 bytes_l109fa9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9fa9 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109fbf : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x109fbf (movR32Imm32Effect 0x109fbf 5 7 0x6) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 54) (.exec 0x109fbf (fun s => s.RIP = 0x109fbf) (movR32Imm32Effect 0x109fbf 5 7 0x6) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x109fc4 (movR32Imm32Effect 0x109fc4 5 6 0x6) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 56) (.exec 0x109fc4 (fun s => s.RIP = 0x109fc4) (movR32Imm32Effect 0x109fc4 5 6 0x6) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x109fc9 (movR64Imm32Effect 0x109fc9 2 0x2010e8) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x109fc9 (fun s => s.RIP = 0x109fc9) (movR64Imm32Effect 0x109fc9 2 0x2010e8) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x109fd0 (callEffect (fun _ => 0x103837) 0x109fd5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x109fd0 (PushPre 0x109fd0 5) (callEffect (fun _ => 0x103837) 0x109fd5) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x109fd5⟩) #v[]
    (.terminate (.call ⟨.l103837, RegMap.args [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)] 62⟩ { target := .l109fd5, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l109fbf : List UInt8 :=
  [0xBF, 0x06, 0x00, 0x00, 0x00, 0xBE, 0x06, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC2, 0xE8, 0x10, 0x20,
    0x00, 0xE8, 0x62, 0x98, 0xFF, 0xFF]

theorem code_l109fbf : ∀ x ∈ codeRange 0x109fbf bytes_l109fbf, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9fbf 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109fd5 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x109fd5 (movR32Imm32Effect 0x109fd5 5 7 0x7) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 54) (.exec 0x109fd5 (fun s => s.RIP = 0x109fd5) (movR32Imm32Effect 0x109fd5 5 7 0x7) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x109fda (movR32Imm32Effect 0x109fda 5 6 0x7) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 56) (.exec 0x109fda (fun s => s.RIP = 0x109fda) (movR32Imm32Effect 0x109fda 5 6 0x7) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x109fdf (movR64Imm32Effect 0x109fdf 2 0x201100) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x109fdf (fun s => s.RIP = 0x109fdf) (movR64Imm32Effect 0x109fdf 2 0x201100) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x109fe6 (callEffect (fun _ => 0x103837) 0x109feb) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x109fe6 (PushPre 0x109fe6 5) (callEffect (fun _ => 0x103837) 0x109feb) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x109feb⟩) #v[]
    (.terminate (.call ⟨.l103837, RegMap.args [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)] 62⟩ { target := .l109feb, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l109fd5 : List UInt8 :=
  [0xBF, 0x07, 0x00, 0x00, 0x00, 0xBE, 0x07, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC2, 0x00, 0x11, 0x20,
    0x00, 0xE8, 0x4C, 0x98, 0xFF, 0xFF]

theorem code_l109fd5 : ∀ x ∈ codeRange 0x109fd5 bytes_l109fd5, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9fd5 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109feb : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x109feb (fun s => s.RIP = 0x109feb) (fun _ => nopEffect 0x109feb 5) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l109ff0, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 54⟩))

def bytes_l109feb : List UInt8 :=
  [0x0F, 0x1F, 0x44, 0x00, 0x00]

theorem code_l109feb : ∀ x ∈ codeRange 0x109feb bytes_l109feb, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9feb 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109ff0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x109ff0 (pushR64Effect 0x109ff0 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x109ff0 (PushPre 0x109ff0 1) (pushR64Effect 0x109ff0 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x109ff1 (pushR64Effect 0x109ff1 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x109ff1 (PushPre 0x109ff1 2) (pushR64Effect 0x109ff1 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x109ff3 (pushR64Effect 0x109ff3 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x109ff3 (PushPre 0x109ff3 2) (pushR64Effect 0x109ff3 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x109ff5 (pushR64Effect 0x109ff5 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x109ff5 (PushPre 0x109ff5 2) (pushR64Effect 0x109ff5 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x109ff7 (pushR64Effect 0x109ff7 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x109ff7 (PushPre 0x109ff7 2) (pushR64Effect 0x109ff7 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x109ff9 (pushR64Effect 0x109ff9 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x109ff9 (PushPre 0x109ff9 1) (pushR64Effect 0x109ff9 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x109ffa (subR64Imm8Effect 0x109ffa 4 0x18) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x109ffa (fun s => s.RIP = 0x109ffa) (subR64Imm8Effect 0x109ffa 4 0x18) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x109ffe (cmpR64Imm8Effect 0x109ffe 6 0x7) (EffectPart.reads (.flag .CF) [.gpr 6] []) (.flag .CF)) #v[6]
    (.letOp (n := 68) (.out 0x109ffe (cmpR64Imm8Effect 0x109ffe 6 0x7) (EffectPart.reads (.flag .ZF) [.gpr 6] []) (.flag .ZF)) #v[6]
    (.letOp (n := 69) (.exec 0x109ffe (fun s => s.RIP = 0x109ffe) (cmpR64Imm8Effect 0x109ffe 6 0x7) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 70) (.pure (condOp 6)) #v[67, 68]
    (.terminate (.condBr (Fin.last 70) ⟨.l10a1f1, RegMap.args [(2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (16, 67), (19, 68), (22, 22), (39, 39), (50, 50), (51, 51)] 71⟩ ⟨.l10a008, RegMap.args [(2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (16, 67), (19, 68), (22, 22), (39, 39), (50, 50), (51, 51)] 71⟩)))))))))))))))))))

def bytes_l109ff0 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x83, 0xEC, 0x18, 0x48, 0x83,
    0xFE, 0x07, 0x0F, 0x86, 0xE9, 0x01, 0x00, 0x00]

theorem code_l109ff0 : ∀ x ∈ codeRange 0x109ff0 bytes_l109ff0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9ff0 24 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10a008_6 : Block Op Label signature Reg.count 291 :=
  .letOp (n := 291) (.out 0x10a1b5 (xorR32R32Effect 0x10a1b5 3 1 11) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 11] []) (.reg (.gpr 1))) #v[289, 273]
    (.letOp (n := 292) (.exec 0x10a1b5 (fun s => s.RIP = 0x10a1b5) (xorR32R32Effect 0x10a1b5 3 1 11) (Reg.operands [.gpr 1, .gpr 11] [])) #v[289, 273]
    (.letOp (n := 293) (.out 0x10a1b8 (xorR32R32Effect 0x10a1b8 3 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 15] []) (.reg (.gpr 0))) #v[285, 281]
    (.letOp (n := 294) (.exec 0x10a1b8 (fun s => s.RIP = 0x10a1b8) (xorR32R32Effect 0x10a1b8 3 0 15) (Reg.operands [.gpr 0, .gpr 15] [])) #v[285, 281]
    (.letOp (n := 295) (.out 0x10a1bb (movR64M64Effect 0x10a1bb 6 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 296) (.exec 0x10a1bb (LoadPre 0x10a1bb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10a1bb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10a1bb 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 297) (.exec 0x10a1c0 (StorePre 0x10a1c0 3 (fun s => AddrMode.addr (.base 6 .none) s (0x10a1c0 + BitVec.ofNat 64 3)) 2) (movM16R16Effect 0x10a1c0 3 1 (.base 6 .none)) (Reg.operands [.gpr 1, .gpr 6] [])) #v[291, 295]
    (.letOp (n := 298) (.exec 0x10a1c3 (StorePre 0x10a1c3 5 (fun s => AddrMode.addr (.base 6 (.d8 0x2)) s (0x10a1c3 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x10a1c3 5 10 (.base 6 (.d8 0x2))) (Reg.operands [.gpr 10, .gpr 6] [])) #v[267, 295]
    (.letOp (n := 299) (.exec 0x10a1c8 (StorePre 0x10a1c8 4 (fun s => AddrMode.addr (.base 6 (.d8 0x4)) s (0x10a1c8 + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x10a1c8 4 7 (.base 6 (.d8 0x4))) (Reg.operands [.gpr 7, .gpr 6] [])) #v[243, 295]
    (.letOp (n := 300) (.exec 0x10a1cc (StorePre 0x10a1cc 4 (fun s => AddrMode.addr (.base 6 (.d8 0x6)) s (0x10a1cc + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x10a1cc 4 2 (.base 6 (.d8 0x6))) (Reg.operands [.gpr 2, .gpr 6] [])) #v[189, 295]
    (.letOp (n := 301) (.exec 0x10a1d0 (StorePre 0x10a1d0 4 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x10a1d0 + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x10a1d0 4 0 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 6] [])) #v[293, 295]
    (.letOp (n := 302) (.exec 0x10a1d4 (StorePre 0x10a1d4 5 (fun s => AddrMode.addr (.base 6 (.d8 0xa)) s (0x10a1d4 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x10a1d4 5 8 (.base 6 (.d8 0xa))) (Reg.operands [.gpr 8, .gpr 6] [])) #v[269, 295]
    (.letOp (n := 303) (.exec 0x10a1d9 (StorePre 0x10a1d9 4 (fun s => AddrMode.addr (.base 6 (.d8 0xc)) s (0x10a1d9 + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x10a1d9 4 5 (.base 6 (.d8 0xc))) (Reg.operands [.gpr 5, .gpr 6] [])) #v[245, 295]
    (.letOp (n := 304) (.exec 0x10a1dd (StorePre 0x10a1dd 5 (fun s => AddrMode.addr (.base 6 (.d8 0xe)) s (0x10a1dd + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x10a1dd 5 12 (.base 6 (.d8 0xe))) (Reg.operands [.gpr 12, .gpr 6] [])) #v[193, 295]
    (.letOp (n := 305) (.out 0x10a1e2 (addR64Imm8Effect 0x10a1e2 4 0x18) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 306) (.exec 0x10a1e2 (fun s => s.RIP = 0x10a1e2) (addR64Imm8Effect 0x10a1e2 4 0x18) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 307) (.out 0x10a1e6 (popR64Effect 0x10a1e6 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[305]
    (.letOp (n := 308) (.out 0x10a1e6 (popR64Effect 0x10a1e6 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[305]
    (.letOp (n := 309) (.exec 0x10a1e6 (PopPre 0x10a1e6) (popR64Effect 0x10a1e6 1 3) (Reg.operands [.gpr 4] [])) #v[305]
    (.letOp (n := 310) (.out 0x10a1e7 (popR64Effect 0x10a1e7 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[308]
    (.letOp (n := 311) (.out 0x10a1e7 (popR64Effect 0x10a1e7 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[308]
    (.letOp (n := 312) (.exec 0x10a1e7 (PopPre 0x10a1e7) (popR64Effect 0x10a1e7 2 12) (Reg.operands [.gpr 4] [])) #v[308]
    (.letOp (n := 313) (.out 0x10a1e9 (popR64Effect 0x10a1e9 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[311]
    (.letOp (n := 314) (.out 0x10a1e9 (popR64Effect 0x10a1e9 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[311]
    (.letOp (n := 315) (.exec 0x10a1e9 (PopPre 0x10a1e9) (popR64Effect 0x10a1e9 2 13) (Reg.operands [.gpr 4] [])) #v[311]
    (.letOp (n := 316) (.out 0x10a1eb (popR64Effect 0x10a1eb 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[314]
    (.letOp (n := 317) (.out 0x10a1eb (popR64Effect 0x10a1eb 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[314]
    (.letOp (n := 318) (.exec 0x10a1eb (PopPre 0x10a1eb) (popR64Effect 0x10a1eb 2 14) (Reg.operands [.gpr 4] [])) #v[314]
    (.letOp (n := 319) (.out 0x10a1ed (popR64Effect 0x10a1ed 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[317]
    (.letOp (n := 320) (.out 0x10a1ed (popR64Effect 0x10a1ed 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[317]
    (.letOp (n := 321) (.exec 0x10a1ed (PopPre 0x10a1ed) (popR64Effect 0x10a1ed 2 15) (Reg.operands [.gpr 4] [])) #v[317]
    (.letOp (n := 322) (.out 0x10a1ef (popR64Effect 0x10a1ef 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[320]
    (.letOp (n := 323) (.out 0x10a1ef (popR64Effect 0x10a1ef 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[320]
    (.letOp (n := 324) (.exec 0x10a1ef (PopPre 0x10a1ef) (popR64Effect 0x10a1ef 1 5) (Reg.operands [.gpr 4] [])) #v[320]
    (.letOp (n := 325) (.out 0x10a1f0 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[323]
    (.letOp (n := 326) (.out 0x10a1f0 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[323]
    (.letOp (n := 327) (.exec 0x10a1f0 (RetPre 0x10a1f0) (retEffect) (Reg.operands [.gpr 4] [])) #v[323]
    (.terminate (.ret (RegMap.args [(0, 293), (1, 291), (2, 189), (3, 307), (4, 326), (5, 322), (6, 295), (7, 243), (8, 269), (9, 219), (10, 267), (11, 273), (12, 310), (13, 313), (14, 316), (15, 319), (22, 22), (39, 39), (50, 50), (51, 51)] 328) (some ⟨325, by decide⟩)))))))))))))))))))))))))))))))))))))))

def bytes_l10a008_6 : List UInt8 :=
  [0x44, 0x31, 0xD9, 0x44, 0x31, 0xF8, 0x48, 0x8B, 0x74, 0x24, 0x10, 0x66, 0x89, 0x0E, 0x66, 0x44,
    0x89, 0x56, 0x02, 0x66, 0x89, 0x7E, 0x04, 0x66, 0x89, 0x56, 0x06, 0x66, 0x89, 0x46, 0x08, 0x66,
    0x44, 0x89, 0x46, 0x0A, 0x66, 0x89, 0x6E, 0x0C, 0x66, 0x44, 0x89, 0x66, 0x0E, 0x48, 0x83, 0xC4,
    0x18, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l10a008_6 : ∀ x ∈ codeRange 0x10a1b5 bytes_l10a008_6, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xa1b5 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10a008_5 : Block Op Label signature Reg.count 251 :=
  .letOp (n := 251) (.out 0x10a16f (movR32R32Effect 0x10a16f 3 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 6] []) (.reg (.gpr 8))) #v[249]
    (.letOp (n := 252) (.exec 0x10a16f (fun s => s.RIP = 0x10a16f) (movR32R32Effect 0x10a16f 3 8 6) (Reg.operands [.gpr 6] [])) #v[249]
    (.letOp (n := 253) (.out 0x10a172 (shrR32Effect 0x10a172 4 8 4) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[251]
    (.letOp (n := 254) (.exec 0x10a172 (fun s => s.RIP = 0x10a172) (shrR32Effect 0x10a172 4 8 4) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[251]
    (.letOp (n := 255) (.out 0x10a176 (shlR32Effect 0x10a176 4 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[177]
    (.letOp (n := 256) (.exec 0x10a176 (fun s => s.RIP = 0x10a176) (shlR32Effect 0x10a176 4 14 2) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[177]
    (.letOp (n := 257) (.out 0x10a17a (xorR32R32Effect 0x10a17a 3 14 1) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 1] []) (.reg (.gpr 14))) #v[255, 143]
    (.letOp (n := 258) (.exec 0x10a17a (fun s => s.RIP = 0x10a17a) (xorR32R32Effect 0x10a17a 3 14 1) (Reg.operands [.gpr 14, .gpr 1] [])) #v[255, 143]
    (.letOp (n := 259) (.out 0x10a17d (xorR32R32Effect 0x10a17d 3 8 14) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 14] []) (.reg (.gpr 8))) #v[253, 257]
    (.letOp (n := 260) (.exec 0x10a17d (fun s => s.RIP = 0x10a17d) (xorR32R32Effect 0x10a17d 3 8 14) (Reg.operands [.gpr 8, .gpr 14] [])) #v[253, 257]
    (.letOp (n := 261) (.out 0x10a180 (andR32Imm32Effect 0x10a180 7 8 0xf0f) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[259]
    (.letOp (n := 262) (.exec 0x10a180 (fun s => s.RIP = 0x10a180) (andR32Imm32Effect 0x10a180 7 8 0xf0f) (Reg.operands [.gpr 8] [])) #v[259]
    (.letOp (n := 263) (.out 0x10a187 (movR32R32Effect 0x10a187 3 10 8) (EffectPart.reads (.reg (.gpr 10)) [.gpr 8] []) (.reg (.gpr 10))) #v[261]
    (.letOp (n := 264) (.exec 0x10a187 (fun s => s.RIP = 0x10a187) (movR32R32Effect 0x10a187 3 10 8) (Reg.operands [.gpr 8] [])) #v[261]
    (.letOp (n := 265) (.out 0x10a18a (shlR32Effect 0x10a18a 4 10 4) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[263]
    (.letOp (n := 266) (.exec 0x10a18a (fun s => s.RIP = 0x10a18a) (shlR32Effect 0x10a18a 4 10 4) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[263]
    (.letOp (n := 267) (.out 0x10a18e (xorR32R32Effect 0x10a18e 3 10 6) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 6] []) (.reg (.gpr 10))) #v[265, 249]
    (.letOp (n := 268) (.exec 0x10a18e (fun s => s.RIP = 0x10a18e) (xorR32R32Effect 0x10a18e 3 10 6) (Reg.operands [.gpr 10, .gpr 6] [])) #v[265, 249]
    (.letOp (n := 269) (.out 0x10a191 (xorR32R32Effect 0x10a191 3 8 14) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 14] []) (.reg (.gpr 8))) #v[261, 257]
    (.letOp (n := 270) (.exec 0x10a191 (fun s => s.RIP = 0x10a191) (xorR32R32Effect 0x10a191 3 8 14) (Reg.operands [.gpr 8, .gpr 14] [])) #v[261, 257]
    (.letOp (n := 271) (.out 0x10a194 (shlR32Effect 0x10a194 4 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[209]
    (.letOp (n := 272) (.exec 0x10a194 (fun s => s.RIP = 0x10a194) (shlR32Effect 0x10a194 4 11 2) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[209]
    (.letOp (n := 273) (.out 0x10a198 (xorR32R32Effect 0x10a198 3 11 3) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 3] []) (.reg (.gpr 11))) #v[271, 197]
    (.letOp (n := 274) (.exec 0x10a198 (fun s => s.RIP = 0x10a198) (xorR32R32Effect 0x10a198 3 11 3) (Reg.operands [.gpr 11, .gpr 3] [])) #v[271, 197]
    (.letOp (n := 275) (.out 0x10a19b (movR32R32Effect 0x10a19b 3 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[273]
    (.letOp (n := 276) (.exec 0x10a19b (fun s => s.RIP = 0x10a19b) (movR32R32Effect 0x10a19b 3 0 11) (Reg.operands [.gpr 11] [])) #v[273]
    (.letOp (n := 277) (.out 0x10a19e (shrR32Effect 0x10a19e 3 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[275]
    (.letOp (n := 278) (.exec 0x10a19e (fun s => s.RIP = 0x10a19e) (shrR32Effect 0x10a19e 3 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[275]
    (.letOp (n := 279) (.out 0x10a1a1 (shlR32Effect 0x10a1a1 4 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[231]
    (.letOp (n := 280) (.exec 0x10a1a1 (fun s => s.RIP = 0x10a1a1) (shlR32Effect 0x10a1a1 4 15 2) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[231]
    (.letOp (n := 281) (.out 0x10a1a5 (xorR32R32Effect 0x10a1a5 3 15 9) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 9] []) (.reg (.gpr 15))) #v[279, 219]
    (.letOp (n := 282) (.exec 0x10a1a5 (fun s => s.RIP = 0x10a1a5) (xorR32R32Effect 0x10a1a5 3 15 9) (Reg.operands [.gpr 15, .gpr 9] [])) #v[279, 219]
    (.letOp (n := 283) (.out 0x10a1a8 (xorR32R32Effect 0x10a1a8 3 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 15] []) (.reg (.gpr 0))) #v[277, 281]
    (.letOp (n := 284) (.exec 0x10a1a8 (fun s => s.RIP = 0x10a1a8) (xorR32R32Effect 0x10a1a8 3 0 15) (Reg.operands [.gpr 0, .gpr 15] [])) #v[277, 281]
    (.letOp (n := 285) (.out 0x10a1ab (andEaxImm32Effect 0x10a1ab 0xf0f) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[283]
    (.letOp (n := 286) (.exec 0x10a1ab (fun s => s.RIP = 0x10a1ab) (andEaxImm32Effect 0x10a1ab 0xf0f) (Reg.operands [.gpr 0] [])) #v[283]
    (.letOp (n := 287) (.out 0x10a1b0 (movR32R32Effect 0x10a1b0 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[285]
    (.letOp (n := 288) (.exec 0x10a1b0 (fun s => s.RIP = 0x10a1b0) (movR32R32Effect 0x10a1b0 2 1 0) (Reg.operands [.gpr 0] [])) #v[285]
    (.letOp (n := 289) (.out 0x10a1b2 (shlR32Effect 0x10a1b2 3 1 4) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[287]
    (.letOp (n := 290) (.exec 0x10a1b2 (fun s => s.RIP = 0x10a1b2) (shlR32Effect 0x10a1b2 3 1 4) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[287]
    (b_l10a008_6))))))))))))))))))))))))))))))))))))))))

def bytes_l10a008_5 : List UInt8 :=
  [0x41, 0x89, 0xF0, 0x41, 0xC1, 0xE8, 0x04, 0x41, 0xC1, 0xE6, 0x02, 0x41, 0x31, 0xCE, 0x45, 0x31,
    0xF0, 0x41, 0x81, 0xE0, 0x0F, 0x0F, 0x00, 0x00, 0x45, 0x89, 0xC2, 0x41, 0xC1, 0xE2, 0x04, 0x41,
    0x31, 0xF2, 0x45, 0x31, 0xF0, 0x41, 0xC1, 0xE3, 0x02, 0x41, 0x31, 0xDB, 0x44, 0x89, 0xD8, 0xC1,
    0xE8, 0x04, 0x41, 0xC1, 0xE7, 0x02, 0x45, 0x31, 0xCF, 0x44, 0x31, 0xF8, 0x25, 0x0F, 0x0F, 0x00,
    0x00, 0x89, 0xC1, 0xC1, 0xE1, 0x04] ++ bytes_l10a008_6

theorem code_l10a008_5 : ∀ x ∈ codeRange 0x10a16f bytes_l10a008_5, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa16f 70 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a008_6

@[cfg_block] def b_l10a008_4 : Block Op Label signature Reg.count 211 :=
  .letOp (n := 211) (.out 0x10a12b (xorR32R32Effect 0x10a12b 3 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 11] []) (.reg (.gpr 10))) #v[205, 209]
    (.letOp (n := 212) (.exec 0x10a12b (fun s => s.RIP = 0x10a12b) (xorR32R32Effect 0x10a12b 3 10 11) (Reg.operands [.gpr 10, .gpr 11] [])) #v[205, 209]
    (.letOp (n := 213) (.out 0x10a12e (movR32R32Effect 0x10a12e 3 5 10) (EffectPart.reads (.reg (.gpr 5)) [.gpr 10] []) (.reg (.gpr 5))) #v[211]
    (.letOp (n := 214) (.exec 0x10a12e (fun s => s.RIP = 0x10a12e) (movR32R32Effect 0x10a12e 3 5 10) (Reg.operands [.gpr 10] [])) #v[211]
    (.letOp (n := 215) (.out 0x10a131 (shrR32Effect 0x10a131 3 5 4) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[213]
    (.letOp (n := 216) (.exec 0x10a131 (fun s => s.RIP = 0x10a131) (shrR32Effect 0x10a131 3 5 4) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[213]
    (.letOp (n := 217) (.out 0x10a134 (addR32R32Effect 0x10a134 3 9 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 9] []) (.reg (.gpr 9))) #v[141, 141]
    (.letOp (n := 218) (.exec 0x10a134 (fun s => s.RIP = 0x10a134) (addR32R32Effect 0x10a134 3 9 9) (Reg.operands [.gpr 9, .gpr 9] [])) #v[141, 141]
    (.letOp (n := 219) (.out 0x10a137 (xorR32R32Effect 0x10a137 3 9 15) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 15] []) (.reg (.gpr 9))) #v[217, 125]
    (.letOp (n := 220) (.exec 0x10a137 (fun s => s.RIP = 0x10a137) (xorR32R32Effect 0x10a137 3 9 15) (Reg.operands [.gpr 9, .gpr 15] [])) #v[217, 125]
    (.letOp (n := 221) (.out 0x10a13a (movR32R32Effect 0x10a13a 3 15 9) (EffectPart.reads (.reg (.gpr 15)) [.gpr 9] []) (.reg (.gpr 15))) #v[219]
    (.letOp (n := 222) (.exec 0x10a13a (fun s => s.RIP = 0x10a13a) (movR32R32Effect 0x10a13a 3 15 9) (Reg.operands [.gpr 9] [])) #v[219]
    (.letOp (n := 223) (.out 0x10a13d (shrR32Effect 0x10a13d 4 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[221]
    (.letOp (n := 224) (.exec 0x10a13d (fun s => s.RIP = 0x10a13d) (shrR32Effect 0x10a13d 4 15 2) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[221]
    (.letOp (n := 225) (.out 0x10a141 (addR32R32Effect 0x10a141 3 13 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 13] []) (.reg (.gpr 13))) #v[171, 171]
    (.letOp (n := 226) (.exec 0x10a141 (fun s => s.RIP = 0x10a141) (addR32R32Effect 0x10a141 3 13 13) (Reg.operands [.gpr 13, .gpr 13] [])) #v[171, 171]
    (.letOp (n := 227) (.out 0x10a144 (xorR32R32Effect 0x10a144 3 13 7) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 7] []) (.reg (.gpr 13))) #v[225, 151]
    (.letOp (n := 228) (.exec 0x10a144 (fun s => s.RIP = 0x10a144) (xorR32R32Effect 0x10a144 3 13 7) (Reg.operands [.gpr 13, .gpr 7] [])) #v[225, 151]
    (.letOp (n := 229) (.out 0x10a147 (xorR32R32Effect 0x10a147 3 15 13) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 13] []) (.reg (.gpr 15))) #v[223, 227]
    (.letOp (n := 230) (.exec 0x10a147 (fun s => s.RIP = 0x10a147) (xorR32R32Effect 0x10a147 3 15 13) (Reg.operands [.gpr 15, .gpr 13] [])) #v[223, 227]
    (.letOp (n := 231) (.out 0x10a14a (andR32Imm32Effect 0x10a14a 7 15 0x3333) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15] []) (.reg (.gpr 15))) #v[229]
    (.letOp (n := 232) (.exec 0x10a14a (fun s => s.RIP = 0x10a14a) (andR32Imm32Effect 0x10a14a 7 15 0x3333) (Reg.operands [.gpr 15] [])) #v[229]
    (.letOp (n := 233) (.out 0x10a151 (xorR32R32Effect 0x10a151 3 13 15) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 15] []) (.reg (.gpr 13))) #v[227, 231]
    (.letOp (n := 234) (.exec 0x10a151 (fun s => s.RIP = 0x10a151) (xorR32R32Effect 0x10a151 3 13 15) (Reg.operands [.gpr 13, .gpr 15] [])) #v[227, 231]
    (.letOp (n := 235) (.out 0x10a154 (xorR32R32Effect 0x10a154 3 5 13) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 13] []) (.reg (.gpr 5))) #v[215, 233]
    (.letOp (n := 236) (.exec 0x10a154 (fun s => s.RIP = 0x10a154) (xorR32R32Effect 0x10a154 3 5 13) (Reg.operands [.gpr 5, .gpr 13] [])) #v[215, 233]
    (.letOp (n := 237) (.out 0x10a157 (andR32Imm32Effect 0x10a157 6 5 0xf0f) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5] []) (.reg (.gpr 5))) #v[235]
    (.letOp (n := 238) (.exec 0x10a157 (fun s => s.RIP = 0x10a157) (andR32Imm32Effect 0x10a157 6 5 0xf0f) (Reg.operands [.gpr 5] [])) #v[235]
    (.letOp (n := 239) (.out 0x10a15d (movR32R32Effect 0x10a15d 2 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[237]
    (.letOp (n := 240) (.exec 0x10a15d (fun s => s.RIP = 0x10a15d) (movR32R32Effect 0x10a15d 2 7 5) (Reg.operands [.gpr 5] [])) #v[237]
    (.letOp (n := 241) (.out 0x10a15f (shlR32Effect 0x10a15f 3 7 4) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[239]
    (.letOp (n := 242) (.exec 0x10a15f (fun s => s.RIP = 0x10a15f) (shlR32Effect 0x10a15f 3 7 4) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[239]
    (.letOp (n := 243) (.out 0x10a162 (xorR32R32Effect 0x10a162 3 7 10) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 10] []) (.reg (.gpr 7))) #v[241, 211]
    (.letOp (n := 244) (.exec 0x10a162 (fun s => s.RIP = 0x10a162) (xorR32R32Effect 0x10a162 3 7 10) (Reg.operands [.gpr 7, .gpr 10] [])) #v[241, 211]
    (.letOp (n := 245) (.out 0x10a165 (xorR32R32Effect 0x10a165 3 5 13) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 13] []) (.reg (.gpr 5))) #v[237, 233]
    (.letOp (n := 246) (.exec 0x10a165 (fun s => s.RIP = 0x10a165) (xorR32R32Effect 0x10a165 3 5 13) (Reg.operands [.gpr 5, .gpr 13] [])) #v[237, 233]
    (.letOp (n := 247) (.out 0x10a168 (shlR32Effect 0x10a168 3 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[110]
    (.letOp (n := 248) (.exec 0x10a168 (fun s => s.RIP = 0x10a168) (shlR32Effect 0x10a168 3 6 2) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[110]
    (.letOp (n := 249) (.out 0x10a16b (xorR32M32LowEffect 0x10a16b 6 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 4] []) (.reg (.gpr 6))) #v[247, 4]
    (.letOp (n := 250) (.exec 0x10a16b (LoadPre 0x10a16b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x10a16b + BitVec.ofNat 64 4)) 4) (xorR32M32LowEffect 0x10a16b 6 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[247, 4]
    (b_l10a008_5))))))))))))))))))))))))))))))))))))))))

def bytes_l10a008_4 : List UInt8 :=
  [0x45, 0x31, 0xDA, 0x44, 0x89, 0xD5, 0xC1, 0xED, 0x04, 0x45, 0x01, 0xC9, 0x45, 0x31, 0xF9, 0x45,
    0x89, 0xCF, 0x41, 0xC1, 0xEF, 0x02, 0x45, 0x01, 0xED, 0x41, 0x31, 0xFD, 0x45, 0x31, 0xEF, 0x41,
    0x81, 0xE7, 0x33, 0x33, 0x00, 0x00, 0x45, 0x31, 0xFD, 0x44, 0x31, 0xED, 0x81, 0xE5, 0x0F, 0x0F,
    0x00, 0x00, 0x89, 0xEF, 0xC1, 0xE7, 0x04, 0x44, 0x31, 0xD7, 0x44, 0x31, 0xED, 0xC1, 0xE6, 0x02,
    0x33, 0x74, 0x24, 0x0C] ++ bytes_l10a008_5

theorem code_l10a008_4 : ∀ x ∈ codeRange 0x10a12b bytes_l10a008_4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa12b 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a008_5

@[cfg_block] def b_l10a008_3 : Block Op Label signature Reg.count 171 :=
  .letOp (n := 171) (.out 0x10a0df (andR32Imm32Effect 0x10a0df 7 13 0x5555) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[169]
    (.letOp (n := 172) (.exec 0x10a0df (fun s => s.RIP = 0x10a0df) (andR32Imm32Effect 0x10a0df 7 13 0x5555) (Reg.operands [.gpr 13] [])) #v[169]
    (.letOp (n := 173) (.out 0x10a0e6 (xorR32R32Effect 0x10a0e6 3 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 13] []) (.reg (.gpr 0))) #v[159, 171]
    (.letOp (n := 174) (.exec 0x10a0e6 (fun s => s.RIP = 0x10a0e6) (xorR32R32Effect 0x10a0e6 3 0 13) (Reg.operands [.gpr 0, .gpr 13] [])) #v[159, 171]
    (.letOp (n := 175) (.out 0x10a0e9 (xorR32R32Effect 0x10a0e9 3 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 0] []) (.reg (.gpr 14))) #v[163, 173]
    (.letOp (n := 176) (.exec 0x10a0e9 (fun s => s.RIP = 0x10a0e9) (xorR32R32Effect 0x10a0e9 3 14 0) (Reg.operands [.gpr 14, .gpr 0] [])) #v[163, 173]
    (.letOp (n := 177) (.out 0x10a0ec (andR32Imm32Effect 0x10a0ec 7 14 0x3333) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14] []) (.reg (.gpr 14))) #v[175]
    (.letOp (n := 178) (.exec 0x10a0ec (fun s => s.RIP = 0x10a0ec) (andR32Imm32Effect 0x10a0ec 7 14 0x3333) (Reg.operands [.gpr 14] [])) #v[175]
    (.letOp (n := 179) (.out 0x10a0f3 (xorR32R32Effect 0x10a0f3 3 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[173, 177]
    (.letOp (n := 180) (.exec 0x10a0f3 (fun s => s.RIP = 0x10a0f3) (xorR32R32Effect 0x10a0f3 3 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[173, 177]
    (.letOp (n := 181) (.out 0x10a0f6 (xorR32R32Effect 0x10a0f6 3 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[116, 179]
    (.letOp (n := 182) (.exec 0x10a0f6 (fun s => s.RIP = 0x10a0f6) (xorR32R32Effect 0x10a0f6 3 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[116, 179]
    (.letOp (n := 183) (.out 0x10a0f9 (andR32Imm32Effect 0x10a0f9 7 8 0xf0f) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[181]
    (.letOp (n := 184) (.exec 0x10a0f9 (fun s => s.RIP = 0x10a0f9) (andR32Imm32Effect 0x10a0f9 7 8 0xf0f) (Reg.operands [.gpr 8] [])) #v[181]
    (.letOp (n := 185) (.out 0x10a100 (movR32R32Effect 0x10a100 3 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8] []) (.reg (.gpr 2))) #v[183]
    (.letOp (n := 186) (.exec 0x10a100 (fun s => s.RIP = 0x10a100) (movR32R32Effect 0x10a100 3 2 8) (Reg.operands [.gpr 8] [])) #v[183]
    (.letOp (n := 187) (.out 0x10a103 (shlR32Effect 0x10a103 3 2 4) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[185]
    (.letOp (n := 188) (.exec 0x10a103 (fun s => s.RIP = 0x10a103) (shlR32Effect 0x10a103 3 2 4) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[185]
    (.letOp (n := 189) (.out 0x10a106 (xorR32R32Effect 0x10a106 3 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 12] []) (.reg (.gpr 2))) #v[187, 112]
    (.letOp (n := 190) (.exec 0x10a106 (fun s => s.RIP = 0x10a106) (xorR32R32Effect 0x10a106 3 2 12) (Reg.operands [.gpr 2, .gpr 12] [])) #v[187, 112]
    (.letOp (n := 191) (.out 0x10a109 (xorR32R32Effect 0x10a109 3 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[183, 179]
    (.letOp (n := 192) (.exec 0x10a109 (fun s => s.RIP = 0x10a109) (xorR32R32Effect 0x10a109 3 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[183, 179]
    (.letOp (n := 193) (.out 0x10a10c (movR32R32Effect 0x10a10c 3 12 8) (EffectPart.reads (.reg (.gpr 12)) [.gpr 8] []) (.reg (.gpr 12))) #v[191]
    (.letOp (n := 194) (.exec 0x10a10c (fun s => s.RIP = 0x10a10c) (movR32R32Effect 0x10a10c 3 12 8) (Reg.operands [.gpr 8] [])) #v[191]
    (.letOp (n := 195) (.out 0x10a10f (addR32R32Effect 0x10a10f 2 3 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 3] []) (.reg (.gpr 3))) #v[75, 75]
    (.letOp (n := 196) (.exec 0x10a10f (fun s => s.RIP = 0x10a10f) (addR32R32Effect 0x10a10f 2 3 3) (Reg.operands [.gpr 3, .gpr 3] [])) #v[75, 75]
    (.letOp (n := 197) (.out 0x10a111 (xorR32R32Effect 0x10a111 3 3 11) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 11] []) (.reg (.gpr 3))) #v[195, 59]
    (.letOp (n := 198) (.exec 0x10a111 (fun s => s.RIP = 0x10a111) (xorR32R32Effect 0x10a111 3 3 11) (Reg.operands [.gpr 3, .gpr 11] [])) #v[195, 59]
    (.letOp (n := 199) (.out 0x10a114 (movR32R32Effect 0x10a114 3 11 3) (EffectPart.reads (.reg (.gpr 11)) [.gpr 3] []) (.reg (.gpr 11))) #v[197]
    (.letOp (n := 200) (.exec 0x10a114 (fun s => s.RIP = 0x10a114) (movR32R32Effect 0x10a114 3 11 3) (Reg.operands [.gpr 3] [])) #v[197]
    (.letOp (n := 201) (.out 0x10a117 (shrR32Effect 0x10a117 4 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[199]
    (.letOp (n := 202) (.exec 0x10a117 (fun s => s.RIP = 0x10a117) (shrR32Effect 0x10a117 4 11 2) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[199]
    (.letOp (n := 203) (.out 0x10a11b (addR32R32Effect 0x10a11b 3 10 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 10] []) (.reg (.gpr 10))) #v[104, 104]
    (.letOp (n := 204) (.exec 0x10a11b (fun s => s.RIP = 0x10a11b) (addR32R32Effect 0x10a11b 3 10 10) (Reg.operands [.gpr 10, .gpr 10] [])) #v[104, 104]
    (.letOp (n := 205) (.out 0x10a11e (xorR32R32Effect 0x10a11e 3 10 5) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 5] []) (.reg (.gpr 10))) #v[203, 88]
    (.letOp (n := 206) (.exec 0x10a11e (fun s => s.RIP = 0x10a11e) (xorR32R32Effect 0x10a11e 3 10 5) (Reg.operands [.gpr 10, .gpr 5] [])) #v[203, 88]
    (.letOp (n := 207) (.out 0x10a121 (xorR32R32Effect 0x10a121 3 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 10] []) (.reg (.gpr 11))) #v[201, 205]
    (.letOp (n := 208) (.exec 0x10a121 (fun s => s.RIP = 0x10a121) (xorR32R32Effect 0x10a121 3 11 10) (Reg.operands [.gpr 11, .gpr 10] [])) #v[201, 205]
    (.letOp (n := 209) (.out 0x10a124 (andR32Imm32Effect 0x10a124 7 11 0x3333) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11] []) (.reg (.gpr 11))) #v[207]
    (.letOp (n := 210) (.exec 0x10a124 (fun s => s.RIP = 0x10a124) (andR32Imm32Effect 0x10a124 7 11 0x3333) (Reg.operands [.gpr 11] [])) #v[207]
    (b_l10a008_4))))))))))))))))))))))))))))))))))))))))

def bytes_l10a008_3 : List UInt8 :=
  [0x41, 0x81, 0xE5, 0x55, 0x55, 0x00, 0x00, 0x44, 0x31, 0xE8, 0x41, 0x31, 0xC6, 0x41, 0x81, 0xE6,
    0x33, 0x33, 0x00, 0x00, 0x44, 0x31, 0xF0, 0x41, 0x31, 0xC0, 0x41, 0x81, 0xE0, 0x0F, 0x0F, 0x00,
    0x00, 0x44, 0x89, 0xC2, 0xC1, 0xE2, 0x04, 0x44, 0x31, 0xE2, 0x41, 0x31, 0xC0, 0x45, 0x89, 0xC4,
    0x01, 0xDB, 0x44, 0x31, 0xDB, 0x41, 0x89, 0xDB, 0x41, 0xC1, 0xEB, 0x02, 0x45, 0x01, 0xD2, 0x41,
    0x31, 0xEA, 0x45, 0x31, 0xD3, 0x41, 0x81, 0xE3, 0x33, 0x33, 0x00, 0x00] ++ bytes_l10a008_4

theorem code_l10a008_3 : ∀ x ∈ codeRange 0x10a0df bytes_l10a008_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa0df 76 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a008_4

@[cfg_block] def b_l10a008_2 : Block Op Label signature Reg.count 131 :=
  .letOp (n := 131) (.out 0x10a095 (movzxR32M8Effect 0x10a095 4 7 (.base 2 (.d8 0x7))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[2]
    (.letOp (n := 132) (.exec 0x10a095 (LoadPre 0x10a095 (fun s => AddrMode.addr (.base 2 (.d8 0x7)) s (0x10a095 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a095 4 7 (.base 2 (.d8 0x7))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 133) (.out 0x10a099 (shlR32Effect 0x10a099 3 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[131]
    (.letOp (n := 134) (.exec 0x10a099 (fun s => s.RIP = 0x10a099) (shlR32Effect 0x10a099 3 7 8) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[131]
    (.letOp (n := 135) (.out 0x10a09c (movzxR32M8Effect 0x10a09c 4 1 (.base 2 (.d8 0x5))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2]
    (.letOp (n := 136) (.exec 0x10a09c (LoadPre 0x10a09c (fun s => AddrMode.addr (.base 2 (.d8 0x5)) s (0x10a09c + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a09c 4 1 (.base 2 (.d8 0x5))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 137) (.out 0x10a0a0 (orR32R32Effect 0x10a0a0 2 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[135, 133]
    (.letOp (n := 138) (.exec 0x10a0a0 (fun s => s.RIP = 0x10a0a0) (orR32R32Effect 0x10a0a0 2 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[135, 133]
    (.letOp (n := 139) (.out 0x10a0a2 (xorR32R32Effect 0x10a0a2 3 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1] []) (.reg (.gpr 9))) #v[129, 137]
    (.letOp (n := 140) (.exec 0x10a0a2 (fun s => s.RIP = 0x10a0a2) (xorR32R32Effect 0x10a0a2 3 9 1) (Reg.operands [.gpr 9, .gpr 1] [])) #v[129, 137]
    (.letOp (n := 141) (.out 0x10a0a5 (andR32Imm32Effect 0x10a0a5 7 9 0x5555) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[139]
    (.letOp (n := 142) (.exec 0x10a0a5 (fun s => s.RIP = 0x10a0a5) (andR32Imm32Effect 0x10a0a5 7 9 0x5555) (Reg.operands [.gpr 9] [])) #v[139]
    (.letOp (n := 143) (.out 0x10a0ac (xorR32R32Effect 0x10a0ac 3 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 9] []) (.reg (.gpr 1))) #v[137, 141]
    (.letOp (n := 144) (.exec 0x10a0ac (fun s => s.RIP = 0x10a0ac) (xorR32R32Effect 0x10a0ac 3 1 9) (Reg.operands [.gpr 1, .gpr 9] [])) #v[137, 141]
    (.letOp (n := 145) (.out 0x10a0af (movzxR32M8Effect 0x10a0af 5 14 (.base 2 (.d8 0xb))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[2]
    (.letOp (n := 146) (.exec 0x10a0af (LoadPre 0x10a0af (fun s => AddrMode.addr (.base 2 (.d8 0xb)) s (0x10a0af + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10a0af 5 14 (.base 2 (.d8 0xb))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 147) (.out 0x10a0b4 (shlR32Effect 0x10a0b4 4 14 8) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[145]
    (.letOp (n := 148) (.exec 0x10a0b4 (fun s => s.RIP = 0x10a0b4) (shlR32Effect 0x10a0b4 4 14 8) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[145]
    (.letOp (n := 149) (.out 0x10a0b8 (movzxR32M8Effect 0x10a0b8 4 7 (.base 2 (.d8 0x9))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[2]
    (.letOp (n := 150) (.exec 0x10a0b8 (LoadPre 0x10a0b8 (fun s => AddrMode.addr (.base 2 (.d8 0x9)) s (0x10a0b8 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a0b8 4 7 (.base 2 (.d8 0x9))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 151) (.out 0x10a0bc (orR32R32Effect 0x10a0bc 3 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 14] []) (.reg (.gpr 7))) #v[149, 147]
    (.letOp (n := 152) (.exec 0x10a0bc (fun s => s.RIP = 0x10a0bc) (orR32R32Effect 0x10a0bc 3 7 14) (Reg.operands [.gpr 7, .gpr 14] [])) #v[149, 147]
    (.letOp (n := 153) (.out 0x10a0bf (movzxR32M8Effect 0x10a0bf 5 14 (.base 2 (.d8 0xf))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[2]
    (.letOp (n := 154) (.exec 0x10a0bf (LoadPre 0x10a0bf (fun s => AddrMode.addr (.base 2 (.d8 0xf)) s (0x10a0bf + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10a0bf 5 14 (.base 2 (.d8 0xf))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 155) (.out 0x10a0c4 (shlR32Effect 0x10a0c4 4 14 8) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[153]
    (.letOp (n := 156) (.exec 0x10a0c4 (fun s => s.RIP = 0x10a0c4) (shlR32Effect 0x10a0c4 4 14 8) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[153]
    (.letOp (n := 157) (.out 0x10a0c8 (movzxR32M8Effect 0x10a0c8 4 0 (.base 2 (.d8 0xd))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 158) (.exec 0x10a0c8 (LoadPre 0x10a0c8 (fun s => AddrMode.addr (.base 2 (.d8 0xd)) s (0x10a0c8 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a0c8 4 0 (.base 2 (.d8 0xd))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 159) (.out 0x10a0cc (orR32R32Effect 0x10a0cc 3 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[157, 155]
    (.letOp (n := 160) (.exec 0x10a0cc (fun s => s.RIP = 0x10a0cc) (orR32R32Effect 0x10a0cc 3 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[157, 155]
    (.letOp (n := 161) (.out 0x10a0cf (movR32R32Effect 0x10a0cf 3 14 1) (EffectPart.reads (.reg (.gpr 14)) [.gpr 1] []) (.reg (.gpr 14))) #v[143]
    (.letOp (n := 162) (.exec 0x10a0cf (fun s => s.RIP = 0x10a0cf) (movR32R32Effect 0x10a0cf 3 14 1) (Reg.operands [.gpr 1] [])) #v[143]
    (.letOp (n := 163) (.out 0x10a0d2 (shrR32Effect 0x10a0d2 4 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[161]
    (.letOp (n := 164) (.exec 0x10a0d2 (fun s => s.RIP = 0x10a0d2) (shrR32Effect 0x10a0d2 4 14 2) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[161]
    (.letOp (n := 165) (.out 0x10a0d6 (movR32R32Effect 0x10a0d6 3 13 7) (EffectPart.reads (.reg (.gpr 13)) [.gpr 7] []) (.reg (.gpr 13))) #v[151]
    (.letOp (n := 166) (.exec 0x10a0d6 (fun s => s.RIP = 0x10a0d6) (movR32R32Effect 0x10a0d6 3 13 7) (Reg.operands [.gpr 7] [])) #v[151]
    (.letOp (n := 167) (.out 0x10a0d9 (shrR32Effect 0x10a0d9 3 13 1) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[165]
    (.letOp (n := 168) (.exec 0x10a0d9 (fun s => s.RIP = 0x10a0d9) (shrR32Effect 0x10a0d9 3 13 1) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[165]
    (.letOp (n := 169) (.out 0x10a0dc (xorR32R32Effect 0x10a0dc 3 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 0] []) (.reg (.gpr 13))) #v[167, 159]
    (.letOp (n := 170) (.exec 0x10a0dc (fun s => s.RIP = 0x10a0dc) (xorR32R32Effect 0x10a0dc 3 13 0) (Reg.operands [.gpr 13, .gpr 0] [])) #v[167, 159]
    (b_l10a008_3))))))))))))))))))))))))))))))))))))))))

def bytes_l10a008_2 : List UInt8 :=
  [0x0F, 0xB6, 0x7A, 0x07, 0xC1, 0xE7, 0x08, 0x0F, 0xB6, 0x4A, 0x05, 0x09, 0xF9, 0x41, 0x31, 0xC9,
    0x41, 0x81, 0xE1, 0x55, 0x55, 0x00, 0x00, 0x44, 0x31, 0xC9, 0x44, 0x0F, 0xB6, 0x72, 0x0B, 0x41,
    0xC1, 0xE6, 0x08, 0x0F, 0xB6, 0x7A, 0x09, 0x44, 0x09, 0xF7, 0x44, 0x0F, 0xB6, 0x72, 0x0F, 0x41,
    0xC1, 0xE6, 0x08, 0x0F, 0xB6, 0x42, 0x0D, 0x44, 0x09, 0xF0, 0x41, 0x89, 0xCE, 0x41, 0xC1, 0xEE,
    0x02, 0x41, 0x89, 0xFD, 0x41, 0xD1, 0xED, 0x41, 0x31, 0xC5] ++ bytes_l10a008_3

theorem code_l10a008_2 : ∀ x ∈ codeRange 0x10a095 bytes_l10a008_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa095 74 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a008_3

@[cfg_block] def b_l10a008_1 : Block Op Label signature Reg.count 92 :=
  .letOp (n := 92) (.out 0x10a049 (shrR32Effect 0x10a049 3 10 1) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[90]
    (.letOp (n := 93) (.exec 0x10a049 (fun s => s.RIP = 0x10a049) (shrR32Effect 0x10a049 3 10 1) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[90]
    (.letOp (n := 94) (.out 0x10a04c (movzxR32M8Effect 0x10a04c 4 1 (.base 2 (.d8 0xe))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2]
    (.letOp (n := 95) (.exec 0x10a04c (LoadPre 0x10a04c (fun s => AddrMode.addr (.base 2 (.d8 0xe)) s (0x10a04c + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a04c 4 1 (.base 2 (.d8 0xe))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 96) (.out 0x10a050 (shlR32Effect 0x10a050 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[94]
    (.letOp (n := 97) (.exec 0x10a050 (fun s => s.RIP = 0x10a050) (shlR32Effect 0x10a050 3 1 8) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[94]
    (.letOp (n := 98) (.out 0x10a053 (movzxR32M8Effect 0x10a053 5 12 (.base 2 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 2] []) (.reg (.gpr 12))) #v[2]
    (.letOp (n := 99) (.exec 0x10a053 (LoadPre 0x10a053 (fun s => AddrMode.addr (.base 2 (.d8 0xc)) s (0x10a053 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10a053 5 12 (.base 2 (.d8 0xc))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 100) (.out 0x10a058 (orR32R32Effect 0x10a058 3 12 1) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 1] []) (.reg (.gpr 12))) #v[98, 96]
    (.letOp (n := 101) (.exec 0x10a058 (fun s => s.RIP = 0x10a058) (orR32R32Effect 0x10a058 3 12 1) (Reg.operands [.gpr 12, .gpr 1] [])) #v[98, 96]
    (.letOp (n := 102) (.out 0x10a05b (xorR32R32Effect 0x10a05b 3 10 12) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 12] []) (.reg (.gpr 10))) #v[92, 100]
    (.letOp (n := 103) (.exec 0x10a05b (fun s => s.RIP = 0x10a05b) (xorR32R32Effect 0x10a05b 3 10 12) (Reg.operands [.gpr 10, .gpr 12] [])) #v[92, 100]
    (.letOp (n := 104) (.out 0x10a05e (andR32Imm32Effect 0x10a05e 7 10 0x5555) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[102]
    (.letOp (n := 105) (.exec 0x10a05e (fun s => s.RIP = 0x10a05e) (andR32Imm32Effect 0x10a05e 7 10 0x5555) (Reg.operands [.gpr 10] [])) #v[102]
    (.letOp (n := 106) (.out 0x10a065 (xorR32R32Effect 0x10a065 3 12 10) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 10] []) (.reg (.gpr 12))) #v[100, 104]
    (.letOp (n := 107) (.exec 0x10a065 (fun s => s.RIP = 0x10a065) (xorR32R32Effect 0x10a065 3 12 10) (Reg.operands [.gpr 12, .gpr 10] [])) #v[100, 104]
    (.letOp (n := 108) (.out 0x10a068 (xorR32R32Effect 0x10a068 3 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 12] []) (.reg (.gpr 6))) #v[80, 106]
    (.letOp (n := 109) (.exec 0x10a068 (fun s => s.RIP = 0x10a068) (xorR32R32Effect 0x10a068 3 6 12) (Reg.operands [.gpr 6, .gpr 12] [])) #v[80, 106]
    (.letOp (n := 110) (.out 0x10a06b (andR32Imm32Effect 0x10a06b 6 6 0x3333) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[108]
    (.letOp (n := 111) (.exec 0x10a06b (fun s => s.RIP = 0x10a06b) (andR32Imm32Effect 0x10a06b 6 6 0x3333) (Reg.operands [.gpr 6] [])) #v[108]
    (.letOp (n := 112) (.out 0x10a071 (xorR32R32Effect 0x10a071 3 12 6) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 6] []) (.reg (.gpr 12))) #v[106, 110]
    (.letOp (n := 113) (.exec 0x10a071 (fun s => s.RIP = 0x10a071) (xorR32R32Effect 0x10a071 3 12 6) (Reg.operands [.gpr 12, .gpr 6] [])) #v[106, 110]
    (.letOp (n := 114) (.out 0x10a074 (movR32R32Effect 0x10a074 3 8 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 12] []) (.reg (.gpr 8))) #v[112]
    (.letOp (n := 115) (.exec 0x10a074 (fun s => s.RIP = 0x10a074) (movR32R32Effect 0x10a074 3 8 12) (Reg.operands [.gpr 12] [])) #v[112]
    (.letOp (n := 116) (.out 0x10a077 (shrR32Effect 0x10a077 4 8 4) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[114]
    (.letOp (n := 117) (.exec 0x10a077 (fun s => s.RIP = 0x10a077) (shrR32Effect 0x10a077 4 8 4) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[114]
    (.letOp (n := 118) (.exec 0x10a07b (StorePre 0x10a07b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10a07b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10a07b 7 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[7, 4]
    (.letOp (n := 119) (.out 0x10a080 (movzxR32M8Effect 0x10a080 4 7 (.base 2 (.d8 0x3))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[2]
    (.letOp (n := 120) (.exec 0x10a080 (LoadPre 0x10a080 (fun s => AddrMode.addr (.base 2 (.d8 0x3)) s (0x10a080 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a080 4 7 (.base 2 (.d8 0x3))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 121) (.out 0x10a084 (shlR32Effect 0x10a084 3 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[119]
    (.letOp (n := 122) (.exec 0x10a084 (fun s => s.RIP = 0x10a084) (shlR32Effect 0x10a084 3 7 8) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[119]
    (.letOp (n := 123) (.out 0x10a087 (movzxR32M8Effect 0x10a087 5 15 (.base 2 (.d8 0x1))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[2]
    (.letOp (n := 124) (.exec 0x10a087 (LoadPre 0x10a087 (fun s => AddrMode.addr (.base 2 (.d8 0x1)) s (0x10a087 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10a087 5 15 (.base 2 (.d8 0x1))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 125) (.out 0x10a08c (orR32R32Effect 0x10a08c 3 15 7) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 7] []) (.reg (.gpr 15))) #v[123, 121]
    (.letOp (n := 126) (.exec 0x10a08c (fun s => s.RIP = 0x10a08c) (orR32R32Effect 0x10a08c 3 15 7) (Reg.operands [.gpr 15, .gpr 7] [])) #v[123, 121]
    (.letOp (n := 127) (.out 0x10a08f (movR32R32Effect 0x10a08f 3 9 15) (EffectPart.reads (.reg (.gpr 9)) [.gpr 15] []) (.reg (.gpr 9))) #v[125]
    (.letOp (n := 128) (.exec 0x10a08f (fun s => s.RIP = 0x10a08f) (movR32R32Effect 0x10a08f 3 9 15) (Reg.operands [.gpr 15] [])) #v[125]
    (.letOp (n := 129) (.out 0x10a092 (shrR32Effect 0x10a092 3 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[127]
    (.letOp (n := 130) (.exec 0x10a092 (fun s => s.RIP = 0x10a092) (shrR32Effect 0x10a092 3 9 1) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[127]
    (b_l10a008_2)))))))))))))))))))))))))))))))))))))))

def bytes_l10a008_1 : List UInt8 :=
  [0x41, 0xD1, 0xEA, 0x0F, 0xB6, 0x4A, 0x0E, 0xC1, 0xE1, 0x08, 0x44, 0x0F, 0xB6, 0x62, 0x0C, 0x41,
    0x09, 0xCC, 0x45, 0x31, 0xE2, 0x41, 0x81, 0xE2, 0x55, 0x55, 0x00, 0x00, 0x45, 0x31, 0xD4, 0x44,
    0x31, 0xE6, 0x81, 0xE6, 0x33, 0x33, 0x00, 0x00, 0x41, 0x31, 0xF4, 0x45, 0x89, 0xE0, 0x41, 0xC1,
    0xE8, 0x04, 0x48, 0x89, 0x7C, 0x24, 0x10, 0x0F, 0xB6, 0x7A, 0x03, 0xC1, 0xE7, 0x08, 0x44, 0x0F,
    0xB6, 0x7A, 0x01, 0x41, 0x09, 0xFF, 0x45, 0x89, 0xF9, 0x41, 0xD1, 0xE9] ++ bytes_l10a008_2

theorem code_l10a008_1 : ∀ x ∈ codeRange 0x10a049 bytes_l10a008_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa049 76 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a008_2

@[cfg_block] def b_l10a008 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10a008 (movzxR32M8Effect 0x10a008 4 0 (.base 2 (.d8 0x2))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 54) (.exec 0x10a008 (LoadPre 0x10a008 (fun s => AddrMode.addr (.base 2 (.d8 0x2)) s (0x10a008 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a008 4 0 (.base 2 (.d8 0x2))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 55) (.out 0x10a00c (shlR32Effect 0x10a00c 3 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x10a00c (fun s => s.RIP = 0x10a00c) (shlR32Effect 0x10a00c 3 0 8) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 57) (.out 0x10a00f (movzxR32M8Effect 0x10a00f 4 11 (.base 2 .none)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[2]
    (.letOp (n := 58) (.exec 0x10a00f (LoadPre 0x10a00f (fun s => AddrMode.addr (.base 2 .none) s (0x10a00f + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a00f 4 11 (.base 2 .none)) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 59) (.out 0x10a013 (orR32R32Effect 0x10a013 3 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0] []) (.reg (.gpr 11))) #v[57, 55]
    (.letOp (n := 60) (.exec 0x10a013 (fun s => s.RIP = 0x10a013) (orR32R32Effect 0x10a013 3 11 0) (Reg.operands [.gpr 11, .gpr 0] [])) #v[57, 55]
    (.letOp (n := 61) (.out 0x10a016 (movR32R32Effect 0x10a016 3 3 11) (EffectPart.reads (.reg (.gpr 3)) [.gpr 11] []) (.reg (.gpr 3))) #v[59]
    (.letOp (n := 62) (.exec 0x10a016 (fun s => s.RIP = 0x10a016) (movR32R32Effect 0x10a016 3 3 11) (Reg.operands [.gpr 11] [])) #v[59]
    (.letOp (n := 63) (.out 0x10a019 (shrR32Effect 0x10a019 2 3 1) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[61]
    (.letOp (n := 64) (.exec 0x10a019 (fun s => s.RIP = 0x10a019) (shrR32Effect 0x10a019 2 3 1) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[61]
    (.letOp (n := 65) (.out 0x10a01b (movzxR32M8Effect 0x10a01b 4 1 (.base 2 (.d8 0x6))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2]
    (.letOp (n := 66) (.exec 0x10a01b (LoadPre 0x10a01b (fun s => AddrMode.addr (.base 2 (.d8 0x6)) s (0x10a01b + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a01b 4 1 (.base 2 (.d8 0x6))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 67) (.out 0x10a01f (shlR32Effect 0x10a01f 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 68) (.exec 0x10a01f (fun s => s.RIP = 0x10a01f) (shlR32Effect 0x10a01f 3 1 8) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[65]
    (.letOp (n := 69) (.out 0x10a022 (movzxR32M8Effect 0x10a022 4 6 (.base 2 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[2]
    (.letOp (n := 70) (.exec 0x10a022 (LoadPre 0x10a022 (fun s => AddrMode.addr (.base 2 (.d8 0x4)) s (0x10a022 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a022 4 6 (.base 2 (.d8 0x4))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 71) (.out 0x10a026 (orR32R32Effect 0x10a026 2 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[69, 67]
    (.letOp (n := 72) (.exec 0x10a026 (fun s => s.RIP = 0x10a026) (orR32R32Effect 0x10a026 2 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[69, 67]
    (.letOp (n := 73) (.out 0x10a028 (xorR32R32Effect 0x10a028 2 3 6) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 6] []) (.reg (.gpr 3))) #v[63, 71]
    (.letOp (n := 74) (.exec 0x10a028 (fun s => s.RIP = 0x10a028) (xorR32R32Effect 0x10a028 2 3 6) (Reg.operands [.gpr 3, .gpr 6] [])) #v[63, 71]
    (.letOp (n := 75) (.out 0x10a02a (andR32Imm32Effect 0x10a02a 6 3 0x5555) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[73]
    (.letOp (n := 76) (.exec 0x10a02a (fun s => s.RIP = 0x10a02a) (andR32Imm32Effect 0x10a02a 6 3 0x5555) (Reg.operands [.gpr 3] [])) #v[73]
    (.letOp (n := 77) (.out 0x10a030 (xorR32R32Effect 0x10a030 2 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 3] []) (.reg (.gpr 6))) #v[71, 75]
    (.letOp (n := 78) (.exec 0x10a030 (fun s => s.RIP = 0x10a030) (xorR32R32Effect 0x10a030 2 6 3) (Reg.operands [.gpr 6, .gpr 3] [])) #v[71, 75]
    (.letOp (n := 79) (.exec 0x10a032 (StorePre 0x10a032 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x10a032 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x10a032 6 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[77, 4]
    (.letOp (n := 80) (.out 0x10a036 (shrR32Effect 0x10a036 3 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[77]
    (.letOp (n := 81) (.exec 0x10a036 (fun s => s.RIP = 0x10a036) (shrR32Effect 0x10a036 3 6 2) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[77]
    (.letOp (n := 82) (.out 0x10a039 (movzxR32M8Effect 0x10a039 4 1 (.base 2 (.d8 0xa))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2]
    (.letOp (n := 83) (.exec 0x10a039 (LoadPre 0x10a039 (fun s => AddrMode.addr (.base 2 (.d8 0xa)) s (0x10a039 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a039 4 1 (.base 2 (.d8 0xa))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 84) (.out 0x10a03d (shlR32Effect 0x10a03d 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[82]
    (.letOp (n := 85) (.exec 0x10a03d (fun s => s.RIP = 0x10a03d) (shlR32Effect 0x10a03d 3 1 8) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[82]
    (.letOp (n := 86) (.out 0x10a040 (movzxR32M8Effect 0x10a040 4 5 (.base 2 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[2]
    (.letOp (n := 87) (.exec 0x10a040 (LoadPre 0x10a040 (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x10a040 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a040 4 5 (.base 2 (.d8 0x8))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 88) (.out 0x10a044 (orR32R32Effect 0x10a044 2 5 1) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 1] []) (.reg (.gpr 5))) #v[86, 84]
    (.letOp (n := 89) (.exec 0x10a044 (fun s => s.RIP = 0x10a044) (orR32R32Effect 0x10a044 2 5 1) (Reg.operands [.gpr 5, .gpr 1] [])) #v[86, 84]
    (.letOp (n := 90) (.out 0x10a046 (movR32R32Effect 0x10a046 3 10 5) (EffectPart.reads (.reg (.gpr 10)) [.gpr 5] []) (.reg (.gpr 10))) #v[88]
    (.letOp (n := 91) (.exec 0x10a046 (fun s => s.RIP = 0x10a046) (movR32R32Effect 0x10a046 3 10 5) (Reg.operands [.gpr 5] [])) #v[88]
    (b_l10a008_1)))))))))))))))))))))))))))))))))))))))

def bytes_l10a008 : List UInt8 :=
  [0x0F, 0xB6, 0x42, 0x02, 0xC1, 0xE0, 0x08, 0x44, 0x0F, 0xB6, 0x1A, 0x41, 0x09, 0xC3, 0x44, 0x89,
    0xDB, 0xD1, 0xEB, 0x0F, 0xB6, 0x4A, 0x06, 0xC1, 0xE1, 0x08, 0x0F, 0xB6, 0x72, 0x04, 0x09, 0xCE,
    0x31, 0xF3, 0x81, 0xE3, 0x55, 0x55, 0x00, 0x00, 0x31, 0xDE, 0x89, 0x74, 0x24, 0x0C, 0xC1, 0xEE,
    0x02, 0x0F, 0xB6, 0x4A, 0x0A, 0xC1, 0xE1, 0x08, 0x0F, 0xB6, 0x6A, 0x08, 0x09, 0xCD, 0x41, 0x89,
    0xEA] ++ bytes_l10a008_1

theorem code_l10a008 : ∀ x ∈ codeRange 0x10a008 bytes_l10a008, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa008 65 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a008_1

@[cfg_block] def b_l10a1f1 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10a1f1 (movR64R64Effect 0x10a1f1 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6] []) (.reg (.gpr 2))) #v[6]
    (.letOp (n := 54) (.exec 0x10a1f1 (fun s => s.RIP = 0x10a1f1) (movR64R64Effect 0x10a1f1 2 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 55) (.out 0x10a1f4 (movR32Imm32Effect 0x10a1f4 5 6 0x8) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 56) (.exec 0x10a1f4 (fun s => s.RIP = 0x10a1f4) (movR32Imm32Effect 0x10a1f4 5 6 0x8) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x10a1f9 (xorR32R32Effect 0x10a1f9 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[7, 7]
    (.letOp (n := 58) (.exec 0x10a1f9 (fun s => s.RIP = 0x10a1f9) (xorR32R32Effect 0x10a1f9 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[7, 7]
    (.letOp (n := 59) (.out 0x10a1fb (movR64Imm32Effect 0x10a1fb 1 0x201118) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 60) (.exec 0x10a1fb (fun s => s.RIP = 0x10a1fb) (movR64Imm32Effect 0x10a1fb 1 0x201118) (Reg.operands [] [])) #v[]
    (.letOp (n := 61) (.out 0x10a202 (callEffect (fun _ => 0x103c70) 0x10a207) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 62) (.exec 0x10a202 (PushPre 0x10a202 5) (callEffect (fun _ => 0x103c70) 0x10a207) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.const ⟨64, 0x10a207⟩) #v[]
    (.terminate (.call ⟨.l103c70, RegMap.args [(1, 59), (2, 53), (4, 61), (5, 5), (6, 55), (7, 57)] 64⟩ { target := .l10a207, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l10a1f1 : List UInt8 :=
  [0x48, 0x89, 0xF2, 0xBE, 0x08, 0x00, 0x00, 0x00, 0x31, 0xFF, 0x48, 0xC7, 0xC1, 0x18, 0x11, 0x20,
    0x00, 0xE8, 0x69, 0x9A, 0xFF, 0xFF]

theorem code_l10a1f1 : ∀ x ∈ codeRange 0x10a1f1 bytes_l10a1f1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xa1f1 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10a207 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x10a207 (fun s => s.RIP = 0x10a207) (fun _ => nopEffect 0x10a207 9) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l10a210, RegMap.args [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 54⟩))

def bytes_l10a207 : List UInt8 :=
  [0x66, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem code_l10a207 : ∀ x ∈ codeRange 0x10a207 bytes_l10a207, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xa207 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10a210 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10a210 (pushR64Effect 0x10a210 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x10a210 (PushPre 0x10a210 1) (pushR64Effect 0x10a210 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x10a211 (pushR64Effect 0x10a211 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x10a211 (PushPre 0x10a211 2) (pushR64Effect 0x10a211 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x10a213 (pushR64Effect 0x10a213 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x10a213 (PushPre 0x10a213 2) (pushR64Effect 0x10a213 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x10a215 (pushR64Effect 0x10a215 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x10a215 (PushPre 0x10a215 2) (pushR64Effect 0x10a215 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x10a217 (pushR64Effect 0x10a217 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x10a217 (PushPre 0x10a217 2) (pushR64Effect 0x10a217 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x10a219 (pushR64Effect 0x10a219 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x10a219 (PushPre 0x10a219 1) (pushR64Effect 0x10a219 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x10a21a (pushR64Effect 0x10a21a 1 0) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 0] []) (.reg (.gpr 4))) #v[63, 0]
    (.letOp (n := 66) (.exec 0x10a21a (PushPre 0x10a21a 1) (pushR64Effect 0x10a21a 1 0) (Reg.operands [.gpr 4, .gpr 0] [])) #v[63, 0]
    (.letOp (n := 67) (.out 0x10a21b (testR64R64Effect 0x10a21b 2 2) (EffectPart.reads (.flag .ZF) [.gpr 2, .gpr 2] []) (.flag .ZF)) #v[2, 2]
    (.letOp (n := 68) (.exec 0x10a21b (fun s => s.RIP = 0x10a21b) (testR64R64Effect 0x10a21b 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 69) (.pure (condOp 4)) #v[67]
    (.terminate (.condBr (Fin.last 69) ⟨.l10a5d7, RegMap.args [(0, 0), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (19, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 70⟩ ⟨.l10a224, RegMap.args [(0, 0), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (19, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 70⟩))))))))))))))))))

def bytes_l10a210 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x50, 0x48, 0x85, 0xD2, 0x0F, 0x84,
    0xB3, 0x03, 0x00, 0x00]

theorem code_l10a210 : ∀ x ∈ codeRange 0x10a210 bytes_l10a210, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xa210 20 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10a224 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10a224 (cmpR64Imm8Effect 0x10a224 2 0x1) (EffectPart.reads (.flag .ZF) [.gpr 2] []) (.flag .ZF)) #v[2]
    (.letOp (n := 54) (.exec 0x10a224 (fun s => s.RIP = 0x10a224) (cmpR64Imm8Effect 0x10a224 2 0x1) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l10a5e7, RegMap.args [(2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l10a22e, RegMap.args [(2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l10a224 : List UInt8 :=
  [0x48, 0x83, 0xFA, 0x01, 0x0F, 0x84, 0xB9, 0x03, 0x00, 0x00]

theorem code_l10a224 : ∀ x ∈ codeRange 0x10a224 bytes_l10a224, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xa224 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10a22e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10a22e (cmpR64Imm8Effect 0x10a22e 2 0x2) (EffectPart.reads (.flag .CF) [.gpr 2] []) (.flag .CF)) #v[2]
    (.letOp (n := 54) (.out 0x10a22e (cmpR64Imm8Effect 0x10a22e 2 0x2) (EffectPart.reads (.flag .ZF) [.gpr 2] []) (.flag .ZF)) #v[2]
    (.letOp (n := 55) (.exec 0x10a22e (fun s => s.RIP = 0x10a22e) (cmpR64Imm8Effect 0x10a22e 2 0x2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 56) (.pure (condOp 6)) #v[53, 54]
    (.terminate (.condBr (Fin.last 56) ⟨.l10a5fd, RegMap.args [(2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩ ⟨.l10a238, RegMap.args [(2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l10a22e : List UInt8 :=
  [0x48, 0x83, 0xFA, 0x02, 0x0F, 0x86, 0xC5, 0x03, 0x00, 0x00]

theorem code_l10a22e : ∀ x ∈ codeRange 0x10a22e bytes_l10a22e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xa22e 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10a238 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10a238 (cmpR64Imm8Effect 0x10a238 2 0x3) (EffectPart.reads (.flag .ZF) [.gpr 2] []) (.flag .ZF)) #v[2]
    (.letOp (n := 54) (.exec 0x10a238 (fun s => s.RIP = 0x10a238) (cmpR64Imm8Effect 0x10a238 2 0x3) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l10a613, RegMap.args [(2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l10a242, RegMap.args [(2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l10a238 : List UInt8 :=
  [0x48, 0x83, 0xFA, 0x03, 0x0F, 0x84, 0xD1, 0x03, 0x00, 0x00]

theorem code_l10a238 : ∀ x ∈ codeRange 0x10a238 bytes_l10a238, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xa238 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10a242 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10a242 (cmpR64Imm8Effect 0x10a242 2 0x4) (EffectPart.reads (.flag .CF) [.gpr 2] []) (.flag .CF)) #v[2]
    (.letOp (n := 54) (.out 0x10a242 (cmpR64Imm8Effect 0x10a242 2 0x4) (EffectPart.reads (.flag .ZF) [.gpr 2] []) (.flag .ZF)) #v[2]
    (.letOp (n := 55) (.exec 0x10a242 (fun s => s.RIP = 0x10a242) (cmpR64Imm8Effect 0x10a242 2 0x4) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 56) (.pure (condOp 6)) #v[53, 54]
    (.terminate (.condBr (Fin.last 56) ⟨.l10a629, RegMap.args [(2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩ ⟨.l10a24c, RegMap.args [(2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l10a242 : List UInt8 :=
  [0x48, 0x83, 0xFA, 0x04, 0x0F, 0x86, 0xDD, 0x03, 0x00, 0x00]

theorem code_l10a242 : ∀ x ∈ codeRange 0x10a242 bytes_l10a242, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xa242 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10a24c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10a24c (cmpR64Imm8Effect 0x10a24c 2 0x5) (EffectPart.reads (.flag .ZF) [.gpr 2] []) (.flag .ZF)) #v[2]
    (.letOp (n := 54) (.exec 0x10a24c (fun s => s.RIP = 0x10a24c) (cmpR64Imm8Effect 0x10a24c 2 0x5) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l10a63f, RegMap.args [(2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l10a256, RegMap.args [(2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l10a24c : List UInt8 :=
  [0x48, 0x83, 0xFA, 0x05, 0x0F, 0x84, 0xE9, 0x03, 0x00, 0x00]

theorem code_l10a24c : ∀ x ∈ codeRange 0x10a24c bytes_l10a24c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xa24c 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10a256 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10a256 (cmpR64Imm8Effect 0x10a256 2 0x6) (EffectPart.reads (.flag .CF) [.gpr 2] []) (.flag .CF)) #v[2]
    (.letOp (n := 54) (.out 0x10a256 (cmpR64Imm8Effect 0x10a256 2 0x6) (EffectPart.reads (.flag .ZF) [.gpr 2] []) (.flag .ZF)) #v[2]
    (.letOp (n := 55) (.exec 0x10a256 (fun s => s.RIP = 0x10a256) (cmpR64Imm8Effect 0x10a256 2 0x6) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 56) (.pure (condOp 6)) #v[53, 54]
    (.terminate (.condBr (Fin.last 56) ⟨.l10a655, RegMap.args [(2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩ ⟨.l10a260, RegMap.args [(2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l10a256 : List UInt8 :=
  [0x48, 0x83, 0xFA, 0x06, 0x0F, 0x86, 0xF5, 0x03, 0x00, 0x00]

theorem code_l10a256 : ∀ x ∈ codeRange 0x10a256 bytes_l10a256, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xa256 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10a260 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10a260 (cmpR64Imm8Effect 0x10a260 2 0x7) (EffectPart.reads (.flag .ZF) [.gpr 2] []) (.flag .ZF)) #v[2]
    (.letOp (n := 54) (.exec 0x10a260 (fun s => s.RIP = 0x10a260) (cmpR64Imm8Effect 0x10a260 2 0x7) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l10a66b, RegMap.args [(2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l10a26a, RegMap.args [(2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l10a260 : List UInt8 :=
  [0x48, 0x83, 0xFA, 0x07, 0x0F, 0x84, 0x01, 0x04, 0x00, 0x00]

theorem code_l10a260 : ∀ x ∈ codeRange 0x10a260 bytes_l10a260, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xa260 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

def b_l10a26a_12 : Block Op Label signature Reg.count 474 :=
  .letOp (n := 474) (.out 0x10a5a5 (movR64R64Effect 0x10a5a5 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[414]
    (.letOp (n := 475) (.exec 0x10a5a5 (fun s => s.RIP = 0x10a5a5) (movR64R64Effect 0x10a5a5 1 0) (Reg.operands [.gpr 0] [])) #v[414]
    (.letOp (n := 476) (.exec 0x10a5a8 (StorePre 0x10a5a8 3 (fun s => AddrMode.addr (.base 7 (.d8 0x3b)) s (0x10a5a8 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a5a8 3 2 (.base 7 (.d8 0x3b))) (Reg.operands [.gpr 2, .gpr 7] [])) #v[471, 7]
    (.letOp (n := 477) (.out 0x10a5ab (movR64R64Effect 0x10a5ab 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0] []) (.reg (.gpr 2))) #v[414]
    (.letOp (n := 478) (.exec 0x10a5ab (fun s => s.RIP = 0x10a5ab) (movR64R64Effect 0x10a5ab 2 0) (Reg.operands [.gpr 0] [])) #v[414]
    (.letOp (n := 479) (.exec 0x10a5ae (StorePre 0x10a5ae 3 (fun s => AddrMode.addr (.base 7 (.d8 0x3c)) s (0x10a5ae + BitVec.ofNat 64 3)) 1) (movM8R8NoRexEffect 0x10a5ae 3 4 (.base 7 (.d8 0x3c))) (Reg.operands [.gpr 0, .gpr 7] [])) #v[414, 7]
    (.letOp (n := 480) (.out 0x10a5b1 (shrR32Effect 0x10a5b1 3 0 24) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[414]
    (.letOp (n := 481) (.exec 0x10a5b1 (fun s => s.RIP = 0x10a5b1) (shrR32Effect 0x10a5b1 3 0 24) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[414]
    (.letOp (n := 482) (.exec 0x10a5b4 (StorePre 0x10a5b4 3 (fun s => AddrMode.addr (.base 7 (.d8 0x3d)) s (0x10a5b4 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a5b4 3 0 (.base 7 (.d8 0x3d))) (Reg.operands [.gpr 0, .gpr 7] [])) #v[480, 7]
    (.letOp (n := 483) (.out 0x10a5b7 (shrR64Effect 0x10a5b7 4 1 40) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[474]
    (.letOp (n := 484) (.exec 0x10a5b7 (fun s => s.RIP = 0x10a5b7) (shrR64Effect 0x10a5b7 4 1 40) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[474]
    (.letOp (n := 485) (.exec 0x10a5bb (StorePre 0x10a5bb 3 (fun s => AddrMode.addr (.base 7 (.d8 0x3e)) s (0x10a5bb + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a5bb 3 1 (.base 7 (.d8 0x3e))) (Reg.operands [.gpr 1, .gpr 7] [])) #v[483, 7]
    (.letOp (n := 486) (.out 0x10a5be (shrR64Effect 0x10a5be 4 2 56) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[477]
    (.letOp (n := 487) (.exec 0x10a5be (fun s => s.RIP = 0x10a5be) (shrR64Effect 0x10a5be 4 2 56) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[477]
    (.letOp (n := 488) (.exec 0x10a5c2 (StorePre 0x10a5c2 3 (fun s => AddrMode.addr (.base 7 (.d8 0x3f)) s (0x10a5c2 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a5c2 3 2 (.base 7 (.d8 0x3f))) (Reg.operands [.gpr 2, .gpr 7] [])) #v[486, 7]
    (.letOp (n := 489) (.out 0x10a5c5 (movR64R64Effect 0x10a5c5 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 490) (.exec 0x10a5c5 (fun s => s.RIP = 0x10a5c5) (movR64R64Effect 0x10a5c5 0 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 491) (.out 0x10a5c8 (addR64Imm8Effect 0x10a5c8 4 0x8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 492) (.exec 0x10a5c8 (fun s => s.RIP = 0x10a5c8) (addR64Imm8Effect 0x10a5c8 4 0x8) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 493) (.out 0x10a5cc (popR64Effect 0x10a5cc 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[491]
    (.letOp (n := 494) (.out 0x10a5cc (popR64Effect 0x10a5cc 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[491]
    (.letOp (n := 495) (.exec 0x10a5cc (PopPre 0x10a5cc) (popR64Effect 0x10a5cc 1 3) (Reg.operands [.gpr 4] [])) #v[491]
    (.letOp (n := 496) (.out 0x10a5cd (popR64Effect 0x10a5cd 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[494]
    (.letOp (n := 497) (.out 0x10a5cd (popR64Effect 0x10a5cd 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[494]
    (.letOp (n := 498) (.exec 0x10a5cd (PopPre 0x10a5cd) (popR64Effect 0x10a5cd 2 12) (Reg.operands [.gpr 4] [])) #v[494]
    (.letOp (n := 499) (.out 0x10a5cf (popR64Effect 0x10a5cf 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[497]
    (.letOp (n := 500) (.out 0x10a5cf (popR64Effect 0x10a5cf 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[497]
    (.letOp (n := 501) (.exec 0x10a5cf (PopPre 0x10a5cf) (popR64Effect 0x10a5cf 2 13) (Reg.operands [.gpr 4] [])) #v[497]
    (.letOp (n := 502) (.out 0x10a5d1 (popR64Effect 0x10a5d1 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[500]
    (.letOp (n := 503) (.out 0x10a5d1 (popR64Effect 0x10a5d1 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[500]
    (.letOp (n := 504) (.exec 0x10a5d1 (PopPre 0x10a5d1) (popR64Effect 0x10a5d1 2 14) (Reg.operands [.gpr 4] [])) #v[500]
    (.letOp (n := 505) (.out 0x10a5d3 (popR64Effect 0x10a5d3 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[503]
    (.letOp (n := 506) (.out 0x10a5d3 (popR64Effect 0x10a5d3 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[503]
    (.letOp (n := 507) (.exec 0x10a5d3 (PopPre 0x10a5d3) (popR64Effect 0x10a5d3 2 15) (Reg.operands [.gpr 4] [])) #v[503]
    (.letOp (n := 508) (.out 0x10a5d5 (popR64Effect 0x10a5d5 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[506]
    (.letOp (n := 509) (.out 0x10a5d5 (popR64Effect 0x10a5d5 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[506]
    (.letOp (n := 510) (.exec 0x10a5d5 (PopPre 0x10a5d5) (popR64Effect 0x10a5d5 1 5) (Reg.operands [.gpr 4] [])) #v[506]
    (.letOp (n := 511) (.out 0x10a5d6 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[509]
    (.letOp (n := 512) (.out 0x10a5d6 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[509]
    (.letOp (n := 513) (.exec 0x10a5d6 (RetPre 0x10a5d6) (retEffect) (Reg.operands [.gpr 4] [])) #v[509]
    (.terminate (.ret (RegMap.args [(0, 489), (1, 483), (2, 486), (3, 493), (4, 512), (5, 508), (6, 469), (7, 7), (8, 425), (9, 163), (10, 423), (11, 349), (12, 496), (13, 499), (14, 502), (15, 505), (22, 22), (39, 39), (50, 50), (51, 51)] 514) (some ⟨511, by decide⟩))))))))))))))))))))))))))))))))))))))))))

def bytes_l10a26a_12 : List UInt8 :=
  [0x48, 0x89, 0xC1, 0x88, 0x57, 0x3B, 0x48, 0x89, 0xC2, 0x88, 0x67, 0x3C, 0xC1, 0xE8, 0x18, 0x88,
    0x47, 0x3D, 0x48, 0xC1, 0xE9, 0x28, 0x88, 0x4F, 0x3E, 0x48, 0xC1, 0xEA, 0x38, 0x88, 0x57, 0x3F,
    0x48, 0x89, 0xF8, 0x48, 0x83, 0xC4, 0x08, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F,
    0x5D, 0xC3]

theorem code_l10a26a_12 : ∀ x ∈ codeRange 0x10a5a5 bytes_l10a26a_12, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xa5a5 50 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

def b_l10a26a_11 : Block Op Label signature Reg.count 443 :=
  .letOp (n := 443) (.exec 0x10a564 (StorePre 0x10a564 4 (fun s => AddrMode.addr (.base 7 (.d8 0x32)) s (0x10a564 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a564 4 6 (.base 7 (.d8 0x32))) (Reg.operands [.gpr 6, .gpr 7] [])) #v[435, 7]
    (.letOp (n := 444) (.out 0x10a568 (movR64R64Effect 0x10a568 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 1] []) (.reg (.gpr 6))) #v[418]
    (.letOp (n := 445) (.exec 0x10a568 (fun s => s.RIP = 0x10a568) (movR64R64Effect 0x10a568 6 1) (Reg.operands [.gpr 1] [])) #v[418]
    (.letOp (n := 446) (.exec 0x10a56b (StorePre 0x10a56b 3 (fun s => AddrMode.addr (.base 7 (.d8 0x33)) s (0x10a56b + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a56b 3 2 (.base 7 (.d8 0x33))) (Reg.operands [.gpr 2, .gpr 7] [])) #v[441, 7]
    (.letOp (n := 447) (.out 0x10a56e (movR32R32Effect 0x10a56e 2 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0] []) (.reg (.gpr 2))) #v[414]
    (.letOp (n := 448) (.exec 0x10a56e (fun s => s.RIP = 0x10a56e) (movR32R32Effect 0x10a56e 2 2 0) (Reg.operands [.gpr 0] [])) #v[414]
    (.letOp (n := 449) (.out 0x10a570 (shrR32Effect 0x10a570 3 2 16) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[447]
    (.letOp (n := 450) (.exec 0x10a570 (fun s => s.RIP = 0x10a570) (shrR32Effect 0x10a570 3 2 16) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[447]
    (.letOp (n := 451) (.exec 0x10a573 (StorePre 0x10a573 3 (fun s => AddrMode.addr (.base 7 (.d8 0x34)) s (0x10a573 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a573 3 0 (.base 7 (.d8 0x34))) (Reg.operands [.gpr 0, .gpr 7] [])) #v[414, 7]
    (.letOp (n := 452) (.exec 0x10a576 (StorePre 0x10a576 3 (fun s => AddrMode.addr (.base 7 (.d8 0x35)) s (0x10a576 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a576 3 2 (.base 7 (.d8 0x35))) (Reg.operands [.gpr 2, .gpr 7] [])) #v[449, 7]
    (.letOp (n := 453) (.out 0x10a579 (movR64R64Effect 0x10a579 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0] []) (.reg (.gpr 2))) #v[414]
    (.letOp (n := 454) (.exec 0x10a579 (fun s => s.RIP = 0x10a579) (movR64R64Effect 0x10a579 2 0) (Reg.operands [.gpr 0] [])) #v[414]
    (.letOp (n := 455) (.out 0x10a57c (shrR64Effect 0x10a57c 4 2 32) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[453]
    (.letOp (n := 456) (.exec 0x10a57c (fun s => s.RIP = 0x10a57c) (shrR64Effect 0x10a57c 4 2 32) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[453]
    (.letOp (n := 457) (.exec 0x10a580 (StorePre 0x10a580 3 (fun s => AddrMode.addr (.base 7 (.d8 0x36)) s (0x10a580 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a580 3 2 (.base 7 (.d8 0x36))) (Reg.operands [.gpr 2, .gpr 7] [])) #v[455, 7]
    (.letOp (n := 458) (.out 0x10a583 (movR64R64Effect 0x10a583 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0] []) (.reg (.gpr 2))) #v[414]
    (.letOp (n := 459) (.exec 0x10a583 (fun s => s.RIP = 0x10a583) (movR64R64Effect 0x10a583 2 0) (Reg.operands [.gpr 0] [])) #v[414]
    (.letOp (n := 460) (.out 0x10a586 (shrR64Effect 0x10a586 4 2 48) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[458]
    (.letOp (n := 461) (.exec 0x10a586 (fun s => s.RIP = 0x10a586) (shrR64Effect 0x10a586 4 2 48) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[458]
    (.letOp (n := 462) (.exec 0x10a58a (StorePre 0x10a58a 3 (fun s => AddrMode.addr (.base 7 (.d8 0x37)) s (0x10a58a + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a58a 3 2 (.base 7 (.d8 0x37))) (Reg.operands [.gpr 2, .gpr 7] [])) #v[460, 7]
    (.letOp (n := 463) (.out 0x10a58d (movR64R64Effect 0x10a58d 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[418]
    (.letOp (n := 464) (.exec 0x10a58d (fun s => s.RIP = 0x10a58d) (movR64R64Effect 0x10a58d 2 1) (Reg.operands [.gpr 1] [])) #v[418]
    (.letOp (n := 465) (.exec 0x10a590 (StorePre 0x10a590 3 (fun s => AddrMode.addr (.base 7 (.d8 0x38)) s (0x10a590 + BitVec.ofNat 64 3)) 1) (movM8R8NoRexEffect 0x10a590 3 5 (.base 7 (.d8 0x38))) (Reg.operands [.gpr 1, .gpr 7] [])) #v[418, 7]
    (.letOp (n := 466) (.out 0x10a593 (shrR32Effect 0x10a593 3 1 24) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[418]
    (.letOp (n := 467) (.exec 0x10a593 (fun s => s.RIP = 0x10a593) (shrR32Effect 0x10a593 3 1 24) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[418]
    (.letOp (n := 468) (.exec 0x10a596 (StorePre 0x10a596 3 (fun s => AddrMode.addr (.base 7 (.d8 0x39)) s (0x10a596 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a596 3 1 (.base 7 (.d8 0x39))) (Reg.operands [.gpr 1, .gpr 7] [])) #v[466, 7]
    (.letOp (n := 469) (.out 0x10a599 (shrR64Effect 0x10a599 4 6 40) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[444]
    (.letOp (n := 470) (.exec 0x10a599 (fun s => s.RIP = 0x10a599) (shrR64Effect 0x10a599 4 6 40) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[444]
    (.letOp (n := 471) (.out 0x10a59d (shrR64Effect 0x10a59d 4 2 56) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[463]
    (.letOp (n := 472) (.exec 0x10a59d (fun s => s.RIP = 0x10a59d) (shrR64Effect 0x10a59d 4 2 56) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[463]
    (.letOp (n := 473) (.exec 0x10a5a1 (StorePre 0x10a5a1 4 (fun s => AddrMode.addr (.base 7 (.d8 0x3a)) s (0x10a5a1 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a5a1 4 6 (.base 7 (.d8 0x3a))) (Reg.operands [.gpr 6, .gpr 7] [])) #v[469, 7]
    (b_l10a26a_12)))))))))))))))))))))))))))))))

def bytes_l10a26a_11 : List UInt8 :=
  [0x40, 0x88, 0x77, 0x32, 0x48, 0x89, 0xCE, 0x88, 0x57, 0x33, 0x89, 0xC2, 0xC1, 0xEA, 0x10, 0x88,
    0x47, 0x34, 0x88, 0x57, 0x35, 0x48, 0x89, 0xC2, 0x48, 0xC1, 0xEA, 0x20, 0x88, 0x57, 0x36, 0x48,
    0x89, 0xC2, 0x48, 0xC1, 0xEA, 0x30, 0x88, 0x57, 0x37, 0x48, 0x89, 0xCA, 0x88, 0x6F, 0x38, 0xC1,
    0xE9, 0x18, 0x88, 0x4F, 0x39, 0x48, 0xC1, 0xEE, 0x28, 0x48, 0xC1, 0xEA, 0x38, 0x40, 0x88, 0x77,
    0x3A] ++ bytes_l10a26a_12

theorem code_l10a26a_11 : ∀ x ∈ codeRange 0x10a564 bytes_l10a26a_11, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa564 65 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a26a_12

def b_l10a26a_10 : Block Op Label signature Reg.count 408 :=
  .letOp (n := 408) (.out 0x10a521 (shrR64Effect 0x10a521 4 1 4) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[406]
    (.letOp (n := 409) (.exec 0x10a521 (fun s => s.RIP = 0x10a521) (shrR64Effect 0x10a521 4 1 4) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[406]
    (.letOp (n := 410) (.out 0x10a525 (xorR64R64Effect 0x10a525 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[408, 248]
    (.letOp (n := 411) (.exec 0x10a525 (fun s => s.RIP = 0x10a525) (xorR64R64Effect 0x10a525 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[408, 248]
    (.letOp (n := 412) (.out 0x10a528 (andR64R64Effect 0x10a528 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 9] []) (.reg (.gpr 1))) #v[410, 163]
    (.letOp (n := 413) (.exec 0x10a528 (fun s => s.RIP = 0x10a528) (andR64R64Effect 0x10a528 1 9) (Reg.operands [.gpr 1, .gpr 9] [])) #v[410, 163]
    (.letOp (n := 414) (.out 0x10a52b (xorR64R64Effect 0x10a52b 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[248, 412]
    (.letOp (n := 415) (.exec 0x10a52b (fun s => s.RIP = 0x10a52b) (xorR64R64Effect 0x10a52b 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[248, 412]
    (.letOp (n := 416) (.out 0x10a52e (shlR64Effect 0x10a52e 4 1 4) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[412]
    (.letOp (n := 417) (.exec 0x10a52e (fun s => s.RIP = 0x10a52e) (shlR64Effect 0x10a52e 4 1 4) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[412]
    (.letOp (n := 418) (.out 0x10a532 (xorR64R64Effect 0x10a532 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 14] []) (.reg (.gpr 1))) #v[416, 218]
    (.letOp (n := 419) (.exec 0x10a532 (fun s => s.RIP = 0x10a532) (xorR64R64Effect 0x10a532 1 14) (Reg.operands [.gpr 1, .gpr 14] [])) #v[416, 218]
    (.letOp (n := 420) (.out 0x10a535 (shrR32Effect 0x10a535 3 2 24) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[340]
    (.letOp (n := 421) (.exec 0x10a535 (fun s => s.RIP = 0x10a535) (shrR32Effect 0x10a535 3 2 24) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[340]
    (.letOp (n := 422) (.exec 0x10a538 (StorePre 0x10a538 3 (fun s => AddrMode.addr (.base 7 (.d8 0x2d)) s (0x10a538 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a538 3 2 (.base 7 (.d8 0x2d))) (Reg.operands [.gpr 2, .gpr 7] [])) #v[420, 7]
    (.letOp (n := 423) (.out 0x10a53b (shrR64Effect 0x10a53b 4 10 40) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[399]
    (.letOp (n := 424) (.exec 0x10a53b (fun s => s.RIP = 0x10a53b) (shrR64Effect 0x10a53b 4 10 40) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[399]
    (.letOp (n := 425) (.out 0x10a53f (shrR64Effect 0x10a53f 4 8 56) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[402]
    (.letOp (n := 426) (.exec 0x10a53f (fun s => s.RIP = 0x10a53f) (shrR64Effect 0x10a53f 4 8 56) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[402]
    (.letOp (n := 427) (.exec 0x10a543 (StorePre 0x10a543 4 (fun s => AddrMode.addr (.base 7 (.d8 0x2e)) s (0x10a543 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a543 4 10 (.base 7 (.d8 0x2e))) (Reg.operands [.gpr 10, .gpr 7] [])) #v[423, 7]
    (.letOp (n := 428) (.out 0x10a547 (movR32R32Effect 0x10a547 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[418]
    (.letOp (n := 429) (.exec 0x10a547 (fun s => s.RIP = 0x10a547) (movR32R32Effect 0x10a547 2 2 1) (Reg.operands [.gpr 1] [])) #v[418]
    (.letOp (n := 430) (.out 0x10a549 (shrR32Effect 0x10a549 3 2 16) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[428]
    (.letOp (n := 431) (.exec 0x10a549 (fun s => s.RIP = 0x10a549) (shrR32Effect 0x10a549 3 2 16) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[428]
    (.letOp (n := 432) (.exec 0x10a54c (StorePre 0x10a54c 4 (fun s => AddrMode.addr (.base 7 (.d8 0x2f)) s (0x10a54c + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a54c 4 8 (.base 7 (.d8 0x2f))) (Reg.operands [.gpr 8, .gpr 7] [])) #v[425, 7]
    (.letOp (n := 433) (.out 0x10a550 (movR64R64Effect 0x10a550 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 1] []) (.reg (.gpr 6))) #v[418]
    (.letOp (n := 434) (.exec 0x10a550 (fun s => s.RIP = 0x10a550) (movR64R64Effect 0x10a550 6 1) (Reg.operands [.gpr 1] [])) #v[418]
    (.letOp (n := 435) (.out 0x10a553 (shrR64Effect 0x10a553 4 6 32) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[433]
    (.letOp (n := 436) (.exec 0x10a553 (fun s => s.RIP = 0x10a553) (shrR64Effect 0x10a553 4 6 32) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[433]
    (.letOp (n := 437) (.exec 0x10a557 (StorePre 0x10a557 3 (fun s => AddrMode.addr (.base 7 (.d8 0x30)) s (0x10a557 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a557 3 1 (.base 7 (.d8 0x30))) (Reg.operands [.gpr 1, .gpr 7] [])) #v[418, 7]
    (.letOp (n := 438) (.exec 0x10a55a (StorePre 0x10a55a 3 (fun s => AddrMode.addr (.base 7 (.d8 0x31)) s (0x10a55a + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a55a 3 2 (.base 7 (.d8 0x31))) (Reg.operands [.gpr 2, .gpr 7] [])) #v[430, 7]
    (.letOp (n := 439) (.out 0x10a55d (movR64R64Effect 0x10a55d 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[418]
    (.letOp (n := 440) (.exec 0x10a55d (fun s => s.RIP = 0x10a55d) (movR64R64Effect 0x10a55d 2 1) (Reg.operands [.gpr 1] [])) #v[418]
    (.letOp (n := 441) (.out 0x10a560 (shrR64Effect 0x10a560 4 2 48) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[439]
    (.letOp (n := 442) (.exec 0x10a560 (fun s => s.RIP = 0x10a560) (shrR64Effect 0x10a560 4 2 48) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[439]
    (b_l10a26a_11)))))))))))))))))))))))))))))))))))

def bytes_l10a26a_10 : List UInt8 :=
  [0x48, 0xC1, 0xE9, 0x04, 0x48, 0x31, 0xC1, 0x4C, 0x21, 0xC9, 0x48, 0x31, 0xC8, 0x48, 0xC1, 0xE1,
    0x04, 0x4C, 0x31, 0xF1, 0xC1, 0xEA, 0x18, 0x88, 0x57, 0x2D, 0x49, 0xC1, 0xEA, 0x28, 0x49, 0xC1,
    0xE8, 0x38, 0x44, 0x88, 0x57, 0x2E, 0x89, 0xCA, 0xC1, 0xEA, 0x10, 0x44, 0x88, 0x47, 0x2F, 0x48,
    0x89, 0xCE, 0x48, 0xC1, 0xEE, 0x20, 0x88, 0x4F, 0x30, 0x88, 0x57, 0x31, 0x48, 0x89, 0xCA, 0x48,
    0xC1, 0xEA, 0x30] ++ bytes_l10a26a_11

theorem code_l10a26a_10 : ∀ x ∈ codeRange 0x10a521 bytes_l10a26a_10, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa521 67 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a26a_11

def b_l10a26a_9 : Block Op Label signature Reg.count 377 :=
  .letOp (n := 377) (.exec 0x10a4dc (StorePre 0x10a4dc 3 (fun s => AddrMode.addr (.base 7 (.d8 0x24)) s (0x10a4dc + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a4dc 3 2 (.base 7 (.d8 0x24))) (Reg.operands [.gpr 2, .gpr 7] [])) #v[340, 7]
    (.letOp (n := 378) (.exec 0x10a4df (StorePre 0x10a4df 4 (fun s => AddrMode.addr (.base 7 (.d8 0x25)) s (0x10a4df + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a4df 4 6 (.base 7 (.d8 0x25))) (Reg.operands [.gpr 6, .gpr 7] [])) #v[375, 7]
    (.letOp (n := 379) (.out 0x10a4e3 (movR64R64Effect 0x10a4e3 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[340]
    (.letOp (n := 380) (.exec 0x10a4e3 (fun s => s.RIP = 0x10a4e3) (movR64R64Effect 0x10a4e3 6 2) (Reg.operands [.gpr 2] [])) #v[340]
    (.letOp (n := 381) (.out 0x10a4e6 (shrR64Effect 0x10a4e6 4 6 32) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[379]
    (.letOp (n := 382) (.exec 0x10a4e6 (fun s => s.RIP = 0x10a4e6) (shrR64Effect 0x10a4e6 4 6 32) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[379]
    (.letOp (n := 383) (.exec 0x10a4ea (StorePre 0x10a4ea 4 (fun s => AddrMode.addr (.base 7 (.d8 0x26)) s (0x10a4ea + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a4ea 4 6 (.base 7 (.d8 0x26))) (Reg.operands [.gpr 6, .gpr 7] [])) #v[381, 7]
    (.letOp (n := 384) (.out 0x10a4ee (movR64R64Effect 0x10a4ee 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[340]
    (.letOp (n := 385) (.exec 0x10a4ee (fun s => s.RIP = 0x10a4ee) (movR64R64Effect 0x10a4ee 6 2) (Reg.operands [.gpr 2] [])) #v[340]
    (.letOp (n := 386) (.out 0x10a4f1 (shrR64Effect 0x10a4f1 4 6 48) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[384]
    (.letOp (n := 387) (.exec 0x10a4f1 (fun s => s.RIP = 0x10a4f1) (shrR64Effect 0x10a4f1 4 6 48) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[384]
    (.letOp (n := 388) (.exec 0x10a4f5 (StorePre 0x10a4f5 4 (fun s => AddrMode.addr (.base 7 (.d8 0x27)) s (0x10a4f5 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a4f5 4 6 (.base 7 (.d8 0x27))) (Reg.operands [.gpr 6, .gpr 7] [])) #v[386, 7]
    (.letOp (n := 389) (.out 0x10a4f9 (movR64R64Effect 0x10a4f9 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 1] []) (.reg (.gpr 6))) #v[344]
    (.letOp (n := 390) (.exec 0x10a4f9 (fun s => s.RIP = 0x10a4f9) (movR64R64Effect 0x10a4f9 6 1) (Reg.operands [.gpr 1] [])) #v[344]
    (.letOp (n := 391) (.exec 0x10a4fc (StorePre 0x10a4fc 3 (fun s => AddrMode.addr (.base 7 (.d8 0x28)) s (0x10a4fc + BitVec.ofNat 64 3)) 1) (movM8R8NoRexEffect 0x10a4fc 3 5 (.base 7 (.d8 0x28))) (Reg.operands [.gpr 1, .gpr 7] [])) #v[344, 7]
    (.letOp (n := 392) (.out 0x10a4ff (shrR32Effect 0x10a4ff 3 1 24) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[344]
    (.letOp (n := 393) (.exec 0x10a4ff (fun s => s.RIP = 0x10a4ff) (shrR32Effect 0x10a4ff 3 1 24) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[344]
    (.letOp (n := 394) (.out 0x10a502 (shrR64Effect 0x10a502 4 8 40) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[370]
    (.letOp (n := 395) (.exec 0x10a502 (fun s => s.RIP = 0x10a502) (shrR64Effect 0x10a502 4 8 40) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[370]
    (.letOp (n := 396) (.out 0x10a506 (shrR64Effect 0x10a506 4 6 56) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[389]
    (.letOp (n := 397) (.exec 0x10a506 (fun s => s.RIP = 0x10a506) (shrR64Effect 0x10a506 4 6 56) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[389]
    (.letOp (n := 398) (.exec 0x10a50a (StorePre 0x10a50a 3 (fun s => AddrMode.addr (.base 7 (.d8 0x29)) s (0x10a50a + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a50a 3 1 (.base 7 (.d8 0x29))) (Reg.operands [.gpr 1, .gpr 7] [])) #v[392, 7]
    (.letOp (n := 399) (.out 0x10a50d (movR64R64Effect 0x10a50d 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[340]
    (.letOp (n := 400) (.exec 0x10a50d (fun s => s.RIP = 0x10a50d) (movR64R64Effect 0x10a50d 10 2) (Reg.operands [.gpr 2] [])) #v[340]
    (.letOp (n := 401) (.exec 0x10a510 (StorePre 0x10a510 4 (fun s => AddrMode.addr (.base 7 (.d8 0x2a)) s (0x10a510 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a510 4 8 (.base 7 (.d8 0x2a))) (Reg.operands [.gpr 8, .gpr 7] [])) #v[394, 7]
    (.letOp (n := 402) (.out 0x10a514 (movR64R64Effect 0x10a514 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[340]
    (.letOp (n := 403) (.exec 0x10a514 (fun s => s.RIP = 0x10a514) (movR64R64Effect 0x10a514 8 2) (Reg.operands [.gpr 2] [])) #v[340]
    (.letOp (n := 404) (.exec 0x10a517 (StorePre 0x10a517 4 (fun s => AddrMode.addr (.base 7 (.d8 0x2b)) s (0x10a517 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a517 4 6 (.base 7 (.d8 0x2b))) (Reg.operands [.gpr 6, .gpr 7] [])) #v[396, 7]
    (.letOp (n := 405) (.exec 0x10a51b (StorePre 0x10a51b 3 (fun s => AddrMode.addr (.base 7 (.d8 0x2c)) s (0x10a51b + BitVec.ofNat 64 3)) 1) (movM8R8NoRexEffect 0x10a51b 3 6 (.base 7 (.d8 0x2c))) (Reg.operands [.gpr 2, .gpr 7] [])) #v[340, 7]
    (.letOp (n := 406) (.out 0x10a51e (movR64R64Effect 0x10a51e 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[218]
    (.letOp (n := 407) (.exec 0x10a51e (fun s => s.RIP = 0x10a51e) (movR64R64Effect 0x10a51e 1 14) (Reg.operands [.gpr 14] [])) #v[218]
    (b_l10a26a_10)))))))))))))))))))))))))))))))

def bytes_l10a26a_9 : List UInt8 :=
  [0x88, 0x57, 0x24, 0x40, 0x88, 0x77, 0x25, 0x48, 0x89, 0xD6, 0x48, 0xC1, 0xEE, 0x20, 0x40, 0x88,
    0x77, 0x26, 0x48, 0x89, 0xD6, 0x48, 0xC1, 0xEE, 0x30, 0x40, 0x88, 0x77, 0x27, 0x48, 0x89, 0xCE,
    0x88, 0x6F, 0x28, 0xC1, 0xE9, 0x18, 0x49, 0xC1, 0xE8, 0x28, 0x48, 0xC1, 0xEE, 0x38, 0x88, 0x4F,
    0x29, 0x49, 0x89, 0xD2, 0x44, 0x88, 0x47, 0x2A, 0x49, 0x89, 0xD0, 0x40, 0x88, 0x77, 0x2B, 0x88,
    0x77, 0x2C, 0x4C, 0x89, 0xF1] ++ bytes_l10a26a_10

theorem code_l10a26a_9 : ∀ x ∈ codeRange 0x10a4dc bytes_l10a26a_9, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa4dc 69 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a26a_10

def b_l10a26a_8 : Block Op Label signature Reg.count 344 :=
  .letOp (n := 344) (.out 0x10a497 (xorR64R64Effect 0x10a497 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[342, 137]
    (.letOp (n := 345) (.exec 0x10a497 (fun s => s.RIP = 0x10a497) (xorR64R64Effect 0x10a497 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[342, 137]
    (.letOp (n := 346) (.out 0x10a49a (shrR32Effect 0x10a49a 4 8 24) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[330]
    (.letOp (n := 347) (.exec 0x10a49a (fun s => s.RIP = 0x10a49a) (shrR32Effect 0x10a49a 4 8 24) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[330]
    (.letOp (n := 348) (.exec 0x10a49e (StorePre 0x10a49e 4 (fun s => AddrMode.addr (.base 7 (.d8 0x1d)) s (0x10a49e + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a49e 4 8 (.base 7 (.d8 0x1d))) (Reg.operands [.gpr 8, .gpr 7] [])) #v[346, 7]
    (.letOp (n := 349) (.out 0x10a4a2 (shrR64Effect 0x10a4a2 4 11 40) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[323]
    (.letOp (n := 350) (.exec 0x10a4a2 (fun s => s.RIP = 0x10a4a2) (shrR64Effect 0x10a4a2 4 11 40) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[323]
    (.letOp (n := 351) (.out 0x10a4a6 (shrR64Effect 0x10a4a6 4 10 56) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[326]
    (.letOp (n := 352) (.exec 0x10a4a6 (fun s => s.RIP = 0x10a4a6) (shrR64Effect 0x10a4a6 4 10 56) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[326]
    (.letOp (n := 353) (.exec 0x10a4aa (StorePre 0x10a4aa 4 (fun s => AddrMode.addr (.base 7 (.d8 0x1e)) s (0x10a4aa + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a4aa 4 11 (.base 7 (.d8 0x1e))) (Reg.operands [.gpr 11, .gpr 7] [])) #v[349, 7]
    (.letOp (n := 354) (.out 0x10a4ae (movR32R32Effect 0x10a4ae 2 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 1] []) (.reg (.gpr 6))) #v[344]
    (.letOp (n := 355) (.exec 0x10a4ae (fun s => s.RIP = 0x10a4ae) (movR32R32Effect 0x10a4ae 2 6 1) (Reg.operands [.gpr 1] [])) #v[344]
    (.letOp (n := 356) (.out 0x10a4b0 (shrR32Effect 0x10a4b0 3 6 16) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[354]
    (.letOp (n := 357) (.exec 0x10a4b0 (fun s => s.RIP = 0x10a4b0) (shrR32Effect 0x10a4b0 3 6 16) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[354]
    (.letOp (n := 358) (.exec 0x10a4b3 (StorePre 0x10a4b3 4 (fun s => AddrMode.addr (.base 7 (.d8 0x1f)) s (0x10a4b3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a4b3 4 10 (.base 7 (.d8 0x1f))) (Reg.operands [.gpr 10, .gpr 7] [])) #v[351, 7]
    (.letOp (n := 359) (.out 0x10a4b7 (movR64R64Effect 0x10a4b7 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 1] []) (.reg (.gpr 8))) #v[344]
    (.letOp (n := 360) (.exec 0x10a4b7 (fun s => s.RIP = 0x10a4b7) (movR64R64Effect 0x10a4b7 8 1) (Reg.operands [.gpr 1] [])) #v[344]
    (.letOp (n := 361) (.out 0x10a4ba (shrR64Effect 0x10a4ba 4 8 32) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[359]
    (.letOp (n := 362) (.exec 0x10a4ba (fun s => s.RIP = 0x10a4ba) (shrR64Effect 0x10a4ba 4 8 32) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[359]
    (.letOp (n := 363) (.exec 0x10a4be (StorePre 0x10a4be 3 (fun s => AddrMode.addr (.base 7 (.d8 0x20)) s (0x10a4be + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a4be 3 1 (.base 7 (.d8 0x20))) (Reg.operands [.gpr 1, .gpr 7] [])) #v[344, 7]
    (.letOp (n := 364) (.exec 0x10a4c1 (StorePre 0x10a4c1 4 (fun s => AddrMode.addr (.base 7 (.d8 0x21)) s (0x10a4c1 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a4c1 4 6 (.base 7 (.d8 0x21))) (Reg.operands [.gpr 6, .gpr 7] [])) #v[356, 7]
    (.letOp (n := 365) (.out 0x10a4c5 (movR64R64Effect 0x10a4c5 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 1] []) (.reg (.gpr 6))) #v[344]
    (.letOp (n := 366) (.exec 0x10a4c5 (fun s => s.RIP = 0x10a4c5) (movR64R64Effect 0x10a4c5 6 1) (Reg.operands [.gpr 1] [])) #v[344]
    (.letOp (n := 367) (.out 0x10a4c8 (shrR64Effect 0x10a4c8 4 6 48) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[365]
    (.letOp (n := 368) (.exec 0x10a4c8 (fun s => s.RIP = 0x10a4c8) (shrR64Effect 0x10a4c8 4 6 48) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[365]
    (.letOp (n := 369) (.exec 0x10a4cc (StorePre 0x10a4cc 4 (fun s => AddrMode.addr (.base 7 (.d8 0x22)) s (0x10a4cc + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a4cc 4 8 (.base 7 (.d8 0x22))) (Reg.operands [.gpr 8, .gpr 7] [])) #v[361, 7]
    (.letOp (n := 370) (.out 0x10a4d0 (movR64R64Effect 0x10a4d0 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 1] []) (.reg (.gpr 8))) #v[344]
    (.letOp (n := 371) (.exec 0x10a4d0 (fun s => s.RIP = 0x10a4d0) (movR64R64Effect 0x10a4d0 8 1) (Reg.operands [.gpr 1] [])) #v[344]
    (.letOp (n := 372) (.exec 0x10a4d3 (StorePre 0x10a4d3 4 (fun s => AddrMode.addr (.base 7 (.d8 0x23)) s (0x10a4d3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a4d3 4 6 (.base 7 (.d8 0x23))) (Reg.operands [.gpr 6, .gpr 7] [])) #v[367, 7]
    (.letOp (n := 373) (.out 0x10a4d7 (movR32R32Effect 0x10a4d7 2 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[340]
    (.letOp (n := 374) (.exec 0x10a4d7 (fun s => s.RIP = 0x10a4d7) (movR32R32Effect 0x10a4d7 2 6 2) (Reg.operands [.gpr 2] [])) #v[340]
    (.letOp (n := 375) (.out 0x10a4d9 (shrR32Effect 0x10a4d9 3 6 16) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[373]
    (.letOp (n := 376) (.exec 0x10a4d9 (fun s => s.RIP = 0x10a4d9) (shrR32Effect 0x10a4d9 3 6 16) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[373]
    (b_l10a26a_9)))))))))))))))))))))))))))))))))

def bytes_l10a26a_8 : List UInt8 :=
  [0x48, 0x31, 0xF1, 0x41, 0xC1, 0xE8, 0x18, 0x44, 0x88, 0x47, 0x1D, 0x49, 0xC1, 0xEB, 0x28, 0x49,
    0xC1, 0xEA, 0x38, 0x44, 0x88, 0x5F, 0x1E, 0x89, 0xCE, 0xC1, 0xEE, 0x10, 0x44, 0x88, 0x57, 0x1F,
    0x49, 0x89, 0xC8, 0x49, 0xC1, 0xE8, 0x20, 0x88, 0x4F, 0x20, 0x40, 0x88, 0x77, 0x21, 0x48, 0x89,
    0xCE, 0x48, 0xC1, 0xEE, 0x30, 0x44, 0x88, 0x47, 0x22, 0x49, 0x89, 0xC8, 0x40, 0x88, 0x77, 0x23,
    0x89, 0xD6, 0xC1, 0xEE, 0x10] ++ bytes_l10a26a_9

theorem code_l10a26a_8 : ∀ x ∈ codeRange 0x10a497 bytes_l10a26a_8, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa497 69 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a26a_9

def b_l10a26a_7 : Block Op Label signature Reg.count 310 :=
  .letOp (n := 310) (.exec 0x10a452 (StorePre 0x10a452 4 (fun s => AddrMode.addr (.base 7 (.d8 0x17)) s (0x10a452 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a452 4 8 (.base 7 (.d8 0x17))) (Reg.operands [.gpr 8, .gpr 7] [])) #v[308, 7]
    (.letOp (n := 311) (.out 0x10a456 (movR64R64Effect 0x10a456 8 3) (EffectPart.reads (.reg (.gpr 8)) [.gpr 3] []) (.reg (.gpr 8))) #v[266]
    (.letOp (n := 312) (.exec 0x10a456 (fun s => s.RIP = 0x10a456) (movR64R64Effect 0x10a456 8 3) (Reg.operands [.gpr 3] [])) #v[266]
    (.letOp (n := 313) (.exec 0x10a459 (StorePre 0x10a459 3 (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x10a459 + BitVec.ofNat 64 3)) 1) (movM8R8NoRexEffect 0x10a459 3 7 (.base 7 (.d8 0x18))) (Reg.operands [.gpr 3, .gpr 7] [])) #v[266, 7]
    (.letOp (n := 314) (.out 0x10a45c (movR32R32Effect 0x10a45c 3 11 3) (EffectPart.reads (.reg (.gpr 11)) [.gpr 3] []) (.reg (.gpr 11))) #v[266]
    (.letOp (n := 315) (.exec 0x10a45c (fun s => s.RIP = 0x10a45c) (movR32R32Effect 0x10a45c 3 11 3) (Reg.operands [.gpr 3] [])) #v[266]
    (.letOp (n := 316) (.out 0x10a45f (shrR32Effect 0x10a45f 4 11 24) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[314]
    (.letOp (n := 317) (.exec 0x10a45f (fun s => s.RIP = 0x10a45f) (shrR32Effect 0x10a45f 4 11 24) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[314]
    (.letOp (n := 318) (.out 0x10a463 (shrR64Effect 0x10a463 4 10 40) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[292]
    (.letOp (n := 319) (.exec 0x10a463 (fun s => s.RIP = 0x10a463) (shrR64Effect 0x10a463 4 10 40) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[292]
    (.letOp (n := 320) (.out 0x10a467 (shrR64Effect 0x10a467 4 8 56) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[311]
    (.letOp (n := 321) (.exec 0x10a467 (fun s => s.RIP = 0x10a467) (shrR64Effect 0x10a467 4 8 56) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[311]
    (.letOp (n := 322) (.exec 0x10a46b (StorePre 0x10a46b 4 (fun s => AddrMode.addr (.base 7 (.d8 0x19)) s (0x10a46b + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a46b 4 11 (.base 7 (.d8 0x19))) (Reg.operands [.gpr 11, .gpr 7] [])) #v[316, 7]
    (.letOp (n := 323) (.out 0x10a46f (movR64R64Effect 0x10a46f 11 1) (EffectPart.reads (.reg (.gpr 11)) [.gpr 1] []) (.reg (.gpr 11))) #v[262]
    (.letOp (n := 324) (.exec 0x10a46f (fun s => s.RIP = 0x10a46f) (movR64R64Effect 0x10a46f 11 1) (Reg.operands [.gpr 1] [])) #v[262]
    (.letOp (n := 325) (.exec 0x10a472 (StorePre 0x10a472 4 (fun s => AddrMode.addr (.base 7 (.d8 0x1a)) s (0x10a472 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a472 4 10 (.base 7 (.d8 0x1a))) (Reg.operands [.gpr 10, .gpr 7] [])) #v[318, 7]
    (.letOp (n := 326) (.out 0x10a476 (movR64R64Effect 0x10a476 10 1) (EffectPart.reads (.reg (.gpr 10)) [.gpr 1] []) (.reg (.gpr 10))) #v[262]
    (.letOp (n := 327) (.exec 0x10a476 (fun s => s.RIP = 0x10a476) (movR64R64Effect 0x10a476 10 1) (Reg.operands [.gpr 1] [])) #v[262]
    (.letOp (n := 328) (.exec 0x10a479 (StorePre 0x10a479 4 (fun s => AddrMode.addr (.base 7 (.d8 0x1b)) s (0x10a479 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a479 4 8 (.base 7 (.d8 0x1b))) (Reg.operands [.gpr 8, .gpr 7] [])) #v[320, 7]
    (.letOp (n := 329) (.exec 0x10a47d (StorePre 0x10a47d 3 (fun s => AddrMode.addr (.base 7 (.d8 0x1c)) s (0x10a47d + BitVec.ofNat 64 3)) 1) (movM8R8NoRexEffect 0x10a47d 3 5 (.base 7 (.d8 0x1c))) (Reg.operands [.gpr 1, .gpr 7] [])) #v[262, 7]
    (.letOp (n := 330) (.out 0x10a480 (movR32R32Effect 0x10a480 3 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 1] []) (.reg (.gpr 8))) #v[262]
    (.letOp (n := 331) (.exec 0x10a480 (fun s => s.RIP = 0x10a480) (movR32R32Effect 0x10a480 3 8 1) (Reg.operands [.gpr 1] [])) #v[262]
    (.letOp (n := 332) (.out 0x10a483 (movR64R64Effect 0x10a483 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[137]
    (.letOp (n := 333) (.exec 0x10a483 (fun s => s.RIP = 0x10a483) (movR64R64Effect 0x10a483 1 6) (Reg.operands [.gpr 6] [])) #v[137]
    (.letOp (n := 334) (.out 0x10a486 (shrR64Effect 0x10a486 4 1 4) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[332]
    (.letOp (n := 335) (.exec 0x10a486 (fun s => s.RIP = 0x10a486) (shrR64Effect 0x10a486 4 1 4) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[332]
    (.letOp (n := 336) (.out 0x10a48a (xorR64R64Effect 0x10a48a 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[334, 151]
    (.letOp (n := 337) (.exec 0x10a48a (fun s => s.RIP = 0x10a48a) (xorR64R64Effect 0x10a48a 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[334, 151]
    (.letOp (n := 338) (.out 0x10a48d (andR64R64Effect 0x10a48d 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 9] []) (.reg (.gpr 1))) #v[336, 163]
    (.letOp (n := 339) (.exec 0x10a48d (fun s => s.RIP = 0x10a48d) (andR64R64Effect 0x10a48d 1 9) (Reg.operands [.gpr 1, .gpr 9] [])) #v[336, 163]
    (.letOp (n := 340) (.out 0x10a490 (xorR64R64Effect 0x10a490 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[151, 338]
    (.letOp (n := 341) (.exec 0x10a490 (fun s => s.RIP = 0x10a490) (xorR64R64Effect 0x10a490 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[151, 338]
    (.letOp (n := 342) (.out 0x10a493 (shlR64Effect 0x10a493 4 1 4) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[338]
    (.letOp (n := 343) (.exec 0x10a493 (fun s => s.RIP = 0x10a493) (shlR64Effect 0x10a493 4 1 4) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[338]
    (b_l10a26a_8))))))))))))))))))))))))))))))))))

def bytes_l10a26a_7 : List UInt8 :=
  [0x44, 0x88, 0x47, 0x17, 0x49, 0x89, 0xD8, 0x88, 0x7F, 0x18, 0x41, 0x89, 0xDB, 0x41, 0xC1, 0xEB,
    0x18, 0x49, 0xC1, 0xEA, 0x28, 0x49, 0xC1, 0xE8, 0x38, 0x44, 0x88, 0x5F, 0x19, 0x49, 0x89, 0xCB,
    0x44, 0x88, 0x57, 0x1A, 0x49, 0x89, 0xCA, 0x44, 0x88, 0x47, 0x1B, 0x88, 0x6F, 0x1C, 0x41, 0x89,
    0xC8, 0x48, 0x89, 0xF1, 0x48, 0xC1, 0xE9, 0x04, 0x48, 0x31, 0xD1, 0x4C, 0x21, 0xC9, 0x48, 0x31,
    0xCA, 0x48, 0xC1, 0xE1, 0x04] ++ bytes_l10a26a_8

theorem code_l10a26a_7 : ∀ x ∈ codeRange 0x10a452 bytes_l10a26a_7, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa452 69 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a26a_8

def b_l10a26a_6 : Block Op Label signature Reg.count 278 :=
  .letOp (n := 278) (.out 0x10a40a (shrR32Effect 0x10a40a 4 8 16) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[276]
    (.letOp (n := 279) (.exec 0x10a40a (fun s => s.RIP = 0x10a40a) (shrR32Effect 0x10a40a 4 8 16) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[276]
    (.letOp (n := 280) (.exec 0x10a40e (StorePre 0x10a40e 4 (fun s => AddrMode.addr (.base 7 (.d8 0xf)) s (0x10a40e + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a40e 4 12 (.base 7 (.d8 0xf))) (Reg.operands [.gpr 12, .gpr 7] [])) #v[273, 7]
    (.letOp (n := 281) (.out 0x10a412 (movR64R64Effect 0x10a412 10 3) (EffectPart.reads (.reg (.gpr 10)) [.gpr 3] []) (.reg (.gpr 10))) #v[266]
    (.letOp (n := 282) (.exec 0x10a412 (fun s => s.RIP = 0x10a412) (movR64R64Effect 0x10a412 10 3) (Reg.operands [.gpr 3] [])) #v[266]
    (.letOp (n := 283) (.out 0x10a415 (shrR64Effect 0x10a415 4 10 32) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[281]
    (.letOp (n := 284) (.exec 0x10a415 (fun s => s.RIP = 0x10a415) (shrR64Effect 0x10a415 4 10 32) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[281]
    (.letOp (n := 285) (.exec 0x10a419 (StorePre 0x10a419 3 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x10a419 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a419 3 3 (.base 7 (.d8 0x10))) (Reg.operands [.gpr 3, .gpr 7] [])) #v[266, 7]
    (.letOp (n := 286) (.exec 0x10a41c (StorePre 0x10a41c 4 (fun s => AddrMode.addr (.base 7 (.d8 0x11)) s (0x10a41c + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a41c 4 8 (.base 7 (.d8 0x11))) (Reg.operands [.gpr 8, .gpr 7] [])) #v[278, 7]
    (.letOp (n := 287) (.out 0x10a420 (movR64R64Effect 0x10a420 8 3) (EffectPart.reads (.reg (.gpr 8)) [.gpr 3] []) (.reg (.gpr 8))) #v[266]
    (.letOp (n := 288) (.exec 0x10a420 (fun s => s.RIP = 0x10a420) (movR64R64Effect 0x10a420 8 3) (Reg.operands [.gpr 3] [])) #v[266]
    (.letOp (n := 289) (.out 0x10a423 (shrR64Effect 0x10a423 4 8 48) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[287]
    (.letOp (n := 290) (.exec 0x10a423 (fun s => s.RIP = 0x10a423) (shrR64Effect 0x10a423 4 8 48) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[287]
    (.letOp (n := 291) (.exec 0x10a427 (StorePre 0x10a427 4 (fun s => AddrMode.addr (.base 7 (.d8 0x12)) s (0x10a427 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a427 4 10 (.base 7 (.d8 0x12))) (Reg.operands [.gpr 10, .gpr 7] [])) #v[283, 7]
    (.letOp (n := 292) (.out 0x10a42b (movR64R64Effect 0x10a42b 10 3) (EffectPart.reads (.reg (.gpr 10)) [.gpr 3] []) (.reg (.gpr 10))) #v[266]
    (.letOp (n := 293) (.exec 0x10a42b (fun s => s.RIP = 0x10a42b) (movR64R64Effect 0x10a42b 10 3) (Reg.operands [.gpr 3] [])) #v[266]
    (.letOp (n := 294) (.exec 0x10a42e (StorePre 0x10a42e 4 (fun s => AddrMode.addr (.base 7 (.d8 0x13)) s (0x10a42e + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a42e 4 8 (.base 7 (.d8 0x13))) (Reg.operands [.gpr 8, .gpr 7] [])) #v[289, 7]
    (.letOp (n := 295) (.out 0x10a432 (movR32R32Effect 0x10a432 3 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 1] []) (.reg (.gpr 8))) #v[262]
    (.letOp (n := 296) (.exec 0x10a432 (fun s => s.RIP = 0x10a432) (movR32R32Effect 0x10a432 3 8 1) (Reg.operands [.gpr 1] [])) #v[262]
    (.letOp (n := 297) (.out 0x10a435 (shrR32Effect 0x10a435 4 8 16) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[295]
    (.letOp (n := 298) (.exec 0x10a435 (fun s => s.RIP = 0x10a435) (shrR32Effect 0x10a435 4 8 16) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[295]
    (.letOp (n := 299) (.exec 0x10a439 (StorePre 0x10a439 3 (fun s => AddrMode.addr (.base 7 (.d8 0x14)) s (0x10a439 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a439 3 1 (.base 7 (.d8 0x14))) (Reg.operands [.gpr 1, .gpr 7] [])) #v[262, 7]
    (.letOp (n := 300) (.exec 0x10a43c (StorePre 0x10a43c 4 (fun s => AddrMode.addr (.base 7 (.d8 0x15)) s (0x10a43c + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a43c 4 8 (.base 7 (.d8 0x15))) (Reg.operands [.gpr 8, .gpr 7] [])) #v[297, 7]
    (.letOp (n := 301) (.out 0x10a440 (movR64R64Effect 0x10a440 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 1] []) (.reg (.gpr 8))) #v[262]
    (.letOp (n := 302) (.exec 0x10a440 (fun s => s.RIP = 0x10a440) (movR64R64Effect 0x10a440 8 1) (Reg.operands [.gpr 1] [])) #v[262]
    (.letOp (n := 303) (.out 0x10a443 (shrR64Effect 0x10a443 4 8 32) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[301]
    (.letOp (n := 304) (.exec 0x10a443 (fun s => s.RIP = 0x10a443) (shrR64Effect 0x10a443 4 8 32) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[301]
    (.letOp (n := 305) (.exec 0x10a447 (StorePre 0x10a447 4 (fun s => AddrMode.addr (.base 7 (.d8 0x16)) s (0x10a447 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a447 4 8 (.base 7 (.d8 0x16))) (Reg.operands [.gpr 8, .gpr 7] [])) #v[303, 7]
    (.letOp (n := 306) (.out 0x10a44b (movR64R64Effect 0x10a44b 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 1] []) (.reg (.gpr 8))) #v[262]
    (.letOp (n := 307) (.exec 0x10a44b (fun s => s.RIP = 0x10a44b) (movR64R64Effect 0x10a44b 8 1) (Reg.operands [.gpr 1] [])) #v[262]
    (.letOp (n := 308) (.out 0x10a44e (shrR64Effect 0x10a44e 4 8 48) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[306]
    (.letOp (n := 309) (.exec 0x10a44e (fun s => s.RIP = 0x10a44e) (shrR64Effect 0x10a44e 4 8 48) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[306]
    (b_l10a26a_7))))))))))))))))))))))))))))))))

def bytes_l10a26a_6 : List UInt8 :=
  [0x41, 0xC1, 0xE8, 0x10, 0x44, 0x88, 0x67, 0x0F, 0x49, 0x89, 0xDA, 0x49, 0xC1, 0xEA, 0x20, 0x88,
    0x5F, 0x10, 0x44, 0x88, 0x47, 0x11, 0x49, 0x89, 0xD8, 0x49, 0xC1, 0xE8, 0x30, 0x44, 0x88, 0x57,
    0x12, 0x49, 0x89, 0xDA, 0x44, 0x88, 0x47, 0x13, 0x41, 0x89, 0xC8, 0x41, 0xC1, 0xE8, 0x10, 0x88,
    0x4F, 0x14, 0x44, 0x88, 0x47, 0x15, 0x49, 0x89, 0xC8, 0x49, 0xC1, 0xE8, 0x20, 0x44, 0x88, 0x47,
    0x16, 0x49, 0x89, 0xC8, 0x49, 0xC1, 0xE8, 0x30] ++ bytes_l10a26a_7

theorem code_l10a26a_6 : ∀ x ∈ codeRange 0x10a40a bytes_l10a26a_6, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa40a 72 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a26a_7

def b_l10a26a_5 : Block Op Label signature Reg.count 240 :=
  .letOp (n := 240) (.out 0x10a3c6 (movR64R64Effect 0x10a3c6 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 8] []) (.reg (.gpr 1))) #v[107]
    (.letOp (n := 241) (.exec 0x10a3c6 (fun s => s.RIP = 0x10a3c6) (movR64R64Effect 0x10a3c6 1 8) (Reg.operands [.gpr 8] [])) #v[107]
    (.letOp (n := 242) (.out 0x10a3c9 (shrR64Effect 0x10a3c9 4 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[240]
    (.letOp (n := 243) (.exec 0x10a3c9 (fun s => s.RIP = 0x10a3c9) (shrR64Effect 0x10a3c9 4 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[240]
    (.letOp (n := 244) (.out 0x10a3cd (xorR64R64Effect 0x10a3cd 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[242, 121]
    (.letOp (n := 245) (.exec 0x10a3cd (fun s => s.RIP = 0x10a3cd) (xorR64R64Effect 0x10a3cd 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[242, 121]
    (.letOp (n := 246) (.out 0x10a3d0 (andR64R64Effect 0x10a3d0 1 11) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 11] []) (.reg (.gpr 1))) #v[244, 133]
    (.letOp (n := 247) (.exec 0x10a3d0 (fun s => s.RIP = 0x10a3d0) (andR64R64Effect 0x10a3d0 1 11) (Reg.operands [.gpr 1, .gpr 11] [])) #v[244, 133]
    (.letOp (n := 248) (.out 0x10a3d3 (xorR64R64Effect 0x10a3d3 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[121, 246]
    (.letOp (n := 249) (.exec 0x10a3d3 (fun s => s.RIP = 0x10a3d3) (xorR64R64Effect 0x10a3d3 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[121, 246]
    (.letOp (n := 250) (.out 0x10a3d6 (shlR64Effect 0x10a3d6 4 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[246]
    (.letOp (n := 251) (.exec 0x10a3d6 (fun s => s.RIP = 0x10a3d6) (shlR64Effect 0x10a3d6 4 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[246]
    (.letOp (n := 252) (.out 0x10a3da (xorR64R64Effect 0x10a3da 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8] []) (.reg (.gpr 1))) #v[250, 107]
    (.letOp (n := 253) (.exec 0x10a3da (fun s => s.RIP = 0x10a3da) (xorR64R64Effect 0x10a3da 1 8) (Reg.operands [.gpr 1, .gpr 8] [])) #v[250, 107]
    (.letOp (n := 254) (.out 0x10a3dd (movR64R64Effect 0x10a3dd 3 15) (EffectPart.reads (.reg (.gpr 3)) [.gpr 15] []) (.reg (.gpr 3))) #v[222]
    (.letOp (n := 255) (.exec 0x10a3dd (fun s => s.RIP = 0x10a3dd) (movR64R64Effect 0x10a3dd 3 15) (Reg.operands [.gpr 15] [])) #v[222]
    (.letOp (n := 256) (.out 0x10a3e0 (shrR64Effect 0x10a3e0 4 3 4) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[254]
    (.letOp (n := 257) (.exec 0x10a3e0 (fun s => s.RIP = 0x10a3e0) (shrR64Effect 0x10a3e0 4 3 4) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[254]
    (.letOp (n := 258) (.out 0x10a3e4 (xorR64R64Effect 0x10a3e4 3 1) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 1] []) (.reg (.gpr 3))) #v[256, 252]
    (.letOp (n := 259) (.exec 0x10a3e4 (fun s => s.RIP = 0x10a3e4) (xorR64R64Effect 0x10a3e4 3 1) (Reg.operands [.gpr 3, .gpr 1] [])) #v[256, 252]
    (.letOp (n := 260) (.out 0x10a3e7 (andR64R64Effect 0x10a3e7 3 9) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 9] []) (.reg (.gpr 3))) #v[258, 163]
    (.letOp (n := 261) (.exec 0x10a3e7 (fun s => s.RIP = 0x10a3e7) (andR64R64Effect 0x10a3e7 3 9) (Reg.operands [.gpr 3, .gpr 9] [])) #v[258, 163]
    (.letOp (n := 262) (.out 0x10a3ea (xorR64R64Effect 0x10a3ea 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 3] []) (.reg (.gpr 1))) #v[252, 260]
    (.letOp (n := 263) (.exec 0x10a3ea (fun s => s.RIP = 0x10a3ea) (xorR64R64Effect 0x10a3ea 1 3) (Reg.operands [.gpr 1, .gpr 3] [])) #v[252, 260]
    (.letOp (n := 264) (.out 0x10a3ed (shlR64Effect 0x10a3ed 4 3 4) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[260]
    (.letOp (n := 265) (.exec 0x10a3ed (fun s => s.RIP = 0x10a3ed) (shlR64Effect 0x10a3ed 4 3 4) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[260]
    (.letOp (n := 266) (.out 0x10a3f1 (xorR64R64Effect 0x10a3f1 3 15) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 15] []) (.reg (.gpr 3))) #v[264, 222]
    (.letOp (n := 267) (.exec 0x10a3f1 (fun s => s.RIP = 0x10a3f1) (xorR64R64Effect 0x10a3f1 3 15) (Reg.operands [.gpr 3, .gpr 15] [])) #v[264, 222]
    (.letOp (n := 268) (.out 0x10a3f4 (shrR32Effect 0x10a3f4 3 5 24) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[238]
    (.letOp (n := 269) (.exec 0x10a3f4 (fun s => s.RIP = 0x10a3f4) (shrR32Effect 0x10a3f4 3 5 24) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[238]
    (.letOp (n := 270) (.exec 0x10a3f7 (StorePre 0x10a3f7 4 (fun s => AddrMode.addr (.base 7 (.d8 0xd)) s (0x10a3f7 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a3f7 4 5 (.base 7 (.d8 0xd))) (Reg.operands [.gpr 5, .gpr 7] [])) #v[268, 7]
    (.letOp (n := 271) (.out 0x10a3fb (shrR64Effect 0x10a3fb 4 10 40) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[231]
    (.letOp (n := 272) (.exec 0x10a3fb (fun s => s.RIP = 0x10a3fb) (shrR64Effect 0x10a3fb 4 10 40) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[231]
    (.letOp (n := 273) (.out 0x10a3ff (shrR64Effect 0x10a3ff 4 12 56) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[234]
    (.letOp (n := 274) (.exec 0x10a3ff (fun s => s.RIP = 0x10a3ff) (shrR64Effect 0x10a3ff 4 12 56) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[234]
    (.letOp (n := 275) (.exec 0x10a403 (StorePre 0x10a403 4 (fun s => AddrMode.addr (.base 7 (.d8 0xe)) s (0x10a403 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a403 4 10 (.base 7 (.d8 0xe))) (Reg.operands [.gpr 10, .gpr 7] [])) #v[271, 7]
    (.letOp (n := 276) (.out 0x10a407 (movR32R32Effect 0x10a407 3 8 3) (EffectPart.reads (.reg (.gpr 8)) [.gpr 3] []) (.reg (.gpr 8))) #v[266]
    (.letOp (n := 277) (.exec 0x10a407 (fun s => s.RIP = 0x10a407) (movR32R32Effect 0x10a407 3 8 3) (Reg.operands [.gpr 3] [])) #v[266]
    (b_l10a26a_6))))))))))))))))))))))))))))))))))))))

def bytes_l10a26a_5 : List UInt8 :=
  [0x4C, 0x89, 0xC1, 0x48, 0xC1, 0xE9, 0x02, 0x48, 0x31, 0xC1, 0x4C, 0x21, 0xD9, 0x48, 0x31, 0xC8,
    0x48, 0xC1, 0xE1, 0x02, 0x4C, 0x31, 0xC1, 0x4C, 0x89, 0xFB, 0x48, 0xC1, 0xEB, 0x04, 0x48, 0x31,
    0xCB, 0x4C, 0x21, 0xCB, 0x48, 0x31, 0xD9, 0x48, 0xC1, 0xE3, 0x04, 0x4C, 0x31, 0xFB, 0xC1, 0xED,
    0x18, 0x40, 0x88, 0x6F, 0x0D, 0x49, 0xC1, 0xEA, 0x28, 0x49, 0xC1, 0xEC, 0x38, 0x44, 0x88, 0x57,
    0x0E, 0x41, 0x89, 0xD8] ++ bytes_l10a26a_6

theorem code_l10a26a_5 : ∀ x ∈ codeRange 0x10a3c6 bytes_l10a26a_5, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa3c6 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a26a_6

def b_l10a26a_4 : Block Op Label signature Reg.count 206 :=
  .letOp (n := 206) (.out 0x10a383 (shrR64Effect 0x10a383 4 15 48) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[204]
    (.letOp (n := 207) (.exec 0x10a383 (fun s => s.RIP = 0x10a383) (shrR64Effect 0x10a383 4 15 48) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[204]
    (.letOp (n := 208) (.exec 0x10a387 (StorePre 0x10a387 4 (fun s => AddrMode.addr (.base 7 (.d8 0x7)) s (0x10a387 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a387 4 15 (.base 7 (.d8 0x7))) (Reg.operands [.gpr 15, .gpr 7] [])) #v[206, 7]
    (.letOp (n := 209) (.exec 0x10a38b (StorePre 0x10a38b 3 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x10a38b + BitVec.ofNat 64 3)) 1) (movM8R8NoRexEffect 0x10a38b 3 5 (.base 7 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 7] [])) #v[171, 7]
    (.letOp (n := 210) (.out 0x10a38e (movR64R64Effect 0x10a38e 15 10) (EffectPart.reads (.reg (.gpr 15)) [.gpr 10] []) (.reg (.gpr 15))) #v[79]
    (.letOp (n := 211) (.exec 0x10a38e (fun s => s.RIP = 0x10a38e) (movR64R64Effect 0x10a38e 15 10) (Reg.operands [.gpr 10] [])) #v[79]
    (.letOp (n := 212) (.out 0x10a391 (shrR64Effect 0x10a391 4 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[210]
    (.letOp (n := 213) (.exec 0x10a391 (fun s => s.RIP = 0x10a391) (shrR64Effect 0x10a391 4 15 2) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[210]
    (.letOp (n := 214) (.out 0x10a395 (xorR64R64Effect 0x10a395 15 14) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 14] []) (.reg (.gpr 15))) #v[212, 93]
    (.letOp (n := 215) (.exec 0x10a395 (fun s => s.RIP = 0x10a395) (xorR64R64Effect 0x10a395 15 14) (Reg.operands [.gpr 15, .gpr 14] [])) #v[212, 93]
    (.letOp (n := 216) (.out 0x10a398 (andR64R64Effect 0x10a398 15 11) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 11] []) (.reg (.gpr 15))) #v[214, 133]
    (.letOp (n := 217) (.exec 0x10a398 (fun s => s.RIP = 0x10a398) (andR64R64Effect 0x10a398 15 11) (Reg.operands [.gpr 15, .gpr 11] [])) #v[214, 133]
    (.letOp (n := 218) (.out 0x10a39b (xorR64R64Effect 0x10a39b 14 15) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 15] []) (.reg (.gpr 14))) #v[93, 216]
    (.letOp (n := 219) (.exec 0x10a39b (fun s => s.RIP = 0x10a39b) (xorR64R64Effect 0x10a39b 14 15) (Reg.operands [.gpr 14, .gpr 15] [])) #v[93, 216]
    (.letOp (n := 220) (.out 0x10a39e (shlR64Effect 0x10a39e 4 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[216]
    (.letOp (n := 221) (.exec 0x10a39e (fun s => s.RIP = 0x10a39e) (shlR64Effect 0x10a39e 4 15 2) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[216]
    (.letOp (n := 222) (.out 0x10a3a2 (xorR64R64Effect 0x10a3a2 15 10) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 10] []) (.reg (.gpr 15))) #v[220, 79]
    (.letOp (n := 223) (.exec 0x10a3a2 (fun s => s.RIP = 0x10a3a2) (xorR64R64Effect 0x10a3a2 15 10) (Reg.operands [.gpr 15, .gpr 10] [])) #v[220, 79]
    (.letOp (n := 224) (.out 0x10a3a5 (shrR32Effect 0x10a3a5 3 1 24) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[171]
    (.letOp (n := 225) (.exec 0x10a3a5 (fun s => s.RIP = 0x10a3a5) (shrR32Effect 0x10a3a5 3 1 24) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[171]
    (.letOp (n := 226) (.out 0x10a3a8 (shrR64Effect 0x10a3a8 4 13 40) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[187]
    (.letOp (n := 227) (.exec 0x10a3a8 (fun s => s.RIP = 0x10a3a8) (shrR64Effect 0x10a3a8 4 13 40) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[187]
    (.letOp (n := 228) (.out 0x10a3ac (shrR64Effect 0x10a3ac 4 5 56) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[190]
    (.letOp (n := 229) (.exec 0x10a3ac (fun s => s.RIP = 0x10a3ac) (shrR64Effect 0x10a3ac 4 5 56) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[190]
    (.letOp (n := 230) (.exec 0x10a3b0 (StorePre 0x10a3b0 3 (fun s => AddrMode.addr (.base 7 (.d8 0x9)) s (0x10a3b0 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a3b0 3 1 (.base 7 (.d8 0x9))) (Reg.operands [.gpr 1, .gpr 7] [])) #v[224, 7]
    (.letOp (n := 231) (.out 0x10a3b3 (movR64R64Effect 0x10a3b3 10 3) (EffectPart.reads (.reg (.gpr 10)) [.gpr 3] []) (.reg (.gpr 10))) #v[167]
    (.letOp (n := 232) (.exec 0x10a3b3 (fun s => s.RIP = 0x10a3b3) (movR64R64Effect 0x10a3b3 10 3) (Reg.operands [.gpr 3] [])) #v[167]
    (.letOp (n := 233) (.exec 0x10a3b6 (StorePre 0x10a3b6 4 (fun s => AddrMode.addr (.base 7 (.d8 0xa)) s (0x10a3b6 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a3b6 4 13 (.base 7 (.d8 0xa))) (Reg.operands [.gpr 13, .gpr 7] [])) #v[226, 7]
    (.letOp (n := 234) (.out 0x10a3ba (movR64R64Effect 0x10a3ba 12 3) (EffectPart.reads (.reg (.gpr 12)) [.gpr 3] []) (.reg (.gpr 12))) #v[167]
    (.letOp (n := 235) (.exec 0x10a3ba (fun s => s.RIP = 0x10a3ba) (movR64R64Effect 0x10a3ba 12 3) (Reg.operands [.gpr 3] [])) #v[167]
    (.letOp (n := 236) (.exec 0x10a3bd (StorePre 0x10a3bd 4 (fun s => AddrMode.addr (.base 7 (.d8 0xb)) s (0x10a3bd + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a3bd 4 5 (.base 7 (.d8 0xb))) (Reg.operands [.gpr 5, .gpr 7] [])) #v[228, 7]
    (.letOp (n := 237) (.exec 0x10a3c1 (StorePre 0x10a3c1 3 (fun s => AddrMode.addr (.base 7 (.d8 0xc)) s (0x10a3c1 + BitVec.ofNat 64 3)) 1) (movM8R8NoRexEffect 0x10a3c1 3 7 (.base 7 (.d8 0xc))) (Reg.operands [.gpr 3, .gpr 7] [])) #v[167, 7]
    (.letOp (n := 238) (.out 0x10a3c4 (movR32R32Effect 0x10a3c4 2 5 3) (EffectPart.reads (.reg (.gpr 5)) [.gpr 3] []) (.reg (.gpr 5))) #v[167]
    (.letOp (n := 239) (.exec 0x10a3c4 (fun s => s.RIP = 0x10a3c4) (movR32R32Effect 0x10a3c4 2 5 3) (Reg.operands [.gpr 3] [])) #v[167]
    (b_l10a26a_5))))))))))))))))))))))))))))))))))

def bytes_l10a26a_4 : List UInt8 :=
  [0x49, 0xC1, 0xEF, 0x30, 0x44, 0x88, 0x7F, 0x07, 0x88, 0x6F, 0x08, 0x4D, 0x89, 0xD7, 0x49, 0xC1,
    0xEF, 0x02, 0x4D, 0x31, 0xF7, 0x4D, 0x21, 0xDF, 0x4D, 0x31, 0xFE, 0x49, 0xC1, 0xE7, 0x02, 0x4D,
    0x31, 0xD7, 0xC1, 0xE9, 0x18, 0x49, 0xC1, 0xED, 0x28, 0x48, 0xC1, 0xED, 0x38, 0x88, 0x4F, 0x09,
    0x49, 0x89, 0xDA, 0x44, 0x88, 0x6F, 0x0A, 0x49, 0x89, 0xDC, 0x40, 0x88, 0x6F, 0x0B, 0x88, 0x7F,
    0x0C, 0x89, 0xDD] ++ bytes_l10a26a_5

theorem code_l10a26a_4 : ∀ x ∈ codeRange 0x10a383 bytes_l10a26a_4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa383 67 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a26a_5

def b_l10a26a_3 : Block Op Label signature Reg.count 173 :=
  .letOp (n := 173) (.out 0x10a340 (movR32R32Effect 0x10a340 2 5 1) (EffectPart.reads (.reg (.gpr 5)) [.gpr 1] []) (.reg (.gpr 5))) #v[171]
    (.letOp (n := 174) (.exec 0x10a340 (fun s => s.RIP = 0x10a340) (movR32R32Effect 0x10a340 2 5 1) (Reg.operands [.gpr 1] [])) #v[171]
    (.letOp (n := 175) (.out 0x10a342 (shrR32Effect 0x10a342 3 5 16) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[173]
    (.letOp (n := 176) (.exec 0x10a342 (fun s => s.RIP = 0x10a342) (shrR32Effect 0x10a342 3 5 16) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[173]
    (.letOp (n := 177) (.out 0x10a345 (movR64R64Effect 0x10a345 15 1) (EffectPart.reads (.reg (.gpr 15)) [.gpr 1] []) (.reg (.gpr 15))) #v[171]
    (.letOp (n := 178) (.exec 0x10a345 (fun s => s.RIP = 0x10a345) (movR64R64Effect 0x10a345 15 1) (Reg.operands [.gpr 1] [])) #v[171]
    (.letOp (n := 179) (.out 0x10a348 (shrR64Effect 0x10a348 4 15 32) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[177]
    (.letOp (n := 180) (.exec 0x10a348 (fun s => s.RIP = 0x10a348) (shrR64Effect 0x10a348 4 15 32) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[177]
    (.letOp (n := 181) (.out 0x10a34c (movR64R64Effect 0x10a34c 12 1) (EffectPart.reads (.reg (.gpr 12)) [.gpr 1] []) (.reg (.gpr 12))) #v[171]
    (.letOp (n := 182) (.exec 0x10a34c (fun s => s.RIP = 0x10a34c) (movR64R64Effect 0x10a34c 12 1) (Reg.operands [.gpr 1] [])) #v[171]
    (.letOp (n := 183) (.out 0x10a34f (shrR64Effect 0x10a34f 4 12 48) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[181]
    (.letOp (n := 184) (.exec 0x10a34f (fun s => s.RIP = 0x10a34f) (shrR64Effect 0x10a34f 4 12 48) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[181]
    (.letOp (n := 185) (.exec 0x10a353 (StorePre 0x10a353 2 (fun s => AddrMode.addr (.base 7 .none) s (0x10a353 + BitVec.ofNat 64 2)) 1) (movM8R8Effect 0x10a353 2 1 (.base 7 .none)) (Reg.operands [.gpr 1, .gpr 7] [])) #v[171, 7]
    (.letOp (n := 186) (.exec 0x10a355 (StorePre 0x10a355 4 (fun s => AddrMode.addr (.base 7 (.d8 0x1)) s (0x10a355 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a355 4 5 (.base 7 (.d8 0x1))) (Reg.operands [.gpr 5, .gpr 7] [])) #v[175, 7]
    (.letOp (n := 187) (.out 0x10a359 (movR64R64Effect 0x10a359 13 1) (EffectPart.reads (.reg (.gpr 13)) [.gpr 1] []) (.reg (.gpr 13))) #v[171]
    (.letOp (n := 188) (.exec 0x10a359 (fun s => s.RIP = 0x10a359) (movR64R64Effect 0x10a359 13 1) (Reg.operands [.gpr 1] [])) #v[171]
    (.letOp (n := 189) (.exec 0x10a35c (StorePre 0x10a35c 4 (fun s => AddrMode.addr (.base 7 (.d8 0x2)) s (0x10a35c + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a35c 4 15 (.base 7 (.d8 0x2))) (Reg.operands [.gpr 15, .gpr 7] [])) #v[179, 7]
    (.letOp (n := 190) (.out 0x10a360 (movR64R64Effect 0x10a360 5 1) (EffectPart.reads (.reg (.gpr 5)) [.gpr 1] []) (.reg (.gpr 5))) #v[171]
    (.letOp (n := 191) (.exec 0x10a360 (fun s => s.RIP = 0x10a360) (movR64R64Effect 0x10a360 5 1) (Reg.operands [.gpr 1] [])) #v[171]
    (.letOp (n := 192) (.exec 0x10a363 (StorePre 0x10a363 4 (fun s => AddrMode.addr (.base 7 (.d8 0x3)) s (0x10a363 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a363 4 12 (.base 7 (.d8 0x3))) (Reg.operands [.gpr 12, .gpr 7] [])) #v[183, 7]
    (.letOp (n := 193) (.out 0x10a367 (movR32R32Effect 0x10a367 3 15 3) (EffectPart.reads (.reg (.gpr 15)) [.gpr 3] []) (.reg (.gpr 15))) #v[167]
    (.letOp (n := 194) (.exec 0x10a367 (fun s => s.RIP = 0x10a367) (movR32R32Effect 0x10a367 3 15 3) (Reg.operands [.gpr 3] [])) #v[167]
    (.letOp (n := 195) (.out 0x10a36a (shrR32Effect 0x10a36a 4 15 16) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[193]
    (.letOp (n := 196) (.exec 0x10a36a (fun s => s.RIP = 0x10a36a) (shrR32Effect 0x10a36a 4 15 16) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[193]
    (.letOp (n := 197) (.exec 0x10a36e (StorePre 0x10a36e 3 (fun s => AddrMode.addr (.base 7 (.d8 0x4)) s (0x10a36e + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a36e 3 3 (.base 7 (.d8 0x4))) (Reg.operands [.gpr 3, .gpr 7] [])) #v[167, 7]
    (.letOp (n := 198) (.exec 0x10a371 (StorePre 0x10a371 4 (fun s => AddrMode.addr (.base 7 (.d8 0x5)) s (0x10a371 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a371 4 15 (.base 7 (.d8 0x5))) (Reg.operands [.gpr 15, .gpr 7] [])) #v[195, 7]
    (.letOp (n := 199) (.out 0x10a375 (movR64R64Effect 0x10a375 15 3) (EffectPart.reads (.reg (.gpr 15)) [.gpr 3] []) (.reg (.gpr 15))) #v[167]
    (.letOp (n := 200) (.exec 0x10a375 (fun s => s.RIP = 0x10a375) (movR64R64Effect 0x10a375 15 3) (Reg.operands [.gpr 3] [])) #v[167]
    (.letOp (n := 201) (.out 0x10a378 (shrR64Effect 0x10a378 4 15 32) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[199]
    (.letOp (n := 202) (.exec 0x10a378 (fun s => s.RIP = 0x10a378) (shrR64Effect 0x10a378 4 15 32) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[199]
    (.letOp (n := 203) (.exec 0x10a37c (StorePre 0x10a37c 4 (fun s => AddrMode.addr (.base 7 (.d8 0x6)) s (0x10a37c + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a37c 4 15 (.base 7 (.d8 0x6))) (Reg.operands [.gpr 15, .gpr 7] [])) #v[201, 7]
    (.letOp (n := 204) (.out 0x10a380 (movR64R64Effect 0x10a380 15 3) (EffectPart.reads (.reg (.gpr 15)) [.gpr 3] []) (.reg (.gpr 15))) #v[167]
    (.letOp (n := 205) (.exec 0x10a380 (fun s => s.RIP = 0x10a380) (movR64R64Effect 0x10a380 15 3) (Reg.operands [.gpr 3] [])) #v[167]
    (b_l10a26a_4)))))))))))))))))))))))))))))))))

def bytes_l10a26a_3 : List UInt8 :=
  [0x89, 0xCD, 0xC1, 0xED, 0x10, 0x49, 0x89, 0xCF, 0x49, 0xC1, 0xEF, 0x20, 0x49, 0x89, 0xCC, 0x49,
    0xC1, 0xEC, 0x30, 0x88, 0x0F, 0x40, 0x88, 0x6F, 0x01, 0x49, 0x89, 0xCD, 0x44, 0x88, 0x7F, 0x02,
    0x48, 0x89, 0xCD, 0x44, 0x88, 0x67, 0x03, 0x41, 0x89, 0xDF, 0x41, 0xC1, 0xEF, 0x10, 0x88, 0x5F,
    0x04, 0x44, 0x88, 0x7F, 0x05, 0x49, 0x89, 0xDF, 0x49, 0xC1, 0xEF, 0x20, 0x44, 0x88, 0x7F, 0x06,
    0x49, 0x89, 0xDF] ++ bytes_l10a26a_4

theorem code_l10a26a_3 : ∀ x ∈ codeRange 0x10a340 bytes_l10a26a_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa340 67 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a26a_4

def b_l10a26a_2 : Block Op Label signature Reg.count 133 :=
  .letOp (n := 133) (.out 0x10a2f1 (movR64Imm64Effect 0x10a2f1 11 0x3333333333333333) (EffectPart.reads (.reg (.gpr 11)) [] []) (.reg (.gpr 11))) #v[]
    (.letOp (n := 134) (.exec 0x10a2f1 (fun s => s.RIP = 0x10a2f1) (movR64Imm64Effect 0x10a2f1 11 0x3333333333333333) (Reg.operands [] [])) #v[]
    (.letOp (n := 135) (.out 0x10a2fb (andR64R64Effect 0x10a2fb 15 11) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 11] []) (.reg (.gpr 15))) #v[131, 133]
    (.letOp (n := 136) (.exec 0x10a2fb (fun s => s.RIP = 0x10a2fb) (andR64R64Effect 0x10a2fb 15 11) (Reg.operands [.gpr 15, .gpr 11] [])) #v[131, 133]
    (.letOp (n := 137) (.out 0x10a2fe (xorR64R64Effect 0x10a2fe 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 15] []) (.reg (.gpr 6))) #v[97, 135]
    (.letOp (n := 138) (.exec 0x10a2fe (fun s => s.RIP = 0x10a2fe) (xorR64R64Effect 0x10a2fe 6 15) (Reg.operands [.gpr 6, .gpr 15] [])) #v[97, 135]
    (.letOp (n := 139) (.out 0x10a301 (shlR64Effect 0x10a301 4 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[135]
    (.letOp (n := 140) (.exec 0x10a301 (fun s => s.RIP = 0x10a301) (shlR64Effect 0x10a301 4 15 2) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[135]
    (.letOp (n := 141) (.out 0x10a305 (xorR64R64Effect 0x10a305 15 1) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 1] []) (.reg (.gpr 15))) #v[139, 83]
    (.letOp (n := 142) (.exec 0x10a305 (fun s => s.RIP = 0x10a305) (xorR64R64Effect 0x10a305 15 1) (Reg.operands [.gpr 15, .gpr 1] [])) #v[139, 83]
    (.letOp (n := 143) (.out 0x10a308 (movR64R64Effect 0x10a308 3 9) (EffectPart.reads (.reg (.gpr 3)) [.gpr 9] []) (.reg (.gpr 3))) #v[111]
    (.letOp (n := 144) (.exec 0x10a308 (fun s => s.RIP = 0x10a308) (movR64R64Effect 0x10a308 3 9) (Reg.operands [.gpr 9] [])) #v[111]
    (.letOp (n := 145) (.out 0x10a30b (shrR64Effect 0x10a30b 4 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[143]
    (.letOp (n := 146) (.exec 0x10a30b (fun s => s.RIP = 0x10a30b) (shrR64Effect 0x10a30b 4 3 2) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[143]
    (.letOp (n := 147) (.out 0x10a30f (xorR64R64Effect 0x10a30f 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 2] []) (.reg (.gpr 3))) #v[145, 125]
    (.letOp (n := 148) (.exec 0x10a30f (fun s => s.RIP = 0x10a30f) (xorR64R64Effect 0x10a30f 3 2) (Reg.operands [.gpr 3, .gpr 2] [])) #v[145, 125]
    (.letOp (n := 149) (.out 0x10a312 (andR64R64Effect 0x10a312 3 11) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 11] []) (.reg (.gpr 3))) #v[147, 133]
    (.letOp (n := 150) (.exec 0x10a312 (fun s => s.RIP = 0x10a312) (andR64R64Effect 0x10a312 3 11) (Reg.operands [.gpr 3, .gpr 11] [])) #v[147, 133]
    (.letOp (n := 151) (.out 0x10a315 (xorR64R64Effect 0x10a315 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 3] []) (.reg (.gpr 2))) #v[125, 149]
    (.letOp (n := 152) (.exec 0x10a315 (fun s => s.RIP = 0x10a315) (xorR64R64Effect 0x10a315 2 3) (Reg.operands [.gpr 2, .gpr 3] [])) #v[125, 149]
    (.letOp (n := 153) (.out 0x10a318 (shlR64Effect 0x10a318 4 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[149]
    (.letOp (n := 154) (.exec 0x10a318 (fun s => s.RIP = 0x10a318) (shlR64Effect 0x10a318 4 3 2) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[149]
    (.letOp (n := 155) (.out 0x10a31c (xorR64R64Effect 0x10a31c 3 9) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 9] []) (.reg (.gpr 3))) #v[153, 111]
    (.letOp (n := 156) (.exec 0x10a31c (fun s => s.RIP = 0x10a31c) (xorR64R64Effect 0x10a31c 3 9) (Reg.operands [.gpr 3, .gpr 9] [])) #v[153, 111]
    (.letOp (n := 157) (.out 0x10a31f (movR64R64Effect 0x10a31f 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 15] []) (.reg (.gpr 1))) #v[141]
    (.letOp (n := 158) (.exec 0x10a31f (fun s => s.RIP = 0x10a31f) (movR64R64Effect 0x10a31f 1 15) (Reg.operands [.gpr 15] [])) #v[141]
    (.letOp (n := 159) (.out 0x10a322 (shrR64Effect 0x10a322 4 1 4) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[157]
    (.letOp (n := 160) (.exec 0x10a322 (fun s => s.RIP = 0x10a322) (shrR64Effect 0x10a322 4 1 4) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[157]
    (.letOp (n := 161) (.out 0x10a326 (xorR64R64Effect 0x10a326 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 3] []) (.reg (.gpr 1))) #v[159, 155]
    (.letOp (n := 162) (.exec 0x10a326 (fun s => s.RIP = 0x10a326) (xorR64R64Effect 0x10a326 1 3) (Reg.operands [.gpr 1, .gpr 3] [])) #v[159, 155]
    (.letOp (n := 163) (.out 0x10a329 (movR64Imm64Effect 0x10a329 9 0xf0f0f0f0f0f0f0f) (EffectPart.reads (.reg (.gpr 9)) [] []) (.reg (.gpr 9))) #v[]
    (.letOp (n := 164) (.exec 0x10a329 (fun s => s.RIP = 0x10a329) (movR64Imm64Effect 0x10a329 9 0xf0f0f0f0f0f0f0f) (Reg.operands [] [])) #v[]
    (.letOp (n := 165) (.out 0x10a333 (andR64R64Effect 0x10a333 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 9] []) (.reg (.gpr 1))) #v[161, 163]
    (.letOp (n := 166) (.exec 0x10a333 (fun s => s.RIP = 0x10a333) (andR64R64Effect 0x10a333 1 9) (Reg.operands [.gpr 1, .gpr 9] [])) #v[161, 163]
    (.letOp (n := 167) (.out 0x10a336 (xorR64R64Effect 0x10a336 3 1) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 1] []) (.reg (.gpr 3))) #v[155, 165]
    (.letOp (n := 168) (.exec 0x10a336 (fun s => s.RIP = 0x10a336) (xorR64R64Effect 0x10a336 3 1) (Reg.operands [.gpr 3, .gpr 1] [])) #v[155, 165]
    (.letOp (n := 169) (.out 0x10a339 (shlR64Effect 0x10a339 4 1 4) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[165]
    (.letOp (n := 170) (.exec 0x10a339 (fun s => s.RIP = 0x10a339) (shlR64Effect 0x10a339 4 1 4) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[165]
    (.letOp (n := 171) (.out 0x10a33d (xorR64R64Effect 0x10a33d 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 15] []) (.reg (.gpr 1))) #v[169, 141]
    (.letOp (n := 172) (.exec 0x10a33d (fun s => s.RIP = 0x10a33d) (xorR64R64Effect 0x10a33d 1 15) (Reg.operands [.gpr 1, .gpr 15] [])) #v[169, 141]
    (b_l10a26a_3))))))))))))))))))))))))))))))))))))))))

def bytes_l10a26a_2 : List UInt8 :=
  [0x49, 0xBB, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x4D, 0x21, 0xDF, 0x4C, 0x31, 0xFE,
    0x49, 0xC1, 0xE7, 0x02, 0x49, 0x31, 0xCF, 0x4C, 0x89, 0xCB, 0x48, 0xC1, 0xEB, 0x02, 0x48, 0x31,
    0xD3, 0x4C, 0x21, 0xDB, 0x48, 0x31, 0xDA, 0x48, 0xC1, 0xE3, 0x02, 0x4C, 0x31, 0xCB, 0x4C, 0x89,
    0xF9, 0x48, 0xC1, 0xE9, 0x04, 0x48, 0x31, 0xD9, 0x49, 0xB9, 0x0F, 0x0F, 0x0F, 0x0F, 0x0F, 0x0F,
    0x0F, 0x0F, 0x4C, 0x21, 0xC9, 0x48, 0x31, 0xCB, 0x48, 0xC1, 0xE1, 0x04, 0x4C, 0x31, 0xF9] ++ bytes_l10a26a_3

theorem code_l10a26a_2 : ∀ x ∈ codeRange 0x10a2f1 bytes_l10a26a_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa2f1 79 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a26a_3

def b_l10a26a_1 : Block Op Label signature Reg.count 93 :=
  .letOp (n := 93) (.out 0x10a2b4 (xorR64R64Effect 0x10a2b4 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 6] []) (.reg (.gpr 14))) #v[59, 91]
    (.letOp (n := 94) (.exec 0x10a2b4 (fun s => s.RIP = 0x10a2b4) (xorR64R64Effect 0x10a2b4 14 6) (Reg.operands [.gpr 14, .gpr 6] [])) #v[59, 91]
    (.letOp (n := 95) (.out 0x10a2b7 (addR64R64Effect 0x10a2b7 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[91, 91]
    (.letOp (n := 96) (.exec 0x10a2b7 (fun s => s.RIP = 0x10a2b7) (addR64R64Effect 0x10a2b7 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[91, 91]
    (.letOp (n := 97) (.out 0x10a2ba (xorR64R64Effect 0x10a2ba 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 15] []) (.reg (.gpr 6))) #v[95, 57]
    (.letOp (n := 98) (.exec 0x10a2ba (fun s => s.RIP = 0x10a2ba) (xorR64R64Effect 0x10a2ba 6 15) (Reg.operands [.gpr 6, .gpr 15] [])) #v[95, 57]
    (.letOp (n := 99) (.out 0x10a2bd (movR64R64Effect 0x10a2bd 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[61]
    (.letOp (n := 100) (.exec 0x10a2bd (fun s => s.RIP = 0x10a2bd) (movR64R64Effect 0x10a2bd 9 2) (Reg.operands [.gpr 2] [])) #v[61]
    (.letOp (n := 101) (.out 0x10a2c0 (shrR64Effect 0x10a2c0 3 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[99]
    (.letOp (n := 102) (.exec 0x10a2c0 (fun s => s.RIP = 0x10a2c0) (shrR64Effect 0x10a2c0 3 9 1) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[99]
    (.letOp (n := 103) (.out 0x10a2c3 (xorR64R64Effect 0x10a2c3 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8] []) (.reg (.gpr 9))) #v[101, 63]
    (.letOp (n := 104) (.exec 0x10a2c3 (fun s => s.RIP = 0x10a2c3) (xorR64R64Effect 0x10a2c3 9 8) (Reg.operands [.gpr 9, .gpr 8] [])) #v[101, 63]
    (.letOp (n := 105) (.out 0x10a2c6 (andR64R64Effect 0x10a2c6 9 3) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 3] []) (.reg (.gpr 9))) #v[103, 75]
    (.letOp (n := 106) (.exec 0x10a2c6 (fun s => s.RIP = 0x10a2c6) (andR64R64Effect 0x10a2c6 9 3) (Reg.operands [.gpr 9, .gpr 3] [])) #v[103, 75]
    (.letOp (n := 107) (.out 0x10a2c9 (xorR64R64Effect 0x10a2c9 8 9) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 9] []) (.reg (.gpr 8))) #v[63, 105]
    (.letOp (n := 108) (.exec 0x10a2c9 (fun s => s.RIP = 0x10a2c9) (xorR64R64Effect 0x10a2c9 8 9) (Reg.operands [.gpr 8, .gpr 9] [])) #v[63, 105]
    (.letOp (n := 109) (.out 0x10a2cc (addR64R64Effect 0x10a2cc 9 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 9] []) (.reg (.gpr 9))) #v[105, 105]
    (.letOp (n := 110) (.exec 0x10a2cc (fun s => s.RIP = 0x10a2cc) (addR64R64Effect 0x10a2cc 9 9) (Reg.operands [.gpr 9, .gpr 9] [])) #v[105, 105]
    (.letOp (n := 111) (.out 0x10a2cf (xorR64R64Effect 0x10a2cf 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2] []) (.reg (.gpr 9))) #v[109, 61]
    (.letOp (n := 112) (.exec 0x10a2cf (fun s => s.RIP = 0x10a2cf) (xorR64R64Effect 0x10a2cf 9 2) (Reg.operands [.gpr 9, .gpr 2] [])) #v[109, 61]
    (.letOp (n := 113) (.out 0x10a2d2 (movR64R64Effect 0x10a2d2 2 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11] []) (.reg (.gpr 2))) #v[65]
    (.letOp (n := 114) (.exec 0x10a2d2 (fun s => s.RIP = 0x10a2d2) (movR64R64Effect 0x10a2d2 2 11) (Reg.operands [.gpr 11] [])) #v[65]
    (.letOp (n := 115) (.out 0x10a2d5 (shrR64Effect 0x10a2d5 3 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[113]
    (.letOp (n := 116) (.exec 0x10a2d5 (fun s => s.RIP = 0x10a2d5) (shrR64Effect 0x10a2d5 3 2 1) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[113]
    (.letOp (n := 117) (.out 0x10a2d8 (xorR64R64Effect 0x10a2d8 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[115, 67]
    (.letOp (n := 118) (.exec 0x10a2d8 (fun s => s.RIP = 0x10a2d8) (xorR64R64Effect 0x10a2d8 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[115, 67]
    (.letOp (n := 119) (.out 0x10a2db (andR64R64Effect 0x10a2db 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 3] []) (.reg (.gpr 2))) #v[117, 75]
    (.letOp (n := 120) (.exec 0x10a2db (fun s => s.RIP = 0x10a2db) (andR64R64Effect 0x10a2db 2 3) (Reg.operands [.gpr 2, .gpr 3] [])) #v[117, 75]
    (.letOp (n := 121) (.out 0x10a2de (xorR64R64Effect 0x10a2de 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[67, 119]
    (.letOp (n := 122) (.exec 0x10a2de (fun s => s.RIP = 0x10a2de) (xorR64R64Effect 0x10a2de 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[67, 119]
    (.letOp (n := 123) (.out 0x10a2e1 (addR64R64Effect 0x10a2e1 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[119, 119]
    (.letOp (n := 124) (.exec 0x10a2e1 (fun s => s.RIP = 0x10a2e1) (addR64R64Effect 0x10a2e1 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[119, 119]
    (.letOp (n := 125) (.out 0x10a2e4 (xorR64R64Effect 0x10a2e4 2 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 11] []) (.reg (.gpr 2))) #v[123, 65]
    (.letOp (n := 126) (.exec 0x10a2e4 (fun s => s.RIP = 0x10a2e4) (xorR64R64Effect 0x10a2e4 2 11) (Reg.operands [.gpr 2, .gpr 11] [])) #v[123, 65]
    (.letOp (n := 127) (.out 0x10a2e7 (movR64R64Effect 0x10a2e7 15 1) (EffectPart.reads (.reg (.gpr 15)) [.gpr 1] []) (.reg (.gpr 15))) #v[83]
    (.letOp (n := 128) (.exec 0x10a2e7 (fun s => s.RIP = 0x10a2e7) (movR64R64Effect 0x10a2e7 15 1) (Reg.operands [.gpr 1] [])) #v[83]
    (.letOp (n := 129) (.out 0x10a2ea (shrR64Effect 0x10a2ea 4 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[127]
    (.letOp (n := 130) (.exec 0x10a2ea (fun s => s.RIP = 0x10a2ea) (shrR64Effect 0x10a2ea 4 15 2) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[127]
    (.letOp (n := 131) (.out 0x10a2ee (xorR64R64Effect 0x10a2ee 15 6) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 6] []) (.reg (.gpr 15))) #v[129, 97]
    (.letOp (n := 132) (.exec 0x10a2ee (fun s => s.RIP = 0x10a2ee) (xorR64R64Effect 0x10a2ee 15 6) (Reg.operands [.gpr 15, .gpr 6] [])) #v[129, 97]
    (b_l10a26a_2))))))))))))))))))))))))))))))))))))))))

def bytes_l10a26a_1 : List UInt8 :=
  [0x49, 0x31, 0xF6, 0x48, 0x01, 0xF6, 0x4C, 0x31, 0xFE, 0x49, 0x89, 0xD1, 0x49, 0xD1, 0xE9, 0x4D,
    0x31, 0xC1, 0x49, 0x21, 0xD9, 0x4D, 0x31, 0xC8, 0x4D, 0x01, 0xC9, 0x49, 0x31, 0xD1, 0x4C, 0x89,
    0xDA, 0x48, 0xD1, 0xEA, 0x48, 0x31, 0xC2, 0x48, 0x21, 0xDA, 0x48, 0x31, 0xD0, 0x48, 0x01, 0xD2,
    0x4C, 0x31, 0xDA, 0x49, 0x89, 0xCF, 0x49, 0xC1, 0xEF, 0x02, 0x49, 0x31, 0xF7] ++ bytes_l10a26a_2

theorem code_l10a26a_1 : ∀ x ∈ codeRange 0x10a2b4 bytes_l10a26a_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa2b4 61 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a26a_2

def b_l10a26a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10a26a (movR64M64Effect 0x10a26a 9 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 6] []) (.reg (.gpr 9))) #v[6]
    (.letOp (n := 54) (.exec 0x10a26a (LoadPre 0x10a26a (fun s => AddrMode.addr (.base 6 .none) s (0x10a26a + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x10a26a 9 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 55) (.out 0x10a26d (movR64M64Effect 0x10a26d 10 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 6] []) (.reg (.gpr 10))) #v[6]
    (.letOp (n := 56) (.exec 0x10a26d (LoadPre 0x10a26d (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x10a26d + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a26d 10 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 57) (.out 0x10a271 (movR64M64Effect 0x10a271 15 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 6] []) (.reg (.gpr 15))) #v[6]
    (.letOp (n := 58) (.exec 0x10a271 (LoadPre 0x10a271 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x10a271 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a271 15 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 59) (.out 0x10a275 (movR64M64Effect 0x10a275 14 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 6] []) (.reg (.gpr 14))) #v[6]
    (.letOp (n := 60) (.exec 0x10a275 (LoadPre 0x10a275 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x10a275 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a275 14 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 61) (.out 0x10a279 (movR64M64Effect 0x10a279 2 (.base 6 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6] []) (.reg (.gpr 2))) #v[6]
    (.letOp (n := 62) (.exec 0x10a279 (LoadPre 0x10a279 (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x10a279 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a279 2 (.base 6 (.d8 0x20))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 63) (.out 0x10a27d (movR64M64Effect 0x10a27d 8 (.base 6 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 6] []) (.reg (.gpr 8))) #v[6]
    (.letOp (n := 64) (.exec 0x10a27d (LoadPre 0x10a27d (fun s => AddrMode.addr (.base 6 (.d8 0x28)) s (0x10a27d + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a27d 8 (.base 6 (.d8 0x28))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 65) (.out 0x10a281 (movR64M64Effect 0x10a281 11 (.base 6 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 6] []) (.reg (.gpr 11))) #v[6]
    (.letOp (n := 66) (.exec 0x10a281 (LoadPre 0x10a281 (fun s => AddrMode.addr (.base 6 (.d8 0x30)) s (0x10a281 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a281 11 (.base 6 (.d8 0x30))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 67) (.out 0x10a285 (movR64M64Effect 0x10a285 0 (.base 6 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 68) (.exec 0x10a285 (LoadPre 0x10a285 (fun s => AddrMode.addr (.base 6 (.d8 0x38)) s (0x10a285 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a285 0 (.base 6 (.d8 0x38))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 69) (.out 0x10a289 (movR64R64Effect 0x10a289 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 9] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 70) (.exec 0x10a289 (fun s => s.RIP = 0x10a289) (movR64R64Effect 0x10a289 1 9) (Reg.operands [.gpr 9] [])) #v[53]
    (.letOp (n := 71) (.out 0x10a28c (shrR64Effect 0x10a28c 3 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[69]
    (.letOp (n := 72) (.exec 0x10a28c (fun s => s.RIP = 0x10a28c) (shrR64Effect 0x10a28c 3 1 1) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[69]
    (.letOp (n := 73) (.out 0x10a28f (xorR64R64Effect 0x10a28f 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10] []) (.reg (.gpr 1))) #v[71, 55]
    (.letOp (n := 74) (.exec 0x10a28f (fun s => s.RIP = 0x10a28f) (xorR64R64Effect 0x10a28f 1 10) (Reg.operands [.gpr 1, .gpr 10] [])) #v[71, 55]
    (.letOp (n := 75) (.out 0x10a292 (movR64Imm64Effect 0x10a292 3 0x5555555555555555) (EffectPart.reads (.reg (.gpr 3)) [] []) (.reg (.gpr 3))) #v[]
    (.letOp (n := 76) (.exec 0x10a292 (fun s => s.RIP = 0x10a292) (movR64Imm64Effect 0x10a292 3 0x5555555555555555) (Reg.operands [] [])) #v[]
    (.letOp (n := 77) (.out 0x10a29c (andR64R64Effect 0x10a29c 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 3] []) (.reg (.gpr 1))) #v[73, 75]
    (.letOp (n := 78) (.exec 0x10a29c (fun s => s.RIP = 0x10a29c) (andR64R64Effect 0x10a29c 1 3) (Reg.operands [.gpr 1, .gpr 3] [])) #v[73, 75]
    (.letOp (n := 79) (.out 0x10a29f (xorR64R64Effect 0x10a29f 10 1) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 1] []) (.reg (.gpr 10))) #v[55, 77]
    (.letOp (n := 80) (.exec 0x10a29f (fun s => s.RIP = 0x10a29f) (xorR64R64Effect 0x10a29f 10 1) (Reg.operands [.gpr 10, .gpr 1] [])) #v[55, 77]
    (.letOp (n := 81) (.out 0x10a2a2 (addR64R64Effect 0x10a2a2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[77, 77]
    (.letOp (n := 82) (.exec 0x10a2a2 (fun s => s.RIP = 0x10a2a2) (addR64R64Effect 0x10a2a2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[77, 77]
    (.letOp (n := 83) (.out 0x10a2a5 (xorR64R64Effect 0x10a2a5 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 9] []) (.reg (.gpr 1))) #v[81, 53]
    (.letOp (n := 84) (.exec 0x10a2a5 (fun s => s.RIP = 0x10a2a5) (xorR64R64Effect 0x10a2a5 1 9) (Reg.operands [.gpr 1, .gpr 9] [])) #v[81, 53]
    (.letOp (n := 85) (.out 0x10a2a8 (movR64R64Effect 0x10a2a8 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[57]
    (.letOp (n := 86) (.exec 0x10a2a8 (fun s => s.RIP = 0x10a2a8) (movR64R64Effect 0x10a2a8 6 15) (Reg.operands [.gpr 15] [])) #v[57]
    (.letOp (n := 87) (.out 0x10a2ab (shrR64Effect 0x10a2ab 3 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[85]
    (.letOp (n := 88) (.exec 0x10a2ab (fun s => s.RIP = 0x10a2ab) (shrR64Effect 0x10a2ab 3 6 1) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[85]
    (.letOp (n := 89) (.out 0x10a2ae (xorR64R64Effect 0x10a2ae 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 14] []) (.reg (.gpr 6))) #v[87, 59]
    (.letOp (n := 90) (.exec 0x10a2ae (fun s => s.RIP = 0x10a2ae) (xorR64R64Effect 0x10a2ae 6 14) (Reg.operands [.gpr 6, .gpr 14] [])) #v[87, 59]
    (.letOp (n := 91) (.out 0x10a2b1 (andR64R64Effect 0x10a2b1 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 3] []) (.reg (.gpr 6))) #v[89, 75]
    (.letOp (n := 92) (.exec 0x10a2b1 (fun s => s.RIP = 0x10a2b1) (andR64R64Effect 0x10a2b1 6 3) (Reg.operands [.gpr 6, .gpr 3] [])) #v[89, 75]
    (b_l10a26a_1))))))))))))))))))))))))))))))))))))))))

def bytes_l10a26a : List UInt8 :=
  [0x4C, 0x8B, 0x0E, 0x4C, 0x8B, 0x56, 0x08, 0x4C, 0x8B, 0x7E, 0x10, 0x4C, 0x8B, 0x76, 0x18, 0x48,
    0x8B, 0x56, 0x20, 0x4C, 0x8B, 0x46, 0x28, 0x4C, 0x8B, 0x5E, 0x30, 0x48, 0x8B, 0x46, 0x38, 0x4C,
    0x89, 0xC9, 0x48, 0xD1, 0xE9, 0x4C, 0x31, 0xD1, 0x48, 0xBB, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55,
    0x55, 0x55, 0x48, 0x21, 0xD9, 0x49, 0x31, 0xCA, 0x48, 0x01, 0xC9, 0x4C, 0x31, 0xC9, 0x4C, 0x89,
    0xFE, 0x48, 0xD1, 0xEE, 0x4C, 0x31, 0xF6, 0x48, 0x21, 0xDE] ++ bytes_l10a26a_1

theorem code_l10a26a : ∀ x ∈ codeRange 0x10a26a bytes_l10a26a, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa26a 74 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a26a_1

@[cfg_block] def b_l10a5d7 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10a5d7 (xorR32R32Effect 0x10a5d7 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[7, 7]
    (.letOp (n := 54) (.exec 0x10a5d7 (fun s => s.RIP = 0x10a5d7) (xorR32R32Effect 0x10a5d7 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[7, 7]
    (.letOp (n := 55) (.out 0x10a5d9 (xorR32R32Effect 0x10a5d9 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[6, 6]
    (.letOp (n := 56) (.exec 0x10a5d9 (fun s => s.RIP = 0x10a5d9) (xorR32R32Effect 0x10a5d9 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 57) (.out 0x10a5db (movR64Imm32Effect 0x10a5db 2 0x201130) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x10a5db (fun s => s.RIP = 0x10a5db) (movR64Imm32Effect 0x10a5db 2 0x201130) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x10a5e2 (callEffect (fun _ => 0x103837) 0x10a5e7) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x10a5e2 (PushPre 0x10a5e2 5) (callEffect (fun _ => 0x103837) 0x10a5e7) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x10a5e7⟩) #v[]
    (.terminate (.call ⟨.l103837, RegMap.args [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)] 62⟩ { target := .l10a5e7, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l10a5d7 : List UInt8 :=
  [0x31, 0xFF, 0x31, 0xF6, 0x48, 0xC7, 0xC2, 0x30, 0x11, 0x20, 0x00, 0xE8, 0x50, 0x92, 0xFF, 0xFF]

theorem code_l10a5d7 : ∀ x ∈ codeRange 0x10a5d7 bytes_l10a5d7, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xa5d7 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10a5e7 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10a5e7 (movR32Imm32Effect 0x10a5e7 5 7 0x1) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 54) (.exec 0x10a5e7 (fun s => s.RIP = 0x10a5e7) (movR32Imm32Effect 0x10a5e7 5 7 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x10a5ec (movR32Imm32Effect 0x10a5ec 5 6 0x1) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 56) (.exec 0x10a5ec (fun s => s.RIP = 0x10a5ec) (movR32Imm32Effect 0x10a5ec 5 6 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x10a5f1 (movR64Imm32Effect 0x10a5f1 2 0x201148) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x10a5f1 (fun s => s.RIP = 0x10a5f1) (movR64Imm32Effect 0x10a5f1 2 0x201148) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x10a5f8 (callEffect (fun _ => 0x103837) 0x10a5fd) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x10a5f8 (PushPre 0x10a5f8 5) (callEffect (fun _ => 0x103837) 0x10a5fd) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x10a5fd⟩) #v[]
    (.terminate (.call ⟨.l103837, RegMap.args [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)] 62⟩ { target := .l10a5fd, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l10a5e7 : List UInt8 :=
  [0xBF, 0x01, 0x00, 0x00, 0x00, 0xBE, 0x01, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC2, 0x48, 0x11, 0x20,
    0x00, 0xE8, 0x3A, 0x92, 0xFF, 0xFF]

theorem code_l10a5e7 : ∀ x ∈ codeRange 0x10a5e7 bytes_l10a5e7, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xa5e7 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10a5fd : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10a5fd (movR32Imm32Effect 0x10a5fd 5 7 0x2) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 54) (.exec 0x10a5fd (fun s => s.RIP = 0x10a5fd) (movR32Imm32Effect 0x10a5fd 5 7 0x2) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x10a602 (movR32Imm32Effect 0x10a602 5 6 0x2) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 56) (.exec 0x10a602 (fun s => s.RIP = 0x10a602) (movR32Imm32Effect 0x10a602 5 6 0x2) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x10a607 (movR64Imm32Effect 0x10a607 2 0x201160) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x10a607 (fun s => s.RIP = 0x10a607) (movR64Imm32Effect 0x10a607 2 0x201160) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x10a60e (callEffect (fun _ => 0x103837) 0x10a613) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x10a60e (PushPre 0x10a60e 5) (callEffect (fun _ => 0x103837) 0x10a613) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x10a613⟩) #v[]
    (.terminate (.call ⟨.l103837, RegMap.args [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)] 62⟩ { target := .l10a613, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l10a5fd : List UInt8 :=
  [0xBF, 0x02, 0x00, 0x00, 0x00, 0xBE, 0x02, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC2, 0x60, 0x11, 0x20,
    0x00, 0xE8, 0x24, 0x92, 0xFF, 0xFF]

theorem code_l10a5fd : ∀ x ∈ codeRange 0x10a5fd bytes_l10a5fd, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xa5fd 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10a613 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10a613 (movR32Imm32Effect 0x10a613 5 7 0x3) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 54) (.exec 0x10a613 (fun s => s.RIP = 0x10a613) (movR32Imm32Effect 0x10a613 5 7 0x3) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x10a618 (movR32Imm32Effect 0x10a618 5 6 0x3) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 56) (.exec 0x10a618 (fun s => s.RIP = 0x10a618) (movR32Imm32Effect 0x10a618 5 6 0x3) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x10a61d (movR64Imm32Effect 0x10a61d 2 0x201178) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x10a61d (fun s => s.RIP = 0x10a61d) (movR64Imm32Effect 0x10a61d 2 0x201178) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x10a624 (callEffect (fun _ => 0x103837) 0x10a629) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x10a624 (PushPre 0x10a624 5) (callEffect (fun _ => 0x103837) 0x10a629) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x10a629⟩) #v[]
    (.terminate (.call ⟨.l103837, RegMap.args [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)] 62⟩ { target := .l10a629, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l10a613 : List UInt8 :=
  [0xBF, 0x03, 0x00, 0x00, 0x00, 0xBE, 0x03, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC2, 0x78, 0x11, 0x20,
    0x00, 0xE8, 0x0E, 0x92, 0xFF, 0xFF]

theorem code_l10a613 : ∀ x ∈ codeRange 0x10a613 bytes_l10a613, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xa613 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10a629 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10a629 (movR32Imm32Effect 0x10a629 5 7 0x4) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 54) (.exec 0x10a629 (fun s => s.RIP = 0x10a629) (movR32Imm32Effect 0x10a629 5 7 0x4) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x10a62e (movR32Imm32Effect 0x10a62e 5 6 0x4) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 56) (.exec 0x10a62e (fun s => s.RIP = 0x10a62e) (movR32Imm32Effect 0x10a62e 5 6 0x4) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x10a633 (movR64Imm32Effect 0x10a633 2 0x201190) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x10a633 (fun s => s.RIP = 0x10a633) (movR64Imm32Effect 0x10a633 2 0x201190) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x10a63a (callEffect (fun _ => 0x103837) 0x10a63f) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x10a63a (PushPre 0x10a63a 5) (callEffect (fun _ => 0x103837) 0x10a63f) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x10a63f⟩) #v[]
    (.terminate (.call ⟨.l103837, RegMap.args [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)] 62⟩ { target := .l10a63f, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l10a629 : List UInt8 :=
  [0xBF, 0x04, 0x00, 0x00, 0x00, 0xBE, 0x04, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC2, 0x90, 0x11, 0x20,
    0x00, 0xE8, 0xF8, 0x91, 0xFF, 0xFF]

theorem code_l10a629 : ∀ x ∈ codeRange 0x10a629 bytes_l10a629, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xa629 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10a63f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10a63f (movR32Imm32Effect 0x10a63f 5 7 0x5) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 54) (.exec 0x10a63f (fun s => s.RIP = 0x10a63f) (movR32Imm32Effect 0x10a63f 5 7 0x5) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x10a644 (movR32Imm32Effect 0x10a644 5 6 0x5) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 56) (.exec 0x10a644 (fun s => s.RIP = 0x10a644) (movR32Imm32Effect 0x10a644 5 6 0x5) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x10a649 (movR64Imm32Effect 0x10a649 2 0x2011a8) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x10a649 (fun s => s.RIP = 0x10a649) (movR64Imm32Effect 0x10a649 2 0x2011a8) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x10a650 (callEffect (fun _ => 0x103837) 0x10a655) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x10a650 (PushPre 0x10a650 5) (callEffect (fun _ => 0x103837) 0x10a655) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x10a655⟩) #v[]
    (.terminate (.call ⟨.l103837, RegMap.args [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)] 62⟩ { target := .l10a655, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l10a63f : List UInt8 :=
  [0xBF, 0x05, 0x00, 0x00, 0x00, 0xBE, 0x05, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC2, 0xA8, 0x11, 0x20,
    0x00, 0xE8, 0xE2, 0x91, 0xFF, 0xFF]

theorem code_l10a63f : ∀ x ∈ codeRange 0x10a63f bytes_l10a63f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xa63f 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10a655 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10a655 (movR32Imm32Effect 0x10a655 5 7 0x6) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 54) (.exec 0x10a655 (fun s => s.RIP = 0x10a655) (movR32Imm32Effect 0x10a655 5 7 0x6) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x10a65a (movR32Imm32Effect 0x10a65a 5 6 0x6) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 56) (.exec 0x10a65a (fun s => s.RIP = 0x10a65a) (movR32Imm32Effect 0x10a65a 5 6 0x6) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x10a65f (movR64Imm32Effect 0x10a65f 2 0x2011c0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x10a65f (fun s => s.RIP = 0x10a65f) (movR64Imm32Effect 0x10a65f 2 0x2011c0) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x10a666 (callEffect (fun _ => 0x103837) 0x10a66b) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x10a666 (PushPre 0x10a666 5) (callEffect (fun _ => 0x103837) 0x10a66b) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x10a66b⟩) #v[]
    (.terminate (.call ⟨.l103837, RegMap.args [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)] 62⟩ { target := .l10a66b, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l10a655 : List UInt8 :=
  [0xBF, 0x06, 0x00, 0x00, 0x00, 0xBE, 0x06, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC2, 0xC0, 0x11, 0x20,
    0x00, 0xE8, 0xCC, 0x91, 0xFF, 0xFF]

theorem code_l10a655 : ∀ x ∈ codeRange 0x10a655 bytes_l10a655, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xa655 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10a66b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10a66b (movR32Imm32Effect 0x10a66b 5 7 0x7) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 54) (.exec 0x10a66b (fun s => s.RIP = 0x10a66b) (movR32Imm32Effect 0x10a66b 5 7 0x7) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x10a670 (movR32Imm32Effect 0x10a670 5 6 0x7) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 56) (.exec 0x10a670 (fun s => s.RIP = 0x10a670) (movR32Imm32Effect 0x10a670 5 6 0x7) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x10a675 (movR64Imm32Effect 0x10a675 2 0x2011d8) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x10a675 (fun s => s.RIP = 0x10a675) (movR64Imm32Effect 0x10a675 2 0x2011d8) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x10a67c (callEffect (fun _ => 0x103837) 0x10a681) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x10a67c (PushPre 0x10a67c 5) (callEffect (fun _ => 0x103837) 0x10a681) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x10a681⟩) #v[]
    (.terminate (.call ⟨.l103837, RegMap.args [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)] 62⟩ { target := .l10a681, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l10a66b : List UInt8 :=
  [0xBF, 0x07, 0x00, 0x00, 0x00, 0xBE, 0x07, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC2, 0xD8, 0x11, 0x20,
    0x00, 0xE8, 0xB6, 0x91, 0xFF, 0xFF]

theorem code_l10a66b : ∀ x ∈ codeRange 0x10a66b bytes_l10a66b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xa66b 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10a681 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x10a681 (fun s => s.RIP = 0x10a681) (fun _ => nopEffect 0x10a681 10) (Reg.operands [] [])) #v[]
    (.letOp (n := 54) (.exec 0x10a68b (fun s => s.RIP = 0x10a68b) (fun _ => nopEffect 0x10a68b 5) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l10a690, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l10a681 : List UInt8 :=
  [0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00, 0x0F, 0x1F, 0x44, 0x00, 0x00]

theorem code_l10a681 : ∀ x ∈ codeRange 0x10a681 bytes_l10a681, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xa681 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10a690 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10a690 (pushR64Effect 0x10a690 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x10a690 (PushPre 0x10a690 1) (pushR64Effect 0x10a690 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x10a691 (pushR64Effect 0x10a691 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x10a691 (PushPre 0x10a691 2) (pushR64Effect 0x10a691 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x10a693 (pushR64Effect 0x10a693 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x10a693 (PushPre 0x10a693 2) (pushR64Effect 0x10a693 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x10a695 (pushR64Effect 0x10a695 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x10a695 (PushPre 0x10a695 2) (pushR64Effect 0x10a695 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x10a697 (pushR64Effect 0x10a697 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x10a697 (PushPre 0x10a697 2) (pushR64Effect 0x10a697 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x10a699 (pushR64Effect 0x10a699 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x10a699 (PushPre 0x10a699 1) (pushR64Effect 0x10a699 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x10a69a (subR64Imm8Effect 0x10a69a 4 0x18) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x10a69a (fun s => s.RIP = 0x10a69a) (subR64Imm8Effect 0x10a69a 4 0x18) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x10a69e (cmpR64Imm8Effect 0x10a69e 6 0x7) (EffectPart.reads (.flag .CF) [.gpr 6] []) (.flag .CF)) #v[6]
    (.letOp (n := 68) (.out 0x10a69e (cmpR64Imm8Effect 0x10a69e 6 0x7) (EffectPart.reads (.flag .ZF) [.gpr 6] []) (.flag .ZF)) #v[6]
    (.letOp (n := 69) (.exec 0x10a69e (fun s => s.RIP = 0x10a69e) (cmpR64Imm8Effect 0x10a69e 6 0x7) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 70) (.pure (condOp 6)) #v[67, 68]
    (.terminate (.condBr (Fin.last 70) ⟨.l10aa99, RegMap.args [(2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (16, 67), (19, 68), (22, 22), (39, 39), (50, 50), (51, 51)] 71⟩ ⟨.l10a6a8, RegMap.args [(2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (16, 67), (19, 68), (22, 22), (39, 39), (50, 50), (51, 51)] 71⟩)))))))))))))))))))

def bytes_l10a690 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x83, 0xEC, 0x18, 0x48, 0x83,
    0xFE, 0x07, 0x0F, 0x86, 0xF1, 0x03, 0x00, 0x00]

theorem code_l10a690 : ∀ x ∈ codeRange 0x10a690 bytes_l10a690, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xa690 24 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

def b_l10a6a8_14 : Block Op Label signature Reg.count 603 :=
  .letOp (n := 603) (.out 0x10aa8f (popR64Effect 0x10aa8f 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[601]
    (.letOp (n := 604) (.out 0x10aa8f (popR64Effect 0x10aa8f 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[601]
    (.letOp (n := 605) (.exec 0x10aa8f (PopPre 0x10aa8f) (popR64Effect 0x10aa8f 2 12) (Reg.operands [.gpr 4] [])) #v[601]
    (.letOp (n := 606) (.out 0x10aa91 (popR64Effect 0x10aa91 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[604]
    (.letOp (n := 607) (.out 0x10aa91 (popR64Effect 0x10aa91 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[604]
    (.letOp (n := 608) (.exec 0x10aa91 (PopPre 0x10aa91) (popR64Effect 0x10aa91 2 13) (Reg.operands [.gpr 4] [])) #v[604]
    (.letOp (n := 609) (.out 0x10aa93 (popR64Effect 0x10aa93 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[607]
    (.letOp (n := 610) (.out 0x10aa93 (popR64Effect 0x10aa93 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[607]
    (.letOp (n := 611) (.exec 0x10aa93 (PopPre 0x10aa93) (popR64Effect 0x10aa93 2 14) (Reg.operands [.gpr 4] [])) #v[607]
    (.letOp (n := 612) (.out 0x10aa95 (popR64Effect 0x10aa95 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[610]
    (.letOp (n := 613) (.out 0x10aa95 (popR64Effect 0x10aa95 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[610]
    (.letOp (n := 614) (.exec 0x10aa95 (PopPre 0x10aa95) (popR64Effect 0x10aa95 2 15) (Reg.operands [.gpr 4] [])) #v[610]
    (.letOp (n := 615) (.out 0x10aa97 (popR64Effect 0x10aa97 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[613]
    (.letOp (n := 616) (.out 0x10aa97 (popR64Effect 0x10aa97 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[613]
    (.letOp (n := 617) (.exec 0x10aa97 (PopPre 0x10aa97) (popR64Effect 0x10aa97 1 5) (Reg.operands [.gpr 4] [])) #v[613]
    (.letOp (n := 618) (.out 0x10aa98 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[616]
    (.letOp (n := 619) (.out 0x10aa98 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[616]
    (.letOp (n := 620) (.exec 0x10aa98 (RetPre 0x10aa98) (retEffect) (Reg.operands [.gpr 4] [])) #v[616]
    (.terminate (.ret (RegMap.args [(0, 538), (1, 562), (2, 484), (3, 600), (4, 619), (5, 615), (6, 588), (7, 536), (8, 586), (9, 564), (10, 482), (11, 568), (12, 603), (13, 606), (14, 609), (15, 612), (22, 22), (39, 39), (50, 50), (51, 51)] 621) (some ⟨618, by decide⟩))))))))))))))))))))

def bytes_l10a6a8_14 : List UInt8 :=
  [0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l10a6a8_14 : ∀ x ∈ codeRange 0x10aa8f bytes_l10a6a8_14, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xaa8f 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

def b_l10a6a8_13 : Block Op Label signature Reg.count 570 :=
  .letOp (n := 570) (.out 0x10aa4a (shlR64Effect 0x10aa4a 4 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[518]
    (.letOp (n := 571) (.exec 0x10aa4a (fun s => s.RIP = 0x10aa4a) (shlR64Effect 0x10aa4a 4 3 2) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[518]
    (.letOp (n := 572) (.out 0x10aa4e (xorR64R64Effect 0x10aa4e 3 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 12] []) (.reg (.gpr 3))) #v[570, 496]
    (.letOp (n := 573) (.exec 0x10aa4e (fun s => s.RIP = 0x10aa4e) (xorR64R64Effect 0x10aa4e 3 12) (Reg.operands [.gpr 3, .gpr 12] [])) #v[570, 496]
    (.letOp (n := 574) (.out 0x10aa51 (movR64R64Effect 0x10aa51 6 11) (EffectPart.reads (.reg (.gpr 6)) [.gpr 11] []) (.reg (.gpr 6))) #v[568]
    (.letOp (n := 575) (.exec 0x10aa51 (fun s => s.RIP = 0x10aa51) (movR64R64Effect 0x10aa51 6 11) (Reg.operands [.gpr 11] [])) #v[568]
    (.letOp (n := 576) (.out 0x10aa54 (shrR64Effect 0x10aa54 4 6 4) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[574]
    (.letOp (n := 577) (.exec 0x10aa54 (fun s => s.RIP = 0x10aa54) (shrR64Effect 0x10aa54 4 6 4) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[574]
    (.letOp (n := 578) (.out 0x10aa58 (xorR64R64Effect 0x10aa58 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 3] []) (.reg (.gpr 6))) #v[576, 572]
    (.letOp (n := 579) (.exec 0x10aa58 (fun s => s.RIP = 0x10aa58) (xorR64R64Effect 0x10aa58 6 3) (Reg.operands [.gpr 6, .gpr 3] [])) #v[576, 572]
    (.letOp (n := 580) (.out 0x10aa5b (andR64R64Effect 0x10aa5b 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 13] []) (.reg (.gpr 6))) #v[578, 556]
    (.letOp (n := 581) (.exec 0x10aa5b (fun s => s.RIP = 0x10aa5b) (andR64R64Effect 0x10aa5b 6 13) (Reg.operands [.gpr 6, .gpr 13] [])) #v[578, 556]
    (.letOp (n := 582) (.out 0x10aa5e (movR64R64Effect 0x10aa5e 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 6] []) (.reg (.gpr 8))) #v[580]
    (.letOp (n := 583) (.exec 0x10aa5e (fun s => s.RIP = 0x10aa5e) (movR64R64Effect 0x10aa5e 8 6) (Reg.operands [.gpr 6] [])) #v[580]
    (.letOp (n := 584) (.out 0x10aa61 (shlR64Effect 0x10aa61 4 8 4) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[582]
    (.letOp (n := 585) (.exec 0x10aa61 (fun s => s.RIP = 0x10aa61) (shlR64Effect 0x10aa61 4 8 4) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[582]
    (.letOp (n := 586) (.out 0x10aa65 (xorR64R64Effect 0x10aa65 8 11) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 11] []) (.reg (.gpr 8))) #v[584, 568]
    (.letOp (n := 587) (.exec 0x10aa65 (fun s => s.RIP = 0x10aa65) (xorR64R64Effect 0x10aa65 8 11) (Reg.operands [.gpr 8, .gpr 11] [])) #v[584, 568]
    (.letOp (n := 588) (.out 0x10aa68 (xorR64R64Effect 0x10aa68 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 3] []) (.reg (.gpr 6))) #v[580, 572]
    (.letOp (n := 589) (.exec 0x10aa68 (fun s => s.RIP = 0x10aa68) (xorR64R64Effect 0x10aa68 6 3) (Reg.operands [.gpr 6, .gpr 3] [])) #v[580, 572]
    (.letOp (n := 590) (.exec 0x10aa6b (StorePre 0x10aa6b 3 (fun s => AddrMode.addr (.base 14 .none) s (0x10aa6b + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x10aa6b 8 (.base 14 .none)) (Reg.operands [.gpr 8, .gpr 14] [])) #v[586, 390]
    (.letOp (n := 591) (.exec 0x10aa6e (StorePre 0x10aa6e 4 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x10aa6e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10aa6e 1 (.base 14 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 14] [])) #v[562, 390]
    (.letOp (n := 592) (.exec 0x10aa72 (StorePre 0x10aa72 4 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x10aa72 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10aa72 7 (.base 14 (.d8 0x10))) (Reg.operands [.gpr 7, .gpr 14] [])) #v[536, 390]
    (.letOp (n := 593) (.exec 0x10aa76 (StorePre 0x10aa76 4 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x10aa76 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10aa76 10 (.base 14 (.d8 0x18))) (Reg.operands [.gpr 10, .gpr 14] [])) #v[482, 390]
    (.letOp (n := 594) (.exec 0x10aa7a (StorePre 0x10aa7a 4 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x10aa7a + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10aa7a 6 (.base 14 (.d8 0x20))) (Reg.operands [.gpr 6, .gpr 14] [])) #v[588, 390]
    (.letOp (n := 595) (.exec 0x10aa7e (StorePre 0x10aa7e 4 (fun s => AddrMode.addr (.base 14 (.d8 0x28)) s (0x10aa7e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10aa7e 9 (.base 14 (.d8 0x28))) (Reg.operands [.gpr 9, .gpr 14] [])) #v[564, 390]
    (.letOp (n := 596) (.exec 0x10aa82 (StorePre 0x10aa82 4 (fun s => AddrMode.addr (.base 14 (.d8 0x30)) s (0x10aa82 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10aa82 0 (.base 14 (.d8 0x30))) (Reg.operands [.gpr 0, .gpr 14] [])) #v[538, 390]
    (.letOp (n := 597) (.exec 0x10aa86 (StorePre 0x10aa86 4 (fun s => AddrMode.addr (.base 14 (.d8 0x38)) s (0x10aa86 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10aa86 2 (.base 14 (.d8 0x38))) (Reg.operands [.gpr 2, .gpr 14] [])) #v[484, 390]
    (.letOp (n := 598) (.out 0x10aa8a (addR64Imm8Effect 0x10aa8a 4 0x18) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 599) (.exec 0x10aa8a (fun s => s.RIP = 0x10aa8a) (addR64Imm8Effect 0x10aa8a 4 0x18) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 600) (.out 0x10aa8e (popR64Effect 0x10aa8e 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[598]
    (.letOp (n := 601) (.out 0x10aa8e (popR64Effect 0x10aa8e 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[598]
    (.letOp (n := 602) (.exec 0x10aa8e (PopPre 0x10aa8e) (popR64Effect 0x10aa8e 1 3) (Reg.operands [.gpr 4] [])) #v[598]
    (b_l10a6a8_14)))))))))))))))))))))))))))))))))

def bytes_l10a6a8_13 : List UInt8 :=
  [0x48, 0xC1, 0xE3, 0x02, 0x4C, 0x31, 0xE3, 0x4C, 0x89, 0xDE, 0x48, 0xC1, 0xEE, 0x04, 0x48, 0x31,
    0xDE, 0x4C, 0x21, 0xEE, 0x49, 0x89, 0xF0, 0x49, 0xC1, 0xE0, 0x04, 0x4D, 0x31, 0xD8, 0x48, 0x31,
    0xDE, 0x4D, 0x89, 0x06, 0x49, 0x89, 0x4E, 0x08, 0x49, 0x89, 0x7E, 0x10, 0x4D, 0x89, 0x56, 0x18,
    0x49, 0x89, 0x76, 0x20, 0x4D, 0x89, 0x4E, 0x28, 0x49, 0x89, 0x46, 0x30, 0x49, 0x89, 0x56, 0x38,
    0x48, 0x83, 0xC4, 0x18, 0x5B] ++ bytes_l10a6a8_14

theorem code_l10a6a8_13 : ∀ x ∈ codeRange 0x10aa4a bytes_l10a6a8_13, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xaa4a 69 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a6a8_14

def b_l10a6a8_12 : Block Op Label signature Reg.count 530 :=
  .letOp (n := 530) (.out 0x10aa06 (andR64R64Effect 0x10aa06 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[526, 528]
    (.letOp (n := 531) (.exec 0x10aa06 (fun s => s.RIP = 0x10aa06) (andR64R64Effect 0x10aa06 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[526, 528]
    (.letOp (n := 532) (.out 0x10aa09 (movR64R64Effect 0x10aa09 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[530]
    (.letOp (n := 533) (.exec 0x10aa09 (fun s => s.RIP = 0x10aa09) (movR64R64Effect 0x10aa09 7 0) (Reg.operands [.gpr 0] [])) #v[530]
    (.letOp (n := 534) (.out 0x10aa0c (shlR64Effect 0x10aa0c 4 7 4) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[532]
    (.letOp (n := 535) (.exec 0x10aa0c (fun s => s.RIP = 0x10aa0c) (shlR64Effect 0x10aa0c 4 7 4) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[532]
    (.letOp (n := 536) (.out 0x10aa10 (xorR64R64Effect 0x10aa10 7 9) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 9] []) (.reg (.gpr 7))) #v[534, 506]
    (.letOp (n := 537) (.exec 0x10aa10 (fun s => s.RIP = 0x10aa10) (xorR64R64Effect 0x10aa10 7 9) (Reg.operands [.gpr 7, .gpr 9] [])) #v[534, 506]
    (.letOp (n := 538) (.out 0x10aa13 (xorR64R64Effect 0x10aa13 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 13] []) (.reg (.gpr 0))) #v[530, 524]
    (.letOp (n := 539) (.exec 0x10aa13 (fun s => s.RIP = 0x10aa13) (xorR64R64Effect 0x10aa13 0 13) (Reg.operands [.gpr 0, .gpr 13] [])) #v[530, 524]
    (.letOp (n := 540) (.out 0x10aa16 (shlR64Effect 0x10aa16 4 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[450]
    (.letOp (n := 541) (.exec 0x10aa16 (fun s => s.RIP = 0x10aa16) (shlR64Effect 0x10aa16 4 5 2) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[450]
    (.letOp (n := 542) (.out 0x10aa1a (xorR64M64Effect 0x10aa1a 5 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 4] []) (.reg (.gpr 5))) #v[540, 4]
    (.letOp (n := 543) (.exec 0x10aa1a (LoadPre 0x10aa1a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10aa1a + BitVec.ofNat 64 5)) 8) (xorR64M64Effect 0x10aa1a 5 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[540, 4]
    (.letOp (n := 544) (.out 0x10aa1f (movR64R64Effect 0x10aa1f 9 5) (EffectPart.reads (.reg (.gpr 9)) [.gpr 5] []) (.reg (.gpr 9))) #v[542]
    (.letOp (n := 545) (.exec 0x10aa1f (fun s => s.RIP = 0x10aa1f) (movR64R64Effect 0x10aa1f 9 5) (Reg.operands [.gpr 5] [])) #v[542]
    (.letOp (n := 546) (.out 0x10aa22 (shrR64Effect 0x10aa22 4 9 4) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[544]
    (.letOp (n := 547) (.exec 0x10aa22 (fun s => s.RIP = 0x10aa22) (shrR64Effect 0x10aa22 4 9 4) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[544]
    (.letOp (n := 548) (.out 0x10aa26 (shlR64Effect 0x10aa26 4 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[468]
    (.letOp (n := 549) (.exec 0x10aa26 (fun s => s.RIP = 0x10aa26) (shlR64Effect 0x10aa26 4 15 2) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[468]
    (.letOp (n := 550) (.out 0x10aa2a (xorR64R64Effect 0x10aa2a 15 6) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 6] []) (.reg (.gpr 15))) #v[548, 458]
    (.letOp (n := 551) (.exec 0x10aa2a (fun s => s.RIP = 0x10aa2a) (xorR64R64Effect 0x10aa2a 15 6) (Reg.operands [.gpr 15, .gpr 6] [])) #v[548, 458]
    (.letOp (n := 552) (.out 0x10aa2d (xorR64R64Effect 0x10aa2d 9 15) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 15] []) (.reg (.gpr 9))) #v[546, 550]
    (.letOp (n := 553) (.exec 0x10aa2d (fun s => s.RIP = 0x10aa2d) (xorR64R64Effect 0x10aa2d 9 15) (Reg.operands [.gpr 9, .gpr 15] [])) #v[546, 550]
    (.letOp (n := 554) (.out 0x10aa30 (andR64R64Effect 0x10aa30 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1] []) (.reg (.gpr 9))) #v[552, 528]
    (.letOp (n := 555) (.exec 0x10aa30 (fun s => s.RIP = 0x10aa30) (andR64R64Effect 0x10aa30 9 1) (Reg.operands [.gpr 9, .gpr 1] [])) #v[552, 528]
    (.letOp (n := 556) (.out 0x10aa33 (movR64R64Effect 0x10aa33 13 1) (EffectPart.reads (.reg (.gpr 13)) [.gpr 1] []) (.reg (.gpr 13))) #v[528]
    (.letOp (n := 557) (.exec 0x10aa33 (fun s => s.RIP = 0x10aa33) (movR64R64Effect 0x10aa33 13 1) (Reg.operands [.gpr 1] [])) #v[528]
    (.letOp (n := 558) (.out 0x10aa36 (movR64R64Effect 0x10aa36 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 9] []) (.reg (.gpr 1))) #v[554]
    (.letOp (n := 559) (.exec 0x10aa36 (fun s => s.RIP = 0x10aa36) (movR64R64Effect 0x10aa36 1 9) (Reg.operands [.gpr 9] [])) #v[554]
    (.letOp (n := 560) (.out 0x10aa39 (shlR64Effect 0x10aa39 4 1 4) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[558]
    (.letOp (n := 561) (.exec 0x10aa39 (fun s => s.RIP = 0x10aa39) (shlR64Effect 0x10aa39 4 1 4) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[558]
    (.letOp (n := 562) (.out 0x10aa3d (xorR64R64Effect 0x10aa3d 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 5] []) (.reg (.gpr 1))) #v[560, 542]
    (.letOp (n := 563) (.exec 0x10aa3d (fun s => s.RIP = 0x10aa3d) (xorR64R64Effect 0x10aa3d 1 5) (Reg.operands [.gpr 1, .gpr 5] [])) #v[560, 542]
    (.letOp (n := 564) (.out 0x10aa40 (xorR64R64Effect 0x10aa40 9 15) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 15] []) (.reg (.gpr 9))) #v[554, 550]
    (.letOp (n := 565) (.exec 0x10aa40 (fun s => s.RIP = 0x10aa40) (xorR64R64Effect 0x10aa40 9 15) (Reg.operands [.gpr 9, .gpr 15] [])) #v[554, 550]
    (.letOp (n := 566) (.out 0x10aa43 (shlR64Effect 0x10aa43 4 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[504]
    (.letOp (n := 567) (.exec 0x10aa43 (fun s => s.RIP = 0x10aa43) (shlR64Effect 0x10aa43 4 11 2) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[504]
    (.letOp (n := 568) (.out 0x10aa47 (xorR64R64Effect 0x10aa47 11 8) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 8] []) (.reg (.gpr 11))) #v[566, 488]
    (.letOp (n := 569) (.exec 0x10aa47 (fun s => s.RIP = 0x10aa47) (xorR64R64Effect 0x10aa47 11 8) (Reg.operands [.gpr 11, .gpr 8] [])) #v[566, 488]
    (b_l10a6a8_13))))))))))))))))))))))))))))))))))))))))

def bytes_l10a6a8_12 : List UInt8 :=
  [0x48, 0x21, 0xC8, 0x48, 0x89, 0xC7, 0x48, 0xC1, 0xE7, 0x04, 0x4C, 0x31, 0xCF, 0x4C, 0x31, 0xE8,
    0x48, 0xC1, 0xE5, 0x02, 0x48, 0x33, 0x6C, 0x24, 0x10, 0x49, 0x89, 0xE9, 0x49, 0xC1, 0xE9, 0x04,
    0x49, 0xC1, 0xE7, 0x02, 0x49, 0x31, 0xF7, 0x4D, 0x31, 0xF9, 0x49, 0x21, 0xC9, 0x49, 0x89, 0xCD,
    0x4C, 0x89, 0xC9, 0x48, 0xC1, 0xE1, 0x04, 0x48, 0x31, 0xE9, 0x4D, 0x31, 0xF9, 0x49, 0xC1, 0xE3,
    0x02, 0x4D, 0x31, 0xC3] ++ bytes_l10a6a8_13

theorem code_l10a6a8_12 : ∀ x ∈ codeRange 0x10aa06 bytes_l10a6a8_12, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xaa06 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a6a8_13

def b_l10a6a8_11 : Block Op Label signature Reg.count 490 :=
  .letOp (n := 490) (.out 0x10a9bf (addR64R64Effect 0x10a9bf 9 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 9] []) (.reg (.gpr 9))) #v[248, 248]
    (.letOp (n := 491) (.exec 0x10a9bf (fun s => s.RIP = 0x10a9bf) (addR64R64Effect 0x10a9bf 9 9) (Reg.operands [.gpr 9, .gpr 9] [])) #v[248, 248]
    (.letOp (n := 492) (.out 0x10a9c2 (xorR64M64Effect 0x10a9c2 9 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 4] []) (.reg (.gpr 9))) #v[490, 4]
    (.letOp (n := 493) (.exec 0x10a9c2 (LoadPre 0x10a9c2 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10a9c2 + BitVec.ofNat 64 4)) 8) (xorR64M64Effect 0x10a9c2 9 (.sib 4 none 0 .none)) (Reg.operands [.gpr 9, .gpr 4] [])) #v[490, 4]
    (.letOp (n := 494) (.out 0x10a9c6 (addR64R64Effect 0x10a9c6 12 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 12] []) (.reg (.gpr 12))) #v[432, 432]
    (.letOp (n := 495) (.exec 0x10a9c6 (fun s => s.RIP = 0x10a9c6) (addR64R64Effect 0x10a9c6 12 12) (Reg.operands [.gpr 12, .gpr 12] [])) #v[432, 432]
    (.letOp (n := 496) (.out 0x10a9c9 (xorR64R64Effect 0x10a9c9 12 11) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 11] []) (.reg (.gpr 12))) #v[494, 296]
    (.letOp (n := 497) (.exec 0x10a9c9 (fun s => s.RIP = 0x10a9c9) (xorR64R64Effect 0x10a9c9 12 11) (Reg.operands [.gpr 12, .gpr 11] [])) #v[494, 296]
    (.letOp (n := 498) (.out 0x10a9cc (movR64R64Effect 0x10a9cc 11 8) (EffectPart.reads (.reg (.gpr 11)) [.gpr 8] []) (.reg (.gpr 11))) #v[488]
    (.letOp (n := 499) (.exec 0x10a9cc (fun s => s.RIP = 0x10a9cc) (movR64R64Effect 0x10a9cc 11 8) (Reg.operands [.gpr 8] [])) #v[488]
    (.letOp (n := 500) (.out 0x10a9cf (shrR64Effect 0x10a9cf 4 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[498]
    (.letOp (n := 501) (.exec 0x10a9cf (fun s => s.RIP = 0x10a9cf) (shrR64Effect 0x10a9cf 4 11 2) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[498]
    (.letOp (n := 502) (.out 0x10a9d3 (xorR64R64Effect 0x10a9d3 11 9) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 9] []) (.reg (.gpr 11))) #v[500, 492]
    (.letOp (n := 503) (.exec 0x10a9d3 (fun s => s.RIP = 0x10a9d3) (xorR64R64Effect 0x10a9d3 11 9) (Reg.operands [.gpr 11, .gpr 9] [])) #v[500, 492]
    (.letOp (n := 504) (.out 0x10a9d6 (andR64R64Effect 0x10a9d6 11 7) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 7] []) (.reg (.gpr 11))) #v[502, 448]
    (.letOp (n := 505) (.exec 0x10a9d6 (fun s => s.RIP = 0x10a9d6) (andR64R64Effect 0x10a9d6 11 7) (Reg.operands [.gpr 11, .gpr 7] [])) #v[502, 448]
    (.letOp (n := 506) (.out 0x10a9d9 (xorR64R64Effect 0x10a9d9 9 11) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 11] []) (.reg (.gpr 9))) #v[492, 504]
    (.letOp (n := 507) (.exec 0x10a9d9 (fun s => s.RIP = 0x10a9d9) (xorR64R64Effect 0x10a9d9 9 11) (Reg.operands [.gpr 9, .gpr 11] [])) #v[492, 504]
    (.letOp (n := 508) (.out 0x10a9dc (addR64R64Effect 0x10a9dc 13 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 13] []) (.reg (.gpr 13))) #v[446, 446]
    (.letOp (n := 509) (.exec 0x10a9dc (fun s => s.RIP = 0x10a9dc) (addR64R64Effect 0x10a9dc 13 13) (Reg.operands [.gpr 13, .gpr 13] [])) #v[446, 446]
    (.letOp (n := 510) (.out 0x10a9df (xorR64R64Effect 0x10a9df 13 1) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 1] []) (.reg (.gpr 13))) #v[508, 384]
    (.letOp (n := 511) (.exec 0x10a9df (fun s => s.RIP = 0x10a9df) (xorR64R64Effect 0x10a9df 13 1) (Reg.operands [.gpr 13, .gpr 1] [])) #v[508, 384]
    (.letOp (n := 512) (.out 0x10a9e2 (movR64R64Effect 0x10a9e2 3 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 12] []) (.reg (.gpr 3))) #v[496]
    (.letOp (n := 513) (.exec 0x10a9e2 (fun s => s.RIP = 0x10a9e2) (movR64R64Effect 0x10a9e2 3 12) (Reg.operands [.gpr 12] [])) #v[496]
    (.letOp (n := 514) (.out 0x10a9e5 (shrR64Effect 0x10a9e5 4 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[512]
    (.letOp (n := 515) (.exec 0x10a9e5 (fun s => s.RIP = 0x10a9e5) (shrR64Effect 0x10a9e5 4 3 2) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[512]
    (.letOp (n := 516) (.out 0x10a9e9 (xorR64R64Effect 0x10a9e9 3 13) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 13] []) (.reg (.gpr 3))) #v[514, 510]
    (.letOp (n := 517) (.exec 0x10a9e9 (fun s => s.RIP = 0x10a9e9) (xorR64R64Effect 0x10a9e9 3 13) (Reg.operands [.gpr 3, .gpr 13] [])) #v[514, 510]
    (.letOp (n := 518) (.out 0x10a9ec (andR64R64Effect 0x10a9ec 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 7] []) (.reg (.gpr 3))) #v[516, 448]
    (.letOp (n := 519) (.exec 0x10a9ec (fun s => s.RIP = 0x10a9ec) (andR64R64Effect 0x10a9ec 3 7) (Reg.operands [.gpr 3, .gpr 7] [])) #v[516, 448]
    (.letOp (n := 520) (.out 0x10a9ef (movR64R64Effect 0x10a9ef 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[506]
    (.letOp (n := 521) (.exec 0x10a9ef (fun s => s.RIP = 0x10a9ef) (movR64R64Effect 0x10a9ef 0 9) (Reg.operands [.gpr 9] [])) #v[506]
    (.letOp (n := 522) (.out 0x10a9f2 (shrR64Effect 0x10a9f2 4 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[520]
    (.letOp (n := 523) (.exec 0x10a9f2 (fun s => s.RIP = 0x10a9f2) (shrR64Effect 0x10a9f2 4 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[520]
    (.letOp (n := 524) (.out 0x10a9f6 (xorR64R64Effect 0x10a9f6 13 3) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 3] []) (.reg (.gpr 13))) #v[510, 518]
    (.letOp (n := 525) (.exec 0x10a9f6 (fun s => s.RIP = 0x10a9f6) (xorR64R64Effect 0x10a9f6 13 3) (Reg.operands [.gpr 13, .gpr 3] [])) #v[510, 518]
    (.letOp (n := 526) (.out 0x10a9f9 (xorR64R64Effect 0x10a9f9 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 13] []) (.reg (.gpr 0))) #v[522, 524]
    (.letOp (n := 527) (.exec 0x10a9f9 (fun s => s.RIP = 0x10a9f9) (xorR64R64Effect 0x10a9f9 0 13) (Reg.operands [.gpr 0, .gpr 13] [])) #v[522, 524]
    (.letOp (n := 528) (.out 0x10a9fc (movR64Imm64Effect 0x10a9fc 1 0xf0f0f0f0f0f0f0f) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 529) (.exec 0x10a9fc (fun s => s.RIP = 0x10a9fc) (movR64Imm64Effect 0x10a9fc 1 0xf0f0f0f0f0f0f0f) (Reg.operands [] [])) #v[]
    (b_l10a6a8_12))))))))))))))))))))))))))))))))))))))))

def bytes_l10a6a8_11 : List UInt8 :=
  [0x4D, 0x01, 0xC9, 0x4C, 0x33, 0x0C, 0x24, 0x4D, 0x01, 0xE4, 0x4D, 0x31, 0xDC, 0x4D, 0x89, 0xC3,
    0x49, 0xC1, 0xEB, 0x02, 0x4D, 0x31, 0xCB, 0x49, 0x21, 0xFB, 0x4D, 0x31, 0xD9, 0x4D, 0x01, 0xED,
    0x49, 0x31, 0xCD, 0x4C, 0x89, 0xE3, 0x48, 0xC1, 0xEB, 0x02, 0x4C, 0x31, 0xEB, 0x48, 0x21, 0xFB,
    0x4C, 0x89, 0xC8, 0x48, 0xC1, 0xE8, 0x04, 0x49, 0x31, 0xDD, 0x4C, 0x31, 0xE8, 0x48, 0xB9, 0x0F,
    0x0F, 0x0F, 0x0F, 0x0F, 0x0F, 0x0F, 0x0F] ++ bytes_l10a6a8_12

theorem code_l10a6a8_11 : ∀ x ∈ codeRange 0x10a9bf bytes_l10a6a8_11, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa9bf 71 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a6a8_12

def b_l10a6a8_10 : Block Op Label signature Reg.count 450 :=
  .letOp (n := 450) (.out 0x10a977 (andR64R64Effect 0x10a977 5 7) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 7] []) (.reg (.gpr 5))) #v[252, 448]
    (.letOp (n := 451) (.exec 0x10a977 (fun s => s.RIP = 0x10a977) (andR64R64Effect 0x10a977 5 7) (Reg.operands [.gpr 5, .gpr 7] [])) #v[252, 448]
    (.letOp (n := 452) (.out 0x10a97a (xorR64R64Effect 0x10a97a 3 5) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 5] []) (.reg (.gpr 3))) #v[250, 450]
    (.letOp (n := 453) (.exec 0x10a97a (fun s => s.RIP = 0x10a97a) (xorR64R64Effect 0x10a97a 3 5) (Reg.operands [.gpr 3, .gpr 5] [])) #v[250, 450]
    (.letOp (n := 454) (.out 0x10a97d (movR64R64Effect 0x10a97d 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3] []) (.reg (.gpr 2))) #v[452]
    (.letOp (n := 455) (.exec 0x10a97d (fun s => s.RIP = 0x10a97d) (movR64R64Effect 0x10a97d 2 3) (Reg.operands [.gpr 3] [])) #v[452]
    (.letOp (n := 456) (.out 0x10a980 (shrR64Effect 0x10a980 4 2 4) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[454]
    (.letOp (n := 457) (.exec 0x10a980 (fun s => s.RIP = 0x10a980) (shrR64Effect 0x10a980 4 2 4) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[454]
    (.letOp (n := 458) (.out 0x10a984 (xorR64R64Effect 0x10a984 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 12] []) (.reg (.gpr 6))) #v[340, 432]
    (.letOp (n := 459) (.exec 0x10a984 (fun s => s.RIP = 0x10a984) (xorR64R64Effect 0x10a984 6 12) (Reg.operands [.gpr 6, .gpr 12] [])) #v[340, 432]
    (.letOp (n := 460) (.out 0x10a987 (movR64R64Effect 0x10a987 15 6) (EffectPart.reads (.reg (.gpr 15)) [.gpr 6] []) (.reg (.gpr 15))) #v[458]
    (.letOp (n := 461) (.exec 0x10a987 (fun s => s.RIP = 0x10a987) (movR64R64Effect 0x10a987 15 6) (Reg.operands [.gpr 6] [])) #v[458]
    (.letOp (n := 462) (.out 0x10a98a (shrR64Effect 0x10a98a 4 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[460]
    (.letOp (n := 463) (.exec 0x10a98a (fun s => s.RIP = 0x10a98a) (shrR64Effect 0x10a98a 4 15 2) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[460]
    (.letOp (n := 464) (.out 0x10a98e (xorR64R64Effect 0x10a98e 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 13] []) (.reg (.gpr 0))) #v[438, 446]
    (.letOp (n := 465) (.exec 0x10a98e (fun s => s.RIP = 0x10a98e) (xorR64R64Effect 0x10a98e 0 13) (Reg.operands [.gpr 0, .gpr 13] [])) #v[438, 446]
    (.letOp (n := 466) (.out 0x10a991 (xorR64R64Effect 0x10a991 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 0] []) (.reg (.gpr 15))) #v[462, 464]
    (.letOp (n := 467) (.exec 0x10a991 (fun s => s.RIP = 0x10a991) (xorR64R64Effect 0x10a991 15 0) (Reg.operands [.gpr 15, .gpr 0] [])) #v[462, 464]
    (.letOp (n := 468) (.out 0x10a994 (andR64R64Effect 0x10a994 15 7) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 7] []) (.reg (.gpr 15))) #v[466, 448]
    (.letOp (n := 469) (.exec 0x10a994 (fun s => s.RIP = 0x10a994) (andR64R64Effect 0x10a994 15 7) (Reg.operands [.gpr 15, .gpr 7] [])) #v[466, 448]
    (.letOp (n := 470) (.out 0x10a997 (xorR64R64Effect 0x10a997 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 15] []) (.reg (.gpr 0))) #v[464, 468]
    (.letOp (n := 471) (.exec 0x10a997 (fun s => s.RIP = 0x10a997) (xorR64R64Effect 0x10a997 0 15) (Reg.operands [.gpr 0, .gpr 15] [])) #v[464, 468]
    (.letOp (n := 472) (.out 0x10a99a (xorR64R64Effect 0x10a99a 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[456, 470]
    (.letOp (n := 473) (.exec 0x10a99a (fun s => s.RIP = 0x10a99a) (xorR64R64Effect 0x10a99a 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[456, 470]
    (.letOp (n := 474) (.out 0x10a99d (movR64Imm64Effect 0x10a99d 10 0xf0f0f0f0f0f0f0f) (EffectPart.reads (.reg (.gpr 10)) [] []) (.reg (.gpr 10))) #v[]
    (.letOp (n := 475) (.exec 0x10a99d (fun s => s.RIP = 0x10a99d) (movR64Imm64Effect 0x10a99d 10 0xf0f0f0f0f0f0f0f) (Reg.operands [] [])) #v[]
    (.letOp (n := 476) (.out 0x10a9a7 (andR64R64Effect 0x10a9a7 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 10] []) (.reg (.gpr 2))) #v[472, 474]
    (.letOp (n := 477) (.exec 0x10a9a7 (fun s => s.RIP = 0x10a9a7) (andR64R64Effect 0x10a9a7 2 10) (Reg.operands [.gpr 2, .gpr 10] [])) #v[472, 474]
    (.letOp (n := 478) (.out 0x10a9aa (movR64R64Effect 0x10a9aa 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[476]
    (.letOp (n := 479) (.exec 0x10a9aa (fun s => s.RIP = 0x10a9aa) (movR64R64Effect 0x10a9aa 10 2) (Reg.operands [.gpr 2] [])) #v[476]
    (.letOp (n := 480) (.out 0x10a9ad (shlR64Effect 0x10a9ad 4 10 4) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[478]
    (.letOp (n := 481) (.exec 0x10a9ad (fun s => s.RIP = 0x10a9ad) (shlR64Effect 0x10a9ad 4 10 4) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[478]
    (.letOp (n := 482) (.out 0x10a9b1 (xorR64R64Effect 0x10a9b1 10 3) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 3] []) (.reg (.gpr 10))) #v[480, 452]
    (.letOp (n := 483) (.exec 0x10a9b1 (fun s => s.RIP = 0x10a9b1) (xorR64R64Effect 0x10a9b1 10 3) (Reg.operands [.gpr 10, .gpr 3] [])) #v[480, 452]
    (.letOp (n := 484) (.out 0x10a9b4 (xorR64R64Effect 0x10a9b4 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[476, 470]
    (.letOp (n := 485) (.exec 0x10a9b4 (fun s => s.RIP = 0x10a9b4) (xorR64R64Effect 0x10a9b4 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[476, 470]
    (.letOp (n := 486) (.out 0x10a9b7 (addR64R64Effect 0x10a9b7 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 8] []) (.reg (.gpr 8))) #v[148, 148]
    (.letOp (n := 487) (.exec 0x10a9b7 (fun s => s.RIP = 0x10a9b7) (addR64R64Effect 0x10a9b7 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[148, 148]
    (.letOp (n := 488) (.out 0x10a9ba (xorR64M64Effect 0x10a9ba 8 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 4] []) (.reg (.gpr 8))) #v[486, 4]
    (.letOp (n := 489) (.exec 0x10a9ba (LoadPre 0x10a9ba (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10a9ba + BitVec.ofNat 64 5)) 8) (xorR64M64Effect 0x10a9ba 8 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[486, 4]
    (b_l10a6a8_11))))))))))))))))))))))))))))))))))))))))

def bytes_l10a6a8_10 : List UInt8 :=
  [0x48, 0x21, 0xFD, 0x48, 0x31, 0xEB, 0x48, 0x89, 0xDA, 0x48, 0xC1, 0xEA, 0x04, 0x4C, 0x31, 0xE6,
    0x49, 0x89, 0xF7, 0x49, 0xC1, 0xEF, 0x02, 0x4C, 0x31, 0xE8, 0x49, 0x31, 0xC7, 0x49, 0x21, 0xFF,
    0x4C, 0x31, 0xF8, 0x48, 0x31, 0xC2, 0x49, 0xBA, 0x0F, 0x0F, 0x0F, 0x0F, 0x0F, 0x0F, 0x0F, 0x0F,
    0x4C, 0x21, 0xD2, 0x49, 0x89, 0xD2, 0x49, 0xC1, 0xE2, 0x04, 0x49, 0x31, 0xDA, 0x48, 0x31, 0xC2,
    0x4D, 0x01, 0xC0, 0x4C, 0x33, 0x44, 0x24, 0x08] ++ bytes_l10a6a8_11

theorem code_l10a6a8_10 : ∀ x ∈ codeRange 0x10a977 bytes_l10a6a8_10, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa977 72 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a6a8_11

def b_l10a6a8_9 : Block Op Label signature Reg.count 410 :=
  .letOp (n := 410) (.out 0x10a92e (shlR32Effect 0x10a92e 3 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[408]
    (.letOp (n := 411) (.exec 0x10a92e (fun s => s.RIP = 0x10a92e) (shlR32Effect 0x10a92e 3 0 8) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[408]
    (.letOp (n := 412) (.out 0x10a931 (orR64R64Effect 0x10a931 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[410, 406]
    (.letOp (n := 413) (.exec 0x10a931 (fun s => s.RIP = 0x10a931) (orR64R64Effect 0x10a931 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[410, 406]
    (.letOp (n := 414) (.out 0x10a934 (movzxR32M8Effect 0x10a934 4 7 (.base 2 (.d8 0x3d))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[2]
    (.letOp (n := 415) (.exec 0x10a934 (LoadPre 0x10a934 (fun s => AddrMode.addr (.base 2 (.d8 0x3d)) s (0x10a934 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a934 4 7 (.base 2 (.d8 0x3d))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 416) (.out 0x10a938 (shlR32Effect 0x10a938 3 7 24) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[414]
    (.letOp (n := 417) (.exec 0x10a938 (fun s => s.RIP = 0x10a938) (shlR32Effect 0x10a938 3 7 24) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[414]
    (.letOp (n := 418) (.out 0x10a93b (orR64R64Effect 0x10a93b 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[416, 412]
    (.letOp (n := 419) (.exec 0x10a93b (fun s => s.RIP = 0x10a93b) (orR64R64Effect 0x10a93b 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[416, 412]
    (.letOp (n := 420) (.out 0x10a93e (movzxR32M8Effect 0x10a93e 5 15 (.base 2 (.d8 0x3e))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[2]
    (.letOp (n := 421) (.exec 0x10a93e (LoadPre 0x10a93e (fun s => AddrMode.addr (.base 2 (.d8 0x3e)) s (0x10a93e + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10a93e 5 15 (.base 2 (.d8 0x3e))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 422) (.out 0x10a943 (shlR64Effect 0x10a943 4 15 40) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[420]
    (.letOp (n := 423) (.exec 0x10a943 (fun s => s.RIP = 0x10a943) (shlR64Effect 0x10a943 4 15 40) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[420]
    (.letOp (n := 424) (.out 0x10a947 (orR64R64Effect 0x10a947 15 7) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 7] []) (.reg (.gpr 15))) #v[422, 418]
    (.letOp (n := 425) (.exec 0x10a947 (fun s => s.RIP = 0x10a947) (orR64R64Effect 0x10a947 15 7) (Reg.operands [.gpr 15, .gpr 7] [])) #v[422, 418]
    (.letOp (n := 426) (.out 0x10a94a (movR64R64Effect 0x10a94a 12 11) (EffectPart.reads (.reg (.gpr 12)) [.gpr 11] []) (.reg (.gpr 12))) #v[296]
    (.letOp (n := 427) (.exec 0x10a94a (fun s => s.RIP = 0x10a94a) (movR64R64Effect 0x10a94a 12 11) (Reg.operands [.gpr 11] [])) #v[296]
    (.letOp (n := 428) (.out 0x10a94d (shrR64Effect 0x10a94d 3 12 1) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[426]
    (.letOp (n := 429) (.exec 0x10a94d (fun s => s.RIP = 0x10a94d) (shrR64Effect 0x10a94d 3 12 1) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[426]
    (.letOp (n := 430) (.out 0x10a950 (xorR64R64Effect 0x10a950 12 6) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 6] []) (.reg (.gpr 12))) #v[428, 340]
    (.letOp (n := 431) (.exec 0x10a950 (fun s => s.RIP = 0x10a950) (xorR64R64Effect 0x10a950 12 6) (Reg.operands [.gpr 12, .gpr 6] [])) #v[428, 340]
    (.letOp (n := 432) (.out 0x10a953 (andR64R64Effect 0x10a953 12 10) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 10] []) (.reg (.gpr 12))) #v[430, 146]
    (.letOp (n := 433) (.exec 0x10a953 (fun s => s.RIP = 0x10a953) (andR64R64Effect 0x10a953 12 10) (Reg.operands [.gpr 12, .gpr 10] [])) #v[430, 146]
    (.letOp (n := 434) (.out 0x10a956 (movzxR32M8Effect 0x10a956 4 0 (.base 2 (.d8 0x3f))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 435) (.exec 0x10a956 (LoadPre 0x10a956 (fun s => AddrMode.addr (.base 2 (.d8 0x3f)) s (0x10a956 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a956 4 0 (.base 2 (.d8 0x3f))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 436) (.out 0x10a95a (shlR64Effect 0x10a95a 4 0 56) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[434]
    (.letOp (n := 437) (.exec 0x10a95a (fun s => s.RIP = 0x10a95a) (shlR64Effect 0x10a95a 4 0 56) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[434]
    (.letOp (n := 438) (.out 0x10a95e (orR64R64Effect 0x10a95e 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 15] []) (.reg (.gpr 0))) #v[436, 424]
    (.letOp (n := 439) (.exec 0x10a95e (fun s => s.RIP = 0x10a95e) (orR64R64Effect 0x10a95e 0 15) (Reg.operands [.gpr 0, .gpr 15] [])) #v[436, 424]
    (.letOp (n := 440) (.out 0x10a961 (movR64R64Effect 0x10a961 13 1) (EffectPart.reads (.reg (.gpr 13)) [.gpr 1] []) (.reg (.gpr 13))) #v[384]
    (.letOp (n := 441) (.exec 0x10a961 (fun s => s.RIP = 0x10a961) (movR64R64Effect 0x10a961 13 1) (Reg.operands [.gpr 1] [])) #v[384]
    (.letOp (n := 442) (.out 0x10a964 (shrR64Effect 0x10a964 3 13 1) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[440]
    (.letOp (n := 443) (.exec 0x10a964 (fun s => s.RIP = 0x10a964) (shrR64Effect 0x10a964 3 13 1) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[440]
    (.letOp (n := 444) (.out 0x10a967 (xorR64R64Effect 0x10a967 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 0] []) (.reg (.gpr 13))) #v[442, 438]
    (.letOp (n := 445) (.exec 0x10a967 (fun s => s.RIP = 0x10a967) (xorR64R64Effect 0x10a967 13 0) (Reg.operands [.gpr 13, .gpr 0] [])) #v[442, 438]
    (.letOp (n := 446) (.out 0x10a96a (andR64R64Effect 0x10a96a 13 10) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 10] []) (.reg (.gpr 13))) #v[444, 146]
    (.letOp (n := 447) (.exec 0x10a96a (fun s => s.RIP = 0x10a96a) (andR64R64Effect 0x10a96a 13 10) (Reg.operands [.gpr 13, .gpr 10] [])) #v[444, 146]
    (.letOp (n := 448) (.out 0x10a96d (movR64Imm64Effect 0x10a96d 7 0x3333333333333333) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 449) (.exec 0x10a96d (fun s => s.RIP = 0x10a96d) (movR64Imm64Effect 0x10a96d 7 0x3333333333333333) (Reg.operands [] [])) #v[]
    (b_l10a6a8_10))))))))))))))))))))))))))))))))))))))))

def bytes_l10a6a8_9 : List UInt8 :=
  [0xC1, 0xE0, 0x08, 0x48, 0x09, 0xF8, 0x0F, 0xB6, 0x7A, 0x3D, 0xC1, 0xE7, 0x18, 0x48, 0x09, 0xC7,
    0x44, 0x0F, 0xB6, 0x7A, 0x3E, 0x49, 0xC1, 0xE7, 0x28, 0x49, 0x09, 0xFF, 0x4D, 0x89, 0xDC, 0x49,
    0xD1, 0xEC, 0x49, 0x31, 0xF4, 0x4D, 0x21, 0xD4, 0x0F, 0xB6, 0x42, 0x3F, 0x48, 0xC1, 0xE0, 0x38,
    0x4C, 0x09, 0xF8, 0x49, 0x89, 0xCD, 0x49, 0xD1, 0xED, 0x49, 0x31, 0xC5, 0x4D, 0x21, 0xD5, 0x48,
    0xBF, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33] ++ bytes_l10a6a8_10

theorem code_l10a6a8_9 : ∀ x ∈ codeRange 0x10a92e bytes_l10a6a8_9, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa92e 73 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a6a8_10

def b_l10a6a8_8 : Block Op Label signature Reg.count 370 :=
  .letOp (n := 370) (.out 0x10a8e7 (shlR32Effect 0x10a8e7 3 1 24) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[368]
    (.letOp (n := 371) (.exec 0x10a8e7 (fun s => s.RIP = 0x10a8e7) (shlR32Effect 0x10a8e7 3 1 24) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[368]
    (.letOp (n := 372) (.out 0x10a8ea (orR64R64Effect 0x10a8ea 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[370, 366]
    (.letOp (n := 373) (.exec 0x10a8ea (fun s => s.RIP = 0x10a8ea) (orR64R64Effect 0x10a8ea 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[370, 366]
    (.letOp (n := 374) (.out 0x10a8ed (movzxR32M8Effect 0x10a8ed 4 0 (.base 2 (.d8 0x2e))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 375) (.exec 0x10a8ed (LoadPre 0x10a8ed (fun s => AddrMode.addr (.base 2 (.d8 0x2e)) s (0x10a8ed + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a8ed 4 0 (.base 2 (.d8 0x2e))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 376) (.out 0x10a8f1 (shlR64Effect 0x10a8f1 4 0 40) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[374]
    (.letOp (n := 377) (.exec 0x10a8f1 (fun s => s.RIP = 0x10a8f1) (shlR64Effect 0x10a8f1 4 0 40) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[374]
    (.letOp (n := 378) (.out 0x10a8f5 (orR64R64Effect 0x10a8f5 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[376, 372]
    (.letOp (n := 379) (.exec 0x10a8f5 (fun s => s.RIP = 0x10a8f5) (orR64R64Effect 0x10a8f5 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[376, 372]
    (.letOp (n := 380) (.out 0x10a8f8 (movzxR32M8Effect 0x10a8f8 4 1 (.base 2 (.d8 0x2f))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2]
    (.letOp (n := 381) (.exec 0x10a8f8 (LoadPre 0x10a8f8 (fun s => AddrMode.addr (.base 2 (.d8 0x2f)) s (0x10a8f8 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a8f8 4 1 (.base 2 (.d8 0x2f))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 382) (.out 0x10a8fc (shlR64Effect 0x10a8fc 4 1 56) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[380]
    (.letOp (n := 383) (.exec 0x10a8fc (fun s => s.RIP = 0x10a8fc) (shlR64Effect 0x10a8fc 4 1 56) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[380]
    (.letOp (n := 384) (.out 0x10a900 (orR64R64Effect 0x10a900 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[382, 378]
    (.letOp (n := 385) (.exec 0x10a900 (fun s => s.RIP = 0x10a900) (orR64R64Effect 0x10a900 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[382, 378]
    (.letOp (n := 386) (.out 0x10a903 (movzxR32M8Effect 0x10a903 4 0 (.base 2 (.d8 0x35))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 387) (.exec 0x10a903 (LoadPre 0x10a903 (fun s => AddrMode.addr (.base 2 (.d8 0x35)) s (0x10a903 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a903 4 0 (.base 2 (.d8 0x35))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 388) (.out 0x10a907 (shlR32Effect 0x10a907 3 0 16) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[386]
    (.letOp (n := 389) (.exec 0x10a907 (fun s => s.RIP = 0x10a907) (shlR32Effect 0x10a907 3 0 16) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[386]
    (.letOp (n := 390) (.out 0x10a90a (movR64R64Effect 0x10a90a 14 7) (EffectPart.reads (.reg (.gpr 14)) [.gpr 7] []) (.reg (.gpr 14))) #v[7]
    (.letOp (n := 391) (.exec 0x10a90a (fun s => s.RIP = 0x10a90a) (movR64R64Effect 0x10a90a 14 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 392) (.out 0x10a90d (movzxR32M8Effect 0x10a90d 4 7 (.base 2 (.d8 0x34))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[2]
    (.letOp (n := 393) (.exec 0x10a90d (LoadPre 0x10a90d (fun s => AddrMode.addr (.base 2 (.d8 0x34)) s (0x10a90d + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a90d 4 7 (.base 2 (.d8 0x34))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 394) (.out 0x10a911 (orR64R64Effect 0x10a911 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[392, 388]
    (.letOp (n := 395) (.exec 0x10a911 (fun s => s.RIP = 0x10a911) (orR64R64Effect 0x10a911 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[392, 388]
    (.letOp (n := 396) (.out 0x10a914 (movzxR32M8Effect 0x10a914 4 0 (.base 2 (.d8 0x36))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 397) (.exec 0x10a914 (LoadPre 0x10a914 (fun s => AddrMode.addr (.base 2 (.d8 0x36)) s (0x10a914 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a914 4 0 (.base 2 (.d8 0x36))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 398) (.out 0x10a918 (shlR64Effect 0x10a918 4 0 32) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[396]
    (.letOp (n := 399) (.exec 0x10a918 (fun s => s.RIP = 0x10a918) (shlR64Effect 0x10a918 4 0 32) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[396]
    (.letOp (n := 400) (.out 0x10a91c (orR64R64Effect 0x10a91c 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[398, 394]
    (.letOp (n := 401) (.exec 0x10a91c (fun s => s.RIP = 0x10a91c) (orR64R64Effect 0x10a91c 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[398, 394]
    (.letOp (n := 402) (.out 0x10a91f (movzxR32M8Effect 0x10a91f 4 7 (.base 2 (.d8 0x37))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[2]
    (.letOp (n := 403) (.exec 0x10a91f (LoadPre 0x10a91f (fun s => AddrMode.addr (.base 2 (.d8 0x37)) s (0x10a91f + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a91f 4 7 (.base 2 (.d8 0x37))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 404) (.out 0x10a923 (shlR64Effect 0x10a923 4 7 48) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[402]
    (.letOp (n := 405) (.exec 0x10a923 (fun s => s.RIP = 0x10a923) (shlR64Effect 0x10a923 4 7 48) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[402]
    (.letOp (n := 406) (.out 0x10a927 (orR64R64Effect 0x10a927 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[404, 400]
    (.letOp (n := 407) (.exec 0x10a927 (fun s => s.RIP = 0x10a927) (orR64R64Effect 0x10a927 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[404, 400]
    (.letOp (n := 408) (.out 0x10a92a (movzxR32M8Effect 0x10a92a 4 0 (.base 2 (.d8 0x3c))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 409) (.exec 0x10a92a (LoadPre 0x10a92a (fun s => AddrMode.addr (.base 2 (.d8 0x3c)) s (0x10a92a + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a92a 4 0 (.base 2 (.d8 0x3c))) (Reg.operands [.gpr 2] [])) #v[2]
    (b_l10a6a8_9))))))))))))))))))))))))))))))))))))))))

def bytes_l10a6a8_8 : List UInt8 :=
  [0xC1, 0xE1, 0x18, 0x48, 0x09, 0xC1, 0x0F, 0xB6, 0x42, 0x2E, 0x48, 0xC1, 0xE0, 0x28, 0x48, 0x09,
    0xC8, 0x0F, 0xB6, 0x4A, 0x2F, 0x48, 0xC1, 0xE1, 0x38, 0x48, 0x09, 0xC1, 0x0F, 0xB6, 0x42, 0x35,
    0xC1, 0xE0, 0x10, 0x49, 0x89, 0xFE, 0x0F, 0xB6, 0x7A, 0x34, 0x48, 0x09, 0xC7, 0x0F, 0xB6, 0x42,
    0x36, 0x48, 0xC1, 0xE0, 0x20, 0x48, 0x09, 0xF8, 0x0F, 0xB6, 0x7A, 0x37, 0x48, 0xC1, 0xE7, 0x30,
    0x48, 0x09, 0xC7, 0x0F, 0xB6, 0x42, 0x3C] ++ bytes_l10a6a8_9

theorem code_l10a6a8_8 : ∀ x ∈ codeRange 0x10a8e7 bytes_l10a6a8_8, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa8e7 71 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a6a8_9

def b_l10a6a8_7 : Block Op Label signature Reg.count 330 :=
  .letOp (n := 330) (.out 0x10a89f (movzxR32M8Effect 0x10a89f 4 0 (.base 2 (.d8 0x1e))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 331) (.exec 0x10a89f (LoadPre 0x10a89f (fun s => AddrMode.addr (.base 2 (.d8 0x1e)) s (0x10a89f + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a89f 4 0 (.base 2 (.d8 0x1e))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 332) (.out 0x10a8a3 (shlR64Effect 0x10a8a3 4 0 40) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[330]
    (.letOp (n := 333) (.exec 0x10a8a3 (fun s => s.RIP = 0x10a8a3) (shlR64Effect 0x10a8a3 4 0 40) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[330]
    (.letOp (n := 334) (.out 0x10a8a7 (orR64R64Effect 0x10a8a7 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[332, 328]
    (.letOp (n := 335) (.exec 0x10a8a7 (fun s => s.RIP = 0x10a8a7) (orR64R64Effect 0x10a8a7 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[332, 328]
    (.letOp (n := 336) (.out 0x10a8aa (movzxR32M8Effect 0x10a8aa 4 6 (.base 2 (.d8 0x1f))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[2]
    (.letOp (n := 337) (.exec 0x10a8aa (LoadPre 0x10a8aa (fun s => AddrMode.addr (.base 2 (.d8 0x1f)) s (0x10a8aa + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a8aa 4 6 (.base 2 (.d8 0x1f))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 338) (.out 0x10a8ae (shlR64Effect 0x10a8ae 4 6 56) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[336]
    (.letOp (n := 339) (.exec 0x10a8ae (fun s => s.RIP = 0x10a8ae) (shlR64Effect 0x10a8ae 4 6 56) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[336]
    (.letOp (n := 340) (.out 0x10a8b2 (orR64R64Effect 0x10a8b2 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[338, 334]
    (.letOp (n := 341) (.exec 0x10a8b2 (fun s => s.RIP = 0x10a8b2) (orR64R64Effect 0x10a8b2 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[338, 334]
    (.letOp (n := 342) (.out 0x10a8b5 (movzxR32M8Effect 0x10a8b5 4 0 (.base 2 (.d8 0x25))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 343) (.exec 0x10a8b5 (LoadPre 0x10a8b5 (fun s => AddrMode.addr (.base 2 (.d8 0x25)) s (0x10a8b5 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a8b5 4 0 (.base 2 (.d8 0x25))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 344) (.out 0x10a8b9 (shlR32Effect 0x10a8b9 3 0 16) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[342]
    (.letOp (n := 345) (.exec 0x10a8b9 (fun s => s.RIP = 0x10a8b9) (shlR32Effect 0x10a8b9 3 0 16) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[342]
    (.letOp (n := 346) (.out 0x10a8bc (movzxR32M8Effect 0x10a8bc 4 1 (.base 2 (.d8 0x24))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2]
    (.letOp (n := 347) (.exec 0x10a8bc (LoadPre 0x10a8bc (fun s => AddrMode.addr (.base 2 (.d8 0x24)) s (0x10a8bc + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a8bc 4 1 (.base 2 (.d8 0x24))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 348) (.out 0x10a8c0 (orR64R64Effect 0x10a8c0 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[346, 344]
    (.letOp (n := 349) (.exec 0x10a8c0 (fun s => s.RIP = 0x10a8c0) (orR64R64Effect 0x10a8c0 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[346, 344]
    (.letOp (n := 350) (.out 0x10a8c3 (movzxR32M8Effect 0x10a8c3 4 0 (.base 2 (.d8 0x26))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 351) (.exec 0x10a8c3 (LoadPre 0x10a8c3 (fun s => AddrMode.addr (.base 2 (.d8 0x26)) s (0x10a8c3 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a8c3 4 0 (.base 2 (.d8 0x26))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 352) (.out 0x10a8c7 (shlR64Effect 0x10a8c7 4 0 32) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[350]
    (.letOp (n := 353) (.exec 0x10a8c7 (fun s => s.RIP = 0x10a8c7) (shlR64Effect 0x10a8c7 4 0 32) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[350]
    (.letOp (n := 354) (.out 0x10a8cb (orR64R64Effect 0x10a8cb 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[352, 348]
    (.letOp (n := 355) (.exec 0x10a8cb (fun s => s.RIP = 0x10a8cb) (orR64R64Effect 0x10a8cb 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[352, 348]
    (.letOp (n := 356) (.out 0x10a8ce (movzxR32M8Effect 0x10a8ce 4 1 (.base 2 (.d8 0x27))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2]
    (.letOp (n := 357) (.exec 0x10a8ce (LoadPre 0x10a8ce (fun s => AddrMode.addr (.base 2 (.d8 0x27)) s (0x10a8ce + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a8ce 4 1 (.base 2 (.d8 0x27))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 358) (.out 0x10a8d2 (shlR64Effect 0x10a8d2 4 1 48) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[356]
    (.letOp (n := 359) (.exec 0x10a8d2 (fun s => s.RIP = 0x10a8d2) (shlR64Effect 0x10a8d2 4 1 48) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[356]
    (.letOp (n := 360) (.out 0x10a8d6 (orR64R64Effect 0x10a8d6 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[358, 354]
    (.letOp (n := 361) (.exec 0x10a8d6 (fun s => s.RIP = 0x10a8d6) (orR64R64Effect 0x10a8d6 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[358, 354]
    (.letOp (n := 362) (.out 0x10a8d9 (movzxR32M8Effect 0x10a8d9 4 0 (.base 2 (.d8 0x2c))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 363) (.exec 0x10a8d9 (LoadPre 0x10a8d9 (fun s => AddrMode.addr (.base 2 (.d8 0x2c)) s (0x10a8d9 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a8d9 4 0 (.base 2 (.d8 0x2c))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 364) (.out 0x10a8dd (shlR32Effect 0x10a8dd 3 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[362]
    (.letOp (n := 365) (.exec 0x10a8dd (fun s => s.RIP = 0x10a8dd) (shlR32Effect 0x10a8dd 3 0 8) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[362]
    (.letOp (n := 366) (.out 0x10a8e0 (orR64R64Effect 0x10a8e0 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[364, 360]
    (.letOp (n := 367) (.exec 0x10a8e0 (fun s => s.RIP = 0x10a8e0) (orR64R64Effect 0x10a8e0 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[364, 360]
    (.letOp (n := 368) (.out 0x10a8e3 (movzxR32M8Effect 0x10a8e3 4 1 (.base 2 (.d8 0x2d))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2]
    (.letOp (n := 369) (.exec 0x10a8e3 (LoadPre 0x10a8e3 (fun s => AddrMode.addr (.base 2 (.d8 0x2d)) s (0x10a8e3 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a8e3 4 1 (.base 2 (.d8 0x2d))) (Reg.operands [.gpr 2] [])) #v[2]
    (b_l10a6a8_8))))))))))))))))))))))))))))))))))))))))

def bytes_l10a6a8_7 : List UInt8 :=
  [0x0F, 0xB6, 0x42, 0x1E, 0x48, 0xC1, 0xE0, 0x28, 0x48, 0x09, 0xC8, 0x0F, 0xB6, 0x72, 0x1F, 0x48,
    0xC1, 0xE6, 0x38, 0x48, 0x09, 0xC6, 0x0F, 0xB6, 0x42, 0x25, 0xC1, 0xE0, 0x10, 0x0F, 0xB6, 0x4A,
    0x24, 0x48, 0x09, 0xC1, 0x0F, 0xB6, 0x42, 0x26, 0x48, 0xC1, 0xE0, 0x20, 0x48, 0x09, 0xC8, 0x0F,
    0xB6, 0x4A, 0x27, 0x48, 0xC1, 0xE1, 0x30, 0x48, 0x09, 0xC1, 0x0F, 0xB6, 0x42, 0x2C, 0xC1, 0xE0,
    0x08, 0x48, 0x09, 0xC8, 0x0F, 0xB6, 0x4A, 0x2D] ++ bytes_l10a6a8_8

theorem code_l10a6a8_7 : ∀ x ∈ codeRange 0x10a89f bytes_l10a6a8_7, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa89f 72 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a6a8_8

def b_l10a6a8_6 : Block Op Label signature Reg.count 290 :=
  .letOp (n := 290) (.out 0x10a858 (orR64R64Effect 0x10a858 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[288, 284]
    (.letOp (n := 291) (.exec 0x10a858 (fun s => s.RIP = 0x10a858) (orR64R64Effect 0x10a858 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[288, 284]
    (.letOp (n := 292) (.out 0x10a85b (movzxR32M8Effect 0x10a85b 5 11 (.base 2 (.d8 0xf))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[2]
    (.letOp (n := 293) (.exec 0x10a85b (LoadPre 0x10a85b (fun s => AddrMode.addr (.base 2 (.d8 0xf)) s (0x10a85b + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10a85b 5 11 (.base 2 (.d8 0xf))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 294) (.out 0x10a860 (shlR64Effect 0x10a860 4 11 56) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[292]
    (.letOp (n := 295) (.exec 0x10a860 (fun s => s.RIP = 0x10a860) (shlR64Effect 0x10a860 4 11 56) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[292]
    (.letOp (n := 296) (.out 0x10a864 (orR64R64Effect 0x10a864 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0] []) (.reg (.gpr 11))) #v[294, 290]
    (.letOp (n := 297) (.exec 0x10a864 (fun s => s.RIP = 0x10a864) (orR64R64Effect 0x10a864 11 0) (Reg.operands [.gpr 11, .gpr 0] [])) #v[294, 290]
    (.letOp (n := 298) (.out 0x10a867 (movzxR32M8Effect 0x10a867 4 0 (.base 2 (.d8 0x15))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 299) (.exec 0x10a867 (LoadPre 0x10a867 (fun s => AddrMode.addr (.base 2 (.d8 0x15)) s (0x10a867 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a867 4 0 (.base 2 (.d8 0x15))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 300) (.out 0x10a86b (shlR32Effect 0x10a86b 3 0 16) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[298]
    (.letOp (n := 301) (.exec 0x10a86b (fun s => s.RIP = 0x10a86b) (shlR32Effect 0x10a86b 3 0 16) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[298]
    (.letOp (n := 302) (.out 0x10a86e (movzxR32M8Effect 0x10a86e 4 1 (.base 2 (.d8 0x14))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2]
    (.letOp (n := 303) (.exec 0x10a86e (LoadPre 0x10a86e (fun s => AddrMode.addr (.base 2 (.d8 0x14)) s (0x10a86e + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a86e 4 1 (.base 2 (.d8 0x14))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 304) (.out 0x10a872 (orR64R64Effect 0x10a872 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[302, 300]
    (.letOp (n := 305) (.exec 0x10a872 (fun s => s.RIP = 0x10a872) (orR64R64Effect 0x10a872 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[302, 300]
    (.letOp (n := 306) (.out 0x10a875 (movzxR32M8Effect 0x10a875 4 0 (.base 2 (.d8 0x16))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 307) (.exec 0x10a875 (LoadPre 0x10a875 (fun s => AddrMode.addr (.base 2 (.d8 0x16)) s (0x10a875 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a875 4 0 (.base 2 (.d8 0x16))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 308) (.out 0x10a879 (shlR64Effect 0x10a879 4 0 32) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[306]
    (.letOp (n := 309) (.exec 0x10a879 (fun s => s.RIP = 0x10a879) (shlR64Effect 0x10a879 4 0 32) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[306]
    (.letOp (n := 310) (.out 0x10a87d (orR64R64Effect 0x10a87d 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[308, 304]
    (.letOp (n := 311) (.exec 0x10a87d (fun s => s.RIP = 0x10a87d) (orR64R64Effect 0x10a87d 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[308, 304]
    (.letOp (n := 312) (.out 0x10a880 (movzxR32M8Effect 0x10a880 4 1 (.base 2 (.d8 0x17))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2]
    (.letOp (n := 313) (.exec 0x10a880 (LoadPre 0x10a880 (fun s => AddrMode.addr (.base 2 (.d8 0x17)) s (0x10a880 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a880 4 1 (.base 2 (.d8 0x17))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 314) (.out 0x10a884 (shlR64Effect 0x10a884 4 1 48) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[312]
    (.letOp (n := 315) (.exec 0x10a884 (fun s => s.RIP = 0x10a884) (shlR64Effect 0x10a884 4 1 48) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[312]
    (.letOp (n := 316) (.out 0x10a888 (orR64R64Effect 0x10a888 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[314, 310]
    (.letOp (n := 317) (.exec 0x10a888 (fun s => s.RIP = 0x10a888) (orR64R64Effect 0x10a888 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[314, 310]
    (.letOp (n := 318) (.out 0x10a88b (movzxR32M8Effect 0x10a88b 4 0 (.base 2 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 319) (.exec 0x10a88b (LoadPre 0x10a88b (fun s => AddrMode.addr (.base 2 (.d8 0x1c)) s (0x10a88b + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a88b 4 0 (.base 2 (.d8 0x1c))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 320) (.out 0x10a88f (shlR32Effect 0x10a88f 3 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[318]
    (.letOp (n := 321) (.exec 0x10a88f (fun s => s.RIP = 0x10a88f) (shlR32Effect 0x10a88f 3 0 8) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[318]
    (.letOp (n := 322) (.out 0x10a892 (orR64R64Effect 0x10a892 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[320, 316]
    (.letOp (n := 323) (.exec 0x10a892 (fun s => s.RIP = 0x10a892) (orR64R64Effect 0x10a892 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[320, 316]
    (.letOp (n := 324) (.out 0x10a895 (movzxR32M8Effect 0x10a895 4 1 (.base 2 (.d8 0x1d))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2]
    (.letOp (n := 325) (.exec 0x10a895 (LoadPre 0x10a895 (fun s => AddrMode.addr (.base 2 (.d8 0x1d)) s (0x10a895 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a895 4 1 (.base 2 (.d8 0x1d))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 326) (.out 0x10a899 (shlR32Effect 0x10a899 3 1 24) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[324]
    (.letOp (n := 327) (.exec 0x10a899 (fun s => s.RIP = 0x10a899) (shlR32Effect 0x10a899 3 1 24) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[324]
    (.letOp (n := 328) (.out 0x10a89c (orR64R64Effect 0x10a89c 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[326, 322]
    (.letOp (n := 329) (.exec 0x10a89c (fun s => s.RIP = 0x10a89c) (orR64R64Effect 0x10a89c 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[326, 322]
    (b_l10a6a8_7))))))))))))))))))))))))))))))))))))))))

def bytes_l10a6a8_6 : List UInt8 :=
  [0x48, 0x09, 0xC8, 0x44, 0x0F, 0xB6, 0x5A, 0x0F, 0x49, 0xC1, 0xE3, 0x38, 0x49, 0x09, 0xC3, 0x0F,
    0xB6, 0x42, 0x15, 0xC1, 0xE0, 0x10, 0x0F, 0xB6, 0x4A, 0x14, 0x48, 0x09, 0xC1, 0x0F, 0xB6, 0x42,
    0x16, 0x48, 0xC1, 0xE0, 0x20, 0x48, 0x09, 0xC8, 0x0F, 0xB6, 0x4A, 0x17, 0x48, 0xC1, 0xE1, 0x30,
    0x48, 0x09, 0xC1, 0x0F, 0xB6, 0x42, 0x1C, 0xC1, 0xE0, 0x08, 0x48, 0x09, 0xC8, 0x0F, 0xB6, 0x4A,
    0x1D, 0xC1, 0xE1, 0x18, 0x48, 0x09, 0xC1] ++ bytes_l10a6a8_7

theorem code_l10a6a8_6 : ∀ x ∈ codeRange 0x10a858 bytes_l10a6a8_6, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa858 71 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a6a8_7

def b_l10a6a8_5 : Block Op Label signature Reg.count 250 :=
  .letOp (n := 250) (.out 0x10a812 (xorR64R64Effect 0x10a812 3 9) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 9] []) (.reg (.gpr 3))) #v[244, 248]
    (.letOp (n := 251) (.exec 0x10a812 (fun s => s.RIP = 0x10a812) (xorR64R64Effect 0x10a812 3 9) (Reg.operands [.gpr 3, .gpr 9] [])) #v[244, 248]
    (.letOp (n := 252) (.out 0x10a815 (xorR64R64Effect 0x10a815 5 3) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 3] []) (.reg (.gpr 5))) #v[153, 250]
    (.letOp (n := 253) (.exec 0x10a815 (fun s => s.RIP = 0x10a815) (xorR64R64Effect 0x10a815 5 3) (Reg.operands [.gpr 5, .gpr 3] [])) #v[153, 250]
    (.letOp (n := 254) (.out 0x10a818 (movzxR32M8Effect 0x10a818 4 0 (.base 2 (.d8 0x5))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 255) (.exec 0x10a818 (LoadPre 0x10a818 (fun s => AddrMode.addr (.base 2 (.d8 0x5)) s (0x10a818 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a818 4 0 (.base 2 (.d8 0x5))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 256) (.out 0x10a81c (shlR32Effect 0x10a81c 3 0 16) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[254]
    (.letOp (n := 257) (.exec 0x10a81c (fun s => s.RIP = 0x10a81c) (shlR32Effect 0x10a81c 3 0 16) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[254]
    (.letOp (n := 258) (.out 0x10a81f (movzxR32M8Effect 0x10a81f 4 1 (.base 2 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2]
    (.letOp (n := 259) (.exec 0x10a81f (LoadPre 0x10a81f (fun s => AddrMode.addr (.base 2 (.d8 0x4)) s (0x10a81f + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a81f 4 1 (.base 2 (.d8 0x4))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 260) (.out 0x10a823 (orR64R64Effect 0x10a823 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[258, 256]
    (.letOp (n := 261) (.exec 0x10a823 (fun s => s.RIP = 0x10a823) (orR64R64Effect 0x10a823 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[258, 256]
    (.letOp (n := 262) (.out 0x10a826 (movzxR32M8Effect 0x10a826 4 0 (.base 2 (.d8 0x6))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 263) (.exec 0x10a826 (LoadPre 0x10a826 (fun s => AddrMode.addr (.base 2 (.d8 0x6)) s (0x10a826 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a826 4 0 (.base 2 (.d8 0x6))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 264) (.out 0x10a82a (shlR64Effect 0x10a82a 4 0 32) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[262]
    (.letOp (n := 265) (.exec 0x10a82a (fun s => s.RIP = 0x10a82a) (shlR64Effect 0x10a82a 4 0 32) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[262]
    (.letOp (n := 266) (.out 0x10a82e (orR64R64Effect 0x10a82e 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[264, 260]
    (.letOp (n := 267) (.exec 0x10a82e (fun s => s.RIP = 0x10a82e) (orR64R64Effect 0x10a82e 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[264, 260]
    (.letOp (n := 268) (.out 0x10a831 (movzxR32M8Effect 0x10a831 4 1 (.base 2 (.d8 0x7))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2]
    (.letOp (n := 269) (.exec 0x10a831 (LoadPre 0x10a831 (fun s => AddrMode.addr (.base 2 (.d8 0x7)) s (0x10a831 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a831 4 1 (.base 2 (.d8 0x7))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 270) (.out 0x10a835 (shlR64Effect 0x10a835 4 1 48) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[268]
    (.letOp (n := 271) (.exec 0x10a835 (fun s => s.RIP = 0x10a835) (shlR64Effect 0x10a835 4 1 48) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[268]
    (.letOp (n := 272) (.out 0x10a839 (orR64R64Effect 0x10a839 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[270, 266]
    (.letOp (n := 273) (.exec 0x10a839 (fun s => s.RIP = 0x10a839) (orR64R64Effect 0x10a839 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[270, 266]
    (.letOp (n := 274) (.out 0x10a83c (movzxR32M8Effect 0x10a83c 4 0 (.base 2 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 275) (.exec 0x10a83c (LoadPre 0x10a83c (fun s => AddrMode.addr (.base 2 (.d8 0xc)) s (0x10a83c + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a83c 4 0 (.base 2 (.d8 0xc))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 276) (.out 0x10a840 (shlR32Effect 0x10a840 3 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[274]
    (.letOp (n := 277) (.exec 0x10a840 (fun s => s.RIP = 0x10a840) (shlR32Effect 0x10a840 3 0 8) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[274]
    (.letOp (n := 278) (.out 0x10a843 (orR64R64Effect 0x10a843 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[276, 272]
    (.letOp (n := 279) (.exec 0x10a843 (fun s => s.RIP = 0x10a843) (orR64R64Effect 0x10a843 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[276, 272]
    (.letOp (n := 280) (.out 0x10a846 (movzxR32M8Effect 0x10a846 4 1 (.base 2 (.d8 0xd))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2]
    (.letOp (n := 281) (.exec 0x10a846 (LoadPre 0x10a846 (fun s => AddrMode.addr (.base 2 (.d8 0xd)) s (0x10a846 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a846 4 1 (.base 2 (.d8 0xd))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 282) (.out 0x10a84a (shlR32Effect 0x10a84a 3 1 24) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[280]
    (.letOp (n := 283) (.exec 0x10a84a (fun s => s.RIP = 0x10a84a) (shlR32Effect 0x10a84a 3 1 24) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[280]
    (.letOp (n := 284) (.out 0x10a84d (orR64R64Effect 0x10a84d 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[282, 278]
    (.letOp (n := 285) (.exec 0x10a84d (fun s => s.RIP = 0x10a84d) (orR64R64Effect 0x10a84d 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[282, 278]
    (.letOp (n := 286) (.out 0x10a850 (movzxR32M8Effect 0x10a850 4 0 (.base 2 (.d8 0xe))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 287) (.exec 0x10a850 (LoadPre 0x10a850 (fun s => AddrMode.addr (.base 2 (.d8 0xe)) s (0x10a850 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a850 4 0 (.base 2 (.d8 0xe))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 288) (.out 0x10a854 (shlR64Effect 0x10a854 4 0 40) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[286]
    (.letOp (n := 289) (.exec 0x10a854 (fun s => s.RIP = 0x10a854) (shlR64Effect 0x10a854 4 0 40) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[286]
    (b_l10a6a8_6))))))))))))))))))))))))))))))))))))))))

def bytes_l10a6a8_5 : List UInt8 :=
  [0x4C, 0x31, 0xCB, 0x48, 0x31, 0xDD, 0x0F, 0xB6, 0x42, 0x05, 0xC1, 0xE0, 0x10, 0x0F, 0xB6, 0x4A,
    0x04, 0x48, 0x09, 0xC1, 0x0F, 0xB6, 0x42, 0x06, 0x48, 0xC1, 0xE0, 0x20, 0x48, 0x09, 0xC8, 0x0F,
    0xB6, 0x4A, 0x07, 0x48, 0xC1, 0xE1, 0x30, 0x48, 0x09, 0xC1, 0x0F, 0xB6, 0x42, 0x0C, 0xC1, 0xE0,
    0x08, 0x48, 0x09, 0xC8, 0x0F, 0xB6, 0x4A, 0x0D, 0xC1, 0xE1, 0x18, 0x48, 0x09, 0xC1, 0x0F, 0xB6,
    0x42, 0x0E, 0x48, 0xC1, 0xE0, 0x28] ++ bytes_l10a6a8_6

theorem code_l10a6a8_5 : ∀ x ∈ codeRange 0x10a812 bytes_l10a6a8_5, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa812 70 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a6a8_6

def b_l10a6a8_4 : Block Op Label signature Reg.count 210 :=
  .letOp (n := 210) (.out 0x10a7cc (movzxR32M8Effect 0x10a7cc 4 0 (.base 2 (.d8 0x32))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 211) (.exec 0x10a7cc (LoadPre 0x10a7cc (fun s => AddrMode.addr (.base 2 (.d8 0x32)) s (0x10a7cc + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a7cc 4 0 (.base 2 (.d8 0x32))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 212) (.out 0x10a7d0 (shlR64Effect 0x10a7d0 4 0 32) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[210]
    (.letOp (n := 213) (.exec 0x10a7d0 (fun s => s.RIP = 0x10a7d0) (shlR64Effect 0x10a7d0 4 0 32) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[210]
    (.letOp (n := 214) (.out 0x10a7d4 (orR64R64Effect 0x10a7d4 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[212, 208]
    (.letOp (n := 215) (.exec 0x10a7d4 (fun s => s.RIP = 0x10a7d4) (orR64R64Effect 0x10a7d4 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[212, 208]
    (.letOp (n := 216) (.out 0x10a7d7 (movzxR32M8Effect 0x10a7d7 4 1 (.base 2 (.d8 0x33))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2]
    (.letOp (n := 217) (.exec 0x10a7d7 (LoadPre 0x10a7d7 (fun s => AddrMode.addr (.base 2 (.d8 0x33)) s (0x10a7d7 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a7d7 4 1 (.base 2 (.d8 0x33))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 218) (.out 0x10a7db (shlR64Effect 0x10a7db 4 1 48) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[216]
    (.letOp (n := 219) (.exec 0x10a7db (fun s => s.RIP = 0x10a7db) (shlR64Effect 0x10a7db 4 1 48) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[216]
    (.letOp (n := 220) (.out 0x10a7df (orR64R64Effect 0x10a7df 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[218, 214]
    (.letOp (n := 221) (.exec 0x10a7df (fun s => s.RIP = 0x10a7df) (orR64R64Effect 0x10a7df 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[218, 214]
    (.letOp (n := 222) (.out 0x10a7e2 (movzxR32M8Effect 0x10a7e2 4 0 (.base 2 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 223) (.exec 0x10a7e2 (LoadPre 0x10a7e2 (fun s => AddrMode.addr (.base 2 (.d8 0x38)) s (0x10a7e2 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a7e2 4 0 (.base 2 (.d8 0x38))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 224) (.out 0x10a7e6 (shlR32Effect 0x10a7e6 3 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[222]
    (.letOp (n := 225) (.exec 0x10a7e6 (fun s => s.RIP = 0x10a7e6) (shlR32Effect 0x10a7e6 3 0 8) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[222]
    (.letOp (n := 226) (.out 0x10a7e9 (orR64R64Effect 0x10a7e9 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[224, 220]
    (.letOp (n := 227) (.exec 0x10a7e9 (fun s => s.RIP = 0x10a7e9) (orR64R64Effect 0x10a7e9 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[224, 220]
    (.letOp (n := 228) (.out 0x10a7ec (movzxR32M8Effect 0x10a7ec 4 1 (.base 2 (.d8 0x39))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2]
    (.letOp (n := 229) (.exec 0x10a7ec (LoadPre 0x10a7ec (fun s => AddrMode.addr (.base 2 (.d8 0x39)) s (0x10a7ec + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a7ec 4 1 (.base 2 (.d8 0x39))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 230) (.out 0x10a7f0 (shlR32Effect 0x10a7f0 3 1 24) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[228]
    (.letOp (n := 231) (.exec 0x10a7f0 (fun s => s.RIP = 0x10a7f0) (shlR32Effect 0x10a7f0 3 1 24) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[228]
    (.letOp (n := 232) (.out 0x10a7f3 (orR64R64Effect 0x10a7f3 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[230, 226]
    (.letOp (n := 233) (.exec 0x10a7f3 (fun s => s.RIP = 0x10a7f3) (orR64R64Effect 0x10a7f3 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[230, 226]
    (.letOp (n := 234) (.out 0x10a7f6 (movzxR32M8Effect 0x10a7f6 4 0 (.base 2 (.d8 0x3a))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 235) (.exec 0x10a7f6 (LoadPre 0x10a7f6 (fun s => AddrMode.addr (.base 2 (.d8 0x3a)) s (0x10a7f6 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a7f6 4 0 (.base 2 (.d8 0x3a))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 236) (.out 0x10a7fa (shlR64Effect 0x10a7fa 4 0 40) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[234]
    (.letOp (n := 237) (.exec 0x10a7fa (fun s => s.RIP = 0x10a7fa) (shlR64Effect 0x10a7fa 4 0 40) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[234]
    (.letOp (n := 238) (.out 0x10a7fe (orR64R64Effect 0x10a7fe 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[236, 232]
    (.letOp (n := 239) (.exec 0x10a7fe (fun s => s.RIP = 0x10a7fe) (orR64R64Effect 0x10a7fe 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[236, 232]
    (.letOp (n := 240) (.out 0x10a801 (movzxR32M8Effect 0x10a801 4 3 (.base 2 (.d8 0x3b))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[2]
    (.letOp (n := 241) (.exec 0x10a801 (LoadPre 0x10a801 (fun s => AddrMode.addr (.base 2 (.d8 0x3b)) s (0x10a801 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a801 4 3 (.base 2 (.d8 0x3b))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 242) (.out 0x10a805 (shlR64Effect 0x10a805 4 3 56) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[240]
    (.letOp (n := 243) (.exec 0x10a805 (fun s => s.RIP = 0x10a805) (shlR64Effect 0x10a805 4 3 56) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[240]
    (.letOp (n := 244) (.out 0x10a809 (orR64R64Effect 0x10a809 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0] []) (.reg (.gpr 3))) #v[242, 238]
    (.letOp (n := 245) (.exec 0x10a809 (fun s => s.RIP = 0x10a809) (orR64R64Effect 0x10a809 3 0) (Reg.operands [.gpr 3, .gpr 0] [])) #v[242, 238]
    (.letOp (n := 246) (.out 0x10a80c (xorR64R64Effect 0x10a80c 9 3) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 3] []) (.reg (.gpr 9))) #v[200, 244]
    (.letOp (n := 247) (.exec 0x10a80c (fun s => s.RIP = 0x10a80c) (xorR64R64Effect 0x10a80c 9 3) (Reg.operands [.gpr 9, .gpr 3] [])) #v[200, 244]
    (.letOp (n := 248) (.out 0x10a80f (andR64R64Effect 0x10a80f 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[246, 146]
    (.letOp (n := 249) (.exec 0x10a80f (fun s => s.RIP = 0x10a80f) (andR64R64Effect 0x10a80f 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[246, 146]
    (b_l10a6a8_5))))))))))))))))))))))))))))))))))))))))

def bytes_l10a6a8_4 : List UInt8 :=
  [0x0F, 0xB6, 0x42, 0x32, 0x48, 0xC1, 0xE0, 0x20, 0x48, 0x09, 0xC8, 0x0F, 0xB6, 0x4A, 0x33, 0x48,
    0xC1, 0xE1, 0x30, 0x48, 0x09, 0xC1, 0x0F, 0xB6, 0x42, 0x38, 0xC1, 0xE0, 0x08, 0x48, 0x09, 0xC8,
    0x0F, 0xB6, 0x4A, 0x39, 0xC1, 0xE1, 0x18, 0x48, 0x09, 0xC1, 0x0F, 0xB6, 0x42, 0x3A, 0x48, 0xC1,
    0xE0, 0x28, 0x48, 0x09, 0xC8, 0x0F, 0xB6, 0x5A, 0x3B, 0x48, 0xC1, 0xE3, 0x38, 0x48, 0x09, 0xC3,
    0x49, 0x31, 0xD9, 0x4D, 0x21, 0xD1] ++ bytes_l10a6a8_5

theorem code_l10a6a8_4 : ∀ x ∈ codeRange 0x10a7cc bytes_l10a6a8_4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa7cc 70 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a6a8_5

def b_l10a6a8_3 : Block Op Label signature Reg.count 171 :=
  .letOp (n := 171) (.out 0x10a785 (shlR64Effect 0x10a785 4 1 48) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[169]
    (.letOp (n := 172) (.exec 0x10a785 (fun s => s.RIP = 0x10a785) (shlR64Effect 0x10a785 4 1 48) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[169]
    (.letOp (n := 173) (.out 0x10a789 (orR64R64Effect 0x10a789 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[171, 167]
    (.letOp (n := 174) (.exec 0x10a789 (fun s => s.RIP = 0x10a789) (orR64R64Effect 0x10a789 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[171, 167]
    (.letOp (n := 175) (.out 0x10a78c (movzxR32M8Effect 0x10a78c 4 0 (.base 2 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 176) (.exec 0x10a78c (LoadPre 0x10a78c (fun s => AddrMode.addr (.base 2 (.d8 0x28)) s (0x10a78c + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a78c 4 0 (.base 2 (.d8 0x28))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 177) (.out 0x10a790 (shlR32Effect 0x10a790 3 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[175]
    (.letOp (n := 178) (.exec 0x10a790 (fun s => s.RIP = 0x10a790) (shlR32Effect 0x10a790 3 0 8) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[175]
    (.letOp (n := 179) (.out 0x10a793 (orR64R64Effect 0x10a793 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[177, 173]
    (.letOp (n := 180) (.exec 0x10a793 (fun s => s.RIP = 0x10a793) (orR64R64Effect 0x10a793 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[177, 173]
    (.letOp (n := 181) (.out 0x10a796 (movzxR32M8Effect 0x10a796 4 1 (.base 2 (.d8 0x29))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2]
    (.letOp (n := 182) (.exec 0x10a796 (LoadPre 0x10a796 (fun s => AddrMode.addr (.base 2 (.d8 0x29)) s (0x10a796 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a796 4 1 (.base 2 (.d8 0x29))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 183) (.out 0x10a79a (shlR32Effect 0x10a79a 3 1 24) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[181]
    (.letOp (n := 184) (.exec 0x10a79a (fun s => s.RIP = 0x10a79a) (shlR32Effect 0x10a79a 3 1 24) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[181]
    (.letOp (n := 185) (.out 0x10a79d (orR64R64Effect 0x10a79d 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[183, 179]
    (.letOp (n := 186) (.exec 0x10a79d (fun s => s.RIP = 0x10a79d) (orR64R64Effect 0x10a79d 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[183, 179]
    (.letOp (n := 187) (.out 0x10a7a0 (movzxR32M8Effect 0x10a7a0 4 0 (.base 2 (.d8 0x2a))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 188) (.exec 0x10a7a0 (LoadPre 0x10a7a0 (fun s => AddrMode.addr (.base 2 (.d8 0x2a)) s (0x10a7a0 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a7a0 4 0 (.base 2 (.d8 0x2a))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 189) (.out 0x10a7a4 (shlR64Effect 0x10a7a4 4 0 40) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[187]
    (.letOp (n := 190) (.exec 0x10a7a4 (fun s => s.RIP = 0x10a7a4) (shlR64Effect 0x10a7a4 4 0 40) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[187]
    (.letOp (n := 191) (.out 0x10a7a8 (orR64R64Effect 0x10a7a8 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[189, 185]
    (.letOp (n := 192) (.exec 0x10a7a8 (fun s => s.RIP = 0x10a7a8) (orR64R64Effect 0x10a7a8 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[189, 185]
    (.letOp (n := 193) (.out 0x10a7ab (movzxR32M8Effect 0x10a7ab 5 9 (.base 2 (.d8 0x2b))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[2]
    (.letOp (n := 194) (.exec 0x10a7ab (LoadPre 0x10a7ab (fun s => AddrMode.addr (.base 2 (.d8 0x2b)) s (0x10a7ab + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10a7ab 5 9 (.base 2 (.d8 0x2b))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 195) (.out 0x10a7b0 (shlR64Effect 0x10a7b0 4 9 56) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[193]
    (.letOp (n := 196) (.exec 0x10a7b0 (fun s => s.RIP = 0x10a7b0) (shlR64Effect 0x10a7b0 4 9 56) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[193]
    (.letOp (n := 197) (.out 0x10a7b4 (orR64R64Effect 0x10a7b4 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0] []) (.reg (.gpr 9))) #v[195, 191]
    (.letOp (n := 198) (.exec 0x10a7b4 (fun s => s.RIP = 0x10a7b4) (orR64R64Effect 0x10a7b4 9 0) (Reg.operands [.gpr 9, .gpr 0] [])) #v[195, 191]
    (.letOp (n := 199) (.exec 0x10a7b7 (StorePre 0x10a7b7 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10a7b7 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10a7b7 9 (.sib 4 none 0 .none)) (Reg.operands [.gpr 9, .gpr 4] [])) #v[197, 4]
    (.letOp (n := 200) (.out 0x10a7bb (shrR64Effect 0x10a7bb 3 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[197]
    (.letOp (n := 201) (.exec 0x10a7bb (fun s => s.RIP = 0x10a7bb) (shrR64Effect 0x10a7bb 3 9 1) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[197]
    (.letOp (n := 202) (.out 0x10a7be (movzxR32M8Effect 0x10a7be 4 0 (.base 2 (.d8 0x31))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 203) (.exec 0x10a7be (LoadPre 0x10a7be (fun s => AddrMode.addr (.base 2 (.d8 0x31)) s (0x10a7be + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a7be 4 0 (.base 2 (.d8 0x31))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 204) (.out 0x10a7c2 (shlR32Effect 0x10a7c2 3 0 16) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[202]
    (.letOp (n := 205) (.exec 0x10a7c2 (fun s => s.RIP = 0x10a7c2) (shlR32Effect 0x10a7c2 3 0 16) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[202]
    (.letOp (n := 206) (.out 0x10a7c5 (movzxR32M8Effect 0x10a7c5 4 1 (.base 2 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2]
    (.letOp (n := 207) (.exec 0x10a7c5 (LoadPre 0x10a7c5 (fun s => AddrMode.addr (.base 2 (.d8 0x30)) s (0x10a7c5 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a7c5 4 1 (.base 2 (.d8 0x30))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 208) (.out 0x10a7c9 (orR64R64Effect 0x10a7c9 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[206, 204]
    (.letOp (n := 209) (.exec 0x10a7c9 (fun s => s.RIP = 0x10a7c9) (orR64R64Effect 0x10a7c9 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[206, 204]
    (b_l10a6a8_4)))))))))))))))))))))))))))))))))))))))

def bytes_l10a6a8_3 : List UInt8 :=
  [0x48, 0xC1, 0xE1, 0x30, 0x48, 0x09, 0xC1, 0x0F, 0xB6, 0x42, 0x28, 0xC1, 0xE0, 0x08, 0x48, 0x09,
    0xC8, 0x0F, 0xB6, 0x4A, 0x29, 0xC1, 0xE1, 0x18, 0x48, 0x09, 0xC1, 0x0F, 0xB6, 0x42, 0x2A, 0x48,
    0xC1, 0xE0, 0x28, 0x48, 0x09, 0xC8, 0x44, 0x0F, 0xB6, 0x4A, 0x2B, 0x49, 0xC1, 0xE1, 0x38, 0x49,
    0x09, 0xC1, 0x4C, 0x89, 0x0C, 0x24, 0x49, 0xD1, 0xE9, 0x0F, 0xB6, 0x42, 0x31, 0xC1, 0xE0, 0x10,
    0x0F, 0xB6, 0x4A, 0x30, 0x48, 0x09, 0xC1] ++ bytes_l10a6a8_4

theorem code_l10a6a8_3 : ∀ x ∈ codeRange 0x10a785 bytes_l10a6a8_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa785 71 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a6a8_4

def b_l10a6a8_2 : Block Op Label signature Reg.count 132 :=
  .letOp (n := 132) (.out 0x10a736 (movzxR32M8Effect 0x10a736 4 0 (.base 2 (.d8 0x1a))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 133) (.exec 0x10a736 (LoadPre 0x10a736 (fun s => AddrMode.addr (.base 2 (.d8 0x1a)) s (0x10a736 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a736 4 0 (.base 2 (.d8 0x1a))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 134) (.out 0x10a73a (shlR64Effect 0x10a73a 4 0 40) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[132]
    (.letOp (n := 135) (.exec 0x10a73a (fun s => s.RIP = 0x10a73a) (shlR64Effect 0x10a73a 4 0 40) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[132]
    (.letOp (n := 136) (.out 0x10a73e (orR64R64Effect 0x10a73e 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[134, 130]
    (.letOp (n := 137) (.exec 0x10a73e (fun s => s.RIP = 0x10a73e) (orR64R64Effect 0x10a73e 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[134, 130]
    (.letOp (n := 138) (.out 0x10a741 (movzxR32M8Effect 0x10a741 4 5 (.base 2 (.d8 0x1b))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[2]
    (.letOp (n := 139) (.exec 0x10a741 (LoadPre 0x10a741 (fun s => AddrMode.addr (.base 2 (.d8 0x1b)) s (0x10a741 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a741 4 5 (.base 2 (.d8 0x1b))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 140) (.out 0x10a745 (shlR64Effect 0x10a745 4 5 56) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[138]
    (.letOp (n := 141) (.exec 0x10a745 (fun s => s.RIP = 0x10a745) (shlR64Effect 0x10a745 4 5 56) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[138]
    (.letOp (n := 142) (.out 0x10a749 (orR64R64Effect 0x10a749 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 0] []) (.reg (.gpr 5))) #v[140, 136]
    (.letOp (n := 143) (.exec 0x10a749 (fun s => s.RIP = 0x10a749) (orR64R64Effect 0x10a749 5 0) (Reg.operands [.gpr 5, .gpr 0] [])) #v[140, 136]
    (.letOp (n := 144) (.out 0x10a74c (xorR64R64Effect 0x10a74c 8 5) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 5] []) (.reg (.gpr 8))) #v[98, 142]
    (.letOp (n := 145) (.exec 0x10a74c (fun s => s.RIP = 0x10a74c) (xorR64R64Effect 0x10a74c 8 5) (Reg.operands [.gpr 8, .gpr 5] [])) #v[98, 142]
    (.letOp (n := 146) (.out 0x10a74f (movR64Imm64Effect 0x10a74f 10 0x5555555555555555) (EffectPart.reads (.reg (.gpr 10)) [] []) (.reg (.gpr 10))) #v[]
    (.letOp (n := 147) (.exec 0x10a74f (fun s => s.RIP = 0x10a74f) (movR64Imm64Effect 0x10a74f 10 0x5555555555555555) (Reg.operands [] [])) #v[]
    (.letOp (n := 148) (.out 0x10a759 (andR64R64Effect 0x10a759 8 10) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 10] []) (.reg (.gpr 8))) #v[144, 146]
    (.letOp (n := 149) (.exec 0x10a759 (fun s => s.RIP = 0x10a759) (andR64R64Effect 0x10a759 8 10) (Reg.operands [.gpr 8, .gpr 10] [])) #v[144, 146]
    (.letOp (n := 150) (.out 0x10a75c (xorR64R64Effect 0x10a75c 5 8) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 8] []) (.reg (.gpr 5))) #v[142, 148]
    (.letOp (n := 151) (.exec 0x10a75c (fun s => s.RIP = 0x10a75c) (xorR64R64Effect 0x10a75c 5 8) (Reg.operands [.gpr 5, .gpr 8] [])) #v[142, 148]
    (.letOp (n := 152) (.exec 0x10a75f (StorePre 0x10a75f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10a75f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10a75f 5 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[150, 4]
    (.letOp (n := 153) (.out 0x10a764 (shrR64Effect 0x10a764 4 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[150]
    (.letOp (n := 154) (.exec 0x10a764 (fun s => s.RIP = 0x10a764) (shrR64Effect 0x10a764 4 5 2) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[150]
    (.letOp (n := 155) (.out 0x10a768 (movzxR32M8Effect 0x10a768 4 0 (.base 2 (.d8 0x21))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 156) (.exec 0x10a768 (LoadPre 0x10a768 (fun s => AddrMode.addr (.base 2 (.d8 0x21)) s (0x10a768 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a768 4 0 (.base 2 (.d8 0x21))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 157) (.out 0x10a76c (shlR32Effect 0x10a76c 3 0 16) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[155]
    (.letOp (n := 158) (.exec 0x10a76c (fun s => s.RIP = 0x10a76c) (shlR32Effect 0x10a76c 3 0 16) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[155]
    (.letOp (n := 159) (.out 0x10a76f (movzxR32M8Effect 0x10a76f 4 1 (.base 2 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2]
    (.letOp (n := 160) (.exec 0x10a76f (LoadPre 0x10a76f (fun s => AddrMode.addr (.base 2 (.d8 0x20)) s (0x10a76f + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a76f 4 1 (.base 2 (.d8 0x20))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 161) (.out 0x10a773 (orR64R64Effect 0x10a773 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[159, 157]
    (.letOp (n := 162) (.exec 0x10a773 (fun s => s.RIP = 0x10a773) (orR64R64Effect 0x10a773 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[159, 157]
    (.letOp (n := 163) (.out 0x10a776 (movzxR32M8Effect 0x10a776 4 0 (.base 2 (.d8 0x22))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 164) (.exec 0x10a776 (LoadPre 0x10a776 (fun s => AddrMode.addr (.base 2 (.d8 0x22)) s (0x10a776 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a776 4 0 (.base 2 (.d8 0x22))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 165) (.out 0x10a77a (shlR64Effect 0x10a77a 4 0 32) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[163]
    (.letOp (n := 166) (.exec 0x10a77a (fun s => s.RIP = 0x10a77a) (shlR64Effect 0x10a77a 4 0 32) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[163]
    (.letOp (n := 167) (.out 0x10a77e (orR64R64Effect 0x10a77e 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[165, 161]
    (.letOp (n := 168) (.exec 0x10a77e (fun s => s.RIP = 0x10a77e) (orR64R64Effect 0x10a77e 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[165, 161]
    (.letOp (n := 169) (.out 0x10a781 (movzxR32M8Effect 0x10a781 4 1 (.base 2 (.d8 0x23))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2]
    (.letOp (n := 170) (.exec 0x10a781 (LoadPre 0x10a781 (fun s => AddrMode.addr (.base 2 (.d8 0x23)) s (0x10a781 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a781 4 1 (.base 2 (.d8 0x23))) (Reg.operands [.gpr 2] [])) #v[2]
    (b_l10a6a8_3)))))))))))))))))))))))))))))))))))))))

def bytes_l10a6a8_2 : List UInt8 :=
  [0x0F, 0xB6, 0x42, 0x1A, 0x48, 0xC1, 0xE0, 0x28, 0x48, 0x09, 0xC8, 0x0F, 0xB6, 0x6A, 0x1B, 0x48,
    0xC1, 0xE5, 0x38, 0x48, 0x09, 0xC5, 0x49, 0x31, 0xE8, 0x49, 0xBA, 0x55, 0x55, 0x55, 0x55, 0x55,
    0x55, 0x55, 0x55, 0x4D, 0x21, 0xD0, 0x4C, 0x31, 0xC5, 0x48, 0x89, 0x6C, 0x24, 0x10, 0x48, 0xC1,
    0xED, 0x02, 0x0F, 0xB6, 0x42, 0x21, 0xC1, 0xE0, 0x10, 0x0F, 0xB6, 0x4A, 0x20, 0x48, 0x09, 0xC1,
    0x0F, 0xB6, 0x42, 0x22, 0x48, 0xC1, 0xE0, 0x20, 0x48, 0x09, 0xC8, 0x0F, 0xB6, 0x4A, 0x23] ++ bytes_l10a6a8_3

theorem code_l10a6a8_2 : ∀ x ∈ codeRange 0x10a736 bytes_l10a6a8_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa736 79 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a6a8_3

def b_l10a6a8_1 : Block Op Label signature Reg.count 93 :=
  .letOp (n := 93) (.out 0x10a6ef (shlR64Effect 0x10a6ef 4 8 56) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[91]
    (.letOp (n := 94) (.exec 0x10a6ef (fun s => s.RIP = 0x10a6ef) (shlR64Effect 0x10a6ef 4 8 56) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[91]
    (.letOp (n := 95) (.out 0x10a6f3 (orR64R64Effect 0x10a6f3 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[93, 89]
    (.letOp (n := 96) (.exec 0x10a6f3 (fun s => s.RIP = 0x10a6f3) (orR64R64Effect 0x10a6f3 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[93, 89]
    (.letOp (n := 97) (.exec 0x10a6f6 (StorePre 0x10a6f6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10a6f6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10a6f6 8 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[95, 4]
    (.letOp (n := 98) (.out 0x10a6fb (shrR64Effect 0x10a6fb 3 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[95]
    (.letOp (n := 99) (.exec 0x10a6fb (fun s => s.RIP = 0x10a6fb) (shrR64Effect 0x10a6fb 3 8 1) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[95]
    (.letOp (n := 100) (.out 0x10a6fe (movzxR32M8Effect 0x10a6fe 4 0 (.base 2 (.d8 0x11))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 101) (.exec 0x10a6fe (LoadPre 0x10a6fe (fun s => AddrMode.addr (.base 2 (.d8 0x11)) s (0x10a6fe + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a6fe 4 0 (.base 2 (.d8 0x11))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 102) (.out 0x10a702 (shlR32Effect 0x10a702 3 0 16) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[100]
    (.letOp (n := 103) (.exec 0x10a702 (fun s => s.RIP = 0x10a702) (shlR32Effect 0x10a702 3 0 16) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[100]
    (.letOp (n := 104) (.out 0x10a705 (movzxR32M8Effect 0x10a705 4 1 (.base 2 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2]
    (.letOp (n := 105) (.exec 0x10a705 (LoadPre 0x10a705 (fun s => AddrMode.addr (.base 2 (.d8 0x10)) s (0x10a705 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a705 4 1 (.base 2 (.d8 0x10))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 106) (.out 0x10a709 (orR64R64Effect 0x10a709 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[104, 102]
    (.letOp (n := 107) (.exec 0x10a709 (fun s => s.RIP = 0x10a709) (orR64R64Effect 0x10a709 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[104, 102]
    (.letOp (n := 108) (.out 0x10a70c (movzxR32M8Effect 0x10a70c 4 0 (.base 2 (.d8 0x12))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 109) (.exec 0x10a70c (LoadPre 0x10a70c (fun s => AddrMode.addr (.base 2 (.d8 0x12)) s (0x10a70c + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a70c 4 0 (.base 2 (.d8 0x12))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 110) (.out 0x10a710 (shlR64Effect 0x10a710 4 0 32) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[108]
    (.letOp (n := 111) (.exec 0x10a710 (fun s => s.RIP = 0x10a710) (shlR64Effect 0x10a710 4 0 32) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[108]
    (.letOp (n := 112) (.out 0x10a714 (orR64R64Effect 0x10a714 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[110, 106]
    (.letOp (n := 113) (.exec 0x10a714 (fun s => s.RIP = 0x10a714) (orR64R64Effect 0x10a714 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[110, 106]
    (.letOp (n := 114) (.out 0x10a717 (movzxR32M8Effect 0x10a717 4 1 (.base 2 (.d8 0x13))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2]
    (.letOp (n := 115) (.exec 0x10a717 (LoadPre 0x10a717 (fun s => AddrMode.addr (.base 2 (.d8 0x13)) s (0x10a717 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a717 4 1 (.base 2 (.d8 0x13))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 116) (.out 0x10a71b (shlR64Effect 0x10a71b 4 1 48) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[114]
    (.letOp (n := 117) (.exec 0x10a71b (fun s => s.RIP = 0x10a71b) (shlR64Effect 0x10a71b 4 1 48) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[114]
    (.letOp (n := 118) (.out 0x10a71f (orR64R64Effect 0x10a71f 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[116, 112]
    (.letOp (n := 119) (.exec 0x10a71f (fun s => s.RIP = 0x10a71f) (orR64R64Effect 0x10a71f 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[116, 112]
    (.letOp (n := 120) (.out 0x10a722 (movzxR32M8Effect 0x10a722 4 0 (.base 2 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 121) (.exec 0x10a722 (LoadPre 0x10a722 (fun s => AddrMode.addr (.base 2 (.d8 0x18)) s (0x10a722 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a722 4 0 (.base 2 (.d8 0x18))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 122) (.out 0x10a726 (shlR32Effect 0x10a726 3 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[120]
    (.letOp (n := 123) (.exec 0x10a726 (fun s => s.RIP = 0x10a726) (shlR32Effect 0x10a726 3 0 8) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[120]
    (.letOp (n := 124) (.out 0x10a729 (orR64R64Effect 0x10a729 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[122, 118]
    (.letOp (n := 125) (.exec 0x10a729 (fun s => s.RIP = 0x10a729) (orR64R64Effect 0x10a729 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[122, 118]
    (.letOp (n := 126) (.out 0x10a72c (movzxR32M8Effect 0x10a72c 4 1 (.base 2 (.d8 0x19))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2]
    (.letOp (n := 127) (.exec 0x10a72c (LoadPre 0x10a72c (fun s => AddrMode.addr (.base 2 (.d8 0x19)) s (0x10a72c + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a72c 4 1 (.base 2 (.d8 0x19))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 128) (.out 0x10a730 (shlR32Effect 0x10a730 3 1 24) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[126]
    (.letOp (n := 129) (.exec 0x10a730 (fun s => s.RIP = 0x10a730) (shlR32Effect 0x10a730 3 1 24) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[126]
    (.letOp (n := 130) (.out 0x10a733 (orR64R64Effect 0x10a733 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[128, 124]
    (.letOp (n := 131) (.exec 0x10a733 (fun s => s.RIP = 0x10a733) (orR64R64Effect 0x10a733 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[128, 124]
    (b_l10a6a8_2)))))))))))))))))))))))))))))))))))))))

def bytes_l10a6a8_1 : List UInt8 :=
  [0x49, 0xC1, 0xE0, 0x38, 0x49, 0x09, 0xC0, 0x4C, 0x89, 0x44, 0x24, 0x08, 0x49, 0xD1, 0xE8, 0x0F,
    0xB6, 0x42, 0x11, 0xC1, 0xE0, 0x10, 0x0F, 0xB6, 0x4A, 0x10, 0x48, 0x09, 0xC1, 0x0F, 0xB6, 0x42,
    0x12, 0x48, 0xC1, 0xE0, 0x20, 0x48, 0x09, 0xC8, 0x0F, 0xB6, 0x4A, 0x13, 0x48, 0xC1, 0xE1, 0x30,
    0x48, 0x09, 0xC1, 0x0F, 0xB6, 0x42, 0x18, 0xC1, 0xE0, 0x08, 0x48, 0x09, 0xC8, 0x0F, 0xB6, 0x4A,
    0x19, 0xC1, 0xE1, 0x18, 0x48, 0x09, 0xC1] ++ bytes_l10a6a8_2

theorem code_l10a6a8_1 : ∀ x ∈ codeRange 0x10a6ef bytes_l10a6a8_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa6ef 71 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a6a8_2

def b_l10a6a8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10a6a8 (movzxR32M8Effect 0x10a6a8 4 0 (.base 2 (.d8 0x1))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 54) (.exec 0x10a6a8 (LoadPre 0x10a6a8 (fun s => AddrMode.addr (.base 2 (.d8 0x1)) s (0x10a6a8 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a6a8 4 0 (.base 2 (.d8 0x1))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 55) (.out 0x10a6ac (shlR32Effect 0x10a6ac 3 0 16) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x10a6ac (fun s => s.RIP = 0x10a6ac) (shlR32Effect 0x10a6ac 3 0 16) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 57) (.out 0x10a6af (movzxR32M8Effect 0x10a6af 3 1 (.base 2 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2]
    (.letOp (n := 58) (.exec 0x10a6af (LoadPre 0x10a6af (fun s => AddrMode.addr (.base 2 .none) s (0x10a6af + BitVec.ofNat 64 3)) 1) (movzxR32M8Effect 0x10a6af 3 1 (.base 2 .none)) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 59) (.out 0x10a6b2 (orR64R64Effect 0x10a6b2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[57, 55]
    (.letOp (n := 60) (.exec 0x10a6b2 (fun s => s.RIP = 0x10a6b2) (orR64R64Effect 0x10a6b2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[57, 55]
    (.letOp (n := 61) (.out 0x10a6b5 (movzxR32M8Effect 0x10a6b5 4 0 (.base 2 (.d8 0x2))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 62) (.exec 0x10a6b5 (LoadPre 0x10a6b5 (fun s => AddrMode.addr (.base 2 (.d8 0x2)) s (0x10a6b5 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a6b5 4 0 (.base 2 (.d8 0x2))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 63) (.out 0x10a6b9 (shlR64Effect 0x10a6b9 4 0 32) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[61]
    (.letOp (n := 64) (.exec 0x10a6b9 (fun s => s.RIP = 0x10a6b9) (shlR64Effect 0x10a6b9 4 0 32) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[61]
    (.letOp (n := 65) (.out 0x10a6bd (orR64R64Effect 0x10a6bd 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[63, 59]
    (.letOp (n := 66) (.exec 0x10a6bd (fun s => s.RIP = 0x10a6bd) (orR64R64Effect 0x10a6bd 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[63, 59]
    (.letOp (n := 67) (.out 0x10a6c0 (movzxR32M8Effect 0x10a6c0 4 1 (.base 2 (.d8 0x3))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2]
    (.letOp (n := 68) (.exec 0x10a6c0 (LoadPre 0x10a6c0 (fun s => AddrMode.addr (.base 2 (.d8 0x3)) s (0x10a6c0 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a6c0 4 1 (.base 2 (.d8 0x3))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 69) (.out 0x10a6c4 (shlR64Effect 0x10a6c4 4 1 48) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[67]
    (.letOp (n := 70) (.exec 0x10a6c4 (fun s => s.RIP = 0x10a6c4) (shlR64Effect 0x10a6c4 4 1 48) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[67]
    (.letOp (n := 71) (.out 0x10a6c8 (orR64R64Effect 0x10a6c8 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[69, 65]
    (.letOp (n := 72) (.exec 0x10a6c8 (fun s => s.RIP = 0x10a6c8) (orR64R64Effect 0x10a6c8 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[69, 65]
    (.letOp (n := 73) (.out 0x10a6cb (movzxR32M8Effect 0x10a6cb 4 0 (.base 2 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 74) (.exec 0x10a6cb (LoadPre 0x10a6cb (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x10a6cb + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a6cb 4 0 (.base 2 (.d8 0x8))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 75) (.out 0x10a6cf (shlR32Effect 0x10a6cf 3 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[73]
    (.letOp (n := 76) (.exec 0x10a6cf (fun s => s.RIP = 0x10a6cf) (shlR32Effect 0x10a6cf 3 0 8) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[73]
    (.letOp (n := 77) (.out 0x10a6d2 (orR64R64Effect 0x10a6d2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[75, 71]
    (.letOp (n := 78) (.exec 0x10a6d2 (fun s => s.RIP = 0x10a6d2) (orR64R64Effect 0x10a6d2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[75, 71]
    (.letOp (n := 79) (.out 0x10a6d5 (movzxR32M8Effect 0x10a6d5 4 1 (.base 2 (.d8 0x9))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2]
    (.letOp (n := 80) (.exec 0x10a6d5 (LoadPre 0x10a6d5 (fun s => AddrMode.addr (.base 2 (.d8 0x9)) s (0x10a6d5 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a6d5 4 1 (.base 2 (.d8 0x9))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 81) (.out 0x10a6d9 (shlR32Effect 0x10a6d9 3 1 24) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[79]
    (.letOp (n := 82) (.exec 0x10a6d9 (fun s => s.RIP = 0x10a6d9) (shlR32Effect 0x10a6d9 3 1 24) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[79]
    (.letOp (n := 83) (.out 0x10a6dc (orR64R64Effect 0x10a6dc 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[81, 77]
    (.letOp (n := 84) (.exec 0x10a6dc (fun s => s.RIP = 0x10a6dc) (orR64R64Effect 0x10a6dc 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[81, 77]
    (.letOp (n := 85) (.out 0x10a6df (movzxR32M8Effect 0x10a6df 4 0 (.base 2 (.d8 0xa))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 86) (.exec 0x10a6df (LoadPre 0x10a6df (fun s => AddrMode.addr (.base 2 (.d8 0xa)) s (0x10a6df + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a6df 4 0 (.base 2 (.d8 0xa))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 87) (.out 0x10a6e3 (shlR64Effect 0x10a6e3 4 0 40) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[85]
    (.letOp (n := 88) (.exec 0x10a6e3 (fun s => s.RIP = 0x10a6e3) (shlR64Effect 0x10a6e3 4 0 40) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[85]
    (.letOp (n := 89) (.out 0x10a6e7 (orR64R64Effect 0x10a6e7 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[87, 83]
    (.letOp (n := 90) (.exec 0x10a6e7 (fun s => s.RIP = 0x10a6e7) (orR64R64Effect 0x10a6e7 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[87, 83]
    (.letOp (n := 91) (.out 0x10a6ea (movzxR32M8Effect 0x10a6ea 5 8 (.base 2 (.d8 0xb))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[2]
    (.letOp (n := 92) (.exec 0x10a6ea (LoadPre 0x10a6ea (fun s => AddrMode.addr (.base 2 (.d8 0xb)) s (0x10a6ea + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10a6ea 5 8 (.base 2 (.d8 0xb))) (Reg.operands [.gpr 2] [])) #v[2]
    (b_l10a6a8_1))))))))))))))))))))))))))))))))))))))))

def bytes_l10a6a8 : List UInt8 :=
  [0x0F, 0xB6, 0x42, 0x01, 0xC1, 0xE0, 0x10, 0x0F, 0xB6, 0x0A, 0x48, 0x09, 0xC1, 0x0F, 0xB6, 0x42,
    0x02, 0x48, 0xC1, 0xE0, 0x20, 0x48, 0x09, 0xC8, 0x0F, 0xB6, 0x4A, 0x03, 0x48, 0xC1, 0xE1, 0x30,
    0x48, 0x09, 0xC1, 0x0F, 0xB6, 0x42, 0x08, 0xC1, 0xE0, 0x08, 0x48, 0x09, 0xC8, 0x0F, 0xB6, 0x4A,
    0x09, 0xC1, 0xE1, 0x18, 0x48, 0x09, 0xC1, 0x0F, 0xB6, 0x42, 0x0A, 0x48, 0xC1, 0xE0, 0x28, 0x48,
    0x09, 0xC8, 0x44, 0x0F, 0xB6, 0x42, 0x0B] ++ bytes_l10a6a8_1

theorem code_l10a6a8 : ∀ x ∈ codeRange 0x10a6a8 bytes_l10a6a8, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa6a8 71 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a6a8_1

@[cfg_block] def b_l10aa99 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x10aa99 (fun s => s.RIP = 0x10aa99) (movR64R64Effect 0x10aa99 2 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 54) (.exec 0x10aa9c (fun s => s.RIP = 0x10aa9c) (movR32Imm32Effect 0x10aa9c 5 6 0x8) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.exec 0x10aaa1 (fun s => s.RIP = 0x10aaa1) (xorR32R32Effect 0x10aaa1 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[7, 7]
    (.letOp (n := 56) (.exec 0x10aaa3 (fun s => s.RIP = 0x10aaa3) (movR64Imm32Effect 0x10aaa3 1 0x2011f0) (Reg.operands [] [])) #v[]
    (cutBlock 0x10aaaa))))

def bytes_l10aa99 : List UInt8 :=
  [0x48, 0x89, 0xF2, 0xBE, 0x08, 0x00, 0x00, 0x00, 0x31, 0xFF, 0x48, 0xC7, 0xC1, 0xF0, 0x11, 0x20,
    0x00, 0xE8, 0xC1, 0x91, 0xFF, 0xFF]

theorem code_l10aa99 : ∀ x ∈ codeRange 0x10aa99 bytes_l10aa99, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xaa99 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

end AesGcm.Proofs.Machine.LIR
