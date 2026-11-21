import K256.Proofs.Verify.LIR.Labels
import K256.Proofs.Common.CFG.EvalAttr
import K256.Proofs.Common.Lift.Generated.Footprints.Part1
import K256.Proofs.Common.Lift.Generated.Footprints.Part2
import K256.Proofs.Common.Lift.Generated.Footprints.Part3
import K256.Proofs.Common.Lift.Generated.Footprints.Part4
import K256.Proofs.Common.Lift.Generated.Footprints.Part5
import K256.Proofs.Verify.LIR.Generated.Footprints

namespace K256.Proofs.Verify.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Sec1.LIR K256.Proofs.Generate.LIR K256.Proofs.Ecdh.LIR

@[cfg_block] def b_l10581a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10581a (leaR64Effect 0x10581a 0 (.sib 4 none 0 (.d32 0x250))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x10581a (fun s => s.RIP = 0x10581a) (leaR64Effect 0x10581a 0 (.sib 4 none 0 (.d32 0x250))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x105822 (leaR64Effect 0x105822 7 (.sib 4 none 0 (.d32 0x2b0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 56) (.exec 0x105822 (fun s => s.RIP = 0x105822) (leaR64Effect 0x105822 7 (.sib 4 none 0 (.d32 0x2b0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x10582a (leaR64Effect 0x10582a 1 (.sib 4 none 0 (.d32 0x160))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 58) (.exec 0x10582a (fun s => s.RIP = 0x10582a) (leaR64Effect 0x10582a 1 (.sib 4 none 0 (.d32 0x160))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x105832 (movR32Imm32Effect 0x105832 5 2 0x20) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 60) (.exec 0x105832 (fun s => s.RIP = 0x105832) (movR32Imm32Effect 0x105832 5 2 0x20) (Reg.operands [] [])) #v[]
    (.letOp (n := 61) (.out 0x105837 (movR32Imm32Effect 0x105837 6 8 0x20) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 62) (.exec 0x105837 (fun s => s.RIP = 0x105837) (movR32Imm32Effect 0x105837 6 8 0x20) (Reg.operands [] [])) #v[]
    (.letOp (n := 63) (.out 0x10583d (movR32Imm32Effect 0x10583d 6 9 0x1) (EffectPart.reads (.reg (.gpr 9)) [] []) (.reg (.gpr 9))) #v[]
    (.letOp (n := 64) (.exec 0x10583d (fun s => s.RIP = 0x10583d) (movR32Imm32Effect 0x10583d 6 9 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 65) (.out 0x105843 (movR64R64Effect 0x105843 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 12] []) (.reg (.gpr 6))) #v[12]
    (.letOp (n := 66) (.exec 0x105843 (fun s => s.RIP = 0x105843) (movR64R64Effect 0x105843 6 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 67) (.out 0x105846 (pushR64Effect 0x105846 1 0) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 0] []) (.reg (.gpr 4))) #v[4, 53]
    (.letOp (n := 68) (.exec 0x105846 (PushPre 0x105846 1) (pushR64Effect 0x105846 1 0) (Reg.operands [.gpr 4, .gpr 0] [])) #v[4, 53]
    (.letOp (n := 69) (.out 0x105847 (pushImm8Effect 0x105847 2 0x0) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[67]
    (.letOp (n := 70) (.exec 0x105847 (PushPre 0x105847 2) (pushImm8Effect 0x105847 2 0x0) (Reg.operands [.gpr 4] [])) #v[67]
    (.letOp (n := 71) (.out 0x105849 (callEffect (fun _ => 0x100ea0) 0x10584e) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[69]
    (.letOp (n := 72) (.exec 0x105849 (PushPre 0x105849 5) (callEffect (fun _ => 0x100ea0) 0x10584e) (Reg.operands [.gpr 4] [])) #v[69]
    (.letOp (n := 73) (.const ⟨64, 0x10584e⟩) #v[]
    (.terminate (.call ⟨.l100ea0, RegMap.args [(0, 53), (1, 57), (2, 59), (3, 3), (4, 71), (5, 5), (6, 65), (7, 55), (8, 61), (9, 63), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 74⟩ { target := .l10584e, kept := #v[], arity := rfl, guard := some (Fin.last 73) }))))))))))))))))))))))

def bytes_l10581a : List UInt8 :=
  [0x48, 0x8D, 0x84, 0x24, 0x50, 0x02, 0x00, 0x00, 0x48, 0x8D, 0xBC, 0x24, 0xB0, 0x02, 0x00, 0x00,
    0x48, 0x8D, 0x8C, 0x24, 0x60, 0x01, 0x00, 0x00, 0xBA, 0x20, 0x00, 0x00, 0x00, 0x41, 0xB8, 0x20,
    0x00, 0x00, 0x00, 0x41, 0xB9, 0x01, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xE6, 0x50, 0x6A, 0x00, 0xE8,
    0x52, 0xB6, 0xFF, 0xFF]

theorem code_l10581a : ∀ x ∈ codeRange 0x10581a bytes_l10581a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x581a 52 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10584e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10584e (addR64Imm8Effect 0x10584e 4 0x10) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 54) (.exec 0x10584e (fun s => s.RIP = 0x10584e) (addR64Imm8Effect 0x10584e 4 0x10) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x105852 (leaR64Effect 0x105852 3 (.sib 4 none 0 (.d32 0x1c8))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[53]
    (.letOp (n := 56) (.exec 0x105852 (fun s => s.RIP = 0x105852) (leaR64Effect 0x105852 3 (.sib 4 none 0 (.d32 0x1c8))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 57) (.out 0x10585a (leaR64Effect 0x10585a 5 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[53]
    (.letOp (n := 58) (.exec 0x10585a (fun s => s.RIP = 0x10585a) (leaR64Effect 0x10585a 5 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 59) (.out 0x105862 (leaR64Effect 0x105862 15 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[53]
    (.letOp (n := 60) (.exec 0x105862 (fun s => s.RIP = 0x105862) (leaR64Effect 0x105862 15 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[53]
    (.terminate (.br ⟨.l105886, RegMap.args [(0, 0), (3, 55), (4, 53), (5, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩)))))))))

def bytes_l10584e : List UInt8 :=
  [0x48, 0x83, 0xC4, 0x10, 0x48, 0x8D, 0x9C, 0x24, 0xC8, 0x01, 0x00, 0x00, 0x48, 0x8D, 0xAC, 0x24,
    0xC0, 0x00, 0x00, 0x00, 0x4C, 0x8D, 0xBC, 0x24, 0xA0, 0x00, 0x00, 0x00, 0xEB, 0x1A]

theorem code_l10584e : ∀ x ∈ codeRange 0x10584e bytes_l10584e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x584e 30 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105870 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x105870 (leaR64Effect 0x105870 0 (.sib 4 none 0 (.d32 0x100))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x105870 (fun s => s.RIP = 0x105870) (leaR64Effect 0x105870 0 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x105878 (leaR64Effect 0x105878 15 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 56) (.exec 0x105878 (fun s => s.RIP = 0x105878) (leaR64Effect 0x105878 15 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x105880 (movR64R64Effect 0x105880 5 13) (EffectPart.reads (.reg (.gpr 5)) [.gpr 13] []) (.reg (.gpr 5))) #v[13]
    (.letOp (n := 58) (.exec 0x105880 (fun s => s.RIP = 0x105880) (movR64R64Effect 0x105880 5 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 59) (.out 0x105883 (movR64R64Effect 0x105883 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[53]
    (.letOp (n := 60) (.exec 0x105883 (fun s => s.RIP = 0x105883) (movR64R64Effect 0x105883 13 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.terminate (.br ⟨.l105886, RegMap.args [(0, 53), (3, 3), (4, 4), (5, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 14), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩)))))))))

def bytes_l105870 : List UInt8 :=
  [0x48, 0x8D, 0x84, 0x24, 0x00, 0x01, 0x00, 0x00, 0x4C, 0x8D, 0xBC, 0x24, 0xA0, 0x00, 0x00, 0x00,
    0x4C, 0x89, 0xED, 0x49, 0x89, 0xC5]

theorem code_l105870 : ∀ x ∈ codeRange 0x105870 bytes_l105870, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5870 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105886 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x105886 (StorePre 0x105886 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x198)) s (0x105886 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x105886 (.sib 4 none 0 (.d32 0x198)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.exec 0x105892 (StorePre 0x105892 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x190)) s (0x105892 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x105892 (.sib 4 none 0 (.d32 0x190)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x10589e (StorePre 0x10589e 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x188)) s (0x10589e + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x10589e (.sib 4 none 0 (.d32 0x188)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.exec 0x1058aa (StorePre 0x1058aa 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x180)) s (0x1058aa + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1058aa (.sib 4 none 0 (.d32 0x180)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1058b6 (movR32Imm32Effect 0x1058b6 5 2 0x20) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x1058b6 (fun s => s.RIP = 0x1058b6) (movR32Imm32Effect 0x1058b6 5 2 0x20) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x1058bb (leaR64Effect 0x1058bb 7 (.sib 4 none 0 (.d32 0x2b0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 60) (.exec 0x1058bb (fun s => s.RIP = 0x1058bb) (leaR64Effect 0x1058bb 7 (.sib 4 none 0 (.d32 0x2b0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x1058c3 (leaR64Effect 0x1058c3 6 (.sib 4 none 0 (.d32 0x180))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 62) (.exec 0x1058c3 (fun s => s.RIP = 0x1058c3) (leaR64Effect 0x1058c3 6 (.sib 4 none 0 (.d32 0x180))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x1058cb (callEffect (fun _ => 0x100a40) 0x1058d0) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 64) (.exec 0x1058cb (PushPre 0x1058cb 5) (callEffect (fun _ => 0x100a40) 0x1058d0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.const ⟨64, 0x1058d0⟩) #v[]
    (.terminate (.call ⟨.l100a40, RegMap.args [(0, 0), (2, 57), (3, 3), (4, 63), (5, 5), (6, 61), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩ { target := .l1058d0, kept := #v[], arity := rfl, guard := some (Fin.last 65) }))))))))))))))

def bytes_l105886 : List UInt8 :=
  [0x48, 0xC7, 0x84, 0x24, 0x98, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24,
    0x90, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0x88, 0x01, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0x80, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0xBA, 0x20, 0x00, 0x00, 0x00, 0x48, 0x8D, 0xBC, 0x24, 0xB0, 0x02, 0x00, 0x00, 0x48, 0x8D, 0xB4,
    0x24, 0x80, 0x01, 0x00, 0x00, 0xE8, 0x70, 0xB1, 0xFF, 0xFF]

theorem code_l105886 : ∀ x ∈ codeRange 0x105886 bytes_l105886, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5886 74 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1058d0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1058d0 (movR64M64Effect 0x1058d0 0 (.sib 4 none 0 (.d32 0x198))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1058d0 (LoadPre 0x1058d0 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x198)) s (0x1058d0 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1058d0 0 (.sib 4 none 0 (.d32 0x198))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x1058d8 (StorePre 0x1058d8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1e0)) s (0x1058d8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1058d8 0 (.sib 4 none 0 (.d32 0x1e0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x1058e0 (movR64M64Effect 0x1058e0 0 (.sib 4 none 0 (.d32 0x190))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x1058e0 (LoadPre 0x1058e0 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x190)) s (0x1058e0 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1058e0 0 (.sib 4 none 0 (.d32 0x190))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x1058e8 (StorePre 0x1058e8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d8)) s (0x1058e8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1058e8 0 (.sib 4 none 0 (.d32 0x1d8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x1058f0 (movR64M64Effect 0x1058f0 0 (.sib 4 none 0 (.d32 0x180))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x1058f0 (LoadPre 0x1058f0 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x180)) s (0x1058f0 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1058f0 0 (.sib 4 none 0 (.d32 0x180))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x1058f8 (movR64M64Effect 0x1058f8 1 (.sib 4 none 0 (.d32 0x188))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 62) (.exec 0x1058f8 (LoadPre 0x1058f8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x188)) s (0x1058f8 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1058f8 1 (.sib 4 none 0 (.d32 0x188))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x105900 (StorePre 0x105900 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d0)) s (0x105900 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105900 1 (.sib 4 none 0 (.d32 0x1d0))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.exec 0x105908 (StorePre 0x105908 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1c8)) s (0x105908 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105908 0 (.sib 4 none 0 (.d32 0x1c8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 65) (.out 0x105910 (movR64R64Effect 0x105910 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[12]
    (.letOp (n := 66) (.exec 0x105910 (fun s => s.RIP = 0x105910) (movR64R64Effect 0x105910 7 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 67) (.out 0x105913 (movR64R64Effect 0x105913 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[3]
    (.letOp (n := 68) (.exec 0x105913 (fun s => s.RIP = 0x105913) (movR64R64Effect 0x105913 6 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 69) (.out 0x105916 (callEffect (fun _ => 0x109e60) 0x10591b) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 70) (.exec 0x105916 (PushPre 0x105916 5) (callEffect (fun _ => 0x109e60) 0x10591b) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.const ⟨64, 0x10591b⟩) #v[]
    (.terminate (.call ⟨.l109e60, RegMap.args [(0, 59), (1, 61), (2, 2), (3, 3), (4, 69), (5, 5), (6, 67), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩ { target := .l10591b, kept := #v[], arity := rfl, guard := some (Fin.last 71) }))))))))))))))))))))

def bytes_l1058d0 : List UInt8 :=
  [0x48, 0x8B, 0x84, 0x24, 0x98, 0x01, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0xE0, 0x01, 0x00, 0x00,
    0x48, 0x8B, 0x84, 0x24, 0x90, 0x01, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0xD8, 0x01, 0x00, 0x00,
    0x48, 0x8B, 0x84, 0x24, 0x80, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x8C, 0x24, 0x88, 0x01, 0x00, 0x00,
    0x48, 0x89, 0x8C, 0x24, 0xD0, 0x01, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0xC8, 0x01, 0x00, 0x00,
    0x4C, 0x89, 0xE7, 0x48, 0x89, 0xDE, 0xE8, 0x45, 0x45, 0x00, 0x00]

theorem code_l1058d0 : ∀ x ∈ codeRange 0x1058d0 bytes_l1058d0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x58d0 75 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10591b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x10591b (StorePre 0x10591b 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x10591b + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x10591b (.sib 4 none 0 (.d32 0xb8)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.exec 0x105927 (StorePre 0x105927 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x105927 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x105927 (.sib 4 none 0 (.d32 0xb0)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x105933 (StorePre 0x105933 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x105933 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x105933 (.sib 4 none 0 (.d32 0xa8)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.exec 0x10593f (StorePre 0x10593f 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x10593f + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x10593f (.sib 4 none 0 (.d32 0xa0)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x10594b (movR32M32Effect 0x10594b 14 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 58) (.exec 0x10594b (LoadPre 0x10594b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10594b + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x10594b 14 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x105950 (movR64R64Effect 0x105950 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[5]
    (.letOp (n := 60) (.exec 0x105950 (fun s => s.RIP = 0x105950) (movR64R64Effect 0x105950 7 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 61) (.out 0x105953 (movR64R64Effect 0x105953 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 62) (.exec 0x105953 (fun s => s.RIP = 0x105953) (movR64R64Effect 0x105953 6 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 63) (.out 0x105956 (movR64R64Effect 0x105956 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12] []) (.reg (.gpr 2))) #v[12]
    (.letOp (n := 64) (.exec 0x105956 (fun s => s.RIP = 0x105956) (movR64R64Effect 0x105956 2 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 65) (.out 0x105959 (movR32R32Effect 0x105959 3 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[57]
    (.letOp (n := 66) (.exec 0x105959 (fun s => s.RIP = 0x105959) (movR32R32Effect 0x105959 3 1 14) (Reg.operands [.gpr 14] [])) #v[57]
    (.letOp (n := 67) (.out 0x10595c (callEffect (fun _ => 0x10a220) 0x105961) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 68) (.exec 0x10595c (PushPre 0x10595c 5) (callEffect (fun _ => 0x10a220) 0x105961) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.const ⟨64, 0x105961⟩) #v[]
    (.terminate (.call ⟨.l10a220, RegMap.args [(1, 65), (2, 63), (3, 3), (4, 67), (5, 5), (6, 61), (7, 59), (12, 12), (13, 13), (14, 57), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 70⟩ { target := .l105961, kept := #v[], arity := rfl, guard := some (Fin.last 69) }))))))))))))))))))

def bytes_l10591b : List UInt8 :=
  [0x48, 0xC7, 0x84, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24,
    0xB0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0xA8, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x44, 0x8B, 0x74, 0x24, 0x28, 0x48, 0x89, 0xEF, 0x4C, 0x89, 0xFE, 0x4C, 0x89, 0xE2, 0x44, 0x89,
    0xF1, 0xE8, 0xBF, 0x48, 0x00, 0x00]

theorem code_l10591b : ∀ x ∈ codeRange 0x10591b bytes_l10591b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x591b 70 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105961 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x105961 (StorePre 0x105961 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x105961 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x105961 (.sib 4 none 0 (.d32 0x118)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.exec 0x10596d (StorePre 0x10596d 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x10596d + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x10596d (.sib 4 none 0 (.d32 0x110)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x105979 (StorePre 0x105979 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x105979 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x105979 (.sib 4 none 0 (.d32 0x108)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.exec 0x105985 (StorePre 0x105985 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x105985 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x105985 (.sib 4 none 0 (.d32 0x100)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x105991 (movR64R64Effect 0x105991 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[5]
    (.letOp (n := 58) (.exec 0x105991 (fun s => s.RIP = 0x105991) (movR64R64Effect 0x105991 7 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 59) (.out 0x105994 (movR64R64Effect 0x105994 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 13] []) (.reg (.gpr 6))) #v[13]
    (.letOp (n := 60) (.exec 0x105994 (fun s => s.RIP = 0x105994) (movR64R64Effect 0x105994 6 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 61) (.out 0x105997 (callEffect (fun _ => 0x10a280) 0x10599c) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 62) (.exec 0x105997 (PushPre 0x105997 5) (callEffect (fun _ => 0x10a280) 0x10599c) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.const ⟨64, 0x10599c⟩) #v[]
    (.terminate (.call ⟨.l10a280, RegMap.args [(0, 0), (3, 3), (4, 61), (5, 5), (6, 59), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ { target := .l10599c, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l105961 : List UInt8 :=
  [0x48, 0xC7, 0x84, 0x24, 0x18, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24,
    0x10, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0x08, 0x01, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x48, 0x89, 0xEF, 0x4C, 0x89, 0xEE, 0xE8, 0xE4, 0x48, 0x00, 0x00]

theorem code_l105961 : ∀ x ∈ codeRange 0x105961 bytes_l105961, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5961 59 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10599c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10599c (notR8Effect 0x10599c 2 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 54) (.exec 0x10599c (fun s => s.RIP = 0x10599c) (notR8Effect 0x10599c 2 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x10599e (andAlImm8Effect 0x10599e 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x10599e (fun s => s.RIP = 0x10599e) (andAlImm8Effect 0x10599e 0x1) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x1059a0 (movzxR32R8Effect 0x1059a0 3 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[55]
    (.letOp (n := 58) (.exec 0x1059a0 (fun s => s.RIP = 0x1059a0) (movzxR32R8Effect 0x1059a0 3 7 0) (Reg.operands [.gpr 0] [])) #v[55]
    (.letOp (n := 59) (.out 0x1059a3 (callEffect (fun _ => 0x127d50) 0x1059a8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x1059a3 (PushPre 0x1059a3 5) (callEffect (fun _ => 0x127d50) 0x1059a8) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x1059a8⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(0, 55), (1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l1059a8, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l10599c : List UInt8 :=
  [0xF6, 0xD0, 0x24, 0x01, 0x0F, 0xB6, 0xF8, 0xE8, 0xA8, 0x23, 0x02, 0x00]

theorem code_l10599c : ∀ x ∈ codeRange 0x10599c bytes_l10599c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x599c 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1059a8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1059a8 (movR64M64Effect 0x1059a8 1 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x1059a8 (LoadPre 0x1059a8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x1059a8 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1059a8 1 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1059b0 (movR64M64Effect 0x1059b0 2 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 56) (.exec 0x1059b0 (LoadPre 0x1059b0 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x1059b0 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1059b0 2 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x1059b8 (StorePre 0x1059b8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1059b8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1059b8 1 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 58) (.exec 0x1059c0 (StorePre 0x1059c0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1059c0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1059c0 2 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 59) (.out 0x1059c8 (movR64M64Effect 0x1059c8 1 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 60) (.exec 0x1059c8 (LoadPre 0x1059c8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x1059c8 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1059c8 1 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x1059d0 (StorePre 0x1059d0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x1059d0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1059d0 1 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x1059d8 (movR64M64Effect 0x1059d8 1 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 63) (.exec 0x1059d8 (LoadPre 0x1059d8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x1059d8 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1059d8 1 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x1059e0 (StorePre 0x1059e0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x1059e0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1059e0 1 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x1059e8 (andR8R8Effect 0x1059e8 3 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[0, 14]
    (.letOp (n := 66) (.exec 0x1059e8 (fun s => s.RIP = 0x1059e8) (andR8R8Effect 0x1059e8 3 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[0, 14]
    (.letOp (n := 67) (.out 0x1059eb (movzxR32R8Effect 0x1059eb 3 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[65]
    (.letOp (n := 68) (.exec 0x1059eb (fun s => s.RIP = 0x1059eb) (movzxR32R8Effect 0x1059eb 3 7 0) (Reg.operands [.gpr 0] [])) #v[65]
    (.letOp (n := 69) (.out 0x1059ee (callEffect (fun _ => 0x127d50) 0x1059f3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 70) (.exec 0x1059ee (PushPre 0x1059ee 5) (callEffect (fun _ => 0x127d50) 0x1059f3) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.const ⟨64, 0x1059f3⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(0, 65), (1, 62), (2, 55), (3, 3), (4, 69), (5, 5), (6, 6), (7, 67), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩ { target := .l1059f3, kept := #v[], arity := rfl, guard := some (Fin.last 71) }))))))))))))))))))))

def bytes_l1059a8 : List UInt8 :=
  [0x48, 0x8B, 0x8C, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x94, 0x24, 0xC8, 0x00, 0x00, 0x00,
    0x48, 0x89, 0x8C, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0x89, 0x94, 0x24, 0x88, 0x00, 0x00, 0x00,
    0x48, 0x8B, 0x8C, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x8C, 0x24, 0x90, 0x00, 0x00, 0x00,
    0x48, 0x8B, 0x8C, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x8C, 0x24, 0x98, 0x00, 0x00, 0x00,
    0x44, 0x20, 0xF0, 0x0F, 0xB6, 0xF8, 0xE8, 0x5D, 0x23, 0x02, 0x00]

theorem code_l1059a8 : ∀ x ∈ codeRange 0x1059a8 bytes_l1059a8, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x59a8 75 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1059f3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1059f3 (cmpAlImm8Effect 0x1059f3 0x1) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[0]
    (.letOp (n := 54) (.exec 0x1059f3 (fun s => s.RIP = 0x1059f3) (cmpAlImm8Effect 0x1059f3 0x1) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l105886, RegMap.args [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l1059fb, RegMap.args [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l1059f3 : List UInt8 :=
  [0x3C, 0x01, 0x0F, 0x85, 0x8B, 0xFE, 0xFF, 0xFF]

theorem code_l1059f3 : ∀ x ∈ codeRange 0x1059f3 bytes_l1059f3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x59f3 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1059fb_1 : Block Op Label signature Reg.count 80 :=
  .letOp (n := 80) (.out 0x105a9c (movR64R64Effect 0x105a9c 2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13] []) (.reg (.gpr 2))) #v[13]
    (.letOp (n := 81) (.exec 0x105a9c (fun s => s.RIP = 0x105a9c) (movR64R64Effect 0x105a9c 2 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 82) (.out 0x105a9f (movR32Imm32Effect 0x105a9f 6 8 0x100) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 83) (.exec 0x105a9f (fun s => s.RIP = 0x105a9f) (movR32Imm32Effect 0x105a9f 6 8 0x100) (Reg.operands [] [])) #v[]
    (.letOp (n := 84) (.out 0x105aa5 (callEffect (fun _ => 0x127d70) 0x105aaa) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 85) (.exec 0x105aa5 (PushPre 0x105aa5 5) (callEffect (fun _ => 0x127d70) 0x105aaa) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 86) (.const ⟨64, 0x105aaa⟩) #v[]
    (.terminate (.call ⟨.l127d70, RegMap.args [(0, 59), (1, 76), (2, 80), (3, 3), (4, 84), (5, 5), (6, 74), (7, 78), (8, 82), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 87⟩ { target := .l105aaa, kept := #v[], arity := rfl, guard := some (Fin.last 86) }))))))))

def bytes_l1059fb_1 : List UInt8 :=
  [0x4C, 0x89, 0xEA, 0x41, 0xB8, 0x00, 0x01, 0x00, 0x00, 0xE8, 0xC6, 0x22, 0x02, 0x00]

theorem code_l1059fb_1 : ∀ x ∈ codeRange 0x105a9c bytes_l1059fb_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5a9c 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1059fb : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1059fb (movR64M64Effect 0x1059fb 0 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1059fb (LoadPre 0x1059fb (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x1059fb + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1059fb 0 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x105a03 (StorePre 0x105a03 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x288)) s (0x105a03 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105a03 0 (.sib 4 none 0 (.d32 0x288))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x105a0b (movR64M64Effect 0x105a0b 0 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x105a0b (LoadPre 0x105a0b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x105a0b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105a0b 0 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x105a13 (StorePre 0x105a13 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x280)) s (0x105a13 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105a13 0 (.sib 4 none 0 (.d32 0x280))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x105a1b (movR64M64Effect 0x105a1b 0 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x105a1b (LoadPre 0x105a1b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x105a1b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105a1b 0 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x105a23 (movR64M64Effect 0x105a23 1 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 62) (.exec 0x105a23 (LoadPre 0x105a23 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x105a23 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105a23 1 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x105a2b (StorePre 0x105a2b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x278)) s (0x105a2b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105a2b 1 (.sib 4 none 0 (.d32 0x278))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.exec 0x105a33 (StorePre 0x105a33 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x270)) s (0x105a33 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105a33 0 (.sib 4 none 0 (.d32 0x270))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 65) (.exec 0x105a3b (StorePre 0x105a3b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x105a3b + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x105a3b (.sib 4 none 0 (.d8 0x8)) 0x1) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x105a40 (StorePre 0x105a40 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x105a40 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x105a40 (.sib 4 none 0 (.d8 0x8)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x105a45 (StorePre 0x105a45 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x105a45 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x105a45 (.sib 4 none 0 (.d8 0x8)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.exec 0x105a4a (StorePre 0x105a4a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x105a4a + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x105a4a (.sib 4 none 0 (.d8 0x8)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.exec 0x105a4f (StorePre 0x105a4f 11 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x105a4f + BitVec.ofNat 64 11)) 4) (movM32Imm32Effect 0x105a4f 11 (.sib 4 none 0 (.d32 0xc0)) 0x100) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.exec 0x105a5a (StorePre 0x105a5a 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x105a5a + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x105a5a (.sib 4 none 0 (.d32 0x118)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.exec 0x105a66 (StorePre 0x105a66 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x105a66 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x105a66 (.sib 4 none 0 (.d32 0x110)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.exec 0x105a72 (StorePre 0x105a72 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x105a72 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x105a72 (.sib 4 none 0 (.d32 0x108)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.exec 0x105a7e (StorePre 0x105a7e 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x105a7e + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x105a7e (.sib 4 none 0 (.d32 0x100)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.out 0x105a8a (movR32Imm32Effect 0x105a8a 5 6 0x20) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 75) (.exec 0x105a8a (fun s => s.RIP = 0x105a8a) (movR32Imm32Effect 0x105a8a 5 6 0x20) (Reg.operands [] [])) #v[]
    (.letOp (n := 76) (.out 0x105a8f (movR32Imm32Effect 0x105a8f 5 1 0x4) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 77) (.exec 0x105a8f (fun s => s.RIP = 0x105a8f) (movR32Imm32Effect 0x105a8f 5 1 0x4) (Reg.operands [] [])) #v[]
    (.letOp (n := 78) (.out 0x105a94 (leaR64Effect 0x105a94 7 (.sib 4 none 0 (.d32 0x160))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 79) (.exec 0x105a94 (fun s => s.RIP = 0x105a94) (leaR64Effect 0x105a94 7 (.sib 4 none 0 (.d32 0x160))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l1059fb_1)))))))))))))))))))))))))))

def bytes_l1059fb : List UInt8 :=
  [0x48, 0x8B, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0x88, 0x02, 0x00, 0x00,
    0x48, 0x8B, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0x80, 0x02, 0x00, 0x00,
    0x48, 0x8B, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x8C, 0x24, 0x88, 0x00, 0x00, 0x00,
    0x48, 0x89, 0x8C, 0x24, 0x78, 0x02, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0x70, 0x02, 0x00, 0x00,
    0xC6, 0x44, 0x24, 0x08, 0x01, 0xC6, 0x44, 0x24, 0x08, 0x00, 0xC6, 0x44, 0x24, 0x08, 0x00, 0xC6,
    0x44, 0x24, 0x08, 0x00, 0xC7, 0x84, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x48,
    0xC7, 0x84, 0x24, 0x18, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0x10,
    0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0x08, 0x01, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xBE,
    0x20, 0x00, 0x00, 0x00, 0xB9, 0x04, 0x00, 0x00, 0x00, 0x48, 0x8D, 0xBC, 0x24, 0x60, 0x01, 0x00,
    0x00] ++ bytes_l1059fb_1

theorem code_l1059fb : ∀ x ∈ codeRange 0x1059fb bytes_l1059fb, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x59fb 161 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1059fb_1

@[cfg_block] def b_l105aaa : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x105aaa (cmpAlImm8Effect 0x105aaa 0xff) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[0]
    (.letOp (n := 54) (.exec 0x105aaa (fun s => s.RIP = 0x105aaa) (cmpAlImm8Effect 0x105aaa 0xff) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x105aac (leaR64Effect 0x105aac 13 (.sib 4 none 0 (.d32 0x290))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 56) (.exec 0x105aac (fun s => s.RIP = 0x105aac) (leaR64Effect 0x105aac 13 (.sib 4 none 0 (.d32 0x290))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 57) ⟨.l105eba, RegMap.args [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 55), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l105aba, RegMap.args [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 55), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l105aaa : List UInt8 :=
  [0x3C, 0xFF, 0x4C, 0x8D, 0xAC, 0x24, 0x90, 0x02, 0x00, 0x00, 0x0F, 0x85, 0x00, 0x04, 0x00, 0x00]

theorem code_l105aaa : ∀ x ∈ codeRange 0x105aaa bytes_l105aaa, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5aaa 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105aba : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x105aba (movR64R64Effect 0x105aba 15 3) (EffectPart.reads (.reg (.gpr 15)) [.gpr 3] []) (.reg (.gpr 15))) #v[3]
    (.letOp (n := 54) (.exec 0x105aba (fun s => s.RIP = 0x105aba) (movR64R64Effect 0x105aba 15 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x105abd (movR64M64Effect 0x105abd 0 (.sib 4 none 0 (.d32 0x118))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 56) (.exec 0x105abd (LoadPre 0x105abd (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x105abd + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105abd 0 (.sib 4 none 0 (.d32 0x118))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x105ac5 (StorePre 0x105ac5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x105ac5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x105ac5 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 58) (.out 0x105aca (movR64M64Effect 0x105aca 0 (.sib 4 none 0 (.d32 0x110))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 59) (.exec 0x105aca (LoadPre 0x105aca (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x105aca + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105aca 0 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.exec 0x105ad2 (StorePre 0x105ad2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x105ad2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x105ad2 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[58, 4]
    (.letOp (n := 61) (.out 0x105ad7 (movR64M64Effect 0x105ad7 0 (.sib 4 none 0 (.d32 0x100))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 62) (.exec 0x105ad7 (LoadPre 0x105ad7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x105ad7 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105ad7 0 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x105adf (movR64M64Effect 0x105adf 1 (.sib 4 none 0 (.d32 0x108))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 64) (.exec 0x105adf (LoadPre 0x105adf (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x105adf + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105adf 1 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.exec 0x105ae7 (StorePre 0x105ae7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x105ae7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x105ae7 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[63, 4]
    (.letOp (n := 66) (.exec 0x105aec (StorePre 0x105aec 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x105aec + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x105aec 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 67) (.out 0x105af1 (movR64R64Effect 0x105af1 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 13] []) (.reg (.gpr 7))) #v[13]
    (.letOp (n := 68) (.exec 0x105af1 (fun s => s.RIP = 0x105af1) (movR64R64Effect 0x105af1 7 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 69) (.out 0x105af4 (movR64R64Effect 0x105af4 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 12] []) (.reg (.gpr 6))) #v[12]
    (.letOp (n := 70) (.exec 0x105af4 (fun s => s.RIP = 0x105af4) (movR64R64Effect 0x105af4 6 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 71) (.out 0x105af7 (callEffect (fun _ => 0x109f80) 0x105afc) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 72) (.exec 0x105af7 (PushPre 0x105af7 5) (callEffect (fun _ => 0x109f80) 0x105afc) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.const ⟨64, 0x105afc⟩) #v[]
    (.terminate (.call ⟨.l109f80, RegMap.args [(0, 61), (1, 63), (3, 3), (4, 71), (5, 5), (6, 69), (7, 67), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 74⟩ { target := .l105afc, kept := #v[], arity := rfl, guard := some (Fin.last 73) }))))))))))))))))))))))

def bytes_l105aba : List UInt8 :=
  [0x49, 0x89, 0xDF, 0x48, 0x8B, 0x84, 0x24, 0x18, 0x01, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x20,
    0x48, 0x8B, 0x84, 0x24, 0x10, 0x01, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x84,
    0x24, 0x00, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x8C, 0x24, 0x08, 0x01, 0x00, 0x00, 0x48, 0x89, 0x4C,
    0x24, 0x10, 0x48, 0x89, 0x44, 0x24, 0x08, 0x4C, 0x89, 0xEF, 0x4C, 0x89, 0xE6, 0xE8, 0x84, 0x44,
    0x00, 0x00]

theorem code_l105aba : ∀ x ∈ codeRange 0x105aba bytes_l105aba, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5aba 66 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105afc : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x105afc (movR64R64Effect 0x105afc 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[12]
    (.letOp (n := 54) (.exec 0x105afc (fun s => s.RIP = 0x105afc) (movR64R64Effect 0x105afc 7 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 55) (.out 0x105aff (leaR64Effect 0x105aff 3 (.sib 4 none 0 (.d32 0x270))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 56) (.exec 0x105aff (fun s => s.RIP = 0x105aff) (leaR64Effect 0x105aff 3 (.sib 4 none 0 (.d32 0x270))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x105b07 (movR64R64Effect 0x105b07 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[55]
    (.letOp (n := 58) (.exec 0x105b07 (fun s => s.RIP = 0x105b07) (movR64R64Effect 0x105b07 6 3) (Reg.operands [.gpr 3] [])) #v[55]
    (.letOp (n := 59) (.out 0x105b0a (callEffect (fun _ => 0x109d80) 0x105b0f) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x105b0a (PushPre 0x105b0a 5) (callEffect (fun _ => 0x109d80) 0x105b0f) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x105b0f⟩) #v[]
    (.terminate (.call ⟨.l109d80, RegMap.args [(3, 55), (4, 59), (5, 5), (6, 57), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l105b0f, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l105afc : List UInt8 :=
  [0x4C, 0x89, 0xE7, 0x48, 0x8D, 0x9C, 0x24, 0x70, 0x02, 0x00, 0x00, 0x48, 0x89, 0xDE, 0xE8, 0x71,
    0x42, 0x00, 0x00]

theorem code_l105afc : ∀ x ∈ codeRange 0x105afc bytes_l105afc, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5afc 19 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105b0f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x105b0f (movzxR32M8Effect 0x105b0f 5 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x105b0f (LoadPre 0x105b0f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x105b0f + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x105b0f 5 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x105b14 (StorePre 0x105b14 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x105b14 + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x105b14 7 0 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x105b1b (cmpAlImm8Effect 0x105b1b 0x1) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[53]
    (.letOp (n := 57) (.exec 0x105b1b (fun s => s.RIP = 0x105b1b) (cmpAlImm8Effect 0x105b1b 0x1) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 58) (.pure (condOp 5)) #v[56]
    (.terminate (.condBr (Fin.last 58) ⟨.l105ed3, RegMap.args [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩ ⟨.l105b23, RegMap.args [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l105b0f : List UInt8 :=
  [0x0F, 0xB6, 0x44, 0x24, 0x28, 0x88, 0x84, 0x24, 0x00, 0x01, 0x00, 0x00, 0x3C, 0x01, 0x0F, 0x85,
    0xB0, 0x03, 0x00, 0x00]

theorem code_l105b0f : ∀ x ∈ codeRange 0x105b0f bytes_l105b0f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5b0f 20 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105b23 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x105b23 (movR64M64Effect 0x105b23 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x105b23 (LoadPre 0x105b23 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x105b23 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x105b23 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x105b28 (movR64M64Effect 0x105b28 1 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x105b28 (LoadPre 0x105b28 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x105b28 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x105b28 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x105b2d (StorePre 0x105b2d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1a8)) s (0x105b2d + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105b2d 0 (.sib 4 none 0 (.d32 0x1a8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 58) (.exec 0x105b35 (StorePre 0x105b35 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1b0)) s (0x105b35 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105b35 1 (.sib 4 none 0 (.d32 0x1b0))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 59) (.out 0x105b3d (movR64M64Effect 0x105b3d 0 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x105b3d (LoadPre 0x105b3d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x105b3d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x105b3d 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x105b42 (StorePre 0x105b42 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1b8)) s (0x105b42 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105b42 0 (.sib 4 none 0 (.d32 0x1b8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x105b4a (movR64M64Effect 0x105b4a 0 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x105b4a (LoadPre 0x105b4a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x105b4a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x105b4a 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x105b4f (StorePre 0x105b4f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1c0)) s (0x105b4f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105b4f 0 (.sib 4 none 0 (.d32 0x1c0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x105b57 (movR64R64Effect 0x105b57 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[12]
    (.letOp (n := 66) (.exec 0x105b57 (fun s => s.RIP = 0x105b57) (movR64R64Effect 0x105b57 7 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 67) (.out 0x105b5a (movR64R64Effect 0x105b5a 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[3]
    (.letOp (n := 68) (.exec 0x105b5a (fun s => s.RIP = 0x105b5a) (movR64R64Effect 0x105b5a 6 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 69) (.out 0x105b5d (callEffect (fun _ => 0x10ee80) 0x105b62) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 70) (.exec 0x105b5d (PushPre 0x105b5d 5) (callEffect (fun _ => 0x10ee80) 0x105b62) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.const ⟨64, 0x105b62⟩) #v[]
    (.terminate (.call ⟨.l10ee80, RegMap.args [(0, 62), (1, 55), (3, 3), (4, 69), (5, 5), (6, 67), (7, 65), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩ { target := .l105b62, kept := #v[], arity := rfl, guard := some (Fin.last 71) }))))))))))))))))))))

def bytes_l105b23 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x08, 0x48, 0x8B, 0x4C, 0x24, 0x10, 0x48, 0x89, 0x84, 0x24, 0xA8, 0x01,
    0x00, 0x00, 0x48, 0x89, 0x8C, 0x24, 0xB0, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x18, 0x48,
    0x89, 0x84, 0x24, 0xB8, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x20, 0x48, 0x89, 0x84, 0x24,
    0xC0, 0x01, 0x00, 0x00, 0x4C, 0x89, 0xE7, 0x48, 0x89, 0xDE, 0xE8, 0x1E, 0x93, 0x00, 0x00]

theorem code_l105b23 : ∀ x ∈ codeRange 0x105b23 bytes_l105b23, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5b23 63 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105b62 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x105b62 (leaR64Effect 0x105b62 3 (.sib 4 none 0 (.d32 0x100))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 54) (.exec 0x105b62 (fun s => s.RIP = 0x105b62) (leaR64Effect 0x105b62 3 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x105b6a (movR64R64Effect 0x105b6a 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 56) (.exec 0x105b6a (fun s => s.RIP = 0x105b6a) (movR64R64Effect 0x105b6a 7 3) (Reg.operands [.gpr 3] [])) #v[53]
    (.letOp (n := 57) (.out 0x105b6d (movR64R64Effect 0x105b6d 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 12] []) (.reg (.gpr 6))) #v[12]
    (.letOp (n := 58) (.exec 0x105b6d (fun s => s.RIP = 0x105b6d) (movR64R64Effect 0x105b6d 6 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 59) (.out 0x105b70 (callEffect (fun _ => 0x10fe50) 0x105b75) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x105b70 (PushPre 0x105b70 5) (callEffect (fun _ => 0x10fe50) 0x105b75) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x105b75⟩) #v[]
    (.terminate (.call ⟨.l10fe50, RegMap.args [(3, 53), (4, 59), (5, 5), (6, 57), (7, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l105b75, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l105b62 : List UInt8 :=
  [0x48, 0x8D, 0x9C, 0x24, 0x00, 0x01, 0x00, 0x00, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xE6, 0xE8, 0xDB,
    0xA2, 0x00, 0x00]

theorem code_l105b62 : ∀ x ∈ codeRange 0x105b62 bytes_l105b62, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5b62 19 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105b75 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x105b75 (leaR64Effect 0x105b75 14 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 54) (.exec 0x105b75 (fun s => s.RIP = 0x105b75) (leaR64Effect 0x105b75 14 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x105b7d (movR64R64Effect 0x105b7d 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 56) (.exec 0x105b7d (fun s => s.RIP = 0x105b7d) (movR64R64Effect 0x105b7d 7 14) (Reg.operands [.gpr 14] [])) #v[53]
    (.letOp (n := 57) (.out 0x105b80 (movR64R64Effect 0x105b80 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[3]
    (.letOp (n := 58) (.exec 0x105b80 (fun s => s.RIP = 0x105b80) (movR64R64Effect 0x105b80 6 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 59) (.out 0x105b83 (callEffect (fun _ => 0x120350) 0x105b88) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x105b83 (PushPre 0x105b83 5) (callEffect (fun _ => 0x120350) 0x105b88) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x105b88⟩) #v[]
    (.terminate (.call ⟨.l120350, RegMap.args [(3, 3), (4, 59), (5, 5), (6, 57), (7, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l105b88, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l105b75 : List UInt8 :=
  [0x4C, 0x8D, 0xB4, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF7, 0x48, 0x89, 0xDE, 0xE8, 0xC8,
    0xA7, 0x01, 0x00]

theorem code_l105b75 : ∀ x ∈ codeRange 0x105b75 bytes_l105b75, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5b75 19 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105b88 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x105b88 (StorePre 0x105b88 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x105b88 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x105b88 (.sib 4 none 0 (.d8 0x8)) 0x1) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.exec 0x105b8d (StorePre 0x105b8d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x105b8d + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x105b8d (.sib 4 none 0 (.d8 0x8)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x105b92 (StorePre 0x105b92 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x105b92 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x105b92 (.sib 4 none 0 (.d8 0x8)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.exec 0x105b97 (StorePre 0x105b97 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x105b97 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x105b97 (.sib 4 none 0 (.d8 0x8)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x105b9c (StorePre 0x105b9c 11 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1c8)) s (0x105b9c + BitVec.ofNat 64 11)) 4) (movM32Imm32Effect 0x105b9c 11 (.sib 4 none 0 (.d32 0x1c8)) 0x100) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x105ba7 (StorePre 0x105ba7 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x105ba7 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x105ba7 (.sib 4 none 0 (.d32 0xd8)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.exec 0x105bb3 (StorePre 0x105bb3 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x105bb3 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x105bb3 (.sib 4 none 0 (.d32 0xd0)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.exec 0x105bbf (StorePre 0x105bbf 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x105bbf + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x105bbf (.sib 4 none 0 (.d32 0xc8)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x105bcb (StorePre 0x105bcb 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x105bcb + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x105bcb (.sib 4 none 0 (.d32 0xc0)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.out 0x105bd7 (movR32Imm32Effect 0x105bd7 5 6 0x20) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 63) (.exec 0x105bd7 (fun s => s.RIP = 0x105bd7) (movR32Imm32Effect 0x105bd7 5 6 0x20) (Reg.operands [] [])) #v[]
    (.letOp (n := 64) (.out 0x105bdc (movR32Imm32Effect 0x105bdc 5 1 0x4) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 65) (.exec 0x105bdc (fun s => s.RIP = 0x105bdc) (movR32Imm32Effect 0x105bdc 5 1 0x4) (Reg.operands [] [])) #v[]
    (.letOp (n := 66) (.out 0x105be1 (movR64R64Effect 0x105be1 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 67) (.exec 0x105be1 (fun s => s.RIP = 0x105be1) (movR64R64Effect 0x105be1 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 68) (.out 0x105be4 (movR64R64Effect 0x105be4 2 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5] []) (.reg (.gpr 2))) #v[5]
    (.letOp (n := 69) (.exec 0x105be4 (fun s => s.RIP = 0x105be4) (movR64R64Effect 0x105be4 2 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 70) (.out 0x105be7 (movR32Imm32Effect 0x105be7 6 8 0x100) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 71) (.exec 0x105be7 (fun s => s.RIP = 0x105be7) (movR32Imm32Effect 0x105be7 6 8 0x100) (Reg.operands [] [])) #v[]
    (.letOp (n := 72) (.out 0x105bed (callEffect (fun _ => 0x127d70) 0x105bf2) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x105bed (PushPre 0x105bed 5) (callEffect (fun _ => 0x127d70) 0x105bf2) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x105bf2⟩) #v[]
    (.terminate (.call ⟨.l127d70, RegMap.args [(0, 0), (1, 64), (2, 68), (3, 3), (4, 72), (5, 5), (6, 62), (7, 66), (8, 70), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l105bf2, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l105b88 : List UInt8 :=
  [0xC6, 0x44, 0x24, 0x08, 0x01, 0xC6, 0x44, 0x24, 0x08, 0x00, 0xC6, 0x44, 0x24, 0x08, 0x00, 0xC6,
    0x44, 0x24, 0x08, 0x00, 0xC7, 0x84, 0x24, 0xC8, 0x01, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x48,
    0xC7, 0x84, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0xD0,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xBE,
    0x20, 0x00, 0x00, 0x00, 0xB9, 0x04, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF7, 0x48, 0x89, 0xEA, 0x41,
    0xB8, 0x00, 0x01, 0x00, 0x00, 0xE8, 0x7E, 0x21, 0x02, 0x00]

theorem code_l105b88 : ∀ x ∈ codeRange 0x105b88 bytes_l105b88, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5b88 106 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105bf2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x105bf2 (cmpAlImm8Effect 0x105bf2 0xff) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[0]
    (.letOp (n := 54) (.exec 0x105bf2 (fun s => s.RIP = 0x105bf2) (cmpAlImm8Effect 0x105bf2 0xff) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l105ef2, RegMap.args [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l105bfa, RegMap.args [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l105bf2 : List UInt8 :=
  [0x3C, 0xFF, 0x0F, 0x85, 0xF8, 0x02, 0x00, 0x00]

theorem code_l105bf2 : ∀ x ∈ codeRange 0x105bf2 bytes_l105bf2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5bf2 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105bfa : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x105bfa (movR64M64Effect 0x105bfa 0 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x105bfa (LoadPre 0x105bfa (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x105bfa + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105bfa 0 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x105c02 (StorePre 0x105c02 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x105c02 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x105c02 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x105c07 (movR64M64Effect 0x105c07 0 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x105c07 (LoadPre 0x105c07 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x105c07 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105c07 0 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x105c0f (StorePre 0x105c0f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x105c0f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x105c0f 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x105c14 (movR64M64Effect 0x105c14 0 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x105c14 (LoadPre 0x105c14 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x105c14 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105c14 0 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x105c1c (movR64M64Effect 0x105c1c 1 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 62) (.exec 0x105c1c (LoadPre 0x105c1c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x105c1c + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105c1c 1 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x105c24 (StorePre 0x105c24 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x105c24 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x105c24 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.exec 0x105c29 (StorePre 0x105c29 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x105c29 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x105c29 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 65) (.out 0x105c2e (leaR64Effect 0x105c2e 7 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 66) (.exec 0x105c2e (fun s => s.RIP = 0x105c2e) (leaR64Effect 0x105c2e 7 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x105c36 (movR64R64Effect 0x105c36 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 12] []) (.reg (.gpr 6))) #v[12]
    (.letOp (n := 68) (.exec 0x105c36 (fun s => s.RIP = 0x105c36) (movR64R64Effect 0x105c36 6 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 69) (.out 0x105c39 (callEffect (fun _ => 0x109f80) 0x105c3e) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 70) (.exec 0x105c39 (PushPre 0x105c39 5) (callEffect (fun _ => 0x109f80) 0x105c3e) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.const ⟨64, 0x105c3e⟩) #v[]
    (.terminate (.call ⟨.l109f80, RegMap.args [(0, 59), (1, 61), (3, 3), (4, 69), (5, 5), (6, 67), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩ { target := .l105c3e, kept := #v[], arity := rfl, guard := some (Fin.last 71) }))))))))))))))))))))

def bytes_l105bfa : List UInt8 :=
  [0x48, 0x8B, 0x84, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x84,
    0x24, 0xD0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x84, 0x24, 0xC0, 0x00,
    0x00, 0x00, 0x48, 0x8B, 0x8C, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x4C, 0x24, 0x10, 0x48,
    0x89, 0x44, 0x24, 0x08, 0x48, 0x8D, 0xBC, 0x24, 0x80, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xE6, 0xE8,
    0x42, 0x43, 0x00, 0x00]

theorem code_l105bfa : ∀ x ∈ codeRange 0x105bfa bytes_l105bfa, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5bfa 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105c3e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x105c3e (movR64M64Effect 0x105c3e 0 (.sib 4 none 0 (.d32 0x1c0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x105c3e (LoadPre 0x105c3e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1c0)) s (0x105c3e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105c3e 0 (.sib 4 none 0 (.d32 0x1c0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x105c46 (StorePre 0x105c46 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x105c46 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105c46 0 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x105c4e (movR64M64Effect 0x105c4e 0 (.sib 4 none 0 (.d32 0x1b8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x105c4e (LoadPre 0x105c4e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1b8)) s (0x105c4e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105c4e 0 (.sib 4 none 0 (.d32 0x1b8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x105c56 (StorePre 0x105c56 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x105c56 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105c56 0 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x105c5e (movR64M64Effect 0x105c5e 0 (.sib 4 none 0 (.d32 0x1a8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x105c5e (LoadPre 0x105c5e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1a8)) s (0x105c5e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105c5e 0 (.sib 4 none 0 (.d32 0x1a8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x105c66 (movR64M64Effect 0x105c66 1 (.sib 4 none 0 (.d32 0x1b0))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 62) (.exec 0x105c66 (LoadPre 0x105c66 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1b0)) s (0x105c66 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105c66 1 (.sib 4 none 0 (.d32 0x1b0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x105c6e (StorePre 0x105c6e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x105c6e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105c6e 1 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.exec 0x105c76 (StorePre 0x105c76 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x105c76 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105c76 0 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 65) (.out 0x105c7e (movR64M64Effect 0x105c7e 0 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 66) (.exec 0x105c7e (LoadPre 0x105c7e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x105c7e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105c7e 0 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x105c86 (StorePre 0x105c86 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x105c86 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x105c86 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x105c8b (movR64M64Effect 0x105c8b 0 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 69) (.exec 0x105c8b (LoadPre 0x105c8b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x105c8b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105c8b 0 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.exec 0x105c93 (StorePre 0x105c93 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x105c93 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x105c93 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[68, 4]
    (.letOp (n := 71) (.out 0x105c98 (movR64M64Effect 0x105c98 0 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 72) (.exec 0x105c98 (LoadPre 0x105c98 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x105c98 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105c98 0 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.out 0x105ca0 (movR64M64Effect 0x105ca0 1 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 74) (.exec 0x105ca0 (LoadPre 0x105ca0 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x105ca0 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105ca0 1 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.exec 0x105ca8 (StorePre 0x105ca8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x105ca8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x105ca8 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[73, 4]
    (.letOp (n := 76) (.exec 0x105cad (StorePre 0x105cad 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x105cad + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x105cad 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[71, 4]
    (.letOp (n := 77) (.out 0x105cb2 (movR64R64Effect 0x105cb2 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[5]
    (.letOp (n := 78) (.exec 0x105cb2 (fun s => s.RIP = 0x105cb2) (movR64R64Effect 0x105cb2 7 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 79) (.out 0x105cb5 (movR64R64Effect 0x105cb5 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 12] []) (.reg (.gpr 6))) #v[12]
    (.letOp (n := 80) (.exec 0x105cb5 (fun s => s.RIP = 0x105cb5) (movR64R64Effect 0x105cb5 6 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 81) (.out 0x105cb8 (movR64M64Effect 0x105cb8 2 (.sib 4 none 0 (.d32 0x158))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 82) (.exec 0x105cb8 (LoadPre 0x105cb8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x158)) s (0x105cb8 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105cb8 2 (.sib 4 none 0 (.d32 0x158))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 83) (.out 0x105cc0 (callEffect (fun _ => 0x109f70) 0x105cc5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 84) (.exec 0x105cc0 (PushPre 0x105cc0 5) (callEffect (fun _ => 0x109f70) 0x105cc5) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 85) (.const ⟨64, 0x105cc5⟩) #v[]
    (.terminate (.call ⟨.l109f70, RegMap.args [(0, 71), (1, 73), (2, 81), (3, 3), (4, 83), (5, 5), (6, 79), (7, 77), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 86⟩ { target := .l105cc5, kept := #v[], arity := rfl, guard := some (Fin.last 85) }))))))))))))))))))))))))))))))))))

def bytes_l105c3e : List UInt8 :=
  [0x48, 0x8B, 0x84, 0x24, 0xC0, 0x01, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0xB8, 0x00, 0x00, 0x00,
    0x48, 0x8B, 0x84, 0x24, 0xB8, 0x01, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00,
    0x48, 0x8B, 0x84, 0x24, 0xA8, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x8C, 0x24, 0xB0, 0x01, 0x00, 0x00,
    0x48, 0x89, 0x8C, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00,
    0x48, 0x8B, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x84,
    0x24, 0x90, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x84, 0x24, 0x80, 0x00,
    0x00, 0x00, 0x48, 0x8B, 0x8C, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x89, 0x4C, 0x24, 0x10, 0x48,
    0x89, 0x44, 0x24, 0x08, 0x48, 0x89, 0xEF, 0x4C, 0x89, 0xE6, 0x48, 0x8B, 0x94, 0x24, 0x58, 0x01,
    0x00, 0x00, 0xE8, 0xAB, 0x42, 0x00, 0x00]

theorem code_l105c3e : ∀ x ∈ codeRange 0x105c3e bytes_l105c3e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5c3e 135 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105cc5 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x105cc5 (movR64R64Effect 0x105cc5 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[12]
    (.letOp (n := 54) (.exec 0x105cc5 (fun s => s.RIP = 0x105cc5) (movR64R64Effect 0x105cc5 7 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 55) (.out 0x105cc8 (movR64R64Effect 0x105cc8 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 13] []) (.reg (.gpr 6))) #v[13]
    (.letOp (n := 56) (.exec 0x105cc8 (fun s => s.RIP = 0x105cc8) (movR64R64Effect 0x105cc8 6 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 57) (.out 0x105ccb (movR64R64Effect 0x105ccb 13 5) (EffectPart.reads (.reg (.gpr 13)) [.gpr 5] []) (.reg (.gpr 13))) #v[5]
    (.letOp (n := 58) (.exec 0x105ccb (fun s => s.RIP = 0x105ccb) (movR64R64Effect 0x105ccb 13 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 59) (.out 0x105cce (movR64R64Effect 0x105cce 2 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5] []) (.reg (.gpr 2))) #v[5]
    (.letOp (n := 60) (.exec 0x105cce (fun s => s.RIP = 0x105cce) (movR64R64Effect 0x105cce 2 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 61) (.out 0x105cd1 (callEffect (fun _ => 0x10a2e0) 0x105cd6) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 62) (.exec 0x105cd1 (PushPre 0x105cd1 5) (callEffect (fun _ => 0x10a2e0) 0x105cd6) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.const ⟨64, 0x105cd6⟩) #v[]
    (.terminate (.call ⟨.l10a2e0, RegMap.args [(0, 0), (2, 59), (3, 3), (4, 61), (5, 5), (6, 55), (7, 53), (8, 8), (12, 12), (13, 57), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ { target := .l105cd6, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l105cc5 : List UInt8 :=
  [0x4C, 0x89, 0xE7, 0x4C, 0x89, 0xEE, 0x49, 0x89, 0xED, 0x48, 0x89, 0xEA, 0xE8, 0x0A, 0x46, 0x00,
    0x00]

theorem code_l105cc5 : ∀ x ∈ codeRange 0x105cc5 bytes_l105cc5, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5cc5 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105cd6 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x105cd6 (movR64R64Effect 0x105cd6 3 15) (EffectPart.reads (.reg (.gpr 3)) [.gpr 15] []) (.reg (.gpr 3))) #v[15]
    (.letOp (n := 54) (.exec 0x105cd6 (fun s => s.RIP = 0x105cd6) (movR64R64Effect 0x105cd6 3 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.out 0x105cd9 (movR64R64Effect 0x105cd9 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[15]
    (.letOp (n := 56) (.exec 0x105cd9 (fun s => s.RIP = 0x105cd9) (movR64R64Effect 0x105cd9 7 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 57) (.out 0x105cdc (movR64R64Effect 0x105cdc 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 58) (.exec 0x105cdc (fun s => s.RIP = 0x105cdc) (movR64R64Effect 0x105cdc 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 59) (.out 0x105cdf (movR64R64Effect 0x105cdf 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12] []) (.reg (.gpr 2))) #v[12]
    (.letOp (n := 60) (.exec 0x105cdf (fun s => s.RIP = 0x105cdf) (movR64R64Effect 0x105cdf 2 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 61) (.out 0x105ce2 (callEffect (fun _ => 0x109f60) 0x105ce7) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 62) (.exec 0x105ce2 (PushPre 0x105ce2 5) (callEffect (fun _ => 0x109f60) 0x105ce7) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.const ⟨64, 0x105ce7⟩) #v[]
    (.terminate (.call ⟨.l109f60, RegMap.args [(2, 59), (3, 53), (4, 61), (5, 5), (6, 57), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ { target := .l105ce7, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l105cd6 : List UInt8 :=
  [0x4C, 0x89, 0xFB, 0x4C, 0x89, 0xFF, 0x4C, 0x89, 0xF6, 0x4C, 0x89, 0xE2, 0xE8, 0x79, 0x42, 0x00,
    0x00]

theorem code_l105cd6 : ∀ x ∈ codeRange 0x105cd6 bytes_l105cd6, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5cd6 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105ce7 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x105ce7 (movR64M64Effect 0x105ce7 0 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x105ce7 (LoadPre 0x105ce7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x105ce7 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105ce7 0 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x105cef (StorePre 0x105cef 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x105cef + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105cef 0 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x105cf7 (movR64M64Effect 0x105cf7 0 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x105cf7 (LoadPre 0x105cf7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x105cf7 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105cf7 0 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x105cff (StorePre 0x105cff 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x105cff + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105cff 0 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x105d07 (movR64M64Effect 0x105d07 0 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x105d07 (LoadPre 0x105d07 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x105d07 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105d07 0 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x105d0f (movR64M64Effect 0x105d0f 1 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 62) (.exec 0x105d0f (LoadPre 0x105d0f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x105d0f + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105d0f 1 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x105d17 (StorePre 0x105d17 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x105d17 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105d17 1 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.exec 0x105d1f (StorePre 0x105d1f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x105d1f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105d1f 0 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 65) (.out 0x105d27 (movR64R64Effect 0x105d27 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[12]
    (.letOp (n := 66) (.exec 0x105d27 (fun s => s.RIP = 0x105d27) (movR64R64Effect 0x105d27 7 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 67) (.out 0x105d2a (movR64R64Effect 0x105d2a 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 68) (.exec 0x105d2a (fun s => s.RIP = 0x105d2a) (movR64R64Effect 0x105d2a 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 69) (.out 0x105d2d (movR64R64Effect 0x105d2d 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15] []) (.reg (.gpr 2))) #v[15]
    (.letOp (n := 70) (.exec 0x105d2d (fun s => s.RIP = 0x105d2d) (movR64R64Effect 0x105d2d 2 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 71) (.out 0x105d30 (callEffect (fun _ => 0x103450) 0x105d35) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 72) (.exec 0x105d30 (PushPre 0x105d30 5) (callEffect (fun _ => 0x103450) 0x105d35) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.const ⟨64, 0x105d35⟩) #v[]
    (.terminate (.call ⟨.l103450, RegMap.args [(0, 59), (1, 61), (2, 69), (3, 3), (4, 71), (5, 5), (6, 67), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 74⟩ { target := .l105d35, kept := #v[], arity := rfl, guard := some (Fin.last 73) }))))))))))))))))))))))

def bytes_l105ce7 : List UInt8 :=
  [0x48, 0x8B, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0xB8, 0x00, 0x00, 0x00,
    0x48, 0x8B, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00,
    0x48, 0x8B, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x8C, 0x24, 0x88, 0x00, 0x00, 0x00,
    0x48, 0x89, 0x8C, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00,
    0x4C, 0x89, 0xE7, 0x4C, 0x89, 0xF6, 0x4C, 0x89, 0xFA, 0xE8, 0x1B, 0xD7, 0xFF, 0xFF]

theorem code_l105ce7 : ∀ x ∈ codeRange 0x105ce7 bytes_l105ce7, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5ce7 78 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105d35 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x105d35 (movR64M64Effect 0x105d35 7 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x105d35 (LoadPre 0x105d35 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x105d35 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x105d35 7 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x105d3a (movR64M64Effect 0x105d3a 0 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 56) (.exec 0x105d3a (LoadPre 0x105d3a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x105d3a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x105d3a 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x105d3f (cmpM8Imm8Effect 0x105d3f 5 (.sib 4 none 0 (.d8 0x8)) 0x0) (EffectPart.reads (.flag .ZF) [.gpr 4] []) (.flag .ZF)) #v[4]
    (.letOp (n := 58) (.exec 0x105d3f (LoadPre 0x105d3f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x105d3f + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x105d3f 5 (.sib 4 none 0 (.d8 0x8)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.pure (condOp 4)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l105d62, RegMap.args [(0, 55), (3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l105d46, RegMap.args [(0, 55), (3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l105d35 : List UInt8 :=
  [0x48, 0x8B, 0x7C, 0x24, 0x10, 0x48, 0x8B, 0x44, 0x24, 0x18, 0x80, 0x7C, 0x24, 0x08, 0x00, 0x74,
    0x1C]

theorem code_l105d35 : ∀ x ∈ codeRange 0x105d35 bytes_l105d35, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5d35 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105d46 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x105d46 (testR64R64Effect 0x105d46 7 7) (EffectPart.reads (.flag .ZF) [.gpr 7, .gpr 7] []) (.flag .ZF)) #v[7, 7]
    (.letOp (n := 54) (.exec 0x105d46 (fun s => s.RIP = 0x105d46) (testR64R64Effect 0x105d46 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[7, 7]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l105870, RegMap.args [(0, 0), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l105d4f, RegMap.args [(0, 0), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l105d46 : List UInt8 :=
  [0x48, 0x85, 0xFF, 0x0F, 0x84, 0x21, 0xFB, 0xFF, 0xFF]

theorem code_l105d46 : ∀ x ∈ codeRange 0x105d46 bytes_l105d46, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5d46 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105d4f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x105d4f (movR64M64Effect 0x105d4f 0 (.base 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 54) (.exec 0x105d4f (LoadPre 0x105d4f (fun s => AddrMode.addr (.base 0 .none) s (0x105d4f + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x105d4f 0 (.base 0 .none)) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x105d52 (testR64R64Effect 0x105d52 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[53, 53]
    (.letOp (n := 56) (.exec 0x105d52 (fun s => s.RIP = 0x105d52) (testR64R64Effect 0x105d52 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[53, 53]
    (.letOp (n := 57) (.pure (condOp 4)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l105870, RegMap.args [(0, 53), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l105d5b, RegMap.args [(0, 53), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l105d4f : List UInt8 :=
  [0x48, 0x8B, 0x00, 0x48, 0x85, 0xC0, 0x0F, 0x84, 0x15, 0xFB, 0xFF, 0xFF]

theorem code_l105d4f : ∀ x ∈ codeRange 0x105d4f bytes_l105d4f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5d4f 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105d5b : Block Op Label signature Reg.count 53 :=
  cutBlock 0x105d5b

def bytes_l105d5b : List UInt8 :=
  [0xFF, 0xD0]

theorem code_l105d5b : ∀ x ∈ codeRange 0x105d5b bytes_l105d5b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5d5b 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105d5d : Block Op Label signature Reg.count 53 :=
  .terminate (.br ⟨.l105870, RegMap.args (entryMap (live .l105d5d)) 53⟩)

def bytes_l105d5d : List UInt8 :=
  [0xE9, 0x0E, 0xFB, 0xFF, 0xFF]

theorem code_l105d5d : ∀ x ∈ codeRange 0x105d5d bytes_l105d5d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5d5d 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105d62 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x105d62 (movR64M64Effect 0x105d62 1 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x105d62 (LoadPre 0x105d62 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x105d62 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x105d62 1 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x105d67 (StorePre 0x105d67 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x105d67 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105d67 1 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x105d6f (movR64M64Effect 0x105d6f 1 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 57) (.exec 0x105d6f (LoadPre 0x105d6f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x105d6f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x105d6f 1 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x105d74 (StorePre 0x105d74 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x105d74 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105d74 1 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x105d7c (movR64M64Effect 0x105d7c 1 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 60) (.exec 0x105d7c (LoadPre 0x105d7c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x105d7c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x105d7c 1 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x105d81 (StorePre 0x105d81 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x105d81 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105d81 1 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x105d89 (movR64M64Effect 0x105d89 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 63) (.exec 0x105d89 (LoadPre 0x105d89 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x105d89 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x105d89 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x105d8e (StorePre 0x105d8e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x105d8e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105d8e 1 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x105d96 (movR64M64Effect 0x105d96 1 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 66) (.exec 0x105d96 (LoadPre 0x105d96 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x105d96 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x105d96 1 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x105d9b (movR64M64Effect 0x105d9b 2 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 68) (.exec 0x105d9b (LoadPre 0x105d9b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x105d9b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x105d9b 2 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.exec 0x105da0 (StorePre 0x105da0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x105da0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105da0 2 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[67, 4]
    (.letOp (n := 70) (.exec 0x105da8 (StorePre 0x105da8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x105da8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105da8 1 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 71) (.exec 0x105db0 (StorePre 0x105db0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x105db0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105db0 7 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[7, 4]
    (.letOp (n := 72) (.exec 0x105db8 (StorePre 0x105db8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x105db8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105db8 0 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[0, 4]
    (.letOp (n := 73) (.out 0x105dc0 (leaR64Effect 0x105dc0 7 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 74) (.exec 0x105dc0 (fun s => s.RIP = 0x105dc0) (leaR64Effect 0x105dc0 7 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.out 0x105dc8 (leaR64Effect 0x105dc8 6 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 76) (.exec 0x105dc8 (fun s => s.RIP = 0x105dc8) (leaR64Effect 0x105dc8 6 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 77) (.out 0x105dd0 (callEffect (fun _ => 0x109e30) 0x105dd5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 78) (.exec 0x105dd0 (PushPre 0x105dd0 5) (callEffect (fun _ => 0x109e30) 0x105dd5) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.const ⟨64, 0x105dd5⟩) #v[]
    (.terminate (.call ⟨.l109e30, RegMap.args [(0, 0), (1, 65), (2, 67), (3, 3), (4, 77), (5, 5), (6, 75), (7, 73), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 80⟩ { target := .l105dd5, kept := #v[], arity := rfl, guard := some (Fin.last 79) }))))))))))))))))))))))))))))

def bytes_l105d62 : List UInt8 :=
  [0x48, 0x8B, 0x4C, 0x24, 0x48, 0x48, 0x89, 0x8C, 0x24, 0xF8, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x4C,
    0x24, 0x40, 0x48, 0x89, 0x8C, 0x24, 0xF0, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x4C, 0x24, 0x38, 0x48,
    0x89, 0x8C, 0x24, 0xE8, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x8C, 0x24,
    0xE0, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x4C, 0x24, 0x20, 0x48, 0x8B, 0x54, 0x24, 0x28, 0x48, 0x89,
    0x94, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x8C, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x48, 0x89,
    0xBC, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x48, 0x8D,
    0xBC, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x48, 0x8D, 0xB4, 0x24, 0x80, 0x00, 0x00, 0x00, 0xE8, 0x5B,
    0x40, 0x00, 0x00]

theorem code_l105d62 : ∀ x ∈ codeRange 0x105d62 bytes_l105d62, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5d62 115 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105dd5 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x105dd5 (leaR64Effect 0x105dd5 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x105dd5 (fun s => s.RIP = 0x105dd5) (leaR64Effect 0x105dd5 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x105dda (leaR64Effect 0x105dda 3 (.sib 4 none 0 (.d32 0x100))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 56) (.exec 0x105dda (fun s => s.RIP = 0x105dda) (leaR64Effect 0x105dda 3 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x105de2 (movR64R64Effect 0x105de2 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[55]
    (.letOp (n := 58) (.exec 0x105de2 (fun s => s.RIP = 0x105de2) (movR64R64Effect 0x105de2 6 3) (Reg.operands [.gpr 3] [])) #v[55]
    (.letOp (n := 59) (.out 0x105de5 (callEffect (fun _ => 0x120350) 0x105dea) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x105de5 (PushPre 0x105de5 5) (callEffect (fun _ => 0x120350) 0x105dea) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x105dea⟩) #v[]
    (.terminate (.call ⟨.l120350, RegMap.args [(3, 55), (4, 59), (5, 5), (6, 57), (7, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l105dea, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l105dd5 : List UInt8 :=
  [0x48, 0x8D, 0x7C, 0x24, 0x08, 0x48, 0x8D, 0x9C, 0x24, 0x00, 0x01, 0x00, 0x00, 0x48, 0x89, 0xDE,
    0xE8, 0x66, 0xA5, 0x01, 0x00]

theorem code_l105dd5 : ∀ x ∈ codeRange 0x105dd5 bytes_l105dd5, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5dd5 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105dea : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x105dea (movR64R64Effect 0x105dea 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 54) (.exec 0x105dea (fun s => s.RIP = 0x105dea) (movR64R64Effect 0x105dea 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x105ded (callEffect (fun _ => 0x1203b0) 0x105df2) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 56) (.exec 0x105ded (PushPre 0x105ded 5) (callEffect (fun _ => 0x1203b0) 0x105df2) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.const ⟨64, 0x105df2⟩) #v[]
    (.terminate (.call ⟨.l1203b0, RegMap.args [(3, 3), (4, 55), (5, 5), (7, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ { target := .l105df2, kept := #v[], arity := rfl, guard := some (Fin.last 57) }))))))

def bytes_l105dea : List UInt8 :=
  [0x48, 0x89, 0xDF, 0xE8, 0xBE, 0xA5, 0x01, 0x00]

theorem code_l105dea : ∀ x ∈ codeRange 0x105dea bytes_l105dea, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5dea 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105df2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x105df2 (leaR64Effect 0x105df2 7 (.sib 4 none 0 (.d32 0x1c8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x105df2 (fun s => s.RIP = 0x105df2) (leaR64Effect 0x105df2 7 (.sib 4 none 0 (.d32 0x1c8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x105dfa (callEffect (fun _ => 0x10a170) 0x105dff) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 56) (.exec 0x105dfa (PushPre 0x105dfa 5) (callEffect (fun _ => 0x10a170) 0x105dff) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.const ⟨64, 0x105dff⟩) #v[]
    (.terminate (.call ⟨.l10a170, RegMap.args [(0, 0), (3, 3), (4, 55), (5, 5), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ { target := .l105dff, kept := #v[], arity := rfl, guard := some (Fin.last 57) }))))))

def bytes_l105df2 : List UInt8 :=
  [0x48, 0x8D, 0xBC, 0x24, 0xC8, 0x01, 0x00, 0x00, 0xE8, 0x71, 0x43, 0x00, 0x00]

theorem code_l105df2 : ∀ x ∈ codeRange 0x105df2 bytes_l105df2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5df2 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105dff : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x105dff (leaR64Effect 0x105dff 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x105dff (fun s => s.RIP = 0x105dff) (leaR64Effect 0x105dff 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x105e04 (leaR64Effect 0x105e04 6 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 56) (.exec 0x105e04 (fun s => s.RIP = 0x105e04) (leaR64Effect 0x105e04 6 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x105e0c (callEffect (fun _ => 0x104c90) 0x105e11) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x105e0c (PushPre 0x105e0c 5) (callEffect (fun _ => 0x104c90) 0x105e11) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x105e11⟩) #v[]
    (.terminate (.call ⟨.l104c90, RegMap.args [(3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ { target := .l105e11, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l105dff : List UInt8 :=
  [0x48, 0x8D, 0x7C, 0x24, 0x08, 0x48, 0x8D, 0xB4, 0x24, 0xC0, 0x00, 0x00, 0x00, 0xE8, 0x7F, 0xEE,
    0xFF, 0xFF]

theorem code_l105dff : ∀ x ∈ codeRange 0x105dff bytes_l105dff, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5dff 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105e11_1 : Block Op Label signature Reg.count 82 :=
  .letOp (n := 82) (.exec 0x105e8d (StorePre 0x105e8d 4 (fun s => AddrMode.addr (.base 0 (.d8 0x28)) s (0x105e8d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x105e8d 6 (.base 0 (.d8 0x28))) (Reg.operands [.gpr 6, .gpr 0] [])) #v[62, 77]
    (.letOp (n := 83) (.exec 0x105e91 (StorePre 0x105e91 4 (fun s => AddrMode.addr (.base 0 (.d8 0x20)) s (0x105e91 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x105e91 7 (.base 0 (.d8 0x20))) (Reg.operands [.gpr 7, .gpr 0] [])) #v[65, 77]
    (.letOp (n := 84) (.exec 0x105e95 (StorePre 0x105e95 4 (fun s => AddrMode.addr (.base 0 (.d8 0x18)) s (0x105e95 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x105e95 8 (.base 0 (.d8 0x18))) (Reg.operands [.gpr 8, .gpr 0] [])) #v[68, 77]
    (.letOp (n := 85) (.exec 0x105e99 (StorePre 0x105e99 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x105e99 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x105e99 9 (.base 0 (.d8 0x8))) (Reg.operands [.gpr 9, .gpr 0] [])) #v[71, 77]
    (.letOp (n := 86) (.exec 0x105e9d (StorePre 0x105e9d 4 (fun s => AddrMode.addr (.base 0 (.d8 0x10)) s (0x105e9d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x105e9d 10 (.base 0 (.d8 0x10))) (Reg.operands [.gpr 10, .gpr 0] [])) #v[73, 77]
    (.letOp (n := 87) (.exec 0x105ea1 (StorePre 0x105ea1 7 (fun s => AddrMode.addr (.base 0 .none) s (0x105ea1 + BitVec.ofNat 64 7)) 8) (movM64Imm32Effect 0x105ea1 (.base 0 .none) 0x0) (Reg.operands [.gpr 0] [])) #v[77]
    (.letOp (n := 88) (.out 0x105ea8 (addR64Imm32Effect 0x105ea8 4 0x2f8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 89) (.exec 0x105ea8 (fun s => s.RIP = 0x105ea8) (addR64Imm32Effect 0x105ea8 4 0x2f8) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 90) (.out 0x105eaf (popR64Effect 0x105eaf 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[88]
    (.letOp (n := 91) (.out 0x105eaf (popR64Effect 0x105eaf 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[88]
    (.letOp (n := 92) (.exec 0x105eaf (PopPre 0x105eaf) (popR64Effect 0x105eaf 1 3) (Reg.operands [.gpr 4] [])) #v[88]
    (.letOp (n := 93) (.out 0x105eb0 (popR64Effect 0x105eb0 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[91]
    (.letOp (n := 94) (.out 0x105eb0 (popR64Effect 0x105eb0 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[91]
    (.letOp (n := 95) (.exec 0x105eb0 (PopPre 0x105eb0) (popR64Effect 0x105eb0 2 12) (Reg.operands [.gpr 4] [])) #v[91]
    (.letOp (n := 96) (.out 0x105eb2 (popR64Effect 0x105eb2 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[94]
    (.letOp (n := 97) (.out 0x105eb2 (popR64Effect 0x105eb2 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[94]
    (.letOp (n := 98) (.exec 0x105eb2 (PopPre 0x105eb2) (popR64Effect 0x105eb2 2 13) (Reg.operands [.gpr 4] [])) #v[94]
    (.letOp (n := 99) (.out 0x105eb4 (popR64Effect 0x105eb4 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[97]
    (.letOp (n := 100) (.out 0x105eb4 (popR64Effect 0x105eb4 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[97]
    (.letOp (n := 101) (.exec 0x105eb4 (PopPre 0x105eb4) (popR64Effect 0x105eb4 2 14) (Reg.operands [.gpr 4] [])) #v[97]
    (.letOp (n := 102) (.out 0x105eb6 (popR64Effect 0x105eb6 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[100]
    (.letOp (n := 103) (.out 0x105eb6 (popR64Effect 0x105eb6 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[100]
    (.letOp (n := 104) (.exec 0x105eb6 (PopPre 0x105eb6) (popR64Effect 0x105eb6 2 15) (Reg.operands [.gpr 4] [])) #v[100]
    (.letOp (n := 105) (.out 0x105eb8 (popR64Effect 0x105eb8 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[103]
    (.letOp (n := 106) (.out 0x105eb8 (popR64Effect 0x105eb8 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[103]
    (.letOp (n := 107) (.exec 0x105eb8 (PopPre 0x105eb8) (popR64Effect 0x105eb8 1 5) (Reg.operands [.gpr 4] [])) #v[103]
    (.letOp (n := 108) (.out 0x105eb9 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[106]
    (.letOp (n := 109) (.out 0x105eb9 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[106]
    (.letOp (n := 110) (.exec 0x105eb9 (RetPre 0x105eb9) (retEffect) (Reg.operands [.gpr 4] [])) #v[106]
    (.terminate (.ret (RegMap.args [(0, 77), (1, 56), (2, 59), (3, 90), (4, 109), (5, 105), (6, 62), (7, 65), (8, 68), (9, 71), (10, 73), (11, 53), (12, 93), (13, 96), (14, 99), (15, 102), (22, 22), (39, 39), (50, 50), (51, 51)] 111) (some ⟨108, by decide⟩)))))))))))))))))))))))))))))))

def bytes_l105e11_1 : List UInt8 :=
  [0x48, 0x89, 0x70, 0x28, 0x48, 0x89, 0x78, 0x20, 0x4C, 0x89, 0x40, 0x18, 0x4C, 0x89, 0x48, 0x08,
    0x4C, 0x89, 0x50, 0x10, 0x48, 0xC7, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0x81, 0xC4, 0xF8, 0x02,
    0x00, 0x00, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l105e11_1 : ∀ x ∈ codeRange 0x105e8d bytes_l105e11_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5e8d 45 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105e11 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x105e11 (movR64M64Effect 0x105e11 11 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 54) (.exec 0x105e11 (LoadPre 0x105e11 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x105e11 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x105e11 11 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x105e16 (StorePre 0x105e16 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x105e16 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105e16 11 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x105e1e (movR64M64Effect 0x105e1e 1 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 57) (.exec 0x105e1e (LoadPre 0x105e1e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x105e1e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x105e1e 1 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x105e23 (StorePre 0x105e23 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x105e23 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105e23 1 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x105e2b (movR64M64Effect 0x105e2b 2 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 60) (.exec 0x105e2b (LoadPre 0x105e2b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x105e2b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x105e2b 2 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x105e30 (StorePre 0x105e30 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x105e30 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105e30 2 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x105e38 (movR64M64Effect 0x105e38 6 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 63) (.exec 0x105e38 (LoadPre 0x105e38 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x105e38 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x105e38 6 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x105e3d (StorePre 0x105e3d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x105e3d + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105e3d 6 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x105e45 (movR64M64Effect 0x105e45 7 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 66) (.exec 0x105e45 (LoadPre 0x105e45 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x105e45 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x105e45 7 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x105e4a (StorePre 0x105e4a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x105e4a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105e4a 7 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x105e52 (movR64M64Effect 0x105e52 8 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 69) (.exec 0x105e52 (LoadPre 0x105e52 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x105e52 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x105e52 8 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.exec 0x105e57 (StorePre 0x105e57 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x105e57 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105e57 8 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[68, 4]
    (.letOp (n := 71) (.out 0x105e5f (movR64M64Effect 0x105e5f 9 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 72) (.exec 0x105e5f (LoadPre 0x105e5f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x105e5f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x105e5f 9 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.out 0x105e64 (movR64M64Effect 0x105e64 10 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 74) (.exec 0x105e64 (LoadPre 0x105e64 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x105e64 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x105e64 10 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.exec 0x105e69 (StorePre 0x105e69 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x105e69 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105e69 10 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[73, 4]
    (.letOp (n := 76) (.exec 0x105e71 (StorePre 0x105e71 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x105e71 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105e71 9 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[71, 4]
    (.letOp (n := 77) (.out 0x105e79 (movR64M64Effect 0x105e79 0 (.sib 4 none 0 (.d32 0x1a0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 78) (.exec 0x105e79 (LoadPre 0x105e79 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1a0)) s (0x105e79 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105e79 0 (.sib 4 none 0 (.d32 0x1a0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.exec 0x105e81 (StorePre 0x105e81 4 (fun s => AddrMode.addr (.base 0 (.d8 0x40)) s (0x105e81 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x105e81 11 (.base 0 (.d8 0x40))) (Reg.operands [.gpr 11, .gpr 0] [])) #v[53, 77]
    (.letOp (n := 80) (.exec 0x105e85 (StorePre 0x105e85 4 (fun s => AddrMode.addr (.base 0 (.d8 0x38)) s (0x105e85 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x105e85 1 (.base 0 (.d8 0x38))) (Reg.operands [.gpr 1, .gpr 0] [])) #v[56, 77]
    (.letOp (n := 81) (.exec 0x105e89 (StorePre 0x105e89 4 (fun s => AddrMode.addr (.base 0 (.d8 0x30)) s (0x105e89 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x105e89 2 (.base 0 (.d8 0x30))) (Reg.operands [.gpr 2, .gpr 0] [])) #v[59, 77]
    (b_l105e11_1)))))))))))))))))))))))))))))

def bytes_l105e11 : List UInt8 :=
  [0x4C, 0x8B, 0x5C, 0x24, 0x40, 0x4C, 0x89, 0x9C, 0x24, 0xF8, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x4C,
    0x24, 0x38, 0x48, 0x89, 0x8C, 0x24, 0xF0, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x54, 0x24, 0x30, 0x48,
    0x89, 0x94, 0x24, 0xE8, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x74, 0x24, 0x28, 0x48, 0x89, 0xB4, 0x24,
    0xE0, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x7C, 0x24, 0x20, 0x48, 0x89, 0xBC, 0x24, 0xD8, 0x00, 0x00,
    0x00, 0x4C, 0x8B, 0x44, 0x24, 0x18, 0x4C, 0x89, 0x84, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x4C, 0x8B,
    0x4C, 0x24, 0x08, 0x4C, 0x8B, 0x54, 0x24, 0x10, 0x4C, 0x89, 0x94, 0x24, 0xC8, 0x00, 0x00, 0x00,
    0x4C, 0x89, 0x8C, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x84, 0x24, 0xA0, 0x01, 0x00, 0x00,
    0x4C, 0x89, 0x58, 0x40, 0x48, 0x89, 0x48, 0x38, 0x48, 0x89, 0x50, 0x30] ++ bytes_l105e11_1

theorem code_l105e11 : ∀ x ∈ codeRange 0x105e11 bytes_l105e11, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x5e11 124 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l105e11_1

@[cfg_block] def b_l105eba : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x105eba (StorePre 0x105eba 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x105eba + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x105eba (.sib 4 none 0 (.d8 0x8)) 0x202498) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.exec 0x105ec3 (StorePre 0x105ec3 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x105ec3 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x105ec3 (.sib 4 none 0 (.d8 0x10)) 0x12a190) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x105ecc (StorePre 0x105ecc 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x105ecc + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x105ecc 5 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[5, 4]
    (.terminate (.br ⟨.l105f09, RegMap.args [(4, 4), (5, 5)] 56⟩))))

def bytes_l105eba : List UInt8 :=
  [0x48, 0xC7, 0x44, 0x24, 0x08, 0x98, 0x24, 0x20, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x10, 0x90, 0xA1,
    0x12, 0x00, 0x48, 0x89, 0x6C, 0x24, 0x18, 0xEB, 0x36]

theorem code_l105eba : ∀ x ∈ codeRange 0x105eba bytes_l105eba, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5eba 25 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105ed3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x105ed3 (leaR64Effect 0x105ed3 6 (.sib 4 none 0 (.d32 0x100))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 54) (.exec 0x105ed3 (fun s => s.RIP = 0x105ed3) (leaR64Effect 0x105ed3 6 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x105edb (xorR32R32Effect 0x105edb 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[7, 7]
    (.letOp (n := 56) (.exec 0x105edb (fun s => s.RIP = 0x105edb) (xorR32R32Effect 0x105edb 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[7, 7]
    (.letOp (n := 57) (.out 0x105edd (movR64Imm32Effect 0x105edd 2 0x2022e8) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x105edd (fun s => s.RIP = 0x105edd) (movR64Imm32Effect 0x105edd 2 0x2022e8) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x105ee4 (xorR32R32Effect 0x105ee4 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[1, 1]
    (.letOp (n := 60) (.exec 0x105ee4 (fun s => s.RIP = 0x105ee4) (xorR32R32Effect 0x105ee4 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[1, 1]
    (.letOp (n := 61) (.out 0x105ee6 (movR64Imm32Effect 0x105ee6 9 0x2022f0) (EffectPart.reads (.reg (.gpr 9)) [] []) (.reg (.gpr 9))) #v[]
    (.letOp (n := 62) (.exec 0x105ee6 (fun s => s.RIP = 0x105ee6) (movR64Imm32Effect 0x105ee6 9 0x2022f0) (Reg.operands [] [])) #v[]
    (.letOp (n := 63) (.out 0x105eed (callEffect (fun _ => 0x115408) 0x105ef2) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 64) (.exec 0x105eed (PushPre 0x105eed 5) (callEffect (fun _ => 0x115408) 0x105ef2) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.const ⟨64, 0x105ef2⟩) #v[]
    (.terminate (.call ⟨.l115408, RegMap.args [(1, 59), (2, 57), (4, 63), (5, 5), (6, 53), (7, 55), (8, 8), (9, 61)] 66⟩ { target := .l105ef2, kept := #v[], arity := rfl, guard := some (Fin.last 65) }))))))))))))))

def bytes_l105ed3 : List UInt8 :=
  [0x48, 0x8D, 0xB4, 0x24, 0x00, 0x01, 0x00, 0x00, 0x31, 0xFF, 0x48, 0xC7, 0xC2, 0xE8, 0x22, 0x20,
    0x00, 0x31, 0xC9, 0x49, 0xC7, 0xC1, 0xF0, 0x22, 0x20, 0x00, 0xE8, 0x16, 0xF5, 0x00, 0x00]

theorem code_l105ed3 : ∀ x ∈ codeRange 0x105ed3 bytes_l105ed3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5ed3 31 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105ef2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x105ef2 (StorePre 0x105ef2 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x105ef2 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x105ef2 (.sib 4 none 0 (.d8 0x8)) 0x202498) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.exec 0x105efb (StorePre 0x105efb 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x105efb + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x105efb (.sib 4 none 0 (.d8 0x10)) 0x12a190) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x105f04 (StorePre 0x105f04 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x105f04 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x105f04 15 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[15, 4]
    (.terminate (.br ⟨.l105f09, RegMap.args [(4, 4), (5, 5), (15, 15)] 56⟩))))

def bytes_l105ef2 : List UInt8 :=
  [0x48, 0xC7, 0x44, 0x24, 0x08, 0x98, 0x24, 0x20, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x10, 0x90, 0xA1,
    0x12, 0x00, 0x4C, 0x89, 0x7C, 0x24, 0x18]

theorem code_l105ef2 : ∀ x ∈ codeRange 0x105ef2 bytes_l105ef2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5ef2 23 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105f09 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x105f09 (StorePre 0x105f09 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x105f09 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x105f09 (.sib 4 none 0 (.d8 0x20)) 0x12a190) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.out 0x105f12 (leaR64Effect 0x105f12 6 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 55) (.exec 0x105f12 (fun s => s.RIP = 0x105f12) (leaR64Effect 0x105f12 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x105f17 (movR64Imm32Effect 0x105f17 7 0x20028f) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 57) (.exec 0x105f17 (fun s => s.RIP = 0x105f17) (movR64Imm32Effect 0x105f17 7 0x20028f) (Reg.operands [] [])) #v[]
    (.letOp (n := 58) (.out 0x105f1e (movR64Imm32Effect 0x105f1e 2 0x202518) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 59) (.exec 0x105f1e (fun s => s.RIP = 0x105f1e) (movR64Imm32Effect 0x105f1e 2 0x202518) (Reg.operands [] [])) #v[]
    (.letOp (n := 60) (.out 0x105f25 (callEffect (fun _ => 0x129770) 0x105f2a) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 61) (.exec 0x105f25 (PushPre 0x105f25 5) (callEffect (fun _ => 0x129770) 0x105f2a) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.const ⟨64, 0x105f2a⟩) #v[]
    (.terminate (.call ⟨.l129770, RegMap.args [(2, 58), (4, 60), (5, 5), (6, 54), (7, 56)] 63⟩ { target := .l105f2a, kept := #v[], arity := rfl, guard := some (Fin.last 62) })))))))))))

def bytes_l105f09 : List UInt8 :=
  [0x48, 0xC7, 0x44, 0x24, 0x20, 0x90, 0xA1, 0x12, 0x00, 0x48, 0x8D, 0x74, 0x24, 0x08, 0x48, 0xC7,
    0xC7, 0x8F, 0x02, 0x20, 0x00, 0x48, 0xC7, 0xC2, 0x18, 0x25, 0x20, 0x00, 0xE8, 0x46, 0x38, 0x02,
    0x00]

theorem code_l105f09 : ∀ x ∈ codeRange 0x105f09 bytes_l105f09, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5f09 33 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105f2a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x105f2a (fun s => s.RIP = 0x105f2a) (fun _ => nopEffect 0x105f2a 6) (Reg.operands [] [])) #v[]
    (.letOp (n := 54) (.out 0x105f30 (pushR64Effect 0x105f30 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 55) (.exec 0x105f30 (PushPre 0x105f30 1) (pushR64Effect 0x105f30 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 56) (.out 0x105f31 (pushR64Effect 0x105f31 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[54, 15]
    (.letOp (n := 57) (.exec 0x105f31 (PushPre 0x105f31 2) (pushR64Effect 0x105f31 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[54, 15]
    (.letOp (n := 58) (.out 0x105f33 (pushR64Effect 0x105f33 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[56, 14]
    (.letOp (n := 59) (.exec 0x105f33 (PushPre 0x105f33 2) (pushR64Effect 0x105f33 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[56, 14]
    (.letOp (n := 60) (.out 0x105f35 (pushR64Effect 0x105f35 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[58, 13]
    (.letOp (n := 61) (.exec 0x105f35 (PushPre 0x105f35 2) (pushR64Effect 0x105f35 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[58, 13]
    (.letOp (n := 62) (.out 0x105f37 (pushR64Effect 0x105f37 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[60, 12]
    (.letOp (n := 63) (.exec 0x105f37 (PushPre 0x105f37 2) (pushR64Effect 0x105f37 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[60, 12]
    (.letOp (n := 64) (.out 0x105f39 (pushR64Effect 0x105f39 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[62, 3]
    (.letOp (n := 65) (.exec 0x105f39 (PushPre 0x105f39 1) (pushR64Effect 0x105f39 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[62, 3]
    (.letOp (n := 66) (.out 0x105f3a (subR64Imm32Effect 0x105f3a 4 0x158) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[64]
    (.letOp (n := 67) (.exec 0x105f3a (fun s => s.RIP = 0x105f3a) (subR64Imm32Effect 0x105f3a 4 0x158) (Reg.operands [.gpr 4] [])) #v[64]
    (.letOp (n := 68) (.out 0x105f41 (movR64R64Effect 0x105f41 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 6] []) (.reg (.gpr 14))) #v[6]
    (.letOp (n := 69) (.exec 0x105f41 (fun s => s.RIP = 0x105f41) (movR64R64Effect 0x105f41 14 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 70) (.exec 0x105f44 (StorePre 0x105f44 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x105f44 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x105f44 7 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[7, 66]
    (.letOp (n := 71) (.out 0x105f49 (movR64M64Effect 0x105f49 5 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 5)) [.gpr 6] []) (.reg (.gpr 5))) #v[6]
    (.letOp (n := 72) (.exec 0x105f49 (LoadPre 0x105f49 (fun s => AddrMode.addr (.base 6 .none) s (0x105f49 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x105f49 5 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 73) (.out 0x105f4c (movR64M64Effect 0x105f4c 13 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 6] []) (.reg (.gpr 13))) #v[6]
    (.letOp (n := 74) (.exec 0x105f4c (LoadPre 0x105f4c (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x105f4c + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x105f4c 13 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 75) (.out 0x105f50 (leaR64Effect 0x105f50 15 (.sib 4 none 0 (.d32 0xe0))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[66]
    (.letOp (n := 76) (.exec 0x105f50 (fun s => s.RIP = 0x105f50) (leaR64Effect 0x105f50 15 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 4] [])) #v[66]
    (.letOp (n := 77) (.out 0x105f58 (leaR64Effect 0x105f58 12 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[66]
    (.letOp (n := 78) (.exec 0x105f58 (fun s => s.RIP = 0x105f58) (leaR64Effect 0x105f58 12 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[66]
    (.terminate (.br ⟨.l106009, RegMap.args [(2, 2), (3, 3), (4, 66), (5, 71), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 73), (14, 68), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)] 79⟩)))))))))))))))))))))))))))

def bytes_l105f2a : List UInt8 :=
  [0x66, 0x0F, 0x1F, 0x44, 0x00, 0x00, 0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53,
    0x48, 0x81, 0xEC, 0x58, 0x01, 0x00, 0x00, 0x49, 0x89, 0xF6, 0x48, 0x89, 0x7C, 0x24, 0x20, 0x48,
    0x8B, 0x2E, 0x4C, 0x8B, 0x6E, 0x08, 0x4C, 0x8D, 0xBC, 0x24, 0xE0, 0x00, 0x00, 0x00, 0x4C, 0x8D,
    0x64, 0x24, 0x68, 0xE9, 0xA7, 0x00, 0x00, 0x00]

theorem code_l105f2a : ∀ x ∈ codeRange 0x105f2a bytes_l105f2a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5f2a 56 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105f70 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x105f70 (movR64M64Effect 0x105f70 0 (.sib 4 none 0 (.d32 0xf8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x105f70 (LoadPre 0x105f70 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x105f70 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105f70 0 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x105f78 (StorePre 0x105f78 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x105f78 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x105f78 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x105f7d (movR64M64Effect 0x105f7d 1 (.sib 4 none 0 (.d32 0xf0))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 57) (.exec 0x105f7d (LoadPre 0x105f7d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x105f7d + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105f7d 1 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x105f85 (StorePre 0x105f85 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x105f85 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x105f85 1 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x105f8a (movR64M64Effect 0x105f8a 2 (.sib 4 none 0 (.d32 0xe0))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 60) (.exec 0x105f8a (LoadPre 0x105f8a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x105f8a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105f8a 2 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x105f92 (movR64M64Effect 0x105f92 6 (.sib 4 none 0 (.d32 0xe8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 62) (.exec 0x105f92 (LoadPre 0x105f92 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x105f92 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x105f92 6 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x105f9a (StorePre 0x105f9a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x105f9a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x105f9a 6 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.exec 0x105f9f (StorePre 0x105f9f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x105f9f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x105f9f 2 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 65) (.exec 0x105fa4 (StorePre 0x105fa4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x105fa4 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x105fa4 2 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 66) (.exec 0x105fa9 (StorePre 0x105fa9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x105fa9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x105fa9 6 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 67) (.exec 0x105fae (StorePre 0x105fae 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x105fae + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x105fae 1 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 68) (.exec 0x105fb3 (StorePre 0x105fb3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x105fb3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x105fb3 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 69) (.exec 0x105fb8 (StorePre 0x105fb8 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x105fb8 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x105fb8 (.sib 4 none 0 (.d32 0xf8)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.exec 0x105fc4 (StorePre 0x105fc4 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x105fc4 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x105fc4 (.sib 4 none 0 (.d32 0xf0)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.exec 0x105fd0 (StorePre 0x105fd0 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x105fd0 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x105fd0 (.sib 4 none 0 (.d32 0xe8)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.exec 0x105fdc (StorePre 0x105fdc 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x105fdc + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x105fdc (.sib 4 none 0 (.d32 0xe0)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.out 0x105fe8 (leaR64Effect 0x105fe8 7 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 74) (.exec 0x105fe8 (fun s => s.RIP = 0x105fe8) (leaR64Effect 0x105fe8 7 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.out 0x105fed (movR64R64Effect 0x105fed 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 76) (.exec 0x105fed (fun s => s.RIP = 0x105fed) (movR64R64Effect 0x105fed 6 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 77) (.out 0x105ff0 (callEffect (fun _ => 0x10a280) 0x105ff5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 78) (.exec 0x105ff0 (PushPre 0x105ff0 5) (callEffect (fun _ => 0x10a280) 0x105ff5) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.const ⟨64, 0x105ff5⟩) #v[]
    (.terminate (.call ⟨.l10a280, RegMap.args [(0, 53), (1, 56), (2, 59), (3, 3), (4, 77), (5, 5), (6, 75), (7, 73), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 80⟩ { target := .l105ff5, kept := #v[], arity := rfl, guard := some (Fin.last 79) }))))))))))))))))))))))))))))

def bytes_l105f70 : List UInt8 :=
  [0x48, 0x8B, 0x84, 0x24, 0xF8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x40, 0x48, 0x8B, 0x8C,
    0x24, 0xF0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x4C, 0x24, 0x38, 0x48, 0x8B, 0x94, 0x24, 0xE0, 0x00,
    0x00, 0x00, 0x48, 0x8B, 0xB4, 0x24, 0xE8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x74, 0x24, 0x30, 0x48,
    0x89, 0x54, 0x24, 0x28, 0x48, 0x89, 0x54, 0x24, 0x48, 0x48, 0x89, 0x74, 0x24, 0x50, 0x48, 0x89,
    0x4C, 0x24, 0x58, 0x48, 0x89, 0x44, 0x24, 0x60, 0x48, 0xC7, 0x84, 0x24, 0xF8, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0xF0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x48, 0xC7, 0x84, 0x24, 0xE8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24,
    0xE0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x7C, 0x24, 0x48, 0x4C, 0x89, 0xFE,
    0xE8, 0x8B, 0x42, 0x00, 0x00]

theorem code_l105f70 : ∀ x ∈ codeRange 0x105f70 bytes_l105f70, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5f70 133 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105ff5 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x105ff5 (notR8Effect 0x105ff5 2 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 54) (.exec 0x105ff5 (fun s => s.RIP = 0x105ff5) (notR8Effect 0x105ff5 2 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x105ff7 (andAlImm8Effect 0x105ff7 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x105ff7 (fun s => s.RIP = 0x105ff7) (andAlImm8Effect 0x105ff7 0x1) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x105ff9 (movzxR32R8Effect 0x105ff9 3 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[55]
    (.letOp (n := 58) (.exec 0x105ff9 (fun s => s.RIP = 0x105ff9) (movzxR32R8Effect 0x105ff9 3 7 0) (Reg.operands [.gpr 0] [])) #v[55]
    (.letOp (n := 59) (.out 0x105ffc (callEffect (fun _ => 0x127d50) 0x106001) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x105ffc (PushPre 0x105ffc 5) (callEffect (fun _ => 0x127d50) 0x106001) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x106001⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(0, 55), (1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l106001, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l105ff5 : List UInt8 :=
  [0xF6, 0xD0, 0x24, 0x01, 0x0F, 0xB6, 0xF8, 0xE8, 0x4F, 0x1D, 0x02, 0x00]

theorem code_l105ff5 : ∀ x ∈ codeRange 0x105ff5 bytes_l105ff5, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5ff5 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106001 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106001 (addR64Imm8Effect 0x106001 13 0xe0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[13]
    (.letOp (n := 54) (.exec 0x106001 (fun s => s.RIP = 0x106001) (addR64Imm8Effect 0x106001 13 0xe0) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 55) (.out 0x106005 (cmpAlImm8Effect 0x106005 0x1) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[0]
    (.letOp (n := 56) (.exec 0x106005 (fun s => s.RIP = 0x106005) (cmpAlImm8Effect 0x106005 0x1) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 57) (.pure (condOp 4)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l10607d, RegMap.args [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l106009, RegMap.args [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l106001 : List UInt8 :=
  [0x49, 0x83, 0xC5, 0xE0, 0x3C, 0x01, 0x74, 0x74]

theorem code_l106001 : ∀ x ∈ codeRange 0x106001 bytes_l106001, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6001 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106009 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106009 (cmpR64Imm8Effect 0x106009 13 0x20) (EffectPart.reads (.flag .CF) [.gpr 13] []) (.flag .CF)) #v[13]
    (.letOp (n := 54) (.exec 0x106009 (fun s => s.RIP = 0x106009) (cmpR64Imm8Effect 0x106009 13 0x20) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 55) (.pure (condOp 2)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l106078, RegMap.args [(2, 2), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l10600f, RegMap.args [(2, 2), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l106009 : List UInt8 :=
  [0x49, 0x83, 0xFD, 0x20, 0x72, 0x69]

theorem code_l106009 : ∀ x ∈ codeRange 0x106009 bytes_l106009, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6009 6 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10600f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10600f (addR64Imm8Effect 0x10600f 5 0x20) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5] []) (.reg (.gpr 5))) #v[5]
    (.letOp (n := 54) (.exec 0x10600f (fun s => s.RIP = 0x10600f) (addR64Imm8Effect 0x10600f 5 0x20) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 55) (.exec 0x106013 (fun s => s.RIP = 0x106013) (fun _ => nopEffect 0x106013 13) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l106020, RegMap.args [(2, 2), (4, 4), (5, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l10600f : List UInt8 :=
  [0x48, 0x83, 0xC5, 0x20, 0x66, 0x66, 0x66, 0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00,
    0x00]

theorem code_l10600f : ∀ x ∈ codeRange 0x10600f bytes_l10600f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x600f 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106020 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106020 (leaR64Effect 0x106020 3 (.base 13 (.d8 0xe0))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 13] []) (.reg (.gpr 3))) #v[13]
    (.letOp (n := 54) (.exec 0x106020 (fun s => s.RIP = 0x106020) (leaR64Effect 0x106020 3 (.base 13 (.d8 0xe0))) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 55) (.exec 0x106024 (StorePre 0x106024 3 (fun s => AddrMode.addr (.base 14 .none) s (0x106024 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x106024 5 (.base 14 .none)) (Reg.operands [.gpr 5, .gpr 14] [])) #v[5, 14]
    (.letOp (n := 56) (.exec 0x106027 (StorePre 0x106027 4 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x106027 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x106027 3 (.base 14 (.d8 0x8))) (Reg.operands [.gpr 3, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 57) (.out 0x10602b (movR64M64Effect 0x10602b 0 (.base 5 (.d8 0xf8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[5]
    (.letOp (n := 58) (.exec 0x10602b (LoadPre 0x10602b (fun s => AddrMode.addr (.base 5 (.d8 0xf8)) s (0x10602b + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10602b 0 (.base 5 (.d8 0xf8))) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 59) (.exec 0x10602f (StorePre 0x10602f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10602f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10602f 0 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 60) (.out 0x106037 (movR64M64Effect 0x106037 0 (.base 5 (.d8 0xf0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[5]
    (.letOp (n := 61) (.exec 0x106037 (LoadPre 0x106037 (fun s => AddrMode.addr (.base 5 (.d8 0xf0)) s (0x106037 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x106037 0 (.base 5 (.d8 0xf0))) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 62) (.exec 0x10603b (StorePre 0x10603b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10603b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10603b 0 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[60, 4]
    (.letOp (n := 63) (.out 0x106040 (movR64M64Effect 0x106040 0 (.base 5 (.d8 0xe0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[5]
    (.letOp (n := 64) (.exec 0x106040 (LoadPre 0x106040 (fun s => AddrMode.addr (.base 5 (.d8 0xe0)) s (0x106040 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x106040 0 (.base 5 (.d8 0xe0))) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 65) (.out 0x106044 (movR64M64Effect 0x106044 1 (.base 5 (.d8 0xe8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[5]
    (.letOp (n := 66) (.exec 0x106044 (LoadPre 0x106044 (fun s => AddrMode.addr (.base 5 (.d8 0xe8)) s (0x106044 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x106044 1 (.base 5 (.d8 0xe8))) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 67) (.exec 0x106048 (StorePre 0x106048 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x106048 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x106048 1 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.exec 0x10604d (StorePre 0x10604d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x10604d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10604d 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[63, 4]
    (.letOp (n := 69) (.out 0x106052 (movR64R64Effect 0x106052 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[15]
    (.letOp (n := 70) (.exec 0x106052 (fun s => s.RIP = 0x106052) (movR64R64Effect 0x106052 7 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 71) (.out 0x106055 (movR64R64Effect 0x106055 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 12] []) (.reg (.gpr 6))) #v[12]
    (.letOp (n := 72) (.exec 0x106055 (fun s => s.RIP = 0x106055) (movR64R64Effect 0x106055 6 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 73) (.out 0x106058 (callEffect (fun _ => 0x109e60) 0x10605d) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 74) (.exec 0x106058 (PushPre 0x106058 5) (callEffect (fun _ => 0x109e60) 0x10605d) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.const ⟨64, 0x10605d⟩) #v[]
    (.terminate (.call ⟨.l109e60, RegMap.args [(0, 63), (1, 65), (2, 2), (3, 53), (4, 73), (5, 5), (6, 71), (7, 69), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 76⟩ { target := .l10605d, kept := #v[], arity := rfl, guard := some (Fin.last 75) }))))))))))))))))))))))))

def bytes_l106020 : List UInt8 :=
  [0x49, 0x8D, 0x5D, 0xE0, 0x49, 0x89, 0x2E, 0x49, 0x89, 0x5E, 0x08, 0x48, 0x8B, 0x45, 0xF8, 0x48,
    0x89, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x45, 0xF0, 0x48, 0x89, 0x44, 0x24, 0x78,
    0x48, 0x8B, 0x45, 0xE0, 0x48, 0x8B, 0x4D, 0xE8, 0x48, 0x89, 0x4C, 0x24, 0x70, 0x48, 0x89, 0x44,
    0x24, 0x68, 0x4C, 0x89, 0xFF, 0x4C, 0x89, 0xE6, 0xE8, 0x03, 0x3E, 0x00, 0x00]

theorem code_l106020 : ∀ x ∈ codeRange 0x106020 bytes_l106020, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6020 61 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10605d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10605d (cmpM8Imm8Effect 0x10605d 8 (.sib 4 none 0 (.d32 0x100)) 0x1) (EffectPart.reads (.flag .ZF) [.gpr 4] []) (.flag .ZF)) #v[4]
    (.letOp (n := 54) (.exec 0x10605d (LoadPre 0x10605d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x10605d + BitVec.ofNat 64 8)) 1) (cmpM8Imm8Effect 0x10605d 8 (.sib 4 none 0 (.d32 0x100)) 0x1) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l105f70, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l10606b, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l10605d : List UInt8 :=
  [0x80, 0xBC, 0x24, 0x00, 0x01, 0x00, 0x00, 0x01, 0x0F, 0x84, 0x05, 0xFF, 0xFF, 0xFF]

theorem code_l10605d : ∀ x ∈ codeRange 0x10605d bytes_l10605d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x605d 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10606b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10606b (addR64Imm8Effect 0x10606b 5 0x20) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5] []) (.reg (.gpr 5))) #v[5]
    (.letOp (n := 54) (.exec 0x10606b (fun s => s.RIP = 0x10606b) (addR64Imm8Effect 0x10606b 5 0x20) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 55) (.out 0x10606f (movR64R64Effect 0x10606f 13 3) (EffectPart.reads (.reg (.gpr 13)) [.gpr 3] []) (.reg (.gpr 13))) #v[3]
    (.letOp (n := 56) (.exec 0x10606f (fun s => s.RIP = 0x10606f) (movR64R64Effect 0x10606f 13 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 57) (.out 0x106072 (cmpR64Imm8Effect 0x106072 3 0x20) (EffectPart.reads (.flag .CF) [.gpr 3] []) (.flag .CF)) #v[3]
    (.letOp (n := 58) (.exec 0x106072 (fun s => s.RIP = 0x106072) (cmpR64Imm8Effect 0x106072 3 0x20) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 59) (.pure (condOp 3)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l106020, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 55), (14, 14), (15, 15), (16, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l106078, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 55), (14, 14), (15, 15), (16, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l10606b : List UInt8 :=
  [0x48, 0x83, 0xC5, 0x20, 0x49, 0x89, 0xDD, 0x48, 0x83, 0xFB, 0x20, 0x73, 0xA8]

theorem code_l10606b : ∀ x ∈ codeRange 0x10606b bytes_l10606b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x606b 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106078 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x106078 (PushPre 0x106078 5) (callEffect (fun _ => 0x100a30) 0x10607d) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.const ⟨64, 0x10607d⟩) #v[]
    (.terminate (.call ⟨.l100a30, RegMap.args [] 55⟩ { target := .l10607d, kept := #v[], arity := rfl, guard := some (Fin.last 54) })))

def bytes_l106078 : List UInt8 :=
  [0xE8, 0xB3, 0xA9, 0xFF, 0xFF]

theorem code_l106078 : ∀ x ∈ codeRange 0x106078 bytes_l106078, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6078 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10607d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10607d (movR64M64Effect 0x10607d 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x10607d (LoadPre 0x10607d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10607d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10607d 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x106082 (StorePre 0x106082 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x106082 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x106082 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x106087 (movR64M64Effect 0x106087 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x106087 (LoadPre 0x106087 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x106087 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106087 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x10608c (StorePre 0x10608c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10608c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10608c 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x106091 (movR64M64Effect 0x106091 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x106091 (LoadPre 0x106091 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x106091 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106091 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x106096 (movR64M64Effect 0x106096 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 62) (.exec 0x106096 (LoadPre 0x106096 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x106096 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106096 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x10609b (StorePre 0x10609b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10609b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10609b 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.exec 0x1060a0 (StorePre 0x1060a0 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1060a0 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1060a0 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 65) (.out 0x1060a4 (leaR64Effect 0x1060a4 14 (.sib 4 none 0 (.d32 0xe0))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 66) (.exec 0x1060a4 (fun s => s.RIP = 0x1060a4) (leaR64Effect 0x1060a4 14 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x1060ac (movR64R64Effect 0x1060ac 6 4) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 68) (.exec 0x1060ac (fun s => s.RIP = 0x1060ac) (movR64R64Effect 0x1060ac 6 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.out 0x1060af (movR64R64Effect 0x1060af 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[65]
    (.letOp (n := 70) (.exec 0x1060af (fun s => s.RIP = 0x1060af) (movR64R64Effect 0x1060af 7 14) (Reg.operands [.gpr 14] [])) #v[65]
    (.letOp (n := 71) (.out 0x1060b2 (callEffect (fun _ => 0x10ee80) 0x1060b7) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 72) (.exec 0x1060b2 (PushPre 0x1060b2 5) (callEffect (fun _ => 0x10ee80) 0x1060b7) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.const ⟨64, 0x1060b7⟩) #v[]
    (.terminate (.call ⟨.l10ee80, RegMap.args [(0, 59), (1, 61), (3, 3), (4, 71), (5, 5), (6, 67), (7, 69), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 74⟩ { target := .l1060b7, kept := #v[], arity := rfl, guard := some (Fin.last 73) }))))))))))))))))))))))

def bytes_l10607d : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x40, 0x48, 0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48,
    0x89, 0x44, 0x24, 0x10, 0x48, 0x8B, 0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89,
    0x4C, 0x24, 0x08, 0x48, 0x89, 0x04, 0x24, 0x4C, 0x8D, 0xB4, 0x24, 0xE0, 0x00, 0x00, 0x00, 0x48,
    0x89, 0xE6, 0x4C, 0x89, 0xF7, 0xE8, 0xC9, 0x8D, 0x00, 0x00]

theorem code_l10607d : ∀ x ∈ codeRange 0x10607d bytes_l10607d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x607d 58 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1060b7 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1060b7 (leaR64Effect 0x1060b7 7 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x1060b7 (fun s => s.RIP = 0x1060b7) (leaR64Effect 0x1060b7 7 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1060bf (movR64R64Effect 0x1060bf 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 56) (.exec 0x1060bf (fun s => s.RIP = 0x1060bf) (movR64R64Effect 0x1060bf 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x1060c2 (callEffect (fun _ => 0x10fe50) 0x1060c7) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x1060c2 (PushPre 0x1060c2 5) (callEffect (fun _ => 0x10fe50) 0x1060c7) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x1060c7⟩) #v[]
    (.terminate (.call ⟨.l10fe50, RegMap.args [(3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ { target := .l1060c7, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l1060b7 : List UInt8 :=
  [0x48, 0x8D, 0xBC, 0x24, 0x88, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF6, 0xE8, 0x89, 0x9D, 0x00, 0x00]

theorem code_l1060b7 : ∀ x ∈ codeRange 0x1060b7 bytes_l1060b7, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x60b7 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1060c7_1 : Block Op Label signature Reg.count 97 :=
  .letOp (n := 97) (.out 0x106117 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[95]
    (.letOp (n := 98) (.out 0x106117 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[95]
    (.letOp (n := 99) (.exec 0x106117 (RetPre 0x106117) (retEffect) (Reg.operands [.gpr 4] [])) #v[95]
    (.terminate (.ret (RegMap.args [(0, 69), (1, 75), (2, 2), (3, 79), (4, 98), (5, 94), (6, 73), (7, 74), (8, 8), (9, 9), (10, 10), (11, 11), (12, 82), (13, 85), (14, 88), (15, 91), (22, 22), (39, 39), (50, 50), (51, 51)] 100) (some ⟨97, by decide⟩)))))

def bytes_l1060c7_1 : List UInt8 :=
  [0xC3]

theorem code_l1060c7_1 : ∀ x ∈ codeRange 0x106117 bytes_l1060c7_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6117 1 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1060c7 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1060c7 (movR64M64Effect 0x1060c7 0 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1060c7 (LoadPre 0x1060c7 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1060c7 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1060c7 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1060cb (movR64M64Effect 0x1060cb 1 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x1060cb (LoadPre 0x1060cb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1060cb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1060cb 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x1060d0 (StorePre 0x1060d0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x1060d0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1060d0 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 58) (.exec 0x1060d5 (StorePre 0x1060d5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x1060d5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1060d5 1 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 59) (.out 0x1060da (movR64M64Effect 0x1060da 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x1060da (LoadPre 0x1060da (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1060da + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1060da 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x1060df (StorePre 0x1060df 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1060df + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1060df 0 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x1060e4 (movR64M64Effect 0x1060e4 0 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x1060e4 (LoadPre 0x1060e4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1060e4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1060e4 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x1060e9 (StorePre 0x1060e9 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1060e9 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1060e9 0 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x1060f1 (leaR64Effect 0x1060f1 6 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 66) (.exec 0x1060f1 (fun s => s.RIP = 0x1060f1) (leaR64Effect 0x1060f1 6 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x1060f6 (movR32Imm32Effect 0x1060f6 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 68) (.exec 0x1060f6 (fun s => s.RIP = 0x1060f6) (movR32Imm32Effect 0x1060f6 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 69) (.out 0x1060fb (movR64M64Effect 0x1060fb 0 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 70) (.exec 0x1060fb (LoadPre 0x1060fb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1060fb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1060fb 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.out 0x106100 (movR64R64Effect 0x106100 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[69]
    (.letOp (n := 72) (.exec 0x106100 (fun s => s.RIP = 0x106100) (movR64R64Effect 0x106100 7 0) (Reg.operands [.gpr 0] [])) #v[69]
    (.letOp (n := 73) (.out 0x106103 (repMovsqEffect 0x106103) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 6))) #v[65, 71, 67, 22]
    (.letOp (n := 74) (.out 0x106103 (repMovsqEffect 0x106103) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 7))) #v[65, 71, 67, 22]
    (.letOp (n := 75) (.out 0x106103 (repMovsqEffect 0x106103) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 1))) #v[65, 71, 67, 22]
    (.letOp (n := 76) (.exec 0x106103 (RepPre 0x106103 (RepMovsqPre 0x106103)) (repMovsqEffect 0x106103) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[65, 71, 67, 22]
    (.letOp (n := 77) (.out 0x106106 (addR64Imm32Effect 0x106106 4 0x158) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 78) (.exec 0x106106 (fun s => s.RIP = 0x106106) (addR64Imm32Effect 0x106106 4 0x158) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.out 0x10610d (popR64Effect 0x10610d 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[77]
    (.letOp (n := 80) (.out 0x10610d (popR64Effect 0x10610d 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[77]
    (.letOp (n := 81) (.exec 0x10610d (PopPre 0x10610d) (popR64Effect 0x10610d 1 3) (Reg.operands [.gpr 4] [])) #v[77]
    (.letOp (n := 82) (.out 0x10610e (popR64Effect 0x10610e 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[80]
    (.letOp (n := 83) (.out 0x10610e (popR64Effect 0x10610e 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[80]
    (.letOp (n := 84) (.exec 0x10610e (PopPre 0x10610e) (popR64Effect 0x10610e 2 12) (Reg.operands [.gpr 4] [])) #v[80]
    (.letOp (n := 85) (.out 0x106110 (popR64Effect 0x106110 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[83]
    (.letOp (n := 86) (.out 0x106110 (popR64Effect 0x106110 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[83]
    (.letOp (n := 87) (.exec 0x106110 (PopPre 0x106110) (popR64Effect 0x106110 2 13) (Reg.operands [.gpr 4] [])) #v[83]
    (.letOp (n := 88) (.out 0x106112 (popR64Effect 0x106112 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[86]
    (.letOp (n := 89) (.out 0x106112 (popR64Effect 0x106112 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[86]
    (.letOp (n := 90) (.exec 0x106112 (PopPre 0x106112) (popR64Effect 0x106112 2 14) (Reg.operands [.gpr 4] [])) #v[86]
    (.letOp (n := 91) (.out 0x106114 (popR64Effect 0x106114 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[89]
    (.letOp (n := 92) (.out 0x106114 (popR64Effect 0x106114 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[89]
    (.letOp (n := 93) (.exec 0x106114 (PopPre 0x106114) (popR64Effect 0x106114 2 15) (Reg.operands [.gpr 4] [])) #v[89]
    (.letOp (n := 94) (.out 0x106116 (popR64Effect 0x106116 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[92]
    (.letOp (n := 95) (.out 0x106116 (popR64Effect 0x106116 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[92]
    (.letOp (n := 96) (.exec 0x106116 (PopPre 0x106116) (popR64Effect 0x106116 1 5) (Reg.operands [.gpr 4] [])) #v[92]
    (b_l1060c7_1))))))))))))))))))))))))))))))))))))))))))))

def bytes_l1060c7 : List UInt8 :=
  [0x48, 0x8B, 0x04, 0x24, 0x48, 0x8B, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x44, 0x24, 0x68, 0x48, 0x89,
    0x4C, 0x24, 0x70, 0x48, 0x8B, 0x44, 0x24, 0x10, 0x48, 0x89, 0x44, 0x24, 0x78, 0x48, 0x8B, 0x44,
    0x24, 0x18, 0x48, 0x89, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x74, 0x24, 0x68, 0xB9,
    0x0F, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x20, 0x48, 0x89, 0xC7, 0xF3, 0x48, 0xA5, 0x48,
    0x81, 0xC4, 0x58, 0x01, 0x00, 0x00, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F, 0x5D] ++ bytes_l1060c7_1

theorem code_l1060c7 : ∀ x ∈ codeRange 0x1060c7 bytes_l1060c7, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x60c7 80 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1060c7_1

@[cfg_block] def b_l106120 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106120 (pushR64Effect 0x106120 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x106120 (PushPre 0x106120 1) (pushR64Effect 0x106120 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x106121 (pushR64Effect 0x106121 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x106121 (PushPre 0x106121 2) (pushR64Effect 0x106121 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x106123 (pushR64Effect 0x106123 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x106123 (PushPre 0x106123 2) (pushR64Effect 0x106123 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x106125 (pushR64Effect 0x106125 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x106125 (PushPre 0x106125 2) (pushR64Effect 0x106125 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x106127 (pushR64Effect 0x106127 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x106127 (PushPre 0x106127 2) (pushR64Effect 0x106127 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x106129 (pushR64Effect 0x106129 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x106129 (PushPre 0x106129 1) (pushR64Effect 0x106129 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x10612a (subR64Imm8Effect 0x10612a 4 0x38) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x10612a (fun s => s.RIP = 0x10612a) (subR64Imm8Effect 0x10612a 4 0x38) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x10612e (movR64R64Effect 0x10612e 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 6] []) (.reg (.gpr 14))) #v[6]
    (.letOp (n := 68) (.exec 0x10612e (fun s => s.RIP = 0x10612e) (movR64R64Effect 0x10612e 14 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 69) (.out 0x106131 (movR64R64Effect 0x106131 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 70) (.exec 0x106131 (fun s => s.RIP = 0x106131) (movR64R64Effect 0x106131 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 71) (.out 0x106134 (movR64R64Effect 0x106134 7 4) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[65]
    (.letOp (n := 72) (.exec 0x106134 (fun s => s.RIP = 0x106134) (movR64R64Effect 0x106134 7 4) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 73) (.out 0x106137 (movR32Imm32Effect 0x106137 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 74) (.exec 0x106137 (fun s => s.RIP = 0x106137) (movR32Imm32Effect 0x106137 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 75) (.out 0x10613c (callEffect (fun _ => 0x127b80) 0x106141) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 76) (.exec 0x10613c (PushPre 0x10613c 5) (callEffect (fun _ => 0x127b80) 0x106141) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 77) (.const ⟨64, 0x106141⟩) #v[]
    (.terminate (.call ⟨.l127b80, RegMap.args [(2, 73), (3, 69), (4, 75), (5, 5), (6, 6), (7, 71), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 78⟩ { target := .l106141, kept := #v[], arity := rfl, guard := some (Fin.last 77) }))))))))))))))))))))))))))

def bytes_l106120 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x83, 0xEC, 0x38, 0x49, 0x89,
    0xF6, 0x48, 0x89, 0xFB, 0x48, 0x89, 0xE7, 0xBA, 0x01, 0x00, 0x00, 0x00, 0xE8, 0x3F, 0x1A, 0x02,
    0x00]

theorem code_l106120 : ∀ x ∈ codeRange 0x106120 bytes_l106120, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6120 33 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106141 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106141 (movR32M32LowEffect 0x106141 0 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x106141 (LoadPre 0x106141 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x106141 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x106141 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x106144 (cmpR32Imm8Effect 0x106144 3 0 0x2) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x106144 (fun s => s.RIP = 0x106144) (cmpR32Imm8Effect 0x106144 3 0 0x2) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l106222, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l10614d, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l106141 : List UInt8 :=
  [0x8B, 0x04, 0x24, 0x83, 0xF8, 0x02, 0x0F, 0x85, 0xD5, 0x00, 0x00, 0x00]

theorem code_l106141 : ∀ x ∈ codeRange 0x106141 bytes_l106141, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6141 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10614d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10614d (movR64M64Effect 0x10614d 6 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 54) (.exec 0x10614d (LoadPre 0x10614d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10614d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10614d 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x106152 (cmpR64Imm8Effect 0x106152 6 0x1) (EffectPart.reads (.flag .ZF) [.gpr 6] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x106152 (fun s => s.RIP = 0x106152) (cmpR64Imm8Effect 0x106152 6 0x1) (Reg.operands [.gpr 6] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l1062b7, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l10615c, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l10614d : List UInt8 :=
  [0x48, 0x8B, 0x74, 0x24, 0x10, 0x48, 0x83, 0xFE, 0x01, 0x0F, 0x85, 0x5B, 0x01, 0x00, 0x00]

theorem code_l10614d : ∀ x ∈ codeRange 0x10614d bytes_l10614d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x614d 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10615c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10615c (movR64M64Effect 0x10615c 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x10615c (LoadPre 0x10615c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10615c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10615c 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x106161 (movsxR32M8Effect 0x106161 3 5 (.base 0 .none)) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[53]
    (.letOp (n := 56) (.exec 0x106161 (LoadPre 0x106161 (fun s => AddrMode.addr (.base 0 .none) s (0x106161 + BitVec.ofNat 64 3)) 1) (movsxR32M8Effect 0x106161 3 5 (.base 0 .none)) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x106164 (testR32R32Effect 0x106164 2 5 5) (EffectPart.reads (.flag .SF) [.gpr 5, .gpr 5] []) (.flag .SF)) #v[55, 55]
    (.letOp (n := 58) (.exec 0x106164 (fun s => s.RIP = 0x106164) (testR32R32Effect 0x106164 2 5 5) (Reg.operands [.gpr 5, .gpr 5] [])) #v[55, 55]
    (.letOp (n := 59) (.pure (condOp 8)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l106176, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (20, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l106168, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (20, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l10615c : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x08, 0x0F, 0xBE, 0x28, 0x85, 0xED, 0x78, 0x0E]

theorem code_l10615c : ∀ x ∈ codeRange 0x10615c bytes_l10615c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x615c 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106168 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x106168 (StorePre 0x106168 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x106168 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x106168 5 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 5, .gpr 3] [])) #v[5, 3]
    (.terminate (.br ⟨.l10616b, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 54⟩))

def bytes_l106168 : List UInt8 :=
  [0x89, 0x6B, 0x04]

theorem code_l106168 : ∀ x ∈ codeRange 0x106168 bytes_l106168, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6168 3 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10616b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x10616b (StorePre 0x10616b 6 (fun s => AddrMode.addr (.base 3 .none) s (0x10616b + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x10616b 6 (.base 3 .none) 0x2) (Reg.operands [.gpr 3] [])) #v[3]
    (.terminate (.br ⟨.l106261, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 54⟩))

def bytes_l10616b : List UInt8 :=
  [0xC7, 0x03, 0x02, 0x00, 0x00, 0x00, 0xE9, 0xEB, 0x00, 0x00, 0x00]

theorem code_l10616b : ∀ x ∈ codeRange 0x10616b bytes_l10616b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x616b 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106176 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106176 (movR32R32Effect 0x106176 2 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[5]
    (.letOp (n := 54) (.exec 0x106176 (fun s => s.RIP = 0x106176) (movR32R32Effect 0x106176 2 0 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 55) (.out 0x106178 (negR8Effect 0x106178 2 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.out 0x106178 (negR8Effect 0x106178 2 0) (EffectPart.reads (.flag .OF) [.gpr 0] []) (.flag .OF)) #v[53]
    (.letOp (n := 57) (.exec 0x106178 (fun s => s.RIP = 0x106178) (negR8Effect 0x106178 2 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 58) (.pure (condOp 1)) #v[56]
    (.terminate (.condBr (Fin.last 58) ⟨.l106197, RegMap.args [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (21, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩ ⟨.l10617c, RegMap.args [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (21, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l106176 : List UInt8 :=
  [0x89, 0xE8, 0xF6, 0xD8, 0x71, 0x1B]

theorem code_l106176 : ∀ x ∈ codeRange 0x106176 bytes_l106176, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6176 6 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10617c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x10617c (StorePre 0x10617c 5 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x10617c + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x10617c (.base 14 (.d8 0x20)) 0x1) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 54) (.out 0x106181 (movR32M32Effect 0x106181 0 (.base 14 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[14]
    (.letOp (n := 55) (.exec 0x106181 (LoadPre 0x106181 (fun s => AddrMode.addr (.base 14 (.d8 0x1c)) s (0x106181 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x106181 0 (.base 14 (.d8 0x1c))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 56) (.exec 0x106185 (StorePre 0x106185 6 (fun s => AddrMode.addr (.base 3 .none) s (0x106185 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x106185 6 (.base 3 .none) 0x1) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 57) (.exec 0x10618b (StorePre 0x10618b 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x10618b + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x10618b 0 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[54, 3]
    (.letOp (n := 58) (.exec 0x10618e (StorePre 0x10618e 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x10618e + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x10618e (.base 3 (.d8 0x8)) 0x4) (Reg.operands [.gpr 3] [])) #v[3]
    (.terminate (.br ⟨.l106261, RegMap.args [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l10617c : List UInt8 :=
  [0x41, 0xC6, 0x46, 0x20, 0x01, 0x41, 0x8B, 0x46, 0x1C, 0xC7, 0x03, 0x01, 0x00, 0x00, 0x00, 0x89,
    0x43, 0x04, 0xC6, 0x43, 0x08, 0x04, 0xE9, 0xCA, 0x00, 0x00, 0x00]

theorem code_l10617c : ∀ x ∈ codeRange 0x10617c bytes_l10617c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x617c 27 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106197 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106197 (cmpR8Imm8Effect 0x106197 4 5 0x85) (EffectPart.reads (.flag .CF) [.gpr 5] []) (.flag .CF)) #v[5]
    (.letOp (n := 54) (.exec 0x106197 (fun s => s.RIP = 0x106197) (cmpR8Imm8Effect 0x106197 4 5 0x85) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 55) (.pure (condOp 3)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l10629f, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l1061a1, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l106197 : List UInt8 :=
  [0x40, 0x80, 0xFD, 0x85, 0x0F, 0x83, 0xFE, 0x00, 0x00, 0x00]

theorem code_l106197 : ∀ x ∈ codeRange 0x106197 bytes_l106197, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6197 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1061a1 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1061a1 (testR8Imm8Effect 0x1061a1 5 0x7f) (EffectPart.reads (.flag .ZF) [.gpr 5] []) (.flag .ZF)) #v[5]
    (.letOp (n := 54) (.exec 0x1061a1 (fun s => s.RIP = 0x1061a1) (testR8Imm8Effect 0x1061a1 5 0x7f) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l106273, RegMap.args [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l1061ab, RegMap.args [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l1061a1 : List UInt8 :=
  [0x40, 0xF6, 0xC5, 0x7F, 0x0F, 0x84, 0xC8, 0x00, 0x00, 0x00]

theorem code_l1061a1 : ∀ x ∈ codeRange 0x1061a1 bytes_l1061a1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x61a1 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1061ab : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1061ab (movR32R32Effect 0x1061ab 3 13 5) (EffectPart.reads (.reg (.gpr 13)) [.gpr 5] []) (.reg (.gpr 13))) #v[5]
    (.letOp (n := 54) (.exec 0x1061ab (fun s => s.RIP = 0x1061ab) (movR32R32Effect 0x1061ab 3 13 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 55) (.out 0x1061ae (andR32Imm8Effect 0x1061ae 4 13 0x7f) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[53]
    (.letOp (n := 56) (.exec 0x1061ae (fun s => s.RIP = 0x1061ae) (andR32Imm8Effect 0x1061ae 4 13 0x7f) (Reg.operands [.gpr 13] [])) #v[53]
    (.letOp (n := 57) (.out 0x1061b2 (xorR32R32Effect 0x1061b2 3 12 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 12] []) (.reg (.gpr 12))) #v[12, 12]
    (.letOp (n := 58) (.exec 0x1061b2 (fun s => s.RIP = 0x1061b2) (xorR32R32Effect 0x1061b2 3 12 12) (Reg.operands [.gpr 12, .gpr 12] [])) #v[12, 12]
    (.letOp (n := 59) (.out 0x1061b5 (movR64R64Effect 0x1061b5 15 4) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 60) (.exec 0x1061b5 (fun s => s.RIP = 0x1061b5) (movR64R64Effect 0x1061b5 15 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x1061b8 (fun s => s.RIP = 0x1061b8) (fun _ => nopEffect 0x1061b8 8) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l1061c0, RegMap.args [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 55), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩))))))))))

def bytes_l1061ab : List UInt8 :=
  [0x41, 0x89, 0xED, 0x41, 0x83, 0xE5, 0x7F, 0x45, 0x31, 0xE4, 0x49, 0x89, 0xE7, 0x0F, 0x1F, 0x84,
    0x00, 0x00, 0x00, 0x00, 0x00]

theorem code_l1061ab : ∀ x ∈ codeRange 0x1061ab bytes_l1061ab, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x61ab 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1061c0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1061c0 (movR64R64Effect 0x1061c0 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[15]
    (.letOp (n := 54) (.exec 0x1061c0 (fun s => s.RIP = 0x1061c0) (movR64R64Effect 0x1061c0 7 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.out 0x1061c3 (movR64R64Effect 0x1061c3 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 56) (.exec 0x1061c3 (fun s => s.RIP = 0x1061c3) (movR64R64Effect 0x1061c3 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x1061c6 (movR32Imm32Effect 0x1061c6 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x1061c6 (fun s => s.RIP = 0x1061c6) (movR32Imm32Effect 0x1061c6 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x1061cb (callEffect (fun _ => 0x127b80) 0x1061d0) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x1061cb (PushPre 0x1061cb 5) (callEffect (fun _ => 0x127b80) 0x1061d0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x1061d0⟩) #v[]
    (.terminate (.call ⟨.l127b80, RegMap.args [(2, 57), (3, 3), (4, 59), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l1061d0, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l1061c0 : List UInt8 :=
  [0x4C, 0x89, 0xFF, 0x4C, 0x89, 0xF6, 0xBA, 0x01, 0x00, 0x00, 0x00, 0xE8, 0xB0, 0x19, 0x02, 0x00]

theorem code_l1061c0 : ∀ x ∈ codeRange 0x1061c0 bytes_l1061c0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x61c0 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1061d0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1061d0 (movR32M32LowEffect 0x1061d0 0 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1061d0 (LoadPre 0x1061d0 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1061d0 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x1061d0 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1061d3 (cmpR32Imm8Effect 0x1061d3 3 0 0x2) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x1061d3 (fun s => s.RIP = 0x1061d3) (cmpR32Imm8Effect 0x1061d3 3 0 0x2) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l106222, RegMap.args [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l1061d8, RegMap.args [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l1061d0 : List UInt8 :=
  [0x8B, 0x04, 0x24, 0x83, 0xF8, 0x02, 0x75, 0x4A]

theorem code_l1061d0 : ∀ x ∈ codeRange 0x1061d0 bytes_l1061d0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x61d0 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1061d8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1061d8 (movR64M64Effect 0x1061d8 6 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 54) (.exec 0x1061d8 (LoadPre 0x1061d8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1061d8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1061d8 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1061dd (cmpR64Imm8Effect 0x1061dd 6 0x1) (EffectPart.reads (.flag .ZF) [.gpr 6] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x1061dd (fun s => s.RIP = 0x1061dd) (cmpR64Imm8Effect 0x1061dd 6 0x1) (Reg.operands [.gpr 6] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l1062b7, RegMap.args [(1, 1), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l1061e7, RegMap.args [(1, 1), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l1061d8 : List UInt8 :=
  [0x48, 0x8B, 0x74, 0x24, 0x10, 0x48, 0x83, 0xFE, 0x01, 0x0F, 0x85, 0xD0, 0x00, 0x00, 0x00]

theorem code_l1061d8 : ∀ x ∈ codeRange 0x1061d8 bytes_l1061d8, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x61d8 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1061e7 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1061e7 (movR64M64Effect 0x1061e7 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1061e7 (LoadPre 0x1061e7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1061e7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1061e7 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1061ec (movR32R32Effect 0x1061ec 3 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12] []) (.reg (.gpr 2))) #v[12]
    (.letOp (n := 56) (.exec 0x1061ec (fun s => s.RIP = 0x1061ec) (movR32R32Effect 0x1061ec 3 2 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 57) (.out 0x1061ef (movzxR32M8Effect 0x1061ef 4 12 (.base 0 .none)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[53]
    (.letOp (n := 58) (.exec 0x1061ef (LoadPre 0x1061ef (fun s => AddrMode.addr (.base 0 .none) s (0x1061ef + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x1061ef 4 12 (.base 0 .none)) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 59) (.out 0x1061f3 (shlR32Effect 0x1061f3 3 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[55]
    (.letOp (n := 60) (.exec 0x1061f3 (fun s => s.RIP = 0x1061f3) (shlR32Effect 0x1061f3 3 2 8) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[55]
    (.letOp (n := 61) (.out 0x1061f6 (orR32R32Effect 0x1061f6 3 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 2] []) (.reg (.gpr 12))) #v[57, 59]
    (.letOp (n := 62) (.exec 0x1061f6 (fun s => s.RIP = 0x1061f6) (orR32R32Effect 0x1061f6 3 12 2) (Reg.operands [.gpr 12, .gpr 2] [])) #v[57, 59]
    (.letOp (n := 63) (.out 0x1061f9 (decR64Effect 0x1061f9 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[13]
    (.letOp (n := 64) (.out 0x1061f9 (decR64Effect 0x1061f9 13) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.flag .ZF)) #v[13]
    (.letOp (n := 65) (.exec 0x1061f9 (fun s => s.RIP = 0x1061f9) (decR64Effect 0x1061f9 13) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[13]
    (.letOp (n := 66) (.pure (condOp 5)) #v[64]
    (.terminate (.condBr (Fin.last 66) ⟨.l1061c0, RegMap.args [(0, 53), (1, 1), (2, 59), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 63), (14, 14), (15, 15), (19, 64), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩ ⟨.l1061fe, RegMap.args [(0, 53), (1, 1), (2, 59), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 63), (14, 14), (15, 15), (19, 64), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩)))))))))))))))

def bytes_l1061e7 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x08, 0x44, 0x89, 0xE2, 0x44, 0x0F, 0xB6, 0x20, 0xC1, 0xE2, 0x08, 0x41,
    0x09, 0xD4, 0x49, 0xFF, 0xCD, 0x75, 0xC2]

theorem code_l1061e7 : ∀ x ∈ codeRange 0x1061e7 bytes_l1061e7, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x61e7 23 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1061fe : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1061fe (movR32R32Effect 0x1061fe 3 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 12] []) (.reg (.gpr 6))) #v[12]
    (.letOp (n := 54) (.exec 0x1061fe (fun s => s.RIP = 0x1061fe) (movR32R32Effect 0x1061fe 3 6 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 55) (.out 0x106201 (andR32Imm8Effect 0x106201 3 6 0x80) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[53]
    (.letOp (n := 56) (.exec 0x106201 (fun s => s.RIP = 0x106201) (andR32Imm8Effect 0x106201 3 6 0x80) (Reg.operands [.gpr 6] [])) #v[53]
    (.letOp (n := 57) (.out 0x106204 (movR8Imm8Effect 0x106204 2 0 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 58) (.exec 0x106204 (fun s => s.RIP = 0x106204) (movR8Imm8Effect 0x106204 2 0 0x1) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 59) (.out 0x106206 (movR8Imm8Effect 0x106206 2 1 0x81) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1]
    (.letOp (n := 60) (.exec 0x106206 (fun s => s.RIP = 0x106206) (movR8Imm8Effect 0x106206 2 1 0x81) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 61) (.out 0x106208 (cmpR32Imm32Effect 0x106208 6 6 0x80) (EffectPart.reads (.flag .ZF) [.gpr 6] []) (.flag .ZF)) #v[55]
    (.letOp (n := 62) (.exec 0x106208 (fun s => s.RIP = 0x106208) (cmpR32Imm32Effect 0x106208 6 6 0x80) (Reg.operands [.gpr 6] [])) #v[55]
    (.letOp (n := 63) (.pure (condOp 4)) #v[61]
    (.terminate (.condBr (Fin.last 63) ⟨.l10628d, RegMap.args [(0, 57), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 55), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (19, 61), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ ⟨.l106210, RegMap.args [(0, 57), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 55), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (19, 61), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩))))))))))))

def bytes_l1061fe : List UInt8 :=
  [0x44, 0x89, 0xE6, 0x83, 0xE6, 0x80, 0xB0, 0x01, 0xB1, 0x81, 0x81, 0xFE, 0x80, 0x00, 0x00, 0x00,
    0x74, 0x7D]

theorem code_l1061fe : ∀ x ∈ codeRange 0x1061fe bytes_l1061fe, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x61fe 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106210 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106210 (addR32Imm32Effect 0x106210 6 2 0xffffff00) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[2]
    (.letOp (n := 54) (.exec 0x106210 (fun s => s.RIP = 0x106210) (addR32Imm32Effect 0x106210 6 2 0xffffff00) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 55) (.out 0x106216 (movR8Imm8Effect 0x106216 2 1 0x82) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1]
    (.letOp (n := 56) (.exec 0x106216 (fun s => s.RIP = 0x106216) (movR8Imm8Effect 0x106216 2 1 0x82) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 57) (.out 0x106218 (cmpR32Imm32Effect 0x106218 6 2 0xff00) (EffectPart.reads (.flag .CF) [.gpr 2] []) (.flag .CF)) #v[53]
    (.letOp (n := 58) (.exec 0x106218 (fun s => s.RIP = 0x106218) (cmpR32Imm32Effect 0x106218 6 2 0xff00) (Reg.operands [.gpr 2] [])) #v[53]
    (.letOp (n := 59) (.pure (condOp 3)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l106276, RegMap.args [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (16, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l106220, RegMap.args [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (16, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l106210 : List UInt8 :=
  [0x81, 0xC2, 0x00, 0xFF, 0xFF, 0xFF, 0xB1, 0x82, 0x81, 0xFA, 0x00, 0xFF, 0x00, 0x00, 0x73, 0x56]

theorem code_l106210 : ∀ x ∈ codeRange 0x106210 bytes_l106210, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6210 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106220 : Block Op Label signature Reg.count 53 :=
  .terminate (.br ⟨.l10628d, RegMap.args (entryMap (live .l106220)) 53⟩)

def bytes_l106220 : List UInt8 :=
  [0xEB, 0x6B]

theorem code_l106220 : ∀ x ∈ codeRange 0x106220 bytes_l106220, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6220 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106222 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106222 (movR32M32LowEffect 0x106222 1 (.sib 4 none 0 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x106222 (LoadPre 0x106222 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x106222 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x106222 1 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x106226 (movR64M64Effect 0x106226 2 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 56) (.exec 0x106226 (LoadPre 0x106226 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x106226 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106226 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x10622b (movR64M64Effect 0x10622b 6 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 58) (.exec 0x10622b (LoadPre 0x10622b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10622b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10622b 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x106230 (movR64M64Effect 0x106230 7 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 60) (.exec 0x106230 (LoadPre 0x106230 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x106230 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106230 7 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x106235 (StorePre 0x106235 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x106235 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x106235 7 (.base 3 (.d8 0x30))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[59, 3]
    (.letOp (n := 62) (.out 0x106239 (movR64M64Effect 0x106239 7 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 63) (.exec 0x106239 (LoadPre 0x106239 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x106239 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106239 7 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x10623e (StorePre 0x10623e 4 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x10623e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10623e 7 (.base 3 (.d8 0x28))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[62, 3]
    (.letOp (n := 65) (.out 0x106242 (movR64M64Effect 0x106242 7 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 66) (.exec 0x106242 (LoadPre 0x106242 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x106242 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106242 7 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x106247 (StorePre 0x106247 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x106247 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x106247 7 (.base 3 (.d8 0x20))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[65, 3]
    (.letOp (n := 68) (.out 0x10624b (movR64M64Effect 0x10624b 7 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 69) (.exec 0x10624b (LoadPre 0x10624b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10624b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10624b 7 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.exec 0x106250 (StorePre 0x106250 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x106250 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x106250 7 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[68, 3]
    (.letOp (n := 71) (.exec 0x106254 (StorePre 0x106254 2 (fun s => AddrMode.addr (.base 3 .none) s (0x106254 + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x106254 0 (.base 3 .none)) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (.letOp (n := 72) (.exec 0x106256 (StorePre 0x106256 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x106256 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x106256 1 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[53, 3]
    (.letOp (n := 73) (.exec 0x106259 (StorePre 0x106259 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x106259 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x106259 2 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[55, 3]
    (.letOp (n := 74) (.exec 0x10625d (StorePre 0x10625d 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x10625d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10625d 6 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[57, 3]
    (.terminate (.br ⟨.l106261, RegMap.args [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩)))))))))))))))))))))))

def bytes_l106222 : List UInt8 :=
  [0x8B, 0x4C, 0x24, 0x04, 0x48, 0x8B, 0x54, 0x24, 0x08, 0x48, 0x8B, 0x74, 0x24, 0x10, 0x48, 0x8B,
    0x7C, 0x24, 0x30, 0x48, 0x89, 0x7B, 0x30, 0x48, 0x8B, 0x7C, 0x24, 0x28, 0x48, 0x89, 0x7B, 0x28,
    0x48, 0x8B, 0x7C, 0x24, 0x20, 0x48, 0x89, 0x7B, 0x20, 0x48, 0x8B, 0x7C, 0x24, 0x18, 0x48, 0x89,
    0x7B, 0x18, 0x89, 0x03, 0x89, 0x4B, 0x04, 0x48, 0x89, 0x53, 0x08, 0x48, 0x89, 0x73, 0x10]

theorem code_l106222 : ∀ x ∈ codeRange 0x106222 bytes_l106222, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6222 63 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106261 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106261 (movR64R64Effect 0x106261 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 54) (.exec 0x106261 (fun s => s.RIP = 0x106261) (movR64R64Effect 0x106261 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x106264 (addR64Imm8Effect 0x106264 4 0x38) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 56) (.exec 0x106264 (fun s => s.RIP = 0x106264) (addR64Imm8Effect 0x106264 4 0x38) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x106268 (popR64Effect 0x106268 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[55]
    (.letOp (n := 58) (.out 0x106268 (popR64Effect 0x106268 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[55]
    (.letOp (n := 59) (.exec 0x106268 (PopPre 0x106268) (popR64Effect 0x106268 1 3) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 60) (.out 0x106269 (popR64Effect 0x106269 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[58]
    (.letOp (n := 61) (.out 0x106269 (popR64Effect 0x106269 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[58]
    (.letOp (n := 62) (.exec 0x106269 (PopPre 0x106269) (popR64Effect 0x106269 2 12) (Reg.operands [.gpr 4] [])) #v[58]
    (.letOp (n := 63) (.out 0x10626b (popR64Effect 0x10626b 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[61]
    (.letOp (n := 64) (.out 0x10626b (popR64Effect 0x10626b 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 65) (.exec 0x10626b (PopPre 0x10626b) (popR64Effect 0x10626b 2 13) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 66) (.out 0x10626d (popR64Effect 0x10626d 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[64]
    (.letOp (n := 67) (.out 0x10626d (popR64Effect 0x10626d 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[64]
    (.letOp (n := 68) (.exec 0x10626d (PopPre 0x10626d) (popR64Effect 0x10626d 2 14) (Reg.operands [.gpr 4] [])) #v[64]
    (.letOp (n := 69) (.out 0x10626f (popR64Effect 0x10626f 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[67]
    (.letOp (n := 70) (.out 0x10626f (popR64Effect 0x10626f 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[67]
    (.letOp (n := 71) (.exec 0x10626f (PopPre 0x10626f) (popR64Effect 0x10626f 2 15) (Reg.operands [.gpr 4] [])) #v[67]
    (.letOp (n := 72) (.out 0x106271 (popR64Effect 0x106271 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[70]
    (.letOp (n := 73) (.out 0x106271 (popR64Effect 0x106271 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[70]
    (.letOp (n := 74) (.exec 0x106271 (PopPre 0x106271) (popR64Effect 0x106271 1 5) (Reg.operands [.gpr 4] [])) #v[70]
    (.letOp (n := 75) (.out 0x106272 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[73]
    (.letOp (n := 76) (.out 0x106272 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[73]
    (.letOp (n := 77) (.exec 0x106272 (RetPre 0x106272) (retEffect) (Reg.operands [.gpr 4] [])) #v[73]
    (.terminate (.ret (RegMap.args [(0, 53), (1, 1), (2, 2), (3, 57), (4, 76), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 78) (some ⟨75, by decide⟩)))))))))))))))))))))))))))

def bytes_l106261 : List UInt8 :=
  [0x48, 0x89, 0xD8, 0x48, 0x83, 0xC4, 0x38, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F,
    0x5D, 0xC3]

theorem code_l106261 : ∀ x ∈ codeRange 0x106261 bytes_l106261, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6261 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106273 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106273 (xorR32R32Effect 0x106273 3 12 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 12] []) (.reg (.gpr 12))) #v[12, 12]
    (.letOp (n := 54) (.exec 0x106273 (fun s => s.RIP = 0x106273) (xorR32R32Effect 0x106273 3 12 12) (Reg.operands [.gpr 12, .gpr 12] [])) #v[12, 12]
    (.terminate (.br ⟨.l106276, RegMap.args [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l106273 : List UInt8 :=
  [0x45, 0x31, 0xE4]

theorem code_l106273 : ∀ x ∈ codeRange 0x106273 bytes_l106273, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6273 3 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106276 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106276 (movR32R32Effect 0x106276 3 1 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 12] []) (.reg (.gpr 1))) #v[12]
    (.letOp (n := 54) (.exec 0x106276 (fun s => s.RIP = 0x106276) (movR32R32Effect 0x106276 3 1 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 55) (.out 0x106279 (subR32Imm32Effect 0x106279 6 1 0x10000) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 56) (.out 0x106279 (subR32Imm32Effect 0x106279 6 1 0x10000) (EffectPart.reads (.flag .CF) [.gpr 1] []) (.flag .CF)) #v[53]
    (.letOp (n := 57) (.exec 0x106279 (fun s => s.RIP = 0x106279) (subR32Imm32Effect 0x106279 6 1 0x10000) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 58) (.out 0x10627f (atFlags (condHolds 3) (setccR8Effect 0x10627f 3 0)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 0))) #v[0, 56]
    (.letOp (n := 59) (.exec 0x10627f (fun s => s.RIP = 0x10627f) (atFlags (condHolds 3) (setccR8Effect 0x10627f 3 0)) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[0, 56]
    (.letOp (n := 60) (.out 0x106282 (cmpR32Imm32Effect 0x106282 6 1 0xff0000) (EffectPart.reads (.flag .CF) [.gpr 1] []) (.flag .CF)) #v[55]
    (.letOp (n := 61) (.exec 0x106282 (fun s => s.RIP = 0x106282) (cmpR32Imm32Effect 0x106282 6 1 0xff0000) (Reg.operands [.gpr 1] [])) #v[55]
    (.letOp (n := 62) (.out 0x106288 (movR8Imm8Effect 0x106288 2 1 0x84) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[55]
    (.letOp (n := 63) (.exec 0x106288 (fun s => s.RIP = 0x106288) (movR8Imm8Effect 0x106288 2 1 0x84) (Reg.operands [.gpr 1] [])) #v[55]
    (.letOp (n := 64) (.out 0x10628a (atFlags StatusFlags.CF (sbbR8Imm8Effect 0x10628a 3 1 0x0)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[62, 60]
    (.letOp (n := 65) (.exec 0x10628a (fun s => s.RIP = 0x10628a) (atFlags StatusFlags.CF (sbbR8Imm8Effect 0x10628a 3 1 0x0)) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[62, 60]
    (.terminate (.br ⟨.l10628d, RegMap.args [(0, 58), (1, 64), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩))))))))))))))

def bytes_l106276 : List UInt8 :=
  [0x44, 0x89, 0xE1, 0x81, 0xE9, 0x00, 0x00, 0x01, 0x00, 0x0F, 0x93, 0xC0, 0x81, 0xF9, 0x00, 0x00,
    0xFF, 0x00, 0xB1, 0x84, 0x80, 0xD9, 0x00]

theorem code_l106276 : ∀ x ∈ codeRange 0x106276 bytes_l106276, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6276 23 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10628d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10628d (testR8R8Effect 0x10628d 2 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[0, 0]
    (.letOp (n := 54) (.exec 0x10628d (fun s => s.RIP = 0x10628d) (testR8R8Effect 0x10628d 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l10629f, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l106291, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l10628d : List UInt8 :=
  [0x84, 0xC0, 0x74, 0x0E]

theorem code_l10628d : ∀ x ∈ codeRange 0x10628d bytes_l10628d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x628d 4 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106291 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106291 (cmpR8R8Effect 0x106291 3 1 5) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 5] []) (.flag .ZF)) #v[1, 5]
    (.letOp (n := 54) (.exec 0x106291 (fun s => s.RIP = 0x106291) (cmpR8R8Effect 0x106291 3 1 5) (Reg.operands [.gpr 1, .gpr 5] [])) #v[1, 5]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l10629f, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l106296, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l106291 : List UInt8 :=
  [0x40, 0x38, 0xE9, 0x75, 0x09]

theorem code_l106291 : ∀ x ∈ codeRange 0x106291 bytes_l106291, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6291 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106296 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x106296 (StorePre 0x106296 4 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x106296 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x106296 12 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 12, .gpr 3] [])) #v[12, 3]
    (.terminate (.br ⟨.l10616b, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)] 54⟩))

def bytes_l106296 : List UInt8 :=
  [0x44, 0x89, 0x63, 0x04, 0xE9, 0xCC, 0xFE, 0xFF, 0xFF]

theorem code_l106296 : ∀ x ∈ codeRange 0x106296 bytes_l106296, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6296 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10629f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x10629f (StorePre 0x10629f 5 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x10629f + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x10629f (.base 14 (.d8 0x20)) 0x1) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 54) (.out 0x1062a4 (movR32M32Effect 0x1062a4 0 (.base 14 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[14]
    (.letOp (n := 55) (.exec 0x1062a4 (LoadPre 0x1062a4 (fun s => AddrMode.addr (.base 14 (.d8 0x1c)) s (0x1062a4 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x1062a4 0 (.base 14 (.d8 0x1c))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 56) (.exec 0x1062a8 (StorePre 0x1062a8 6 (fun s => AddrMode.addr (.base 3 .none) s (0x1062a8 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x1062a8 6 (.base 3 .none) 0x1) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 57) (.exec 0x1062ae (StorePre 0x1062ae 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x1062ae + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x1062ae 0 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[54, 3]
    (.letOp (n := 58) (.exec 0x1062b1 (StorePre 0x1062b1 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x1062b1 + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x1062b1 (.base 3 (.d8 0x8)) 0xd) (Reg.operands [.gpr 3] [])) #v[3]
    (.terminate (.br ⟨.l106261, RegMap.args [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l10629f : List UInt8 :=
  [0x41, 0xC6, 0x46, 0x20, 0x01, 0x41, 0x8B, 0x46, 0x1C, 0xC7, 0x03, 0x01, 0x00, 0x00, 0x00, 0x89,
    0x43, 0x04, 0xC6, 0x43, 0x08, 0x0D, 0xEB, 0xAA]

theorem code_l10629f : ∀ x ∈ codeRange 0x10629f bytes_l10629f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x629f 24 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1062b7 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1062b7 (movR32Imm32Effect 0x1062b7 5 7 0x1) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 54) (.exec 0x1062b7 (fun s => s.RIP = 0x1062b7) (movR32Imm32Effect 0x1062b7 5 7 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x1062bc (movR64Imm32Effect 0x1062bc 2 0x202530) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 56) (.exec 0x1062bc (fun s => s.RIP = 0x1062bc) (movR64Imm32Effect 0x1062bc 2 0x202530) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x1062c3 (callEffect (fun _ => 0x129c90) 0x1062c8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x1062c3 (PushPre 0x1062c3 5) (callEffect (fun _ => 0x129c90) 0x1062c8) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x1062c8⟩) #v[]
    (.terminate (.call ⟨.l129c90, RegMap.args [(2, 55), (4, 57), (5, 5), (6, 6), (7, 53)] 60⟩ { target := .l1062c8, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l1062b7 : List UInt8 :=
  [0xBF, 0x01, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC2, 0x30, 0x25, 0x20, 0x00, 0xE8, 0xC8, 0x39, 0x02,
    0x00]

theorem code_l1062b7 : ∀ x ∈ codeRange 0x1062b7 bytes_l1062b7, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x62b7 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1062c8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1062c8 (fun s => s.RIP = 0x1062c8) (fun _ => nopEffect 0x1062c8 8) (Reg.operands [] [])) #v[]
    (.letOp (n := 54) (.out 0x1062d0 (pushR64Effect 0x1062d0 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[4, 14]
    (.letOp (n := 55) (.exec 0x1062d0 (PushPre 0x1062d0 2) (pushR64Effect 0x1062d0 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[4, 14]
    (.letOp (n := 56) (.out 0x1062d2 (pushR64Effect 0x1062d2 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[54, 3]
    (.letOp (n := 57) (.exec 0x1062d2 (PushPre 0x1062d2 1) (pushR64Effect 0x1062d2 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[54, 3]
    (.letOp (n := 58) (.out 0x1062d3 (subR64Imm32Effect 0x1062d3 4 0x88) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[56]
    (.letOp (n := 59) (.exec 0x1062d3 (fun s => s.RIP = 0x1062d3) (subR64Imm32Effect 0x1062d3 4 0x88) (Reg.operands [.gpr 4] [])) #v[56]
    (.letOp (n := 60) (.out 0x1062da (movR64R64Effect 0x1062da 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 7] []) (.reg (.gpr 6))) #v[7]
    (.letOp (n := 61) (.exec 0x1062da (fun s => s.RIP = 0x1062da) (movR64R64Effect 0x1062da 6 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 62) (.out 0x1062dd (leaR64Effect 0x1062dd 7 (.sib 4 none 0 (.d8 0xf))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[58]
    (.letOp (n := 63) (.exec 0x1062dd (fun s => s.RIP = 0x1062dd) (leaR64Effect 0x1062dd 7 (.sib 4 none 0 (.d8 0xf))) (Reg.operands [.gpr 4] [])) #v[58]
    (.letOp (n := 64) (.out 0x1062e2 (movR32Imm32Effect 0x1062e2 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 65) (.exec 0x1062e2 (fun s => s.RIP = 0x1062e2) (movR32Imm32Effect 0x1062e2 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 66) (.out 0x1062e7 (callEffect (fun _ => 0x1215e0) 0x1062ec) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[58]
    (.letOp (n := 67) (.exec 0x1062e7 (PushPre 0x1062e7 5) (callEffect (fun _ => 0x1215e0) 0x1062ec) (Reg.operands [.gpr 4] [])) #v[58]
    (.letOp (n := 68) (.const ⟨64, 0x1062ec⟩) #v[]
    (.terminate (.call ⟨.l1215e0, RegMap.args [(2, 64), (3, 3), (4, 66), (5, 5), (6, 60), (7, 62), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 69⟩ { target := .l1062ec, kept := #v[], arity := rfl, guard := some (Fin.last 68) })))))))))))))))))

def bytes_l1062c8 : List UInt8 :=
  [0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00, 0x41, 0x56, 0x53, 0x48, 0x81, 0xEC, 0x88, 0x00,
    0x00, 0x00, 0x48, 0x89, 0xFE, 0x48, 0x8D, 0x7C, 0x24, 0x0F, 0xBA, 0x01, 0x00, 0x00, 0x00, 0xE8,
    0xF4, 0xB2, 0x01, 0x00]

theorem code_l1062c8 : ∀ x ∈ codeRange 0x1062c8 bytes_l1062c8, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x62c8 36 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1062ec : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1062ec (movzxR32M8Effect 0x1062ec 5 1 (.sib 4 none 0 (.d8 0xf))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x1062ec (LoadPre 0x1062ec (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x1062ec + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1062ec 5 1 (.sib 4 none 0 (.d8 0xf))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1062f1 (cmpR64Imm8Effect 0x1062f1 1 0x6) (EffectPart.reads (.flag .CF) [.gpr 1] []) (.flag .CF)) #v[53]
    (.letOp (n := 56) (.exec 0x1062f1 (fun s => s.RIP = 0x1062f1) (cmpR64Imm8Effect 0x1062f1 1 0x6) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 57) (.out 0x1062f5 (atFlags (condHolds 2) (setccR8Effect 0x1062f5 3 0)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 0))) #v[0, 55]
    (.letOp (n := 58) (.exec 0x1062f5 (fun s => s.RIP = 0x1062f5) (atFlags (condHolds 2) (setccR8Effect 0x1062f5 3 0)) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[0, 55]
    (.letOp (n := 59) (.out 0x1062f8 (movR8Imm8Effect 0x1062f8 2 2 0x3d) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[2]
    (.letOp (n := 60) (.exec 0x1062f8 (fun s => s.RIP = 0x1062f8) (movR8Imm8Effect 0x1062f8 2 2 0x3d) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 61) (.out 0x1062fa (shrR8ClEffect 0x1062fa 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[59, 53]
    (.letOp (n := 62) (.exec 0x1062fa (fun s => s.RIP = 0x1062fa) (shrR8ClEffect 0x1062fa 2 2) (Reg.operands [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[59, 53]
    (.letOp (n := 63) (.out 0x1062fc (testR8R8Effect 0x1062fc 2 0 2) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 2] []) (.flag .ZF)) #v[57, 61]
    (.letOp (n := 64) (.exec 0x1062fc (fun s => s.RIP = 0x1062fc) (testR8R8Effect 0x1062fc 2 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[57, 61]
    (.letOp (n := 65) (.pure (condOp 5)) #v[63]
    (.terminate (.condBr (Fin.last 65) ⟨.l10632c, RegMap.args [(0, 57), (1, 53), (2, 61), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 63), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩ ⟨.l106300, RegMap.args [(0, 57), (1, 53), (2, 61), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 63), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩))))))))))))))

def bytes_l1062ec : List UInt8 :=
  [0x0F, 0xB6, 0x4C, 0x24, 0x0F, 0x48, 0x83, 0xF9, 0x06, 0x0F, 0x92, 0xC0, 0xB2, 0x3D, 0xD2, 0xEA,
    0x84, 0xD0, 0x75, 0x2C]

theorem code_l1062ec : ∀ x ∈ codeRange 0x1062ec bytes_l1062ec, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x62ec 20 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106300 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x106300 (StorePre 0x106300 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x106300 + BitVec.ofNat 64 8)) 4) (movM32Imm32Effect 0x106300 8 (.sib 4 none 0 (.d8 0x50)) 0x3) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.out 0x106308 (leaR64Effect 0x106308 2 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 55) (.exec 0x106308 (fun s => s.RIP = 0x106308) (leaR64Effect 0x106308 2 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x10630d (movR32Imm32Effect 0x10630d 5 6 0xb) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 57) (.exec 0x10630d (fun s => s.RIP = 0x10630d) (movR32Imm32Effect 0x10630d 5 6 0xb) (Reg.operands [] [])) #v[]
    (.letOp (n := 58) (.out 0x106312 (movR64Imm32Effect 0x106312 7 0x202800) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 59) (.exec 0x106312 (fun s => s.RIP = 0x106312) (movR64Imm32Effect 0x106312 7 0x202800) (Reg.operands [] [])) #v[]
    (.letOp (n := 60) (.out 0x106319 (movR64Imm32Effect 0x106319 1 0x2027e0) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 61) (.exec 0x106319 (fun s => s.RIP = 0x106319) (movR64Imm32Effect 0x106319 1 0x2027e0) (Reg.operands [] [])) #v[]
    (.letOp (n := 62) (.out 0x106320 (movR64Imm32Effect 0x106320 8 0x202810) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 63) (.exec 0x106320 (fun s => s.RIP = 0x106320) (movR64Imm32Effect 0x106320 8 0x202810) (Reg.operands [] [])) #v[]
    (.letOp (n := 64) (.out 0x106327 (callEffect (fun _ => 0x1295a0) 0x10632c) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 65) (.exec 0x106327 (PushPre 0x106327 5) (callEffect (fun _ => 0x1295a0) 0x10632c) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.const ⟨64, 0x10632c⟩) #v[]
    (.terminate (.call ⟨.l1295a0, RegMap.args [(1, 60), (2, 54), (4, 64), (5, 5), (6, 56), (7, 58), (8, 62)] 67⟩ { target := .l10632c, kept := #v[], arity := rfl, guard := some (Fin.last 66) })))))))))))))))

def bytes_l106300 : List UInt8 :=
  [0xC7, 0x44, 0x24, 0x50, 0x03, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x54, 0x24, 0x50, 0xBE, 0x0B, 0x00,
    0x00, 0x00, 0x48, 0xC7, 0xC7, 0x00, 0x28, 0x20, 0x00, 0x48, 0xC7, 0xC1, 0xE0, 0x27, 0x20, 0x00,
    0x49, 0xC7, 0xC0, 0x10, 0x28, 0x20, 0x00, 0xE8, 0x74, 0x32, 0x02, 0x00]

theorem code_l106300 : ∀ x ∈ codeRange 0x106300 bytes_l106300, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6300 44 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10632c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10632c (movR64M64Effect 0x10632c 3 (.abs (some 1) 3 0x202548)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 1] []) (.reg (.gpr 3))) #v[1]
    (.letOp (n := 54) (.exec 0x10632c (LoadPre 0x10632c (fun s => AddrMode.addr (.abs (some 1) 3 0x202548) s (0x10632c + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10632c 3 (.abs (some 1) 3 0x202548)) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 55) (.out 0x106334 (callEffect (fun _ => 0x1084d0) 0x106339) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 56) (.exec 0x106334 (PushPre 0x106334 5) (callEffect (fun _ => 0x1084d0) 0x106339) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.const ⟨64, 0x106339⟩) #v[]
    (.terminate (.call ⟨.l1084d0, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 53), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ { target := .l106339, kept := #v[], arity := rfl, guard := some (Fin.last 57) }))))))

def bytes_l10632c : List UInt8 :=
  [0x48, 0x8B, 0x1C, 0xCD, 0x48, 0x25, 0x20, 0x00, 0xE8, 0x97, 0x21, 0x00, 0x00]

theorem code_l10632c : ∀ x ∈ codeRange 0x10632c bytes_l10632c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x632c 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106339 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106339 (movR64M64Effect 0x106339 14 (.rip 0x1f9cc0)) (EffectPart.reads (.reg (.gpr 14)) [] []) (.reg (.gpr 14))) #v[]
    (.letOp (n := 54) (.exec 0x106339 (LoadPre 0x106339 (fun s => AddrMode.addr (.rip 0x1f9cc0) s (0x106339 + BitVec.ofNat 64 7)) 8) (movR64M64Effect 0x106339 14 (.rip 0x1f9cc0)) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x106340 (movR64R64Effect 0x106340 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x106340 (fun s => s.RIP = 0x106340) (movR64R64Effect 0x106340 0 14) (Reg.operands [.gpr 14] [])) #v[53]
    (.letOp (n := 57) (.out 0x106343 (addR64R64Effect 0x106343 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[55, 3]
    (.letOp (n := 58) (.out 0x106343 (addR64R64Effect 0x106343 0 3) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 3] []) (.flag .CF)) #v[55, 3]
    (.letOp (n := 59) (.exec 0x106343 (fun s => s.RIP = 0x106343) (addR64R64Effect 0x106343 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[55, 3]
    (.letOp (n := 60) (.pure (condOp 2)) #v[58]
    (.terminate (.condBr (Fin.last 60) ⟨.l106351, RegMap.args [(0, 57), (2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (16, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩ ⟨.l106348, RegMap.args [(0, 57), (2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (16, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩)))))))))

def bytes_l106339 : List UInt8 :=
  [0x4C, 0x8B, 0x35, 0xC0, 0x9C, 0x1F, 0x00, 0x4C, 0x89, 0xF0, 0x48, 0x01, 0xD8, 0x72, 0x09]

theorem code_l106339 : ∀ x ∈ codeRange 0x106339 bytes_l106339, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6339 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106348 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106348 (cmpR64M64Effect 0x106348 0 (.rip 0x1f9cb9)) (EffectPart.reads (.flag .CF) [.gpr 0] []) (.flag .CF)) #v[0]
    (.letOp (n := 54) (.out 0x106348 (cmpR64M64Effect 0x106348 0 (.rip 0x1f9cb9)) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[0]
    (.letOp (n := 55) (.exec 0x106348 (LoadPre 0x106348 (fun s => AddrMode.addr (.rip 0x1f9cb9) s (0x106348 + BitVec.ofNat 64 7)) 8) (cmpR64M64Effect 0x106348 0 (.rip 0x1f9cb9)) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 56) (.pure (condOp 6)) #v[53, 54]
    (.terminate (.condBr (Fin.last 56) ⟨.l10635e, RegMap.args [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩ ⟨.l106351, RegMap.args [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l106348 : List UInt8 :=
  [0x48, 0x3B, 0x05, 0xB9, 0x9C, 0x1F, 0x00, 0x76, 0x0D]

theorem code_l106348 : ∀ x ∈ codeRange 0x106348 bytes_l106348, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6348 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106351 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106351 (movR32Imm32Effect 0x106351 5 7 0x1) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 54) (.exec 0x106351 (fun s => s.RIP = 0x106351) (movR32Imm32Effect 0x106351 5 7 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x106356 (movR64R64Effect 0x106356 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[3]
    (.letOp (n := 56) (.exec 0x106356 (fun s => s.RIP = 0x106356) (movR64R64Effect 0x106356 6 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 57) (.out 0x106359 (callEffect (fun _ => 0x1286fc) 0x10635e) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x106359 (PushPre 0x106359 5) (callEffect (fun _ => 0x1286fc) 0x10635e) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x10635e⟩) #v[]
    (.terminate (.call ⟨.l1286fc, RegMap.args [(2, 2), (3, 3), (4, 57), (5, 5), (6, 55), (7, 53)] 60⟩ { target := .l10635e, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l106351 : List UInt8 :=
  [0xBF, 0x01, 0x00, 0x00, 0x00, 0x48, 0x89, 0xDE, 0xE8, 0x9E, 0x23, 0x02, 0x00]

theorem code_l106351 : ∀ x ∈ codeRange 0x106351 bytes_l106351, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6351 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10635e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x10635e (StorePre 0x10635e 7 (fun s => AddrMode.addr (.rip 0x1f9c9b) s (0x10635e + BitVec.ofNat 64 7)) 8) (movM64R64Effect 0x10635e 0 (.rip 0x1f9c9b)) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 54) (.out 0x106365 (testR64R64Effect 0x106365 14 14) (EffectPart.reads (.flag .ZF) [.gpr 14, .gpr 14] []) (.flag .ZF)) #v[14, 14]
    (.letOp (n := 55) (.exec 0x106365 (fun s => s.RIP = 0x106365) (testR64R64Effect 0x106365 14 14) (Reg.operands [.gpr 14, .gpr 14] [])) #v[14, 14]
    (.letOp (n := 56) (.pure (condOp 4)) #v[54]
    (.terminate (.condBr (Fin.last 56) ⟨.l106351, RegMap.args [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩ ⟨.l10636a, RegMap.args [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l10635e : List UInt8 :=
  [0x48, 0x89, 0x05, 0x9B, 0x9C, 0x1F, 0x00, 0x4D, 0x85, 0xF6, 0x74, 0xE7]

theorem code_l10635e : ∀ x ∈ codeRange 0x10635e bytes_l10635e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x635e 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10636a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10636a (leaR64Effect 0x10636a 6 (.sib 4 none 0 (.d8 0xf))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 54) (.exec 0x10636a (fun s => s.RIP = 0x10636a) (leaR64Effect 0x10636a 6 (.sib 4 none 0 (.d8 0xf))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10636f (movR64R64Effect 0x10636f 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 56) (.exec 0x10636f (fun s => s.RIP = 0x10636f) (movR64R64Effect 0x10636f 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x106372 (movR64R64Effect 0x106372 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3] []) (.reg (.gpr 2))) #v[3]
    (.letOp (n := 58) (.exec 0x106372 (fun s => s.RIP = 0x106372) (movR64R64Effect 0x106372 2 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 59) (.out 0x106375 (callEffect (callMemPtr 0x106375 (.rip 0xfda55)) (0x106375 + BitVec.ofNat 64 (callMemLen (.rip 0xfda55)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x106375 (GoesTo (CallMemPre 0x106375 (.rip 0xfda55)) (callEffect (callMemPtr 0x106375 (.rip 0xfda55)) (0x106375 + BitVec.ofNat 64 (callMemLen (.rip 0xfda55)))) 0x12a820) (callEffect (callMemPtr 0x106375 (.rip 0xfda55)) (0x106375 + BitVec.ofNat 64 (callMemLen (.rip 0xfda55)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x10637b⟩) #v[]
    (.terminate (.call ⟨.l12a820, RegMap.args [(2, 57), (3, 3), (4, 59), (5, 5), (6, 53), (7, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l10637b, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l10636a : List UInt8 :=
  [0x48, 0x8D, 0x74, 0x24, 0x0F, 0x4C, 0x89, 0xF7, 0x48, 0x89, 0xDA, 0xFF, 0x15, 0x55, 0xDA, 0x0F,
    0x00]

theorem code_l10636a : ∀ x ∈ codeRange 0x10636a bytes_l10636a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x636a 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10637b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10637b (movR64R64Effect 0x10637b 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[14]
    (.letOp (n := 54) (.exec 0x10637b (fun s => s.RIP = 0x10637b) (movR64R64Effect 0x10637b 0 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 55) (.out 0x10637e (movR64R64Effect 0x10637e 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3] []) (.reg (.gpr 2))) #v[3]
    (.letOp (n := 56) (.exec 0x10637e (fun s => s.RIP = 0x10637e) (movR64R64Effect 0x10637e 2 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 57) (.out 0x106381 (addR64Imm32Effect 0x106381 4 0x88) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x106381 (fun s => s.RIP = 0x106381) (addR64Imm32Effect 0x106381 4 0x88) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x106388 (popR64Effect 0x106388 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[57]
    (.letOp (n := 60) (.out 0x106388 (popR64Effect 0x106388 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[57]
    (.letOp (n := 61) (.exec 0x106388 (PopPre 0x106388) (popR64Effect 0x106388 1 3) (Reg.operands [.gpr 4] [])) #v[57]
    (.letOp (n := 62) (.out 0x106389 (popR64Effect 0x106389 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[60]
    (.letOp (n := 63) (.out 0x106389 (popR64Effect 0x106389 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[60]
    (.letOp (n := 64) (.exec 0x106389 (PopPre 0x106389) (popR64Effect 0x106389 2 14) (Reg.operands [.gpr 4] [])) #v[60]
    (.letOp (n := 65) (.out 0x10638b (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[63]
    (.letOp (n := 66) (.out 0x10638b (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 67) (.exec 0x10638b (RetPre 0x10638b) (retEffect) (Reg.operands [.gpr 4] [])) #v[63]
    (.terminate (.ret (RegMap.args [(0, 53), (1, 1), (2, 55), (3, 59), (4, 66), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 62), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 68) (some ⟨65, by decide⟩)))))))))))))))))

def bytes_l10637b : List UInt8 :=
  [0x4C, 0x89, 0xF0, 0x48, 0x89, 0xDA, 0x48, 0x81, 0xC4, 0x88, 0x00, 0x00, 0x00, 0x5B, 0x41, 0x5E,
    0xC3]

theorem code_l10637b : ∀ x ∈ codeRange 0x10637b bytes_l10637b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x637b 17 (by decide +kernel)
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
    (.terminate (.br ⟨.l1065b0, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 54⟩))

def bytes_l1065ac : List UInt8 :=
  [0x0F, 0x1F, 0x40, 0x00]

theorem code_l1065ac : ∀ x ∈ codeRange 0x1065ac bytes_l1065ac, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x65ac 4 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1065b0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1065b0 (pushR64Effect 0x1065b0 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x1065b0 (PushPre 0x1065b0 1) (pushR64Effect 0x1065b0 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x1065b1 (pushR64Effect 0x1065b1 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x1065b1 (PushPre 0x1065b1 2) (pushR64Effect 0x1065b1 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x1065b3 (pushR64Effect 0x1065b3 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x1065b3 (PushPre 0x1065b3 2) (pushR64Effect 0x1065b3 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x1065b5 (pushR64Effect 0x1065b5 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x1065b5 (PushPre 0x1065b5 2) (pushR64Effect 0x1065b5 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x1065b7 (pushR64Effect 0x1065b7 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x1065b7 (PushPre 0x1065b7 2) (pushR64Effect 0x1065b7 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x1065b9 (pushR64Effect 0x1065b9 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x1065b9 (PushPre 0x1065b9 1) (pushR64Effect 0x1065b9 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x1065ba (subR64Imm8Effect 0x1065ba 4 0x18) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x1065ba (fun s => s.RIP = 0x1065ba) (subR64Imm8Effect 0x1065ba 4 0x18) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x1065be (cmpR32Imm32Effect 0x1065be 6 2 0x100) (EffectPart.reads (.flag .CF) [.gpr 2] []) (.flag .CF)) #v[2]
    (.letOp (n := 68) (.exec 0x1065be (fun s => s.RIP = 0x1065be) (cmpR32Imm32Effect 0x1065be 6 2 0x100) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 69) (.pure (condOp 3)) #v[67]
    (.terminate (.condBr (Fin.last 69) ⟨.l106764, RegMap.args [(2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (16, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 70⟩ ⟨.l1065ca, RegMap.args [(2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (16, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 70⟩))))))))))))))))))

def bytes_l1065b0 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x83, 0xEC, 0x18, 0x81, 0xFA,
    0x00, 0x01, 0x00, 0x00, 0x0F, 0x83, 0x9A, 0x01, 0x00, 0x00]

theorem code_l1065b0 : ∀ x ∈ codeRange 0x1065b0 bytes_l1065b0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x65b0 26 (by decide +kernel)
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

@[cfg_block] def b_l1067b0_2 : Block Op Label signature Reg.count 128 :=
  .letOp (n := 128) (.out 0x106841 (negR32Effect 0x106841 2 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[126]
    (.letOp (n := 129) (.exec 0x106841 (fun s => s.RIP = 0x106841) (negR32Effect 0x106841 2 1) (Reg.operands [.gpr 1] [])) #v[126]
    (.letOp (n := 130) (.out 0x106843 (andR32R32Effect 0x106843 2 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[128, 123]
    (.letOp (n := 131) (.exec 0x106843 (fun s => s.RIP = 0x106843) (andR32R32Effect 0x106843 2 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[128, 123]
    (.letOp (n := 132) (.out 0x106845 (addR32R32Effect 0x106845 2 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[94, 71]
    (.letOp (n := 133) (.exec 0x106845 (fun s => s.RIP = 0x106845) (addR32R32Effect 0x106845 2 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[94, 71]
    (.letOp (n := 134) (.out 0x106847 (addR32R32Effect 0x106847 2 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 3] []) (.reg (.gpr 2))) #v[132, 115]
    (.letOp (n := 135) (.exec 0x106847 (fun s => s.RIP = 0x106847) (addR32R32Effect 0x106847 2 2 3) (Reg.operands [.gpr 2, .gpr 3] [])) #v[132, 115]
    (.letOp (n := 136) (.out 0x106849 (addR32R32Effect 0x106849 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[134, 130]
    (.letOp (n := 137) (.exec 0x106849 (fun s => s.RIP = 0x106849) (addR32R32Effect 0x106849 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[134, 130]
    (.letOp (n := 138) (.out 0x10684b (movR32Imm32Effect 0x10684b 5 0 0x100) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 139) (.exec 0x10684b (fun s => s.RIP = 0x10684b) (movR32Imm32Effect 0x10684b 5 0 0x100) (Reg.operands [] [])) #v[]
    (.letOp (n := 140) (.out 0x106850 (subR32R32Effect 0x106850 2 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[138, 136]
    (.letOp (n := 141) (.exec 0x106850 (fun s => s.RIP = 0x106850) (subR32R32Effect 0x106850 2 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[138, 136]
    (.letOp (n := 142) (.out 0x106852 (addR64Imm8Effect 0x106852 4 0x1) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[55]
    (.letOp (n := 143) (.exec 0x106852 (fun s => s.RIP = 0x106852) (addR64Imm8Effect 0x106852 4 0x1) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 144) (.out 0x106856 (popR64Effect 0x106856 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[142]
    (.letOp (n := 145) (.out 0x106856 (popR64Effect 0x106856 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[142]
    (.letOp (n := 146) (.exec 0x106856 (PopPre 0x106856) (popR64Effect 0x106856 1 3) (Reg.operands [.gpr 4] [])) #v[142]
    (.letOp (n := 147) (.out 0x106857 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[145]
    (.letOp (n := 148) (.out 0x106857 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[145]
    (.letOp (n := 149) (.exec 0x106857 (RetPre 0x106857) (retEffect) (Reg.operands [.gpr 4] [])) #v[145]
    (.terminate (.ret (RegMap.args [(0, 140), (1, 130), (2, 136), (3, 144), (4, 148), (5, 5), (6, 123), (7, 7), (8, 119), (9, 102), (10, 96), (11, 108), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 150) (some ⟨147, by decide⟩))))))))))))))))))))))))

def bytes_l1067b0_2 : List UInt8 :=
  [0xF7, 0xD9, 0x21, 0xF1, 0x01, 0xC2, 0x01, 0xDA, 0x01, 0xCA, 0xB8, 0x00, 0x01, 0x00, 0x00, 0x29,
    0xD0, 0x48, 0x83, 0xC4, 0x01, 0x5B, 0xC3]

theorem code_l1067b0_2 : ∀ x ∈ codeRange 0x106841 bytes_l1067b0_2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6841 23 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1067b0_1 : Block Op Label signature Reg.count 90 :=
  .letOp (n := 90) (.out 0x1067f9 (movzxR32M8Effect 0x1067f9 4 2 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[55]
    (.letOp (n := 91) (.exec 0x1067f9 (LoadPre 0x1067f9 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1067f9 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x1067f9 4 2 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 92) (.out 0x1067fd (negR32Effect 0x1067fd 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[90]
    (.letOp (n := 93) (.exec 0x1067fd (fun s => s.RIP = 0x1067fd) (negR32Effect 0x1067fd 2 2) (Reg.operands [.gpr 2] [])) #v[90]
    (.letOp (n := 94) (.out 0x1067ff (andR32R32Effect 0x1067ff 3 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 10] []) (.reg (.gpr 2))) #v[92, 79]
    (.letOp (n := 95) (.exec 0x1067ff (fun s => s.RIP = 0x1067ff) (andR32R32Effect 0x1067ff 3 2 10) (Reg.operands [.gpr 2, .gpr 10] [])) #v[92, 79]
    (.letOp (n := 96) (.out 0x106802 (xorR32R32Effect 0x106802 3 10 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 10] []) (.reg (.gpr 10))) #v[79, 79]
    (.letOp (n := 97) (.exec 0x106802 (fun s => s.RIP = 0x106802) (xorR32R32Effect 0x106802 3 10 10) (Reg.operands [.gpr 10, .gpr 10] [])) #v[79, 79]
    (.letOp (n := 98) (.out 0x106805 (testR64R64Effect 0x106805 9 9) (EffectPart.reads (.flag .ZF) [.gpr 9, .gpr 9] []) (.flag .ZF)) #v[73, 73]
    (.letOp (n := 99) (.exec 0x106805 (fun s => s.RIP = 0x106805) (testR64R64Effect 0x106805 9 9) (Reg.operands [.gpr 9, .gpr 9] [])) #v[73, 73]
    (.letOp (n := 100) (.out 0x106808 (atFlags (condHolds 5) (cmovR32R32Effect 0x106808 4 8 10)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 8))) #v[88, 96, 98]
    (.letOp (n := 101) (.exec 0x106808 (fun s => s.RIP = 0x106808) (atFlags (condHolds 5) (cmovR32R32Effect 0x106808 4 8 10)) (Reg.operands [.gpr 8, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[88, 96, 98]
    (.letOp (n := 102) (.out 0x10680c (movR64M64Effect 0x10680c 9 (.base 7 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 7] []) (.reg (.gpr 9))) #v[7]
    (.letOp (n := 103) (.exec 0x10680c (LoadPre 0x10680c (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x10680c + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10680c 9 (.base 7 (.d8 0x8))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 104) (.out 0x106810 (movR32Imm32Effect 0x106810 6 11 0x7f) (EffectPart.reads (.reg (.gpr 11)) [] []) (.reg (.gpr 11))) #v[]
    (.letOp (n := 105) (.exec 0x106810 (fun s => s.RIP = 0x106810) (movR32Imm32Effect 0x106810 6 11 0x7f) (Reg.operands [] [])) #v[]
    (.letOp (n := 106) (.out 0x106816 (bsrR64R64Effect 0x106816 4 11 9) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 9] []) (.reg (.gpr 11))) #v[104, 102]
    (.letOp (n := 107) (.exec 0x106816 (fun s => s.RIP = 0x106816) (bsrR64R64Effect 0x106816 4 11 9) (Reg.operands [.gpr 11, .gpr 9] [])) #v[104, 102]
    (.letOp (n := 108) (.out 0x10681a (xorR32Imm8Effect 0x10681a 4 11 0x3f) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11] []) (.reg (.gpr 11))) #v[106]
    (.letOp (n := 109) (.exec 0x10681a (fun s => s.RIP = 0x10681a) (xorR32Imm8Effect 0x10681a 4 11 0x3f) (Reg.operands [.gpr 11] [])) #v[106]
    (.letOp (n := 110) (.exec 0x10681e (StorePre 0x10681e 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10681e + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10681e 4 8 (.sib 4 none 0 .none)) (Reg.operands [.gpr 8, .gpr 4] [])) #v[100, 55]
    (.letOp (n := 111) (.out 0x106822 (movzxR32M8Effect 0x106822 4 3 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[55]
    (.letOp (n := 112) (.exec 0x106822 (LoadPre 0x106822 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x106822 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x106822 4 3 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 113) (.out 0x106826 (negR32Effect 0x106826 2 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[111]
    (.letOp (n := 114) (.exec 0x106826 (fun s => s.RIP = 0x106826) (negR32Effect 0x106826 2 3) (Reg.operands [.gpr 3] [])) #v[111]
    (.letOp (n := 115) (.out 0x106828 (andR32R32Effect 0x106828 3 3 11) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 11] []) (.reg (.gpr 3))) #v[113, 108]
    (.letOp (n := 116) (.exec 0x106828 (fun s => s.RIP = 0x106828) (andR32R32Effect 0x106828 3 3 11) (Reg.operands [.gpr 3, .gpr 11] [])) #v[113, 108]
    (.letOp (n := 117) (.out 0x10682b (testR64R64Effect 0x10682b 9 9) (EffectPart.reads (.flag .ZF) [.gpr 9, .gpr 9] []) (.flag .ZF)) #v[102, 102]
    (.letOp (n := 118) (.exec 0x10682b (fun s => s.RIP = 0x10682b) (testR64R64Effect 0x10682b 9 9) (Reg.operands [.gpr 9, .gpr 9] [])) #v[102, 102]
    (.letOp (n := 119) (.out 0x10682e (atFlags (condHolds 5) (cmovR32R32Effect 0x10682e 4 8 10)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 8))) #v[100, 96, 117]
    (.letOp (n := 120) (.exec 0x10682e (fun s => s.RIP = 0x10682e) (atFlags (condHolds 5) (cmovR32R32Effect 0x10682e 4 8 10)) (Reg.operands [.gpr 8, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[100, 96, 117]
    (.letOp (n := 121) (.out 0x106832 (bsrR64M64Effect 0x106832 4 6 (.base 7 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7] []) (.reg (.gpr 6))) #v[86, 7]
    (.letOp (n := 122) (.exec 0x106832 (LoadPre 0x106832 (fun s => AddrMode.addr (.base 7 .none) s (0x106832 + BitVec.ofNat 64 4)) 8) (bsrR64M64Effect 0x106832 4 6 (.base 7 .none)) (Reg.operands [.gpr 6, .gpr 7] [])) #v[86, 7]
    (.letOp (n := 123) (.out 0x106836 (xorR32Imm8Effect 0x106836 3 6 0x3f) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[121]
    (.letOp (n := 124) (.exec 0x106836 (fun s => s.RIP = 0x106836) (xorR32Imm8Effect 0x106836 3 6 0x3f) (Reg.operands [.gpr 6] [])) #v[121]
    (.letOp (n := 125) (.exec 0x106839 (StorePre 0x106839 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x106839 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x106839 4 8 (.sib 4 none 0 .none)) (Reg.operands [.gpr 8, .gpr 4] [])) #v[119, 55]
    (.letOp (n := 126) (.out 0x10683d (movzxR32M8Effect 0x10683d 4 1 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[55]
    (.letOp (n := 127) (.exec 0x10683d (LoadPre 0x10683d (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10683d + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10683d 4 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[55]
    (b_l1067b0_2))))))))))))))))))))))))))))))))))))))

def bytes_l1067b0_1 : List UInt8 :=
  [0x0F, 0xB6, 0x14, 0x24, 0xF7, 0xDA, 0x44, 0x21, 0xD2, 0x45, 0x31, 0xD2, 0x4D, 0x85, 0xC9, 0x45,
    0x0F, 0x45, 0xC2, 0x4C, 0x8B, 0x4F, 0x08, 0x41, 0xBB, 0x7F, 0x00, 0x00, 0x00, 0x4D, 0x0F, 0xBD,
    0xD9, 0x41, 0x83, 0xF3, 0x3F, 0x44, 0x88, 0x04, 0x24, 0x0F, 0xB6, 0x1C, 0x24, 0xF7, 0xDB, 0x44,
    0x21, 0xDB, 0x4D, 0x85, 0xC9, 0x45, 0x0F, 0x45, 0xC2, 0x48, 0x0F, 0xBD, 0x37, 0x83, 0xF6, 0x3F,
    0x44, 0x88, 0x04, 0x24, 0x0F, 0xB6, 0x0C, 0x24] ++ bytes_l1067b0_2

theorem code_l1067b0_1 : ∀ x ∈ codeRange 0x1067f9 bytes_l1067b0_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x67f9 72 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1067b0_2

@[cfg_block] def b_l1067b0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1067b0 (pushR64Effect 0x1067b0 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[4, 3]
    (.letOp (n := 54) (.exec 0x1067b0 (PushPre 0x1067b0 1) (pushR64Effect 0x1067b0 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[4, 3]
    (.letOp (n := 55) (.out 0x1067b1 (subR64Imm8Effect 0x1067b1 4 0x1) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[53]
    (.letOp (n := 56) (.exec 0x1067b1 (fun s => s.RIP = 0x1067b1) (subR64Imm8Effect 0x1067b1 4 0x1) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 57) (.out 0x1067b5 (movR64M64Effect 0x1067b5 2 (.base 7 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7] []) (.reg (.gpr 2))) #v[7]
    (.letOp (n := 58) (.exec 0x1067b5 (LoadPre 0x1067b5 (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x1067b5 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1067b5 2 (.base 7 (.d8 0x18))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 59) (.out 0x1067b9 (movR32Imm32Effect 0x1067b9 5 6 0x7f) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 60) (.exec 0x1067b9 (fun s => s.RIP = 0x1067b9) (movR32Imm32Effect 0x1067b9 5 6 0x7f) (Reg.operands [] [])) #v[]
    (.letOp (n := 61) (.out 0x1067be (bsrR64R64Effect 0x1067be 4 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[59, 57]
    (.letOp (n := 62) (.exec 0x1067be (fun s => s.RIP = 0x1067be) (bsrR64R64Effect 0x1067be 4 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[59, 57]
    (.letOp (n := 63) (.out 0x1067c2 (xorR32Imm8Effect 0x1067c2 3 6 0x3f) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[61]
    (.letOp (n := 64) (.exec 0x1067c2 (fun s => s.RIP = 0x1067c2) (xorR32Imm8Effect 0x1067c2 3 6 0x3f) (Reg.operands [.gpr 6] [])) #v[61]
    (.letOp (n := 65) (.exec 0x1067c5 (StorePre 0x1067c5 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1067c5 + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x1067c5 (.sib 4 none 0 .none) 0x1) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 66) (.exec 0x1067c9 (fun s => s.RIP = 0x1067c9) (movR64R64Effect 0x1067c9 1 4) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 67) (.out 0x1067cc (movzxR32M8Effect 0x1067cc 4 0 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[55]
    (.letOp (n := 68) (.exec 0x1067cc (LoadPre 0x1067cc (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1067cc + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x1067cc 4 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 69) (.out 0x1067d0 (negR32Effect 0x1067d0 2 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[67]
    (.letOp (n := 70) (.exec 0x1067d0 (fun s => s.RIP = 0x1067d0) (negR32Effect 0x1067d0 2 0) (Reg.operands [.gpr 0] [])) #v[67]
    (.letOp (n := 71) (.out 0x1067d2 (andR32R32Effect 0x1067d2 2 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[69, 63]
    (.letOp (n := 72) (.exec 0x1067d2 (fun s => s.RIP = 0x1067d2) (andR32R32Effect 0x1067d2 2 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[69, 63]
    (.letOp (n := 73) (.out 0x1067d4 (movR64M64Effect 0x1067d4 9 (.base 7 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 7] []) (.reg (.gpr 9))) #v[7]
    (.letOp (n := 74) (.exec 0x1067d4 (LoadPre 0x1067d4 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x1067d4 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1067d4 9 (.base 7 (.d8 0x10))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 75) (.out 0x1067d8 (movR32Imm32Effect 0x1067d8 6 10 0x7f) (EffectPart.reads (.reg (.gpr 10)) [] []) (.reg (.gpr 10))) #v[]
    (.letOp (n := 76) (.exec 0x1067d8 (fun s => s.RIP = 0x1067d8) (movR32Imm32Effect 0x1067d8 6 10 0x7f) (Reg.operands [] [])) #v[]
    (.letOp (n := 77) (.out 0x1067de (bsrR64R64Effect 0x1067de 4 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9] []) (.reg (.gpr 10))) #v[75, 73]
    (.letOp (n := 78) (.exec 0x1067de (fun s => s.RIP = 0x1067de) (bsrR64R64Effect 0x1067de 4 10 9) (Reg.operands [.gpr 10, .gpr 9] [])) #v[75, 73]
    (.letOp (n := 79) (.out 0x1067e2 (xorR32Imm8Effect 0x1067e2 4 10 0x3f) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[77]
    (.letOp (n := 80) (.exec 0x1067e2 (fun s => s.RIP = 0x1067e2) (xorR32Imm8Effect 0x1067e2 4 10 0x3f) (Reg.operands [.gpr 10] [])) #v[77]
    (.letOp (n := 81) (.out 0x1067e6 (xorR32R32Effect 0x1067e6 3 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 8] []) (.reg (.gpr 8))) #v[8, 8]
    (.letOp (n := 82) (.exec 0x1067e6 (fun s => s.RIP = 0x1067e6) (xorR32R32Effect 0x1067e6 3 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[8, 8]
    (.letOp (n := 83) (.out 0x1067e9 (testR64R64Effect 0x1067e9 2 2) (EffectPart.reads (.flag .ZF) [.gpr 2, .gpr 2] []) (.flag .ZF)) #v[57, 57]
    (.letOp (n := 84) (.exec 0x1067e9 (fun s => s.RIP = 0x1067e9) (testR64R64Effect 0x1067e9 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[57, 57]
    (.letOp (n := 85) (.exec 0x1067ec (StorePre 0x1067ec 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1067ec + BitVec.ofNat 64 4)) 1) (atFlags (condHolds 4) (setccM8Effect 0x1067ec 4 (.sib 4 none 0 .none))) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.ZF])) #v[55, 83]
    (.letOp (n := 86) (.out 0x1067f0 (movR32Imm32Effect 0x1067f0 5 6 0x7f) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 87) (.exec 0x1067f0 (fun s => s.RIP = 0x1067f0) (movR32Imm32Effect 0x1067f0 5 6 0x7f) (Reg.operands [] [])) #v[]
    (.letOp (n := 88) (.out 0x1067f5 (atFlags (condHolds 4) (setccR8Effect 0x1067f5 4 8)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 8))) #v[81, 83]
    (.letOp (n := 89) (.exec 0x1067f5 (fun s => s.RIP = 0x1067f5) (atFlags (condHolds 4) (setccR8Effect 0x1067f5 4 8)) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[81, 83]
    (b_l1067b0_1)))))))))))))))))))))))))))))))))))))

def bytes_l1067b0 : List UInt8 :=
  [0x53, 0x48, 0x83, 0xEC, 0x01, 0x48, 0x8B, 0x57, 0x18, 0xBE, 0x7F, 0x00, 0x00, 0x00, 0x48, 0x0F,
    0xBD, 0xF2, 0x83, 0xF6, 0x3F, 0xC6, 0x04, 0x24, 0x01, 0x48, 0x89, 0xE1, 0x0F, 0xB6, 0x04, 0x24,
    0xF7, 0xD8, 0x21, 0xF0, 0x4C, 0x8B, 0x4F, 0x10, 0x41, 0xBA, 0x7F, 0x00, 0x00, 0x00, 0x4D, 0x0F,
    0xBD, 0xD1, 0x41, 0x83, 0xF2, 0x3F, 0x45, 0x31, 0xC0, 0x48, 0x85, 0xD2, 0x0F, 0x94, 0x04, 0x24,
    0xBE, 0x7F, 0x00, 0x00, 0x00, 0x41, 0x0F, 0x94, 0xC0] ++ bytes_l1067b0_1

theorem code_l1067b0 : ∀ x ∈ codeRange 0x1067b0 bytes_l1067b0, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x67b0 73 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1067b0_1

@[cfg_block] def b_l106860 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106860 (pushR64Effect 0x106860 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[4, 3]
    (.letOp (n := 54) (.exec 0x106860 (PushPre 0x106860 1) (pushR64Effect 0x106860 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[4, 3]
    (.letOp (n := 55) (.out 0x106861 (subR64Imm8Effect 0x106861 4 0x40) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[53]
    (.letOp (n := 56) (.exec 0x106861 (fun s => s.RIP = 0x106861) (subR64Imm8Effect 0x106861 4 0x40) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 57) (.out 0x106865 (movR64R64Effect 0x106865 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 58) (.exec 0x106865 (fun s => s.RIP = 0x106865) (movR64R64Effect 0x106865 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 59) (.out 0x106868 (leaR64Effect 0x106868 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[55]
    (.letOp (n := 60) (.exec 0x106868 (fun s => s.RIP = 0x106868) (leaR64Effect 0x106868 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 61) (.out 0x10686d (movR32Imm32Effect 0x10686d 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 62) (.exec 0x10686d (fun s => s.RIP = 0x10686d) (movR32Imm32Effect 0x10686d 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 63) (.out 0x106872 (callEffect (fun _ => 0x127b80) 0x106877) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[55]
    (.letOp (n := 64) (.exec 0x106872 (PushPre 0x106872 5) (callEffect (fun _ => 0x127b80) 0x106877) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 65) (.const ⟨64, 0x106877⟩) #v[]
    (.terminate (.call ⟨.l127b80, RegMap.args [(2, 61), (3, 57), (4, 63), (5, 5), (6, 6), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩ { target := .l106877, kept := #v[], arity := rfl, guard := some (Fin.last 65) }))))))))))))))

def bytes_l106860 : List UInt8 :=
  [0x53, 0x48, 0x83, 0xEC, 0x40, 0x48, 0x89, 0xFB, 0x48, 0x8D, 0x7C, 0x24, 0x08, 0xBA, 0x01, 0x00,
    0x00, 0x00, 0xE8, 0x09, 0x13, 0x02, 0x00]

theorem code_l106860 : ∀ x ∈ codeRange 0x106860 bytes_l106860, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6860 23 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106877 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106877 (movR32M32LowEffect 0x106877 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x106877 (LoadPre 0x106877 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x106877 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x106877 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10687b (cmpR32Imm8Effect 0x10687b 3 0 0x2) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x10687b (fun s => s.RIP = 0x10687b) (cmpR32Imm8Effect 0x10687b 3 0 0x2) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l106898, RegMap.args [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l106880, RegMap.args [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l106877 : List UInt8 :=
  [0x8B, 0x44, 0x24, 0x08, 0x83, 0xF8, 0x02, 0x75, 0x18]

theorem code_l106877 : ∀ x ∈ codeRange 0x106877 bytes_l106877, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6877 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106880 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106880 (movR64M64Effect 0x106880 6 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 54) (.exec 0x106880 (LoadPre 0x106880 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x106880 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106880 6 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x106885 (cmpR64Imm8Effect 0x106885 6 0x1) (EffectPart.reads (.flag .ZF) [.gpr 6] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x106885 (fun s => s.RIP = 0x106885) (cmpR64Imm8Effect 0x106885 6 0x1) (Reg.operands [.gpr 6] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l1068e0, RegMap.args [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l10688b, RegMap.args [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l106880 : List UInt8 :=
  [0x48, 0x8B, 0x74, 0x24, 0x18, 0x48, 0x83, 0xFE, 0x01, 0x75, 0x55]

theorem code_l106880 : ∀ x ∈ codeRange 0x106880 bytes_l106880, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6880 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10688b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10688b (movR64M64Effect 0x10688b 1 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x10688b (LoadPre 0x10688b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10688b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10688b 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x106890 (movzxR32M8Effect 0x106890 3 1 (.base 1 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 56) (.exec 0x106890 (LoadPre 0x106890 (fun s => AddrMode.addr (.base 1 .none) s (0x106890 + BitVec.ofNat 64 3)) 1) (movzxR32M8Effect 0x106890 3 1 (.base 1 .none)) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 57) (.exec 0x106893 (StorePre 0x106893 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x106893 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x106893 3 1 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[55, 3]
    (.terminate (.br ⟨.l1068d5, RegMap.args [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l10688b : List UInt8 :=
  [0x48, 0x8B, 0x4C, 0x24, 0x10, 0x0F, 0xB6, 0x09, 0x88, 0x4B, 0x04, 0xEB, 0x3D]

theorem code_l10688b : ∀ x ∈ codeRange 0x10688b bytes_l10688b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x688b 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106898 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106898 (movR32M32LowEffect 0x106898 1 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x106898 (LoadPre 0x106898 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x106898 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x106898 1 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10689c (movR64M64Effect 0x10689c 2 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 56) (.exec 0x10689c (LoadPre 0x10689c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10689c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10689c 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1068a1 (movR64M64Effect 0x1068a1 6 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 58) (.exec 0x1068a1 (LoadPre 0x1068a1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1068a1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1068a1 6 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x1068a6 (movR64M64Effect 0x1068a6 7 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 60) (.exec 0x1068a6 (LoadPre 0x1068a6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1068a6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1068a6 7 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x1068ab (StorePre 0x1068ab 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x1068ab + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1068ab 7 (.base 3 (.d8 0x30))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[59, 3]
    (.letOp (n := 62) (.out 0x1068af (movR64M64Effect 0x1068af 7 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 63) (.exec 0x1068af (LoadPre 0x1068af (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1068af + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1068af 7 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x1068b4 (StorePre 0x1068b4 4 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x1068b4 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1068b4 7 (.base 3 (.d8 0x28))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[62, 3]
    (.letOp (n := 65) (.out 0x1068b8 (movR64M64Effect 0x1068b8 7 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 66) (.exec 0x1068b8 (LoadPre 0x1068b8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1068b8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1068b8 7 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x1068bd (StorePre 0x1068bd 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x1068bd + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1068bd 7 (.base 3 (.d8 0x20))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[65, 3]
    (.letOp (n := 68) (.out 0x1068c1 (movR64M64Effect 0x1068c1 7 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 69) (.exec 0x1068c1 (LoadPre 0x1068c1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1068c1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1068c1 7 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.exec 0x1068c6 (StorePre 0x1068c6 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x1068c6 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1068c6 7 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[68, 3]
    (.letOp (n := 71) (.exec 0x1068ca (StorePre 0x1068ca 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x1068ca + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x1068ca 1 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[53, 3]
    (.letOp (n := 72) (.exec 0x1068cd (StorePre 0x1068cd 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x1068cd + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1068cd 2 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[55, 3]
    (.letOp (n := 73) (.exec 0x1068d1 (StorePre 0x1068d1 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x1068d1 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1068d1 6 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[57, 3]
    (.terminate (.br ⟨.l1068d5, RegMap.args [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 74⟩))))))))))))))))))))))

def bytes_l106898 : List UInt8 :=
  [0x8B, 0x4C, 0x24, 0x0C, 0x48, 0x8B, 0x54, 0x24, 0x10, 0x48, 0x8B, 0x74, 0x24, 0x18, 0x48, 0x8B,
    0x7C, 0x24, 0x38, 0x48, 0x89, 0x7B, 0x30, 0x48, 0x8B, 0x7C, 0x24, 0x30, 0x48, 0x89, 0x7B, 0x28,
    0x48, 0x8B, 0x7C, 0x24, 0x28, 0x48, 0x89, 0x7B, 0x20, 0x48, 0x8B, 0x7C, 0x24, 0x20, 0x48, 0x89,
    0x7B, 0x18, 0x89, 0x4B, 0x04, 0x48, 0x89, 0x53, 0x08, 0x48, 0x89, 0x73, 0x10]

theorem code_l106898 : ∀ x ∈ codeRange 0x106898 bytes_l106898, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6898 61 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1068d5 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1068d5 (StorePre 0x1068d5 2 (fun s => AddrMode.addr (.base 3 .none) s (0x1068d5 + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x1068d5 0 (.base 3 .none)) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (.letOp (n := 54) (.out 0x1068d7 (movR64R64Effect 0x1068d7 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 55) (.exec 0x1068d7 (fun s => s.RIP = 0x1068d7) (movR64R64Effect 0x1068d7 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 56) (.out 0x1068da (addR64Imm8Effect 0x1068da 4 0x40) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 57) (.exec 0x1068da (fun s => s.RIP = 0x1068da) (addR64Imm8Effect 0x1068da 4 0x40) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.out 0x1068de (popR64Effect 0x1068de 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[56]
    (.letOp (n := 59) (.out 0x1068de (popR64Effect 0x1068de 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[56]
    (.letOp (n := 60) (.exec 0x1068de (PopPre 0x1068de) (popR64Effect 0x1068de 1 3) (Reg.operands [.gpr 4] [])) #v[56]
    (.letOp (n := 61) (.out 0x1068df (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[59]
    (.letOp (n := 62) (.out 0x1068df (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 63) (.exec 0x1068df (RetPre 0x1068df) (retEffect) (Reg.operands [.gpr 4] [])) #v[59]
    (.terminate (.ret (RegMap.args [(0, 54), (1, 1), (2, 2), (3, 58), (4, 62), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 64) (some ⟨61, by decide⟩)))))))))))))

def bytes_l1068d5 : List UInt8 :=
  [0x89, 0x03, 0x48, 0x89, 0xD8, 0x48, 0x83, 0xC4, 0x40, 0x5B, 0xC3]

theorem code_l1068d5 : ∀ x ∈ codeRange 0x1068d5 bytes_l1068d5, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x68d5 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1068e0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1068e0 (movR32Imm32Effect 0x1068e0 5 7 0x1) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 54) (.exec 0x1068e0 (fun s => s.RIP = 0x1068e0) (movR32Imm32Effect 0x1068e0 5 7 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x1068e5 (movR64Imm32Effect 0x1068e5 2 0x202530) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 56) (.exec 0x1068e5 (fun s => s.RIP = 0x1068e5) (movR64Imm32Effect 0x1068e5 2 0x202530) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x1068ec (callEffect (fun _ => 0x129c90) 0x1068f1) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x1068ec (PushPre 0x1068ec 5) (callEffect (fun _ => 0x129c90) 0x1068f1) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x1068f1⟩) #v[]
    (.terminate (.call ⟨.l129c90, RegMap.args [(2, 55), (4, 57), (5, 5), (6, 6), (7, 53)] 60⟩ { target := .l1068f1, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l1068e0 : List UInt8 :=
  [0xBF, 0x01, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC2, 0x30, 0x25, 0x20, 0x00, 0xE8, 0x9F, 0x33, 0x02,
    0x00]

theorem code_l1068e0 : ∀ x ∈ codeRange 0x1068e0 bytes_l1068e0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x68e0 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1068f1 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1068f1 (fun s => s.RIP = 0x1068f1) (fun _ => nopEffect 0x1068f1 10) (Reg.operands [] [])) #v[]
    (.letOp (n := 54) (.exec 0x1068fb (fun s => s.RIP = 0x1068fb) (fun _ => nopEffect 0x1068fb 5) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l106900, RegMap.args [(3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l1068f1 : List UInt8 :=
  [0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00, 0x0F, 0x1F, 0x44, 0x00, 0x00]

theorem code_l1068f1 : ∀ x ∈ codeRange 0x1068f1 bytes_l1068f1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x68f1 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106900 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106900 (pushR64Effect 0x106900 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x106900 (PushPre 0x106900 1) (pushR64Effect 0x106900 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x106901 (pushR64Effect 0x106901 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[53, 14]
    (.letOp (n := 56) (.exec 0x106901 (PushPre 0x106901 2) (pushR64Effect 0x106901 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 57) (.out 0x106903 (pushR64Effect 0x106903 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[55, 3]
    (.letOp (n := 58) (.exec 0x106903 (PushPre 0x106903 1) (pushR64Effect 0x106903 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[55, 3]
    (.letOp (n := 59) (.out 0x106904 (subR64Imm8Effect 0x106904 4 0x40) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[57]
    (.letOp (n := 60) (.exec 0x106904 (fun s => s.RIP = 0x106904) (subR64Imm8Effect 0x106904 4 0x40) (Reg.operands [.gpr 4] [])) #v[57]
    (.letOp (n := 61) (.out 0x106908 (movR64R64Effect 0x106908 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 6] []) (.reg (.gpr 14))) #v[6]
    (.letOp (n := 62) (.exec 0x106908 (fun s => s.RIP = 0x106908) (movR64R64Effect 0x106908 14 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 63) (.out 0x10690b (movR64R64Effect 0x10690b 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 64) (.exec 0x10690b (fun s => s.RIP = 0x10690b) (movR64R64Effect 0x10690b 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 65) (.out 0x10690e (leaR64Effect 0x10690e 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[59]
    (.letOp (n := 66) (.exec 0x10690e (fun s => s.RIP = 0x10690e) (leaR64Effect 0x10690e 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 67) (.out 0x106913 (movR32Imm32Effect 0x106913 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 68) (.exec 0x106913 (fun s => s.RIP = 0x106913) (movR32Imm32Effect 0x106913 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 69) (.out 0x106918 (callEffect (fun _ => 0x127b80) 0x10691d) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 70) (.exec 0x106918 (PushPre 0x106918 5) (callEffect (fun _ => 0x127b80) 0x10691d) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 71) (.const ⟨64, 0x10691d⟩) #v[]
    (.terminate (.call ⟨.l127b80, RegMap.args [(2, 67), (3, 63), (4, 69), (5, 5), (6, 6), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩ { target := .l10691d, kept := #v[], arity := rfl, guard := some (Fin.last 71) }))))))))))))))))))))

def bytes_l106900 : List UInt8 :=
  [0x55, 0x41, 0x56, 0x53, 0x48, 0x83, 0xEC, 0x40, 0x49, 0x89, 0xF6, 0x48, 0x89, 0xFB, 0x48, 0x8D,
    0x7C, 0x24, 0x08, 0xBA, 0x01, 0x00, 0x00, 0x00, 0xE8, 0x63, 0x12, 0x02, 0x00]

theorem code_l106900 : ∀ x ∈ codeRange 0x106900 bytes_l106900, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6900 29 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10691d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10691d (movR32M32LowEffect 0x10691d 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x10691d (LoadPre 0x10691d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10691d + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x10691d 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x106921 (cmpR32Imm8Effect 0x106921 3 0 0x2) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x106921 (fun s => s.RIP = 0x106921) (cmpR32Imm8Effect 0x106921 3 0 0x2) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l106958, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l106926, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l10691d : List UInt8 :=
  [0x8B, 0x44, 0x24, 0x08, 0x83, 0xF8, 0x02, 0x75, 0x32]

theorem code_l10691d : ∀ x ∈ codeRange 0x10691d bytes_l10691d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x691d 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106926 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106926 (movR64M64Effect 0x106926 6 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 54) (.exec 0x106926 (LoadPre 0x106926 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x106926 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106926 6 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10692b (cmpR64Imm8Effect 0x10692b 6 0x1) (EffectPart.reads (.flag .ZF) [.gpr 6] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x10692b (fun s => s.RIP = 0x10692b) (cmpR64Imm8Effect 0x10692b 6 0x1) (Reg.operands [.gpr 6] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l106b45, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l106935, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l106926 : List UInt8 :=
  [0x48, 0x8B, 0x74, 0x24, 0x18, 0x48, 0x83, 0xFE, 0x01, 0x0F, 0x85, 0x10, 0x02, 0x00, 0x00]

theorem code_l106926 : ∀ x ∈ codeRange 0x106926 bytes_l106926, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6926 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106935 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106935 (movR64M64Effect 0x106935 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x106935 (LoadPre 0x106935 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x106935 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106935 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10693a (movzxR32M8Effect 0x10693a 3 5 (.base 0 .none)) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[53]
    (.letOp (n := 56) (.exec 0x10693a (LoadPre 0x10693a (fun s => AddrMode.addr (.base 0 .none) s (0x10693a + BitVec.ofNat 64 3)) 1) (movzxR32M8Effect 0x10693a 3 5 (.base 0 .none)) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x10693d (movR32R32Effect 0x10693d 2 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[55]
    (.letOp (n := 58) (.exec 0x10693d (fun s => s.RIP = 0x10693d) (movR32R32Effect 0x10693d 2 0 5) (Reg.operands [.gpr 5] [])) #v[55]
    (.letOp (n := 59) (.out 0x10693f (decR32Effect 0x10693f 2 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[57]
    (.letOp (n := 60) (.exec 0x10693f (fun s => s.RIP = 0x10693f) (decR32Effect 0x10693f 2 0) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[57]
    (.letOp (n := 61) (.out 0x106941 (cmpR32Imm8Effect 0x106941 3 0 0x30) (EffectPart.reads (.flag .CF) [.gpr 0] []) (.flag .CF)) #v[59]
    (.letOp (n := 62) (.out 0x106941 (cmpR32Imm8Effect 0x106941 3 0 0x30) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[59]
    (.letOp (n := 63) (.exec 0x106941 (fun s => s.RIP = 0x106941) (cmpR32Imm8Effect 0x106941 3 0 0x30) (Reg.operands [.gpr 0] [])) #v[59]
    (.letOp (n := 64) (.pure (condOp 7)) #v[61, 62]
    (.terminate (.condBr (Fin.last 64) ⟨.l1069fd, RegMap.args [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 61), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)] 65⟩ ⟨.l10694a, RegMap.args [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 61), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)] 65⟩)))))))))))))

def bytes_l106935 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x10, 0x0F, 0xB6, 0x28, 0x89, 0xE8, 0xFF, 0xC8, 0x83, 0xF8, 0x30, 0x0F,
    0x87, 0xB3, 0x00, 0x00, 0x00]

theorem code_l106935 : ∀ x ∈ codeRange 0x106935 bytes_l106935, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6935 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10694a : Block Op Label signature Reg.count 53 :=
  cutBlock 0x10694a

def bytes_l10694a : List UInt8 :=
  [0xFF, 0x24, 0xC5, 0x78, 0x25, 0x20, 0x00]

theorem code_l10694a : ∀ x ∈ codeRange 0x10694a bytes_l10694a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x694a 7 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106958_1 : Block Op Label signature Reg.count 84 :=
  .letOp (n := 84) (.exec 0x1069a8 (StorePre 0x1069a8 4 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x1069a8 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1069a8 4 7 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[71, 3]
    (.terminate (.br ⟨.l106a4f, RegMap.args [(0, 0), (1, 77), (2, 55), (3, 3), (4, 4), (6, 57), (7, 71), (8, 75), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 85⟩))

def bytes_l106958_1 : List UInt8 :=
  [0x40, 0x88, 0x7B, 0x04, 0xE9, 0x9E, 0x00, 0x00, 0x00]

theorem code_l106958_1 : ∀ x ∈ codeRange 0x1069a8 bytes_l106958_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x69a8 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106958 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106958 (movR32M32LowEffect 0x106958 1 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x106958 (LoadPre 0x106958 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x106958 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x106958 1 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10695c (movR64M64Effect 0x10695c 2 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 56) (.exec 0x10695c (LoadPre 0x10695c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10695c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10695c 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x106961 (movR64M64Effect 0x106961 6 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 58) (.exec 0x106961 (LoadPre 0x106961 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x106961 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106961 6 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x106966 (movR64M64Effect 0x106966 7 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 60) (.exec 0x106966 (LoadPre 0x106966 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x106966 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106966 7 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x10696b (StorePre 0x10696b 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x10696b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10696b 7 (.base 3 (.d8 0x30))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[59, 3]
    (.letOp (n := 62) (.out 0x10696f (movR64M64Effect 0x10696f 7 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 63) (.exec 0x10696f (LoadPre 0x10696f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10696f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10696f 7 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x106974 (StorePre 0x106974 4 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x106974 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x106974 7 (.base 3 (.d8 0x28))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[62, 3]
    (.letOp (n := 65) (.out 0x106978 (movR64M64Effect 0x106978 7 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 66) (.exec 0x106978 (LoadPre 0x106978 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x106978 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106978 7 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x10697d (StorePre 0x10697d 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x10697d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10697d 7 (.base 3 (.d8 0x20))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[65, 3]
    (.letOp (n := 68) (.out 0x106981 (movR64M64Effect 0x106981 7 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 69) (.exec 0x106981 (LoadPre 0x106981 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x106981 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106981 7 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.exec 0x106986 (StorePre 0x106986 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x106986 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x106986 7 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[68, 3]
    (.letOp (n := 71) (.out 0x10698a (movR32R32Effect 0x10698a 2 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 1] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 72) (.exec 0x10698a (fun s => s.RIP = 0x10698a) (movR32R32Effect 0x10698a 2 7 1) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 73) (.out 0x10698c (movR32R32Effect 0x10698c 3 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 1] []) (.reg (.gpr 8))) #v[53]
    (.letOp (n := 74) (.exec 0x10698c (fun s => s.RIP = 0x10698c) (movR32R32Effect 0x10698c 3 8 1) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 75) (.out 0x10698f (shrR32Effect 0x10698f 4 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[73]
    (.letOp (n := 76) (.exec 0x10698f (fun s => s.RIP = 0x10698f) (shrR32Effect 0x10698f 4 8 8) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[73]
    (.letOp (n := 77) (.out 0x106993 (shrR32Effect 0x106993 3 1 24) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 78) (.exec 0x106993 (fun s => s.RIP = 0x106993) (shrR32Effect 0x106993 3 1 24) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 79) (.exec 0x106996 (StorePre 0x106996 3 (fun s => AddrMode.addr (.base 3 (.d8 0x7)) s (0x106996 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x106996 3 1 (.base 3 (.d8 0x7))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[77, 3]
    (.letOp (n := 80) (.exec 0x106999 (StorePre 0x106999 5 (fun s => AddrMode.addr (.base 3 (.d8 0x5)) s (0x106999 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x106999 5 8 (.base 3 (.d8 0x5))) (Reg.operands [.gpr 8, .gpr 3] [])) #v[75, 3]
    (.letOp (n := 81) (.exec 0x10699e (StorePre 0x10699e 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x10699e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10699e 2 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[55, 3]
    (.letOp (n := 82) (.exec 0x1069a2 (StorePre 0x1069a2 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x1069a2 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1069a2 6 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[57, 3]
    (.letOp (n := 83) (.exec 0x1069a6 (StorePre 0x1069a6 2 (fun s => AddrMode.addr (.base 3 .none) s (0x1069a6 + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x1069a6 0 (.base 3 .none)) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (b_l106958_1)))))))))))))))))))))))))))))))

def bytes_l106958 : List UInt8 :=
  [0x8B, 0x4C, 0x24, 0x0C, 0x48, 0x8B, 0x54, 0x24, 0x10, 0x48, 0x8B, 0x74, 0x24, 0x18, 0x48, 0x8B,
    0x7C, 0x24, 0x38, 0x48, 0x89, 0x7B, 0x30, 0x48, 0x8B, 0x7C, 0x24, 0x30, 0x48, 0x89, 0x7B, 0x28,
    0x48, 0x8B, 0x7C, 0x24, 0x28, 0x48, 0x89, 0x7B, 0x20, 0x48, 0x8B, 0x7C, 0x24, 0x20, 0x48, 0x89,
    0x7B, 0x18, 0x89, 0xCF, 0x41, 0x89, 0xC8, 0x41, 0xC1, 0xE8, 0x08, 0xC1, 0xE9, 0x18, 0x88, 0x4B,
    0x07, 0x66, 0x44, 0x89, 0x43, 0x05, 0x48, 0x89, 0x53, 0x08, 0x48, 0x89, 0x73, 0x10, 0x89, 0x03] ++ bytes_l106958_1

theorem code_l106958 : ∀ x ∈ codeRange 0x106958 bytes_l106958, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x6958 80 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l106958_1

@[cfg_block] def b_l1069fd : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1069fd (cmpR8Imm8Effect 0x1069fd 4 5 0x3f) (EffectPart.reads (.flag .ZF) [.gpr 5] []) (.flag .ZF)) #v[5]
    (.letOp (n := 54) (.out 0x1069fd (cmpR8Imm8Effect 0x1069fd 4 5 0x3f) (EffectPart.reads (.flag .SF) [.gpr 5] []) (.flag .SF)) #v[5]
    (.letOp (n := 55) (.out 0x1069fd (cmpR8Imm8Effect 0x1069fd 4 5 0x3f) (EffectPart.reads (.flag .OF) [.gpr 5] []) (.flag .OF)) #v[5]
    (.letOp (n := 56) (.exec 0x1069fd (fun s => s.RIP = 0x1069fd) (cmpR8Imm8Effect 0x1069fd 4 5 0x3f) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 57) (.pure (condOp 14)) #v[53, 54, 55]
    (.terminate (.condBr (Fin.last 57) ⟨.l106a73, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (20, 54), (21, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l106a03, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (20, 54), (21, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l1069fd : List UInt8 :=
  [0x40, 0x80, 0xFD, 0x3F, 0x7E, 0x70]

theorem code_l1069fd : ∀ x ∈ codeRange 0x1069fd bytes_l1069fd, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x69fd 6 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106a03 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106a03 (movzxR32R8Effect 0x106a03 4 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[5]
    (.letOp (n := 54) (.exec 0x106a03 (fun s => s.RIP = 0x106a03) (movzxR32R8Effect 0x106a03 4 6 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 55) (.out 0x106a07 (leaR64Effect 0x106a07 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 56) (.exec 0x106a07 (fun s => s.RIP = 0x106a07) (leaR64Effect 0x106a07 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x106a0c (movR64R64Effect 0x106a0c 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14] []) (.reg (.gpr 2))) #v[14]
    (.letOp (n := 58) (.exec 0x106a0c (fun s => s.RIP = 0x106a0c) (movR64R64Effect 0x106a0c 2 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 59) (.out 0x106a0f (callEffect (fun _ => 0x106b60) 0x106a14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x106a0f (PushPre 0x106a0f 5) (callEffect (fun _ => 0x106b60) 0x106a14) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x106a14⟩) #v[]
    (.terminate (.call ⟨.l106b60, RegMap.args [(1, 1), (2, 57), (3, 3), (4, 59), (5, 5), (6, 53), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l106a14, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l106a03 : List UInt8 :=
  [0x40, 0x0F, 0xB6, 0xF5, 0x48, 0x8D, 0x7C, 0x24, 0x08, 0x4C, 0x89, 0xF2, 0xE8, 0x4C, 0x01, 0x00,
    0x00]

theorem code_l106a03 : ∀ x ∈ codeRange 0x106a03 bytes_l106a03, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6a03 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106a14 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106a14 (movR32M32LowEffect 0x106a14 1 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x106a14 (LoadPre 0x106a14 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x106a14 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x106a14 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x106a18 (movzxR32M8Effect 0x106a18 5 0 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 56) (.exec 0x106a18 (LoadPre 0x106a18 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x106a18 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x106a18 5 0 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x106a1d (cmpR32Imm8Effect 0x106a1d 3 1 0x2) (EffectPart.reads (.flag .ZF) [.gpr 1] []) (.flag .ZF)) #v[53]
    (.letOp (n := 58) (.exec 0x106a1d (fun s => s.RIP = 0x106a1d) (cmpR32Imm8Effect 0x106a1d 3 1 0x2) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 59) (.pure (condOp 5)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l106ad0, RegMap.args [(0, 55), (1, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l106a26, RegMap.args [(0, 55), (1, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l106a14 : List UInt8 :=
  [0x8B, 0x4C, 0x24, 0x08, 0x0F, 0xB6, 0x44, 0x24, 0x0C, 0x83, 0xF9, 0x02, 0x0F, 0x85, 0xAA, 0x00,
    0x00, 0x00]

theorem code_l106a14 : ∀ x ∈ codeRange 0x106a14 bytes_l106a14, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6a14 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106a26 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106a26 (movR32M32LowEffect 0x106a26 2 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 54) (.exec 0x106a26 (LoadPre 0x106a26 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x106a26 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x106a26 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x106a2a (movR8Imm8Effect 0x106a2a 2 1 0x16) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1]
    (.letOp (n := 56) (.exec 0x106a2a (fun s => s.RIP = 0x106a2a) (movR8Imm8Effect 0x106a2a 2 1 0x16) (Reg.operands [.gpr 1] [])) #v[1]
    (.terminate (.br ⟨.l106a34, RegMap.args [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l106a26 : List UInt8 :=
  [0x8B, 0x54, 0x24, 0x10, 0xB1, 0x16, 0xEB, 0x06]

theorem code_l106a26 : ∀ x ∈ codeRange 0x106a26 bytes_l106a26, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6a26 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106a34 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106a34 (shrR8Effect 0x106a34 4 5 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[5]
    (.letOp (n := 54) (.exec 0x106a34 (fun s => s.RIP = 0x106a34) (shrR8Effect 0x106a34 4 5 5) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5]
    (.letOp (n := 55) (.out 0x106a38 (andR8Imm8Effect 0x106a38 4 5 0x1) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5] []) (.reg (.gpr 5))) #v[53]
    (.letOp (n := 56) (.exec 0x106a38 (fun s => s.RIP = 0x106a38) (andR8Imm8Effect 0x106a38 4 5 0x1) (Reg.operands [.gpr 5] [])) #v[53]
    (.letOp (n := 57) (.exec 0x106a3c (StorePre 0x106a3c 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x106a3c + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x106a3c 3 1 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[1, 3]
    (.letOp (n := 58) (.exec 0x106a3f (StorePre 0x106a3f 3 (fun s => AddrMode.addr (.base 3 (.d8 0x5)) s (0x106a3f + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x106a3f 3 0 (.base 3 (.d8 0x5))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (.letOp (n := 59) (.exec 0x106a42 (StorePre 0x106a42 3 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x106a42 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x106a42 2 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[2, 3]
    (.letOp (n := 60) (.exec 0x106a45 (StorePre 0x106a45 4 (fun s => AddrMode.addr (.base 3 (.d8 0xc)) s (0x106a45 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x106a45 4 5 (.base 3 (.d8 0xc))) (Reg.operands [.gpr 5, .gpr 3] [])) #v[55, 3]
    (.letOp (n := 61) (.exec 0x106a49 (StorePre 0x106a49 6 (fun s => AddrMode.addr (.base 3 .none) s (0x106a49 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x106a49 6 (.base 3 .none) 0x2) (Reg.operands [.gpr 3] [])) #v[3]
    (.terminate (.br ⟨.l106a4f, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩))))))))))

def bytes_l106a34 : List UInt8 :=
  [0x40, 0xC0, 0xED, 0x05, 0x40, 0x80, 0xE5, 0x01, 0x88, 0x4B, 0x04, 0x88, 0x43, 0x05, 0x89, 0x53,
    0x08, 0x40, 0x88, 0x6B, 0x0C, 0xC7, 0x03, 0x02, 0x00, 0x00, 0x00]

theorem code_l106a34 : ∀ x ∈ codeRange 0x106a34 bytes_l106a34, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6a34 27 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106a4f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106a4f (movR64R64Effect 0x106a4f 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 54) (.exec 0x106a4f (fun s => s.RIP = 0x106a4f) (movR64R64Effect 0x106a4f 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x106a52 (addR64Imm8Effect 0x106a52 4 0x40) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 56) (.exec 0x106a52 (fun s => s.RIP = 0x106a52) (addR64Imm8Effect 0x106a52 4 0x40) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x106a56 (popR64Effect 0x106a56 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[55]
    (.letOp (n := 58) (.out 0x106a56 (popR64Effect 0x106a56 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[55]
    (.letOp (n := 59) (.exec 0x106a56 (PopPre 0x106a56) (popR64Effect 0x106a56 1 3) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 60) (.out 0x106a57 (popR64Effect 0x106a57 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[58]
    (.letOp (n := 61) (.out 0x106a57 (popR64Effect 0x106a57 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[58]
    (.letOp (n := 62) (.exec 0x106a57 (PopPre 0x106a57) (popR64Effect 0x106a57 2 14) (Reg.operands [.gpr 4] [])) #v[58]
    (.letOp (n := 63) (.out 0x106a59 (popR64Effect 0x106a59 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[61]
    (.letOp (n := 64) (.out 0x106a59 (popR64Effect 0x106a59 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 65) (.exec 0x106a59 (PopPre 0x106a59) (popR64Effect 0x106a59 1 5) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 66) (.out 0x106a5a (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[64]
    (.letOp (n := 67) (.out 0x106a5a (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[64]
    (.letOp (n := 68) (.exec 0x106a5a (RetPre 0x106a5a) (retEffect) (Reg.operands [.gpr 4] [])) #v[64]
    (.terminate (.ret (RegMap.args [(0, 53), (1, 1), (2, 2), (3, 57), (4, 67), (5, 63), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 69) (some ⟨66, by decide⟩))))))))))))))))))

def bytes_l106a4f : List UInt8 :=
  [0x48, 0x89, 0xD8, 0x48, 0x83, 0xC4, 0x40, 0x5B, 0x41, 0x5E, 0x5D, 0xC3]

theorem code_l106a4f : ∀ x ∈ codeRange 0x106a4f bytes_l106a4f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6a4f 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106a73 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106a73 (cmpR8Imm8Effect 0x106a73 4 5 0xc0) (EffectPart.reads (.flag .CF) [.gpr 5] []) (.flag .CF)) #v[5]
    (.letOp (n := 54) (.out 0x106a73 (cmpR8Imm8Effect 0x106a73 4 5 0xc0) (EffectPart.reads (.flag .SF) [.gpr 5] []) (.flag .SF)) #v[5]
    (.letOp (n := 55) (.out 0x106a73 (cmpR8Imm8Effect 0x106a73 4 5 0xc0) (EffectPart.reads (.flag .OF) [.gpr 5] []) (.flag .OF)) #v[5]
    (.letOp (n := 56) (.exec 0x106a73 (fun s => s.RIP = 0x106a73) (cmpR8Imm8Effect 0x106a73 4 5 0xc0) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 57) (.pure (condOp 13)) #v[54, 55]
    (.terminate (.condBr (Fin.last 57) ⟨.l106aa0, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (20, 54), (21, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l106a79, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (20, 54), (21, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l106a73 : List UInt8 :=
  [0x40, 0x80, 0xFD, 0xC0, 0x7D, 0x27]

theorem code_l106a73 : ∀ x ∈ codeRange 0x106a73 bytes_l106a73, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6a73 6 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106a79 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106a79 (movzxR32R8Effect 0x106a79 4 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[5]
    (.letOp (n := 54) (.exec 0x106a79 (fun s => s.RIP = 0x106a79) (movzxR32R8Effect 0x106a79 4 6 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 55) (.out 0x106a7d (leaR64Effect 0x106a7d 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 56) (.exec 0x106a7d (fun s => s.RIP = 0x106a7d) (leaR64Effect 0x106a7d 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x106a82 (movR64R64Effect 0x106a82 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14] []) (.reg (.gpr 2))) #v[14]
    (.letOp (n := 58) (.exec 0x106a82 (fun s => s.RIP = 0x106a82) (movR64R64Effect 0x106a82 2 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 59) (.out 0x106a85 (callEffect (fun _ => 0x106b60) 0x106a8a) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x106a85 (PushPre 0x106a85 5) (callEffect (fun _ => 0x106b60) 0x106a8a) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x106a8a⟩) #v[]
    (.terminate (.call ⟨.l106b60, RegMap.args [(1, 1), (2, 57), (3, 3), (4, 59), (5, 5), (6, 53), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l106a8a, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l106a79 : List UInt8 :=
  [0x40, 0x0F, 0xB6, 0xF5, 0x48, 0x8D, 0x7C, 0x24, 0x08, 0x4C, 0x89, 0xF2, 0xE8, 0xD6, 0x00, 0x00,
    0x00]

theorem code_l106a79 : ∀ x ∈ codeRange 0x106a79 bytes_l106a79, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6a79 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106a8a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106a8a (movR32M32LowEffect 0x106a8a 1 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x106a8a (LoadPre 0x106a8a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x106a8a + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x106a8a 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x106a8e (movzxR32M8Effect 0x106a8e 5 0 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 56) (.exec 0x106a8e (LoadPre 0x106a8e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x106a8e + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x106a8e 5 0 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x106a93 (cmpR32Imm8Effect 0x106a93 3 1 0x2) (EffectPart.reads (.flag .ZF) [.gpr 1] []) (.flag .ZF)) #v[53]
    (.letOp (n := 58) (.exec 0x106a93 (fun s => s.RIP = 0x106a93) (cmpR32Imm8Effect 0x106a93 3 1 0x2) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 59) (.pure (condOp 5)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l106ad0, RegMap.args [(0, 55), (1, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l106a98, RegMap.args [(0, 55), (1, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l106a8a : List UInt8 :=
  [0x8B, 0x4C, 0x24, 0x08, 0x0F, 0xB6, 0x44, 0x24, 0x0C, 0x83, 0xF9, 0x02, 0x75, 0x38]

theorem code_l106a8a : ∀ x ∈ codeRange 0x106a8a bytes_l106a8a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6a8a 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106a98 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106a98 (movR32M32LowEffect 0x106a98 2 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 54) (.exec 0x106a98 (LoadPre 0x106a98 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x106a98 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x106a98 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x106a9c (movR8Imm8Effect 0x106a9c 2 1 0x17) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1]
    (.letOp (n := 56) (.exec 0x106a9c (fun s => s.RIP = 0x106a9c) (movR8Imm8Effect 0x106a9c 2 1 0x17) (Reg.operands [.gpr 1] [])) #v[1]
    (.terminate (.br ⟨.l106a34, RegMap.args [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l106a98 : List UInt8 :=
  [0x8B, 0x54, 0x24, 0x10, 0xB1, 0x17, 0xEB, 0x94]

theorem code_l106a98 : ∀ x ∈ codeRange 0x106a98 bytes_l106a98, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6a98 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106aa0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.pure (condOp 2)) #v[16]
    (.terminate (.condBr (Fin.last 53) ⟨.l106b26, RegMap.args (entryMap (live .l106aa0)) 54⟩ ⟨.l106aa6, RegMap.args (entryMap (live .l106aa0)) 54⟩))

def bytes_l106aa0 : List UInt8 :=
  [0x0F, 0x82, 0x80, 0x00, 0x00, 0x00]

theorem code_l106aa0 : ∀ x ∈ codeRange 0x106aa0 bytes_l106aa0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6aa0 6 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106aa6 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106aa6 (movzxR32R8Effect 0x106aa6 4 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[5]
    (.letOp (n := 54) (.exec 0x106aa6 (fun s => s.RIP = 0x106aa6) (movzxR32R8Effect 0x106aa6 4 6 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 55) (.out 0x106aaa (leaR64Effect 0x106aaa 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 56) (.exec 0x106aaa (fun s => s.RIP = 0x106aaa) (leaR64Effect 0x106aaa 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x106aaf (movR64R64Effect 0x106aaf 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14] []) (.reg (.gpr 2))) #v[14]
    (.letOp (n := 58) (.exec 0x106aaf (fun s => s.RIP = 0x106aaf) (movR64R64Effect 0x106aaf 2 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 59) (.out 0x106ab2 (callEffect (fun _ => 0x106b60) 0x106ab7) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x106ab2 (PushPre 0x106ab2 5) (callEffect (fun _ => 0x106b60) 0x106ab7) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x106ab7⟩) #v[]
    (.terminate (.call ⟨.l106b60, RegMap.args [(1, 1), (2, 57), (3, 3), (4, 59), (5, 5), (6, 53), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l106ab7, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l106aa6 : List UInt8 :=
  [0x40, 0x0F, 0xB6, 0xF5, 0x48, 0x8D, 0x7C, 0x24, 0x08, 0x4C, 0x89, 0xF2, 0xE8, 0xA9, 0x00, 0x00,
    0x00]

theorem code_l106aa6 : ∀ x ∈ codeRange 0x106aa6 bytes_l106aa6, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6aa6 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106ab7 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106ab7 (movR32M32LowEffect 0x106ab7 1 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x106ab7 (LoadPre 0x106ab7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x106ab7 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x106ab7 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x106abb (movzxR32M8Effect 0x106abb 5 0 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 56) (.exec 0x106abb (LoadPre 0x106abb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x106abb + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x106abb 5 0 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x106ac0 (cmpR32Imm8Effect 0x106ac0 3 1 0x2) (EffectPart.reads (.flag .ZF) [.gpr 1] []) (.flag .ZF)) #v[53]
    (.letOp (n := 58) (.exec 0x106ac0 (fun s => s.RIP = 0x106ac0) (cmpR32Imm8Effect 0x106ac0 3 1 0x2) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 59) (.pure (condOp 5)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l106ad0, RegMap.args [(0, 55), (1, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l106ac5, RegMap.args [(0, 55), (1, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l106ab7 : List UInt8 :=
  [0x8B, 0x4C, 0x24, 0x08, 0x0F, 0xB6, 0x44, 0x24, 0x0C, 0x83, 0xF9, 0x02, 0x75, 0x0B]

theorem code_l106ab7 : ∀ x ∈ codeRange 0x106ab7 bytes_l106ab7, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6ab7 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106ac5 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106ac5 (movR32M32LowEffect 0x106ac5 2 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 54) (.exec 0x106ac5 (LoadPre 0x106ac5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x106ac5 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x106ac5 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x106ac9 (movR8Imm8Effect 0x106ac9 2 1 0x18) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1]
    (.letOp (n := 56) (.exec 0x106ac9 (fun s => s.RIP = 0x106ac9) (movR8Imm8Effect 0x106ac9 2 1 0x18) (Reg.operands [.gpr 1] [])) #v[1]
    (.terminate (.br ⟨.l106a34, RegMap.args [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l106ac5 : List UInt8 :=
  [0x8B, 0x54, 0x24, 0x10, 0xB1, 0x18, 0xE9, 0x64, 0xFF, 0xFF, 0xFF]

theorem code_l106ac5 : ∀ x ∈ codeRange 0x106ac5 bytes_l106ac5, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6ac5 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106ad0_1 : Block Op Label signature Reg.count 82 :=
  .terminate (.br ⟨.l106a4f, RegMap.args [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (6, 76), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 82⟩)

def bytes_l106ad0_1 : List UInt8 :=
  [0xE9, 0x29, 0xFF, 0xFF, 0xFF]

theorem code_l106ad0_1 : ∀ x ∈ codeRange 0x106b21 bytes_l106ad0_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6b21 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106ad0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106ad0 (movzxR32M8Effect 0x106ad0 5 2 (.sib 4 none 0 (.d8 0xf))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 54) (.exec 0x106ad0 (LoadPre 0x106ad0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x106ad0 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x106ad0 5 2 (.sib 4 none 0 (.d8 0xf))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x106ad5 (StorePre 0x106ad5 3 (fun s => AddrMode.addr (.base 3 (.d8 0x7)) s (0x106ad5 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x106ad5 3 2 (.base 3 (.d8 0x7))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[53, 3]
    (.letOp (n := 56) (.out 0x106ad8 (movzxR32M16Effect 0x106ad8 5 2 (.sib 4 none 0 (.d8 0xd))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 57) (.exec 0x106ad8 (LoadPre 0x106ad8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xd)) s (0x106ad8 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x106ad8 5 2 (.sib 4 none 0 (.d8 0xd))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x106add (StorePre 0x106add 4 (fun s => AddrMode.addr (.base 3 (.d8 0x5)) s (0x106add + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x106add 4 2 (.base 3 (.d8 0x5))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[56, 3]
    (.letOp (n := 59) (.out 0x106ae1 (movR32M32LowEffect 0x106ae1 2 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 60) (.exec 0x106ae1 (LoadPre 0x106ae1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x106ae1 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x106ae1 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x106ae5 (movR64M64Effect 0x106ae5 6 (.sib 4 none 0 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 62) (.exec 0x106ae5 (LoadPre 0x106ae5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x106ae5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106ae5 6 (.sib 4 none 0 (.d8 0x1c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x106aea (StorePre 0x106aea 4 (fun s => AddrMode.addr (.base 3 (.d8 0x14)) s (0x106aea + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x106aea 6 (.base 3 (.d8 0x14))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 64) (.out 0x106aee (movR64M64Effect 0x106aee 6 (.sib 4 none 0 (.d8 0x24))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 65) (.exec 0x106aee (LoadPre 0x106aee (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x106aee + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106aee 6 (.sib 4 none 0 (.d8 0x24))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x106af3 (StorePre 0x106af3 4 (fun s => AddrMode.addr (.base 3 (.d8 0x1c)) s (0x106af3 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x106af3 6 (.base 3 (.d8 0x1c))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[64, 3]
    (.letOp (n := 67) (.out 0x106af7 (movR64M64Effect 0x106af7 6 (.sib 4 none 0 (.d8 0x2c))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 68) (.exec 0x106af7 (LoadPre 0x106af7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x106af7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106af7 6 (.sib 4 none 0 (.d8 0x2c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.exec 0x106afc (StorePre 0x106afc 4 (fun s => AddrMode.addr (.base 3 (.d8 0x24)) s (0x106afc + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x106afc 6 (.base 3 (.d8 0x24))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[67, 3]
    (.letOp (n := 70) (.out 0x106b00 (movR64M64Effect 0x106b00 6 (.sib 4 none 0 (.d8 0x34))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 71) (.exec 0x106b00 (LoadPre 0x106b00 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x106b00 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106b00 6 (.sib 4 none 0 (.d8 0x34))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.exec 0x106b05 (StorePre 0x106b05 4 (fun s => AddrMode.addr (.base 3 (.d8 0x2c)) s (0x106b05 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x106b05 6 (.base 3 (.d8 0x2c))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[70, 3]
    (.letOp (n := 73) (.out 0x106b09 (movR32M32LowEffect 0x106b09 6 (.sib 4 none 0 (.d8 0x3c))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 74) (.exec 0x106b09 (LoadPre 0x106b09 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x106b09 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x106b09 6 (.sib 4 none 0 (.d8 0x3c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.exec 0x106b0d (StorePre 0x106b0d 3 (fun s => AddrMode.addr (.base 3 (.d8 0x34)) s (0x106b0d + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x106b0d 6 (.base 3 (.d8 0x34))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[73, 3]
    (.letOp (n := 76) (.out 0x106b10 (movR64M64Effect 0x106b10 6 (.sib 4 none 0 (.d8 0x14))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 77) (.exec 0x106b10 (LoadPre 0x106b10 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x106b10 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106b10 6 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 78) (.exec 0x106b15 (StorePre 0x106b15 4 (fun s => AddrMode.addr (.base 3 (.d8 0xc)) s (0x106b15 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x106b15 6 (.base 3 (.d8 0xc))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[76, 3]
    (.letOp (n := 79) (.exec 0x106b19 (StorePre 0x106b19 2 (fun s => AddrMode.addr (.base 3 .none) s (0x106b19 + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x106b19 1 (.base 3 .none)) (Reg.operands [.gpr 1, .gpr 3] [])) #v[1, 3]
    (.letOp (n := 80) (.exec 0x106b1b (StorePre 0x106b1b 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x106b1b + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x106b1b 3 0 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (.letOp (n := 81) (.exec 0x106b1e (StorePre 0x106b1e 3 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x106b1e + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x106b1e 2 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[59, 3]
    (b_l106ad0_1)))))))))))))))))))))))))))))

def bytes_l106ad0 : List UInt8 :=
  [0x0F, 0xB6, 0x54, 0x24, 0x0F, 0x88, 0x53, 0x07, 0x0F, 0xB7, 0x54, 0x24, 0x0D, 0x66, 0x89, 0x53,
    0x05, 0x8B, 0x54, 0x24, 0x10, 0x48, 0x8B, 0x74, 0x24, 0x1C, 0x48, 0x89, 0x73, 0x14, 0x48, 0x8B,
    0x74, 0x24, 0x24, 0x48, 0x89, 0x73, 0x1C, 0x48, 0x8B, 0x74, 0x24, 0x2C, 0x48, 0x89, 0x73, 0x24,
    0x48, 0x8B, 0x74, 0x24, 0x34, 0x48, 0x89, 0x73, 0x2C, 0x8B, 0x74, 0x24, 0x3C, 0x89, 0x73, 0x34,
    0x48, 0x8B, 0x74, 0x24, 0x14, 0x48, 0x89, 0x73, 0x0C, 0x89, 0x0B, 0x88, 0x43, 0x04, 0x89, 0x53,
    0x08] ++ bytes_l106ad0_1

theorem code_l106ad0 : ∀ x ∈ codeRange 0x106ad0 bytes_l106ad0, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x6ad0 81 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l106ad0_1

@[cfg_block] def b_l106b26 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x106b26 (StorePre 0x106b26 5 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x106b26 + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x106b26 (.base 14 (.d8 0x20)) 0x1) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 54) (.out 0x106b2b (movR32M32Effect 0x106b2b 0 (.base 14 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[14]
    (.letOp (n := 55) (.exec 0x106b2b (LoadPre 0x106b2b (fun s => AddrMode.addr (.base 14 (.d8 0x1c)) s (0x106b2b + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x106b2b 0 (.base 14 (.d8 0x1c))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 56) (.exec 0x106b2f (StorePre 0x106b2f 6 (fun s => AddrMode.addr (.base 3 .none) s (0x106b2f + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x106b2f 6 (.base 3 .none) 0x1) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 57) (.exec 0x106b35 (StorePre 0x106b35 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x106b35 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x106b35 0 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[54, 3]
    (.letOp (n := 58) (.exec 0x106b38 (StorePre 0x106b38 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x106b38 + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x106b38 (.base 3 (.d8 0x8)) 0x12) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 59) (.exec 0x106b3c (StorePre 0x106b3c 4 (fun s => AddrMode.addr (.base 3 (.d8 0x9)) s (0x106b3c + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x106b3c 4 5 (.base 3 (.d8 0x9))) (Reg.operands [.gpr 5, .gpr 3] [])) #v[5, 3]
    (.terminate (.br ⟨.l106a4f, RegMap.args [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l106b26 : List UInt8 :=
  [0x41, 0xC6, 0x46, 0x20, 0x01, 0x41, 0x8B, 0x46, 0x1C, 0xC7, 0x03, 0x01, 0x00, 0x00, 0x00, 0x89,
    0x43, 0x04, 0xC6, 0x43, 0x08, 0x12, 0x40, 0x88, 0x6B, 0x09, 0xE9, 0x0A, 0xFF, 0xFF, 0xFF]

theorem code_l106b26 : ∀ x ∈ codeRange 0x106b26 bytes_l106b26, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6b26 31 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106b45 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106b45 (movR32Imm32Effect 0x106b45 5 7 0x1) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 54) (.exec 0x106b45 (fun s => s.RIP = 0x106b45) (movR32Imm32Effect 0x106b45 5 7 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x106b4a (movR64Imm32Effect 0x106b4a 2 0x202530) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 56) (.exec 0x106b4a (fun s => s.RIP = 0x106b4a) (movR64Imm32Effect 0x106b4a 2 0x202530) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x106b51 (callEffect (fun _ => 0x129c90) 0x106b56) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x106b51 (PushPre 0x106b51 5) (callEffect (fun _ => 0x129c90) 0x106b56) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x106b56⟩) #v[]
    (.terminate (.call ⟨.l129c90, RegMap.args [(2, 55), (4, 57), (5, 5), (6, 6), (7, 53)] 60⟩ { target := .l106b56, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l106b45 : List UInt8 :=
  [0xBF, 0x01, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC2, 0x30, 0x25, 0x20, 0x00, 0xE8, 0x3A, 0x31, 0x02,
    0x00]

theorem code_l106b45 : ∀ x ∈ codeRange 0x106b45 bytes_l106b45, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6b45 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106b56 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x106b56 (fun s => s.RIP = 0x106b56) (fun _ => nopEffect 0x106b56 10) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l106b60, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 54⟩))

def bytes_l106b56 : List UInt8 :=
  [0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem code_l106b56 : ∀ x ∈ codeRange 0x106b56 bytes_l106b56, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6b56 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106b60 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106b60 (pushR64Effect 0x106b60 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x106b60 (PushPre 0x106b60 1) (pushR64Effect 0x106b60 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x106b61 (pushR64Effect 0x106b61 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x106b61 (PushPre 0x106b61 2) (pushR64Effect 0x106b61 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x106b63 (pushR64Effect 0x106b63 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x106b63 (PushPre 0x106b63 2) (pushR64Effect 0x106b63 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x106b65 (pushR64Effect 0x106b65 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x106b65 (PushPre 0x106b65 2) (pushR64Effect 0x106b65 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x106b67 (pushR64Effect 0x106b67 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x106b67 (PushPre 0x106b67 2) (pushR64Effect 0x106b67 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x106b69 (pushR64Effect 0x106b69 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x106b69 (PushPre 0x106b69 1) (pushR64Effect 0x106b69 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x106b6a (subR64Imm8Effect 0x106b6a 4 0x78) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x106b6a (fun s => s.RIP = 0x106b6a) (subR64Imm8Effect 0x106b6a 4 0x78) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x106b6e (movR64R64Effect 0x106b6e 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 68) (.exec 0x106b6e (fun s => s.RIP = 0x106b6e) (movR64R64Effect 0x106b6e 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 69) (.out 0x106b71 (movR32R32Effect 0x106b71 2 5 6) (EffectPart.reads (.reg (.gpr 5)) [.gpr 6] []) (.reg (.gpr 5))) #v[6]
    (.letOp (n := 70) (.exec 0x106b71 (fun s => s.RIP = 0x106b71) (movR32R32Effect 0x106b71 2 5 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 71) (.out 0x106b73 (andR8Imm8Effect 0x106b73 4 5 0x20) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5] []) (.reg (.gpr 5))) #v[69]
    (.letOp (n := 72) (.exec 0x106b73 (fun s => s.RIP = 0x106b73) (andR8Imm8Effect 0x106b73 4 5 0x20) (Reg.operands [.gpr 5] [])) #v[69]
    (.letOp (n := 73) (.out 0x106b77 (andR8Imm8Effect 0x106b77 4 6 0x1f) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[6]
    (.letOp (n := 74) (.exec 0x106b77 (fun s => s.RIP = 0x106b77) (andR8Imm8Effect 0x106b77 4 6 0x1f) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 75) (.out 0x106b7b (cmpR8Imm8Effect 0x106b7b 4 6 0x1f) (EffectPart.reads (.flag .ZF) [.gpr 6] []) (.flag .ZF)) #v[73]
    (.letOp (n := 76) (.exec 0x106b7b (fun s => s.RIP = 0x106b7b) (cmpR8Imm8Effect 0x106b7b 4 6 0x1f) (Reg.operands [.gpr 6] [])) #v[73]
    (.letOp (n := 77) (.pure (condOp 5)) #v[75]
    (.terminate (.condBr (Fin.last 77) ⟨.l106bde, RegMap.args [(1, 1), (2, 2), (3, 67), (4, 65), (5, 71), (6, 73), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 75), (22, 22), (39, 39), (50, 50), (51, 51)] 78⟩ ⟨.l106b81, RegMap.args [(1, 1), (2, 2), (3, 67), (4, 65), (5, 71), (6, 73), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 75), (22, 22), (39, 39), (50, 50), (51, 51)] 78⟩))))))))))))))))))))))))))

def bytes_l106b60 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x83, 0xEC, 0x78, 0x48, 0x89,
    0xFB, 0x89, 0xF5, 0x40, 0x80, 0xE5, 0x20, 0x40, 0x80, 0xE6, 0x1F, 0x40, 0x80, 0xFE, 0x1F, 0x75,
    0x5D]

theorem code_l106b60 : ∀ x ∈ codeRange 0x106b60 bytes_l106b60, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6b60 33 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106b81 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106b81 (movR64R64Effect 0x106b81 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[2]
    (.letOp (n := 54) (.exec 0x106b81 (fun s => s.RIP = 0x106b81) (movR64R64Effect 0x106b81 14 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 55) (.out 0x106b84 (leaR64Effect 0x106b84 7 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 56) (.exec 0x106b84 (fun s => s.RIP = 0x106b84) (leaR64Effect 0x106b84 7 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x106b89 (movR64R64Effect 0x106b89 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[2]
    (.letOp (n := 58) (.exec 0x106b89 (fun s => s.RIP = 0x106b89) (movR64R64Effect 0x106b89 6 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 59) (.out 0x106b8c (movR32Imm32Effect 0x106b8c 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 60) (.exec 0x106b8c (fun s => s.RIP = 0x106b8c) (movR32Imm32Effect 0x106b8c 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 61) (.out 0x106b91 (callEffect (fun _ => 0x127b80) 0x106b96) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 62) (.exec 0x106b91 (PushPre 0x106b91 5) (callEffect (fun _ => 0x127b80) 0x106b96) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.const ⟨64, 0x106b96⟩) #v[]
    (.terminate (.call ⟨.l127b80, RegMap.args [(2, 59), (3, 3), (4, 61), (5, 5), (6, 57), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ { target := .l106b96, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l106b81 : List UInt8 :=
  [0x49, 0x89, 0xD6, 0x48, 0x8D, 0x7C, 0x24, 0x40, 0x48, 0x89, 0xD6, 0xBA, 0x01, 0x00, 0x00, 0x00,
    0xE8, 0xEA, 0x0F, 0x02, 0x00]

theorem code_l106b81 : ∀ x ∈ codeRange 0x106b81 bytes_l106b81, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6b81 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106b96 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106b96 (movR32M32LowEffect 0x106b96 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x106b96 (LoadPre 0x106b96 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x106b96 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x106b96 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x106b9a (cmpR32Imm8Effect 0x106b9a 3 0 0x2) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x106b9a (fun s => s.RIP = 0x106b9a) (cmpR32Imm8Effect 0x106b9a 3 0 0x2) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l106c54, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l106ba3, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l106b96 : List UInt8 :=
  [0x8B, 0x44, 0x24, 0x40, 0x83, 0xF8, 0x02, 0x0F, 0x85, 0xB1, 0x00, 0x00, 0x00]

theorem code_l106b96 : ∀ x ∈ codeRange 0x106b96 bytes_l106b96, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6b96 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106ba3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106ba3 (movR64M64Effect 0x106ba3 6 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 54) (.exec 0x106ba3 (LoadPre 0x106ba3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x106ba3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106ba3 6 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x106ba8 (cmpR64Imm8Effect 0x106ba8 6 0x1) (EffectPart.reads (.flag .ZF) [.gpr 6] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x106ba8 (fun s => s.RIP = 0x106ba8) (cmpR64Imm8Effect 0x106ba8 6 0x1) (Reg.operands [.gpr 6] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l106db1, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l106bb2, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l106ba3 : List UInt8 :=
  [0x48, 0x8B, 0x74, 0x24, 0x50, 0x48, 0x83, 0xFE, 0x01, 0x0F, 0x85, 0xFF, 0x01, 0x00, 0x00]

theorem code_l106ba3 : ∀ x ∈ codeRange 0x106ba3 bytes_l106ba3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6ba3 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106bb2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106bb2 (movR64M64Effect 0x106bb2 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x106bb2 (LoadPre 0x106bb2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x106bb2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106bb2 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x106bb7 (movzxR32M8Effect 0x106bb7 4 15 (.base 0 .none)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[53]
    (.letOp (n := 56) (.exec 0x106bb7 (LoadPre 0x106bb7 (fun s => AddrMode.addr (.base 0 .none) s (0x106bb7 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x106bb7 4 15 (.base 0 .none)) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x106bbb (movR32R32Effect 0x106bbb 3 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[55]
    (.letOp (n := 58) (.exec 0x106bbb (fun s => s.RIP = 0x106bbb) (movR32R32Effect 0x106bbb 3 0 15) (Reg.operands [.gpr 15] [])) #v[55]
    (.letOp (n := 59) (.out 0x106bbe (andR32Imm8Effect 0x106bbe 4 15 0x7f) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15] []) (.reg (.gpr 15))) #v[55]
    (.letOp (n := 60) (.exec 0x106bbe (fun s => s.RIP = 0x106bbe) (andR32Imm8Effect 0x106bbe 4 15 0x7f) (Reg.operands [.gpr 15] [])) #v[55]
    (.letOp (n := 61) (.out 0x106bc2 (testR8R8Effect 0x106bc2 2 0 0) (EffectPart.reads (.flag .SF) [.gpr 0, .gpr 0] []) (.flag .SF)) #v[57, 57]
    (.letOp (n := 62) (.exec 0x106bc2 (fun s => s.RIP = 0x106bc2) (testR8R8Effect 0x106bc2 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[57, 57]
    (.letOp (n := 63) (.pure (condOp 8)) #v[61]
    (.terminate (.condBr (Fin.last 63) ⟨.l106bf8, RegMap.args [(0, 57), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 59), (20, 61), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ ⟨.l106bc6, RegMap.args [(0, 57), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 59), (20, 61), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩))))))))))))

def bytes_l106bb2 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x44, 0x0F, 0xB6, 0x38, 0x44, 0x89, 0xF8, 0x41, 0x83, 0xE7, 0x7F,
    0x84, 0xC0, 0x78, 0x32]

theorem code_l106bb2 : ∀ x ∈ codeRange 0x106bb2 bytes_l106bb2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6bb2 20 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106bc6 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106bc6 (cmpR8Imm8Effect 0x106bc6 4 15 0x1f) (EffectPart.reads (.flag .CF) [.gpr 15] []) (.flag .CF)) #v[15]
    (.letOp (n := 54) (.exec 0x106bc6 (fun s => s.RIP = 0x106bc6) (cmpR8Imm8Effect 0x106bc6 4 15 0x1f) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.pure (condOp 2)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l106d55, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l106bd0, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l106bc6 : List UInt8 :=
  [0x41, 0x80, 0xFF, 0x1F, 0x0F, 0x82, 0x85, 0x01, 0x00, 0x00]

theorem code_l106bc6 : ∀ x ∈ codeRange 0x106bc6 bytes_l106bc6, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6bc6 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106bd0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106bd0 (shrR8Effect 0x106bd0 4 5 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[5]
    (.letOp (n := 54) (.exec 0x106bd0 (fun s => s.RIP = 0x106bd0) (shrR8Effect 0x106bd0 4 5 5) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5]
    (.letOp (n := 55) (.exec 0x106bd4 (StorePre 0x106bd4 4 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x106bd4 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x106bd4 4 5 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 5, .gpr 3] [])) #v[53, 3]
    (.letOp (n := 56) (.exec 0x106bd8 (StorePre 0x106bd8 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x106bd8 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x106bd8 15 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 15, .gpr 3] [])) #v[15, 3]
    (.terminate (.br ⟨.l106bed, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l106bd0 : List UInt8 :=
  [0x40, 0xC0, 0xED, 0x05, 0x40, 0x88, 0x6B, 0x04, 0x44, 0x89, 0x7B, 0x08, 0xEB, 0x0F]

theorem code_l106bd0 : ∀ x ∈ codeRange 0x106bd0 bytes_l106bd0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6bd0 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106bde : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106bde (movzxR32R8Effect 0x106bde 4 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 54) (.exec 0x106bde (fun s => s.RIP = 0x106bde) (movzxR32R8Effect 0x106bde 4 0 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 55) (.out 0x106be2 (shrR8Effect 0x106be2 4 5 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[5]
    (.letOp (n := 56) (.exec 0x106be2 (fun s => s.RIP = 0x106be2) (shrR8Effect 0x106be2 4 5 5) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5]
    (.letOp (n := 57) (.exec 0x106be6 (StorePre 0x106be6 4 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x106be6 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x106be6 4 5 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 5, .gpr 3] [])) #v[55, 3]
    (.letOp (n := 58) (.exec 0x106bea (StorePre 0x106bea 3 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x106bea + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x106bea 0 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[53, 3]
    (.terminate (.br ⟨.l106bed, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l106bde : List UInt8 :=
  [0x40, 0x0F, 0xB6, 0xC6, 0x40, 0xC0, 0xED, 0x05, 0x40, 0x88, 0x6B, 0x04, 0x89, 0x43, 0x08]

theorem code_l106bde : ∀ x ∈ codeRange 0x106bde bytes_l106bde, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6bde 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106bed : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x106bed (StorePre 0x106bed 6 (fun s => AddrMode.addr (.base 3 .none) s (0x106bed + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x106bed 6 (.base 3 .none) 0x2) (Reg.operands [.gpr 3] [])) #v[3]
    (.terminate (.br ⟨.l106d6b, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 54⟩))

def bytes_l106bed : List UInt8 :=
  [0xC7, 0x03, 0x02, 0x00, 0x00, 0x00, 0xE9, 0x73, 0x01, 0x00, 0x00]

theorem code_l106bed : ∀ x ∈ codeRange 0x106bed bytes_l106bed, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6bed 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106bf8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106bf8 (testR8R8Effect 0x106bf8 3 15 15) (EffectPart.reads (.flag .ZF) [.gpr 15, .gpr 15] []) (.flag .ZF)) #v[15, 15]
    (.letOp (n := 54) (.exec 0x106bf8 (fun s => s.RIP = 0x106bf8) (testR8R8Effect 0x106bf8 3 15 15) (Reg.operands [.gpr 15, .gpr 15] [])) #v[15, 15]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l106d55, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l106c01, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l106bf8 : List UInt8 :=
  [0x45, 0x84, 0xFF, 0x0F, 0x84, 0x54, 0x01, 0x00, 0x00]

theorem code_l106bf8 : ∀ x ∈ codeRange 0x106bf8 bytes_l106bf8, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6bf8 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106c01 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106c01 (leaR64Effect 0x106c01 7 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x106c01 (fun s => s.RIP = 0x106c01) (leaR64Effect 0x106c01 7 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x106c06 (movR64R64Effect 0x106c06 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 56) (.exec 0x106c06 (fun s => s.RIP = 0x106c06) (movR64R64Effect 0x106c06 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x106c09 (movR32Imm32Effect 0x106c09 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x106c09 (fun s => s.RIP = 0x106c09) (movR32Imm32Effect 0x106c09 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x106c0e (callEffect (fun _ => 0x127b80) 0x106c13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x106c0e (PushPre 0x106c0e 5) (callEffect (fun _ => 0x127b80) 0x106c13) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x106c13⟩) #v[]
    (.terminate (.call ⟨.l127b80, RegMap.args [(2, 57), (3, 3), (4, 59), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l106c13, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l106c01 : List UInt8 :=
  [0x48, 0x8D, 0x7C, 0x24, 0x40, 0x4C, 0x89, 0xF6, 0xBA, 0x01, 0x00, 0x00, 0x00, 0xE8, 0x6D, 0x0F,
    0x02, 0x00]

theorem code_l106c01 : ∀ x ∈ codeRange 0x106c01 bytes_l106c01, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6c01 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106c13 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106c13 (movR32M32LowEffect 0x106c13 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x106c13 (LoadPre 0x106c13 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x106c13 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x106c13 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x106c17 (cmpR32Imm8Effect 0x106c17 3 0 0x2) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x106c17 (fun s => s.RIP = 0x106c17) (cmpR32Imm8Effect 0x106c17 3 0 0x2) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l106c54, RegMap.args [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l106c1c, RegMap.args [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l106c13 : List UInt8 :=
  [0x8B, 0x44, 0x24, 0x40, 0x83, 0xF8, 0x02, 0x75, 0x38]

theorem code_l106c13 : ∀ x ∈ codeRange 0x106c13 bytes_l106c13, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6c13 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106c1c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106c1c (movR64M64Effect 0x106c1c 6 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 54) (.exec 0x106c1c (LoadPre 0x106c1c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x106c1c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106c1c 6 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x106c21 (cmpR64Imm8Effect 0x106c21 6 0x1) (EffectPart.reads (.flag .ZF) [.gpr 6] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x106c21 (fun s => s.RIP = 0x106c21) (cmpR64Imm8Effect 0x106c21 6 0x1) (Reg.operands [.gpr 6] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l106db1, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l106c2b, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l106c1c : List UInt8 :=
  [0x48, 0x8B, 0x74, 0x24, 0x50, 0x48, 0x83, 0xFE, 0x01, 0x0F, 0x85, 0x86, 0x01, 0x00, 0x00]

theorem code_l106c1c : ∀ x ∈ codeRange 0x106c1c bytes_l106c1c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6c1c 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106c2b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106c2b (movR64M64Effect 0x106c2b 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x106c2b (LoadPre 0x106c2b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x106c2b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106c2b 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x106c30 (movzxR32M8Effect 0x106c30 4 12 (.base 0 .none)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[53]
    (.letOp (n := 56) (.exec 0x106c30 (LoadPre 0x106c30 (fun s => AddrMode.addr (.base 0 .none) s (0x106c30 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x106c30 4 12 (.base 0 .none)) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x106c34 (movR32R32Effect 0x106c34 3 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[55]
    (.letOp (n := 58) (.exec 0x106c34 (fun s => s.RIP = 0x106c34) (movR32R32Effect 0x106c34 3 0 12) (Reg.operands [.gpr 12] [])) #v[55]
    (.letOp (n := 59) (.out 0x106c37 (movR32R32Effect 0x106c37 3 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 15] []) (.reg (.gpr 1))) #v[15]
    (.letOp (n := 60) (.exec 0x106c37 (fun s => s.RIP = 0x106c37) (movR32R32Effect 0x106c37 3 1 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 61) (.out 0x106c3a (shlR32Effect 0x106c3a 3 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[59]
    (.letOp (n := 62) (.exec 0x106c3a (fun s => s.RIP = 0x106c3a) (shlR32Effect 0x106c3a 3 1 7) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[59]
    (.letOp (n := 63) (.out 0x106c3d (andR32Imm8Effect 0x106c3d 4 12 0x7f) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[55]
    (.letOp (n := 64) (.exec 0x106c3d (fun s => s.RIP = 0x106c3d) (andR32Imm8Effect 0x106c3d 4 12 0x7f) (Reg.operands [.gpr 12] [])) #v[55]
    (.letOp (n := 65) (.out 0x106c41 (orR32R32Effect 0x106c41 3 12 1) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 1] []) (.reg (.gpr 12))) #v[63, 61]
    (.letOp (n := 66) (.exec 0x106c41 (fun s => s.RIP = 0x106c41) (orR32R32Effect 0x106c41 3 12 1) (Reg.operands [.gpr 12, .gpr 1] [])) #v[63, 61]
    (.letOp (n := 67) (.out 0x106c44 (testR8R8Effect 0x106c44 2 0 0) (EffectPart.reads (.flag .SF) [.gpr 0, .gpr 0] []) (.flag .SF)) #v[57, 57]
    (.letOp (n := 68) (.exec 0x106c44 (fun s => s.RIP = 0x106c44) (testR8R8Effect 0x106c44 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[57, 57]
    (.letOp (n := 69) (.pure (condOp 8)) #v[67]
    (.terminate (.condBr (Fin.last 69) ⟨.l106cdf, RegMap.args [(0, 57), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 65), (13, 13), (14, 14), (15, 15), (20, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 70⟩ ⟨.l106c4c, RegMap.args [(0, 57), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 65), (13, 13), (14, 14), (15, 15), (20, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 70⟩))))))))))))))))))

def bytes_l106c2b : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x44, 0x0F, 0xB6, 0x20, 0x44, 0x89, 0xE0, 0x44, 0x89, 0xF9, 0xC1,
    0xE1, 0x07, 0x41, 0x83, 0xE4, 0x7F, 0x41, 0x09, 0xCC, 0x84, 0xC0, 0x0F, 0x88, 0x93, 0x00, 0x00,
    0x00]

theorem code_l106c2b : ∀ x ∈ codeRange 0x106c2b bytes_l106c2b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6c2b 33 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106c4c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106c4c (movR32R32Effect 0x106c4c 3 15 12) (EffectPart.reads (.reg (.gpr 15)) [.gpr 12] []) (.reg (.gpr 15))) #v[12]
    (.letOp (n := 54) (.exec 0x106c4c (fun s => s.RIP = 0x106c4c) (movR32R32Effect 0x106c4c 3 15 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.terminate (.br ⟨.l106bd0, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l106c4c : List UInt8 :=
  [0x45, 0x89, 0xE7, 0xE9, 0x7C, 0xFF, 0xFF, 0xFF]

theorem code_l106c4c : ∀ x ∈ codeRange 0x106c4c bytes_l106c4c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6c4c 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106c54 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106c54 (movR32M32LowEffect 0x106c54 1 (.sib 4 none 0 (.d8 0x44))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x106c54 (LoadPre 0x106c54 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x106c54 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x106c54 1 (.sib 4 none 0 (.d8 0x44))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x106c58 (movR64M64Effect 0x106c58 2 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 56) (.exec 0x106c58 (LoadPre 0x106c58 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x106c58 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106c58 2 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x106c5d (movR64M64Effect 0x106c5d 6 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 58) (.exec 0x106c5d (LoadPre 0x106c5d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x106c5d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106c5d 6 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x106c62 (movR64M64Effect 0x106c62 7 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 60) (.exec 0x106c62 (LoadPre 0x106c62 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x106c62 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106c62 7 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x106c67 (StorePre 0x106c67 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x106c67 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x106c67 7 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x106c6c (movR64M64Effect 0x106c6c 7 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 63) (.exec 0x106c6c (LoadPre 0x106c6c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x106c6c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106c6c 7 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x106c71 (StorePre 0x106c71 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x106c71 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x106c71 7 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x106c76 (movR64M64Effect 0x106c76 7 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 66) (.exec 0x106c76 (LoadPre 0x106c76 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x106c76 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106c76 7 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x106c7b (StorePre 0x106c7b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x106c7b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x106c7b 7 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x106c80 (movR64M64Effect 0x106c80 7 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 69) (.exec 0x106c80 (LoadPre 0x106c80 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x106c80 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106c80 7 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.exec 0x106c85 (StorePre 0x106c85 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x106c85 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x106c85 7 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[68, 4]
    (.letOp (n := 71) (.exec 0x106c8a (StorePre 0x106c8a 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x106c8a + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x106c8a 1 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 72) (.exec 0x106c8e (StorePre 0x106c8e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x106c8e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x106c8e 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 73) (.exec 0x106c93 (StorePre 0x106c93 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x106c93 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x106c93 6 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[57, 4]
    (.terminate (.br ⟨.l106c98, RegMap.args [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 74⟩))))))))))))))))))))))

def bytes_l106c54 : List UInt8 :=
  [0x8B, 0x4C, 0x24, 0x44, 0x48, 0x8B, 0x54, 0x24, 0x48, 0x48, 0x8B, 0x74, 0x24, 0x50, 0x48, 0x8B,
    0x7C, 0x24, 0x58, 0x48, 0x89, 0x7C, 0x24, 0x20, 0x48, 0x8B, 0x7C, 0x24, 0x60, 0x48, 0x89, 0x7C,
    0x24, 0x28, 0x48, 0x8B, 0x7C, 0x24, 0x68, 0x48, 0x89, 0x7C, 0x24, 0x30, 0x48, 0x8B, 0x7C, 0x24,
    0x70, 0x48, 0x89, 0x7C, 0x24, 0x38, 0x89, 0x4C, 0x24, 0x0C, 0x48, 0x89, 0x54, 0x24, 0x10, 0x48,
    0x89, 0x74, 0x24, 0x18]

theorem code_l106c54 : ∀ x ∈ codeRange 0x106c54 bytes_l106c54, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6c54 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106c98 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106c98 (movR32M32LowEffect 0x106c98 2 (.sib 4 none 0 (.d8 0x3c))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 54) (.exec 0x106c98 (LoadPre 0x106c98 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x106c98 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x106c98 2 (.sib 4 none 0 (.d8 0x3c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x106c9c (StorePre 0x106c9c 3 (fun s => AddrMode.addr (.base 3 (.d8 0x34)) s (0x106c9c + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x106c9c 2 (.base 3 (.d8 0x34))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[53, 3]
    (.letOp (n := 56) (.out 0x106c9f (movR64M64Effect 0x106c9f 2 (.sib 4 none 0 (.d8 0x35))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 57) (.exec 0x106c9f (LoadPre 0x106c9f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x35)) s (0x106c9f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106c9f 2 (.sib 4 none 0 (.d8 0x35))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x106ca4 (StorePre 0x106ca4 4 (fun s => AddrMode.addr (.base 3 (.d8 0x2d)) s (0x106ca4 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x106ca4 2 (.base 3 (.d8 0x2d))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[56, 3]
    (.letOp (n := 59) (.out 0x106ca8 (movR64M64Effect 0x106ca8 2 (.sib 4 none 0 (.d8 0x2d))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 60) (.exec 0x106ca8 (LoadPre 0x106ca8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2d)) s (0x106ca8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106ca8 2 (.sib 4 none 0 (.d8 0x2d))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x106cad (StorePre 0x106cad 4 (fun s => AddrMode.addr (.base 3 (.d8 0x25)) s (0x106cad + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x106cad 2 (.base 3 (.d8 0x25))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[59, 3]
    (.letOp (n := 62) (.out 0x106cb1 (movR64M64Effect 0x106cb1 2 (.sib 4 none 0 (.d8 0x25))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 63) (.exec 0x106cb1 (LoadPre 0x106cb1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x25)) s (0x106cb1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106cb1 2 (.sib 4 none 0 (.d8 0x25))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x106cb6 (StorePre 0x106cb6 4 (fun s => AddrMode.addr (.base 3 (.d8 0x1d)) s (0x106cb6 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x106cb6 2 (.base 3 (.d8 0x1d))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[62, 3]
    (.letOp (n := 65) (.out 0x106cba (movR64M64Effect 0x106cba 2 (.sib 4 none 0 (.d8 0x1d))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 66) (.exec 0x106cba (LoadPre 0x106cba (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1d)) s (0x106cba + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106cba 2 (.sib 4 none 0 (.d8 0x1d))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x106cbf (StorePre 0x106cbf 4 (fun s => AddrMode.addr (.base 3 (.d8 0x15)) s (0x106cbf + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x106cbf 2 (.base 3 (.d8 0x15))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[65, 3]
    (.letOp (n := 68) (.out 0x106cc3 (movR64M64Effect 0x106cc3 2 (.sib 4 none 0 (.d8 0xd))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 69) (.exec 0x106cc3 (LoadPre 0x106cc3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xd)) s (0x106cc3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106cc3 2 (.sib 4 none 0 (.d8 0xd))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.out 0x106cc8 (movR64M64Effect 0x106cc8 6 (.sib 4 none 0 (.d8 0x15))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 71) (.exec 0x106cc8 (LoadPre 0x106cc8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x15)) s (0x106cc8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106cc8 6 (.sib 4 none 0 (.d8 0x15))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.exec 0x106ccd (StorePre 0x106ccd 4 (fun s => AddrMode.addr (.base 3 (.d8 0xd)) s (0x106ccd + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x106ccd 6 (.base 3 (.d8 0xd))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[70, 3]
    (.letOp (n := 73) (.exec 0x106cd1 (StorePre 0x106cd1 4 (fun s => AddrMode.addr (.base 3 (.d8 0x5)) s (0x106cd1 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x106cd1 2 (.base 3 (.d8 0x5))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[68, 3]
    (.letOp (n := 74) (.exec 0x106cd5 (StorePre 0x106cd5 2 (fun s => AddrMode.addr (.base 3 .none) s (0x106cd5 + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x106cd5 0 (.base 3 .none)) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (.letOp (n := 75) (.exec 0x106cd7 (StorePre 0x106cd7 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x106cd7 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x106cd7 3 1 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[1, 3]
    (.terminate (.br ⟨.l106d6b, RegMap.args [(0, 0), (1, 1), (2, 68), (3, 3), (4, 4), (6, 70), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 76⟩))))))))))))))))))))))))

def bytes_l106c98 : List UInt8 :=
  [0x8B, 0x54, 0x24, 0x3C, 0x89, 0x53, 0x34, 0x48, 0x8B, 0x54, 0x24, 0x35, 0x48, 0x89, 0x53, 0x2D,
    0x48, 0x8B, 0x54, 0x24, 0x2D, 0x48, 0x89, 0x53, 0x25, 0x48, 0x8B, 0x54, 0x24, 0x25, 0x48, 0x89,
    0x53, 0x1D, 0x48, 0x8B, 0x54, 0x24, 0x1D, 0x48, 0x89, 0x53, 0x15, 0x48, 0x8B, 0x54, 0x24, 0x0D,
    0x48, 0x8B, 0x74, 0x24, 0x15, 0x48, 0x89, 0x73, 0x0D, 0x48, 0x89, 0x53, 0x05, 0x89, 0x03, 0x88,
    0x4B, 0x04, 0xE9, 0x8C, 0x00, 0x00, 0x00]

theorem code_l106c98 : ∀ x ∈ codeRange 0x106c98 bytes_l106c98, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6c98 71 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106cdf : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106cdf (leaR64Effect 0x106cdf 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x106cdf (fun s => s.RIP = 0x106cdf) (leaR64Effect 0x106cdf 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x106ce4 (movR64R64Effect 0x106ce4 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 56) (.exec 0x106ce4 (fun s => s.RIP = 0x106ce4) (movR64R64Effect 0x106ce4 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x106ce7 (callEffect (fun _ => 0x106860) 0x106cec) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x106ce7 (PushPre 0x106ce7 5) (callEffect (fun _ => 0x106860) 0x106cec) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x106cec⟩) #v[]
    (.terminate (.call ⟨.l106860, RegMap.args [(3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ { target := .l106cec, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l106cdf : List UInt8 :=
  [0x48, 0x8D, 0x7C, 0x24, 0x08, 0x4C, 0x89, 0xF6, 0xE8, 0x74, 0xFB, 0xFF, 0xFF]

theorem code_l106cdf : ∀ x ∈ codeRange 0x106cdf bytes_l106cdf, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6cdf 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106cec : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106cec (movR32M32LowEffect 0x106cec 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x106cec (LoadPre 0x106cec (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x106cec + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x106cec 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x106cf0 (movzxR32M8Effect 0x106cf0 5 1 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x106cf0 (LoadPre 0x106cf0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x106cf0 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x106cf0 5 1 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x106cf5 (cmpR32Imm8Effect 0x106cf5 3 0 0x2) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[53]
    (.letOp (n := 58) (.exec 0x106cf5 (fun s => s.RIP = 0x106cf5) (cmpR32Imm8Effect 0x106cf5 3 0 0x2) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 59) (.pure (condOp 5)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l106c98, RegMap.args [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l106cfa, RegMap.args [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l106cec : List UInt8 :=
  [0x8B, 0x44, 0x24, 0x08, 0x0F, 0xB6, 0x4C, 0x24, 0x0C, 0x83, 0xF8, 0x02, 0x75, 0x9E]

theorem code_l106cec : ∀ x ∈ codeRange 0x106cec bytes_l106cec, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6cec 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106cfa : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106cfa (movzxR32R8Effect 0x106cfa 3 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[1]
    (.letOp (n := 54) (.exec 0x106cfa (fun s => s.RIP = 0x106cfa) (movzxR32R8Effect 0x106cfa 3 0 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 55) (.out 0x106cfd (shlR32Effect 0x106cfd 4 12 7) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[12]
    (.letOp (n := 56) (.exec 0x106cfd (fun s => s.RIP = 0x106cfd) (shlR32Effect 0x106cfd 4 12 7) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[12]
    (.letOp (n := 57) (.out 0x106d01 (movR32R32Effect 0x106d01 3 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[53]
    (.letOp (n := 58) (.exec 0x106d01 (fun s => s.RIP = 0x106d01) (movR32R32Effect 0x106d01 3 13 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 59) (.out 0x106d04 (andR32Imm8Effect 0x106d04 4 13 0x7f) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[57]
    (.letOp (n := 60) (.exec 0x106d04 (fun s => s.RIP = 0x106d04) (andR32Imm8Effect 0x106d04 4 13 0x7f) (Reg.operands [.gpr 13] [])) #v[57]
    (.letOp (n := 61) (.out 0x106d08 (orR32R32Effect 0x106d08 3 13 12) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 12] []) (.reg (.gpr 13))) #v[59, 55]
    (.letOp (n := 62) (.exec 0x106d08 (fun s => s.RIP = 0x106d08) (orR32R32Effect 0x106d08 3 13 12) (Reg.operands [.gpr 13, .gpr 12] [])) #v[59, 55]
    (.letOp (n := 63) (.out 0x106d0b (testR8R8Effect 0x106d0b 2 0 0) (EffectPart.reads (.flag .SF) [.gpr 0, .gpr 0] []) (.flag .SF)) #v[53, 53]
    (.letOp (n := 64) (.exec 0x106d0b (fun s => s.RIP = 0x106d0b) (testR8R8Effect 0x106d0b 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[53, 53]
    (.letOp (n := 65) (.pure (condOp 8)) #v[63]
    (.terminate (.condBr (Fin.last 65) ⟨.l106d17, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 61), (14, 14), (15, 15), (20, 63), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩ ⟨.l106d0f, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 61), (14, 14), (15, 15), (20, 63), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩))))))))))))))

def bytes_l106cfa : List UInt8 :=
  [0x0F, 0xB6, 0xC1, 0x41, 0xC1, 0xE4, 0x07, 0x41, 0x89, 0xC5, 0x41, 0x83, 0xE5, 0x7F, 0x45, 0x09,
    0xE5, 0x84, 0xC0, 0x78, 0x08]

theorem code_l106cfa : ∀ x ∈ codeRange 0x106cfa bytes_l106cfa, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6cfa 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106d0f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106d0f (movR32R32Effect 0x106d0f 3 15 13) (EffectPart.reads (.reg (.gpr 15)) [.gpr 13] []) (.reg (.gpr 15))) #v[13]
    (.letOp (n := 54) (.exec 0x106d0f (fun s => s.RIP = 0x106d0f) (movR32R32Effect 0x106d0f 3 15 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.terminate (.br ⟨.l106bd0, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l106d0f : List UInt8 :=
  [0x45, 0x89, 0xEF, 0xE9, 0xB9, 0xFE, 0xFF, 0xFF]

theorem code_l106d0f : ∀ x ∈ codeRange 0x106d0f bytes_l106d0f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6d0f 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106d17 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106d17 (leaR64Effect 0x106d17 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x106d17 (fun s => s.RIP = 0x106d17) (leaR64Effect 0x106d17 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x106d1c (movR64R64Effect 0x106d1c 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 56) (.exec 0x106d1c (fun s => s.RIP = 0x106d1c) (movR64R64Effect 0x106d1c 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x106d1f (callEffect (fun _ => 0x106860) 0x106d24) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x106d1f (PushPre 0x106d1f 5) (callEffect (fun _ => 0x106860) 0x106d24) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x106d24⟩) #v[]
    (.terminate (.call ⟨.l106860, RegMap.args [(3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ { target := .l106d24, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l106d17 : List UInt8 :=
  [0x48, 0x8D, 0x7C, 0x24, 0x08, 0x4C, 0x89, 0xF6, 0xE8, 0x3C, 0xFB, 0xFF, 0xFF]

theorem code_l106d17 : ∀ x ∈ codeRange 0x106d17 bytes_l106d17, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6d17 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106d24 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106d24 (movR32M32LowEffect 0x106d24 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x106d24 (LoadPre 0x106d24 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x106d24 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x106d24 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x106d28 (movzxR32M8Effect 0x106d28 5 1 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x106d28 (LoadPre 0x106d28 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x106d28 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x106d28 5 1 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x106d2d (cmpR32Imm8Effect 0x106d2d 3 0 0x2) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[53]
    (.letOp (n := 58) (.exec 0x106d2d (fun s => s.RIP = 0x106d2d) (cmpR32Imm8Effect 0x106d2d 3 0 0x2) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 59) (.pure (condOp 5)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l106c98, RegMap.args [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l106d36, RegMap.args [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l106d24 : List UInt8 :=
  [0x8B, 0x44, 0x24, 0x08, 0x0F, 0xB6, 0x4C, 0x24, 0x0C, 0x83, 0xF8, 0x02, 0x0F, 0x85, 0x62, 0xFF,
    0xFF, 0xFF]

theorem code_l106d24 : ∀ x ∈ codeRange 0x106d24 bytes_l106d24, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6d24 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106d36 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106d36 (movzxR32R8Effect 0x106d36 3 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[1]
    (.letOp (n := 54) (.exec 0x106d36 (fun s => s.RIP = 0x106d36) (movzxR32R8Effect 0x106d36 3 0 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 55) (.out 0x106d39 (shlR32Effect 0x106d39 4 13 7) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[13]
    (.letOp (n := 56) (.exec 0x106d39 (fun s => s.RIP = 0x106d39) (shlR32Effect 0x106d39 4 13 7) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[13]
    (.letOp (n := 57) (.out 0x106d3d (movR32R32Effect 0x106d3d 3 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[53]
    (.letOp (n := 58) (.exec 0x106d3d (fun s => s.RIP = 0x106d3d) (movR32R32Effect 0x106d3d 3 12 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 59) (.out 0x106d40 (andR32Imm8Effect 0x106d40 4 12 0x7f) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[57]
    (.letOp (n := 60) (.exec 0x106d40 (fun s => s.RIP = 0x106d40) (andR32Imm8Effect 0x106d40 4 12 0x7f) (Reg.operands [.gpr 12] [])) #v[57]
    (.letOp (n := 61) (.out 0x106d44 (orR32R32Effect 0x106d44 3 12 13) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 13] []) (.reg (.gpr 12))) #v[59, 55]
    (.letOp (n := 62) (.exec 0x106d44 (fun s => s.RIP = 0x106d44) (orR32R32Effect 0x106d44 3 12 13) (Reg.operands [.gpr 12, .gpr 13] [])) #v[59, 55]
    (.letOp (n := 63) (.out 0x106d47 (testR8R8Effect 0x106d47 2 0 0) (EffectPart.reads (.flag .SF) [.gpr 0, .gpr 0] []) (.flag .SF)) #v[53, 53]
    (.letOp (n := 64) (.exec 0x106d47 (fun s => s.RIP = 0x106d47) (testR8R8Effect 0x106d47 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[53, 53]
    (.letOp (n := 65) (.pure (condOp 9)) #v[63]
    (.terminate (.condBr (Fin.last 65) ⟨.l106c4c, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 55), (14, 14), (15, 15), (20, 63), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩ ⟨.l106d4f, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 55), (14, 14), (15, 15), (20, 63), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩))))))))))))))

def bytes_l106d36 : List UInt8 :=
  [0x0F, 0xB6, 0xC1, 0x41, 0xC1, 0xE5, 0x07, 0x41, 0x89, 0xC4, 0x41, 0x83, 0xE4, 0x7F, 0x45, 0x09,
    0xEC, 0x84, 0xC0, 0x0F, 0x89, 0xFD, 0xFE, 0xFF, 0xFF]

theorem code_l106d36 : ∀ x ∈ codeRange 0x106d36 bytes_l106d36, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6d36 25 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106d4f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106d4f (cmpR8Imm8Effect 0x106d4f 4 15 0xf) (EffectPart.reads (.flag .CF) [.gpr 15] []) (.flag .CF)) #v[15]
    (.letOp (n := 54) (.out 0x106d4f (cmpR8Imm8Effect 0x106d4f 4 15 0xf) (EffectPart.reads (.flag .ZF) [.gpr 15] []) (.flag .ZF)) #v[15]
    (.letOp (n := 55) (.exec 0x106d4f (fun s => s.RIP = 0x106d4f) (cmpR8Imm8Effect 0x106d4f 4 15 0xf) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 56) (.pure (condOp 6)) #v[53, 54]
    (.terminate (.condBr (Fin.last 56) ⟨.l106d7a, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩ ⟨.l106d55, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l106d4f : List UInt8 :=
  [0x41, 0x80, 0xFF, 0x0F, 0x76, 0x25]

theorem code_l106d4f : ∀ x ∈ codeRange 0x106d4f bytes_l106d4f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6d4f 6 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106d55 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x106d55 (StorePre 0x106d55 5 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x106d55 + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x106d55 (.base 14 (.d8 0x20)) 0x1) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 54) (.out 0x106d5a (movR32M32Effect 0x106d5a 0 (.base 14 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[14]
    (.letOp (n := 55) (.exec 0x106d5a (LoadPre 0x106d5a (fun s => AddrMode.addr (.base 14 (.d8 0x1c)) s (0x106d5a + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x106d5a 0 (.base 14 (.d8 0x1c))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 56) (.exec 0x106d5e (StorePre 0x106d5e 6 (fun s => AddrMode.addr (.base 3 .none) s (0x106d5e + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x106d5e 6 (.base 3 .none) 0x1) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 57) (.exec 0x106d64 (StorePre 0x106d64 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x106d64 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x106d64 0 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[54, 3]
    (.letOp (n := 58) (.exec 0x106d67 (StorePre 0x106d67 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x106d67 + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x106d67 (.base 3 (.d8 0x8)) 0x10) (Reg.operands [.gpr 3] [])) #v[3]
    (.terminate (.br ⟨.l106d6b, RegMap.args [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l106d55 : List UInt8 :=
  [0x41, 0xC6, 0x46, 0x20, 0x01, 0x41, 0x8B, 0x46, 0x1C, 0xC7, 0x03, 0x01, 0x00, 0x00, 0x00, 0x89,
    0x43, 0x04, 0xC6, 0x43, 0x08, 0x10]

theorem code_l106d55 : ∀ x ∈ codeRange 0x106d55 bytes_l106d55, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6d55 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106d6b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106d6b (addR64Imm8Effect 0x106d6b 4 0x78) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 54) (.exec 0x106d6b (fun s => s.RIP = 0x106d6b) (addR64Imm8Effect 0x106d6b 4 0x78) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x106d6f (popR64Effect 0x106d6f 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[53]
    (.letOp (n := 56) (.out 0x106d6f (popR64Effect 0x106d6f 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[53]
    (.letOp (n := 57) (.exec 0x106d6f (PopPre 0x106d6f) (popR64Effect 0x106d6f 1 3) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 58) (.out 0x106d70 (popR64Effect 0x106d70 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[56]
    (.letOp (n := 59) (.out 0x106d70 (popR64Effect 0x106d70 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[56]
    (.letOp (n := 60) (.exec 0x106d70 (PopPre 0x106d70) (popR64Effect 0x106d70 2 12) (Reg.operands [.gpr 4] [])) #v[56]
    (.letOp (n := 61) (.out 0x106d72 (popR64Effect 0x106d72 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[59]
    (.letOp (n := 62) (.out 0x106d72 (popR64Effect 0x106d72 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 63) (.exec 0x106d72 (PopPre 0x106d72) (popR64Effect 0x106d72 2 13) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 64) (.out 0x106d74 (popR64Effect 0x106d74 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[62]
    (.letOp (n := 65) (.out 0x106d74 (popR64Effect 0x106d74 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[62]
    (.letOp (n := 66) (.exec 0x106d74 (PopPre 0x106d74) (popR64Effect 0x106d74 2 14) (Reg.operands [.gpr 4] [])) #v[62]
    (.letOp (n := 67) (.out 0x106d76 (popR64Effect 0x106d76 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[65]
    (.letOp (n := 68) (.out 0x106d76 (popR64Effect 0x106d76 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 69) (.exec 0x106d76 (PopPre 0x106d76) (popR64Effect 0x106d76 2 15) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 70) (.out 0x106d78 (popR64Effect 0x106d78 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[68]
    (.letOp (n := 71) (.out 0x106d78 (popR64Effect 0x106d78 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[68]
    (.letOp (n := 72) (.exec 0x106d78 (PopPre 0x106d78) (popR64Effect 0x106d78 1 5) (Reg.operands [.gpr 4] [])) #v[68]
    (.letOp (n := 73) (.out 0x106d79 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[71]
    (.letOp (n := 74) (.out 0x106d79 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[71]
    (.letOp (n := 75) (.exec 0x106d79 (RetPre 0x106d79) (retEffect) (Reg.operands [.gpr 4] [])) #v[71]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 2), (3, 55), (4, 74), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 76) (some ⟨73, by decide⟩)))))))))))))))))))))))))

def bytes_l106d6b : List UInt8 :=
  [0x48, 0x83, 0xC4, 0x78, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l106d6b : ∀ x ∈ codeRange 0x106d6b bytes_l106d6b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6d6b 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106d7a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106d7a (leaR64Effect 0x106d7a 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x106d7a (fun s => s.RIP = 0x106d7a) (leaR64Effect 0x106d7a 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x106d7f (movR64R64Effect 0x106d7f 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 56) (.exec 0x106d7f (fun s => s.RIP = 0x106d7f) (movR64R64Effect 0x106d7f 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x106d82 (callEffect (fun _ => 0x106860) 0x106d87) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x106d82 (PushPre 0x106d82 5) (callEffect (fun _ => 0x106860) 0x106d87) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x106d87⟩) #v[]
    (.terminate (.call ⟨.l106860, RegMap.args [(3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ { target := .l106d87, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l106d7a : List UInt8 :=
  [0x48, 0x8D, 0x7C, 0x24, 0x08, 0x4C, 0x89, 0xF6, 0xE8, 0xD9, 0xFA, 0xFF, 0xFF]

theorem code_l106d7a : ∀ x ∈ codeRange 0x106d7a bytes_l106d7a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6d7a 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106d87 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106d87 (movR32M32LowEffect 0x106d87 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x106d87 (LoadPre 0x106d87 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x106d87 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x106d87 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x106d8b (movzxR32M8Effect 0x106d8b 5 1 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x106d8b (LoadPre 0x106d8b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x106d8b + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x106d8b 5 1 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x106d90 (cmpR32Imm8Effect 0x106d90 3 0 0x2) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[53]
    (.letOp (n := 58) (.exec 0x106d90 (fun s => s.RIP = 0x106d90) (cmpR32Imm8Effect 0x106d90 3 0 0x2) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 59) (.pure (condOp 5)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l106c98, RegMap.args [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l106d99, RegMap.args [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l106d87 : List UInt8 :=
  [0x8B, 0x44, 0x24, 0x08, 0x0F, 0xB6, 0x4C, 0x24, 0x0C, 0x83, 0xF8, 0x02, 0x0F, 0x85, 0xFF, 0xFE,
    0xFF, 0xFF]

theorem code_l106d87 : ∀ x ∈ codeRange 0x106d87 bytes_l106d87, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6d87 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106d99 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106d99 (testR8R8Effect 0x106d99 2 1 1) (EffectPart.reads (.flag .SF) [.gpr 1, .gpr 1] []) (.flag .SF)) #v[1, 1]
    (.letOp (n := 54) (.exec 0x106d99 (fun s => s.RIP = 0x106d99) (testR8R8Effect 0x106d99 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[1, 1]
    (.letOp (n := 55) (.pure (condOp 8)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l106d55, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (20, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l106d9d, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (20, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l106d99 : List UInt8 :=
  [0x84, 0xC9, 0x78, 0xB8]

theorem code_l106d99 : ∀ x ∈ codeRange 0x106d99 bytes_l106d99, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6d99 4 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106d9d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106d9d (movzxR32R8Effect 0x106d9d 4 15 1) (EffectPart.reads (.reg (.gpr 15)) [.gpr 1] []) (.reg (.gpr 15))) #v[1]
    (.letOp (n := 54) (.exec 0x106d9d (fun s => s.RIP = 0x106d9d) (movzxR32R8Effect 0x106d9d 4 15 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 55) (.out 0x106da1 (shlR32Effect 0x106da1 4 12 7) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[12]
    (.letOp (n := 56) (.exec 0x106da1 (fun s => s.RIP = 0x106da1) (shlR32Effect 0x106da1 4 12 7) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[12]
    (.letOp (n := 57) (.out 0x106da5 (andR32Imm8Effect 0x106da5 4 15 0x7f) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15] []) (.reg (.gpr 15))) #v[53]
    (.letOp (n := 58) (.exec 0x106da5 (fun s => s.RIP = 0x106da5) (andR32Imm8Effect 0x106da5 4 15 0x7f) (Reg.operands [.gpr 15] [])) #v[53]
    (.letOp (n := 59) (.out 0x106da9 (orR32R32Effect 0x106da9 3 15 12) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 12] []) (.reg (.gpr 15))) #v[57, 55]
    (.letOp (n := 60) (.exec 0x106da9 (fun s => s.RIP = 0x106da9) (orR32R32Effect 0x106da9 3 15 12) (Reg.operands [.gpr 15, .gpr 12] [])) #v[57, 55]
    (.terminate (.br ⟨.l106bd0, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩)))))))))

def bytes_l106d9d : List UInt8 :=
  [0x44, 0x0F, 0xB6, 0xF9, 0x41, 0xC1, 0xE4, 0x07, 0x41, 0x83, 0xE7, 0x7F, 0x45, 0x09, 0xE7, 0xE9,
    0x1F, 0xFE, 0xFF, 0xFF]

theorem code_l106d9d : ∀ x ∈ codeRange 0x106d9d bytes_l106d9d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6d9d 20 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106db1 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106db1 (movR32Imm32Effect 0x106db1 5 7 0x1) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 54) (.exec 0x106db1 (fun s => s.RIP = 0x106db1) (movR32Imm32Effect 0x106db1 5 7 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x106db6 (movR64Imm32Effect 0x106db6 2 0x202530) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 56) (.exec 0x106db6 (fun s => s.RIP = 0x106db6) (movR64Imm32Effect 0x106db6 2 0x202530) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x106dbd (callEffect (fun _ => 0x129c90) 0x106dc2) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x106dbd (PushPre 0x106dbd 5) (callEffect (fun _ => 0x129c90) 0x106dc2) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x106dc2⟩) #v[]
    (.terminate (.call ⟨.l129c90, RegMap.args [(2, 55), (4, 57), (5, 5), (6, 6), (7, 53)] 60⟩ { target := .l106dc2, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l106db1 : List UInt8 :=
  [0xBF, 0x01, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC2, 0x30, 0x25, 0x20, 0x00, 0xE8, 0xCE, 0x2E, 0x02,
    0x00]

theorem code_l106db1 : ∀ x ∈ codeRange 0x106db1 bytes_l106db1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6db1 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106dc2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x106dc2 (fun s => s.RIP = 0x106dc2) (fun _ => nopEffect 0x106dc2 10) (Reg.operands [] [])) #v[]
    (.letOp (n := 54) (.exec 0x106dcc (fun s => s.RIP = 0x106dcc) (fun _ => nopEffect 0x106dcc 4) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l106dd0, RegMap.args [(3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l106dc2 : List UInt8 :=
  [0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00, 0x0F, 0x1F, 0x40, 0x00]

theorem code_l106dc2 : ∀ x ∈ codeRange 0x106dc2 bytes_l106dc2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6dc2 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106dd0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106dd0 (pushR64Effect 0x106dd0 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x106dd0 (PushPre 0x106dd0 1) (pushR64Effect 0x106dd0 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x106dd1 (pushR64Effect 0x106dd1 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x106dd1 (PushPre 0x106dd1 2) (pushR64Effect 0x106dd1 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x106dd3 (pushR64Effect 0x106dd3 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x106dd3 (PushPre 0x106dd3 2) (pushR64Effect 0x106dd3 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x106dd5 (pushR64Effect 0x106dd5 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x106dd5 (PushPre 0x106dd5 2) (pushR64Effect 0x106dd5 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x106dd7 (pushR64Effect 0x106dd7 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x106dd7 (PushPre 0x106dd7 2) (pushR64Effect 0x106dd7 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x106dd9 (pushR64Effect 0x106dd9 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x106dd9 (PushPre 0x106dd9 1) (pushR64Effect 0x106dd9 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x106dda (subR64Imm8Effect 0x106dda 4 0x48) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x106dda (fun s => s.RIP = 0x106dda) (subR64Imm8Effect 0x106dda 4 0x48) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x106dde (movR64R64Effect 0x106dde 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 68) (.exec 0x106dde (fun s => s.RIP = 0x106dde) (movR64R64Effect 0x106dde 0 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 69) (.out 0x106de1 (movR64R64Effect 0x106de1 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 70) (.exec 0x106de1 (fun s => s.RIP = 0x106de1) (movR64R64Effect 0x106de1 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 71) (.exec 0x106de4 (StorePre 0x106de4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x106de4 + BitVec.ofNat 64 8)) 4) (movM32Imm32Effect 0x106de4 8 (.sib 4 none 0 (.d8 0x24)) 0x100) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 72) (.exec 0x106dec (StorePre 0x106dec 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x106dec + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x106dec (.sib 4 none 0 (.d8 0x40)) 0x0) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 73) (.exec 0x106df5 (StorePre 0x106df5 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x106df5 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x106df5 (.sib 4 none 0 (.d8 0x38)) 0x0) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 74) (.exec 0x106dfe (StorePre 0x106dfe 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x106dfe + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x106dfe (.sib 4 none 0 (.d8 0x30)) 0x0) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 75) (.exec 0x106e07 (StorePre 0x106e07 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x106e07 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x106e07 (.sib 4 none 0 (.d8 0x28)) 0x0) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 76) (.out 0x106e10 (leaR64Effect 0x106e10 2 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[65]
    (.letOp (n := 77) (.exec 0x106e10 (fun s => s.RIP = 0x106e10) (leaR64Effect 0x106e10 2 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 78) (.out 0x106e15 (movR32Imm32Effect 0x106e15 5 6 0x20) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 79) (.exec 0x106e15 (fun s => s.RIP = 0x106e15) (movR32Imm32Effect 0x106e15 5 6 0x20) (Reg.operands [] [])) #v[]
    (.letOp (n := 80) (.out 0x106e1a (movR32Imm32Effect 0x106e1a 5 1 0x4) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 81) (.exec 0x106e1a (fun s => s.RIP = 0x106e1a) (movR32Imm32Effect 0x106e1a 5 1 0x4) (Reg.operands [] [])) #v[]
    (.letOp (n := 82) (.out 0x106e1f (movR64R64Effect 0x106e1f 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[67]
    (.letOp (n := 83) (.exec 0x106e1f (fun s => s.RIP = 0x106e1f) (movR64R64Effect 0x106e1f 7 0) (Reg.operands [.gpr 0] [])) #v[67]
    (.letOp (n := 84) (.out 0x106e22 (movR32Imm32Effect 0x106e22 6 8 0x100) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 85) (.exec 0x106e22 (fun s => s.RIP = 0x106e22) (movR32Imm32Effect 0x106e22 6 8 0x100) (Reg.operands [] [])) #v[]
    (.letOp (n := 86) (.out 0x106e28 (callEffect (fun _ => 0x127d70) 0x106e2d) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 87) (.exec 0x106e28 (PushPre 0x106e28 5) (callEffect (fun _ => 0x127d70) 0x106e2d) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 88) (.const ⟨64, 0x106e2d⟩) #v[]
    (.terminate (.call ⟨.l127d70, RegMap.args [(0, 67), (1, 80), (2, 76), (3, 69), (4, 86), (5, 5), (6, 78), (7, 82), (8, 84), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 89⟩ { target := .l106e2d, kept := #v[], arity := rfl, guard := some (Fin.last 88) })))))))))))))))))))))))))))))))))))))

def bytes_l106dd0 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x83, 0xEC, 0x48, 0x48, 0x89,
    0xF0, 0x48, 0x89, 0xFB, 0xC7, 0x44, 0x24, 0x24, 0x00, 0x01, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24,
    0x40, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x38, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7,
    0x44, 0x24, 0x30, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x28, 0x00, 0x00, 0x00, 0x00,
    0x48, 0x8D, 0x54, 0x24, 0x28, 0xBE, 0x20, 0x00, 0x00, 0x00, 0xB9, 0x04, 0x00, 0x00, 0x00, 0x48,
    0x89, 0xC7, 0x41, 0xB8, 0x00, 0x01, 0x00, 0x00, 0xE8, 0x43, 0x0F, 0x02, 0x00]

theorem code_l106dd0 : ∀ x ∈ codeRange 0x106dd0 bytes_l106dd0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6dd0 93 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106e2d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106e2d (cmpAlImm8Effect 0x106e2d 0xff) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[0]
    (.letOp (n := 54) (.exec 0x106e2d (fun s => s.RIP = 0x106e2d) (cmpAlImm8Effect 0x106e2d 0xff) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l106f70, RegMap.args [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l106e35, RegMap.args [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l106e2d : List UInt8 :=
  [0x3C, 0xFF, 0x0F, 0x85, 0x3B, 0x01, 0x00, 0x00]

theorem code_l106e2d : ∀ x ∈ codeRange 0x106e2d bytes_l106e2d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6e2d 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106e35_2 : Block Op Label signature Reg.count 129 :=
  .letOp (n := 129) (.out 0x106ece (shrR64Effect 0x106ece 4 2 63) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[127]
    (.letOp (n := 130) (.exec 0x106ece (fun s => s.RIP = 0x106ece) (shrR64Effect 0x106ece 4 2 63) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[127]
    (.letOp (n := 131) (.exec 0x106ed2 (StorePre 0x106ed2 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x106ed2 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x106ed2 2 (.sib 4 none 0 .none)) (Reg.operands [.gpr 2, .gpr 4] [])) #v[129, 4]
    (.letOp (n := 132) (.out 0x106ed6 (movzxR32M8Effect 0x106ed6 4 0 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 133) (.exec 0x106ed6 (LoadPre 0x106ed6 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x106ed6 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x106ed6 4 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 134) (.out 0x106eda (andAlImm8Effect 0x106eda 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[132]
    (.letOp (n := 135) (.exec 0x106eda (fun s => s.RIP = 0x106eda) (andAlImm8Effect 0x106eda 0x1) (Reg.operands [.gpr 0] [])) #v[132]
    (.letOp (n := 136) (.out 0x106edc (movzxR32R8Effect 0x106edc 3 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[134]
    (.letOp (n := 137) (.exec 0x106edc (fun s => s.RIP = 0x106edc) (movzxR32R8Effect 0x106edc 3 7 0) (Reg.operands [.gpr 0] [])) #v[134]
    (.letOp (n := 138) (.out 0x106edf (callEffect (fun _ => 0x127d50) 0x106ee4) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 139) (.exec 0x106edf (PushPre 0x106edf 5) (callEffect (fun _ => 0x127d50) 0x106ee4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 140) (.const ⟨64, 0x106ee4⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(0, 134), (1, 121), (2, 129), (3, 3), (4, 138), (5, 5), (6, 87), (7, 136), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 59), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 141⟩ { target := .l106ee4, kept := #v[], arity := rfl, guard := some (Fin.last 140) })))))))))))))

def bytes_l106e35_2 : List UInt8 :=
  [0x48, 0xC1, 0xEA, 0x3F, 0x48, 0x89, 0x14, 0x24, 0x0F, 0xB6, 0x04, 0x24, 0x24, 0x01, 0x0F, 0xB6,
    0xF8, 0xE8, 0x6C, 0x0E, 0x02, 0x00]

theorem code_l106e35_2 : ∀ x ∈ codeRange 0x106ece bytes_l106e35_2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6ece 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106e35_1 : Block Op Label signature Reg.count 91 :=
  .letOp (n := 91) (.out 0x106e89 (notR64Effect 0x106e89 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[89]
    (.letOp (n := 92) (.exec 0x106e89 (fun s => s.RIP = 0x106e89) (notR64Effect 0x106e89 2) (Reg.operands [.gpr 2] [])) #v[89]
    (.letOp (n := 93) (.out 0x106e8c (orR64R64Effect 0x106e8c 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[91, 87]
    (.letOp (n := 94) (.exec 0x106e8c (fun s => s.RIP = 0x106e8c) (orR64R64Effect 0x106e8c 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[91, 87]
    (.letOp (n := 95) (.out 0x106e8f (shrR64Effect 0x106e8f 4 2 63) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[93]
    (.letOp (n := 96) (.exec 0x106e8f (fun s => s.RIP = 0x106e8f) (shrR64Effect 0x106e8f 4 2 63) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[93]
    (.letOp (n := 97) (.exec 0x106e93 (StorePre 0x106e93 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x106e93 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x106e93 2 (.sib 4 none 0 .none)) (Reg.operands [.gpr 2, .gpr 4] [])) #v[95, 4]
    (.letOp (n := 98) (.out 0x106e97 (subR64M64Effect 0x106e97 1 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 4] []) (.reg (.gpr 1))) #v[75, 4]
    (.letOp (n := 99) (.exec 0x106e97 (LoadPre 0x106e97 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x106e97 + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x106e97 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 1, .gpr 4] [])) #v[75, 4]
    (.letOp (n := 100) (.out 0x106e9b (sarR64Effect 0x106e9b 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[98]
    (.letOp (n := 101) (.exec 0x106e9b (fun s => s.RIP = 0x106e9b) (sarR64Effect 0x106e9b 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[98]
    (.letOp (n := 102) (.out 0x106e9f (movR64R64Effect 0x106e9f 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12] []) (.reg (.gpr 2))) #v[57]
    (.letOp (n := 103) (.exec 0x106e9f (fun s => s.RIP = 0x106e9f) (movR64R64Effect 0x106e9f 2 12) (Reg.operands [.gpr 12] [])) #v[57]
    (.letOp (n := 104) (.out 0x106ea2 (notR64Effect 0x106ea2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[102]
    (.letOp (n := 105) (.exec 0x106ea2 (fun s => s.RIP = 0x106ea2) (notR64Effect 0x106ea2 2) (Reg.operands [.gpr 2] [])) #v[102]
    (.letOp (n := 106) (.out 0x106ea5 (addR64R64Effect 0x106ea5 1 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 12] []) (.reg (.gpr 1))) #v[100, 57]
    (.letOp (n := 107) (.exec 0x106ea5 (fun s => s.RIP = 0x106ea5) (addR64R64Effect 0x106ea5 1 12) (Reg.operands [.gpr 1, .gpr 12] [])) #v[100, 57]
    (.letOp (n := 108) (.out 0x106ea8 (addR64Imm8Effect 0x106ea8 1 0x2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[106]
    (.letOp (n := 109) (.exec 0x106ea8 (fun s => s.RIP = 0x106ea8) (addR64Imm8Effect 0x106ea8 1 0x2) (Reg.operands [.gpr 1] [])) #v[106]
    (.letOp (n := 110) (.out 0x106eac (orR64R64Effect 0x106eac 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[108, 104]
    (.letOp (n := 111) (.exec 0x106eac (fun s => s.RIP = 0x106eac) (orR64R64Effect 0x106eac 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[108, 104]
    (.letOp (n := 112) (.out 0x106eaf (shrR64Effect 0x106eaf 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[110]
    (.letOp (n := 113) (.exec 0x106eaf (fun s => s.RIP = 0x106eaf) (shrR64Effect 0x106eaf 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[110]
    (.letOp (n := 114) (.exec 0x106eb3 (StorePre 0x106eb3 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x106eb3 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x106eb3 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 1, .gpr 4] [])) #v[112, 4]
    (.letOp (n := 115) (.out 0x106eb7 (movR64M64Effect 0x106eb7 1 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 116) (.exec 0x106eb7 (LoadPre 0x106eb7 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x106eb7 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x106eb7 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 117) (.out 0x106ebb (decR64Effect 0x106ebb 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[115]
    (.letOp (n := 118) (.exec 0x106ebb (fun s => s.RIP = 0x106ebb) (decR64Effect 0x106ebb 1) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[115]
    (.letOp (n := 119) (.out 0x106ebe (shrR64Effect 0x106ebe 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[117]
    (.letOp (n := 120) (.exec 0x106ebe (fun s => s.RIP = 0x106ebe) (shrR64Effect 0x106ebe 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[117]
    (.letOp (n := 121) (.out 0x106ec2 (addR64R64Effect 0x106ec2 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 13] []) (.reg (.gpr 1))) #v[119, 59]
    (.letOp (n := 122) (.exec 0x106ec2 (fun s => s.RIP = 0x106ec2) (addR64R64Effect 0x106ec2 1 13) (Reg.operands [.gpr 1, .gpr 13] [])) #v[119, 59]
    (.letOp (n := 123) (.out 0x106ec5 (movR64R64Effect 0x106ec5 2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13] []) (.reg (.gpr 2))) #v[59]
    (.letOp (n := 124) (.exec 0x106ec5 (fun s => s.RIP = 0x106ec5) (movR64R64Effect 0x106ec5 2 13) (Reg.operands [.gpr 13] [])) #v[59]
    (.letOp (n := 125) (.out 0x106ec8 (notR64Effect 0x106ec8 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[123]
    (.letOp (n := 126) (.exec 0x106ec8 (fun s => s.RIP = 0x106ec8) (notR64Effect 0x106ec8 2) (Reg.operands [.gpr 2] [])) #v[123]
    (.letOp (n := 127) (.out 0x106ecb (orR64R64Effect 0x106ecb 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[125, 121]
    (.letOp (n := 128) (.exec 0x106ecb (fun s => s.RIP = 0x106ecb) (orR64R64Effect 0x106ecb 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[125, 121]
    (b_l106e35_2))))))))))))))))))))))))))))))))))))))

def bytes_l106e35_1 : List UInt8 :=
  [0x48, 0xF7, 0xD2, 0x48, 0x09, 0xF2, 0x48, 0xC1, 0xEA, 0x3F, 0x48, 0x89, 0x14, 0x24, 0x48, 0x2B,
    0x0C, 0x24, 0x48, 0xC1, 0xF9, 0x3F, 0x4C, 0x89, 0xE2, 0x48, 0xF7, 0xD2, 0x4C, 0x01, 0xE1, 0x48,
    0x83, 0xC1, 0x02, 0x48, 0x09, 0xD1, 0x48, 0xC1, 0xE9, 0x3F, 0x48, 0x89, 0x0C, 0x24, 0x48, 0x8B,
    0x0C, 0x24, 0x48, 0xFF, 0xC9, 0x48, 0xC1, 0xE9, 0x3F, 0x4C, 0x01, 0xE9, 0x4C, 0x89, 0xEA, 0x48,
    0xF7, 0xD2, 0x48, 0x09, 0xCA] ++ bytes_l106e35_2

theorem code_l106e35_1 : ∀ x ∈ codeRange 0x106e89 bytes_l106e35_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x6e89 69 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l106e35_2

@[cfg_block] def b_l106e35 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106e35 (movR64M64Effect 0x106e35 14 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 54) (.exec 0x106e35 (LoadPre 0x106e35 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x106e35 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106e35 14 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x106e3a (movR64M64Effect 0x106e3a 15 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 56) (.exec 0x106e3a (LoadPre 0x106e3a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x106e3a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106e3a 15 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x106e3f (movR64M64Effect 0x106e3f 12 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 58) (.exec 0x106e3f (LoadPre 0x106e3f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x106e3f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106e3f 12 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x106e44 (movR64M64Effect 0x106e44 13 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 60) (.exec 0x106e44 (LoadPre 0x106e44 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x106e44 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106e44 13 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x106e49 (movR64Imm64Effect 0x106e49 0 0x402da1732fc9bebf) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 62) (.exec 0x106e49 (fun s => s.RIP = 0x106e49) (movR64Imm64Effect 0x106e49 0 0x402da1732fc9bebf) (Reg.operands [] [])) #v[]
    (.letOp (n := 63) (.out 0x106e53 (addR64R64Effect 0x106e53 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[61, 53]
    (.letOp (n := 64) (.exec 0x106e53 (fun s => s.RIP = 0x106e53) (addR64R64Effect 0x106e53 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[61, 53]
    (.letOp (n := 65) (.out 0x106e56 (movR64R64Effect 0x106e56 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 66) (.exec 0x106e56 (fun s => s.RIP = 0x106e56) (movR64R64Effect 0x106e56 1 14) (Reg.operands [.gpr 14] [])) #v[53]
    (.letOp (n := 67) (.out 0x106e59 (notR64Effect 0x106e59 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 68) (.exec 0x106e59 (fun s => s.RIP = 0x106e59) (notR64Effect 0x106e59 1) (Reg.operands [.gpr 1] [])) #v[65]
    (.letOp (n := 69) (.out 0x106e5c (orR64R64Effect 0x106e5c 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[67, 63]
    (.letOp (n := 70) (.exec 0x106e5c (fun s => s.RIP = 0x106e5c) (orR64R64Effect 0x106e5c 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[67, 63]
    (.letOp (n := 71) (.out 0x106e5f (shrR64Effect 0x106e5f 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[69]
    (.letOp (n := 72) (.exec 0x106e5f (fun s => s.RIP = 0x106e5f) (shrR64Effect 0x106e5f 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[69]
    (.letOp (n := 73) (.exec 0x106e63 (StorePre 0x106e63 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x106e63 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x106e63 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 1, .gpr 4] [])) #v[71, 4]
    (.letOp (n := 74) (.exec 0x106e67 (fun s => s.RIP = 0x106e67) (movR64R64Effect 0x106e67 0 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.out 0x106e6a (xorR32R32Effect 0x106e6a 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[71, 71]
    (.letOp (n := 76) (.exec 0x106e6a (fun s => s.RIP = 0x106e6a) (xorR32R32Effect 0x106e6a 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[71, 71]
    (.letOp (n := 77) (.out 0x106e6c (xorR32R32Effect 0x106e6c 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[2, 2]
    (.letOp (n := 78) (.exec 0x106e6c (fun s => s.RIP = 0x106e6c) (xorR32R32Effect 0x106e6c 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 79) (.out 0x106e6e (subR64M64Effect 0x106e6e 2 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 4] []) (.reg (.gpr 2))) #v[77, 4]
    (.letOp (n := 80) (.exec 0x106e6e (LoadPre 0x106e6e (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x106e6e + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x106e6e 2 (.sib 4 none 0 .none)) (Reg.operands [.gpr 2, .gpr 4] [])) #v[77, 4]
    (.letOp (n := 81) (.out 0x106e72 (sarR64Effect 0x106e72 4 2 63) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[79]
    (.letOp (n := 82) (.exec 0x106e72 (fun s => s.RIP = 0x106e72) (sarR64Effect 0x106e72 4 2 63) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[79]
    (.letOp (n := 83) (.out 0x106e76 (movR64Imm64Effect 0x106e76 6 0x4551231950b75fc5) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 84) (.exec 0x106e76 (fun s => s.RIP = 0x106e76) (movR64Imm64Effect 0x106e76 6 0x4551231950b75fc5) (Reg.operands [] [])) #v[]
    (.letOp (n := 85) (.out 0x106e80 (addR64R64Effect 0x106e80 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 15] []) (.reg (.gpr 6))) #v[83, 55]
    (.letOp (n := 86) (.exec 0x106e80 (fun s => s.RIP = 0x106e80) (addR64R64Effect 0x106e80 6 15) (Reg.operands [.gpr 6, .gpr 15] [])) #v[83, 55]
    (.letOp (n := 87) (.out 0x106e83 (addR64R64Effect 0x106e83 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[85, 81]
    (.letOp (n := 88) (.exec 0x106e83 (fun s => s.RIP = 0x106e83) (addR64R64Effect 0x106e83 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[85, 81]
    (.letOp (n := 89) (.out 0x106e86 (movR64R64Effect 0x106e86 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15] []) (.reg (.gpr 2))) #v[55]
    (.letOp (n := 90) (.exec 0x106e86 (fun s => s.RIP = 0x106e86) (movR64R64Effect 0x106e86 2 15) (Reg.operands [.gpr 15] [])) #v[55]
    (b_l106e35_1))))))))))))))))))))))))))))))))))))))

def bytes_l106e35 : List UInt8 :=
  [0x4C, 0x8B, 0x74, 0x24, 0x28, 0x4C, 0x8B, 0x7C, 0x24, 0x30, 0x4C, 0x8B, 0x64, 0x24, 0x38, 0x4C,
    0x8B, 0x6C, 0x24, 0x40, 0x48, 0xB8, 0xBF, 0xBE, 0xC9, 0x2F, 0x73, 0xA1, 0x2D, 0x40, 0x4C, 0x01,
    0xF0, 0x4C, 0x89, 0xF1, 0x48, 0xF7, 0xD1, 0x48, 0x09, 0xC1, 0x48, 0xC1, 0xE9, 0x3F, 0x48, 0x89,
    0x0C, 0x24, 0x48, 0x89, 0xE0, 0x31, 0xC9, 0x31, 0xD2, 0x48, 0x2B, 0x14, 0x24, 0x48, 0xC1, 0xFA,
    0x3F, 0x48, 0xBE, 0xC5, 0x5F, 0xB7, 0x50, 0x19, 0x23, 0x51, 0x45, 0x4C, 0x01, 0xFE, 0x48, 0x01,
    0xD6, 0x4C, 0x89, 0xFA] ++ bytes_l106e35_1

theorem code_l106e35 : ∀ x ∈ codeRange 0x106e35 bytes_l106e35, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x6e35 84 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l106e35_1

@[cfg_block] def b_l106ee4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106ee4 (movR32Imm32Effect 0x106ee4 5 5 0x1) (EffectPart.reads (.reg (.gpr 5)) [] []) (.reg (.gpr 5))) #v[]
    (.letOp (n := 54) (.exec 0x106ee4 (fun s => s.RIP = 0x106ee4) (movR32Imm32Effect 0x106ee4 5 5 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x106ee9 (cmpAlImm8Effect 0x106ee9 0x1) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[0]
    (.letOp (n := 56) (.exec 0x106ee9 (fun s => s.RIP = 0x106ee9) (cmpAlImm8Effect 0x106ee9 0x1) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l106f5b, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l106eed, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l106ee4 : List UInt8 :=
  [0xBD, 0x01, 0x00, 0x00, 0x00, 0x3C, 0x01, 0x75, 0x6E]

theorem code_l106ee4 : ∀ x ∈ codeRange 0x106ee4 bytes_l106ee4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6ee4 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

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

end K256.Proofs.Verify.LIR
