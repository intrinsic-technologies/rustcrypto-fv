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

@[cfg_block] def b_l110418_4 : Block Op Label signature Reg.count 188 :=
  .letOp (n := 188) (.out 0x1105eb (leaR64Effect 0x1105eb 6 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 189) (.exec 0x1105eb (fun s => s.RIP = 0x1105eb) (leaR64Effect 0x1105eb 6 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.br ⟨.l110300, RegMap.args [(0, 133), (1, 135), (2, 139), (3, 3), (4, 4), (5, 5), (6, 188), (7, 186), (8, 178), (9, 168), (10, 151), (11, 94), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 190⟩)))

def bytes_l110418_4 : List UInt8 :=
  [0x48, 0x8D, 0x74, 0x24, 0x58, 0xE9, 0x0B, 0xFD, 0xFF, 0xFF]

theorem code_l110418_4 : ∀ x ∈ codeRange 0x1105eb bytes_l110418_4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x105eb 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l110418_3 : Block Op Label signature Reg.count 160 :=
  .letOp (n := 160) (.out 0x110563 (movR64M64Effect 0x110563 8 (.sib 4 none 0 (.d32 0xe0))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 161) (.exec 0x110563 (LoadPre 0x110563 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x110563 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x110563 8 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 162) (.out 0x11056b (movR64M64Effect 0x11056b 9 (.sib 4 none 0 (.d32 0xe8))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 163) (.exec 0x11056b (LoadPre 0x11056b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x11056b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11056b 9 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 164) (.exec 0x110573 (StorePre 0x110573 4 (fun s => AddrMode.addr (.base 10 (.d8 0x8)) s (0x110573 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110573 9 (.base 10 (.d8 0x8))) (Reg.operands [.gpr 9, .gpr 10] [])) #v[162, 151]
    (.letOp (n := 165) (.exec 0x110577 (StorePre 0x110577 3 (fun s => AddrMode.addr (.base 10 .none) s (0x110577 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x110577 8 (.base 10 .none)) (Reg.operands [.gpr 8, .gpr 10] [])) #v[160, 151]
    (.letOp (n := 166) (.out 0x11057a (movR64M64Effect 0x11057a 8 (.sib 4 none 0 (.d32 0x108))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 167) (.exec 0x11057a (LoadPre 0x11057a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x11057a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11057a 8 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 168) (.out 0x110582 (movR64M64Effect 0x110582 9 (.sib 4 none 0 (.d32 0x110))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 169) (.exec 0x110582 (LoadPre 0x110582 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x110582 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x110582 9 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 170) (.exec 0x11058a (StorePre 0x11058a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x11058a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11058a 8 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[166, 4]
    (.letOp (n := 171) (.exec 0x11058f (StorePre 0x11058f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x11058f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11058f 9 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[168, 4]
    (.letOp (n := 172) (.out 0x110594 (movR64M64Effect 0x110594 8 (.sib 4 none 0 (.d32 0x118))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 173) (.exec 0x110594 (LoadPre 0x110594 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x110594 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x110594 8 (.sib 4 none 0 (.d32 0x118))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 174) (.exec 0x11059c (StorePre 0x11059c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x11059c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11059c 8 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[172, 4]
    (.letOp (n := 175) (.out 0x1105a1 (movR64M64Effect 0x1105a1 8 (.sib 4 none 0 (.d32 0x120))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 176) (.exec 0x1105a1 (LoadPre 0x1105a1 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x1105a1 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1105a1 8 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 177) (.exec 0x1105a9 (StorePre 0x1105a9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x1105a9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1105a9 8 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[175, 4]
    (.letOp (n := 178) (.out 0x1105ae (movR64M64Effect 0x1105ae 8 (.sib 4 none 0 (.d32 0x128))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 179) (.exec 0x1105ae (LoadPre 0x1105ae (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x1105ae + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1105ae 8 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 180) (.exec 0x1105b6 (StorePre 0x1105b6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1105b6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1105b6 8 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[178, 4]
    (.letOp (n := 181) (.exec 0x1105bb (StorePre 0x1105bb 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1105bb + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1105bb 0 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[133, 4]
    (.letOp (n := 182) (.exec 0x1105c3 (StorePre 0x1105c3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1105c3 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1105c3 1 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[135, 4]
    (.letOp (n := 183) (.exec 0x1105cb (StorePre 0x1105cb 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x1105cb + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1105cb 2 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[139, 4]
    (.letOp (n := 184) (.exec 0x1105d3 (StorePre 0x1105d3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x1105d3 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1105d3 7 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[147, 4]
    (.letOp (n := 185) (.exec 0x1105db (StorePre 0x1105db 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x1105db + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1105db 6 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[145, 4]
    (.letOp (n := 186) (.out 0x1105e3 (leaR64Effect 0x1105e3 7 (.sib 4 none 0 (.d32 0x130))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 187) (.exec 0x1105e3 (fun s => s.RIP = 0x1105e3) (leaR64Effect 0x1105e3 7 (.sib 4 none 0 (.d32 0x130))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l110418_4))))))))))))))))))))))))))))

def bytes_l110418_3 : List UInt8 :=
  [0x4C, 0x8B, 0x84, 0x24, 0xE0, 0x00, 0x00, 0x00, 0x4C, 0x8B, 0x8C, 0x24, 0xE8, 0x00, 0x00, 0x00,
    0x4D, 0x89, 0x4A, 0x08, 0x4D, 0x89, 0x02, 0x4C, 0x8B, 0x84, 0x24, 0x08, 0x01, 0x00, 0x00, 0x4C,
    0x8B, 0x8C, 0x24, 0x10, 0x01, 0x00, 0x00, 0x4C, 0x89, 0x44, 0x24, 0x58, 0x4C, 0x89, 0x4C, 0x24,
    0x60, 0x4C, 0x8B, 0x84, 0x24, 0x18, 0x01, 0x00, 0x00, 0x4C, 0x89, 0x44, 0x24, 0x68, 0x4C, 0x8B,
    0x84, 0x24, 0x20, 0x01, 0x00, 0x00, 0x4C, 0x89, 0x44, 0x24, 0x70, 0x4C, 0x8B, 0x84, 0x24, 0x28,
    0x01, 0x00, 0x00, 0x4C, 0x89, 0x44, 0x24, 0x78, 0x48, 0x89, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00,
    0x48, 0x89, 0x8C, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x89, 0x94, 0x24, 0x90, 0x00, 0x00, 0x00,
    0x48, 0x89, 0xBC, 0x24, 0x98, 0x00, 0x00, 0x00, 0x48, 0x89, 0xB4, 0x24, 0xA0, 0x00, 0x00, 0x00,
    0x48, 0x8D, 0xBC, 0x24, 0x30, 0x01, 0x00, 0x00] ++ bytes_l110418_4

theorem code_l110418_3 : ∀ x ∈ codeRange 0x110563 bytes_l110418_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x10563 136 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110418_4

@[cfg_block] def b_l110418_2 : Block Op Label signature Reg.count 125 :=
  .letOp (n := 125) (.exec 0x1104f7 (StorePre 0x1104f7 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x1104f7 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1104f7 6 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[123, 4]
    (.letOp (n := 126) (.exec 0x1104ff (StorePre 0x1104ff 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x1104ff + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1104ff 10 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[121, 4]
    (.letOp (n := 127) (.out 0x110507 (movR64Imm64Effect 0x110507 6 0xffffffffffff) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 128) (.exec 0x110507 (fun s => s.RIP = 0x110507) (movR64Imm64Effect 0x110507 6 0xffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 129) (.out 0x110511 (andR64R64Effect 0x110511 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6] []) (.reg (.gpr 8))) #v[72, 127]
    (.letOp (n := 130) (.exec 0x110511 (fun s => s.RIP = 0x110511) (andR64R64Effect 0x110511 8 6) (Reg.operands [.gpr 8, .gpr 6] [])) #v[72, 127]
    (.letOp (n := 131) (.out 0x110514 (movR64Imm64Effect 0x110514 9 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 9)) [] []) (.reg (.gpr 9))) #v[]
    (.letOp (n := 132) (.exec 0x110514 (fun s => s.RIP = 0x110514) (movR64Imm64Effect 0x110514 9 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 133) (.out 0x11051e (andR64R64Effect 0x11051e 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[86, 131]
    (.letOp (n := 134) (.exec 0x11051e (fun s => s.RIP = 0x11051e) (andR64R64Effect 0x11051e 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[86, 131]
    (.letOp (n := 135) (.out 0x110521 (andR64R64Effect 0x110521 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 9] []) (.reg (.gpr 1))) #v[96, 131]
    (.letOp (n := 136) (.exec 0x110521 (fun s => s.RIP = 0x110521) (andR64R64Effect 0x110521 1 9) (Reg.operands [.gpr 1, .gpr 9] [])) #v[96, 131]
    (.letOp (n := 137) (.out 0x110524 (addR64R64Effect 0x110524 7 11) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 11] []) (.reg (.gpr 7))) #v[110, 94]
    (.letOp (n := 138) (.exec 0x110524 (fun s => s.RIP = 0x110524) (addR64R64Effect 0x110524 7 11) (Reg.operands [.gpr 7, .gpr 11] [])) #v[110, 94]
    (.letOp (n := 139) (.out 0x110527 (andR64R64Effect 0x110527 2 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 9] []) (.reg (.gpr 2))) #v[104, 131]
    (.letOp (n := 140) (.exec 0x110527 (fun s => s.RIP = 0x110527) (andR64R64Effect 0x110527 2 9) (Reg.operands [.gpr 2, .gpr 9] [])) #v[104, 131]
    (.letOp (n := 141) (.out 0x11052a (movR64R64Effect 0x11052a 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 7] []) (.reg (.gpr 6))) #v[137]
    (.letOp (n := 142) (.exec 0x11052a (fun s => s.RIP = 0x11052a) (movR64R64Effect 0x11052a 6 7) (Reg.operands [.gpr 7] [])) #v[137]
    (.letOp (n := 143) (.out 0x11052d (shrR64Effect 0x11052d 4 6 52) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[141]
    (.letOp (n := 144) (.exec 0x11052d (fun s => s.RIP = 0x11052d) (shrR64Effect 0x11052d 4 6 52) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[141]
    (.letOp (n := 145) (.out 0x110531 (addR64R64Effect 0x110531 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 8] []) (.reg (.gpr 6))) #v[143, 129]
    (.letOp (n := 146) (.exec 0x110531 (fun s => s.RIP = 0x110531) (addR64R64Effect 0x110531 6 8) (Reg.operands [.gpr 6, .gpr 8] [])) #v[143, 129]
    (.letOp (n := 147) (.out 0x110534 (andR64R64Effect 0x110534 7 9) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 9] []) (.reg (.gpr 7))) #v[137, 131]
    (.letOp (n := 148) (.exec 0x110534 (fun s => s.RIP = 0x110534) (andR64R64Effect 0x110534 7 9) (Reg.operands [.gpr 7, .gpr 9] [])) #v[137, 131]
    (.letOp (n := 149) (.out 0x110537 (movR64M64Effect 0x110537 8 (.sib 4 none 0 (.d32 0x100))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 150) (.exec 0x110537 (LoadPre 0x110537 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x110537 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x110537 8 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 151) (.out 0x11053f (leaR64Effect 0x11053f 10 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 152) (.exec 0x11053f (fun s => s.RIP = 0x11053f) (leaR64Effect 0x11053f 10 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 153) (.exec 0x110547 (StorePre 0x110547 4 (fun s => AddrMode.addr (.base 10 (.d8 0x20)) s (0x110547 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110547 8 (.base 10 (.d8 0x20))) (Reg.operands [.gpr 8, .gpr 10] [])) #v[149, 151]
    (.letOp (n := 154) (.out 0x11054b (movR64M64Effect 0x11054b 8 (.sib 4 none 0 (.d32 0xf8))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 155) (.exec 0x11054b (LoadPre 0x11054b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x11054b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11054b 8 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 156) (.exec 0x110553 (StorePre 0x110553 4 (fun s => AddrMode.addr (.base 10 (.d8 0x18)) s (0x110553 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110553 8 (.base 10 (.d8 0x18))) (Reg.operands [.gpr 8, .gpr 10] [])) #v[154, 151]
    (.letOp (n := 157) (.out 0x110557 (movR64M64Effect 0x110557 8 (.sib 4 none 0 (.d32 0xf0))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 158) (.exec 0x110557 (LoadPre 0x110557 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x110557 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x110557 8 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 159) (.exec 0x11055f (StorePre 0x11055f 4 (fun s => AddrMode.addr (.base 10 (.d8 0x10)) s (0x11055f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11055f 8 (.base 10 (.d8 0x10))) (Reg.operands [.gpr 8, .gpr 10] [])) #v[157, 151]
    (b_l110418_3)))))))))))))))))))))))))))))))))))

def bytes_l110418_2 : List UInt8 :=
  [0x48, 0x89, 0xB4, 0x24, 0xE8, 0x00, 0x00, 0x00, 0x4C, 0x89, 0x94, 0x24, 0xE0, 0x00, 0x00, 0x00,
    0x48, 0xBE, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x49, 0x21, 0xF0, 0x49, 0xB9, 0xFF,
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x4C, 0x21, 0xC8, 0x4C, 0x21, 0xC9, 0x4C, 0x01, 0xDF,
    0x4C, 0x21, 0xCA, 0x48, 0x89, 0xFE, 0x48, 0xC1, 0xEE, 0x34, 0x4C, 0x01, 0xC6, 0x4C, 0x21, 0xCF,
    0x4C, 0x8B, 0x84, 0x24, 0x00, 0x01, 0x00, 0x00, 0x4C, 0x8D, 0x94, 0x24, 0xA8, 0x00, 0x00, 0x00,
    0x4D, 0x89, 0x42, 0x20, 0x4C, 0x8B, 0x84, 0x24, 0xF8, 0x00, 0x00, 0x00, 0x4D, 0x89, 0x42, 0x18,
    0x4C, 0x8B, 0x84, 0x24, 0xF0, 0x00, 0x00, 0x00, 0x4D, 0x89, 0x42, 0x10] ++ bytes_l110418_3

theorem code_l110418_2 : ∀ x ∈ codeRange 0x1104f7 bytes_l110418_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x104f7 108 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110418_3

@[cfg_block] def b_l110418_1 : Block Op Label signature Reg.count 88 :=
  .letOp (n := 88) (.out 0x110492 (movR64R64Effect 0x110492 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[86]
    (.letOp (n := 89) (.exec 0x110492 (fun s => s.RIP = 0x110492) (movR64R64Effect 0x110492 1 0) (Reg.operands [.gpr 0] [])) #v[86]
    (.letOp (n := 90) (.out 0x110495 (shrR64Effect 0x110495 4 1 52) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[88]
    (.letOp (n := 91) (.exec 0x110495 (fun s => s.RIP = 0x110495) (shrR64Effect 0x110495 4 1 52) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[88]
    (.letOp (n := 92) (.out 0x110499 (subR64M64Effect 0x110499 1 (.sib 6 (some 9) 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6, .gpr 9] []) (.reg (.gpr 1))) #v[90, 6, 53]
    (.letOp (n := 93) (.exec 0x110499 (LoadPre 0x110499 (fun s => AddrMode.addr (.sib 6 (some 9) 0 (.d8 0x30)) s (0x110499 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x110499 1 (.sib 6 (some 9) 0 (.d8 0x30))) (Reg.operands [.gpr 1, .gpr 6, .gpr 9] [])) #v[90, 6, 53]
    (.letOp (n := 94) (.out 0x11049e (movR64Imm64Effect 0x11049e 11 0x3ffffffffffffc) (EffectPart.reads (.reg (.gpr 11)) [] []) (.reg (.gpr 11))) #v[]
    (.letOp (n := 95) (.exec 0x11049e (fun s => s.RIP = 0x11049e) (movR64Imm64Effect 0x11049e 11 0x3ffffffffffffc) (Reg.operands [] [])) #v[]
    (.letOp (n := 96) (.out 0x1104a8 (addR64R64Effect 0x1104a8 1 11) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 11] []) (.reg (.gpr 1))) #v[92, 94]
    (.letOp (n := 97) (.exec 0x1104a8 (fun s => s.RIP = 0x1104a8) (addR64R64Effect 0x1104a8 1 11) (Reg.operands [.gpr 1, .gpr 11] [])) #v[92, 94]
    (.letOp (n := 98) (.out 0x1104ab (movR64R64Effect 0x1104ab 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[96]
    (.letOp (n := 99) (.exec 0x1104ab (fun s => s.RIP = 0x1104ab) (movR64R64Effect 0x1104ab 2 1) (Reg.operands [.gpr 1] [])) #v[96]
    (.letOp (n := 100) (.out 0x1104ae (shrR64Effect 0x1104ae 4 2 52) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[98]
    (.letOp (n := 101) (.exec 0x1104ae (fun s => s.RIP = 0x1104ae) (shrR64Effect 0x1104ae 4 2 52) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[98]
    (.letOp (n := 102) (.out 0x1104b2 (subR64M64Effect 0x1104b2 2 (.sib 6 (some 9) 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6, .gpr 9] []) (.reg (.gpr 2))) #v[100, 6, 53]
    (.letOp (n := 103) (.exec 0x1104b2 (LoadPre 0x1104b2 (fun s => AddrMode.addr (.sib 6 (some 9) 0 (.d8 0x38)) s (0x1104b2 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x1104b2 2 (.sib 6 (some 9) 0 (.d8 0x38))) (Reg.operands [.gpr 2, .gpr 6, .gpr 9] [])) #v[100, 6, 53]
    (.letOp (n := 104) (.out 0x1104b7 (addR64R64Effect 0x1104b7 2 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 11] []) (.reg (.gpr 2))) #v[102, 94]
    (.letOp (n := 105) (.exec 0x1104b7 (fun s => s.RIP = 0x1104b7) (addR64R64Effect 0x1104b7 2 11) (Reg.operands [.gpr 2, .gpr 11] [])) #v[102, 94]
    (.letOp (n := 106) (.out 0x1104ba (movR64R64Effect 0x1104ba 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[104]
    (.letOp (n := 107) (.exec 0x1104ba (fun s => s.RIP = 0x1104ba) (movR64R64Effect 0x1104ba 7 2) (Reg.operands [.gpr 2] [])) #v[104]
    (.letOp (n := 108) (.out 0x1104bd (shrR64Effect 0x1104bd 4 7 52) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[106]
    (.letOp (n := 109) (.exec 0x1104bd (fun s => s.RIP = 0x1104bd) (shrR64Effect 0x1104bd 4 7 52) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[106]
    (.letOp (n := 110) (.out 0x1104c1 (subR64M64Effect 0x1104c1 7 (.sib 6 (some 9) 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6, .gpr 9] []) (.reg (.gpr 7))) #v[108, 6, 53]
    (.letOp (n := 111) (.exec 0x1104c1 (LoadPre 0x1104c1 (fun s => AddrMode.addr (.sib 6 (some 9) 0 (.d8 0x40)) s (0x1104c1 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x1104c1 7 (.sib 6 (some 9) 0 (.d8 0x40))) (Reg.operands [.gpr 7, .gpr 6, .gpr 9] [])) #v[108, 6, 53]
    (.letOp (n := 112) (.out 0x1104c6 (movR64M64Effect 0x1104c6 10 (.sib 6 (some 9) 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 6, .gpr 9] []) (.reg (.gpr 10))) #v[6, 53]
    (.letOp (n := 113) (.exec 0x1104c6 (LoadPre 0x1104c6 (fun s => AddrMode.addr (.sib 6 (some 9) 0 (.d8 0x70)) s (0x1104c6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1104c6 10 (.sib 6 (some 9) 0 (.d8 0x70))) (Reg.operands [.gpr 6, .gpr 9] [])) #v[6, 53]
    (.letOp (n := 114) (.exec 0x1104cb (StorePre 0x1104cb 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x1104cb + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1104cb 10 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[112, 4]
    (.letOp (n := 115) (.out 0x1104d3 (movR64M64Effect 0x1104d3 10 (.sib 6 (some 9) 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 6, .gpr 9] []) (.reg (.gpr 10))) #v[6, 53]
    (.letOp (n := 116) (.exec 0x1104d3 (LoadPre 0x1104d3 (fun s => AddrMode.addr (.sib 6 (some 9) 0 (.d8 0x68)) s (0x1104d3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1104d3 10 (.sib 6 (some 9) 0 (.d8 0x68))) (Reg.operands [.gpr 6, .gpr 9] [])) #v[6, 53]
    (.letOp (n := 117) (.exec 0x1104d8 (StorePre 0x1104d8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x1104d8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1104d8 10 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[115, 4]
    (.letOp (n := 118) (.out 0x1104e0 (movR64M64Effect 0x1104e0 10 (.sib 6 (some 9) 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 6, .gpr 9] []) (.reg (.gpr 10))) #v[6, 53]
    (.letOp (n := 119) (.exec 0x1104e0 (LoadPre 0x1104e0 (fun s => AddrMode.addr (.sib 6 (some 9) 0 (.d8 0x60)) s (0x1104e0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1104e0 10 (.sib 6 (some 9) 0 (.d8 0x60))) (Reg.operands [.gpr 6, .gpr 9] [])) #v[6, 53]
    (.letOp (n := 120) (.exec 0x1104e5 (StorePre 0x1104e5 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x1104e5 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1104e5 10 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[118, 4]
    (.letOp (n := 121) (.out 0x1104ed (movR64M64Effect 0x1104ed 10 (.sib 6 (some 9) 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 6, .gpr 9] []) (.reg (.gpr 10))) #v[6, 53]
    (.letOp (n := 122) (.exec 0x1104ed (LoadPre 0x1104ed (fun s => AddrMode.addr (.sib 6 (some 9) 0 (.d8 0x50)) s (0x1104ed + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1104ed 10 (.sib 6 (some 9) 0 (.d8 0x50))) (Reg.operands [.gpr 6, .gpr 9] [])) #v[6, 53]
    (.letOp (n := 123) (.out 0x1104f2 (movR64M64Effect 0x1104f2 6 (.sib 6 (some 9) 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 9] []) (.reg (.gpr 6))) #v[6, 53]
    (.letOp (n := 124) (.exec 0x1104f2 (LoadPre 0x1104f2 (fun s => AddrMode.addr (.sib 6 (some 9) 0 (.d8 0x58)) s (0x1104f2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1104f2 6 (.sib 6 (some 9) 0 (.d8 0x58))) (Reg.operands [.gpr 6, .gpr 9] [])) #v[6, 53]
    (b_l110418_2)))))))))))))))))))))))))))))))))))))

def bytes_l110418_1 : List UInt8 :=
  [0x48, 0x89, 0xC1, 0x48, 0xC1, 0xE9, 0x34, 0x4A, 0x2B, 0x4C, 0x0E, 0x30, 0x49, 0xBB, 0xFC, 0xFF,
    0xFF, 0xFF, 0xFF, 0xFF, 0x3F, 0x00, 0x4C, 0x01, 0xD9, 0x48, 0x89, 0xCA, 0x48, 0xC1, 0xEA, 0x34,
    0x4A, 0x2B, 0x54, 0x0E, 0x38, 0x4C, 0x01, 0xDA, 0x48, 0x89, 0xD7, 0x48, 0xC1, 0xEF, 0x34, 0x4A,
    0x2B, 0x7C, 0x0E, 0x40, 0x4E, 0x8B, 0x54, 0x0E, 0x70, 0x4C, 0x89, 0x94, 0x24, 0x00, 0x01, 0x00,
    0x00, 0x4E, 0x8B, 0x54, 0x0E, 0x68, 0x4C, 0x89, 0x94, 0x24, 0xF8, 0x00, 0x00, 0x00, 0x4E, 0x8B,
    0x54, 0x0E, 0x60, 0x4C, 0x89, 0x94, 0x24, 0xF0, 0x00, 0x00, 0x00, 0x4E, 0x8B, 0x54, 0x0E, 0x50,
    0x4A, 0x8B, 0x74, 0x0E, 0x58] ++ bytes_l110418_2

theorem code_l110418_1 : ∀ x ∈ codeRange 0x110492 bytes_l110418_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x10492 101 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110418_2

@[cfg_block] def b_l110418 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x110418 (imulR64R64Imm8Effect 0x110418 4 9 7 0x78) (EffectPart.reads (.reg (.gpr 9)) [.gpr 7] []) (.reg (.gpr 9))) #v[7]
    (.letOp (n := 54) (.exec 0x110418 (fun s => s.RIP = 0x110418) (imulR64R64Imm8Effect 0x110418 4 9 7 0x78) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 55) (.out 0x11041c (movR64M64Effect 0x11041c 0 (.sib 6 (some 9) 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6, .gpr 9] []) (.reg (.gpr 0))) #v[6, 53]
    (.letOp (n := 56) (.exec 0x11041c (LoadPre 0x11041c (fun s => AddrMode.addr (.sib 6 (some 9) 0 (.d8 0x20)) s (0x11041c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11041c 0 (.sib 6 (some 9) 0 (.d8 0x20))) (Reg.operands [.gpr 6, .gpr 9] [])) #v[6, 53]
    (.letOp (n := 57) (.exec 0x110421 (StorePre 0x110421 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x110421 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x110421 0 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 58) (.out 0x110429 (movR64M64Effect 0x110429 0 (.sib 6 (some 9) 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6, .gpr 9] []) (.reg (.gpr 0))) #v[6, 53]
    (.letOp (n := 59) (.exec 0x110429 (LoadPre 0x110429 (fun s => AddrMode.addr (.sib 6 (some 9) 0 (.d8 0x18)) s (0x110429 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x110429 0 (.sib 6 (some 9) 0 (.d8 0x18))) (Reg.operands [.gpr 6, .gpr 9] [])) #v[6, 53]
    (.letOp (n := 60) (.exec 0x11042e (StorePre 0x11042e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x11042e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11042e 0 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[58, 4]
    (.letOp (n := 61) (.out 0x110436 (movR64M64Effect 0x110436 0 (.sib 6 (some 9) 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6, .gpr 9] []) (.reg (.gpr 0))) #v[6, 53]
    (.letOp (n := 62) (.exec 0x110436 (LoadPre 0x110436 (fun s => AddrMode.addr (.sib 6 (some 9) 0 (.d8 0x10)) s (0x110436 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x110436 0 (.sib 6 (some 9) 0 (.d8 0x10))) (Reg.operands [.gpr 6, .gpr 9] [])) #v[6, 53]
    (.letOp (n := 63) (.exec 0x11043b (StorePre 0x11043b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x11043b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11043b 0 (.sib 4 none 0 (.d32 0x118))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.out 0x110443 (movR64M64Effect 0x110443 0 (.sib 6 (some 9) 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6, .gpr 9] []) (.reg (.gpr 0))) #v[6, 53]
    (.letOp (n := 65) (.exec 0x110443 (LoadPre 0x110443 (fun s => AddrMode.addr (.sib 6 (some 9) 0 .none) s (0x110443 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x110443 0 (.sib 6 (some 9) 0 .none)) (Reg.operands [.gpr 6, .gpr 9] [])) #v[6, 53]
    (.letOp (n := 66) (.out 0x110447 (movR64M64Effect 0x110447 1 (.sib 6 (some 9) 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6, .gpr 9] []) (.reg (.gpr 1))) #v[6, 53]
    (.letOp (n := 67) (.exec 0x110447 (LoadPre 0x110447 (fun s => AddrMode.addr (.sib 6 (some 9) 0 (.d8 0x8)) s (0x110447 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x110447 1 (.sib 6 (some 9) 0 (.d8 0x8))) (Reg.operands [.gpr 6, .gpr 9] [])) #v[6, 53]
    (.letOp (n := 68) (.exec 0x11044c (StorePre 0x11044c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x11044c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11044c 1 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[66, 4]
    (.letOp (n := 69) (.exec 0x110454 (StorePre 0x110454 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x110454 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x110454 0 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 70) (.out 0x11045c (movR64Imm64Effect 0x11045c 8 0x3fffffffffffc) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 71) (.exec 0x11045c (fun s => s.RIP = 0x11045c) (movR64Imm64Effect 0x11045c 8 0x3fffffffffffc) (Reg.operands [] [])) #v[]
    (.letOp (n := 72) (.out 0x110466 (subR64M64Effect 0x110466 8 (.sib 6 (some 9) 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6, .gpr 9] []) (.reg (.gpr 8))) #v[70, 6, 53]
    (.letOp (n := 73) (.exec 0x110466 (LoadPre 0x110466 (fun s => AddrMode.addr (.sib 6 (some 9) 0 (.d8 0x48)) s (0x110466 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x110466 8 (.sib 6 (some 9) 0 (.d8 0x48))) (Reg.operands [.gpr 8, .gpr 6, .gpr 9] [])) #v[70, 6, 53]
    (.letOp (n := 74) (.out 0x11046b (movR64R64Effect 0x11046b 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[72]
    (.letOp (n := 75) (.exec 0x11046b (fun s => s.RIP = 0x11046b) (movR64R64Effect 0x11046b 0 8) (Reg.operands [.gpr 8] [])) #v[72]
    (.letOp (n := 76) (.out 0x11046e (shrR64Effect 0x11046e 4 0 48) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[74]
    (.letOp (n := 77) (.exec 0x11046e (fun s => s.RIP = 0x11046e) (shrR64Effect 0x11046e 4 0 48) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[74]
    (.letOp (n := 78) (.out 0x110472 (movR64Imm64Effect 0x110472 1 0x1000003d1) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 79) (.exec 0x110472 (fun s => s.RIP = 0x110472) (movR64Imm64Effect 0x110472 1 0x1000003d1) (Reg.operands [] [])) #v[]
    (.letOp (n := 80) (.out 0x11047c (imulR64R64Effect 0x11047c 4 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[76, 78]
    (.letOp (n := 81) (.exec 0x11047c (fun s => s.RIP = 0x11047c) (imulR64R64Effect 0x11047c 4 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[76, 78]
    (.letOp (n := 82) (.out 0x110480 (subR64M64Effect 0x110480 0 (.sib 6 (some 9) 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6, .gpr 9] []) (.reg (.gpr 0))) #v[80, 6, 53]
    (.letOp (n := 83) (.exec 0x110480 (LoadPre 0x110480 (fun s => AddrMode.addr (.sib 6 (some 9) 0 (.d8 0x28)) s (0x110480 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x110480 0 (.sib 6 (some 9) 0 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 6, .gpr 9] [])) #v[80, 6, 53]
    (.letOp (n := 84) (.out 0x110485 (movR64Imm64Effect 0x110485 1 0x3ffffbfffff0bc) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 85) (.exec 0x110485 (fun s => s.RIP = 0x110485) (movR64Imm64Effect 0x110485 1 0x3ffffbfffff0bc) (Reg.operands [] [])) #v[]
    (.letOp (n := 86) (.out 0x11048f (addR64R64Effect 0x11048f 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[82, 84]
    (.letOp (n := 87) (.exec 0x11048f (fun s => s.RIP = 0x11048f) (addR64R64Effect 0x11048f 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[82, 84]
    (b_l110418_1)))))))))))))))))))))))))))))))))))

def bytes_l110418 : List UInt8 :=
  [0x4C, 0x6B, 0xCF, 0x78, 0x4A, 0x8B, 0x44, 0x0E, 0x20, 0x48, 0x89, 0x84, 0x24, 0x28, 0x01, 0x00,
    0x00, 0x4A, 0x8B, 0x44, 0x0E, 0x18, 0x48, 0x89, 0x84, 0x24, 0x20, 0x01, 0x00, 0x00, 0x4A, 0x8B,
    0x44, 0x0E, 0x10, 0x48, 0x89, 0x84, 0x24, 0x18, 0x01, 0x00, 0x00, 0x4A, 0x8B, 0x04, 0x0E, 0x4A,
    0x8B, 0x4C, 0x0E, 0x08, 0x48, 0x89, 0x8C, 0x24, 0x10, 0x01, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24,
    0x08, 0x01, 0x00, 0x00, 0x49, 0xB8, 0xFC, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x03, 0x00, 0x4E, 0x2B,
    0x44, 0x0E, 0x48, 0x4C, 0x89, 0xC0, 0x48, 0xC1, 0xE8, 0x30, 0x48, 0xB9, 0xD1, 0x03, 0x00, 0x00,
    0x01, 0x00, 0x00, 0x00, 0x48, 0x0F, 0xAF, 0xC1, 0x4A, 0x2B, 0x44, 0x0E, 0x28, 0x48, 0xB9, 0xBC,
    0xF0, 0xFF, 0xFF, 0xFB, 0xFF, 0x3F, 0x00, 0x48, 0x01, 0xC8] ++ bytes_l110418_1

theorem code_l110418 : ∀ x ∈ codeRange 0x110418 bytes_l110418, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x10418 122 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110418_1

@[cfg_block] def b_l110600 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x110600 (movR64M64Effect 0x110600 2 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 54) (.exec 0x110600 (LoadPre 0x110600 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x110600 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x110600 2 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x110605 (movR64R64Effect 0x110605 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[53]
    (.letOp (n := 56) (.exec 0x110605 (fun s => s.RIP = 0x110605) (movR64R64Effect 0x110605 9 2) (Reg.operands [.gpr 2] [])) #v[53]
    (.letOp (n := 57) (.out 0x110608 (movR64R64Effect 0x110608 11 12) (EffectPart.reads (.reg (.gpr 11)) [.gpr 12] []) (.reg (.gpr 11))) #v[12]
    (.letOp (n := 58) (.exec 0x110608 (fun s => s.RIP = 0x110608) (movR64R64Effect 0x110608 11 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 59) (.out 0x11060b (movR64R64Effect 0x11060b 10 13) (EffectPart.reads (.reg (.gpr 10)) [.gpr 13] []) (.reg (.gpr 10))) #v[13]
    (.letOp (n := 60) (.exec 0x11060b (fun s => s.RIP = 0x11060b) (movR64R64Effect 0x11060b 10 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 61) (.out 0x11060e (movR64R64Effect 0x11060e 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 62) (.exec 0x11060e (fun s => s.RIP = 0x11060e) (movR64R64Effect 0x11060e 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 63) (.out 0x110611 (movR64M64Effect 0x110611 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 64) (.exec 0x110611 (LoadPre 0x110611 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x110611 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x110611 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x110616 (movR64R64Effect 0x110616 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 12] []) (.reg (.gpr 6))) #v[12]
    (.letOp (n := 66) (.exec 0x110616 (fun s => s.RIP = 0x110616) (movR64R64Effect 0x110616 6 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 67) (.out 0x110619 (movR64R64Effect 0x110619 3 8) (EffectPart.reads (.reg (.gpr 3)) [.gpr 8] []) (.reg (.gpr 3))) #v[8]
    (.letOp (n := 68) (.exec 0x110619 (fun s => s.RIP = 0x110619) (movR64R64Effect 0x110619 3 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 69) (.out 0x11061c (movR64R64Effect 0x11061c 8 13) (EffectPart.reads (.reg (.gpr 8)) [.gpr 13] []) (.reg (.gpr 8))) #v[13]
    (.letOp (n := 70) (.exec 0x11061c (fun s => s.RIP = 0x11061c) (movR64R64Effect 0x11061c 8 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 71) (.out 0x11061f (movR64R64Effect 0x11061f 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[14]
    (.letOp (n := 72) (.exec 0x11061f (fun s => s.RIP = 0x11061f) (movR64R64Effect 0x11061f 1 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 73) (.out 0x110622 (testR64R64Effect 0x110622 3 3) (EffectPart.reads (.flag .ZF) [.gpr 3, .gpr 3] []) (.flag .ZF)) #v[67, 67]
    (.letOp (n := 74) (.exec 0x110622 (fun s => s.RIP = 0x110622) (testR64R64Effect 0x110622 3 3) (Reg.operands [.gpr 3, .gpr 3] [])) #v[67, 67]
    (.letOp (n := 75) (.pure (condOp 4)) #v[73]
    (.terminate (.condBr (Fin.last 75) ⟨.l1106b6, RegMap.args [(0, 63), (1, 71), (2, 53), (3, 67), (4, 4), (5, 5), (6, 65), (7, 61), (8, 69), (9, 55), (10, 59), (11, 57), (12, 12), (13, 13), (14, 14), (19, 73), (22, 22), (39, 39), (50, 50), (51, 51)] 76⟩ ⟨.l11062b, RegMap.args [(0, 63), (1, 71), (2, 53), (3, 67), (4, 4), (5, 5), (6, 65), (7, 61), (8, 69), (9, 55), (10, 59), (11, 57), (12, 12), (13, 13), (14, 14), (19, 73), (22, 22), (39, 39), (50, 50), (51, 51)] 76⟩))))))))))))))))))))))))

def bytes_l110600 : List UInt8 :=
  [0x48, 0x8B, 0x54, 0x24, 0x50, 0x49, 0x89, 0xD1, 0x4D, 0x89, 0xE3, 0x4D, 0x89, 0xEA, 0x4C, 0x89,
    0xF7, 0x48, 0x8B, 0x44, 0x24, 0x48, 0x4C, 0x89, 0xE6, 0x4C, 0x89, 0xC3, 0x4D, 0x89, 0xE8, 0x4C,
    0x89, 0xF1, 0x48, 0x85, 0xDB, 0x0F, 0x84, 0x8B, 0x00, 0x00, 0x00]

theorem code_l110600 : ∀ x ∈ codeRange 0x110600 bytes_l110600, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x10600 43 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11062b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x11062b (fun s => s.RIP = 0x11062b) (fun _ => nopEffect 0x11062b 5) (Reg.operands [] [])) #v[]
    (.letOp (n := 54) (.out 0x110630 (movR64M64Effect 0x110630 11 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 55) (.exec 0x110630 (LoadPre 0x110630 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x110630 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x110630 11 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x110635 (testR64R64Effect 0x110635 8 8) (EffectPart.reads (.flag .ZF) [.gpr 8, .gpr 8] []) (.flag .ZF)) #v[8, 8]
    (.letOp (n := 57) (.exec 0x110635 (fun s => s.RIP = 0x110635) (testR64R64Effect 0x110635 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[8, 8]
    (.letOp (n := 58) (.pure (condOp 5)) #v[56]
    (.terminate (.condBr (Fin.last 58) ⟨.l110648, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (8, 8), (11, 54), (12, 12), (13, 13), (14, 14), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩ ⟨.l11063a, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (8, 8), (11, 54), (12, 12), (13, 13), (14, 14), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l11062b : List UInt8 :=
  [0x0F, 0x1F, 0x44, 0x00, 0x00, 0x4C, 0x8B, 0x5C, 0x24, 0x20, 0x4D, 0x85, 0xC0, 0x75, 0x0E]

theorem code_l11062b : ∀ x ∈ codeRange 0x11062b bytes_l11062b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1062b 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11063a : Block Op Label signature Reg.count 53 :=
  .terminate (.br ⟨.l11064d, RegMap.args (entryMap (live .l11063a)) 53⟩)

def bytes_l11063a : List UInt8 :=
  [0xEB, 0x11]

theorem code_l11063a : ∀ x ∈ codeRange 0x11063a bytes_l11063a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1063a 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l110640 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x110640 (incR64Effect 0x110640 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[6]
    (.letOp (n := 54) (.exec 0x110640 (fun s => s.RIP = 0x110640) (incR64Effect 0x110640 6) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6]
    (.letOp (n := 55) (.out 0x110643 (testR64R64Effect 0x110643 8 8) (EffectPart.reads (.flag .ZF) [.gpr 8, .gpr 8] []) (.flag .ZF)) #v[8, 8]
    (.letOp (n := 56) (.exec 0x110643 (fun s => s.RIP = 0x110643) (testR64R64Effect 0x110643 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[8, 8]
    (.letOp (n := 57) (.pure (condOp 4)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l11064d, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 53), (8, 8), (11, 11), (12, 12), (13, 13), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l110648, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 53), (8, 8), (11, 11), (12, 12), (13, 13), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l110640 : List UInt8 :=
  [0x48, 0xFF, 0xC6, 0x4D, 0x85, 0xC0, 0x74, 0x05]

theorem code_l110640 : ∀ x ∈ codeRange 0x110640 bytes_l110640, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x10640 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l110648 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x110648 (cmpR64R64Effect 0x110648 6 2) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 2] []) (.flag .CF)) #v[6, 2]
    (.letOp (n := 54) (.exec 0x110648 (fun s => s.RIP = 0x110648) (cmpR64R64Effect 0x110648 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[6, 2]
    (.letOp (n := 55) (.pure (condOp 2)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l110640, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (8, 8), (11, 11), (12, 12), (13, 13), (14, 14), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l11064d, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (8, 8), (11, 11), (12, 12), (13, 13), (14, 14), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l110648 : List UInt8 :=
  [0x48, 0x39, 0xD6, 0x72, 0xF3]

theorem code_l110648 : ∀ x ∈ codeRange 0x110648 bytes_l110648, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x10648 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11064d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11064d (testR64R64Effect 0x11064d 1 1) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 1] []) (.flag .ZF)) #v[1, 1]
    (.letOp (n := 54) (.exec 0x11064d (fun s => s.RIP = 0x11064d) (testR64R64Effect 0x11064d 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[1, 1]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l110680, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (8, 8), (11, 11), (12, 12), (13, 13), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l110652, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (8, 8), (11, 11), (12, 12), (13, 13), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l11064d : List UInt8 :=
  [0x48, 0x85, 0xC9, 0x74, 0x2E]

theorem code_l11064d : ∀ x ∈ codeRange 0x11064d bytes_l11064d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1064d 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l110652 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x110652 (cmpR64R64Effect 0x110652 1 5) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 5] []) (.flag .ZF)) #v[1, 5]
    (.letOp (n := 54) (.exec 0x110652 (fun s => s.RIP = 0x110652) (cmpR64R64Effect 0x110652 1 5) (Reg.operands [.gpr 1, .gpr 5] [])) #v[1, 5]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l110680, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (8, 8), (11, 11), (12, 12), (13, 13), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l110657, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (8, 8), (11, 11), (12, 12), (13, 13), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l110652 : List UInt8 :=
  [0x48, 0x39, 0xE9, 0x74, 0x29]

theorem code_l110652 : ∀ x ∈ codeRange 0x110652 bytes_l110652, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x10652 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l110657 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x110657 (movR64R64Effect 0x110657 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 1] []) (.reg (.gpr 8))) #v[1]
    (.letOp (n := 54) (.exec 0x110657 (fun s => s.RIP = 0x110657) (movR64R64Effect 0x110657 8 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 55) (.out 0x11065a (addR64Imm32Effect 0x11065a 1 0x9a0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1]
    (.letOp (n := 56) (.exec 0x11065a (fun s => s.RIP = 0x11065a) (addR64Imm32Effect 0x11065a 1 0x9a0) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 57) (.out 0x110661 (movR32Imm32Effect 0x110661 5 2 0x2) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x110661 (fun s => s.RIP = 0x110661) (movR32Imm32Effect 0x110661 5 2 0x2) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x110666 (xorR32R32Effect 0x110666 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[6, 6]
    (.letOp (n := 60) (.exec 0x110666 (fun s => s.RIP = 0x110666) (xorR32R32Effect 0x110666 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 61) (.out 0x110668 (incR64Effect 0x110668 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[59]
    (.letOp (n := 62) (.exec 0x110668 (fun s => s.RIP = 0x110668) (incR64Effect 0x110668 6) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[59]
    (.letOp (n := 63) (.out 0x11066b (testR64R64Effect 0x11066b 8 8) (EffectPart.reads (.flag .ZF) [.gpr 8, .gpr 8] []) (.flag .ZF)) #v[53, 53]
    (.letOp (n := 64) (.exec 0x11066b (fun s => s.RIP = 0x11066b) (testR64R64Effect 0x11066b 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[53, 53]
    (.letOp (n := 65) (.pure (condOp 5)) #v[63]
    (.terminate (.condBr (Fin.last 65) ⟨.l110648, RegMap.args [(0, 0), (1, 55), (2, 57), (4, 4), (5, 5), (6, 61), (8, 53), (11, 11), (12, 12), (13, 13), (14, 14), (19, 63), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩ ⟨.l110670, RegMap.args [(0, 0), (1, 55), (2, 57), (4, 4), (5, 5), (6, 61), (8, 53), (11, 11), (12, 12), (13, 13), (14, 14), (19, 63), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩))))))))))))))

def bytes_l110657 : List UInt8 :=
  [0x49, 0x89, 0xC8, 0x48, 0x81, 0xC1, 0xA0, 0x09, 0x00, 0x00, 0xBA, 0x02, 0x00, 0x00, 0x00, 0x31,
    0xF6, 0x48, 0xFF, 0xC6, 0x4D, 0x85, 0xC0, 0x75, 0xD8]

theorem code_l110657 : ∀ x ∈ codeRange 0x110657 bytes_l110657, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x10657 25 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l110670 : Block Op Label signature Reg.count 53 :=
  .terminate (.br ⟨.l11064d, RegMap.args (entryMap (live .l110670)) 53⟩)

def bytes_l110670 : List UInt8 :=
  [0xEB, 0xDB]

theorem code_l110670 : ∀ x ∈ codeRange 0x110670 bytes_l110670, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x10670 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l110680 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x110680 (cmpR64R64Effect 0x110680 0 11) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 11] []) (.flag .CF)) #v[0, 11]
    (.letOp (n := 54) (.exec 0x110680 (fun s => s.RIP = 0x110680) (cmpR64R64Effect 0x110680 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[0, 11]
    (.letOp (n := 55) (.pure (condOp 3)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l1106d0, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (8, 8), (11, 11), (12, 12), (13, 13), (14, 14), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l110685, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (8, 8), (11, 11), (12, 12), (13, 13), (14, 14), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l110680 : List UInt8 :=
  [0x4C, 0x39, 0xD8, 0x73, 0x4B]

theorem code_l110680 : ∀ x ∈ codeRange 0x110680 bytes_l110680, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x10680 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l110685 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x110685 (incR64Effect 0x110685 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 54) (.exec 0x110685 (fun s => s.RIP = 0x110685) (incR64Effect 0x110685 0) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[0]
    (.letOp (n := 55) (.out 0x110688 (xorR32R32Effect 0x110688 3 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 8] []) (.reg (.gpr 8))) #v[8, 8]
    (.letOp (n := 56) (.exec 0x110688 (fun s => s.RIP = 0x110688) (xorR32R32Effect 0x110688 3 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[8, 8]
    (.letOp (n := 57) (.out 0x11068b (movR64M64Effect 0x11068b 11 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 58) (.exec 0x11068b (LoadPre 0x11068b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11068b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11068b 11 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x110690 (testR64R64Effect 0x110690 8 8) (EffectPart.reads (.flag .ZF) [.gpr 8, .gpr 8] []) (.flag .ZF)) #v[55, 55]
    (.letOp (n := 60) (.exec 0x110690 (fun s => s.RIP = 0x110690) (testR64R64Effect 0x110690 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[55, 55]
    (.letOp (n := 61) (.pure (condOp 5)) #v[59]
    (.terminate (.condBr (Fin.last 61) ⟨.l110648, RegMap.args [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (8, 55), (11, 57), (12, 12), (13, 13), (14, 14), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ ⟨.l110695, RegMap.args [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (8, 55), (11, 57), (12, 12), (13, 13), (14, 14), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩))))))))))

def bytes_l110685 : List UInt8 :=
  [0x48, 0xFF, 0xC0, 0x45, 0x31, 0xC0, 0x4C, 0x8B, 0x5C, 0x24, 0x20, 0x4D, 0x85, 0xC0, 0x75, 0xB3]

theorem code_l110685 : ∀ x ∈ codeRange 0x110685 bytes_l110685, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x10685 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l110695 : Block Op Label signature Reg.count 53 :=
  .terminate (.br ⟨.l11064d, RegMap.args (entryMap (live .l110695)) 53⟩)

def bytes_l110695 : List UInt8 :=
  [0xEB, 0xB6]

theorem code_l110695 : ∀ x ∈ codeRange 0x110695 bytes_l110695, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x10695 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1106a0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1106a0 (movR64R64Effect 0x1106a0 10 7) (EffectPart.reads (.reg (.gpr 10)) [.gpr 7] []) (.reg (.gpr 10))) #v[7]
    (.letOp (n := 54) (.exec 0x1106a0 (fun s => s.RIP = 0x1106a0) (movR64R64Effect 0x1106a0 10 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 55) (.out 0x1106a3 (addR64Imm32Effect 0x1106a3 7 0x9a0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[7]
    (.letOp (n := 56) (.exec 0x1106a3 (fun s => s.RIP = 0x1106a3) (addR64Imm32Effect 0x1106a3 7 0x9a0) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 57) (.out 0x1106aa (movR32Imm32Effect 0x1106aa 6 9 0x2) (EffectPart.reads (.reg (.gpr 9)) [] []) (.reg (.gpr 9))) #v[]
    (.letOp (n := 58) (.exec 0x1106aa (fun s => s.RIP = 0x1106aa) (movR32Imm32Effect 0x1106aa 6 9 0x2) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x1106b0 (xorR32R32Effect 0x1106b0 3 11 11) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 11] []) (.reg (.gpr 11))) #v[11, 11]
    (.letOp (n := 60) (.exec 0x1106b0 (fun s => s.RIP = 0x1106b0) (xorR32R32Effect 0x1106b0 3 11 11) (Reg.operands [.gpr 11, .gpr 11] [])) #v[11, 11]
    (.terminate (.br ⟨.l1106b3, RegMap.args [(2, 2), (4, 4), (5, 5), (7, 55), (9, 57), (10, 53), (11, 59), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩)))))))))

def bytes_l1106a0 : List UInt8 :=
  [0x49, 0x89, 0xFA, 0x48, 0x81, 0xC7, 0xA0, 0x09, 0x00, 0x00, 0x41, 0xB9, 0x02, 0x00, 0x00, 0x00,
    0x45, 0x31, 0xDB]

theorem code_l1106a0 : ∀ x ∈ codeRange 0x1106a0 bytes_l1106a0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x106a0 19 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1106b3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1106b3 (incR64Effect 0x1106b3 11) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[11]
    (.letOp (n := 54) (.exec 0x1106b3 (fun s => s.RIP = 0x1106b3) (incR64Effect 0x1106b3 11) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[11]
    (.terminate (.br ⟨.l1106b6, RegMap.args [(2, 2), (4, 4), (5, 5), (7, 7), (9, 9), (10, 10), (11, 53), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l1106b3 : List UInt8 :=
  [0x49, 0xFF, 0xC3]

theorem code_l1106b3 : ∀ x ∈ codeRange 0x1106b3 bytes_l1106b3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x106b3 3 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1106b6 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1106b6 (testR64R64Effect 0x1106b6 10 10) (EffectPart.reads (.flag .ZF) [.gpr 10, .gpr 10] []) (.flag .ZF)) #v[10, 10]
    (.letOp (n := 54) (.exec 0x1106b6 (fun s => s.RIP = 0x1106b6) (testR64R64Effect 0x1106b6 10 10) (Reg.operands [.gpr 10, .gpr 10] [])) #v[10, 10]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l1106c0, RegMap.args [(2, 2), (4, 4), (5, 5), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l1106bb, RegMap.args [(2, 2), (4, 4), (5, 5), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l1106b6 : List UInt8 :=
  [0x4D, 0x85, 0xD2, 0x74, 0x05]

theorem code_l1106b6 : ∀ x ∈ codeRange 0x1106b6 bytes_l1106b6, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x106b6 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1106bb : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1106bb (cmpR64R64Effect 0x1106bb 11 9) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 9] []) (.flag .CF)) #v[11, 9]
    (.letOp (n := 54) (.exec 0x1106bb (fun s => s.RIP = 0x1106bb) (cmpR64R64Effect 0x1106bb 11 9) (Reg.operands [.gpr 11, .gpr 9] [])) #v[11, 9]
    (.letOp (n := 55) (.pure (condOp 2)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l1106b3, RegMap.args [(2, 2), (4, 4), (5, 5), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l1106c0, RegMap.args [(2, 2), (4, 4), (5, 5), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l1106bb : List UInt8 :=
  [0x4D, 0x39, 0xCB, 0x72, 0xF3]

theorem code_l1106bb : ∀ x ∈ codeRange 0x1106bb bytes_l1106bb, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x106bb 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1106c0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1106c0 (testR64R64Effect 0x1106c0 7 7) (EffectPart.reads (.flag .ZF) [.gpr 7, .gpr 7] []) (.flag .ZF)) #v[7, 7]
    (.letOp (n := 54) (.exec 0x1106c0 (fun s => s.RIP = 0x1106c0) (testR64R64Effect 0x1106c0 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[7, 7]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l1106d0, RegMap.args [(2, 2), (4, 4), (5, 5), (7, 7), (11, 11), (12, 12), (13, 13), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l1106c5, RegMap.args [(2, 2), (4, 4), (5, 5), (7, 7), (11, 11), (12, 12), (13, 13), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l1106c0 : List UInt8 :=
  [0x48, 0x85, 0xFF, 0x74, 0x0B]

theorem code_l1106c0 : ∀ x ∈ codeRange 0x1106c0 bytes_l1106c0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x106c0 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1106c5 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1106c5 (cmpR64R64Effect 0x1106c5 7 5) (EffectPart.reads (.flag .ZF) [.gpr 7, .gpr 5] []) (.flag .ZF)) #v[7, 5]
    (.letOp (n := 54) (.exec 0x1106c5 (fun s => s.RIP = 0x1106c5) (cmpR64R64Effect 0x1106c5 7 5) (Reg.operands [.gpr 7, .gpr 5] [])) #v[7, 5]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l1106a0, RegMap.args [(2, 2), (4, 4), (5, 5), (7, 7), (11, 11), (12, 12), (13, 13), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l1106ca, RegMap.args [(2, 2), (4, 4), (5, 5), (7, 7), (11, 11), (12, 12), (13, 13), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l1106c5 : List UInt8 :=
  [0x48, 0x39, 0xEF, 0x75, 0xD6]

theorem code_l1106c5 : ∀ x ∈ codeRange 0x1106c5 bytes_l1106c5, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x106c5 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1106ca : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1106ca (fun s => s.RIP = 0x1106ca) (fun _ => nopEffect 0x1106ca 6) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l1106d0, RegMap.args [(2, 2), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)] 54⟩))

def bytes_l1106ca : List UInt8 :=
  [0x66, 0x0F, 0x1F, 0x44, 0x00, 0x00]

theorem code_l1106ca : ∀ x ∈ codeRange 0x1106ca bytes_l1106ca, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x106ca 6 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1106d0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1106d0 (movR64M64Effect 0x1106d0 8 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 54) (.exec 0x1106d0 (LoadPre 0x1106d0 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1106d0 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1106d0 8 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1106d4 (movR64M64Effect 0x1106d4 9 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 56) (.exec 0x1106d4 (LoadPre 0x1106d4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1106d4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1106d4 9 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1106d9 (movR64M64Effect 0x1106d9 10 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 58) (.exec 0x1106d9 (LoadPre 0x1106d9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1106d9 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1106d9 10 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x1106de (testR64R64Effect 0x1106de 9 9) (EffectPart.reads (.flag .ZF) [.gpr 9, .gpr 9] []) (.flag .ZF)) #v[55, 55]
    (.letOp (n := 60) (.exec 0x1106de (fun s => s.RIP = 0x1106de) (testR64R64Effect 0x1106de 9 9) (Reg.operands [.gpr 9, .gpr 9] [])) #v[55, 55]
    (.letOp (n := 61) (.pure (condOp 5)) #v[59]
    (.terminate (.condBr (Fin.last 61) ⟨.l110278, RegMap.args [(2, 2), (4, 4), (5, 5), (8, 53), (9, 55), (10, 57), (11, 11), (12, 12), (13, 13), (14, 14), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ ⟨.l1106e7, RegMap.args [(2, 2), (4, 4), (5, 5), (8, 53), (9, 55), (10, 57), (11, 11), (12, 12), (13, 13), (14, 14), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩))))))))))

def bytes_l1106d0 : List UInt8 :=
  [0x4C, 0x8B, 0x04, 0x24, 0x4C, 0x8B, 0x4C, 0x24, 0x10, 0x4C, 0x8B, 0x54, 0x24, 0x08, 0x4D, 0x85,
    0xC9, 0x0F, 0x85, 0x91, 0xFB, 0xFF, 0xFF]

theorem code_l1106d0 : ∀ x ∈ codeRange 0x1106d0 bytes_l1106d0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x106d0 23 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1106e7 : Block Op Label signature Reg.count 53 :=
  .terminate (.br ⟨.l11075a, RegMap.args (entryMap (live .l1106e7)) 53⟩)

def bytes_l1106e7 : List UInt8 :=
  [0xEB, 0x71]

theorem code_l1106e7 : ∀ x ∈ codeRange 0x1106e7 bytes_l1106e7, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x106e7 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1106e9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1106e9 (cmpMImm8Effect 0x1106e9 5 64 (.sib 4 none 0 .none) 0x0) (EffectPart.reads (.flag .ZF) [.gpr 4] []) (.flag .ZF)) #v[4]
    (.letOp (n := 54) (.exec 0x1106e9 (LoadPre 0x1106e9 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1106e9 + BitVec.ofNat 64 5)) 8) (cmpMImm8Effect 0x1106e9 5 64 (.sib 4 none 0 .none) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1106ee (atFlags (condHolds 4) (setccR8Effect 0x1106ee 4 11)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 11))) #v[11, 53]
    (.letOp (n := 56) (.exec 0x1106ee (fun s => s.RIP = 0x1106ee) (atFlags (condHolds 4) (setccR8Effect 0x1106ee 4 11)) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[11, 53]
    (.letOp (n := 57) (.exec 0x1106f2 (StorePre 0x1106f2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x1106f2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1106f2 2 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2, 4]
    (.letOp (n := 58) (.exec 0x1106f7 (StorePre 0x1106f7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1106f7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1106f7 1 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1, 4]
    (.letOp (n := 59) (.out 0x1106fc (movR64M64Effect 0x1106fc 1 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 60) (.exec 0x1106fc (LoadPre 0x1106fc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1106fc + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1106fc 1 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x110701 (StorePre 0x110701 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x110701 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x110701 1 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.exec 0x110709 (StorePre 0x110709 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x110709 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x110709 0 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[0, 4]
    (.letOp (n := 63) (.exec 0x110711 (StorePre 0x110711 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x110711 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x110711 6 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[6, 4]
    (.letOp (n := 64) (.exec 0x110719 (StorePre 0x110719 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x110719 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x110719 (.sib 4 none 0 (.d8 0x68)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.exec 0x110722 (StorePre 0x110722 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x110722 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110722 14 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[14, 4]
    (.letOp (n := 66) (.out 0x110727 (cmpR64R64Effect 0x110727 9 10) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 10] []) (.flag .CF)) #v[9, 10]
    (.letOp (n := 67) (.exec 0x110727 (fun s => s.RIP = 0x110727) (cmpR64R64Effect 0x110727 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[9, 10]
    (.letOp (n := 68) (.out 0x11072a (atFlags (condHolds 3) (setccR8Effect 0x11072a 3 0)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 0))) #v[0, 66]
    (.letOp (n := 69) (.exec 0x11072a (fun s => s.RIP = 0x11072a) (atFlags (condHolds 3) (setccR8Effect 0x11072a 3 0)) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[0, 66]
    (.letOp (n := 70) (.out 0x11072d (orR8R8Effect 0x11072d 3 0 11) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 11] []) (.flag .ZF)) #v[68, 55]
    (.letOp (n := 71) (.exec 0x11072d (fun s => s.RIP = 0x11072d) (orR8R8Effect 0x11072d 3 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[68, 55]
    (.letOp (n := 72) (.pure (condOp 5)) #v[70]
    (.terminate (.condBr (Fin.last 72) ⟨.l110743, RegMap.args [(1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 55), (12, 12), (13, 13), (14, 14), (15, 15), (19, 70), (22, 22), (39, 39), (50, 50), (51, 51)] 73⟩ ⟨.l110732, RegMap.args [(1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 55), (12, 12), (13, 13), (14, 14), (15, 15), (19, 70), (22, 22), (39, 39), (50, 50), (51, 51)] 73⟩)))))))))))))))))))))

def bytes_l1106e9 : List UInt8 :=
  [0x48, 0x83, 0x3C, 0x24, 0x00, 0x41, 0x0F, 0x94, 0xC3, 0x48, 0x89, 0x54, 0x24, 0x70, 0x48, 0x89,
    0x4C, 0x24, 0x78, 0x48, 0x8B, 0x4C, 0x24, 0x18, 0x48, 0x89, 0x8C, 0x24, 0x80, 0x00, 0x00, 0x00,
    0x48, 0x89, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x89, 0xB4, 0x24, 0x90, 0x00, 0x00, 0x00,
    0x48, 0xC7, 0x44, 0x24, 0x68, 0x00, 0x00, 0x00, 0x00, 0x4C, 0x89, 0x74, 0x24, 0x58, 0x4D, 0x39,
    0xD1, 0x0F, 0x93, 0xC0, 0x44, 0x08, 0xD8, 0x75, 0x11]

theorem code_l1106e9 : ∀ x ∈ codeRange 0x1106e9 bytes_l1106e9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x106e9 73 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l110732 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x110732 (leaR64Effect 0x110732 0 (.base 9 (.d8 0x1))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[9]
    (.letOp (n := 54) (.exec 0x110732 (fun s => s.RIP = 0x110732) (leaR64Effect 0x110732 0 (.base 9 (.d8 0x1))) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 55) (.exec 0x110736 (StorePre 0x110736 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x110736 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x110736 0 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.terminate (.br ⟨.l1101c9, RegMap.args [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l110732 : List UInt8 :=
  [0x49, 0x8D, 0x41, 0x01, 0x48, 0x89, 0x84, 0x24, 0xB8, 0x00, 0x00, 0x00, 0xE9, 0x86, 0xFA, 0xFF,
    0xFF]

theorem code_l110732 : ∀ x ∈ codeRange 0x110732 bytes_l110732, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x10732 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l110743 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x110743 (leaR64Effect 0x110743 7 (.sib 4 none 0 (.d32 0x130))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x110743 (fun s => s.RIP = 0x110743) (leaR64Effect 0x110743 7 (.sib 4 none 0 (.d32 0x130))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x11074b (movR32Imm32Effect 0x11074b 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 56) (.exec 0x11074b (fun s => s.RIP = 0x11074b) (movR32Imm32Effect 0x11074b 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x110750 (movR64Imm32Effect 0x110750 6 0x202d48) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 58) (.exec 0x110750 (fun s => s.RIP = 0x110750) (movR64Imm32Effect 0x110750 6 0x202d48) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.exec 0x110757 (RepPre 0x110757 (RepMovsqPre 0x110757)) (repMovsqEffect 0x110757) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[57, 53, 55, 22]
    (.terminate (.br ⟨.l11075a, RegMap.args [(2, 2), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l110743 : List UInt8 :=
  [0x48, 0x8D, 0xBC, 0x24, 0x30, 0x01, 0x00, 0x00, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC6,
    0x48, 0x2D, 0x20, 0x00, 0xF3, 0x48, 0xA5]

theorem code_l110743 : ∀ x ∈ codeRange 0x110743 bytes_l110743, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x10743 23 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11075a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11075a (leaR64Effect 0x11075a 6 (.sib 4 none 0 (.d32 0x130))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 54) (.exec 0x11075a (fun s => s.RIP = 0x11075a) (leaR64Effect 0x11075a 6 (.sib 4 none 0 (.d32 0x130))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x110762 (movR32Imm32Effect 0x110762 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 56) (.exec 0x110762 (fun s => s.RIP = 0x110762) (movR32Imm32Effect 0x110762 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x110767 (movR64M64Effect 0x110767 0 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 58) (.exec 0x110767 (LoadPre 0x110767 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x110767 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x110767 0 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x11076f (movR64R64Effect 0x11076f 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[57]
    (.letOp (n := 60) (.exec 0x11076f (fun s => s.RIP = 0x11076f) (movR64R64Effect 0x11076f 7 0) (Reg.operands [.gpr 0] [])) #v[57]
    (.letOp (n := 61) (.out 0x110772 (repMovsqEffect 0x110772) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 6))) #v[53, 59, 55, 22]
    (.letOp (n := 62) (.out 0x110772 (repMovsqEffect 0x110772) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 7))) #v[53, 59, 55, 22]
    (.letOp (n := 63) (.out 0x110772 (repMovsqEffect 0x110772) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 1))) #v[53, 59, 55, 22]
    (.letOp (n := 64) (.exec 0x110772 (RepPre 0x110772 (RepMovsqPre 0x110772)) (repMovsqEffect 0x110772) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[53, 59, 55, 22]
    (.letOp (n := 65) (.out 0x110775 (addR64Imm32Effect 0x110775 4 0x1a8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 66) (.exec 0x110775 (fun s => s.RIP = 0x110775) (addR64Imm32Effect 0x110775 4 0x1a8) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x11077c (popR64Effect 0x11077c 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[65]
    (.letOp (n := 68) (.out 0x11077c (popR64Effect 0x11077c 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 69) (.exec 0x11077c (PopPre 0x11077c) (popR64Effect 0x11077c 1 3) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 70) (.out 0x11077d (popR64Effect 0x11077d 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[68]
    (.letOp (n := 71) (.out 0x11077d (popR64Effect 0x11077d 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[68]
    (.letOp (n := 72) (.exec 0x11077d (PopPre 0x11077d) (popR64Effect 0x11077d 2 12) (Reg.operands [.gpr 4] [])) #v[68]
    (.letOp (n := 73) (.out 0x11077f (popR64Effect 0x11077f 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[71]
    (.letOp (n := 74) (.out 0x11077f (popR64Effect 0x11077f 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[71]
    (.letOp (n := 75) (.exec 0x11077f (PopPre 0x11077f) (popR64Effect 0x11077f 2 13) (Reg.operands [.gpr 4] [])) #v[71]
    (.letOp (n := 76) (.out 0x110781 (popR64Effect 0x110781 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[74]
    (.letOp (n := 77) (.out 0x110781 (popR64Effect 0x110781 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[74]
    (.letOp (n := 78) (.exec 0x110781 (PopPre 0x110781) (popR64Effect 0x110781 2 14) (Reg.operands [.gpr 4] [])) #v[74]
    (.letOp (n := 79) (.out 0x110783 (popR64Effect 0x110783 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[77]
    (.letOp (n := 80) (.out 0x110783 (popR64Effect 0x110783 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[77]
    (.letOp (n := 81) (.exec 0x110783 (PopPre 0x110783) (popR64Effect 0x110783 2 15) (Reg.operands [.gpr 4] [])) #v[77]
    (.letOp (n := 82) (.out 0x110785 (popR64Effect 0x110785 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[80]
    (.letOp (n := 83) (.out 0x110785 (popR64Effect 0x110785 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[80]
    (.letOp (n := 84) (.exec 0x110785 (PopPre 0x110785) (popR64Effect 0x110785 1 5) (Reg.operands [.gpr 4] [])) #v[80]
    (.letOp (n := 85) (.out 0x110786 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[83]
    (.letOp (n := 86) (.out 0x110786 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[83]
    (.letOp (n := 87) (.exec 0x110786 (RetPre 0x110786) (retEffect) (Reg.operands [.gpr 4] [])) #v[83]
    (.terminate (.ret (RegMap.args [(0, 57), (1, 63), (2, 2), (3, 67), (4, 86), (5, 82), (6, 61), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (12, 70), (13, 73), (14, 76), (15, 79), (22, 22), (39, 39), (50, 50), (51, 51)] 88) (some ⟨85, by decide⟩)))))))))))))))))))))))))))))))))))))

def bytes_l11075a : List UInt8 :=
  [0x48, 0x8D, 0xB4, 0x24, 0x30, 0x01, 0x00, 0x00, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x84,
    0x24, 0xD0, 0x00, 0x00, 0x00, 0x48, 0x89, 0xC7, 0xF3, 0x48, 0xA5, 0x48, 0x81, 0xC4, 0xA8, 0x01,
    0x00, 0x00, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l11075a : ∀ x ∈ codeRange 0x11075a bytes_l11075a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1075a 45 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l110787 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x110787 (movR32Imm32Effect 0x110787 5 6 0x8) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 54) (.exec 0x110787 (fun s => s.RIP = 0x110787) (movR32Imm32Effect 0x110787 5 6 0x8) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x11078c (movR64Imm32Effect 0x11078c 2 0x202cd0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 56) (.exec 0x11078c (fun s => s.RIP = 0x11078c) (movR64Imm32Effect 0x11078c 2 0x202cd0) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x110793 (callEffect (fun _ => 0x1295f2) 0x110798) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x110793 (PushPre 0x110793 5) (callEffect (fun _ => 0x1295f2) 0x110798) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x110798⟩) #v[]
    (.terminate (.call ⟨.l1295f2, RegMap.args [(2, 55), (4, 57), (5, 5), (6, 53), (7, 7)] 60⟩ { target := .l110798, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l110787 : List UInt8 :=
  [0xBE, 0x08, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC2, 0xD0, 0x2C, 0x20, 0x00, 0xE8, 0x5A, 0x8E, 0x01,
    0x00]

theorem code_l110787 : ∀ x ∈ codeRange 0x110787 bytes_l110787, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x10787 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l110798 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x110798 (movR32Imm32Effect 0x110798 5 6 0x8) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 54) (.exec 0x110798 (fun s => s.RIP = 0x110798) (movR32Imm32Effect 0x110798 5 6 0x8) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x11079d (movR64Imm32Effect 0x11079d 2 0x202cb8) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 56) (.exec 0x11079d (fun s => s.RIP = 0x11079d) (movR64Imm32Effect 0x11079d 2 0x202cb8) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x1107a4 (callEffect (fun _ => 0x1295f2) 0x1107a9) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x1107a4 (PushPre 0x1107a4 5) (callEffect (fun _ => 0x1295f2) 0x1107a9) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x1107a9⟩) #v[]
    (.terminate (.call ⟨.l1295f2, RegMap.args [(2, 55), (4, 57), (5, 5), (6, 53), (7, 7)] 60⟩ { target := .l1107a9, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l110798 : List UInt8 :=
  [0xBE, 0x08, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC2, 0xB8, 0x2C, 0x20, 0x00, 0xE8, 0x49, 0x8E, 0x01,
    0x00]

theorem code_l110798 : ∀ x ∈ codeRange 0x110798 bytes_l110798, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x10798 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1107a9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1107a9 (fun s => s.RIP = 0x1107a9) (fun _ => nopEffect 0x1107a9 7) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l1107b0, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 54⟩))

def bytes_l1107a9 : List UInt8 :=
  [0x0F, 0x1F, 0x80, 0x00, 0x00, 0x00, 0x00]

theorem code_l1107a9 : ∀ x ∈ codeRange 0x1107a9 bytes_l1107a9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x107a9 7 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1107b0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1107b0 (pushR64Effect 0x1107b0 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x1107b0 (PushPre 0x1107b0 1) (pushR64Effect 0x1107b0 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x1107b1 (pushR64Effect 0x1107b1 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x1107b1 (PushPre 0x1107b1 2) (pushR64Effect 0x1107b1 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x1107b3 (pushR64Effect 0x1107b3 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x1107b3 (PushPre 0x1107b3 2) (pushR64Effect 0x1107b3 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x1107b5 (pushR64Effect 0x1107b5 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x1107b5 (PushPre 0x1107b5 2) (pushR64Effect 0x1107b5 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x1107b7 (pushR64Effect 0x1107b7 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x1107b7 (PushPre 0x1107b7 2) (pushR64Effect 0x1107b7 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x1107b9 (pushR64Effect 0x1107b9 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x1107b9 (PushPre 0x1107b9 1) (pushR64Effect 0x1107b9 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x1107ba (subR64Imm8Effect 0x1107ba 4 0x58) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x1107ba (fun s => s.RIP = 0x1107ba) (subR64Imm8Effect 0x1107ba 4 0x58) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x1107be (movR64R64Effect 0x1107be 12 9) (EffectPart.reads (.reg (.gpr 12)) [.gpr 9] []) (.reg (.gpr 12))) #v[9]
    (.letOp (n := 68) (.exec 0x1107be (fun s => s.RIP = 0x1107be) (movR64R64Effect 0x1107be 12 9) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 69) (.out 0x1107c1 (movR64R64Effect 0x1107c1 13 8) (EffectPart.reads (.reg (.gpr 13)) [.gpr 8] []) (.reg (.gpr 13))) #v[8]
    (.letOp (n := 70) (.exec 0x1107c1 (fun s => s.RIP = 0x1107c1) (movR64R64Effect 0x1107c1 13 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 71) (.out 0x1107c4 (movR64R64Effect 0x1107c4 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[1]
    (.letOp (n := 72) (.exec 0x1107c4 (fun s => s.RIP = 0x1107c4) (movR64R64Effect 0x1107c4 0 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 73) (.out 0x1107c7 (movR64R64Effect 0x1107c7 15 6) (EffectPart.reads (.reg (.gpr 15)) [.gpr 6] []) (.reg (.gpr 15))) #v[6]
    (.letOp (n := 74) (.exec 0x1107c7 (fun s => s.RIP = 0x1107c7) (movR64R64Effect 0x1107c7 15 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 75) (.exec 0x1107ca (StorePre 0x1107ca 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1107ca + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1107ca 7 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[7, 65]
    (.letOp (n := 76) (.out 0x1107cf (movR32Imm32Effect 0x1107cf 5 3 0x1) (EffectPart.reads (.reg (.gpr 3)) [] []) (.reg (.gpr 3))) #v[]
    (.letOp (n := 77) (.exec 0x1107cf (fun s => s.RIP = 0x1107cf) (movR32Imm32Effect 0x1107cf 5 3 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 78) (.out 0x1107d4 (movR32R32Effect 0x1107d4 3 1 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 12] []) (.reg (.gpr 1))) #v[67]
    (.letOp (n := 79) (.exec 0x1107d4 (fun s => s.RIP = 0x1107d4) (movR32R32Effect 0x1107d4 3 1 12) (Reg.operands [.gpr 12] [])) #v[67]
    (.letOp (n := 80) (.out 0x1107d7 (shlR64ClEffect 0x1107d7 3 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[76, 78]
    (.letOp (n := 81) (.exec 0x1107d7 (fun s => s.RIP = 0x1107d7) (shlR64ClEffect 0x1107d7 3 3) (Reg.operands [.gpr 3, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[76, 78]
    (.letOp (n := 82) (.out 0x1107da (leaR64Effect 0x1107da 7 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[65]
    (.letOp (n := 83) (.exec 0x1107da (fun s => s.RIP = 0x1107da) (leaR64Effect 0x1107da 7 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 84) (.out 0x1107df (movR64R64Effect 0x1107df 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[2]
    (.letOp (n := 85) (.exec 0x1107df (fun s => s.RIP = 0x1107df) (movR64R64Effect 0x1107df 6 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 86) (.out 0x1107e2 (movR64R64Effect 0x1107e2 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0] []) (.reg (.gpr 2))) #v[71]
    (.letOp (n := 87) (.exec 0x1107e2 (fun s => s.RIP = 0x1107e2) (movR64R64Effect 0x1107e2 2 0) (Reg.operands [.gpr 0] [])) #v[71]
    (.letOp (n := 88) (.out 0x1107e5 (callEffect (fun _ => 0x1241e0) 0x1107ea) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 89) (.exec 0x1107e5 (PushPre 0x1107e5 5) (callEffect (fun _ => 0x1241e0) 0x1107ea) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 90) (.const ⟨64, 0x1107ea⟩) #v[]
    (.terminate (.call ⟨.l1241e0, RegMap.args [(0, 71), (1, 78), (2, 86), (3, 80), (4, 88), (5, 5), (6, 84), (7, 82), (8, 8), (9, 9), (10, 10), (11, 11), (12, 67), (13, 69), (14, 14), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)] 91⟩ { target := .l1107ea, kept := #v[], arity := rfl, guard := some (Fin.last 90) })))))))))))))))))))))))))))))))))))))))

def bytes_l1107b0 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x83, 0xEC, 0x58, 0x4D, 0x89,
    0xCC, 0x4D, 0x89, 0xC5, 0x48, 0x89, 0xC8, 0x49, 0x89, 0xF7, 0x48, 0x89, 0x7C, 0x24, 0x10, 0xBB,
    0x01, 0x00, 0x00, 0x00, 0x44, 0x89, 0xE1, 0x48, 0xD3, 0xE3, 0x48, 0x8D, 0x7C, 0x24, 0x30, 0x48,
    0x89, 0xD6, 0x48, 0x89, 0xC2, 0xE8, 0xF6, 0x39, 0x01, 0x00]

theorem code_l1107b0 : ∀ x ∈ codeRange 0x1107b0 bytes_l1107b0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x107b0 58 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1107ea : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1107ea (xorR32R32Effect 0x1107ea 3 14 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 14] []) (.reg (.gpr 14))) #v[14, 14]
    (.letOp (n := 54) (.exec 0x1107ea (fun s => s.RIP = 0x1107ea) (xorR32R32Effect 0x1107ea 3 14 14) (Reg.operands [.gpr 14, .gpr 14] [])) #v[14, 14]
    (.letOp (n := 55) (.exec 0x1107ed (StorePre 0x1107ed 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1107ed + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1107ed 13 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[13, 4]
    (.letOp (n := 56) (.out 0x1107f2 (testR64R64Effect 0x1107f2 13 13) (EffectPart.reads (.flag .ZF) [.gpr 13, .gpr 13] []) (.flag .ZF)) #v[13, 13]
    (.letOp (n := 57) (.exec 0x1107f2 (fun s => s.RIP = 0x1107f2) (testR64R64Effect 0x1107f2 13 13) (Reg.operands [.gpr 13, .gpr 13] [])) #v[13, 13]
    (.letOp (n := 58) (.pure (condOp 4)) #v[56]
    (.terminate (.condBr (Fin.last 58) ⟨.l110955, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩ ⟨.l1107fb, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l1107ea : List UInt8 :=
  [0x45, 0x31, 0xF6, 0x4C, 0x89, 0x6C, 0x24, 0x18, 0x4D, 0x85, 0xED, 0x0F, 0x84, 0x5A, 0x01, 0x00,
    0x00]

theorem code_l1107ea : ∀ x ∈ codeRange 0x1107ea bytes_l1107ea, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x107ea 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1107fb : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1107fb (StorePre 0x1107fb 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1107fb + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1107fb 15 (.sib 4 none 0 .none)) (Reg.operands [.gpr 15, .gpr 4] [])) #v[15, 4]
    (.letOp (n := 54) (.out 0x1107ff (leaR64Effect 0x1107ff 0 (.base 3 (.d8 0xff))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 55) (.exec 0x1107ff (fun s => s.RIP = 0x1107ff) (leaR64Effect 0x1107ff 0 (.base 3 (.d8 0xff))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 56) (.exec 0x110803 (StorePre 0x110803 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x110803 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110803 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[54, 4]
    (.letOp (n := 57) (.out 0x110808 (movR64R64Effect 0x110808 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 58) (.exec 0x110808 (fun s => s.RIP = 0x110808) (movR64R64Effect 0x110808 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 59) (.out 0x11080b (shrR64Effect 0x11080b 3 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[57]
    (.letOp (n := 60) (.exec 0x11080b (fun s => s.RIP = 0x11080b) (shrR64Effect 0x11080b 3 0 1) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[57]
    (.letOp (n := 61) (.exec 0x11080e (StorePre 0x11080e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11080e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11080e 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x110813 (movzxR32R8Effect 0x110813 3 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 63) (.exec 0x110813 (fun s => s.RIP = 0x110813) (movzxR32R8Effect 0x110813 3 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 64) (.exec 0x110816 (StorePre 0x110816 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x110816 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x110816 0 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x11081a (xorR32R32Effect 0x11081a 2 5 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 5] []) (.reg (.gpr 5))) #v[5, 5]
    (.letOp (n := 66) (.exec 0x11081a (fun s => s.RIP = 0x11081a) (xorR32R32Effect 0x11081a 2 5 5) (Reg.operands [.gpr 5, .gpr 5] [])) #v[5, 5]
    (.letOp (n := 67) (.out 0x11081c (xorR32R32Effect 0x11081c 3 15 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 15] []) (.reg (.gpr 15))) #v[15, 15]
    (.letOp (n := 68) (.exec 0x11081c (fun s => s.RIP = 0x11081c) (xorR32R32Effect 0x11081c 3 15 15) (Reg.operands [.gpr 15, .gpr 15] [])) #v[15, 15]
    (.letOp (n := 69) (.out 0x11081f (xorR32R32Effect 0x11081f 3 13 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 13] []) (.reg (.gpr 13))) #v[13, 13]
    (.letOp (n := 70) (.exec 0x11081f (fun s => s.RIP = 0x11081f) (xorR32R32Effect 0x11081f 3 13 13) (Reg.operands [.gpr 13, .gpr 13] [])) #v[13, 13]
    (.terminate (.br ⟨.l110847, RegMap.args [(0, 62), (2, 2), (3, 3), (4, 4), (5, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 69), (14, 14), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 71⟩)))))))))))))))))))

def bytes_l1107fb : List UInt8 :=
  [0x4C, 0x89, 0x3C, 0x24, 0x48, 0x8D, 0x43, 0xFF, 0x48, 0x89, 0x44, 0x24, 0x28, 0x48, 0x89, 0xD8,
    0x48, 0xD1, 0xE8, 0x48, 0x89, 0x44, 0x24, 0x20, 0x0F, 0xB6, 0xC3, 0x89, 0x44, 0x24, 0x0C, 0x31,
    0xED, 0x45, 0x31, 0xFF, 0x45, 0x31, 0xED, 0xEB, 0x23]

theorem code_l1107fb : ∀ x ∈ codeRange 0x1107fb bytes_l1107fb, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x107fb 41 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l110830 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x110830 (incR64Effect 0x110830 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[14]
    (.letOp (n := 54) (.exec 0x110830 (fun s => s.RIP = 0x110830) (incR64Effect 0x110830 14) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[14]
    (.terminate (.br ⟨.l110833, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l110830 : List UInt8 :=
  [0x49, 0xFF, 0xC6]

theorem code_l110830 : ∀ x ∈ codeRange 0x110830 bytes_l110830, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x10830 3 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l110833 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x110833 (addR64R64Effect 0x110833 15 5) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 5] []) (.reg (.gpr 15))) #v[15, 5]
    (.letOp (n := 54) (.exec 0x110833 (fun s => s.RIP = 0x110833) (addR64R64Effect 0x110833 15 5) (Reg.operands [.gpr 15, .gpr 5] [])) #v[15, 5]
    (.letOp (n := 55) (.out 0x110836 (movR64R64Effect 0x110836 5 15) (EffectPart.reads (.reg (.gpr 5)) [.gpr 15] []) (.reg (.gpr 5))) #v[53]
    (.letOp (n := 56) (.exec 0x110836 (fun s => s.RIP = 0x110836) (movR64R64Effect 0x110836 5 15) (Reg.operands [.gpr 15] [])) #v[53]
    (.letOp (n := 57) (.out 0x110839 (negR64Effect 0x110839 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5] []) (.reg (.gpr 5))) #v[55]
    (.letOp (n := 58) (.exec 0x110839 (fun s => s.RIP = 0x110839) (negR64Effect 0x110839 5) (Reg.operands [.gpr 5] [])) #v[55]
    (.letOp (n := 59) (.out 0x11083c (cmpR64M64Effect 0x11083c 15 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 4] []) (.flag .CF)) #v[53, 4]
    (.letOp (n := 60) (.exec 0x11083c (LoadPre 0x11083c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11083c + BitVec.ofNat 64 5)) 8) (cmpR64M64Effect 0x11083c 15 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 61) (.pure (condOp 3)) #v[59]
    (.terminate (.condBr (Fin.last 61) ⟨.l11093a, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 57), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (16, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ ⟨.l110847, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 57), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (16, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩))))))))))

def bytes_l110833 : List UInt8 :=
  [0x49, 0x01, 0xEF, 0x4C, 0x89, 0xFD, 0x48, 0xF7, 0xDD, 0x4C, 0x3B, 0x7C, 0x24, 0x18, 0x0F, 0x83,
    0xF3, 0x00, 0x00, 0x00]

theorem code_l110833 : ∀ x ∈ codeRange 0x110833 bytes_l110833, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x10833 20 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l110847 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x110847 (movR64R64Effect 0x110847 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 54) (.exec 0x110847 (fun s => s.RIP = 0x110847) (movR64R64Effect 0x110847 6 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.out 0x11084a (shrR64Effect 0x11084a 4 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[53]
    (.letOp (n := 56) (.exec 0x11084a (fun s => s.RIP = 0x11084a) (shrR64Effect 0x11084a 4 6 6) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 57) (.out 0x11084e (movR32R32Effect 0x11084e 3 3 15) (EffectPart.reads (.reg (.gpr 3)) [.gpr 15] []) (.reg (.gpr 3))) #v[15]
    (.letOp (n := 58) (.exec 0x11084e (fun s => s.RIP = 0x11084e) (movR32R32Effect 0x11084e 3 3 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 59) (.out 0x110851 (andR32Imm8Effect 0x110851 3 3 0x3f) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[57]
    (.letOp (n := 60) (.exec 0x110851 (fun s => s.RIP = 0x110851) (andR32Imm8Effect 0x110851 3 3 0x3f) (Reg.operands [.gpr 3] [])) #v[57]
    (.letOp (n := 61) (.out 0x110854 (leaR64Effect 0x110854 7 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 62) (.exec 0x110854 (fun s => s.RIP = 0x110854) (leaR64Effect 0x110854 7 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x110859 (callEffect (fun _ => 0x124100) 0x11085e) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 64) (.exec 0x110859 (PushPre 0x110859 5) (callEffect (fun _ => 0x124100) 0x11085e) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.const ⟨64, 0x11085e⟩) #v[]
    (.terminate (.call ⟨.l124100, RegMap.args [(0, 0), (2, 2), (3, 59), (4, 63), (5, 5), (6, 55), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩ { target := .l11085e, kept := #v[], arity := rfl, guard := some (Fin.last 65) }))))))))))))))

def bytes_l110847 : List UInt8 :=
  [0x4C, 0x89, 0xFE, 0x48, 0xC1, 0xEE, 0x06, 0x44, 0x89, 0xFB, 0x83, 0xE3, 0x3F, 0x48, 0x8D, 0x7C,
    0x24, 0x30, 0xE8, 0xA2, 0x38, 0x01, 0x00]

theorem code_l110847 : ∀ x ∈ codeRange 0x110847 bytes_l110847, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x10847 23 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11085e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11085e (leaR64Effect 0x11085e 1 (.sib 3 (some 12) 0 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 3, .gpr 12] []) (.reg (.gpr 1))) #v[3, 12]
    (.letOp (n := 54) (.exec 0x11085e (fun s => s.RIP = 0x11085e) (leaR64Effect 0x11085e 1 (.sib 3 (some 12) 0 .none)) (Reg.operands [.gpr 3, .gpr 12] [])) #v[3, 12]
    (.letOp (n := 55) (.out 0x110862 (cmpR64Imm8Effect 0x110862 1 0x40) (EffectPart.reads (.flag .CF) [.gpr 1] []) (.flag .CF)) #v[53]
    (.letOp (n := 56) (.exec 0x110862 (fun s => s.RIP = 0x110862) (cmpR64Imm8Effect 0x110862 1 0x40) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 3)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l110880, RegMap.args [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l110868, RegMap.args [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l11085e : List UInt8 :=
  [0x4A, 0x8D, 0x0C, 0x23, 0x48, 0x83, 0xF9, 0x40, 0x73, 0x18]

theorem code_l11085e : ∀ x ∈ codeRange 0x11085e bytes_l11085e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1085e 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l110868 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x110868 (movR32R32Effect 0x110868 2 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 3] []) (.reg (.gpr 1))) #v[3]
    (.letOp (n := 54) (.exec 0x110868 (fun s => s.RIP = 0x110868) (movR32R32Effect 0x110868 2 1 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x11086a (shrR64ClEffect 0x11086a 3 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[0, 53]
    (.letOp (n := 56) (.exec 0x11086a (fun s => s.RIP = 0x11086a) (shrR64ClEffect 0x11086a 3 0) (Reg.operands [.gpr 0, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[0, 53]
    (.letOp (n := 57) (.out 0x11086d (movR64R64Effect 0x11086d 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0] []) (.reg (.gpr 2))) #v[55]
    (.letOp (n := 58) (.exec 0x11086d (fun s => s.RIP = 0x11086d) (movR64R64Effect 0x11086d 2 0) (Reg.operands [.gpr 0] [])) #v[55]
    (.terminate (.br ⟨.l11088d, RegMap.args [(0, 55), (1, 53), (2, 57), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l110868 : List UInt8 :=
  [0x89, 0xD9, 0x48, 0xD3, 0xE8, 0x48, 0x89, 0xC2, 0xEB, 0x1B]

theorem code_l110868 : ∀ x ∈ codeRange 0x110868 bytes_l110868, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x10868 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l110880 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x110880 (movR32R32Effect 0x110880 2 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 3] []) (.reg (.gpr 1))) #v[3]
    (.letOp (n := 54) (.exec 0x110880 (fun s => s.RIP = 0x110880) (movR32R32Effect 0x110880 2 1 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x110882 (shrR64ClEffect 0x110882 3 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[0, 53]
    (.letOp (n := 56) (.exec 0x110882 (fun s => s.RIP = 0x110882) (shrR64ClEffect 0x110882 3 0) (Reg.operands [.gpr 0, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[0, 53]
    (.letOp (n := 57) (.out 0x110885 (movR32R32Effect 0x110885 2 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[5]
    (.letOp (n := 58) (.exec 0x110885 (fun s => s.RIP = 0x110885) (movR32R32Effect 0x110885 2 1 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 59) (.out 0x110887 (shlR64ClEffect 0x110887 3 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[2, 57]
    (.letOp (n := 60) (.exec 0x110887 (fun s => s.RIP = 0x110887) (shlR64ClEffect 0x110887 3 2) (Reg.operands [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2, 57]
    (.letOp (n := 61) (.out 0x11088a (orR64R64Effect 0x11088a 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[59, 55]
    (.letOp (n := 62) (.exec 0x11088a (fun s => s.RIP = 0x11088a) (orR64R64Effect 0x11088a 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[59, 55]
    (.terminate (.br ⟨.l11088d, RegMap.args [(0, 55), (1, 57), (2, 61), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 63⟩)))))))))))

def bytes_l110880 : List UInt8 :=
  [0x89, 0xD9, 0x48, 0xD3, 0xE8, 0x89, 0xE9, 0x48, 0xD3, 0xE2, 0x48, 0x09, 0xC2]

theorem code_l110880 : ∀ x ∈ codeRange 0x110880 bytes_l110880, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x10880 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11088d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11088d (andR64M64Effect 0x11088d 2 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 4] []) (.reg (.gpr 2))) #v[2, 4]
    (.letOp (n := 54) (.exec 0x11088d (LoadPre 0x11088d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11088d + BitVec.ofNat 64 5)) 8) (andR64M64Effect 0x11088d 2 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2, 4]
    (.letOp (n := 55) (.out 0x110892 (addR64R64Effect 0x110892 2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 13] []) (.reg (.gpr 2))) #v[53, 13]
    (.letOp (n := 56) (.exec 0x110892 (fun s => s.RIP = 0x110892) (addR64R64Effect 0x110892 2 13) (Reg.operands [.gpr 2, .gpr 13] [])) #v[53, 13]
    (.letOp (n := 57) (.out 0x110895 (testR8Imm8LowEffect 0x110895 2 0x1) (EffectPart.reads (.flag .ZF) [.gpr 2] []) (.flag .ZF)) #v[55]
    (.letOp (n := 58) (.exec 0x110895 (fun s => s.RIP = 0x110895) (testR8Imm8LowEffect 0x110895 2 0x1) (Reg.operands [.gpr 2] [])) #v[55]
    (.letOp (n := 59) (.out 0x110898 (movR64M64Effect 0x110898 6 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 60) (.exec 0x110898 (LoadPre 0x110898 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x110898 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x110898 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.pure (condOp 5)) #v[57]
    (.terminate (.condBr (Fin.last 61) ⟨.l1108d0, RegMap.args [(0, 0), (1, 1), (2, 55), (4, 4), (5, 5), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ ⟨.l11089f, RegMap.args [(0, 0), (1, 1), (2, 55), (4, 4), (5, 5), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩))))))))))

def bytes_l11088d : List UInt8 :=
  [0x48, 0x23, 0x54, 0x24, 0x28, 0x4C, 0x01, 0xEA, 0xF6, 0xC2, 0x01, 0x48, 0x8B, 0x74, 0x24, 0x10,
    0x75, 0x31]

theorem code_l11088d : ∀ x ∈ codeRange 0x11088d bytes_l11088d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1088d 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11089f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11089f (cmpMREffect 0x11089f 4 64 14 (.sib 4 none 0 .none)) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 4] []) (.flag .CF)) #v[14, 4]
    (.letOp (n := 54) (.out 0x11089f (cmpMREffect 0x11089f 4 64 14 (.sib 4 none 0 .none)) (EffectPart.reads (.flag .ZF) [.gpr 14, .gpr 4] []) (.flag .ZF)) #v[14, 4]
    (.letOp (n := 55) (.exec 0x11089f (LoadPre 0x11089f (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x11089f + BitVec.ofNat 64 4)) 8) (cmpMREffect 0x11089f 4 64 14 (.sib 4 none 0 .none)) (Reg.operands [.gpr 14, .gpr 4] [])) #v[14, 4]
    (.letOp (n := 56) (.pure (condOp 6)) #v[53, 54]
    (.terminate (.condBr (Fin.last 56) ⟨.l11097a, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩ ⟨.l1108a9, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l11089f : List UInt8 :=
  [0x4C, 0x39, 0x34, 0x24, 0x0F, 0x86, 0xD1, 0x00, 0x00, 0x00]

theorem code_l11089f : ∀ x ∈ codeRange 0x11089f bytes_l11089f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1089f 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1108a9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1108a9 (StorePre 0x1108a9 5 (fun s => AddrMode.addr (.sib 6 (some 14) 0 .none) s (0x1108a9 + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x1108a9 (.sib 6 (some 14) 0 .none) 0x0) (Reg.operands [.gpr 6, .gpr 14] [])) #v[6, 14]
    (.letOp (n := 54) (.out 0x1108ae (incR64Effect 0x1108ae 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[14]
    (.letOp (n := 55) (.exec 0x1108ae (fun s => s.RIP = 0x1108ae) (incR64Effect 0x1108ae 14) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[14]
    (.letOp (n := 56) (.out 0x1108b1 (incR64Effect 0x1108b1 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[15]
    (.letOp (n := 57) (.exec 0x1108b1 (fun s => s.RIP = 0x1108b1) (incR64Effect 0x1108b1 15) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[15]
    (.letOp (n := 58) (.out 0x1108b4 (movR64R64Effect 0x1108b4 5 15) (EffectPart.reads (.reg (.gpr 5)) [.gpr 15] []) (.reg (.gpr 5))) #v[56]
    (.letOp (n := 59) (.exec 0x1108b4 (fun s => s.RIP = 0x1108b4) (movR64R64Effect 0x1108b4 5 15) (Reg.operands [.gpr 15] [])) #v[56]
    (.letOp (n := 60) (.out 0x1108b7 (negR64Effect 0x1108b7 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5] []) (.reg (.gpr 5))) #v[58]
    (.letOp (n := 61) (.exec 0x1108b7 (fun s => s.RIP = 0x1108b7) (negR64Effect 0x1108b7 5) (Reg.operands [.gpr 5] [])) #v[58]
    (.letOp (n := 62) (.out 0x1108ba (cmpR64M64Effect 0x1108ba 15 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 4] []) (.flag .CF)) #v[56, 4]
    (.letOp (n := 63) (.exec 0x1108ba (LoadPre 0x1108ba (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1108ba + BitVec.ofNat 64 5)) 8) (cmpR64M64Effect 0x1108ba 15 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 64) (.pure (condOp 2)) #v[62]
    (.terminate (.condBr (Fin.last 64) ⟨.l110847, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 60), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 54), (15, 56), (16, 62), (22, 22), (39, 39), (50, 50), (51, 51)] 65⟩ ⟨.l1108c1, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 60), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 54), (15, 56), (16, 62), (22, 22), (39, 39), (50, 50), (51, 51)] 65⟩)))))))))))))

def bytes_l1108a9 : List UInt8 :=
  [0x42, 0xC6, 0x04, 0x36, 0x00, 0x49, 0xFF, 0xC6, 0x49, 0xFF, 0xC7, 0x4C, 0x89, 0xFD, 0x48, 0xF7,
    0xDD, 0x4C, 0x3B, 0x7C, 0x24, 0x18, 0x72, 0x86]

theorem code_l1108a9 : ∀ x ∈ codeRange 0x1108a9 bytes_l1108a9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x108a9 24 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1108c1 : Block Op Label signature Reg.count 53 :=
  .terminate (.br ⟨.l11093a, RegMap.args (entryMap (live .l1108c1)) 53⟩)

def bytes_l1108c1 : List UInt8 :=
  [0xEB, 0x77]

theorem code_l1108c1 : ∀ x ∈ codeRange 0x1108c1 bytes_l1108c1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x108c1 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1108d0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1108d0 (movR64M64Effect 0x1108d0 0 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1108d0 (LoadPre 0x1108d0 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1108d0 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1108d0 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1108d4 (subR64R64Effect 0x1108d4 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[53, 14]
    (.letOp (n := 56) (.out 0x1108d4 (subR64R64Effect 0x1108d4 0 14) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 14] []) (.flag .CF)) #v[53, 14]
    (.letOp (n := 57) (.out 0x1108d4 (subR64R64Effect 0x1108d4 0 14) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 14] []) (.flag .ZF)) #v[53, 14]
    (.letOp (n := 58) (.exec 0x1108d4 (fun s => s.RIP = 0x1108d4) (subR64R64Effect 0x1108d4 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 59) (.pure (condOp 6)) #v[56, 57]
    (.terminate (.condBr (Fin.last 59) ⟨.l11098d, RegMap.args [(0, 55), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 56), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l1108dd, RegMap.args [(0, 55), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 56), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l1108d0 : List UInt8 :=
  [0x48, 0x8B, 0x04, 0x24, 0x4C, 0x29, 0xF0, 0x0F, 0x86, 0xB0, 0x00, 0x00, 0x00]

theorem code_l1108d0 : ∀ x ∈ codeRange 0x1108d0 bytes_l1108d0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x108d0 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1108dd : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1108dd (xorR32R32Effect 0x1108dd 3 13 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 13] []) (.reg (.gpr 13))) #v[13, 13]
    (.letOp (n := 54) (.exec 0x1108dd (fun s => s.RIP = 0x1108dd) (xorR32R32Effect 0x1108dd 3 13 13) (Reg.operands [.gpr 13, .gpr 13] [])) #v[13, 13]
    (.letOp (n := 55) (.out 0x1108e0 (cmpR64M64Effect 0x1108e0 2 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.flag .CF) [.gpr 2, .gpr 4] []) (.flag .CF)) #v[2, 4]
    (.letOp (n := 56) (.exec 0x1108e0 (LoadPre 0x1108e0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1108e0 + BitVec.ofNat 64 5)) 8) (cmpR64M64Effect 0x1108e0 2 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2, 4]
    (.letOp (n := 57) (.out 0x1108e5 (atFlags (condHolds 3) (setccR8Effect 0x1108e5 4 13)) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 13))) #v[53, 55]
    (.letOp (n := 58) (.exec 0x1108e5 (fun s => s.RIP = 0x1108e5) (atFlags (condHolds 3) (setccR8Effect 0x1108e5 4 13)) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[53, 55]
    (.letOp (n := 59) (.out 0x1108e9 (movR32Imm32Effect 0x1108e9 5 1 0x0) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 60) (.exec 0x1108e9 (fun s => s.RIP = 0x1108e9) (movR32Imm32Effect 0x1108e9 5 1 0x0) (Reg.operands [] [])) #v[]
    (.letOp (n := 61) (.out 0x1108ee (atFlags (condHolds 3) (cmovR32M32Effect 0x1108ee 5 1 (.sib 4 none 0 (.d8 0xc)))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 1))) #v[59, 4, 55]
    (.letOp (n := 62) (.exec 0x1108ee (LoadPre 0x1108ee (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x1108ee + BitVec.ofNat 64 5)) 4) (atFlags (condHolds 3) (cmovR32M32Effect 0x1108ee 5 1 (.sib 4 none 0 (.d8 0xc)))) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[59, 4, 55]
    (.letOp (n := 63) (.out 0x1108f3 (subR8R8Effect 0x1108f3 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[2, 61]
    (.letOp (n := 64) (.exec 0x1108f3 (fun s => s.RIP = 0x1108f3) (subR8R8Effect 0x1108f3 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[2, 61]
    (.letOp (n := 65) (.exec 0x1108f5 (StorePre 0x1108f5 4 (fun s => AddrMode.addr (.sib 6 (some 14) 0 .none) s (0x1108f5 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1108f5 4 2 (.sib 6 (some 14) 0 .none)) (Reg.operands [.gpr 2, .gpr 6, .gpr 14] [])) #v[63, 6, 14]
    (.letOp (n := 66) (.out 0x1108f9 (addR64M64Effect 0x1108f9 5 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 4] []) (.reg (.gpr 5))) #v[5, 4]
    (.letOp (n := 67) (.exec 0x1108f9 (LoadPre 0x1108f9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1108f9 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x1108f9 5 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[5, 4]
    (.letOp (n := 68) (.out 0x1108fe (subR64R64Effect 0x1108fe 5 13) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 13] []) (.reg (.gpr 5))) #v[66, 57]
    (.letOp (n := 69) (.exec 0x1108fe (fun s => s.RIP = 0x1108fe) (subR64R64Effect 0x1108fe 5 13) (Reg.operands [.gpr 5, .gpr 13] [])) #v[66, 57]
    (.letOp (n := 70) (.out 0x110901 (cmpR64R64Effect 0x110901 5 12) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 12] []) (.flag .CF)) #v[68, 12]
    (.letOp (n := 71) (.exec 0x110901 (fun s => s.RIP = 0x110901) (cmpR64R64Effect 0x110901 5 12) (Reg.operands [.gpr 5, .gpr 12] [])) #v[68, 12]
    (.letOp (n := 72) (.out 0x110904 (atFlags (condHolds 3) (cmovR64R64Effect 0x110904 4 5 12)) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 5))) #v[68, 12, 70]
    (.letOp (n := 73) (.exec 0x110904 (fun s => s.RIP = 0x110904) (atFlags (condHolds 3) (cmovR64R64Effect 0x110904 4 5 12)) (Reg.operands [.gpr 5, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[68, 12, 70]
    (.letOp (n := 74) (.out 0x110908 (cmpR64Imm8Effect 0x110908 5 0x2) (EffectPart.reads (.flag .CF) [.gpr 5] []) (.flag .CF)) #v[72]
    (.letOp (n := 75) (.exec 0x110908 (fun s => s.RIP = 0x110908) (cmpR64Imm8Effect 0x110908 5 0x2) (Reg.operands [.gpr 5] [])) #v[72]
    (.letOp (n := 76) (.pure (condOp 2)) #v[74]
    (.terminate (.condBr (Fin.last 76) ⟨.l110830, RegMap.args [(0, 0), (1, 61), (2, 63), (4, 4), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 57), (14, 14), (15, 15), (16, 74), (22, 22), (39, 39), (50, 50), (51, 51)] 77⟩ ⟨.l110912, RegMap.args [(0, 0), (1, 61), (2, 63), (4, 4), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 57), (14, 14), (15, 15), (16, 74), (22, 22), (39, 39), (50, 50), (51, 51)] 77⟩)))))))))))))))))))))))))

def bytes_l1108dd : List UInt8 :=
  [0x45, 0x31, 0xED, 0x48, 0x3B, 0x54, 0x24, 0x20, 0x41, 0x0F, 0x93, 0xC5, 0xB9, 0x00, 0x00, 0x00,
    0x00, 0x0F, 0x43, 0x4C, 0x24, 0x0C, 0x28, 0xCA, 0x42, 0x88, 0x14, 0x36, 0x48, 0x03, 0x6C, 0x24,
    0x18, 0x4C, 0x29, 0xED, 0x4C, 0x39, 0xE5, 0x49, 0x0F, 0x43, 0xEC, 0x48, 0x83, 0xFD, 0x02, 0x0F,
    0x82, 0x1E, 0xFF, 0xFF, 0xFF]

theorem code_l1108dd : ∀ x ∈ codeRange 0x1108dd bytes_l1108dd, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x108dd 53 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l110912 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x110912 (leaR64Effect 0x110912 1 (.sib 14 (some 5) 0 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14, .gpr 5] []) (.reg (.gpr 1))) #v[14, 5]
    (.letOp (n := 54) (.exec 0x110912 (fun s => s.RIP = 0x110912) (leaR64Effect 0x110912 1 (.sib 14 (some 5) 0 .none)) (Reg.operands [.gpr 14, .gpr 5] [])) #v[14, 5]
    (.letOp (n := 55) (.out 0x110916 (addR64R64Effect 0x110916 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 6] []) (.reg (.gpr 14))) #v[14, 6]
    (.letOp (n := 56) (.exec 0x110916 (fun s => s.RIP = 0x110916) (addR64R64Effect 0x110916 14 6) (Reg.operands [.gpr 14, .gpr 6] [])) #v[14, 6]
    (.letOp (n := 57) (.out 0x110919 (movR32Imm32Effect 0x110919 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x110919 (fun s => s.RIP = 0x110919) (movR32Imm32Effect 0x110919 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.exec 0x11091e (fun s => s.RIP = 0x11091e) (fun _ => nopEffect 0x11091e 2) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l110920, RegMap.args [(0, 0), (1, 53), (2, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l110912 : List UInt8 :=
  [0x49, 0x8D, 0x0C, 0x2E, 0x49, 0x01, 0xF6, 0xBA, 0x01, 0x00, 0x00, 0x00, 0x66, 0x90]

theorem code_l110912 : ∀ x ∈ codeRange 0x110912 bytes_l110912, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x10912 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l110920 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x110920 (cmpR64R64Effect 0x110920 0 2) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 2] []) (.flag .ZF)) #v[0, 2]
    (.letOp (n := 54) (.exec 0x110920 (fun s => s.RIP = 0x110920) (cmpR64R64Effect 0x110920 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[0, 2]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l110967, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l110925, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l110920 : List UInt8 :=
  [0x48, 0x39, 0xD0, 0x74, 0x42]

theorem code_l110920 : ∀ x ∈ codeRange 0x110920 bytes_l110920, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x10920 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l110925 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x110925 (StorePre 0x110925 5 (fun s => AddrMode.addr (.sib 14 (some 2) 0 .none) s (0x110925 + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x110925 (.sib 14 (some 2) 0 .none) 0x0) (Reg.operands [.gpr 14, .gpr 2] [])) #v[14, 2]
    (.letOp (n := 54) (.out 0x11092a (incR64Effect 0x11092a 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[2]
    (.letOp (n := 55) (.exec 0x11092a (fun s => s.RIP = 0x11092a) (incR64Effect 0x11092a 2) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2]
    (.letOp (n := 56) (.out 0x11092d (cmpR64R64Effect 0x11092d 5 2) (EffectPart.reads (.flag .ZF) [.gpr 5, .gpr 2] []) (.flag .ZF)) #v[5, 54]
    (.letOp (n := 57) (.exec 0x11092d (fun s => s.RIP = 0x11092d) (cmpR64R64Effect 0x11092d 5 2) (Reg.operands [.gpr 5, .gpr 2] [])) #v[5, 54]
    (.letOp (n := 58) (.pure (condOp 5)) #v[56]
    (.terminate (.condBr (Fin.last 58) ⟨.l110920, RegMap.args [(0, 0), (1, 1), (2, 54), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩ ⟨.l110932, RegMap.args [(0, 0), (1, 1), (2, 54), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l110925 : List UInt8 :=
  [0x41, 0xC6, 0x04, 0x16, 0x00, 0x48, 0xFF, 0xC2, 0x48, 0x39, 0xD5, 0x75, 0xEE]

theorem code_l110925 : ∀ x ∈ codeRange 0x110925 bytes_l110925, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x10925 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l110932 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x110932 (movR64R64Effect 0x110932 14 1) (EffectPart.reads (.reg (.gpr 14)) [.gpr 1] []) (.reg (.gpr 14))) #v[1]
    (.letOp (n := 54) (.exec 0x110932 (fun s => s.RIP = 0x110932) (movR64R64Effect 0x110932 14 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.terminate (.br ⟨.l110833, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l110932 : List UInt8 :=
  [0x49, 0x89, 0xCE, 0xE9, 0xF9, 0xFE, 0xFF, 0xFF]

theorem code_l110932 : ∀ x ∈ codeRange 0x110932 bytes_l110932, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x10932 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11093a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11093a (testR64R64Effect 0x11093a 13 13) (EffectPart.reads (.flag .ZF) [.gpr 13, .gpr 13] []) (.flag .ZF)) #v[13, 13]
    (.letOp (n := 54) (.exec 0x11093a (fun s => s.RIP = 0x11093a) (testR64R64Effect 0x11093a 13 13) (Reg.operands [.gpr 13, .gpr 13] [])) #v[13, 13]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l110955, RegMap.args [(1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l11093f, RegMap.args [(1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l11093a : List UInt8 :=
  [0x4D, 0x85, 0xED, 0x74, 0x16]

theorem code_l11093a : ∀ x ∈ codeRange 0x11093a bytes_l11093a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1093a 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11093f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11093f (movR64M64Effect 0x11093f 6 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 54) (.exec 0x11093f (LoadPre 0x11093f (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x11093f + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11093f 6 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x110943 (cmpR64R64Effect 0x110943 14 6) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 6] []) (.flag .CF)) #v[14, 53]
    (.letOp (n := 56) (.exec 0x110943 (fun s => s.RIP = 0x110943) (cmpR64R64Effect 0x110943 14 6) (Reg.operands [.gpr 14, .gpr 6] [])) #v[14, 53]
    (.letOp (n := 57) (.pure (condOp 3)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l1109a0, RegMap.args [(1, 1), (2, 2), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l110948, RegMap.args [(1, 1), (2, 2), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l11093f : List UInt8 :=
  [0x48, 0x8B, 0x34, 0x24, 0x49, 0x39, 0xF6, 0x73, 0x58]

theorem code_l11093f : ∀ x ∈ codeRange 0x11093f bytes_l11093f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1093f 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l110948 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x110948 (movR64M64Effect 0x110948 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x110948 (LoadPre 0x110948 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x110948 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x110948 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x11094d (StorePre 0x11094d 5 (fun s => AddrMode.addr (.sib 0 (some 14) 0 .none) s (0x11094d + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x11094d (.sib 0 (some 14) 0 .none) 0x1) (Reg.operands [.gpr 0, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 56) (.out 0x110952 (incR64Effect 0x110952 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[14]
    (.letOp (n := 57) (.exec 0x110952 (fun s => s.RIP = 0x110952) (incR64Effect 0x110952 14) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[14]
    (.terminate (.br ⟨.l110955, RegMap.args [(0, 53), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l110948 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x10, 0x42, 0xC6, 0x04, 0x30, 0x01, 0x49, 0xFF, 0xC6]

theorem code_l110948 : ∀ x ∈ codeRange 0x110948 bytes_l110948, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x10948 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l110955 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x110955 (movR64R64Effect 0x110955 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[14]
    (.letOp (n := 54) (.exec 0x110955 (fun s => s.RIP = 0x110955) (movR64R64Effect 0x110955 0 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 55) (.out 0x110958 (addR64Imm8Effect 0x110958 4 0x58) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 56) (.exec 0x110958 (fun s => s.RIP = 0x110958) (addR64Imm8Effect 0x110958 4 0x58) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x11095c (popR64Effect 0x11095c 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[55]
    (.letOp (n := 58) (.out 0x11095c (popR64Effect 0x11095c 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[55]
    (.letOp (n := 59) (.exec 0x11095c (PopPre 0x11095c) (popR64Effect 0x11095c 1 3) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 60) (.out 0x11095d (popR64Effect 0x11095d 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[58]
    (.letOp (n := 61) (.out 0x11095d (popR64Effect 0x11095d 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[58]
    (.letOp (n := 62) (.exec 0x11095d (PopPre 0x11095d) (popR64Effect 0x11095d 2 12) (Reg.operands [.gpr 4] [])) #v[58]
    (.letOp (n := 63) (.out 0x11095f (popR64Effect 0x11095f 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[61]
    (.letOp (n := 64) (.out 0x11095f (popR64Effect 0x11095f 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 65) (.exec 0x11095f (PopPre 0x11095f) (popR64Effect 0x11095f 2 13) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 66) (.out 0x110961 (popR64Effect 0x110961 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[64]
    (.letOp (n := 67) (.out 0x110961 (popR64Effect 0x110961 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[64]
    (.letOp (n := 68) (.exec 0x110961 (PopPre 0x110961) (popR64Effect 0x110961 2 14) (Reg.operands [.gpr 4] [])) #v[64]
    (.letOp (n := 69) (.out 0x110963 (popR64Effect 0x110963 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[67]
    (.letOp (n := 70) (.out 0x110963 (popR64Effect 0x110963 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[67]
    (.letOp (n := 71) (.exec 0x110963 (PopPre 0x110963) (popR64Effect 0x110963 2 15) (Reg.operands [.gpr 4] [])) #v[67]
    (.letOp (n := 72) (.out 0x110965 (popR64Effect 0x110965 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[70]
    (.letOp (n := 73) (.out 0x110965 (popR64Effect 0x110965 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[70]
    (.letOp (n := 74) (.exec 0x110965 (PopPre 0x110965) (popR64Effect 0x110965 1 5) (Reg.operands [.gpr 4] [])) #v[70]
    (.letOp (n := 75) (.out 0x110966 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[73]
    (.letOp (n := 76) (.out 0x110966 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[73]
    (.letOp (n := 77) (.exec 0x110966 (RetPre 0x110966) (retEffect) (Reg.operands [.gpr 4] [])) #v[73]
    (.terminate (.ret (RegMap.args [(0, 53), (1, 1), (2, 2), (3, 57), (4, 76), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 78) (some ⟨75, by decide⟩)))))))))))))))))))))))))))

def bytes_l110955 : List UInt8 :=
  [0x4C, 0x89, 0xF0, 0x48, 0x83, 0xC4, 0x58, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F,
    0x5D, 0xC3]

theorem code_l110955 : ∀ x ∈ codeRange 0x110955 bytes_l110955, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x10955 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l110967 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x110967 (movR64M64Effect 0x110967 7 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x110967 (LoadPre 0x110967 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x110967 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x110967 7 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x11096b (movR64R64Effect 0x11096b 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 7] []) (.reg (.gpr 6))) #v[53]
    (.letOp (n := 56) (.exec 0x11096b (fun s => s.RIP = 0x11096b) (movR64R64Effect 0x11096b 6 7) (Reg.operands [.gpr 7] [])) #v[53]
    (.letOp (n := 57) (.out 0x11096e (movR64Imm32Effect 0x11096e 2 0x202d30) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x11096e (fun s => s.RIP = 0x11096e) (movR64Imm32Effect 0x11096e 2 0x202d30) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x110975 (callEffect (fun _ => 0x1295f2) 0x11097a) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x110975 (PushPre 0x110975 5) (callEffect (fun _ => 0x1295f2) 0x11097a) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x11097a⟩) #v[]
    (.terminate (.call ⟨.l1295f2, RegMap.args [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)] 62⟩ { target := .l11097a, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l110967 : List UInt8 :=
  [0x48, 0x8B, 0x3C, 0x24, 0x48, 0x89, 0xFE, 0x48, 0xC7, 0xC2, 0x30, 0x2D, 0x20, 0x00, 0xE8, 0x78,
    0x8C, 0x01, 0x00]

theorem code_l110967 : ∀ x ∈ codeRange 0x110967 bytes_l110967, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x10967 19 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11097a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11097a (movR64R64Effect 0x11097a 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 54) (.exec 0x11097a (fun s => s.RIP = 0x11097a) (movR64R64Effect 0x11097a 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 55) (.out 0x11097d (movR64M64Effect 0x11097d 6 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 56) (.exec 0x11097d (LoadPre 0x11097d (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x11097d + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11097d 6 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x110981 (movR64Imm32Effect 0x110981 2 0x202d00) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x110981 (fun s => s.RIP = 0x110981) (movR64Imm32Effect 0x110981 2 0x202d00) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x110988 (callEffect (fun _ => 0x1295f2) 0x11098d) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x110988 (PushPre 0x110988 5) (callEffect (fun _ => 0x1295f2) 0x11098d) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x11098d⟩) #v[]
    (.terminate (.call ⟨.l1295f2, RegMap.args [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53), (14, 14)] 62⟩ { target := .l11098d, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l11097a : List UInt8 :=
  [0x4C, 0x89, 0xF7, 0x48, 0x8B, 0x34, 0x24, 0x48, 0xC7, 0xC2, 0x00, 0x2D, 0x20, 0x00, 0xE8, 0x65,
    0x8C, 0x01, 0x00]

theorem code_l11097a : ∀ x ∈ codeRange 0x11097a bytes_l11097a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1097a 19 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11098d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11098d (movR64R64Effect 0x11098d 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 54) (.exec 0x11098d (fun s => s.RIP = 0x11098d) (movR64R64Effect 0x11098d 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 55) (.out 0x110990 (movR64M64Effect 0x110990 6 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 56) (.exec 0x110990 (LoadPre 0x110990 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x110990 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x110990 6 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x110994 (movR64Imm32Effect 0x110994 2 0x202d18) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x110994 (fun s => s.RIP = 0x110994) (movR64Imm32Effect 0x110994 2 0x202d18) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x11099b (callEffect (fun _ => 0x1295f2) 0x1109a0) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x11099b (PushPre 0x11099b 5) (callEffect (fun _ => 0x1295f2) 0x1109a0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x1109a0⟩) #v[]
    (.terminate (.call ⟨.l1295f2, RegMap.args [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53), (14, 14)] 62⟩ { target := .l1109a0, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l11098d : List UInt8 :=
  [0x4C, 0x89, 0xF7, 0x48, 0x8B, 0x34, 0x24, 0x48, 0xC7, 0xC2, 0x18, 0x2D, 0x20, 0x00, 0xE8, 0x52,
    0x8C, 0x01, 0x00]

theorem code_l11098d : ∀ x ∈ codeRange 0x11098d bytes_l11098d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1098d 19 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1109a0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1109a0 (movR64R64Effect 0x1109a0 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 54) (.exec 0x1109a0 (fun s => s.RIP = 0x1109a0) (movR64R64Effect 0x1109a0 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 55) (.out 0x1109a3 (movR64Imm32Effect 0x1109a3 2 0x202ce8) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 56) (.exec 0x1109a3 (fun s => s.RIP = 0x1109a3) (movR64Imm32Effect 0x1109a3 2 0x202ce8) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x1109aa (callEffect (fun _ => 0x1295f2) 0x1109af) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x1109aa (PushPre 0x1109aa 5) (callEffect (fun _ => 0x1295f2) 0x1109af) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x1109af⟩) #v[]
    (.terminate (.call ⟨.l1295f2, RegMap.args [(2, 55), (4, 57), (5, 5), (6, 6), (7, 53), (14, 14)] 60⟩ { target := .l1109af, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l1109a0 : List UInt8 :=
  [0x4C, 0x89, 0xF7, 0x48, 0xC7, 0xC2, 0xE8, 0x2C, 0x20, 0x00, 0xE8, 0x43, 0x8C, 0x01, 0x00]

theorem code_l1109a0 : ∀ x ∈ codeRange 0x1109a0 bytes_l1109a0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x109a0 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1109af : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1109af (fun s => s.RIP = 0x1109af) (fun _ => nopEffect 0x1109af 1) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l1109b0, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 54⟩))

def bytes_l1109af : List UInt8 :=
  [0x90]

theorem code_l1109af : ∀ x ∈ codeRange 0x1109af bytes_l1109af, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x109af 1 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1109b0_7 : Block Op Label signature Reg.count 326 :=
  .letOp (n := 326) (.out 0x110b70 (popR64Effect 0x110b70 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[324]
    (.letOp (n := 327) (.out 0x110b70 (popR64Effect 0x110b70 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[324]
    (.letOp (n := 328) (.exec 0x110b70 (PopPre 0x110b70) (popR64Effect 0x110b70 1 5) (Reg.operands [.gpr 4] [])) #v[324]
    (.letOp (n := 329) (.out 0x110b71 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[327]
    (.letOp (n := 330) (.out 0x110b71 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[327]
    (.letOp (n := 331) (.exec 0x110b71 (RetPre 0x110b71) (retEffect) (Reg.operands [.gpr 4] [])) #v[327]
    (.terminate (.ret (RegMap.args [(0, 234), (1, 303), (2, 281), (3, 311), (4, 330), (5, 326), (6, 292), (7, 270), (8, 297), (9, 286), (10, 275), (11, 264), (12, 314), (13, 317), (14, 320), (15, 323), (22, 22), (39, 39), (50, 50), (51, 51)] 332) (some ⟨329, by decide⟩))))))))

def bytes_l1109b0_7 : List UInt8 :=
  [0x5D, 0xC3]

theorem code_l1109b0_7 : ∀ x ∈ codeRange 0x110b70 bytes_l1109b0_7, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x10b70 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1109b0_6 : Block Op Label signature Reg.count 286 :=
  .letOp (n := 286) (.out 0x110b35 (xorR64R64Effect 0x110b35 9 14) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 14] []) (.reg (.gpr 9))) #v[102, 180]
    (.letOp (n := 287) (.exec 0x110b35 (fun s => s.RIP = 0x110b35) (xorR64R64Effect 0x110b35 9 14) (Reg.operands [.gpr 9, .gpr 14] [])) #v[102, 180]
    (.letOp (n := 288) (.out 0x110b38 (negR64Effect 0x110b38 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[284]
    (.letOp (n := 289) (.exec 0x110b38 (fun s => s.RIP = 0x110b38) (negR64Effect 0x110b38 6) (Reg.operands [.gpr 6] [])) #v[284]
    (.letOp (n := 290) (.out 0x110b3b (andR64R64Effect 0x110b3b 6 9) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 9] []) (.reg (.gpr 6))) #v[288, 286]
    (.letOp (n := 291) (.exec 0x110b3b (fun s => s.RIP = 0x110b3b) (andR64R64Effect 0x110b3b 6 9) (Reg.operands [.gpr 6, .gpr 9] [])) #v[288, 286]
    (.letOp (n := 292) (.out 0x110b3e (xorR64R64Effect 0x110b3e 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 14] []) (.reg (.gpr 6))) #v[290, 180]
    (.letOp (n := 293) (.exec 0x110b3e (fun s => s.RIP = 0x110b3e) (xorR64R64Effect 0x110b3e 6 14) (Reg.operands [.gpr 6, .gpr 14] [])) #v[290, 180]
    (.letOp (n := 294) (.exec 0x110b41 (StorePre 0x110b41 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x110b41 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x110b41 3 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 1, .gpr 4] [])) #v[240, 65]
    (.letOp (n := 295) (.out 0x110b44 (movzxR32M8Effect 0x110b44 4 1 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 296) (.exec 0x110b44 (LoadPre 0x110b44 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x110b44 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x110b44 4 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 297) (.out 0x110b48 (xorR64R64Effect 0x110b48 8 15) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 15] []) (.reg (.gpr 8))) #v[105, 211]
    (.letOp (n := 298) (.exec 0x110b48 (fun s => s.RIP = 0x110b48) (xorR64R64Effect 0x110b48 8 15) (Reg.operands [.gpr 8, .gpr 15] [])) #v[105, 211]
    (.letOp (n := 299) (.out 0x110b4b (negR64Effect 0x110b4b 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[295]
    (.letOp (n := 300) (.exec 0x110b4b (fun s => s.RIP = 0x110b4b) (negR64Effect 0x110b4b 1) (Reg.operands [.gpr 1] [])) #v[295]
    (.letOp (n := 301) (.out 0x110b4e (andR64R64Effect 0x110b4e 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8] []) (.reg (.gpr 1))) #v[299, 297]
    (.letOp (n := 302) (.exec 0x110b4e (fun s => s.RIP = 0x110b4e) (andR64R64Effect 0x110b4e 1 8) (Reg.operands [.gpr 1, .gpr 8] [])) #v[299, 297]
    (.letOp (n := 303) (.out 0x110b51 (xorR64R64Effect 0x110b51 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 15] []) (.reg (.gpr 1))) #v[301, 211]
    (.letOp (n := 304) (.exec 0x110b51 (fun s => s.RIP = 0x110b51) (xorR64R64Effect 0x110b51 1 15) (Reg.operands [.gpr 1, .gpr 15] [])) #v[301, 211]
    (.letOp (n := 305) (.exec 0x110b54 (StorePre 0x110b54 3 (fun s => AddrMode.addr (.base 0 .none) s (0x110b54 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x110b54 7 (.base 0 .none)) (Reg.operands [.gpr 7, .gpr 0] [])) #v[270, 234]
    (.letOp (n := 306) (.exec 0x110b57 (StorePre 0x110b57 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x110b57 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110b57 2 (.base 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 0] [])) #v[281, 234]
    (.letOp (n := 307) (.exec 0x110b5b (StorePre 0x110b5b 4 (fun s => AddrMode.addr (.base 0 (.d8 0x10)) s (0x110b5b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110b5b 6 (.base 0 (.d8 0x10))) (Reg.operands [.gpr 6, .gpr 0] [])) #v[292, 234]
    (.letOp (n := 308) (.exec 0x110b5f (StorePre 0x110b5f 4 (fun s => AddrMode.addr (.base 0 (.d8 0x18)) s (0x110b5f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110b5f 1 (.base 0 (.d8 0x18))) (Reg.operands [.gpr 1, .gpr 0] [])) #v[303, 234]
    (.letOp (n := 309) (.out 0x110b63 (addR64Imm8Effect 0x110b63 4 0x10) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 310) (.exec 0x110b63 (fun s => s.RIP = 0x110b63) (addR64Imm8Effect 0x110b63 4 0x10) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 311) (.out 0x110b67 (popR64Effect 0x110b67 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[309]
    (.letOp (n := 312) (.out 0x110b67 (popR64Effect 0x110b67 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[309]
    (.letOp (n := 313) (.exec 0x110b67 (PopPre 0x110b67) (popR64Effect 0x110b67 1 3) (Reg.operands [.gpr 4] [])) #v[309]
    (.letOp (n := 314) (.out 0x110b68 (popR64Effect 0x110b68 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[312]
    (.letOp (n := 315) (.out 0x110b68 (popR64Effect 0x110b68 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[312]
    (.letOp (n := 316) (.exec 0x110b68 (PopPre 0x110b68) (popR64Effect 0x110b68 2 12) (Reg.operands [.gpr 4] [])) #v[312]
    (.letOp (n := 317) (.out 0x110b6a (popR64Effect 0x110b6a 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[315]
    (.letOp (n := 318) (.out 0x110b6a (popR64Effect 0x110b6a 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[315]
    (.letOp (n := 319) (.exec 0x110b6a (PopPre 0x110b6a) (popR64Effect 0x110b6a 2 13) (Reg.operands [.gpr 4] [])) #v[315]
    (.letOp (n := 320) (.out 0x110b6c (popR64Effect 0x110b6c 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[318]
    (.letOp (n := 321) (.out 0x110b6c (popR64Effect 0x110b6c 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[318]
    (.letOp (n := 322) (.exec 0x110b6c (PopPre 0x110b6c) (popR64Effect 0x110b6c 2 14) (Reg.operands [.gpr 4] [])) #v[318]
    (.letOp (n := 323) (.out 0x110b6e (popR64Effect 0x110b6e 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[321]
    (.letOp (n := 324) (.out 0x110b6e (popR64Effect 0x110b6e 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[321]
    (.letOp (n := 325) (.exec 0x110b6e (PopPre 0x110b6e) (popR64Effect 0x110b6e 2 15) (Reg.operands [.gpr 4] [])) #v[321]
    (b_l1109b0_7))))))))))))))))))))))))))))))))))))))))

def bytes_l1109b0_6 : List UInt8 :=
  [0x4D, 0x31, 0xF1, 0x48, 0xF7, 0xDE, 0x4C, 0x21, 0xCE, 0x4C, 0x31, 0xF6, 0x88, 0x0C, 0x24, 0x0F,
    0xB6, 0x0C, 0x24, 0x4D, 0x31, 0xF8, 0x48, 0xF7, 0xD9, 0x4C, 0x21, 0xC1, 0x4C, 0x31, 0xF9, 0x48,
    0x89, 0x38, 0x48, 0x89, 0x50, 0x08, 0x48, 0x89, 0x70, 0x10, 0x48, 0x89, 0x48, 0x18, 0x48, 0x83,
    0xC4, 0x10, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F] ++ bytes_l1109b0_7

theorem code_l1109b0_6 : ∀ x ∈ codeRange 0x110b35 bytes_l1109b0_6, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x10b35 59 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1109b0_7

@[cfg_block] def b_l1109b0_5 : Block Op Label signature Reg.count 252 :=
  .letOp (n := 252) (.out 0x110af2 (addM8Imm8Effect 0x110af2 5 (.sib 4 none 0 (.d8 0xf)) 0xff) (EffectPart.reads (.flag .CF) [.gpr 4] []) (.flag .CF)) #v[65]
    (.letOp (n := 253) (.exec 0x110af2 (StorePre 0x110af2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x110af2 + BitVec.ofNat 64 5)) 1) (addM8Imm8Effect 0x110af2 5 (.sib 4 none 0 (.d8 0xf)) 0xff) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 254) (.out 0x110af7 (atFlags StatusFlags.CF (adcR64R64Effect 0x110af7 7 3)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[250, 97, 252]
    (.letOp (n := 255) (.exec 0x110af7 (fun s => s.RIP = 0x110af7) (atFlags StatusFlags.CF (adcR64R64Effect 0x110af7 7 3)) (Reg.operands [.gpr 7, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[250, 97, 252]
    (.letOp (n := 256) (.out 0x110afa (shrR64Effect 0x110afa 4 7 63) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[254]
    (.letOp (n := 257) (.exec 0x110afa (fun s => s.RIP = 0x110afa) (shrR64Effect 0x110afa 4 7 63) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[254]
    (.letOp (n := 258) (.exec 0x110afe (StorePre 0x110afe 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x110afe + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110afe 7 (.sib 4 none 0 .none)) (Reg.operands [.gpr 7, .gpr 4] [])) #v[256, 65]
    (.letOp (n := 259) (.exec 0x110b02 (fun s => s.RIP = 0x110b02) (movR64R64Effect 0x110b02 7 4) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 260) (.exec 0x110b05 (StorePre 0x110b05 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x110b05 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x110b05 3 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 1, .gpr 4] [])) #v[240, 65]
    (.letOp (n := 261) (.exec 0x110b08 (fun s => s.RIP = 0x110b08) (movR64R64Effect 0x110b08 3 4) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 262) (.out 0x110b0b (movzxR32M8Effect 0x110b0b 4 7 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[65]
    (.letOp (n := 263) (.exec 0x110b0b (LoadPre 0x110b0b (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x110b0b + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x110b0b 4 7 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 264) (.out 0x110b0f (xorR64R64Effect 0x110b0f 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 2] []) (.reg (.gpr 11))) #v[71, 117]
    (.letOp (n := 265) (.exec 0x110b0f (fun s => s.RIP = 0x110b0f) (xorR64R64Effect 0x110b0f 11 2) (Reg.operands [.gpr 11, .gpr 2] [])) #v[71, 117]
    (.letOp (n := 266) (.out 0x110b12 (negR64Effect 0x110b12 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[262]
    (.letOp (n := 267) (.exec 0x110b12 (fun s => s.RIP = 0x110b12) (negR64Effect 0x110b12 7) (Reg.operands [.gpr 7] [])) #v[262]
    (.letOp (n := 268) (.out 0x110b15 (andR64R64Effect 0x110b15 7 11) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 11] []) (.reg (.gpr 7))) #v[266, 264]
    (.letOp (n := 269) (.exec 0x110b15 (fun s => s.RIP = 0x110b15) (andR64R64Effect 0x110b15 7 11) (Reg.operands [.gpr 7, .gpr 11] [])) #v[266, 264]
    (.letOp (n := 270) (.out 0x110b18 (xorR64R64Effect 0x110b18 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2] []) (.reg (.gpr 7))) #v[268, 117]
    (.letOp (n := 271) (.exec 0x110b18 (fun s => s.RIP = 0x110b18) (xorR64R64Effect 0x110b18 7 2) (Reg.operands [.gpr 7, .gpr 2] [])) #v[268, 117]
    (.letOp (n := 272) (.exec 0x110b1b (StorePre 0x110b1b 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x110b1b + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x110b1b 3 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 1, .gpr 4] [])) #v[240, 65]
    (.letOp (n := 273) (.out 0x110b1e (movzxR32M8Effect 0x110b1e 4 2 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[65]
    (.letOp (n := 274) (.exec 0x110b1e (LoadPre 0x110b1e (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x110b1e + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x110b1e 4 2 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 275) (.out 0x110b22 (xorR64R64Effect 0x110b22 10 6) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 6] []) (.reg (.gpr 10))) #v[99, 149]
    (.letOp (n := 276) (.exec 0x110b22 (fun s => s.RIP = 0x110b22) (xorR64R64Effect 0x110b22 10 6) (Reg.operands [.gpr 10, .gpr 6] [])) #v[99, 149]
    (.letOp (n := 277) (.out 0x110b25 (negR64Effect 0x110b25 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[273]
    (.letOp (n := 278) (.exec 0x110b25 (fun s => s.RIP = 0x110b25) (negR64Effect 0x110b25 2) (Reg.operands [.gpr 2] [])) #v[273]
    (.letOp (n := 279) (.out 0x110b28 (andR64R64Effect 0x110b28 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 10] []) (.reg (.gpr 2))) #v[277, 275]
    (.letOp (n := 280) (.exec 0x110b28 (fun s => s.RIP = 0x110b28) (andR64R64Effect 0x110b28 2 10) (Reg.operands [.gpr 2, .gpr 10] [])) #v[277, 275]
    (.letOp (n := 281) (.out 0x110b2b (xorR64R64Effect 0x110b2b 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[279, 149]
    (.letOp (n := 282) (.exec 0x110b2b (fun s => s.RIP = 0x110b2b) (xorR64R64Effect 0x110b2b 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[279, 149]
    (.letOp (n := 283) (.exec 0x110b2e (StorePre 0x110b2e 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x110b2e + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x110b2e 3 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 1, .gpr 4] [])) #v[240, 65]
    (.letOp (n := 284) (.out 0x110b31 (movzxR32M8Effect 0x110b31 4 6 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[65]
    (.letOp (n := 285) (.exec 0x110b31 (LoadPre 0x110b31 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x110b31 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x110b31 4 6 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (b_l1109b0_6))))))))))))))))))))))))))))))))))

def bytes_l1109b0_5 : List UInt8 :=
  [0x80, 0x44, 0x24, 0x0F, 0xFF, 0x48, 0x11, 0xDF, 0x48, 0xC1, 0xEF, 0x3F, 0x48, 0x89, 0x3C, 0x24,
    0x48, 0x89, 0xE7, 0x88, 0x0C, 0x24, 0x48, 0x89, 0xE3, 0x0F, 0xB6, 0x3C, 0x24, 0x49, 0x31, 0xD3,
    0x48, 0xF7, 0xDF, 0x4C, 0x21, 0xDF, 0x48, 0x31, 0xD7, 0x88, 0x0C, 0x24, 0x0F, 0xB6, 0x14, 0x24,
    0x49, 0x31, 0xF2, 0x48, 0xF7, 0xDA, 0x4C, 0x21, 0xD2, 0x48, 0x31, 0xF2, 0x88, 0x0C, 0x24, 0x0F,
    0xB6, 0x34, 0x24] ++ bytes_l1109b0_6

theorem code_l1109b0_5 : ∀ x ∈ codeRange 0x110af2 bytes_l1109b0_5, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x10af2 67 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1109b0_6

@[cfg_block] def b_l1109b0_4 : Block Op Label signature Reg.count 215 :=
  .letOp (n := 215) (.out 0x110ab1 (notR64Effect 0x110ab1 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[213]
    (.letOp (n := 216) (.exec 0x110ab1 (fun s => s.RIP = 0x110ab1) (notR64Effect 0x110ab1 13) (Reg.operands [.gpr 13] [])) #v[213]
    (.letOp (n := 217) (.out 0x110ab4 (movR64R64Effect 0x110ab4 5 1) (EffectPart.reads (.reg (.gpr 5)) [.gpr 1] []) (.reg (.gpr 5))) #v[203]
    (.letOp (n := 218) (.exec 0x110ab4 (fun s => s.RIP = 0x110ab4) (movR64R64Effect 0x110ab4 5 1) (Reg.operands [.gpr 1] [])) #v[203]
    (.letOp (n := 219) (.out 0x110ab7 (andR64R64Effect 0x110ab7 5 13) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 13] []) (.reg (.gpr 5))) #v[217, 215]
    (.letOp (n := 220) (.exec 0x110ab7 (fun s => s.RIP = 0x110ab7) (andR64R64Effect 0x110ab7 5 13) (Reg.operands [.gpr 5, .gpr 13] [])) #v[217, 215]
    (.letOp (n := 221) (.out 0x110aba (orR64R64Effect 0x110aba 13 1) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 1] []) (.reg (.gpr 13))) #v[215, 203]
    (.letOp (n := 222) (.exec 0x110aba (fun s => s.RIP = 0x110aba) (orR64R64Effect 0x110aba 13 1) (Reg.operands [.gpr 13, .gpr 1] [])) #v[215, 203]
    (.letOp (n := 223) (.out 0x110abd (andR64R64Effect 0x110abd 13 15) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 15] []) (.reg (.gpr 13))) #v[221, 211]
    (.letOp (n := 224) (.exec 0x110abd (fun s => s.RIP = 0x110abd) (andR64R64Effect 0x110abd 13 15) (Reg.operands [.gpr 13, .gpr 15] [])) #v[221, 211]
    (.letOp (n := 225) (.out 0x110ac0 (orR64R64Effect 0x110ac0 13 5) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 5] []) (.reg (.gpr 13))) #v[223, 219]
    (.letOp (n := 226) (.exec 0x110ac0 (fun s => s.RIP = 0x110ac0) (orR64R64Effect 0x110ac0 13 5) (Reg.operands [.gpr 13, .gpr 5] [])) #v[223, 219]
    (.letOp (n := 227) (.out 0x110ac3 (shrR64Effect 0x110ac3 4 13 63) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[225]
    (.letOp (n := 228) (.exec 0x110ac3 (fun s => s.RIP = 0x110ac3) (shrR64Effect 0x110ac3 4 13 63) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[225]
    (.letOp (n := 229) (.exec 0x110ac7 (StorePre 0x110ac7 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x110ac7 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110ac7 13 (.sib 4 none 0 .none)) (Reg.operands [.gpr 13, .gpr 4] [])) #v[227, 65]
    (.letOp (n := 230) (.out 0x110acb (xorR32R32Effect 0x110acb 3 13 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 13] []) (.reg (.gpr 13))) #v[227, 227]
    (.letOp (n := 231) (.exec 0x110acb (fun s => s.RIP = 0x110acb) (xorR32R32Effect 0x110acb 3 13 13) (Reg.operands [.gpr 13, .gpr 13] [])) #v[227, 227]
    (.letOp (n := 232) (.out 0x110ace (subR64M64Effect 0x110ace 13 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 4] []) (.reg (.gpr 13))) #v[230, 65]
    (.letOp (n := 233) (.exec 0x110ace (LoadPre 0x110ace (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x110ace + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x110ace 13 (.sib 4 none 0 .none)) (Reg.operands [.gpr 13, .gpr 4] [])) #v[230, 65]
    (.letOp (n := 234) (.out 0x110ad2 (movR64R64Effect 0x110ad2 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 235) (.exec 0x110ad2 (fun s => s.RIP = 0x110ad2) (movR64R64Effect 0x110ad2 0 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 236) (.out 0x110ad5 (testR64R64Effect 0x110ad5 12 12) (EffectPart.reads (.flag .ZF) [.gpr 12, .gpr 12] []) (.flag .ZF)) #v[111, 111]
    (.letOp (n := 237) (.exec 0x110ad5 (fun s => s.RIP = 0x110ad5) (testR64R64Effect 0x110ad5 12 12) (Reg.operands [.gpr 12, .gpr 12] [])) #v[111, 111]
    (.letOp (n := 238) (.out 0x110ad8 (atFlags (condHolds 4) (setccR8Effect 0x110ad8 3 1)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 1))) #v[203, 236]
    (.letOp (n := 239) (.exec 0x110ad8 (fun s => s.RIP = 0x110ad8) (atFlags (condHolds 4) (setccR8Effect 0x110ad8 3 1)) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[203, 236]
    (.letOp (n := 240) (.out 0x110adb (andR8R8Effect 0x110adb 3 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 13] []) (.reg (.gpr 1))) #v[238, 232]
    (.letOp (n := 241) (.exec 0x110adb (fun s => s.RIP = 0x110adb) (andR8R8Effect 0x110adb 3 1 13) (Reg.operands [.gpr 1, .gpr 13] [])) #v[238, 232]
    (.letOp (n := 242) (.exec 0x110ade (StorePre 0x110ade 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x110ade + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x110ade 3 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 1, .gpr 4] [])) #v[240, 65]
    (.letOp (n := 243) (.exec 0x110ae1 (fun s => s.RIP = 0x110ae1) (movR64R64Effect 0x110ae1 7 4) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 244) (.out 0x110ae4 (movzxR32M8Effect 0x110ae4 4 7 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[65]
    (.letOp (n := 245) (.exec 0x110ae4 (LoadPre 0x110ae4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x110ae4 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x110ae4 4 7 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 246) (.out 0x110ae8 (decR64Effect 0x110ae8 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[244]
    (.letOp (n := 247) (.exec 0x110ae8 (fun s => s.RIP = 0x110ae8) (decR64Effect 0x110ae8 7) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[244]
    (.letOp (n := 248) (.out 0x110aeb (andR64R64Effect 0x110aeb 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 13] []) (.reg (.gpr 7))) #v[246, 232]
    (.letOp (n := 249) (.exec 0x110aeb (fun s => s.RIP = 0x110aeb) (andR64R64Effect 0x110aeb 7 13) (Reg.operands [.gpr 7, .gpr 13] [])) #v[246, 232]
    (.letOp (n := 250) (.out 0x110aee (sarR64Effect 0x110aee 4 7 63) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[248]
    (.letOp (n := 251) (.exec 0x110aee (fun s => s.RIP = 0x110aee) (sarR64Effect 0x110aee 4 7 63) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[248]
    (b_l1109b0_5)))))))))))))))))))))))))))))))))))))

def bytes_l1109b0_4 : List UInt8 :=
  [0x49, 0xF7, 0xD5, 0x48, 0x89, 0xCD, 0x4C, 0x21, 0xED, 0x49, 0x09, 0xCD, 0x4D, 0x21, 0xFD, 0x49,
    0x09, 0xED, 0x49, 0xC1, 0xED, 0x3F, 0x4C, 0x89, 0x2C, 0x24, 0x45, 0x31, 0xED, 0x4C, 0x2B, 0x2C,
    0x24, 0x48, 0x89, 0xF8, 0x4D, 0x85, 0xE4, 0x0F, 0x94, 0xC1, 0x44, 0x20, 0xE9, 0x88, 0x0C, 0x24,
    0x48, 0x89, 0xE7, 0x0F, 0xB6, 0x3C, 0x24, 0x48, 0xFF, 0xCF, 0x4C, 0x21, 0xEF, 0x48, 0xC1, 0xFF,
    0x3F] ++ bytes_l1109b0_5

theorem code_l1109b0_4 : ∀ x ∈ codeRange 0x110ab1 bytes_l1109b0_4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x10ab1 65 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1109b0_5

@[cfg_block] def b_l1109b0_3 : Block Op Label signature Reg.count 176 :=
  .letOp (n := 176) (.out 0x110a6f (subR64R64Effect 0x110a6f 13 5) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 5] []) (.reg (.gpr 13))) #v[174, 172]
    (.letOp (n := 177) (.exec 0x110a6f (fun s => s.RIP = 0x110a6f) (subR64R64Effect 0x110a6f 13 5) (Reg.operands [.gpr 13, .gpr 5] [])) #v[174, 172]
    (.letOp (n := 178) (.out 0x110a72 (sarR64Effect 0x110a72 4 14 63) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[170]
    (.letOp (n := 179) (.exec 0x110a72 (fun s => s.RIP = 0x110a72) (sarR64Effect 0x110a72 4 14 63) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[170]
    (.letOp (n := 180) (.out 0x110a76 (addR64R64Effect 0x110a76 14 13) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 13] []) (.reg (.gpr 14))) #v[178, 176]
    (.letOp (n := 181) (.exec 0x110a76 (fun s => s.RIP = 0x110a76) (addR64R64Effect 0x110a76 14 13) (Reg.operands [.gpr 14, .gpr 13] [])) #v[178, 176]
    (.letOp (n := 182) (.out 0x110a79 (movR64R64Effect 0x110a79 13 9) (EffectPart.reads (.reg (.gpr 13)) [.gpr 9] []) (.reg (.gpr 13))) #v[102]
    (.letOp (n := 183) (.exec 0x110a79 (fun s => s.RIP = 0x110a79) (movR64R64Effect 0x110a79 13 9) (Reg.operands [.gpr 9] [])) #v[102]
    (.letOp (n := 184) (.out 0x110a7c (notR64Effect 0x110a7c 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[182]
    (.letOp (n := 185) (.exec 0x110a7c (fun s => s.RIP = 0x110a7c) (notR64Effect 0x110a7c 13) (Reg.operands [.gpr 13] [])) #v[182]
    (.letOp (n := 186) (.out 0x110a7f (movR64R64Effect 0x110a7f 15 5) (EffectPart.reads (.reg (.gpr 15)) [.gpr 5] []) (.reg (.gpr 15))) #v[172]
    (.letOp (n := 187) (.exec 0x110a7f (fun s => s.RIP = 0x110a7f) (movR64R64Effect 0x110a7f 15 5) (Reg.operands [.gpr 5] [])) #v[172]
    (.letOp (n := 188) (.out 0x110a82 (andR64R64Effect 0x110a82 15 13) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 13] []) (.reg (.gpr 15))) #v[186, 184]
    (.letOp (n := 189) (.exec 0x110a82 (fun s => s.RIP = 0x110a82) (andR64R64Effect 0x110a82 15 13) (Reg.operands [.gpr 15, .gpr 13] [])) #v[186, 184]
    (.letOp (n := 190) (.out 0x110a85 (orR64R64Effect 0x110a85 13 5) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 5] []) (.reg (.gpr 13))) #v[184, 172]
    (.letOp (n := 191) (.exec 0x110a85 (fun s => s.RIP = 0x110a85) (orR64R64Effect 0x110a85 13 5) (Reg.operands [.gpr 13, .gpr 5] [])) #v[184, 172]
    (.letOp (n := 192) (.out 0x110a88 (andR64R64Effect 0x110a88 13 14) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 14] []) (.reg (.gpr 13))) #v[190, 180]
    (.letOp (n := 193) (.exec 0x110a88 (fun s => s.RIP = 0x110a88) (andR64R64Effect 0x110a88 13 14) (Reg.operands [.gpr 13, .gpr 14] [])) #v[190, 180]
    (.letOp (n := 194) (.out 0x110a8b (orR64R64Effect 0x110a8b 13 15) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 15] []) (.reg (.gpr 13))) #v[192, 188]
    (.letOp (n := 195) (.exec 0x110a8b (fun s => s.RIP = 0x110a8b) (orR64R64Effect 0x110a8b 13 15) (Reg.operands [.gpr 13, .gpr 15] [])) #v[192, 188]
    (.letOp (n := 196) (.out 0x110a8e (shrR64Effect 0x110a8e 4 13 63) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[194]
    (.letOp (n := 197) (.exec 0x110a8e (fun s => s.RIP = 0x110a8e) (shrR64Effect 0x110a8e 4 13 63) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[194]
    (.letOp (n := 198) (.exec 0x110a92 (StorePre 0x110a92 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x110a92 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110a92 13 (.sib 4 none 0 .none)) (Reg.operands [.gpr 13, .gpr 4] [])) #v[196, 65]
    (.letOp (n := 199) (.out 0x110a96 (xorR32R32Effect 0x110a96 3 15 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 15] []) (.reg (.gpr 15))) #v[188, 188]
    (.letOp (n := 200) (.exec 0x110a96 (fun s => s.RIP = 0x110a96) (xorR32R32Effect 0x110a96 3 15 15) (Reg.operands [.gpr 15, .gpr 15] [])) #v[188, 188]
    (.letOp (n := 201) (.out 0x110a99 (subR64M64Effect 0x110a99 15 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 4] []) (.reg (.gpr 15))) #v[199, 65]
    (.letOp (n := 202) (.exec 0x110a99 (LoadPre 0x110a99 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x110a99 + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x110a99 15 (.sib 4 none 0 .none)) (Reg.operands [.gpr 15, .gpr 4] [])) #v[199, 65]
    (.letOp (n := 203) (.out 0x110a9d (movR64M64Effect 0x110a9d 1 (.base 1 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1]
    (.letOp (n := 204) (.exec 0x110a9d (LoadPre 0x110a9d (fun s => AddrMode.addr (.base 1 (.d8 0x18)) s (0x110a9d + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x110a9d 1 (.base 1 (.d8 0x18))) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 205) (.out 0x110aa1 (movR64R64Effect 0x110aa1 13 8) (EffectPart.reads (.reg (.gpr 13)) [.gpr 8] []) (.reg (.gpr 13))) #v[105]
    (.letOp (n := 206) (.exec 0x110aa1 (fun s => s.RIP = 0x110aa1) (movR64R64Effect 0x110aa1 13 8) (Reg.operands [.gpr 8] [])) #v[105]
    (.letOp (n := 207) (.out 0x110aa4 (subR64R64Effect 0x110aa4 13 1) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 1] []) (.reg (.gpr 13))) #v[205, 203]
    (.letOp (n := 208) (.exec 0x110aa4 (fun s => s.RIP = 0x110aa4) (subR64R64Effect 0x110aa4 13 1) (Reg.operands [.gpr 13, .gpr 1] [])) #v[205, 203]
    (.letOp (n := 209) (.out 0x110aa7 (sarR64Effect 0x110aa7 4 15 63) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[201]
    (.letOp (n := 210) (.exec 0x110aa7 (fun s => s.RIP = 0x110aa7) (sarR64Effect 0x110aa7 4 15 63) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[201]
    (.letOp (n := 211) (.out 0x110aab (addR64R64Effect 0x110aab 15 13) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 13] []) (.reg (.gpr 15))) #v[209, 207]
    (.letOp (n := 212) (.exec 0x110aab (fun s => s.RIP = 0x110aab) (addR64R64Effect 0x110aab 15 13) (Reg.operands [.gpr 15, .gpr 13] [])) #v[209, 207]
    (.letOp (n := 213) (.out 0x110aae (movR64R64Effect 0x110aae 13 8) (EffectPart.reads (.reg (.gpr 13)) [.gpr 8] []) (.reg (.gpr 13))) #v[105]
    (.letOp (n := 214) (.exec 0x110aae (fun s => s.RIP = 0x110aae) (movR64R64Effect 0x110aae 13 8) (Reg.operands [.gpr 8] [])) #v[105]
    (b_l1109b0_4)))))))))))))))))))))))))))))))))))))))

def bytes_l1109b0_3 : List UInt8 :=
  [0x49, 0x29, 0xED, 0x49, 0xC1, 0xFE, 0x3F, 0x4D, 0x01, 0xEE, 0x4D, 0x89, 0xCD, 0x49, 0xF7, 0xD5,
    0x49, 0x89, 0xEF, 0x4D, 0x21, 0xEF, 0x49, 0x09, 0xED, 0x4D, 0x21, 0xF5, 0x4D, 0x09, 0xFD, 0x49,
    0xC1, 0xED, 0x3F, 0x4C, 0x89, 0x2C, 0x24, 0x45, 0x31, 0xFF, 0x4C, 0x2B, 0x3C, 0x24, 0x48, 0x8B,
    0x49, 0x18, 0x4D, 0x89, 0xC5, 0x49, 0x29, 0xCD, 0x49, 0xC1, 0xFF, 0x3F, 0x4D, 0x01, 0xEF, 0x4D,
    0x89, 0xC5] ++ bytes_l1109b0_4

theorem code_l1109b0_3 : ∀ x ∈ codeRange 0x110a6f bytes_l1109b0_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x10a6f 66 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1109b0_4

@[cfg_block] def b_l1109b0_2 : Block Op Label signature Reg.count 137 :=
  .letOp (n := 137) (.out 0x110a2d (xorR32R32Effect 0x110a2d 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[133, 133]
    (.letOp (n := 138) (.exec 0x110a2d (fun s => s.RIP = 0x110a2d) (xorR32R32Effect 0x110a2d 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[133, 133]
    (.letOp (n := 139) (.out 0x110a2f (subR64M64Effect 0x110a2f 6 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 4] []) (.reg (.gpr 6))) #v[137, 65]
    (.letOp (n := 140) (.exec 0x110a2f (LoadPre 0x110a2f (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x110a2f + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x110a2f 6 (.sib 4 none 0 .none)) (Reg.operands [.gpr 6, .gpr 4] [])) #v[137, 65]
    (.letOp (n := 141) (.out 0x110a33 (movR64M64Effect 0x110a33 14 (.base 1 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 1] []) (.reg (.gpr 14))) #v[1]
    (.letOp (n := 142) (.exec 0x110a33 (LoadPre 0x110a33 (fun s => AddrMode.addr (.base 1 (.d8 0x8)) s (0x110a33 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x110a33 14 (.base 1 (.d8 0x8))) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 143) (.out 0x110a37 (movR64R64Effect 0x110a37 15 10) (EffectPart.reads (.reg (.gpr 15)) [.gpr 10] []) (.reg (.gpr 15))) #v[99]
    (.letOp (n := 144) (.exec 0x110a37 (fun s => s.RIP = 0x110a37) (movR64R64Effect 0x110a37 15 10) (Reg.operands [.gpr 10] [])) #v[99]
    (.letOp (n := 145) (.out 0x110a3a (subR64R64Effect 0x110a3a 15 14) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 14] []) (.reg (.gpr 15))) #v[143, 141]
    (.letOp (n := 146) (.exec 0x110a3a (fun s => s.RIP = 0x110a3a) (subR64R64Effect 0x110a3a 15 14) (Reg.operands [.gpr 15, .gpr 14] [])) #v[143, 141]
    (.letOp (n := 147) (.out 0x110a3d (sarR64Effect 0x110a3d 4 6 63) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[139]
    (.letOp (n := 148) (.exec 0x110a3d (fun s => s.RIP = 0x110a3d) (sarR64Effect 0x110a3d 4 6 63) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[139]
    (.letOp (n := 149) (.out 0x110a41 (addR64R64Effect 0x110a41 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 15] []) (.reg (.gpr 6))) #v[147, 145]
    (.letOp (n := 150) (.exec 0x110a41 (fun s => s.RIP = 0x110a41) (addR64R64Effect 0x110a41 6 15) (Reg.operands [.gpr 6, .gpr 15] [])) #v[147, 145]
    (.letOp (n := 151) (.out 0x110a44 (movR64R64Effect 0x110a44 15 10) (EffectPart.reads (.reg (.gpr 15)) [.gpr 10] []) (.reg (.gpr 15))) #v[99]
    (.letOp (n := 152) (.exec 0x110a44 (fun s => s.RIP = 0x110a44) (movR64R64Effect 0x110a44 15 10) (Reg.operands [.gpr 10] [])) #v[99]
    (.letOp (n := 153) (.out 0x110a47 (notR64Effect 0x110a47 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15] []) (.reg (.gpr 15))) #v[151]
    (.letOp (n := 154) (.exec 0x110a47 (fun s => s.RIP = 0x110a47) (notR64Effect 0x110a47 15) (Reg.operands [.gpr 15] [])) #v[151]
    (.letOp (n := 155) (.out 0x110a4a (movR64R64Effect 0x110a4a 13 14) (EffectPart.reads (.reg (.gpr 13)) [.gpr 14] []) (.reg (.gpr 13))) #v[141]
    (.letOp (n := 156) (.exec 0x110a4a (fun s => s.RIP = 0x110a4a) (movR64R64Effect 0x110a4a 13 14) (Reg.operands [.gpr 14] [])) #v[141]
    (.letOp (n := 157) (.out 0x110a4d (andR64R64Effect 0x110a4d 13 15) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 15] []) (.reg (.gpr 13))) #v[155, 153]
    (.letOp (n := 158) (.exec 0x110a4d (fun s => s.RIP = 0x110a4d) (andR64R64Effect 0x110a4d 13 15) (Reg.operands [.gpr 13, .gpr 15] [])) #v[155, 153]
    (.letOp (n := 159) (.out 0x110a50 (orR64R64Effect 0x110a50 15 14) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 14] []) (.reg (.gpr 15))) #v[153, 141]
    (.letOp (n := 160) (.exec 0x110a50 (fun s => s.RIP = 0x110a50) (orR64R64Effect 0x110a50 15 14) (Reg.operands [.gpr 15, .gpr 14] [])) #v[153, 141]
    (.letOp (n := 161) (.out 0x110a53 (andR64R64Effect 0x110a53 15 6) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 6] []) (.reg (.gpr 15))) #v[159, 149]
    (.letOp (n := 162) (.exec 0x110a53 (fun s => s.RIP = 0x110a53) (andR64R64Effect 0x110a53 15 6) (Reg.operands [.gpr 15, .gpr 6] [])) #v[159, 149]
    (.letOp (n := 163) (.out 0x110a56 (orR64R64Effect 0x110a56 15 13) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 13] []) (.reg (.gpr 15))) #v[161, 157]
    (.letOp (n := 164) (.exec 0x110a56 (fun s => s.RIP = 0x110a56) (orR64R64Effect 0x110a56 15 13) (Reg.operands [.gpr 15, .gpr 13] [])) #v[161, 157]
    (.letOp (n := 165) (.out 0x110a59 (shrR64Effect 0x110a59 4 15 63) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[163]
    (.letOp (n := 166) (.exec 0x110a59 (fun s => s.RIP = 0x110a59) (shrR64Effect 0x110a59 4 15 63) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[163]
    (.letOp (n := 167) (.exec 0x110a5d (StorePre 0x110a5d 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x110a5d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110a5d 15 (.sib 4 none 0 .none)) (Reg.operands [.gpr 15, .gpr 4] [])) #v[165, 65]
    (.letOp (n := 168) (.out 0x110a61 (xorR32R32Effect 0x110a61 3 14 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 14] []) (.reg (.gpr 14))) #v[141, 141]
    (.letOp (n := 169) (.exec 0x110a61 (fun s => s.RIP = 0x110a61) (xorR32R32Effect 0x110a61 3 14 14) (Reg.operands [.gpr 14, .gpr 14] [])) #v[141, 141]
    (.letOp (n := 170) (.out 0x110a64 (subR64M64Effect 0x110a64 14 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 4] []) (.reg (.gpr 14))) #v[168, 65]
    (.letOp (n := 171) (.exec 0x110a64 (LoadPre 0x110a64 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x110a64 + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x110a64 14 (.sib 4 none 0 .none)) (Reg.operands [.gpr 14, .gpr 4] [])) #v[168, 65]
    (.letOp (n := 172) (.out 0x110a68 (movR64M64Effect 0x110a68 5 (.base 1 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 1] []) (.reg (.gpr 5))) #v[1]
    (.letOp (n := 173) (.exec 0x110a68 (LoadPre 0x110a68 (fun s => AddrMode.addr (.base 1 (.d8 0x10)) s (0x110a68 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x110a68 5 (.base 1 (.d8 0x10))) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 174) (.out 0x110a6c (movR64R64Effect 0x110a6c 13 9) (EffectPart.reads (.reg (.gpr 13)) [.gpr 9] []) (.reg (.gpr 13))) #v[102]
    (.letOp (n := 175) (.exec 0x110a6c (fun s => s.RIP = 0x110a6c) (movR64R64Effect 0x110a6c 13 9) (Reg.operands [.gpr 9] [])) #v[102]
    (b_l1109b0_3)))))))))))))))))))))))))))))))))))))))

def bytes_l1109b0_2 : List UInt8 :=
  [0x31, 0xF6, 0x48, 0x2B, 0x34, 0x24, 0x4C, 0x8B, 0x71, 0x08, 0x4D, 0x89, 0xD7, 0x4D, 0x29, 0xF7,
    0x48, 0xC1, 0xFE, 0x3F, 0x4C, 0x01, 0xFE, 0x4D, 0x89, 0xD7, 0x49, 0xF7, 0xD7, 0x4D, 0x89, 0xF5,
    0x4D, 0x21, 0xFD, 0x4D, 0x09, 0xF7, 0x49, 0x21, 0xF7, 0x4D, 0x09, 0xEF, 0x49, 0xC1, 0xEF, 0x3F,
    0x4C, 0x89, 0x3C, 0x24, 0x45, 0x31, 0xF6, 0x4C, 0x2B, 0x34, 0x24, 0x48, 0x8B, 0x69, 0x10, 0x4D,
    0x89, 0xCD] ++ bytes_l1109b0_3

theorem code_l1109b0_2 : ∀ x ∈ codeRange 0x110a2d bytes_l1109b0_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x10a2d 66 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1109b0_3

@[cfg_block] def b_l1109b0_1 : Block Op Label signature Reg.count 97 :=
  .letOp (n := 97) (.out 0x1109eb (atFlags (condHolds 2) (setccR8Effect 0x1109eb 3 3)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[90, 93]
    (.letOp (n := 98) (.exec 0x1109eb (fun s => s.RIP = 0x1109eb) (atFlags (condHolds 2) (setccR8Effect 0x1109eb 3 3)) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[90, 93]
    (.letOp (n := 99) (.out 0x1109ee (addR64M64Effect 0x1109ee 10 (.base 2 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2] []) (.reg (.gpr 10))) #v[76, 2]
    (.letOp (n := 100) (.out 0x1109ee (addR64M64Effect 0x1109ee 10 (.base 2 (.d8 0x8))) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 2] []) (.flag .CF)) #v[76, 2]
    (.letOp (n := 101) (.exec 0x1109ee (LoadPre 0x1109ee (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x1109ee + BitVec.ofNat 64 4)) 8) (addR64M64Effect 0x1109ee 10 (.base 2 (.d8 0x8))) (Reg.operands [.gpr 10, .gpr 2] [])) #v[76, 2]
    (.letOp (n := 102) (.out 0x1109f2 (atFlags StatusFlags.CF (adcR64R64Effect 0x1109f2 9 0)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[83, 95, 100]
    (.letOp (n := 103) (.out 0x1109f2 (atFlags StatusFlags.CF (adcR64R64Effect 0x1109f2 9 0)) (Reg.operands [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[83, 95, 100]
    (.letOp (n := 104) (.exec 0x1109f2 (fun s => s.RIP = 0x1109f2) (atFlags StatusFlags.CF (adcR64R64Effect 0x1109f2 9 0)) (Reg.operands [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[83, 95, 100]
    (.letOp (n := 105) (.out 0x1109f5 (atFlags StatusFlags.CF (adcR64R64Effect 0x1109f5 8 14)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[86, 92, 103]
    (.letOp (n := 106) (.out 0x1109f5 (atFlags StatusFlags.CF (adcR64R64Effect 0x1109f5 8 14)) (Reg.operands [.gpr 8, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[86, 92, 103]
    (.letOp (n := 107) (.exec 0x1109f5 (fun s => s.RIP = 0x1109f5) (atFlags StatusFlags.CF (adcR64R64Effect 0x1109f5 8 14)) (Reg.operands [.gpr 8, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[86, 92, 103]
    (.letOp (n := 108) (.exec 0x1109f8 (StorePre 0x1109f8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x1109f8 + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 2) (setccM8Effect 0x1109f8 5 (.sib 4 none 0 (.d8 0xf)))) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[65, 106]
    (.letOp (n := 109) (.out 0x1109fd (movR64R64Effect 0x1109fd 12 3) (EffectPart.reads (.reg (.gpr 12)) [.gpr 3] []) (.reg (.gpr 12))) #v[97]
    (.letOp (n := 110) (.exec 0x1109fd (fun s => s.RIP = 0x1109fd) (movR64R64Effect 0x1109fd 12 3) (Reg.operands [.gpr 3] [])) #v[97]
    (.letOp (n := 111) (.out 0x110a00 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x110a00 12 0x0)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 12))) #v[109, 106]
    (.letOp (n := 112) (.exec 0x110a00 (fun s => s.RIP = 0x110a00) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x110a00 12 0x0)) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[109, 106]
    (.letOp (n := 113) (.out 0x110a04 (movR64M64Effect 0x110a04 0 (.base 1 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[1]
    (.letOp (n := 114) (.exec 0x110a04 (LoadPre 0x110a04 (fun s => AddrMode.addr (.base 1 .none) s (0x110a04 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x110a04 0 (.base 1 .none)) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 115) (.out 0x110a07 (movR64R64Effect 0x110a07 2 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11] []) (.reg (.gpr 2))) #v[71]
    (.letOp (n := 116) (.exec 0x110a07 (fun s => s.RIP = 0x110a07) (movR64R64Effect 0x110a07 2 11) (Reg.operands [.gpr 11] [])) #v[71]
    (.letOp (n := 117) (.out 0x110a0a (subR64R64Effect 0x110a0a 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[115, 113]
    (.letOp (n := 118) (.exec 0x110a0a (fun s => s.RIP = 0x110a0a) (subR64R64Effect 0x110a0a 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[115, 113]
    (.letOp (n := 119) (.out 0x110a0d (movR64R64Effect 0x110a0d 6 11) (EffectPart.reads (.reg (.gpr 6)) [.gpr 11] []) (.reg (.gpr 6))) #v[71]
    (.letOp (n := 120) (.exec 0x110a0d (fun s => s.RIP = 0x110a0d) (movR64R64Effect 0x110a0d 6 11) (Reg.operands [.gpr 11] [])) #v[71]
    (.letOp (n := 121) (.out 0x110a10 (notR64Effect 0x110a10 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[119]
    (.letOp (n := 122) (.exec 0x110a10 (fun s => s.RIP = 0x110a10) (notR64Effect 0x110a10 6) (Reg.operands [.gpr 6] [])) #v[119]
    (.letOp (n := 123) (.out 0x110a13 (movR64R64Effect 0x110a13 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[113]
    (.letOp (n := 124) (.exec 0x110a13 (fun s => s.RIP = 0x110a13) (movR64R64Effect 0x110a13 14 0) (Reg.operands [.gpr 0] [])) #v[113]
    (.letOp (n := 125) (.out 0x110a16 (andR64R64Effect 0x110a16 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 6] []) (.reg (.gpr 14))) #v[123, 121]
    (.letOp (n := 126) (.exec 0x110a16 (fun s => s.RIP = 0x110a16) (andR64R64Effect 0x110a16 14 6) (Reg.operands [.gpr 14, .gpr 6] [])) #v[123, 121]
    (.letOp (n := 127) (.out 0x110a19 (orR64R64Effect 0x110a19 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[121, 113]
    (.letOp (n := 128) (.exec 0x110a19 (fun s => s.RIP = 0x110a19) (orR64R64Effect 0x110a19 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[121, 113]
    (.letOp (n := 129) (.out 0x110a1c (andR64R64Effect 0x110a1c 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[127, 117]
    (.letOp (n := 130) (.exec 0x110a1c (fun s => s.RIP = 0x110a1c) (andR64R64Effect 0x110a1c 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[127, 117]
    (.letOp (n := 131) (.out 0x110a1f (orR64R64Effect 0x110a1f 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 14] []) (.reg (.gpr 6))) #v[129, 125]
    (.letOp (n := 132) (.exec 0x110a1f (fun s => s.RIP = 0x110a1f) (orR64R64Effect 0x110a1f 6 14) (Reg.operands [.gpr 6, .gpr 14] [])) #v[129, 125]
    (.letOp (n := 133) (.out 0x110a22 (shrR64Effect 0x110a22 4 6 63) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[131]
    (.letOp (n := 134) (.exec 0x110a22 (fun s => s.RIP = 0x110a22) (shrR64Effect 0x110a22 4 6 63) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[131]
    (.letOp (n := 135) (.exec 0x110a26 (StorePre 0x110a26 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x110a26 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110a26 6 (.sib 4 none 0 .none)) (Reg.operands [.gpr 6, .gpr 4] [])) #v[133, 65]
    (.letOp (n := 136) (.exec 0x110a2a (fun s => s.RIP = 0x110a2a) (movR64R64Effect 0x110a2a 0 4) (Reg.operands [.gpr 4] [])) #v[65]
    (b_l1109b0_2))))))))))))))))))))))))))))))))))))))))

def bytes_l1109b0_1 : List UInt8 :=
  [0x0F, 0x92, 0xC3, 0x4C, 0x03, 0x52, 0x08, 0x49, 0x11, 0xC1, 0x4D, 0x11, 0xF0, 0x0F, 0x92, 0x44,
    0x24, 0x0F, 0x49, 0x89, 0xDC, 0x49, 0x83, 0xD4, 0x00, 0x48, 0x8B, 0x01, 0x4C, 0x89, 0xDA, 0x48,
    0x29, 0xC2, 0x4C, 0x89, 0xDE, 0x48, 0xF7, 0xD6, 0x49, 0x89, 0xC6, 0x49, 0x21, 0xF6, 0x48, 0x09,
    0xC6, 0x48, 0x21, 0xD6, 0x4C, 0x09, 0xF6, 0x48, 0xC1, 0xEE, 0x3F, 0x48, 0x89, 0x34, 0x24, 0x48,
    0x89, 0xE0] ++ bytes_l1109b0_2

theorem code_l1109b0_1 : ∀ x ∈ codeRange 0x1109eb bytes_l1109b0_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x109eb 66 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1109b0_2

@[cfg_block] def b_l1109b0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1109b0 (pushR64Effect 0x1109b0 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x1109b0 (PushPre 0x1109b0 1) (pushR64Effect 0x1109b0 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x1109b1 (pushR64Effect 0x1109b1 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x1109b1 (PushPre 0x1109b1 2) (pushR64Effect 0x1109b1 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x1109b3 (pushR64Effect 0x1109b3 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x1109b3 (PushPre 0x1109b3 2) (pushR64Effect 0x1109b3 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x1109b5 (pushR64Effect 0x1109b5 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x1109b5 (PushPre 0x1109b5 2) (pushR64Effect 0x1109b5 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x1109b7 (pushR64Effect 0x1109b7 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x1109b7 (PushPre 0x1109b7 2) (pushR64Effect 0x1109b7 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x1109b9 (pushR64Effect 0x1109b9 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x1109b9 (PushPre 0x1109b9 1) (pushR64Effect 0x1109b9 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x1109ba (subR64Imm8Effect 0x1109ba 4 0x10) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x1109ba (fun s => s.RIP = 0x1109ba) (subR64Imm8Effect 0x1109ba 4 0x10) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x1109be (movR64M64Effect 0x1109be 11 (.base 2 .none)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[2]
    (.letOp (n := 68) (.exec 0x1109be (LoadPre 0x1109be (fun s => AddrMode.addr (.base 2 .none) s (0x1109be + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1109be 11 (.base 2 .none)) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 69) (.out 0x1109c1 (movR64M64Effect 0x1109c1 9 (.base 2 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[2]
    (.letOp (n := 70) (.exec 0x1109c1 (LoadPre 0x1109c1 (fun s => AddrMode.addr (.base 2 (.d8 0x10)) s (0x1109c1 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1109c1 9 (.base 2 (.d8 0x10))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 71) (.out 0x1109c5 (addR64M64Effect 0x1109c5 11 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 6] []) (.reg (.gpr 11))) #v[67, 6]
    (.letOp (n := 72) (.out 0x1109c5 (addR64M64Effect 0x1109c5 11 (.base 6 .none)) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 6] []) (.flag .CF)) #v[67, 6]
    (.letOp (n := 73) (.exec 0x1109c5 (LoadPre 0x1109c5 (fun s => AddrMode.addr (.base 6 .none) s (0x1109c5 + BitVec.ofNat 64 3)) 8) (addR64M64Effect 0x1109c5 11 (.base 6 .none)) (Reg.operands [.gpr 11, .gpr 6] [])) #v[67, 6]
    (.letOp (n := 74) (.out 0x1109c8 (movR64M64Effect 0x1109c8 10 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 6] []) (.reg (.gpr 10))) #v[6]
    (.letOp (n := 75) (.exec 0x1109c8 (LoadPre 0x1109c8 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x1109c8 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1109c8 10 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 76) (.out 0x1109cc (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1109cc 10 0x0)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[74, 72]
    (.letOp (n := 77) (.out 0x1109cc (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1109cc 10 0x0)) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[74, 72]
    (.letOp (n := 78) (.exec 0x1109cc (fun s => s.RIP = 0x1109cc) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1109cc 10 0x0)) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[74, 72]
    (.letOp (n := 79) (.out 0x1109d0 (atFlags (condHolds 2) (setccR8Effect 0x1109d0 3 0)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 0))) #v[0, 77]
    (.letOp (n := 80) (.exec 0x1109d0 (fun s => s.RIP = 0x1109d0) (atFlags (condHolds 2) (setccR8Effect 0x1109d0 3 0)) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[0, 77]
    (.letOp (n := 81) (.out 0x1109d3 (xorR32R32Effect 0x1109d3 3 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 8] []) (.reg (.gpr 8))) #v[8, 8]
    (.letOp (n := 82) (.exec 0x1109d3 (fun s => s.RIP = 0x1109d3) (xorR32R32Effect 0x1109d3 3 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[8, 8]
    (.letOp (n := 83) (.out 0x1109d6 (addR64M64Effect 0x1109d6 9 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 6] []) (.reg (.gpr 9))) #v[69, 6]
    (.letOp (n := 84) (.out 0x1109d6 (addR64M64Effect 0x1109d6 9 (.base 6 (.d8 0x10))) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 6] []) (.flag .CF)) #v[69, 6]
    (.letOp (n := 85) (.exec 0x1109d6 (LoadPre 0x1109d6 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x1109d6 + BitVec.ofNat 64 4)) 8) (addR64M64Effect 0x1109d6 9 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 9, .gpr 6] [])) #v[69, 6]
    (.letOp (n := 86) (.out 0x1109da (atFlags (condHolds 2) (setccR8Effect 0x1109da 4 8)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[81, 84]
    (.letOp (n := 87) (.exec 0x1109da (fun s => s.RIP = 0x1109da) (atFlags (condHolds 2) (setccR8Effect 0x1109da 4 8)) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[81, 84]
    (.letOp (n := 88) (.out 0x1109de (movR64M64Effect 0x1109de 14 (.base 2 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[2]
    (.letOp (n := 89) (.exec 0x1109de (LoadPre 0x1109de (fun s => AddrMode.addr (.base 2 (.d8 0x18)) s (0x1109de + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1109de 14 (.base 2 (.d8 0x18))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 90) (.out 0x1109e2 (xorR32R32Effect 0x1109e2 2 3 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 3] []) (.reg (.gpr 3))) #v[3, 3]
    (.letOp (n := 91) (.exec 0x1109e2 (fun s => s.RIP = 0x1109e2) (xorR32R32Effect 0x1109e2 2 3 3) (Reg.operands [.gpr 3, .gpr 3] [])) #v[3, 3]
    (.letOp (n := 92) (.out 0x1109e4 (addR64M64Effect 0x1109e4 14 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 6] []) (.reg (.gpr 14))) #v[88, 6]
    (.letOp (n := 93) (.out 0x1109e4 (addR64M64Effect 0x1109e4 14 (.base 6 (.d8 0x18))) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 6] []) (.flag .CF)) #v[88, 6]
    (.letOp (n := 94) (.exec 0x1109e4 (LoadPre 0x1109e4 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x1109e4 + BitVec.ofNat 64 4)) 8) (addR64M64Effect 0x1109e4 14 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 14, .gpr 6] [])) #v[88, 6]
    (.letOp (n := 95) (.out 0x1109e8 (movzxR32R8Effect 0x1109e8 3 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[79]
    (.letOp (n := 96) (.exec 0x1109e8 (fun s => s.RIP = 0x1109e8) (movzxR32R8Effect 0x1109e8 3 0 0) (Reg.operands [.gpr 0] [])) #v[79]
    (b_l1109b0_1))))))))))))))))))))))))))))))))))))))))))))

def bytes_l1109b0 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x83, 0xEC, 0x10, 0x4C, 0x8B,
    0x1A, 0x4C, 0x8B, 0x4A, 0x10, 0x4C, 0x03, 0x1E, 0x4C, 0x8B, 0x56, 0x08, 0x49, 0x83, 0xD2, 0x00,
    0x0F, 0x92, 0xC0, 0x45, 0x31, 0xC0, 0x4C, 0x03, 0x4E, 0x10, 0x41, 0x0F, 0x92, 0xC0, 0x4C, 0x8B,
    0x72, 0x18, 0x31, 0xDB, 0x4C, 0x03, 0x76, 0x18, 0x0F, 0xB6, 0xC0] ++ bytes_l1109b0_1

theorem code_l1109b0 : ∀ x ∈ codeRange 0x1109b0 bytes_l1109b0, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x109b0 59 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1109b0_1

@[cfg_block] def b_l110b80_4 : Block Op Label signature Reg.count 204 :=
  .letOp (n := 204) (.out 0x110c99 (decR64Effect 0x110c99 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[192]
    (.letOp (n := 205) (.exec 0x110c99 (fun s => s.RIP = 0x110c99) (decR64Effect 0x110c99 10) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[192]
    (.letOp (n := 206) (.out 0x110c9c (andR64R64Effect 0x110c9c 10 8) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 8] []) (.reg (.gpr 10))) #v[204, 107]
    (.letOp (n := 207) (.exec 0x110c9c (fun s => s.RIP = 0x110c9c) (andR64R64Effect 0x110c9c 10 8) (Reg.operands [.gpr 10, .gpr 8] [])) #v[204, 107]
    (.letOp (n := 208) (.out 0x110c9f (decR64Effect 0x110c9f 11) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[195]
    (.letOp (n := 209) (.exec 0x110c9f (fun s => s.RIP = 0x110c9f) (decR64Effect 0x110c9f 11) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[195]
    (.letOp (n := 210) (.out 0x110ca2 (andR64R64Effect 0x110ca2 11 3) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 3] []) (.reg (.gpr 11))) #v[208, 136]
    (.letOp (n := 211) (.exec 0x110ca2 (fun s => s.RIP = 0x110ca2) (andR64R64Effect 0x110ca2 11 3) (Reg.operands [.gpr 11, .gpr 3] [])) #v[208, 136]
    (.letOp (n := 212) (.out 0x110ca5 (movzxR32M8Effect 0x110ca5 5 1 (.sib 4 none 0 (.d8 0x7))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[61]
    (.letOp (n := 213) (.exec 0x110ca5 (LoadPre 0x110ca5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x110ca5 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x110ca5 5 1 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 214) (.out 0x110caa (decR64Effect 0x110caa 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[212]
    (.letOp (n := 215) (.exec 0x110caa (fun s => s.RIP = 0x110caa) (decR64Effect 0x110caa 1) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[212]
    (.letOp (n := 216) (.out 0x110cad (andR64R64Effect 0x110cad 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[214, 163]
    (.letOp (n := 217) (.exec 0x110cad (fun s => s.RIP = 0x110cad) (andR64R64Effect 0x110cad 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[214, 163]
    (.letOp (n := 218) (.exec 0x110cb0 (StorePre 0x110cb0 3 (fun s => AddrMode.addr (.base 7 .none) s (0x110cb0 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x110cb0 2 (.base 7 .none)) (Reg.operands [.gpr 2, .gpr 7] [])) #v[202, 7]
    (.letOp (n := 219) (.exec 0x110cb3 (StorePre 0x110cb3 4 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x110cb3 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110cb3 10 (.base 7 (.d8 0x8))) (Reg.operands [.gpr 10, .gpr 7] [])) #v[206, 7]
    (.letOp (n := 220) (.exec 0x110cb7 (StorePre 0x110cb7 4 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x110cb7 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110cb7 11 (.base 7 (.d8 0x10))) (Reg.operands [.gpr 11, .gpr 7] [])) #v[210, 7]
    (.letOp (n := 221) (.exec 0x110cbb (StorePre 0x110cbb 4 (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x110cbb + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110cbb 1 (.base 7 (.d8 0x18))) (Reg.operands [.gpr 1, .gpr 7] [])) #v[216, 7]
    (.letOp (n := 222) (.out 0x110cbf (addR64Imm8Effect 0x110cbf 4 0x10) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 223) (.exec 0x110cbf (fun s => s.RIP = 0x110cbf) (addR64Imm8Effect 0x110cbf 4 0x10) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 224) (.out 0x110cc3 (popR64Effect 0x110cc3 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[222]
    (.letOp (n := 225) (.out 0x110cc3 (popR64Effect 0x110cc3 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[222]
    (.letOp (n := 226) (.exec 0x110cc3 (PopPre 0x110cc3) (popR64Effect 0x110cc3 1 3) (Reg.operands [.gpr 4] [])) #v[222]
    (.letOp (n := 227) (.out 0x110cc4 (popR64Effect 0x110cc4 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[225]
    (.letOp (n := 228) (.out 0x110cc4 (popR64Effect 0x110cc4 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[225]
    (.letOp (n := 229) (.exec 0x110cc4 (PopPre 0x110cc4) (popR64Effect 0x110cc4 2 12) (Reg.operands [.gpr 4] [])) #v[225]
    (.letOp (n := 230) (.out 0x110cc6 (popR64Effect 0x110cc6 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[228]
    (.letOp (n := 231) (.out 0x110cc6 (popR64Effect 0x110cc6 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[228]
    (.letOp (n := 232) (.exec 0x110cc6 (PopPre 0x110cc6) (popR64Effect 0x110cc6 2 14) (Reg.operands [.gpr 4] [])) #v[228]
    (.letOp (n := 233) (.out 0x110cc8 (popR64Effect 0x110cc8 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[231]
    (.letOp (n := 234) (.out 0x110cc8 (popR64Effect 0x110cc8 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[231]
    (.letOp (n := 235) (.exec 0x110cc8 (PopPre 0x110cc8) (popR64Effect 0x110cc8 2 15) (Reg.operands [.gpr 4] [])) #v[231]
    (.letOp (n := 236) (.out 0x110cca (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[234]
    (.letOp (n := 237) (.out 0x110cca (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[234]
    (.letOp (n := 238) (.exec 0x110cca (RetPre 0x110cca) (retEffect) (Reg.operands [.gpr 4] [])) #v[234]
    (.terminate (.ret (RegMap.args [(0, 198), (1, 216), (2, 202), (3, 224), (4, 237), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 206), (11, 210), (12, 227), (13, 13), (14, 230), (15, 233), (22, 22), (39, 39), (50, 50), (51, 51)] 239) (some ⟨236, by decide⟩)))))))))))))))))))))))))))))))))))))

def bytes_l110b80_4 : List UInt8 :=
  [0x49, 0xFF, 0xCA, 0x4D, 0x21, 0xC2, 0x49, 0xFF, 0xCB, 0x49, 0x21, 0xDB, 0x0F, 0xB6, 0x4C, 0x24,
    0x07, 0x48, 0xFF, 0xC9, 0x48, 0x21, 0xF1, 0x48, 0x89, 0x17, 0x4C, 0x89, 0x57, 0x08, 0x4C, 0x89,
    0x5F, 0x10, 0x48, 0x89, 0x4F, 0x18, 0x48, 0x83, 0xC4, 0x10, 0x5B, 0x41, 0x5C, 0x41, 0x5E, 0x41,
    0x5F, 0xC3]

theorem code_l110b80_4 : ∀ x ∈ codeRange 0x110c99 bytes_l110b80_4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x10c99 50 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l110b80_3 : Block Op Label signature Reg.count 169 :=
  .letOp (n := 169) (.out 0x110c48 (andR64R64Effect 0x110c48 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 2] []) (.reg (.gpr 15))) #v[167, 165]
    (.letOp (n := 170) (.exec 0x110c48 (fun s => s.RIP = 0x110c48) (andR64R64Effect 0x110c48 15 2) (Reg.operands [.gpr 15, .gpr 2] [])) #v[167, 165]
    (.letOp (n := 171) (.out 0x110c4b (orR64R64Effect 0x110c4b 2 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 9] []) (.reg (.gpr 2))) #v[165, 69]
    (.letOp (n := 172) (.exec 0x110c4b (fun s => s.RIP = 0x110c4b) (orR64R64Effect 0x110c4b 2 9) (Reg.operands [.gpr 2, .gpr 9] [])) #v[165, 69]
    (.letOp (n := 173) (.out 0x110c4e (andR64R64Effect 0x110c4e 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[171, 163]
    (.letOp (n := 174) (.exec 0x110c4e (fun s => s.RIP = 0x110c4e) (andR64R64Effect 0x110c4e 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[171, 163]
    (.letOp (n := 175) (.out 0x110c51 (orR64R64Effect 0x110c51 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 15] []) (.reg (.gpr 2))) #v[173, 169]
    (.letOp (n := 176) (.exec 0x110c51 (fun s => s.RIP = 0x110c51) (orR64R64Effect 0x110c51 2 15) (Reg.operands [.gpr 2, .gpr 15] [])) #v[173, 169]
    (.letOp (n := 177) (.out 0x110c54 (shrR64Effect 0x110c54 4 2 63) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[175]
    (.letOp (n := 178) (.exec 0x110c54 (fun s => s.RIP = 0x110c54) (shrR64Effect 0x110c54 4 2 63) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[175]
    (.letOp (n := 179) (.exec 0x110c58 (StorePre 0x110c58 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x110c58 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110c58 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[177, 61]
    (.letOp (n := 180) (.out 0x110c5d (orR64R64Effect 0x110c5d 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[65, 63]
    (.letOp (n := 181) (.exec 0x110c5d (fun s => s.RIP = 0x110c5d) (orR64R64Effect 0x110c5d 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[65, 63]
    (.letOp (n := 182) (.out 0x110c60 (orR64R64Effect 0x110c60 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[180, 67]
    (.letOp (n := 183) (.exec 0x110c60 (fun s => s.RIP = 0x110c60) (orR64R64Effect 0x110c60 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[180, 67]
    (.letOp (n := 184) (.out 0x110c63 (orR64R64Effect 0x110c63 0 9) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 9] []) (.flag .ZF)) #v[182, 69]
    (.letOp (n := 185) (.exec 0x110c63 (fun s => s.RIP = 0x110c63) (orR64R64Effect 0x110c63 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[182, 69]
    (.letOp (n := 186) (.exec 0x110c66 (StorePre 0x110c66 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x110c66 + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 4) (setccM8Effect 0x110c66 5 (.sib 4 none 0 (.d8 0x7)))) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.ZF])) #v[61, 184]
    (.letOp (n := 187) (.out 0x110c6b (leaR64Effect 0x110c6b 9 (.sib 4 none 0 (.d8 0x7))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[61]
    (.letOp (n := 188) (.exec 0x110c6b (fun s => s.RIP = 0x110c6b) (leaR64Effect 0x110c6b 9 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 189) (.out 0x110c70 (movzxR32M8Effect 0x110c70 5 2 (.sib 4 none 0 (.d8 0x7))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[61]
    (.letOp (n := 190) (.exec 0x110c70 (LoadPre 0x110c70 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x110c70 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x110c70 5 2 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 191) (.exec 0x110c75 (StorePre 0x110c75 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x110c75 + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 4) (setccM8Effect 0x110c75 5 (.sib 4 none 0 (.d8 0x7)))) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.ZF])) #v[61, 184]
    (.letOp (n := 192) (.out 0x110c7a (movzxR32M8Effect 0x110c7a 6 10 (.sib 4 none 0 (.d8 0x7))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[61]
    (.letOp (n := 193) (.exec 0x110c7a (LoadPre 0x110c7a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x110c7a + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x110c7a 6 10 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 194) (.exec 0x110c80 (StorePre 0x110c80 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x110c80 + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 4) (setccM8Effect 0x110c80 5 (.sib 4 none 0 (.d8 0x7)))) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.ZF])) #v[61, 184]
    (.letOp (n := 195) (.out 0x110c85 (movzxR32M8Effect 0x110c85 6 11 (.sib 4 none 0 (.d8 0x7))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[61]
    (.letOp (n := 196) (.exec 0x110c85 (LoadPre 0x110c85 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x110c85 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x110c85 6 11 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 197) (.exec 0x110c8b (StorePre 0x110c8b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x110c8b + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 4) (setccM8Effect 0x110c8b 5 (.sib 4 none 0 (.d8 0x7)))) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.ZF])) #v[61, 184]
    (.letOp (n := 198) (.out 0x110c90 (movR64R64Effect 0x110c90 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 199) (.exec 0x110c90 (fun s => s.RIP = 0x110c90) (movR64R64Effect 0x110c90 0 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 200) (.out 0x110c93 (decR64Effect 0x110c93 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[189]
    (.letOp (n := 201) (.exec 0x110c93 (fun s => s.RIP = 0x110c93) (decR64Effect 0x110c93 2) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[189]
    (.letOp (n := 202) (.out 0x110c96 (andR64R64Effect 0x110c96 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[200, 75]
    (.letOp (n := 203) (.exec 0x110c96 (fun s => s.RIP = 0x110c96) (andR64R64Effect 0x110c96 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[200, 75]
    (b_l110b80_4)))))))))))))))))))))))))))))))))))

def bytes_l110b80_3 : List UInt8 :=
  [0x49, 0x21, 0xD7, 0x4C, 0x09, 0xCA, 0x48, 0x21, 0xF2, 0x4C, 0x09, 0xFA, 0x48, 0xC1, 0xEA, 0x3F,
    0x48, 0x89, 0x54, 0x24, 0x08, 0x4C, 0x09, 0xD0, 0x4C, 0x09, 0xD8, 0x4C, 0x09, 0xC8, 0x0F, 0x94,
    0x44, 0x24, 0x07, 0x4C, 0x8D, 0x4C, 0x24, 0x07, 0x0F, 0xB6, 0x54, 0x24, 0x07, 0x0F, 0x94, 0x44,
    0x24, 0x07, 0x44, 0x0F, 0xB6, 0x54, 0x24, 0x07, 0x0F, 0x94, 0x44, 0x24, 0x07, 0x44, 0x0F, 0xB6,
    0x5C, 0x24, 0x07, 0x0F, 0x94, 0x44, 0x24, 0x07, 0x48, 0x89, 0xF8, 0x48, 0xFF, 0xCA, 0x48, 0x21,
    0xCA] ++ bytes_l110b80_4

theorem code_l110b80_3 : ∀ x ∈ codeRange 0x110c48 bytes_l110b80_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x10c48 81 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110b80_4

@[cfg_block] def b_l110b80_2 : Block Op Label signature Reg.count 130 :=
  .letOp (n := 130) (.out 0x110c04 (movR64R64Effect 0x110c04 12 15) (EffectPart.reads (.reg (.gpr 12)) [.gpr 15] []) (.reg (.gpr 12))) #v[128]
    (.letOp (n := 131) (.exec 0x110c04 (fun s => s.RIP = 0x110c04) (movR64R64Effect 0x110c04 12 15) (Reg.operands [.gpr 15] [])) #v[128]
    (.letOp (n := 132) (.out 0x110c07 (subR64R64Effect 0x110c07 12 11) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 11] []) (.reg (.gpr 12))) #v[130, 67]
    (.letOp (n := 133) (.exec 0x110c07 (fun s => s.RIP = 0x110c07) (subR64R64Effect 0x110c07 12 11) (Reg.operands [.gpr 12, .gpr 11] [])) #v[130, 67]
    (.letOp (n := 134) (.out 0x110c0a (sarR64Effect 0x110c0a 4 3 63) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[126]
    (.letOp (n := 135) (.exec 0x110c0a (fun s => s.RIP = 0x110c0a) (sarR64Effect 0x110c0a 4 3 63) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[126]
    (.letOp (n := 136) (.out 0x110c0e (addR64R64Effect 0x110c0e 3 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 12] []) (.reg (.gpr 3))) #v[134, 132]
    (.letOp (n := 137) (.exec 0x110c0e (fun s => s.RIP = 0x110c0e) (addR64R64Effect 0x110c0e 3 12) (Reg.operands [.gpr 3, .gpr 12] [])) #v[134, 132]
    (.letOp (n := 138) (.out 0x110c11 (notR64Effect 0x110c11 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15] []) (.reg (.gpr 15))) #v[128]
    (.letOp (n := 139) (.exec 0x110c11 (fun s => s.RIP = 0x110c11) (notR64Effect 0x110c11 15) (Reg.operands [.gpr 15] [])) #v[128]
    (.letOp (n := 140) (.out 0x110c14 (movR64R64Effect 0x110c14 12 11) (EffectPart.reads (.reg (.gpr 12)) [.gpr 11] []) (.reg (.gpr 12))) #v[67]
    (.letOp (n := 141) (.exec 0x110c14 (fun s => s.RIP = 0x110c14) (movR64R64Effect 0x110c14 12 11) (Reg.operands [.gpr 11] [])) #v[67]
    (.letOp (n := 142) (.out 0x110c17 (andR64R64Effect 0x110c17 12 15) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 15] []) (.reg (.gpr 12))) #v[140, 138]
    (.letOp (n := 143) (.exec 0x110c17 (fun s => s.RIP = 0x110c17) (andR64R64Effect 0x110c17 12 15) (Reg.operands [.gpr 12, .gpr 15] [])) #v[140, 138]
    (.letOp (n := 144) (.out 0x110c1a (orR64R64Effect 0x110c1a 15 11) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 11] []) (.reg (.gpr 15))) #v[138, 67]
    (.letOp (n := 145) (.exec 0x110c1a (fun s => s.RIP = 0x110c1a) (orR64R64Effect 0x110c1a 15 11) (Reg.operands [.gpr 15, .gpr 11] [])) #v[138, 67]
    (.letOp (n := 146) (.out 0x110c1d (andR64R64Effect 0x110c1d 15 3) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 3] []) (.reg (.gpr 15))) #v[144, 136]
    (.letOp (n := 147) (.exec 0x110c1d (fun s => s.RIP = 0x110c1d) (andR64R64Effect 0x110c1d 15 3) (Reg.operands [.gpr 15, .gpr 3] [])) #v[144, 136]
    (.letOp (n := 148) (.out 0x110c20 (orR64R64Effect 0x110c20 15 12) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 12] []) (.reg (.gpr 15))) #v[146, 142]
    (.letOp (n := 149) (.exec 0x110c20 (fun s => s.RIP = 0x110c20) (orR64R64Effect 0x110c20 15 12) (Reg.operands [.gpr 15, .gpr 12] [])) #v[146, 142]
    (.letOp (n := 150) (.out 0x110c23 (shrR64Effect 0x110c23 4 15 63) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[148]
    (.letOp (n := 151) (.exec 0x110c23 (fun s => s.RIP = 0x110c23) (shrR64Effect 0x110c23 4 15 63) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[148]
    (.letOp (n := 152) (.exec 0x110c27 (StorePre 0x110c27 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x110c27 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110c27 15 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[150, 61]
    (.letOp (n := 153) (.out 0x110c2c (subR64M64Effect 0x110c2c 6 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 4] []) (.reg (.gpr 6))) #v[93, 61]
    (.letOp (n := 154) (.exec 0x110c2c (LoadPre 0x110c2c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x110c2c + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x110c2c 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[93, 61]
    (.letOp (n := 155) (.out 0x110c31 (movR64M64Effect 0x110c31 2 (.base 2 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[2]
    (.letOp (n := 156) (.exec 0x110c31 (LoadPre 0x110c31 (fun s => AddrMode.addr (.base 2 (.d8 0x18)) s (0x110c31 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x110c31 2 (.base 2 (.d8 0x18))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 157) (.out 0x110c35 (movR64R64Effect 0x110c35 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[155]
    (.letOp (n := 158) (.exec 0x110c35 (fun s => s.RIP = 0x110c35) (movR64R64Effect 0x110c35 15 2) (Reg.operands [.gpr 2] [])) #v[155]
    (.letOp (n := 159) (.out 0x110c38 (subR64R64Effect 0x110c38 15 9) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 9] []) (.reg (.gpr 15))) #v[157, 69]
    (.letOp (n := 160) (.exec 0x110c38 (fun s => s.RIP = 0x110c38) (subR64R64Effect 0x110c38 15 9) (Reg.operands [.gpr 15, .gpr 9] [])) #v[157, 69]
    (.letOp (n := 161) (.out 0x110c3b (sarR64Effect 0x110c3b 4 6 63) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[153]
    (.letOp (n := 162) (.exec 0x110c3b (fun s => s.RIP = 0x110c3b) (sarR64Effect 0x110c3b 4 6 63) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[153]
    (.letOp (n := 163) (.out 0x110c3f (addR64R64Effect 0x110c3f 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 15] []) (.reg (.gpr 6))) #v[161, 159]
    (.letOp (n := 164) (.exec 0x110c3f (fun s => s.RIP = 0x110c3f) (addR64R64Effect 0x110c3f 6 15) (Reg.operands [.gpr 6, .gpr 15] [])) #v[161, 159]
    (.letOp (n := 165) (.out 0x110c42 (notR64Effect 0x110c42 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[155]
    (.letOp (n := 166) (.exec 0x110c42 (fun s => s.RIP = 0x110c42) (notR64Effect 0x110c42 2) (Reg.operands [.gpr 2] [])) #v[155]
    (.letOp (n := 167) (.out 0x110c45 (movR64R64Effect 0x110c45 15 9) (EffectPart.reads (.reg (.gpr 15)) [.gpr 9] []) (.reg (.gpr 15))) #v[69]
    (.letOp (n := 168) (.exec 0x110c45 (fun s => s.RIP = 0x110c45) (movR64R64Effect 0x110c45 15 9) (Reg.operands [.gpr 9] [])) #v[69]
    (b_l110b80_3)))))))))))))))))))))))))))))))))))))))

def bytes_l110b80_2 : List UInt8 :=
  [0x4D, 0x89, 0xFC, 0x4D, 0x29, 0xDC, 0x48, 0xC1, 0xFB, 0x3F, 0x4C, 0x01, 0xE3, 0x49, 0xF7, 0xD7,
    0x4D, 0x89, 0xDC, 0x4D, 0x21, 0xFC, 0x4D, 0x09, 0xDF, 0x49, 0x21, 0xDF, 0x4D, 0x09, 0xE7, 0x49,
    0xC1, 0xEF, 0x3F, 0x4C, 0x89, 0x7C, 0x24, 0x08, 0x48, 0x2B, 0x74, 0x24, 0x08, 0x48, 0x8B, 0x52,
    0x18, 0x49, 0x89, 0xD7, 0x4D, 0x29, 0xCF, 0x48, 0xC1, 0xFE, 0x3F, 0x4C, 0x01, 0xFE, 0x48, 0xF7,
    0xD2, 0x4D, 0x89, 0xCF] ++ bytes_l110b80_3

theorem code_l110b80_2 : ∀ x ∈ codeRange 0x110c04 bytes_l110b80_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x10c04 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110b80_3

@[cfg_block] def b_l110b80_1 : Block Op Label signature Reg.count 92 :=
  .letOp (n := 92) (.exec 0x110bbe (fun s => s.RIP = 0x110bbe) (leaR64Effect 0x110bbe 14 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 93) (.out 0x110bc3 (xorR32R32Effect 0x110bc3 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[89, 89]
    (.letOp (n := 94) (.exec 0x110bc3 (fun s => s.RIP = 0x110bc3) (xorR32R32Effect 0x110bc3 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[89, 89]
    (.letOp (n := 95) (.out 0x110bc5 (xorR32R32Effect 0x110bc5 3 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 8] []) (.reg (.gpr 8))) #v[81, 81]
    (.letOp (n := 96) (.exec 0x110bc5 (fun s => s.RIP = 0x110bc5) (xorR32R32Effect 0x110bc5 3 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[81, 81]
    (.letOp (n := 97) (.out 0x110bc8 (subR64M64Effect 0x110bc8 8 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 4] []) (.reg (.gpr 8))) #v[95, 61]
    (.letOp (n := 98) (.exec 0x110bc8 (LoadPre 0x110bc8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x110bc8 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x110bc8 8 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[95, 61]
    (.letOp (n := 99) (.out 0x110bcd (movR64M64Effect 0x110bcd 3 (.base 2 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[2]
    (.letOp (n := 100) (.exec 0x110bcd (LoadPre 0x110bcd (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x110bcd + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x110bcd 3 (.base 2 (.d8 0x8))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 101) (.out 0x110bd1 (movR64R64Effect 0x110bd1 15 3) (EffectPart.reads (.reg (.gpr 15)) [.gpr 3] []) (.reg (.gpr 15))) #v[99]
    (.letOp (n := 102) (.exec 0x110bd1 (fun s => s.RIP = 0x110bd1) (movR64R64Effect 0x110bd1 15 3) (Reg.operands [.gpr 3] [])) #v[99]
    (.letOp (n := 103) (.out 0x110bd4 (subR64R64Effect 0x110bd4 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 0] []) (.reg (.gpr 15))) #v[101, 65]
    (.letOp (n := 104) (.exec 0x110bd4 (fun s => s.RIP = 0x110bd4) (subR64R64Effect 0x110bd4 15 0) (Reg.operands [.gpr 15, .gpr 0] [])) #v[101, 65]
    (.letOp (n := 105) (.out 0x110bd7 (sarR64Effect 0x110bd7 4 8 63) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[97]
    (.letOp (n := 106) (.exec 0x110bd7 (fun s => s.RIP = 0x110bd7) (sarR64Effect 0x110bd7 4 8 63) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[97]
    (.letOp (n := 107) (.out 0x110bdb (addR64R64Effect 0x110bdb 8 15) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 15] []) (.reg (.gpr 8))) #v[105, 103]
    (.letOp (n := 108) (.exec 0x110bdb (fun s => s.RIP = 0x110bdb) (addR64R64Effect 0x110bdb 8 15) (Reg.operands [.gpr 8, .gpr 15] [])) #v[105, 103]
    (.letOp (n := 109) (.out 0x110bde (notR64Effect 0x110bde 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[99]
    (.letOp (n := 110) (.exec 0x110bde (fun s => s.RIP = 0x110bde) (notR64Effect 0x110bde 3) (Reg.operands [.gpr 3] [])) #v[99]
    (.letOp (n := 111) (.out 0x110be1 (movR64R64Effect 0x110be1 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[65]
    (.letOp (n := 112) (.exec 0x110be1 (fun s => s.RIP = 0x110be1) (movR64R64Effect 0x110be1 15 0) (Reg.operands [.gpr 0] [])) #v[65]
    (.letOp (n := 113) (.out 0x110be4 (andR64R64Effect 0x110be4 15 3) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 3] []) (.reg (.gpr 15))) #v[111, 109]
    (.letOp (n := 114) (.exec 0x110be4 (fun s => s.RIP = 0x110be4) (andR64R64Effect 0x110be4 15 3) (Reg.operands [.gpr 15, .gpr 3] [])) #v[111, 109]
    (.letOp (n := 115) (.out 0x110be7 (orR64R64Effect 0x110be7 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0] []) (.reg (.gpr 3))) #v[109, 65]
    (.letOp (n := 116) (.exec 0x110be7 (fun s => s.RIP = 0x110be7) (orR64R64Effect 0x110be7 3 0) (Reg.operands [.gpr 3, .gpr 0] [])) #v[109, 65]
    (.letOp (n := 117) (.out 0x110bea (andR64R64Effect 0x110bea 3 8) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 8] []) (.reg (.gpr 3))) #v[115, 107]
    (.letOp (n := 118) (.exec 0x110bea (fun s => s.RIP = 0x110bea) (andR64R64Effect 0x110bea 3 8) (Reg.operands [.gpr 3, .gpr 8] [])) #v[115, 107]
    (.letOp (n := 119) (.out 0x110bed (orR64R64Effect 0x110bed 3 15) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 15] []) (.reg (.gpr 3))) #v[117, 113]
    (.letOp (n := 120) (.exec 0x110bed (fun s => s.RIP = 0x110bed) (orR64R64Effect 0x110bed 3 15) (Reg.operands [.gpr 3, .gpr 15] [])) #v[117, 113]
    (.letOp (n := 121) (.out 0x110bf0 (shrR64Effect 0x110bf0 4 3 63) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[119]
    (.letOp (n := 122) (.exec 0x110bf0 (fun s => s.RIP = 0x110bf0) (shrR64Effect 0x110bf0 4 3 63) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[119]
    (.letOp (n := 123) (.exec 0x110bf4 (StorePre 0x110bf4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x110bf4 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110bf4 3 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[121, 61]
    (.letOp (n := 124) (.out 0x110bf9 (xorR32R32Effect 0x110bf9 2 3 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 3] []) (.reg (.gpr 3))) #v[121, 121]
    (.letOp (n := 125) (.exec 0x110bf9 (fun s => s.RIP = 0x110bf9) (xorR32R32Effect 0x110bf9 2 3 3) (Reg.operands [.gpr 3, .gpr 3] [])) #v[121, 121]
    (.letOp (n := 126) (.out 0x110bfb (subR64M64Effect 0x110bfb 3 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 4] []) (.reg (.gpr 3))) #v[124, 61]
    (.letOp (n := 127) (.exec 0x110bfb (LoadPre 0x110bfb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x110bfb + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x110bfb 3 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[124, 61]
    (.letOp (n := 128) (.out 0x110c00 (movR64M64Effect 0x110c00 15 (.base 2 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[2]
    (.letOp (n := 129) (.exec 0x110c00 (LoadPre 0x110c00 (fun s => AddrMode.addr (.base 2 (.d8 0x10)) s (0x110c00 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x110c00 15 (.base 2 (.d8 0x10))) (Reg.operands [.gpr 2] [])) #v[2]
    (b_l110b80_2))))))))))))))))))))))))))))))))))))))

def bytes_l110b80_1 : List UInt8 :=
  [0x4C, 0x8D, 0x74, 0x24, 0x08, 0x31, 0xF6, 0x45, 0x31, 0xC0, 0x4C, 0x2B, 0x44, 0x24, 0x08, 0x48,
    0x8B, 0x5A, 0x08, 0x49, 0x89, 0xDF, 0x49, 0x29, 0xC7, 0x49, 0xC1, 0xF8, 0x3F, 0x4D, 0x01, 0xF8,
    0x48, 0xF7, 0xD3, 0x49, 0x89, 0xC7, 0x49, 0x21, 0xDF, 0x48, 0x09, 0xC3, 0x4C, 0x21, 0xC3, 0x4C,
    0x09, 0xFB, 0x48, 0xC1, 0xEB, 0x3F, 0x48, 0x89, 0x5C, 0x24, 0x08, 0x31, 0xDB, 0x48, 0x2B, 0x5C,
    0x24, 0x08, 0x4C, 0x8B, 0x7A, 0x10] ++ bytes_l110b80_2

theorem code_l110b80_1 : ∀ x ∈ codeRange 0x110bbe bytes_l110b80_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x10bbe 70 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110b80_2

@[cfg_block] def b_l110b80 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x110b80 (pushR64Effect 0x110b80 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[4, 15]
    (.letOp (n := 54) (.exec 0x110b80 (PushPre 0x110b80 2) (pushR64Effect 0x110b80 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[4, 15]
    (.letOp (n := 55) (.out 0x110b82 (pushR64Effect 0x110b82 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[53, 14]
    (.letOp (n := 56) (.exec 0x110b82 (PushPre 0x110b82 2) (pushR64Effect 0x110b82 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 57) (.out 0x110b84 (pushR64Effect 0x110b84 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[55, 12]
    (.letOp (n := 58) (.exec 0x110b84 (PushPre 0x110b84 2) (pushR64Effect 0x110b84 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[55, 12]
    (.letOp (n := 59) (.out 0x110b86 (pushR64Effect 0x110b86 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[57, 3]
    (.letOp (n := 60) (.exec 0x110b86 (PushPre 0x110b86 1) (pushR64Effect 0x110b86 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[57, 3]
    (.letOp (n := 61) (.out 0x110b87 (subR64Imm8Effect 0x110b87 4 0x10) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 62) (.exec 0x110b87 (fun s => s.RIP = 0x110b87) (subR64Imm8Effect 0x110b87 4 0x10) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 63) (.out 0x110b8b (movR64M64Effect 0x110b8b 10 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 6] []) (.reg (.gpr 10))) #v[6]
    (.letOp (n := 64) (.exec 0x110b8b (LoadPre 0x110b8b (fun s => AddrMode.addr (.base 6 .none) s (0x110b8b + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x110b8b 10 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 65) (.out 0x110b8e (movR64M64Effect 0x110b8e 0 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 66) (.exec 0x110b8e (LoadPre 0x110b8e (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x110b8e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x110b8e 0 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 67) (.out 0x110b92 (movR64M64Effect 0x110b92 11 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 6] []) (.reg (.gpr 11))) #v[6]
    (.letOp (n := 68) (.exec 0x110b92 (LoadPre 0x110b92 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x110b92 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x110b92 11 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 69) (.out 0x110b96 (movR64M64Effect 0x110b96 9 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 6] []) (.reg (.gpr 9))) #v[6]
    (.letOp (n := 70) (.exec 0x110b96 (LoadPre 0x110b96 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x110b96 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x110b96 9 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 71) (.out 0x110b9a (movR64M64Effect 0x110b9a 6 (.base 2 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[2]
    (.letOp (n := 72) (.exec 0x110b9a (LoadPre 0x110b9a (fun s => AddrMode.addr (.base 2 .none) s (0x110b9a + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x110b9a 6 (.base 2 .none)) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 73) (.out 0x110b9d (movR64R64Effect 0x110b9d 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[71]
    (.letOp (n := 74) (.exec 0x110b9d (fun s => s.RIP = 0x110b9d) (movR64R64Effect 0x110b9d 1 6) (Reg.operands [.gpr 6] [])) #v[71]
    (.letOp (n := 75) (.out 0x110ba0 (subR64R64Effect 0x110ba0 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10] []) (.reg (.gpr 1))) #v[73, 63]
    (.letOp (n := 76) (.exec 0x110ba0 (fun s => s.RIP = 0x110ba0) (subR64R64Effect 0x110ba0 1 10) (Reg.operands [.gpr 1, .gpr 10] [])) #v[73, 63]
    (.letOp (n := 77) (.out 0x110ba3 (notR64Effect 0x110ba3 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[71]
    (.letOp (n := 78) (.exec 0x110ba3 (fun s => s.RIP = 0x110ba3) (notR64Effect 0x110ba3 6) (Reg.operands [.gpr 6] [])) #v[71]
    (.letOp (n := 79) (.out 0x110ba6 (movR64R64Effect 0x110ba6 8 10) (EffectPart.reads (.reg (.gpr 8)) [.gpr 10] []) (.reg (.gpr 8))) #v[63]
    (.letOp (n := 80) (.exec 0x110ba6 (fun s => s.RIP = 0x110ba6) (movR64R64Effect 0x110ba6 8 10) (Reg.operands [.gpr 10] [])) #v[63]
    (.letOp (n := 81) (.out 0x110ba9 (andR64R64Effect 0x110ba9 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6] []) (.reg (.gpr 8))) #v[79, 77]
    (.letOp (n := 82) (.exec 0x110ba9 (fun s => s.RIP = 0x110ba9) (andR64R64Effect 0x110ba9 8 6) (Reg.operands [.gpr 8, .gpr 6] [])) #v[79, 77]
    (.letOp (n := 83) (.out 0x110bac (orR64R64Effect 0x110bac 6 10) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 10] []) (.reg (.gpr 6))) #v[77, 63]
    (.letOp (n := 84) (.exec 0x110bac (fun s => s.RIP = 0x110bac) (orR64R64Effect 0x110bac 6 10) (Reg.operands [.gpr 6, .gpr 10] [])) #v[77, 63]
    (.letOp (n := 85) (.out 0x110baf (andR64R64Effect 0x110baf 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[83, 75]
    (.letOp (n := 86) (.exec 0x110baf (fun s => s.RIP = 0x110baf) (andR64R64Effect 0x110baf 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[83, 75]
    (.letOp (n := 87) (.out 0x110bb2 (orR64R64Effect 0x110bb2 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 8] []) (.reg (.gpr 6))) #v[85, 81]
    (.letOp (n := 88) (.exec 0x110bb2 (fun s => s.RIP = 0x110bb2) (orR64R64Effect 0x110bb2 6 8) (Reg.operands [.gpr 6, .gpr 8] [])) #v[85, 81]
    (.letOp (n := 89) (.out 0x110bb5 (shrR64Effect 0x110bb5 4 6 63) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[87]
    (.letOp (n := 90) (.exec 0x110bb5 (fun s => s.RIP = 0x110bb5) (shrR64Effect 0x110bb5 4 6 63) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[87]
    (.letOp (n := 91) (.exec 0x110bb9 (StorePre 0x110bb9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x110bb9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110bb9 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[89, 61]
    (b_l110b80_1)))))))))))))))))))))))))))))))))))))))

def bytes_l110b80 : List UInt8 :=
  [0x41, 0x57, 0x41, 0x56, 0x41, 0x54, 0x53, 0x48, 0x83, 0xEC, 0x10, 0x4C, 0x8B, 0x16, 0x48, 0x8B,
    0x46, 0x08, 0x4C, 0x8B, 0x5E, 0x10, 0x4C, 0x8B, 0x4E, 0x18, 0x48, 0x8B, 0x32, 0x48, 0x89, 0xF1,
    0x4C, 0x29, 0xD1, 0x48, 0xF7, 0xD6, 0x4D, 0x89, 0xD0, 0x49, 0x21, 0xF0, 0x4C, 0x09, 0xD6, 0x48,
    0x21, 0xCE, 0x4C, 0x09, 0xC6, 0x48, 0xC1, 0xEE, 0x3F, 0x48, 0x89, 0x74, 0x24, 0x08] ++ bytes_l110b80_1

theorem code_l110b80 : ∀ x ∈ codeRange 0x110b80 bytes_l110b80, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x10b80 62 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110b80_1

@[cfg_block] def b_l110cd0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x110cd0 (pushR64Effect 0x110cd0 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x110cd0 (PushPre 0x110cd0 1) (pushR64Effect 0x110cd0 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x110cd1 (pushR64Effect 0x110cd1 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x110cd1 (PushPre 0x110cd1 2) (pushR64Effect 0x110cd1 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x110cd3 (pushR64Effect 0x110cd3 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x110cd3 (PushPre 0x110cd3 2) (pushR64Effect 0x110cd3 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x110cd5 (pushR64Effect 0x110cd5 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x110cd5 (PushPre 0x110cd5 2) (pushR64Effect 0x110cd5 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x110cd7 (pushR64Effect 0x110cd7 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x110cd7 (PushPre 0x110cd7 2) (pushR64Effect 0x110cd7 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x110cd9 (pushR64Effect 0x110cd9 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x110cd9 (PushPre 0x110cd9 1) (pushR64Effect 0x110cd9 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x110cda (subR64Imm32Effect 0x110cda 4 0x1f8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x110cda (fun s => s.RIP = 0x110cda) (subR64Imm32Effect 0x110cda 4 0x1f8) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.exec 0x110ce1 (StorePre 0x110ce1 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1a0)) s (0x110ce1 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x110ce1 7 (.sib 4 none 0 (.d32 0x1a0))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[7, 65]
    (.letOp (n := 68) (.out 0x110ce9 (leaR64Effect 0x110ce9 7 (.sib 4 none 0 (.d32 0x128))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[65]
    (.letOp (n := 69) (.exec 0x110ce9 (fun s => s.RIP = 0x110ce9) (leaR64Effect 0x110ce9 7 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 70) (.out 0x110cf1 (movR32Imm32Effect 0x110cf1 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 71) (.exec 0x110cf1 (fun s => s.RIP = 0x110cf1) (movR32Imm32Effect 0x110cf1 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 72) (.exec 0x110cf6 (RepPre 0x110cf6 (RepMovsqPre 0x110cf6)) (repMovsqEffect 0x110cf6) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[6, 68, 70, 22]
    (.letOp (n := 73) (.out 0x110cf9 (leaR64Effect 0x110cf9 6 (.sib 4 none 0 (.d32 0x150))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[65]
    (.letOp (n := 74) (.exec 0x110cf9 (fun s => s.RIP = 0x110cf9) (leaR64Effect 0x110cf9 6 (.sib 4 none 0 (.d32 0x150))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 75) (.out 0x110d01 (leaR64Effect 0x110d01 7 (.sib 4 none 0 (.d32 0x1a8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[65]
    (.letOp (n := 76) (.exec 0x110d01 (fun s => s.RIP = 0x110d01) (leaR64Effect 0x110d01 7 (.sib 4 none 0 (.d32 0x1a8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 77) (.out 0x110d09 (callEffect (fun _ => 0x1145f0) 0x110d0e) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 78) (.exec 0x110d09 (PushPre 0x110d09 5) (callEffect (fun _ => 0x1145f0) 0x110d0e) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 79) (.const ⟨64, 0x110d0e⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(3, 3), (4, 77), (5, 5), (6, 73), (7, 75), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 80⟩ { target := .l110d0e, kept := #v[], arity := rfl, guard := some (Fin.last 79) }))))))))))))))))))))))))))))

def bytes_l110cd0 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0xF8, 0x01, 0x00,
    0x00, 0x48, 0x89, 0xBC, 0x24, 0xA0, 0x01, 0x00, 0x00, 0x48, 0x8D, 0xBC, 0x24, 0x28, 0x01, 0x00,
    0x00, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0xF3, 0x48, 0xA5, 0x48, 0x8D, 0xB4, 0x24, 0x50, 0x01, 0x00,
    0x00, 0x48, 0x8D, 0xBC, 0x24, 0xA8, 0x01, 0x00, 0x00, 0xE8, 0xE2, 0x38, 0x00, 0x00]

theorem code_l110cd0 : ∀ x ∈ codeRange 0x110cd0 bytes_l110cd0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x10cd0 62 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l110d0e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x110d0e (movR64M64Effect 0x110d0e 0 (.sib 4 none 0 (.d32 0x1a8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x110d0e (LoadPre 0x110d0e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1a8)) s (0x110d0e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x110d0e 0 (.sib 4 none 0 (.d32 0x1a8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x110d16 (StorePre 0x110d16 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x110d16 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110d16 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x110d1b (movR64M64Effect 0x110d1b 0 (.sib 4 none 0 (.d32 0x1b0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x110d1b (LoadPre 0x110d1b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1b0)) s (0x110d1b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x110d1b 0 (.sib 4 none 0 (.d32 0x1b0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x110d23 (StorePre 0x110d23 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x110d23 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110d23 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x110d28 (movR64M64Effect 0x110d28 0 (.sib 4 none 0 (.d32 0x1b8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x110d28 (LoadPre 0x110d28 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1b8)) s (0x110d28 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x110d28 0 (.sib 4 none 0 (.d32 0x1b8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x110d30 (StorePre 0x110d30 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x110d30 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110d30 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x110d35 (movR64M64Effect 0x110d35 0 (.sib 4 none 0 (.d32 0x1c0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x110d35 (LoadPre 0x110d35 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1c0)) s (0x110d35 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x110d35 0 (.sib 4 none 0 (.d32 0x1c0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x110d3d (StorePre 0x110d3d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x110d3d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110d3d 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x110d42 (movR64M64Effect 0x110d42 0 (.sib 4 none 0 (.d32 0x1c8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 66) (.exec 0x110d42 (LoadPre 0x110d42 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1c8)) s (0x110d42 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x110d42 0 (.sib 4 none 0 (.d32 0x1c8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x110d4a (StorePre 0x110d4a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x110d4a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110d4a 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x110d4f (leaR64Effect 0x110d4f 6 (.sib 4 none 0 (.d32 0x178))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 69) (.exec 0x110d4f (fun s => s.RIP = 0x110d4f) (leaR64Effect 0x110d4f 6 (.sib 4 none 0 (.d32 0x178))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.out 0x110d57 (leaR64Effect 0x110d57 7 (.sib 4 none 0 (.d32 0x1d0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 71) (.exec 0x110d57 (fun s => s.RIP = 0x110d57) (leaR64Effect 0x110d57 7 (.sib 4 none 0 (.d32 0x1d0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.out 0x110d5f (callEffect (fun _ => 0x1145f0) 0x110d64) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x110d5f (PushPre 0x110d5f 5) (callEffect (fun _ => 0x1145f0) 0x110d64) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x110d64⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 65), (3, 3), (4, 72), (5, 5), (6, 68), (7, 70), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l110d64, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l110d0e : List UInt8 :=
  [0x48, 0x8B, 0x84, 0x24, 0xA8, 0x01, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x84,
    0x24, 0xB0, 0x01, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x28, 0x48, 0x8B, 0x84, 0x24, 0xB8, 0x01,
    0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x48, 0x48, 0x8B, 0x84, 0x24, 0xC0, 0x01, 0x00, 0x00, 0x48,
    0x89, 0x44, 0x24, 0x60, 0x48, 0x8B, 0x84, 0x24, 0xC8, 0x01, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24,
    0x40, 0x48, 0x8D, 0xB4, 0x24, 0x78, 0x01, 0x00, 0x00, 0x48, 0x8D, 0xBC, 0x24, 0xD0, 0x01, 0x00,
    0x00, 0xE8, 0x8C, 0x38, 0x00, 0x00]

theorem code_l110d0e : ∀ x ∈ codeRange 0x110d0e bytes_l110d0e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x10d0e 86 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

end K256.Proofs.Signing.LIR
