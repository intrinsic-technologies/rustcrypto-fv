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

@[cfg_block] def b_l109490_2 : Block Op Label signature Reg.count 112 :=
  .letOp (n := 112) (.exec 0x10955c (StorePre 0x10955c 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10955c + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10955c (.sib 4 none 0 (.d8 0x60)) 0x0) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 113) (.out 0x109565 (movR64M64Effect 0x109565 0 (.base 8 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[8]
    (.letOp (n := 114) (.exec 0x109565 (LoadPre 0x109565 (fun s => AddrMode.addr (.base 8 (.d8 0x18)) s (0x109565 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109565 0 (.base 8 (.d8 0x18))) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 115) (.exec 0x109569 (StorePre 0x109569 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x109569 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x109569 0 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[113, 65]
    (.letOp (n := 116) (.out 0x109571 (movR64M64Effect 0x109571 0 (.base 8 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[8]
    (.letOp (n := 117) (.exec 0x109571 (LoadPre 0x109571 (fun s => AddrMode.addr (.base 8 (.d8 0x10)) s (0x109571 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109571 0 (.base 8 (.d8 0x10))) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 118) (.exec 0x109575 (StorePre 0x109575 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x109575 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x109575 0 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[116, 65]
    (.letOp (n := 119) (.out 0x10957d (movR64M64Effect 0x10957d 0 (.base 8 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[8]
    (.letOp (n := 120) (.exec 0x10957d (LoadPre 0x10957d (fun s => AddrMode.addr (.base 8 .none) s (0x10957d + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x10957d 0 (.base 8 .none)) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 121) (.out 0x109580 (movR64M64Effect 0x109580 1 (.base 8 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 8] []) (.reg (.gpr 1))) #v[8]
    (.letOp (n := 122) (.exec 0x109580 (LoadPre 0x109580 (fun s => AddrMode.addr (.base 8 (.d8 0x8)) s (0x109580 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109580 1 (.base 8 (.d8 0x8))) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 123) (.exec 0x109584 (StorePre 0x109584 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x109584 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x109584 1 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[121, 65]
    (.letOp (n := 124) (.exec 0x10958c (StorePre 0x10958c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10958c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10958c 0 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[119, 65]
    (.letOp (n := 125) (.exec 0x109594 (StorePre 0x109594 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x109594 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x109594 (.sib 4 none 0 (.d32 0xa8)) 0x0) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 126) (.out 0x10959c (movR32Imm32Effect 0x10959c 6 12 0x1) (EffectPart.reads (.reg (.gpr 12)) [] []) (.reg (.gpr 12))) #v[]
    (.letOp (n := 127) (.exec 0x10959c (fun s => s.RIP = 0x10959c) (movR32Imm32Effect 0x10959c 6 12 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 128) (.out 0x1095a2 (movR32Imm32Effect 0x1095a2 5 6 0x24f) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 129) (.exec 0x1095a2 (fun s => s.RIP = 0x1095a2) (movR32Imm32Effect 0x1095a2 5 6 0x24f) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l1097fe, RegMap.args [(0, 119), (1, 121), (2, 2), (3, 3), (4, 65), (5, 5), (6, 128), (7, 7), (8, 8), (12, 126), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 130⟩)))))))))))))))))))

def bytes_l109490_2 : List UInt8 :=
  [0x48, 0xC7, 0x44, 0x24, 0x60, 0x00, 0x00, 0x00, 0x00, 0x49, 0x8B, 0x40, 0x18, 0x48, 0x89, 0x84,
    0x24, 0xA0, 0x00, 0x00, 0x00, 0x49, 0x8B, 0x40, 0x10, 0x48, 0x89, 0x84, 0x24, 0x98, 0x00, 0x00,
    0x00, 0x49, 0x8B, 0x00, 0x49, 0x8B, 0x48, 0x08, 0x48, 0x89, 0x8C, 0x24, 0x90, 0x00, 0x00, 0x00,
    0x48, 0x89, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, 0xC6, 0x84, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x00,
    0x41, 0xBC, 0x01, 0x00, 0x00, 0x00, 0xBE, 0x4F, 0x02, 0x00, 0x00, 0xE9, 0x52, 0x02, 0x00, 0x00]

theorem code_l109490_2 : ∀ x ∈ codeRange 0x10955c bytes_l109490_2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x955c 80 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109490_1 : Block Op Label signature Reg.count 86 :=
  .letOp (n := 86) (.exec 0x1094ed (StorePre 0x1094ed 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1094ed + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1094ed 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[84, 65]
    (.letOp (n := 87) (.out 0x1094f2 (movR64M64Effect 0x1094f2 0 (.base 2 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 88) (.exec 0x1094f2 (LoadPre 0x1094f2 (fun s => AddrMode.addr (.base 2 .none) s (0x1094f2 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1094f2 0 (.base 2 .none)) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 89) (.exec 0x1094f5 (StorePre 0x1094f5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1094f5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1094f5 2 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2, 65]
    (.letOp (n := 90) (.out 0x1094fa (movR64M64Effect 0x1094fa 1 (.base 2 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2]
    (.letOp (n := 91) (.exec 0x1094fa (LoadPre 0x1094fa (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x1094fa + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1094fa 1 (.base 2 (.d8 0x8))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 92) (.exec 0x1094fe (StorePre 0x1094fe 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1094fe + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1094fe 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[90, 65]
    (.letOp (n := 93) (.exec 0x109503 (StorePre 0x109503 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109503 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109503 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[87, 65]
    (.letOp (n := 94) (.exec 0x109508 (StorePre 0x109508 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x109508 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x109508 (.sib 4 none 0 (.d8 0x28)) 0x0) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 95) (.out 0x10950d (movR64M64Effect 0x10950d 0 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 96) (.exec 0x10950d (LoadPre 0x10950d (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x10950d + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10950d 0 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 97) (.exec 0x109511 (StorePre 0x109511 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x109511 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109511 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[95, 65]
    (.letOp (n := 98) (.out 0x109516 (movR64M64Effect 0x109516 0 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 99) (.exec 0x109516 (LoadPre 0x109516 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x109516 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109516 0 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 100) (.exec 0x10951a (StorePre 0x10951a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10951a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10951a 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[98, 65]
    (.letOp (n := 101) (.out 0x10951f (movR64M64Effect 0x10951f 0 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 102) (.exec 0x10951f (LoadPre 0x10951f (fun s => AddrMode.addr (.base 6 .none) s (0x10951f + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x10951f 0 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 103) (.out 0x109522 (movR64M64Effect 0x109522 1 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[6]
    (.letOp (n := 104) (.exec 0x109522 (LoadPre 0x109522 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x109522 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109522 1 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 105) (.exec 0x109526 (StorePre 0x109526 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x109526 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109526 1 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[103, 65]
    (.letOp (n := 106) (.exec 0x10952b (StorePre 0x10952b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10952b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10952b 0 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[101, 65]
    (.letOp (n := 107) (.exec 0x109530 (StorePre 0x109530 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x109530 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x109530 (.sib 4 none 0 (.d8 0x50)) 0x0) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 108) (.exec 0x109535 (StorePre 0x109535 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x109535 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x109535 (.sib 4 none 0 (.d32 0x80)) 0x0) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 109) (.exec 0x109541 (StorePre 0x109541 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x109541 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x109541 (.sib 4 none 0 (.d8 0x78)) 0x0) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 110) (.exec 0x10954a (StorePre 0x10954a 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x10954a + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10954a (.sib 4 none 0 (.d8 0x70)) 0x0) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 111) (.exec 0x109553 (StorePre 0x109553 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x109553 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x109553 (.sib 4 none 0 (.d8 0x68)) 0x0) (Reg.operands [.gpr 4] [])) #v[65]
    (b_l109490_2))))))))))))))))))))))))))

def bytes_l109490_1 : List UInt8 :=
  [0x48, 0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x02, 0x48, 0x89, 0x54, 0x24, 0x58, 0x48, 0x8B, 0x4A,
    0x08, 0x48, 0x89, 0x4C, 0x24, 0x10, 0x48, 0x89, 0x44, 0x24, 0x08, 0xC6, 0x44, 0x24, 0x28, 0x00,
    0x48, 0x8B, 0x46, 0x18, 0x48, 0x89, 0x44, 0x24, 0x48, 0x48, 0x8B, 0x46, 0x10, 0x48, 0x89, 0x44,
    0x24, 0x40, 0x48, 0x8B, 0x06, 0x48, 0x8B, 0x4E, 0x08, 0x48, 0x89, 0x4C, 0x24, 0x38, 0x48, 0x89,
    0x44, 0x24, 0x30, 0xC6, 0x44, 0x24, 0x50, 0x00, 0x48, 0xC7, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x78, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44,
    0x24, 0x70, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x68, 0x00, 0x00, 0x00, 0x00] ++ bytes_l109490_2

theorem code_l109490_1 : ∀ x ∈ codeRange 0x1094ed bytes_l109490_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x94ed 111 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l109490_2

@[cfg_block] def b_l109490 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x109490 (pushR64Effect 0x109490 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x109490 (PushPre 0x109490 1) (pushR64Effect 0x109490 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x109491 (pushR64Effect 0x109491 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x109491 (PushPre 0x109491 2) (pushR64Effect 0x109491 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x109493 (pushR64Effect 0x109493 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x109493 (PushPre 0x109493 2) (pushR64Effect 0x109493 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x109495 (pushR64Effect 0x109495 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x109495 (PushPre 0x109495 2) (pushR64Effect 0x109495 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x109497 (pushR64Effect 0x109497 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x109497 (PushPre 0x109497 2) (pushR64Effect 0x109497 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x109499 (pushR64Effect 0x109499 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x109499 (PushPre 0x109499 1) (pushR64Effect 0x109499 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x10949a (subR64Imm32Effect 0x10949a 4 0x158) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x10949a (fun s => s.RIP = 0x10949a) (subR64Imm32Effect 0x10949a 4 0x158) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.exec 0x1094a1 (StorePre 0x1094a1 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x1094a1 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1094a1 1 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1, 65]
    (.letOp (n := 68) (.exec 0x1094a9 (StorePre 0x1094a9 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x1094a9 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1094a9 7 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[7, 65]
    (.letOp (n := 69) (.out 0x1094b1 (movR64M64Effect 0x1094b1 0 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 70) (.exec 0x1094b1 (LoadPre 0x1094b1 (fun s => AddrMode.addr (.base 6 .none) s (0x1094b1 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1094b1 0 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 71) (.exec 0x1094b4 (StorePre 0x1094b4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x1094b4 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1094b4 0 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[69, 65]
    (.letOp (n := 72) (.out 0x1094bc (movR64M64Effect 0x1094bc 0 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 73) (.exec 0x1094bc (LoadPre 0x1094bc (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x1094bc + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1094bc 0 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 74) (.exec 0x1094c0 (StorePre 0x1094c0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x1094c0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1094c0 0 (.sib 4 none 0 (.d32 0x118))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[72, 65]
    (.letOp (n := 75) (.out 0x1094c8 (movR64M64Effect 0x1094c8 0 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 76) (.exec 0x1094c8 (LoadPre 0x1094c8 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x1094c8 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1094c8 0 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 77) (.exec 0x1094cc (StorePre 0x1094cc 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x1094cc + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1094cc 0 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[75, 65]
    (.letOp (n := 78) (.out 0x1094d4 (movR64M64Effect 0x1094d4 0 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 79) (.exec 0x1094d4 (LoadPre 0x1094d4 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x1094d4 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1094d4 0 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 80) (.exec 0x1094d8 (StorePre 0x1094d8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x1094d8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1094d8 0 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[78, 65]
    (.letOp (n := 81) (.out 0x1094e0 (movR64M64Effect 0x1094e0 0 (.base 2 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 82) (.exec 0x1094e0 (LoadPre 0x1094e0 (fun s => AddrMode.addr (.base 2 (.d8 0x18)) s (0x1094e0 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1094e0 0 (.base 2 (.d8 0x18))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 83) (.exec 0x1094e4 (StorePre 0x1094e4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1094e4 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1094e4 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[81, 65]
    (.letOp (n := 84) (.out 0x1094e9 (movR64M64Effect 0x1094e9 0 (.base 2 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 85) (.exec 0x1094e9 (LoadPre 0x1094e9 (fun s => AddrMode.addr (.base 2 (.d8 0x10)) s (0x1094e9 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1094e9 0 (.base 2 (.d8 0x10))) (Reg.operands [.gpr 2] [])) #v[2]
    (b_l109490_1)))))))))))))))))))))))))))))))))

def bytes_l109490 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0x58, 0x01, 0x00,
    0x00, 0x48, 0x89, 0x8C, 0x24, 0x28, 0x01, 0x00, 0x00, 0x48, 0x89, 0xBC, 0x24, 0x20, 0x01, 0x00,
    0x00, 0x48, 0x8B, 0x06, 0x48, 0x89, 0x84, 0x24, 0x08, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x46, 0x08,
    0x48, 0x89, 0x84, 0x24, 0x18, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x46, 0x10, 0x48, 0x89, 0x84, 0x24,
    0x00, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x46, 0x18, 0x48, 0x89, 0x84, 0x24, 0x10, 0x01, 0x00, 0x00,
    0x48, 0x8B, 0x42, 0x18, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x42, 0x10] ++ bytes_l109490_1

theorem code_l109490 : ∀ x ∈ codeRange 0x109490 bytes_l109490, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x9490 93 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l109490_1

@[cfg_block] def b_l1095b0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1095b0 (movR32Imm32Effect 0x1095b0 6 14 0x1) (EffectPart.reads (.reg (.gpr 14)) [] []) (.reg (.gpr 14))) #v[]
    (.letOp (n := 54) (.exec 0x1095b0 (fun s => s.RIP = 0x1095b0) (movR32Imm32Effect 0x1095b0 6 14 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x1095b6 (xorR32R32Effect 0x1095b6 3 13 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 13] []) (.reg (.gpr 13))) #v[13, 13]
    (.letOp (n := 56) (.exec 0x1095b6 (fun s => s.RIP = 0x1095b6) (xorR32R32Effect 0x1095b6 3 13 13) (Reg.operands [.gpr 13, .gpr 13] [])) #v[13, 13]
    (.letOp (n := 57) (.out 0x1095b9 (xorR32R32Effect 0x1095b9 3 15 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 15] []) (.reg (.gpr 15))) #v[15, 15]
    (.letOp (n := 58) (.exec 0x1095b9 (fun s => s.RIP = 0x1095b9) (xorR32R32Effect 0x1095b9 3 15 15) (Reg.operands [.gpr 15, .gpr 15] [])) #v[15, 15]
    (.letOp (n := 59) (.out 0x1095bc (movR32Imm32Effect 0x1095bc 5 3 0x1) (EffectPart.reads (.reg (.gpr 3)) [] []) (.reg (.gpr 3))) #v[]
    (.letOp (n := 60) (.exec 0x1095bc (fun s => s.RIP = 0x1095bc) (movR32Imm32Effect 0x1095bc 5 3 0x1) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l1095c1, RegMap.args [(3, 59), (4, 4), (9, 9), (12, 12), (13, 55), (14, 53), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩)))))))))

def bytes_l1095b0 : List UInt8 :=
  [0x41, 0xBE, 0x01, 0x00, 0x00, 0x00, 0x45, 0x31, 0xED, 0x45, 0x31, 0xFF, 0xBB, 0x01, 0x00, 0x00,
    0x00]

theorem code_l1095b0 : ∀ x ∈ codeRange 0x1095b0 bytes_l1095b0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x95b0 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1095c1 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1095c1 (movR64R64Effect 0x1095c1 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 54) (.exec 0x1095c1 (fun s => s.RIP = 0x1095c1) (movR64R64Effect 0x1095c1 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x1095c4 (shrR64Effect 0x1095c4 4 0 63) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x1095c4 (fun s => s.RIP = 0x1095c4) (shrR64Effect 0x1095c4 4 0 63) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 57) (.exec 0x1095c8 (StorePre 0x1095c8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x138)) s (0x1095c8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1095c8 0 (.sib 4 none 0 (.d32 0x138))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 58) (.exec 0x1095d0 (StorePre 0x1095d0 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x1095d0 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1095d0 4 0 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 59) (.exec 0x1095d4 (fun s => s.RIP = 0x1095d4) (leaR64Effect 0x1095d4 1 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.out 0x1095d9 (movR64R64Effect 0x1095d9 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[15]
    (.letOp (n := 61) (.exec 0x1095d9 (fun s => s.RIP = 0x1095d9) (movR64R64Effect 0x1095d9 0 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 62) (.out 0x1095dc (shrR64Effect 0x1095dc 4 0 63) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[60]
    (.letOp (n := 63) (.exec 0x1095dc (fun s => s.RIP = 0x1095dc) (shrR64Effect 0x1095dc 4 0 63) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[60]
    (.letOp (n := 64) (.exec 0x1095e0 (StorePre 0x1095e0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x1095e0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1095e0 0 (.sib 4 none 0 (.d32 0x140))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.exec 0x1095e8 (StorePre 0x1095e8 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x1095e8 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1095e8 4 0 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 66) (.out 0x1095ec (leaR64Effect 0x1095ec 7 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 67) (.exec 0x1095ec (fun s => s.RIP = 0x1095ec) (leaR64Effect 0x1095ec 7 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.out 0x1095f4 (leaR64Effect 0x1095f4 6 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 69) (.exec 0x1095f4 (fun s => s.RIP = 0x1095f4) (leaR64Effect 0x1095f4 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.out 0x1095f9 (leaR64Effect 0x1095f9 2 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 71) (.exec 0x1095f9 (fun s => s.RIP = 0x1095f9) (leaR64Effect 0x1095f9 2 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.out 0x1095fe (movR64R64Effect 0x1095fe 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 3] []) (.reg (.gpr 1))) #v[3]
    (.letOp (n := 73) (.exec 0x1095fe (fun s => s.RIP = 0x1095fe) (movR64R64Effect 0x1095fe 1 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 74) (.out 0x109601 (movR64R64Effect 0x109601 8 15) (EffectPart.reads (.reg (.gpr 8)) [.gpr 15] []) (.reg (.gpr 8))) #v[15]
    (.letOp (n := 75) (.exec 0x109601 (fun s => s.RIP = 0x109601) (movR64R64Effect 0x109601 8 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 76) (.out 0x109604 (movR32R32Effect 0x109604 3 5 9) (EffectPart.reads (.reg (.gpr 5)) [.gpr 9] []) (.reg (.gpr 5))) #v[9]
    (.letOp (n := 77) (.exec 0x109604 (fun s => s.RIP = 0x109604) (movR32R32Effect 0x109604 3 5 9) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 78) (.out 0x109607 (callEffect (fun _ => 0x108890) 0x10960c) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 79) (.exec 0x109607 (PushPre 0x109607 5) (callEffect (fun _ => 0x108890) 0x10960c) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 80) (.const ⟨64, 0x10960c⟩) #v[]
    (.terminate (.call ⟨.l108890, RegMap.args [(0, 62), (1, 72), (2, 70), (3, 3), (4, 78), (5, 76), (6, 68), (7, 66), (8, 74), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 81⟩ { target := .l10960c, kept := #v[], arity := rfl, guard := some (Fin.last 80) })))))))))))))))))))))))))))))

def bytes_l1095c1 : List UInt8 :=
  [0x48, 0x89, 0xD8, 0x48, 0xC1, 0xE8, 0x3F, 0x48, 0x89, 0x84, 0x24, 0x38, 0x01, 0x00, 0x00, 0x88,
    0x44, 0x24, 0x07, 0x48, 0x8D, 0x4C, 0x24, 0x07, 0x4C, 0x89, 0xF8, 0x48, 0xC1, 0xE8, 0x3F, 0x48,
    0x89, 0x84, 0x24, 0x40, 0x01, 0x00, 0x00, 0x88, 0x44, 0x24, 0x07, 0x48, 0x8D, 0xBC, 0x24, 0xB0,
    0x00, 0x00, 0x00, 0x48, 0x8D, 0x74, 0x24, 0x08, 0x48, 0x8D, 0x54, 0x24, 0x30, 0x48, 0x89, 0xD9,
    0x4D, 0x89, 0xF8, 0x44, 0x89, 0xCD, 0xE8, 0x84, 0xF2, 0xFF, 0xFF]

theorem code_l1095c1 : ∀ x ∈ codeRange 0x1095c1 bytes_l1095c1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x95c1 75 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10960c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10960c (movR64R64Effect 0x10960c 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[13]
    (.letOp (n := 54) (.exec 0x10960c (fun s => s.RIP = 0x10960c) (movR64R64Effect 0x10960c 0 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 55) (.out 0x10960f (shrR64Effect 0x10960f 4 0 63) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x10960f (fun s => s.RIP = 0x10960f) (shrR64Effect 0x10960f 4 0 63) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 57) (.exec 0x109613 (StorePre 0x109613 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x148)) s (0x109613 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x109613 0 (.sib 4 none 0 (.d32 0x148))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 58) (.exec 0x10961b (StorePre 0x10961b 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x10961b + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10961b 4 0 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 59) (.exec 0x10961f (fun s => s.RIP = 0x10961f) (leaR64Effect 0x10961f 0 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.out 0x109624 (movR64R64Effect 0x109624 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[14]
    (.letOp (n := 61) (.exec 0x109624 (fun s => s.RIP = 0x109624) (movR64R64Effect 0x109624 1 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 62) (.out 0x109627 (shrR64Effect 0x109627 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[60]
    (.letOp (n := 63) (.exec 0x109627 (fun s => s.RIP = 0x109627) (shrR64Effect 0x109627 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[60]
    (.letOp (n := 64) (.exec 0x10962b (StorePre 0x10962b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x10962b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10962b 1 (.sib 4 none 0 (.d32 0x130))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.exec 0x109633 (StorePre 0x109633 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x109633 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109633 4 1 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 66) (.out 0x109637 (leaR64Effect 0x109637 7 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 67) (.exec 0x109637 (fun s => s.RIP = 0x109637) (leaR64Effect 0x109637 7 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.out 0x10963f (leaR64Effect 0x10963f 6 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 69) (.exec 0x10963f (fun s => s.RIP = 0x10963f) (leaR64Effect 0x10963f 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.out 0x109644 (leaR64Effect 0x109644 2 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 71) (.exec 0x109644 (fun s => s.RIP = 0x109644) (leaR64Effect 0x109644 2 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.out 0x109649 (movR64R64Effect 0x109649 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 13] []) (.reg (.gpr 1))) #v[13]
    (.letOp (n := 73) (.exec 0x109649 (fun s => s.RIP = 0x109649) (movR64R64Effect 0x109649 1 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 74) (.out 0x10964c (movR64R64Effect 0x10964c 8 14) (EffectPart.reads (.reg (.gpr 8)) [.gpr 14] []) (.reg (.gpr 8))) #v[14]
    (.letOp (n := 75) (.exec 0x10964c (fun s => s.RIP = 0x10964c) (movR64R64Effect 0x10964c 8 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 76) (.out 0x10964f (movR32R32Effect 0x10964f 3 9 5) (EffectPart.reads (.reg (.gpr 9)) [.gpr 5] []) (.reg (.gpr 9))) #v[5]
    (.letOp (n := 77) (.exec 0x10964f (fun s => s.RIP = 0x10964f) (movR32R32Effect 0x10964f 3 9 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 78) (.out 0x109652 (callEffect (fun _ => 0x108890) 0x109657) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 79) (.exec 0x109652 (PushPre 0x109652 5) (callEffect (fun _ => 0x108890) 0x109657) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 80) (.const ⟨64, 0x109657⟩) #v[]
    (.terminate (.call ⟨.l108890, RegMap.args [(1, 72), (2, 70), (3, 3), (4, 78), (5, 5), (6, 68), (7, 66), (8, 74), (9, 76), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 81⟩ { target := .l109657, kept := #v[], arity := rfl, guard := some (Fin.last 80) })))))))))))))))))))))))))))))

def bytes_l10960c : List UInt8 :=
  [0x4C, 0x89, 0xE8, 0x48, 0xC1, 0xE8, 0x3F, 0x48, 0x89, 0x84, 0x24, 0x48, 0x01, 0x00, 0x00, 0x88,
    0x44, 0x24, 0x07, 0x48, 0x8D, 0x44, 0x24, 0x07, 0x4C, 0x89, 0xF1, 0x48, 0xC1, 0xE9, 0x3F, 0x48,
    0x89, 0x8C, 0x24, 0x30, 0x01, 0x00, 0x00, 0x88, 0x4C, 0x24, 0x07, 0x48, 0x8D, 0xBC, 0x24, 0xD8,
    0x00, 0x00, 0x00, 0x48, 0x8D, 0x74, 0x24, 0x08, 0x48, 0x8D, 0x54, 0x24, 0x30, 0x4C, 0x89, 0xE9,
    0x4D, 0x89, 0xF0, 0x41, 0x89, 0xE9, 0xE8, 0x39, 0xF2, 0xFF, 0xFF]

theorem code_l10960c : ∀ x ∈ codeRange 0x10960c bytes_l10960c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x960c 75 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109657_1 : Block Op Label signature Reg.count 84 :=
  .letOp (n := 84) (.exec 0x1096c7 (StorePre 0x1096c7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1096c7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1096c7 0 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[82, 4]
    (.letOp (n := 85) (.out 0x1096cc (movR64M64Effect 0x1096cc 0 (.sib 4 none 0 (.d32 0x138))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 86) (.exec 0x1096cc (LoadPre 0x1096cc (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x138)) s (0x1096cc + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1096cc 0 (.sib 4 none 0 (.d32 0x138))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 87) (.exec 0x1096d4 (StorePre 0x1096d4 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x1096d4 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1096d4 4 0 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[85, 4]
    (.letOp (n := 88) (.exec 0x1096d8 (fun s => s.RIP = 0x1096d8) (leaR64Effect 0x1096d8 0 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 89) (.out 0x1096dd (movR64M64Effect 0x1096dd 1 (.sib 4 none 0 (.d32 0x140))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 90) (.exec 0x1096dd (LoadPre 0x1096dd (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x1096dd + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1096dd 1 (.sib 4 none 0 (.d32 0x140))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 91) (.exec 0x1096e5 (StorePre 0x1096e5 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x1096e5 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1096e5 4 1 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[89, 4]
    (.letOp (n := 92) (.out 0x1096e9 (leaR64Effect 0x1096e9 7 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 93) (.exec 0x1096e9 (fun s => s.RIP = 0x1096e9) (leaR64Effect 0x1096e9 7 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 94) (.out 0x1096f1 (leaR64Effect 0x1096f1 6 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 95) (.exec 0x1096f1 (fun s => s.RIP = 0x1096f1) (leaR64Effect 0x1096f1 6 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 96) (.out 0x1096f6 (leaR64Effect 0x1096f6 2 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 97) (.exec 0x1096f6 (fun s => s.RIP = 0x1096f6) (leaR64Effect 0x1096f6 2 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 98) (.out 0x1096fe (movR64R64Effect 0x1096fe 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 3] []) (.reg (.gpr 1))) #v[3]
    (.letOp (n := 99) (.exec 0x1096fe (fun s => s.RIP = 0x1096fe) (movR64R64Effect 0x1096fe 1 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 100) (.out 0x109701 (movR64R64Effect 0x109701 8 15) (EffectPart.reads (.reg (.gpr 8)) [.gpr 15] []) (.reg (.gpr 8))) #v[15]
    (.letOp (n := 101) (.exec 0x109701 (fun s => s.RIP = 0x109701) (movR64R64Effect 0x109701 8 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 102) (.out 0x109704 (movR32R32Effect 0x109704 3 9 5) (EffectPart.reads (.reg (.gpr 9)) [.gpr 5] []) (.reg (.gpr 9))) #v[5]
    (.letOp (n := 103) (.exec 0x109704 (fun s => s.RIP = 0x109704) (movR32R32Effect 0x109704 3 9 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 104) (.out 0x109707 (movR64M64Effect 0x109707 15 (.sib 4 none 0 (.d32 0x128))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 105) (.exec 0x109707 (LoadPre 0x109707 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x109707 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x109707 15 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 106) (.out 0x10970f (pushR64Effect 0x10970f 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[4, 104]
    (.letOp (n := 107) (.exec 0x10970f (PushPre 0x10970f 2) (pushR64Effect 0x10970f 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[4, 104]
    (.letOp (n := 108) (.out 0x109711 (movR64M64Effect 0x109711 3 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[106]
    (.letOp (n := 109) (.exec 0x109711 (LoadPre 0x109711 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x109711 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109711 3 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[106]
    (.letOp (n := 110) (.out 0x109716 (pushR64Effect 0x109716 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[106, 108]
    (.letOp (n := 111) (.exec 0x109716 (PushPre 0x109716 1) (pushR64Effect 0x109716 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[106, 108]
    (.letOp (n := 112) (.out 0x109717 (callEffect (fun _ => 0x108980) 0x10971c) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[110]
    (.letOp (n := 113) (.exec 0x109717 (PushPre 0x109717 5) (callEffect (fun _ => 0x108980) 0x10971c) (Reg.operands [.gpr 4] [])) #v[110]
    (.letOp (n := 114) (.const ⟨64, 0x10971c⟩) #v[]
    (.terminate (.call ⟨.l108980, RegMap.args [(1, 98), (2, 96), (3, 108), (4, 112), (5, 5), (6, 94), (7, 92), (8, 100), (9, 102), (12, 12), (13, 13), (14, 14), (15, 104), (22, 22), (39, 39), (50, 50), (51, 51)] 115⟩ { target := .l10971c, kept := #v[], arity := rfl, guard := some (Fin.last 114) }))))))))))))))))))))))))))))))))

def bytes_l109657_1 : List UInt8 :=
  [0x48, 0x89, 0x44, 0x24, 0x50, 0x48, 0x8B, 0x84, 0x24, 0x38, 0x01, 0x00, 0x00, 0x88, 0x44, 0x24,
    0x07, 0x48, 0x8D, 0x44, 0x24, 0x07, 0x48, 0x8B, 0x8C, 0x24, 0x40, 0x01, 0x00, 0x00, 0x88, 0x4C,
    0x24, 0x07, 0x48, 0x8D, 0xBC, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x74, 0x24, 0x60, 0x48,
    0x8D, 0x94, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x89, 0xD9, 0x4D, 0x89, 0xF8, 0x41, 0x89, 0xE9,
    0x4C, 0x8B, 0xBC, 0x24, 0x28, 0x01, 0x00, 0x00, 0x41, 0x57, 0x48, 0x8B, 0x5C, 0x24, 0x60, 0x53,
    0xE8, 0x64, 0xF2, 0xFF, 0xFF]

theorem code_l109657_1 : ∀ x ∈ codeRange 0x1096c7 bytes_l109657_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x96c7 85 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109657 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x109657 (movR64M64Effect 0x109657 0 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x109657 (LoadPre 0x109657 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x109657 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x109657 0 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x10965f (StorePre 0x10965f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10965f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10965f 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x109664 (movR64M64Effect 0x109664 0 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x109664 (LoadPre 0x109664 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x109664 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x109664 0 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x10966c (StorePre 0x10966c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10966c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10966c 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x109671 (movR64M64Effect 0x109671 0 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x109671 (LoadPre 0x109671 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x109671 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x109671 0 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x109679 (StorePre 0x109679 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x109679 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109679 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x10967e (movR64M64Effect 0x10967e 0 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x10967e (LoadPre 0x10967e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x10967e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10967e 0 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x109686 (movR64M64Effect 0x109686 1 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x109686 (LoadPre 0x109686 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x109686 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x109686 1 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x10968e (StorePre 0x10968e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10968e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10968e 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x109693 (StorePre 0x109693 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109693 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109693 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x109698 (leaR64Effect 0x109698 2 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 69) (.exec 0x109698 (fun s => s.RIP = 0x109698) (leaR64Effect 0x109698 2 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.out 0x1096a0 (movR64M64Effect 0x1096a0 0 (.base 2 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[68]
    (.letOp (n := 71) (.exec 0x1096a0 (LoadPre 0x1096a0 (fun s => AddrMode.addr (.base 2 .none) s (0x1096a0 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1096a0 0 (.base 2 .none)) (Reg.operands [.gpr 2] [])) #v[68]
    (.letOp (n := 72) (.out 0x1096a3 (movR64M64Effect 0x1096a3 1 (.base 2 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[68]
    (.letOp (n := 73) (.exec 0x1096a3 (LoadPre 0x1096a3 (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x1096a3 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1096a3 1 (.base 2 (.d8 0x8))) (Reg.operands [.gpr 2] [])) #v[68]
    (.letOp (n := 74) (.exec 0x1096a7 (StorePre 0x1096a7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1096a7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1096a7 0 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[70, 4]
    (.letOp (n := 75) (.exec 0x1096ac (StorePre 0x1096ac 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1096ac + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1096ac 1 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[72, 4]
    (.letOp (n := 76) (.out 0x1096b1 (movR64M64Effect 0x1096b1 0 (.base 2 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[68]
    (.letOp (n := 77) (.exec 0x1096b1 (LoadPre 0x1096b1 (fun s => AddrMode.addr (.base 2 (.d8 0x10)) s (0x1096b1 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1096b1 0 (.base 2 (.d8 0x10))) (Reg.operands [.gpr 2] [])) #v[68]
    (.letOp (n := 78) (.exec 0x1096b5 (StorePre 0x1096b5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1096b5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1096b5 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[76, 4]
    (.letOp (n := 79) (.out 0x1096ba (movR64M64Effect 0x1096ba 0 (.base 2 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[68]
    (.letOp (n := 80) (.exec 0x1096ba (LoadPre 0x1096ba (fun s => AddrMode.addr (.base 2 (.d8 0x18)) s (0x1096ba + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1096ba 0 (.base 2 (.d8 0x18))) (Reg.operands [.gpr 2] [])) #v[68]
    (.letOp (n := 81) (.exec 0x1096be (StorePre 0x1096be 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1096be + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1096be 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[79, 4]
    (.letOp (n := 82) (.out 0x1096c3 (movR64M64Effect 0x1096c3 0 (.base 2 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[68]
    (.letOp (n := 83) (.exec 0x1096c3 (LoadPre 0x1096c3 (fun s => AddrMode.addr (.base 2 (.d8 0x20)) s (0x1096c3 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1096c3 0 (.base 2 (.d8 0x20))) (Reg.operands [.gpr 2] [])) #v[68]
    (b_l109657_1)))))))))))))))))))))))))))))))

def bytes_l109657 : List UInt8 :=
  [0x48, 0x8B, 0x84, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x28, 0x48, 0x8B, 0x84,
    0x24, 0xC8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x84, 0x24, 0xC0, 0x00,
    0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x48,
    0x8B, 0x8C, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x4C, 0x24, 0x10, 0x48, 0x89, 0x44, 0x24,
    0x08, 0x48, 0x8D, 0x94, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x02, 0x48, 0x8B, 0x4A, 0x08,
    0x48, 0x89, 0x44, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x38, 0x48, 0x8B, 0x42, 0x10, 0x48, 0x89,
    0x44, 0x24, 0x40, 0x48, 0x8B, 0x42, 0x18, 0x48, 0x89, 0x44, 0x24, 0x48, 0x48, 0x8B, 0x42, 0x20] ++ bytes_l109657_1

theorem code_l109657 : ∀ x ∈ codeRange 0x109657 bytes_l109657, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x9657 112 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l109657_1

@[cfg_block] def b_l10971c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10971c (addR64Imm8Effect 0x10971c 4 0x10) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 54) (.exec 0x10971c (fun s => s.RIP = 0x10971c) (addR64Imm8Effect 0x10971c 4 0x10) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x109720 (movR64M64Effect 0x109720 0 (.sib 4 none 0 (.d32 0x148))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x109720 (LoadPre 0x109720 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x148)) s (0x109720 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x109720 0 (.sib 4 none 0 (.d32 0x148))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 57) (.exec 0x109728 (StorePre 0x109728 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x109728 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109728 4 0 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 53]
    (.letOp (n := 58) (.exec 0x10972c (fun s => s.RIP = 0x10972c) (leaR64Effect 0x10972c 1 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 59) (.out 0x109731 (movR64M64Effect 0x109731 0 (.sib 4 none 0 (.d32 0x130))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 60) (.exec 0x109731 (LoadPre 0x109731 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x109731 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x109731 0 (.sib 4 none 0 (.d32 0x130))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 61) (.exec 0x109739 (StorePre 0x109739 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x109739 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109739 4 0 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 53]
    (.letOp (n := 62) (.out 0x10973d (leaR64Effect 0x10973d 7 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 63) (.exec 0x10973d (fun s => s.RIP = 0x10973d) (leaR64Effect 0x10973d 7 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 64) (.out 0x109745 (leaR64Effect 0x109745 6 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[53]
    (.letOp (n := 65) (.exec 0x109745 (fun s => s.RIP = 0x109745) (leaR64Effect 0x109745 6 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 66) (.out 0x10974a (leaR64Effect 0x10974a 2 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[53]
    (.letOp (n := 67) (.exec 0x10974a (fun s => s.RIP = 0x10974a) (leaR64Effect 0x10974a 2 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 68) (.out 0x109752 (movR64R64Effect 0x109752 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 13] []) (.reg (.gpr 1))) #v[13]
    (.letOp (n := 69) (.exec 0x109752 (fun s => s.RIP = 0x109752) (movR64R64Effect 0x109752 1 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 70) (.out 0x109755 (movR64R64Effect 0x109755 8 14) (EffectPart.reads (.reg (.gpr 8)) [.gpr 14] []) (.reg (.gpr 8))) #v[14]
    (.letOp (n := 71) (.exec 0x109755 (fun s => s.RIP = 0x109755) (movR64R64Effect 0x109755 8 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x109758 (movR32R32Effect 0x109758 3 9 5) (EffectPart.reads (.reg (.gpr 9)) [.gpr 5] []) (.reg (.gpr 9))) #v[5]
    (.letOp (n := 73) (.exec 0x109758 (fun s => s.RIP = 0x109758) (movR32R32Effect 0x109758 3 9 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 74) (.out 0x10975b (pushR64Effect 0x10975b 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 75) (.exec 0x10975b (PushPre 0x10975b 2) (pushR64Effect 0x10975b 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 76) (.out 0x10975d (pushR64Effect 0x10975d 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[74, 3]
    (.letOp (n := 77) (.exec 0x10975d (PushPre 0x10975d 1) (pushR64Effect 0x10975d 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[74, 3]
    (.letOp (n := 78) (.out 0x10975e (callEffect (fun _ => 0x108980) 0x109763) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[76]
    (.letOp (n := 79) (.exec 0x10975e (PushPre 0x10975e 5) (callEffect (fun _ => 0x108980) 0x109763) (Reg.operands [.gpr 4] [])) #v[76]
    (.letOp (n := 80) (.const ⟨64, 0x109763⟩) #v[]
    (.terminate (.call ⟨.l108980, RegMap.args [(0, 59), (1, 68), (2, 66), (3, 3), (4, 78), (5, 5), (6, 64), (7, 62), (8, 70), (9, 72), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 81⟩ { target := .l109763, kept := #v[], arity := rfl, guard := some (Fin.last 80) })))))))))))))))))))))))))))))

def bytes_l10971c : List UInt8 :=
  [0x48, 0x83, 0xC4, 0x10, 0x48, 0x8B, 0x84, 0x24, 0x48, 0x01, 0x00, 0x00, 0x88, 0x44, 0x24, 0x07,
    0x48, 0x8D, 0x4C, 0x24, 0x07, 0x48, 0x8B, 0x84, 0x24, 0x30, 0x01, 0x00, 0x00, 0x88, 0x44, 0x24,
    0x07, 0x48, 0x8D, 0xBC, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x74, 0x24, 0x60, 0x48, 0x8D,
    0x94, 0x24, 0x88, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xE9, 0x4D, 0x89, 0xF0, 0x41, 0x89, 0xE9, 0x41,
    0x57, 0x53, 0xE8, 0x1D, 0xF2, 0xFF, 0xFF]

theorem code_l10971c : ∀ x ∈ codeRange 0x10971c bytes_l10971c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x971c 71 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109763_1 : Block Op Label signature Reg.count 84 :=
  .letOp (n := 84) (.out 0x1097e2 (movR64M64Effect 0x1097e2 0 (.base 2 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[70]
    (.letOp (n := 85) (.exec 0x1097e2 (LoadPre 0x1097e2 (fun s => AddrMode.addr (.base 2 (.d8 0x20)) s (0x1097e2 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1097e2 0 (.base 2 (.d8 0x20))) (Reg.operands [.gpr 2] [])) #v[70]
    (.letOp (n := 86) (.exec 0x1097e6 (StorePre 0x1097e6 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x1097e6 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1097e6 0 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[84, 53]
    (.letOp (n := 87) (.out 0x1097ee (movR64M64Effect 0x1097ee 6 (.sib 4 none 0 (.d32 0x150))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[53]
    (.letOp (n := 88) (.exec 0x1097ee (LoadPre 0x1097ee (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x150)) s (0x1097ee + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1097ee 6 (.sib 4 none 0 (.d32 0x150))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 89) (.out 0x1097f6 (subR32R32Effect 0x1097f6 2 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 5] []) (.reg (.gpr 6))) #v[87, 5]
    (.letOp (n := 90) (.out 0x1097f6 (subR32R32Effect 0x1097f6 2 6 5) (EffectPart.reads (.flag .ZF) [.gpr 6, .gpr 5] []) (.flag .ZF)) #v[87, 5]
    (.letOp (n := 91) (.exec 0x1097f6 (fun s => s.RIP = 0x1097f6) (subR32R32Effect 0x1097f6 2 6 5) (Reg.operands [.gpr 6, .gpr 5] [])) #v[87, 5]
    (.letOp (n := 92) (.pure (condOp 4)) #v[90]
    (.terminate (.condBr (Fin.last 92) ⟨.l109948, RegMap.args [(0, 84), (1, 74), (2, 70), (3, 3), (4, 53), (5, 5), (6, 89), (12, 12), (13, 13), (15, 15), (19, 90), (22, 22), (39, 39), (50, 50), (51, 51)] 93⟩ ⟨.l1097fe, RegMap.args [(0, 84), (1, 74), (2, 70), (3, 3), (4, 53), (5, 5), (6, 89), (12, 12), (13, 13), (15, 15), (19, 90), (22, 22), (39, 39), (50, 50), (51, 51)] 93⟩))))))))))

def bytes_l109763_1 : List UInt8 :=
  [0x48, 0x8B, 0x42, 0x20, 0x48, 0x89, 0x84, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x48, 0x8B, 0xB4, 0x24,
    0x50, 0x01, 0x00, 0x00, 0x29, 0xEE, 0x0F, 0x84, 0x4A, 0x01, 0x00, 0x00]

theorem code_l109763_1 : ∀ x ∈ codeRange 0x1097e2 bytes_l109763_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x97e2 28 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109763 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x109763 (addR64Imm8Effect 0x109763 4 0x10) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 54) (.exec 0x109763 (fun s => s.RIP = 0x109763) (addR64Imm8Effect 0x109763 4 0x10) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x109767 (movR64M64Effect 0x109767 0 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x109767 (LoadPre 0x109767 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x109767 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x109767 0 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 57) (.exec 0x10976f (StorePre 0x10976f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10976f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10976f 0 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 53]
    (.letOp (n := 58) (.out 0x109777 (movR64M64Effect 0x109777 0 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 59) (.exec 0x109777 (LoadPre 0x109777 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x109777 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x109777 0 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 60) (.exec 0x10977f (StorePre 0x10977f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10977f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10977f 0 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[58, 53]
    (.letOp (n := 61) (.out 0x109784 (movR64M64Effect 0x109784 0 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 62) (.exec 0x109784 (LoadPre 0x109784 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x109784 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x109784 0 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 63) (.exec 0x10978c (StorePre 0x10978c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x10978c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10978c 0 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[61, 53]
    (.letOp (n := 64) (.out 0x109791 (movR64M64Effect 0x109791 0 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 65) (.exec 0x109791 (LoadPre 0x109791 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x109791 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x109791 0 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 66) (.out 0x109799 (movR64M64Effect 0x109799 1 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 67) (.exec 0x109799 (LoadPre 0x109799 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x109799 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x109799 1 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 68) (.exec 0x1097a1 (StorePre 0x1097a1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x1097a1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1097a1 1 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[66, 53]
    (.letOp (n := 69) (.exec 0x1097a6 (StorePre 0x1097a6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1097a6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1097a6 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[64, 53]
    (.letOp (n := 70) (.out 0x1097ab (leaR64Effect 0x1097ab 2 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[53]
    (.letOp (n := 71) (.exec 0x1097ab (fun s => s.RIP = 0x1097ab) (leaR64Effect 0x1097ab 2 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 72) (.out 0x1097b3 (movR64M64Effect 0x1097b3 0 (.base 2 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[70]
    (.letOp (n := 73) (.exec 0x1097b3 (LoadPre 0x1097b3 (fun s => AddrMode.addr (.base 2 .none) s (0x1097b3 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1097b3 0 (.base 2 .none)) (Reg.operands [.gpr 2] [])) #v[70]
    (.letOp (n := 74) (.out 0x1097b6 (movR64M64Effect 0x1097b6 1 (.base 2 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[70]
    (.letOp (n := 75) (.exec 0x1097b6 (LoadPre 0x1097b6 (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x1097b6 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1097b6 1 (.base 2 (.d8 0x8))) (Reg.operands [.gpr 2] [])) #v[70]
    (.letOp (n := 76) (.exec 0x1097ba (StorePre 0x1097ba 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1097ba + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1097ba 0 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[72, 53]
    (.letOp (n := 77) (.exec 0x1097c2 (StorePre 0x1097c2 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x1097c2 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1097c2 1 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[74, 53]
    (.letOp (n := 78) (.out 0x1097ca (movR64M64Effect 0x1097ca 0 (.base 2 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[70]
    (.letOp (n := 79) (.exec 0x1097ca (LoadPre 0x1097ca (fun s => AddrMode.addr (.base 2 (.d8 0x10)) s (0x1097ca + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1097ca 0 (.base 2 (.d8 0x10))) (Reg.operands [.gpr 2] [])) #v[70]
    (.letOp (n := 80) (.exec 0x1097ce (StorePre 0x1097ce 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x1097ce + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1097ce 0 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[78, 53]
    (.letOp (n := 81) (.out 0x1097d6 (movR64M64Effect 0x1097d6 0 (.base 2 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[70]
    (.letOp (n := 82) (.exec 0x1097d6 (LoadPre 0x1097d6 (fun s => AddrMode.addr (.base 2 (.d8 0x18)) s (0x1097d6 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1097d6 0 (.base 2 (.d8 0x18))) (Reg.operands [.gpr 2] [])) #v[70]
    (.letOp (n := 83) (.exec 0x1097da (StorePre 0x1097da 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x1097da + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1097da 0 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[81, 53]
    (b_l109763_1)))))))))))))))))))))))))))))))

def bytes_l109763 : List UInt8 :=
  [0x48, 0x83, 0xC4, 0x10, 0x48, 0x8B, 0x84, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24,
    0x80, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24,
    0x78, 0x48, 0x8B, 0x84, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x70, 0x48, 0x8B,
    0x84, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x8C, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x48, 0x89,
    0x4C, 0x24, 0x68, 0x48, 0x89, 0x44, 0x24, 0x60, 0x48, 0x8D, 0x94, 0x24, 0xD8, 0x00, 0x00, 0x00,
    0x48, 0x8B, 0x02, 0x48, 0x8B, 0x4A, 0x08, 0x48, 0x89, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48,
    0x89, 0x8C, 0x24, 0x90, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x42, 0x10, 0x48, 0x89, 0x84, 0x24, 0x98,
    0x00, 0x00, 0x00, 0x48, 0x8B, 0x42, 0x18, 0x48, 0x89, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00] ++ bytes_l109763_1

theorem code_l109763 : ∀ x ∈ codeRange 0x109763 bytes_l109763, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x9763 127 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l109763_1

@[cfg_block] def b_l1097fe : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1097fe (movR64M64Effect 0x1097fe 2 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 54) (.exec 0x1097fe (LoadPre 0x1097fe (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1097fe + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1097fe 2 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x109803 (testR64R64Effect 0x109803 2 2) (EffectPart.reads (.flag .ZF) [.gpr 2, .gpr 2] []) (.flag .ZF)) #v[53, 53]
    (.letOp (n := 56) (.exec 0x109803 (fun s => s.RIP = 0x109803) (testR64R64Effect 0x109803 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[53, 53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l109824, RegMap.args [(2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (12, 12), (13, 13), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l109808, RegMap.args [(2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (12, 12), (13, 13), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l1097fe : List UInt8 :=
  [0x48, 0x8B, 0x54, 0x24, 0x30, 0x48, 0x85, 0xD2, 0x75, 0x1C]

theorem code_l1097fe : ∀ x ∈ codeRange 0x1097fe bytes_l1097fe, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x97fe 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109808 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x109808 (cmpMImm8Effect 0x109808 6 64 (.sib 4 none 0 (.d8 0x38)) 0x0) (EffectPart.reads (.flag .ZF) [.gpr 4] []) (.flag .ZF)) #v[4]
    (.letOp (n := 54) (.exec 0x109808 (LoadPre 0x109808 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x109808 + BitVec.ofNat 64 6)) 8) (cmpMImm8Effect 0x109808 6 64 (.sib 4 none 0 (.d8 0x38)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l109824, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (12, 12), (13, 13), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l109810, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (12, 12), (13, 13), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l109808 : List UInt8 :=
  [0x48, 0x83, 0x7C, 0x24, 0x38, 0x00, 0x75, 0x14]

theorem code_l109808 : ∀ x ∈ codeRange 0x109808 bytes_l109808, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9808 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109810 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x109810 (cmpMImm8Effect 0x109810 6 64 (.sib 4 none 0 (.d8 0x40)) 0x0) (EffectPart.reads (.flag .ZF) [.gpr 4] []) (.flag .ZF)) #v[4]
    (.letOp (n := 54) (.exec 0x109810 (LoadPre 0x109810 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x109810 + BitVec.ofNat 64 6)) 8) (cmpMImm8Effect 0x109810 6 64 (.sib 4 none 0 (.d8 0x40)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l109824, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (12, 12), (13, 13), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l109818, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (12, 12), (13, 13), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l109810 : List UInt8 :=
  [0x48, 0x83, 0x7C, 0x24, 0x40, 0x00, 0x75, 0x0C]

theorem code_l109810 : ∀ x ∈ codeRange 0x109810 bytes_l109810, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9810 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109818 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x109818 (cmpMImm8Effect 0x109818 6 64 (.sib 4 none 0 (.d8 0x48)) 0x0) (EffectPart.reads (.flag .ZF) [.gpr 4] []) (.flag .ZF)) #v[4]
    (.letOp (n := 54) (.exec 0x109818 (LoadPre 0x109818 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x109818 + BitVec.ofNat 64 6)) 8) (cmpMImm8Effect 0x109818 6 64 (.sib 4 none 0 (.d8 0x48)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l109948, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (12, 12), (13, 13), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l109824, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (12, 12), (13, 13), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l109818 : List UInt8 :=
  [0x48, 0x83, 0x7C, 0x24, 0x48, 0x00, 0x0F, 0x84, 0x24, 0x01, 0x00, 0x00]

theorem code_l109818 : ∀ x ∈ codeRange 0x109818 bytes_l109818, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9818 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109824_1 : Block Op Label signature Reg.count 89 :=
  .letOp (n := 89) (.pure (condOp 4)) #v[77]
    (.terminate (.condBr (Fin.last 89) ⟨.l1095b0, RegMap.args [(0, 84), (1, 86), (2, 2), (4, 4), (6, 79), (9, 76), (12, 12), (13, 13), (15, 15), (19, 77), (22, 22), (39, 39), (50, 50), (51, 51)] 90⟩ ⟨.l10988a, RegMap.args [(0, 84), (1, 86), (2, 2), (4, 4), (6, 79), (9, 76), (12, 12), (13, 13), (15, 15), (19, 77), (22, 22), (39, 39), (50, 50), (51, 51)] 90⟩))

def bytes_l109824_1 : List UInt8 :=
  [0x0F, 0x84, 0x26, 0xFD, 0xFF, 0xFF]

theorem code_l109824_1 : ∀ x ∈ codeRange 0x109884 bytes_l109824_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9884 6 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109824 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x109824 (movR32R32Effect 0x109824 2 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 54) (.exec 0x109824 (fun s => s.RIP = 0x109824) (movR32R32Effect 0x109824 2 0 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 55) (.out 0x109826 (notR32Effect 0x109826 2 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x109826 (fun s => s.RIP = 0x109826) (notR32Effect 0x109826 2 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x109828 (leaR32Effect 0x109828 3 1 (.base 6 (.d8 0xc2))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[6]
    (.letOp (n := 58) (.exec 0x109828 (fun s => s.RIP = 0x109828) (leaR32Effect 0x109828 3 1 (.base 6 (.d8 0xc2))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 59) (.out 0x10982b (andR32R32Effect 0x10982b 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[57, 55]
    (.letOp (n := 60) (.exec 0x10982b (fun s => s.RIP = 0x10982b) (andR32R32Effect 0x10982b 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[57, 55]
    (.letOp (n := 61) (.out 0x10982d (shrR32Effect 0x10982d 3 1 31) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[59]
    (.letOp (n := 62) (.exec 0x10982d (fun s => s.RIP = 0x10982d) (shrR32Effect 0x10982d 3 1 31) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[59]
    (.letOp (n := 63) (.exec 0x109830 (StorePre 0x109830 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x109830 + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x109830 7 1 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.exec 0x109837 (fun s => s.RIP = 0x109837) (leaR64Effect 0x109837 7 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x10983f (movzxR32M8Effect 0x10983f 8 0 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 66) (.exec 0x10983f (LoadPre 0x10983f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x10983f + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x10983f 8 0 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x109847 (negR32Effect 0x109847 2 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 68) (.exec 0x109847 (fun s => s.RIP = 0x109847) (negR32Effect 0x109847 2 0) (Reg.operands [.gpr 0] [])) #v[65]
    (.letOp (n := 69) (.exec 0x109849 (StorePre 0x109849 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x150)) s (0x109849 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x109849 6 (.sib 4 none 0 (.d32 0x150))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[6, 4]
    (.letOp (n := 70) (.out 0x109851 (movR32R32Effect 0x109851 3 9 6) (EffectPart.reads (.reg (.gpr 9)) [.gpr 6] []) (.reg (.gpr 9))) #v[6]
    (.letOp (n := 71) (.exec 0x109851 (fun s => s.RIP = 0x109851) (movR32R32Effect 0x109851 3 9 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 72) (.out 0x109854 (xorR32Imm8Effect 0x109854 4 9 0x3e) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[70]
    (.letOp (n := 73) (.exec 0x109854 (fun s => s.RIP = 0x109854) (xorR32Imm8Effect 0x109854 4 9 0x3e) (Reg.operands [.gpr 9] [])) #v[70]
    (.letOp (n := 74) (.out 0x109858 (andR32R32Effect 0x109858 3 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0] []) (.reg (.gpr 9))) #v[72, 67]
    (.letOp (n := 75) (.exec 0x109858 (fun s => s.RIP = 0x109858) (andR32R32Effect 0x109858 3 9 0) (Reg.operands [.gpr 9, .gpr 0] [])) #v[72, 67]
    (.letOp (n := 76) (.out 0x10985b (xorR32Imm8Effect 0x10985b 4 9 0x3e) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[74]
    (.letOp (n := 77) (.out 0x10985b (xorR32Imm8Effect 0x10985b 4 9 0x3e) (EffectPart.reads (.flag .ZF) [.gpr 9] []) (.flag .ZF)) #v[74]
    (.letOp (n := 78) (.exec 0x10985b (fun s => s.RIP = 0x10985b) (xorR32Imm8Effect 0x10985b 4 9 0x3e) (Reg.operands [.gpr 9] [])) #v[74]
    (.letOp (n := 79) (.out 0x10985f (movR64M64Effect 0x10985f 6 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 80) (.exec 0x10985f (LoadPre 0x10985f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10985f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10985f 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 81) (.out 0x109864 (movzxR32M8Effect 0x109864 5 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 82) (.exec 0x109864 (LoadPre 0x109864 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x109864 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109864 5 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 83) (.exec 0x109869 (StorePre 0x109869 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x109869 + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x109869 7 0 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[81, 4]
    (.letOp (n := 84) (.out 0x109870 (movzxR32M8Effect 0x109870 8 0 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 85) (.exec 0x109870 (LoadPre 0x109870 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x109870 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x109870 8 0 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 86) (.out 0x109878 (movzxR32M8Effect 0x109878 5 1 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 87) (.exec 0x109878 (LoadPre 0x109878 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x109878 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109878 5 1 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 88) (.exec 0x10987d (StorePre 0x10987d 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x10987d + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x10987d 7 1 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[86, 4]
    (b_l109824_1))))))))))))))))))))))))))))))))))))

def bytes_l109824 : List UInt8 :=
  [0x89, 0xF0, 0xF7, 0xD0, 0x8D, 0x4E, 0xC2, 0x21, 0xC1, 0xC1, 0xE9, 0x1F, 0x88, 0x8C, 0x24, 0xB0,
    0x00, 0x00, 0x00, 0x48, 0x8D, 0xBC, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x0F, 0xB6, 0x84, 0x24, 0xB0,
    0x00, 0x00, 0x00, 0xF7, 0xD8, 0x48, 0x89, 0xB4, 0x24, 0x50, 0x01, 0x00, 0x00, 0x41, 0x89, 0xF1,
    0x41, 0x83, 0xF1, 0x3E, 0x41, 0x21, 0xC1, 0x41, 0x83, 0xF1, 0x3E, 0x48, 0x8B, 0x74, 0x24, 0x08,
    0x0F, 0xB6, 0x44, 0x24, 0x28, 0x88, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x0F, 0xB6, 0x84, 0x24,
    0xB0, 0x00, 0x00, 0x00, 0x0F, 0xB6, 0x4C, 0x24, 0x50, 0x88, 0x8C, 0x24, 0xB0, 0x00, 0x00, 0x00] ++ bytes_l109824_1

theorem code_l109824 : ∀ x ∈ codeRange 0x109824 bytes_l109824, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x9824 96 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l109824_1

@[cfg_block] def b_l10988a_1 : Block Op Label signature Reg.count 93 :=
  .letOp (n := 93) (.out 0x1098d3 (movR32Imm32Effect 0x1098d3 5 7 0x1) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 94) (.exec 0x1098d3 (fun s => s.RIP = 0x1098d3) (movR32Imm32Effect 0x1098d3 5 7 0x1) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l109925, RegMap.args [(0, 83), (1, 69), (2, 87), (3, 85), (4, 4), (6, 91), (7, 93), (8, 55), (9, 9), (12, 12), (15, 89), (22, 22), (39, 39), (50, 50), (51, 51)] 95⟩)))

def bytes_l10988a_1 : List UInt8 :=
  [0xBF, 0x01, 0x00, 0x00, 0x00, 0xEB, 0x4B]

theorem code_l10988a_1 : ∀ x ∈ codeRange 0x1098d3 bytes_l10988a_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x98d3 7 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10988a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10988a (movzxR32M8Effect 0x10988a 8 1 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x10988a (LoadPre 0x10988a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x10988a + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x10988a 8 1 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x109892 (movR64Imm64Effect 0x109892 8 0x7fffffffffffffff) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 56) (.exec 0x109892 (fun s => s.RIP = 0x109892) (movR64Imm64Effect 0x109892 8 0x7fffffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x10989c (andR64R64Effect 0x10989c 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 8] []) (.reg (.gpr 2))) #v[2, 55]
    (.letOp (n := 58) (.exec 0x10989c (fun s => s.RIP = 0x10989c) (andR64R64Effect 0x10989c 2 8) (Reg.operands [.gpr 2, .gpr 8] [])) #v[2, 55]
    (.letOp (n := 59) (.out 0x10989f (movR64R64Effect 0x10989f 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[57]
    (.letOp (n := 60) (.exec 0x10989f (fun s => s.RIP = 0x10989f) (movR64R64Effect 0x10989f 7 2) (Reg.operands [.gpr 2] [])) #v[57]
    (.letOp (n := 61) (.out 0x1098a2 (negR64Effect 0x1098a2 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[59]
    (.letOp (n := 62) (.exec 0x1098a2 (fun s => s.RIP = 0x1098a2) (negR64Effect 0x1098a2 7) (Reg.operands [.gpr 7] [])) #v[59]
    (.letOp (n := 63) (.out 0x1098a5 (xorR64R64Effect 0x1098a5 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2] []) (.reg (.gpr 7))) #v[61, 57]
    (.letOp (n := 64) (.exec 0x1098a5 (fun s => s.RIP = 0x1098a5) (xorR64R64Effect 0x1098a5 7 2) (Reg.operands [.gpr 7, .gpr 2] [])) #v[61, 57]
    (.letOp (n := 65) (.out 0x1098a8 (negR64Effect 0x1098a8 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 66) (.exec 0x1098a8 (fun s => s.RIP = 0x1098a8) (negR64Effect 0x1098a8 1) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 67) (.out 0x1098ab (andR64R64Effect 0x1098ab 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[65, 63]
    (.letOp (n := 68) (.exec 0x1098ab (fun s => s.RIP = 0x1098ab) (andR64R64Effect 0x1098ab 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[65, 63]
    (.letOp (n := 69) (.out 0x1098ae (xorR64R64Effect 0x1098ae 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[67, 57]
    (.letOp (n := 70) (.exec 0x1098ae (fun s => s.RIP = 0x1098ae) (xorR64R64Effect 0x1098ae 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[67, 57]
    (.letOp (n := 71) (.out 0x1098b1 (andR64R64Effect 0x1098b1 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 8] []) (.reg (.gpr 6))) #v[6, 55]
    (.letOp (n := 72) (.exec 0x1098b1 (fun s => s.RIP = 0x1098b1) (andR64R64Effect 0x1098b1 6 8) (Reg.operands [.gpr 6, .gpr 8] [])) #v[6, 55]
    (.letOp (n := 73) (.out 0x1098b4 (movR64R64Effect 0x1098b4 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6] []) (.reg (.gpr 2))) #v[71]
    (.letOp (n := 74) (.exec 0x1098b4 (fun s => s.RIP = 0x1098b4) (movR64R64Effect 0x1098b4 2 6) (Reg.operands [.gpr 6] [])) #v[71]
    (.letOp (n := 75) (.out 0x1098b7 (negR64Effect 0x1098b7 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[73]
    (.letOp (n := 76) (.exec 0x1098b7 (fun s => s.RIP = 0x1098b7) (negR64Effect 0x1098b7 2) (Reg.operands [.gpr 2] [])) #v[73]
    (.letOp (n := 77) (.out 0x1098ba (xorR64R64Effect 0x1098ba 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[75, 71]
    (.letOp (n := 78) (.exec 0x1098ba (fun s => s.RIP = 0x1098ba) (xorR64R64Effect 0x1098ba 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[75, 71]
    (.letOp (n := 79) (.out 0x1098bd (negR64Effect 0x1098bd 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 80) (.exec 0x1098bd (fun s => s.RIP = 0x1098bd) (negR64Effect 0x1098bd 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 81) (.out 0x1098c0 (andR64R64Effect 0x1098c0 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[79, 77]
    (.letOp (n := 82) (.exec 0x1098c0 (fun s => s.RIP = 0x1098c0) (andR64R64Effect 0x1098c0 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[79, 77]
    (.letOp (n := 83) (.out 0x1098c3 (xorR64R64Effect 0x1098c3 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[81, 71]
    (.letOp (n := 84) (.exec 0x1098c3 (fun s => s.RIP = 0x1098c3) (xorR64R64Effect 0x1098c3 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[81, 71]
    (.letOp (n := 85) (.out 0x1098c6 (movR32Imm32Effect 0x1098c6 5 3 0x1) (EffectPart.reads (.reg (.gpr 3)) [] []) (.reg (.gpr 3))) #v[]
    (.letOp (n := 86) (.exec 0x1098c6 (fun s => s.RIP = 0x1098c6) (movR32Imm32Effect 0x1098c6 5 3 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 87) (.out 0x1098cb (movR32R32Effect 0x1098cb 3 2 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9] []) (.reg (.gpr 2))) #v[9]
    (.letOp (n := 88) (.exec 0x1098cb (fun s => s.RIP = 0x1098cb) (movR32R32Effect 0x1098cb 3 2 9) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 89) (.out 0x1098ce (xorR32R32Effect 0x1098ce 3 15 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 15] []) (.reg (.gpr 15))) #v[15, 15]
    (.letOp (n := 90) (.exec 0x1098ce (fun s => s.RIP = 0x1098ce) (xorR32R32Effect 0x1098ce 3 15 15) (Reg.operands [.gpr 15, .gpr 15] [])) #v[15, 15]
    (.letOp (n := 91) (.out 0x1098d1 (xorR32R32Effect 0x1098d1 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[71, 71]
    (.letOp (n := 92) (.exec 0x1098d1 (fun s => s.RIP = 0x1098d1) (xorR32R32Effect 0x1098d1 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[71, 71]
    (b_l10988a_1))))))))))))))))))))))))))))))))))))))))

def bytes_l10988a : List UInt8 :=
  [0x0F, 0xB6, 0x8C, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x49, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0x7F, 0x4C, 0x21, 0xC2, 0x48, 0x89, 0xD7, 0x48, 0xF7, 0xDF, 0x48, 0x31, 0xD7, 0x48, 0xF7,
    0xD9, 0x48, 0x21, 0xF9, 0x48, 0x31, 0xD1, 0x4C, 0x21, 0xC6, 0x48, 0x89, 0xF2, 0x48, 0xF7, 0xDA,
    0x48, 0x31, 0xF2, 0x48, 0xF7, 0xD8, 0x48, 0x21, 0xD0, 0x48, 0x31, 0xF0, 0xBB, 0x01, 0x00, 0x00,
    0x00, 0x44, 0x89, 0xCA, 0x45, 0x31, 0xFF, 0x31, 0xF6] ++ bytes_l10988a_1

theorem code_l10988a : ∀ x ∈ codeRange 0x10988a bytes_l10988a, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x988a 73 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10988a_1

@[cfg_block] def b_l1098e0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1098e0 (testR64R64Effect 0x1098e0 12 12) (EffectPart.reads (.flag .ZF) [.gpr 12, .gpr 12] []) (.flag .ZF)) #v[12, 12]
    (.letOp (n := 54) (.out 0x1098e0 (testR64R64Effect 0x1098e0 12 12) (EffectPart.reads (.flag .SF) [.gpr 12, .gpr 12] []) (.flag .SF)) #v[12, 12]
    (.letOp (n := 55) (.out 0x1098e0 (testR64R64Effect 0x1098e0 12 12) (EffectPart.reads (.flag .OF) [.gpr 12, .gpr 12] []) (.flag .OF)) #v[12, 12]
    (.letOp (n := 56) (.exec 0x1098e0 (fun s => s.RIP = 0x1098e0) (testR64R64Effect 0x1098e0 12 12) (Reg.operands [.gpr 12, .gpr 12] [])) #v[12, 12]
    (.letOp (n := 57) (.pure (condOp 14)) #v[53, 54, 55]
    (.terminate (.condBr (Fin.last 57) ⟨.l109930, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (12, 12), (15, 15), (19, 53), (20, 54), (21, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l1098e5, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (12, 12), (15, 15), (19, 53), (20, 54), (21, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l1098e0 : List UInt8 :=
  [0x4D, 0x85, 0xE4, 0x7E, 0x4B]

theorem code_l1098e0 : ∀ x ∈ codeRange 0x1098e0 bytes_l1098e0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x98e0 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1098e5 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1098e5 (movR64R64Effect 0x1098e5 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 1] []) (.reg (.gpr 8))) #v[1]
    (.letOp (n := 54) (.exec 0x1098e5 (fun s => s.RIP = 0x1098e5) (movR64R64Effect 0x1098e5 8 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 55) (.out 0x1098e8 (subR64R64Effect 0x1098e8 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[53, 0]
    (.letOp (n := 56) (.exec 0x1098e8 (fun s => s.RIP = 0x1098e8) (subR64R64Effect 0x1098e8 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[53, 0]
    (.letOp (n := 57) (.out 0x1098eb (movR32Imm32Effect 0x1098eb 5 0 0x2) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 58) (.exec 0x1098eb (fun s => s.RIP = 0x1098eb) (movR32Imm32Effect 0x1098eb 5 0 0x2) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x1098f0 (subR64R64Effect 0x1098f0 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 12] []) (.reg (.gpr 0))) #v[57, 12]
    (.letOp (n := 60) (.exec 0x1098f0 (fun s => s.RIP = 0x1098f0) (subR64R64Effect 0x1098f0 0 12) (Reg.operands [.gpr 0, .gpr 12] [])) #v[57, 12]
    (.letOp (n := 61) (.out 0x1098f3 (movR64R64Effect 0x1098f3 13 6) (EffectPart.reads (.reg (.gpr 13)) [.gpr 6] []) (.reg (.gpr 13))) #v[6]
    (.letOp (n := 62) (.exec 0x1098f3 (fun s => s.RIP = 0x1098f3) (movR64R64Effect 0x1098f3 13 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 63) (.out 0x1098f6 (subR64R64Effect 0x1098f6 13 3) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 3] []) (.reg (.gpr 13))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x1098f6 (fun s => s.RIP = 0x1098f6) (subR64R64Effect 0x1098f6 13 3) (Reg.operands [.gpr 13, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x1098f9 (movR64R64Effect 0x1098f9 14 7) (EffectPart.reads (.reg (.gpr 14)) [.gpr 7] []) (.reg (.gpr 14))) #v[7]
    (.letOp (n := 66) (.exec 0x1098f9 (fun s => s.RIP = 0x1098f9) (movR64R64Effect 0x1098f9 14 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 67) (.out 0x1098fc (subR64R64Effect 0x1098fc 14 15) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 15] []) (.reg (.gpr 14))) #v[65, 15]
    (.letOp (n := 68) (.exec 0x1098fc (fun s => s.RIP = 0x1098fc) (subR64R64Effect 0x1098fc 14 15) (Reg.operands [.gpr 14, .gpr 15] [])) #v[65, 15]
    (.letOp (n := 69) (.out 0x1098ff (movR64R64Effect 0x1098ff 15 7) (EffectPart.reads (.reg (.gpr 15)) [.gpr 7] []) (.reg (.gpr 15))) #v[7]
    (.letOp (n := 70) (.exec 0x1098ff (fun s => s.RIP = 0x1098ff) (movR64R64Effect 0x1098ff 15 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 71) (.out 0x109902 (movR64R64Effect 0x109902 3 6) (EffectPart.reads (.reg (.gpr 3)) [.gpr 6] []) (.reg (.gpr 3))) #v[6]
    (.letOp (n := 72) (.exec 0x109902 (fun s => s.RIP = 0x109902) (movR64R64Effect 0x109902 3 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 73) (.out 0x109905 (movR64R64Effect 0x109905 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[59]
    (.letOp (n := 74) (.exec 0x109905 (fun s => s.RIP = 0x109905) (movR64R64Effect 0x109905 12 0) (Reg.operands [.gpr 0] [])) #v[59]
    (.letOp (n := 75) (.out 0x109908 (movR64R64Effect 0x109908 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[1]
    (.letOp (n := 76) (.exec 0x109908 (fun s => s.RIP = 0x109908) (movR64R64Effect 0x109908 0 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.terminate (.br ⟨.l10990b, RegMap.args [(0, 75), (1, 1), (2, 2), (3, 71), (4, 4), (6, 6), (7, 7), (8, 55), (9, 9), (12, 73), (13, 63), (14, 67), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 77⟩)))))))))))))))))))))))))

def bytes_l1098e5 : List UInt8 :=
  [0x49, 0x89, 0xC8, 0x49, 0x29, 0xC0, 0xB8, 0x02, 0x00, 0x00, 0x00, 0x4C, 0x29, 0xE0, 0x49, 0x89,
    0xF5, 0x49, 0x29, 0xDD, 0x49, 0x89, 0xFE, 0x4D, 0x29, 0xFE, 0x49, 0x89, 0xFF, 0x48, 0x89, 0xF3,
    0x49, 0x89, 0xC4, 0x48, 0x89, 0xC8]

theorem code_l1098e5 : ∀ x ∈ codeRange 0x1098e5 bytes_l1098e5, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x98e5 38 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10990b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10990b (sarR64Effect 0x10990b 3 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[8]
    (.letOp (n := 54) (.exec 0x10990b (fun s => s.RIP = 0x10990b) (sarR64Effect 0x10990b 3 8 1) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[8]
    (.letOp (n := 55) (.out 0x10990e (addR64R64Effect 0x10990e 3 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 3] []) (.reg (.gpr 3))) #v[3, 3]
    (.letOp (n := 56) (.exec 0x10990e (fun s => s.RIP = 0x10990e) (addR64R64Effect 0x10990e 3 3) (Reg.operands [.gpr 3, .gpr 3] [])) #v[3, 3]
    (.letOp (n := 57) (.out 0x109911 (addR64R64Effect 0x109911 15 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 15] []) (.reg (.gpr 15))) #v[15, 15]
    (.letOp (n := 58) (.exec 0x109911 (fun s => s.RIP = 0x109911) (addR64R64Effect 0x109911 15 15) (Reg.operands [.gpr 15, .gpr 15] [])) #v[15, 15]
    (.letOp (n := 59) (.out 0x109914 (movR64R64Effect 0x109914 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 8] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 60) (.exec 0x109914 (fun s => s.RIP = 0x109914) (movR64R64Effect 0x109914 1 8) (Reg.operands [.gpr 8] [])) #v[53]
    (.letOp (n := 61) (.out 0x109917 (movR64R64Effect 0x109917 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 13] []) (.reg (.gpr 6))) #v[13]
    (.letOp (n := 62) (.exec 0x109917 (fun s => s.RIP = 0x109917) (movR64R64Effect 0x109917 6 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 63) (.out 0x10991a (movR64R64Effect 0x10991a 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 64) (.exec 0x10991a (fun s => s.RIP = 0x10991a) (movR64R64Effect 0x10991a 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 65) (.out 0x10991d (decR32Effect 0x10991d 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[2]
    (.letOp (n := 66) (.out 0x10991d (decR32Effect 0x10991d 2 2) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.flag .ZF)) #v[2]
    (.letOp (n := 67) (.exec 0x10991d (fun s => s.RIP = 0x10991d) (decR32Effect 0x10991d 2 2) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2]
    (.letOp (n := 68) (.pure (condOp 4)) #v[66]
    (.terminate (.condBr (Fin.last 68) ⟨.l1095c1, RegMap.args [(0, 0), (1, 59), (2, 65), (3, 55), (4, 4), (6, 61), (7, 63), (8, 53), (9, 9), (12, 12), (13, 13), (14, 14), (15, 57), (19, 66), (22, 22), (39, 39), (50, 50), (51, 51)] 69⟩ ⟨.l109925, RegMap.args [(0, 0), (1, 59), (2, 65), (3, 55), (4, 4), (6, 61), (7, 63), (8, 53), (9, 9), (12, 12), (13, 13), (14, 14), (15, 57), (19, 66), (22, 22), (39, 39), (50, 50), (51, 51)] 69⟩)))))))))))))))))

def bytes_l10990b : List UInt8 :=
  [0x49, 0xD1, 0xF8, 0x48, 0x01, 0xDB, 0x4D, 0x01, 0xFF, 0x4C, 0x89, 0xC1, 0x4C, 0x89, 0xEE, 0x4C,
    0x89, 0xF7, 0xFF, 0xCA, 0x0F, 0x84, 0x9C, 0xFC, 0xFF, 0xFF]

theorem code_l10990b : ∀ x ∈ codeRange 0x10990b bytes_l10990b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x990b 26 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109925 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x109925 (testR8Imm8LowEffect 0x109925 1 0x1) (EffectPart.reads (.flag .ZF) [.gpr 1] []) (.flag .ZF)) #v[1]
    (.letOp (n := 54) (.exec 0x109925 (fun s => s.RIP = 0x109925) (testR8Imm8LowEffect 0x109925 1 0x1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l1098e0, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (12, 12), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l10992a, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (12, 12), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l109925 : List UInt8 :=
  [0xF6, 0xC1, 0x01, 0x75, 0xB6]

theorem code_l109925 : ∀ x ∈ codeRange 0x109925 bytes_l109925, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9925 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10992a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10992a (addR64Imm8Effect 0x10992a 12 0x2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[12]
    (.letOp (n := 54) (.exec 0x10992a (fun s => s.RIP = 0x10992a) (addR64Imm8Effect 0x10992a 12 0x2) (Reg.operands [.gpr 12] [])) #v[12]
    (.terminate (.br ⟨.l10993d, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (12, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l10992a : List UInt8 :=
  [0x49, 0x83, 0xC4, 0x02, 0xEB, 0x0D]

theorem code_l10992a : ∀ x ∈ codeRange 0x10992a bytes_l10992a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x992a 6 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109930 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x109930 (addR64R64Effect 0x109930 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1, 0]
    (.letOp (n := 54) (.exec 0x109930 (fun s => s.RIP = 0x109930) (addR64R64Effect 0x109930 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1, 0]
    (.letOp (n := 55) (.out 0x109933 (addR64Imm8Effect 0x109933 12 0x2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[12]
    (.letOp (n := 56) (.exec 0x109933 (fun s => s.RIP = 0x109933) (addR64Imm8Effect 0x109933 12 0x2) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 57) (.out 0x109937 (addR64R64Effect 0x109937 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 3] []) (.reg (.gpr 6))) #v[6, 3]
    (.letOp (n := 58) (.exec 0x109937 (fun s => s.RIP = 0x109937) (addR64R64Effect 0x109937 6 3) (Reg.operands [.gpr 6, .gpr 3] [])) #v[6, 3]
    (.letOp (n := 59) (.out 0x10993a (addR64R64Effect 0x10993a 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 15] []) (.reg (.gpr 7))) #v[7, 15]
    (.letOp (n := 60) (.exec 0x10993a (fun s => s.RIP = 0x10993a) (addR64R64Effect 0x10993a 7 15) (Reg.operands [.gpr 7, .gpr 15] [])) #v[7, 15]
    (.terminate (.br ⟨.l10993d, RegMap.args [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 59), (9, 9), (12, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩)))))))))

def bytes_l109930 : List UInt8 :=
  [0x48, 0x01, 0xC1, 0x49, 0x83, 0xC4, 0x02, 0x48, 0x01, 0xDE, 0x4C, 0x01, 0xFF]

theorem code_l109930 : ∀ x ∈ codeRange 0x109930 bytes_l109930, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9930 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10993d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10993d (movR64R64Effect 0x10993d 14 7) (EffectPart.reads (.reg (.gpr 14)) [.gpr 7] []) (.reg (.gpr 14))) #v[7]
    (.letOp (n := 54) (.exec 0x10993d (fun s => s.RIP = 0x10993d) (movR64R64Effect 0x10993d 14 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 55) (.out 0x109940 (movR64R64Effect 0x109940 13 6) (EffectPart.reads (.reg (.gpr 13)) [.gpr 6] []) (.reg (.gpr 13))) #v[6]
    (.letOp (n := 56) (.exec 0x109940 (fun s => s.RIP = 0x109940) (movR64R64Effect 0x109940 13 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 57) (.out 0x109943 (movR64R64Effect 0x109943 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 1] []) (.reg (.gpr 8))) #v[1]
    (.letOp (n := 58) (.exec 0x109943 (fun s => s.RIP = 0x109943) (movR64R64Effect 0x109943 8 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.terminate (.br ⟨.l10990b, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 57), (9, 9), (12, 12), (13, 55), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l10993d : List UInt8 :=
  [0x49, 0x89, 0xFE, 0x49, 0x89, 0xF5, 0x49, 0x89, 0xC8, 0xEB, 0xC3]

theorem code_l10993d : ∀ x ∈ codeRange 0x10993d bytes_l10993d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x993d 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109948 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x109948 (movR64M64Effect 0x109948 0 (.sib 4 none 0 (.d32 0x118))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x109948 (LoadPre 0x109948 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x109948 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x109948 0 (.sib 4 none 0 (.d32 0x118))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x109950 (orR64M64Effect 0x109950 0 (.sib 4 none 0 (.d32 0x108))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[53, 4]
    (.letOp (n := 56) (.exec 0x109950 (LoadPre 0x109950 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x109950 + BitVec.ofNat 64 8)) 8) (orR64M64Effect 0x109950 0 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 57) (.out 0x109958 (orR64M64Effect 0x109958 0 (.sib 4 none 0 (.d32 0x100))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[55, 4]
    (.letOp (n := 58) (.exec 0x109958 (LoadPre 0x109958 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x109958 + BitVec.ofNat 64 8)) 8) (orR64M64Effect 0x109958 0 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 59) (.out 0x109960 (orR64M64Effect 0x109960 0 (.sib 4 none 0 (.d32 0x110))) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 4] []) (.flag .ZF)) #v[57, 4]
    (.letOp (n := 60) (.exec 0x109960 (LoadPre 0x109960 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x109960 + BitVec.ofNat 64 8)) 8) (orR64M64Effect 0x109960 0 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 61) (.out 0x109968 (atFlags (condHolds 5) (setccR8Effect 0x109968 3 3)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 3))) #v[3, 59]
    (.letOp (n := 62) (.exec 0x109968 (fun s => s.RIP = 0x109968) (atFlags (condHolds 5) (setccR8Effect 0x109968 3 3)) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[3, 59]
    (.letOp (n := 63) (.out 0x10996b (movR32M32LowEffect 0x10996b 2 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 64) (.exec 0x10996b (LoadPre 0x10996b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10996b + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x10996b 2 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x10996f (leaR64Effect 0x10996f 6 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 66) (.exec 0x10996f (fun s => s.RIP = 0x10996f) (leaR64Effect 0x10996f 6 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x109974 (movR64M64Effect 0x109974 14 (.sib 4 none 0 (.d32 0x120))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 68) (.exec 0x109974 (LoadPre 0x109974 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x109974 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x109974 14 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.out 0x10997c (movR64R64Effect 0x10997c 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[67]
    (.letOp (n := 70) (.exec 0x10997c (fun s => s.RIP = 0x10997c) (movR64R64Effect 0x10997c 7 14) (Reg.operands [.gpr 14] [])) #v[67]
    (.letOp (n := 71) (.out 0x10997f (movR64M64Effect 0x10997f 1 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 72) (.exec 0x10997f (LoadPre 0x10997f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10997f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10997f 1 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.out 0x109984 (callEffect (fun _ => 0x109c00) 0x109989) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 74) (.exec 0x109984 (PushPre 0x109984 5) (callEffect (fun _ => 0x109c00) 0x109989) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.const ⟨64, 0x109989⟩) #v[]
    (.terminate (.call ⟨.l109c00, RegMap.args [(1, 71), (2, 63), (3, 61), (4, 73), (5, 5), (6, 65), (7, 69), (12, 12), (13, 13), (14, 67), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 76⟩ { target := .l109989, kept := #v[], arity := rfl, guard := some (Fin.last 75) }))))))))))))))))))))))))

def bytes_l109948 : List UInt8 :=
  [0x48, 0x8B, 0x84, 0x24, 0x18, 0x01, 0x00, 0x00, 0x48, 0x0B, 0x84, 0x24, 0x08, 0x01, 0x00, 0x00,
    0x48, 0x0B, 0x84, 0x24, 0x00, 0x01, 0x00, 0x00, 0x48, 0x0B, 0x84, 0x24, 0x10, 0x01, 0x00, 0x00,
    0x0F, 0x95, 0xC3, 0x8B, 0x54, 0x24, 0x28, 0x48, 0x8D, 0x74, 0x24, 0x60, 0x4C, 0x8B, 0xB4, 0x24,
    0x20, 0x01, 0x00, 0x00, 0x4C, 0x89, 0xF7, 0x48, 0x8B, 0x4C, 0x24, 0x58, 0xE8, 0x77, 0x02, 0x00,
    0x00]

theorem code_l109948 : ∀ x ∈ codeRange 0x109948 bytes_l109948, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9948 65 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109989 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x109989 (movR64M64Effect 0x109989 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x109989 (LoadPre 0x109989 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109989 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109989 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10998e (xorR64Imm8Effect 0x10998e 0 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x10998e (fun s => s.RIP = 0x10998e) (xorR64Imm8Effect 0x10998e 0 0x1) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x109992 (orR64M64Effect 0x109992 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[55, 4]
    (.letOp (n := 58) (.exec 0x109992 (LoadPre 0x109992 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x109992 + BitVec.ofNat 64 5)) 8) (orR64M64Effect 0x109992 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 59) (.out 0x109997 (orR64M64Effect 0x109997 0 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[57, 4]
    (.letOp (n := 60) (.exec 0x109997 (LoadPre 0x109997 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x109997 + BitVec.ofNat 64 5)) 8) (orR64M64Effect 0x109997 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 61) (.out 0x10999c (orR64M64Effect 0x10999c 0 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[59, 4]
    (.letOp (n := 62) (.out 0x10999c (orR64M64Effect 0x10999c 0 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 4] []) (.flag .ZF)) #v[59, 4]
    (.letOp (n := 63) (.exec 0x10999c (LoadPre 0x10999c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10999c + BitVec.ofNat 64 5)) 8) (orR64M64Effect 0x10999c 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 64) (.out 0x1099a1 (atFlags (condHolds 4) (setccR8Effect 0x1099a1 3 0)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 0))) #v[61, 62]
    (.letOp (n := 65) (.exec 0x1099a1 (fun s => s.RIP = 0x1099a1) (atFlags (condHolds 4) (setccR8Effect 0x1099a1 3 0)) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[61, 62]
    (.letOp (n := 66) (.out 0x1099a4 (andR8R8Effect 0x1099a4 2 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[64, 3]
    (.letOp (n := 67) (.exec 0x1099a4 (fun s => s.RIP = 0x1099a4) (andR8R8Effect 0x1099a4 2 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[64, 3]
    (.letOp (n := 68) (.exec 0x1099a6 (StorePre 0x1099a6 4 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x1099a6 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1099a6 4 0 (.base 14 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 14] [])) #v[66, 14]
    (.letOp (n := 69) (.out 0x1099aa (movR64R64Effect 0x1099aa 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[14]
    (.letOp (n := 70) (.exec 0x1099aa (fun s => s.RIP = 0x1099aa) (movR64R64Effect 0x1099aa 0 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 71) (.out 0x1099ad (addR64Imm32Effect 0x1099ad 4 0x158) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 72) (.exec 0x1099ad (fun s => s.RIP = 0x1099ad) (addR64Imm32Effect 0x1099ad 4 0x158) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.out 0x1099b4 (popR64Effect 0x1099b4 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[71]
    (.letOp (n := 74) (.out 0x1099b4 (popR64Effect 0x1099b4 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[71]
    (.letOp (n := 75) (.exec 0x1099b4 (PopPre 0x1099b4) (popR64Effect 0x1099b4 1 3) (Reg.operands [.gpr 4] [])) #v[71]
    (.letOp (n := 76) (.out 0x1099b5 (popR64Effect 0x1099b5 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[74]
    (.letOp (n := 77) (.out 0x1099b5 (popR64Effect 0x1099b5 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[74]
    (.letOp (n := 78) (.exec 0x1099b5 (PopPre 0x1099b5) (popR64Effect 0x1099b5 2 12) (Reg.operands [.gpr 4] [])) #v[74]
    (.letOp (n := 79) (.out 0x1099b7 (popR64Effect 0x1099b7 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[77]
    (.letOp (n := 80) (.out 0x1099b7 (popR64Effect 0x1099b7 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[77]
    (.letOp (n := 81) (.exec 0x1099b7 (PopPre 0x1099b7) (popR64Effect 0x1099b7 2 13) (Reg.operands [.gpr 4] [])) #v[77]
    (.letOp (n := 82) (.out 0x1099b9 (popR64Effect 0x1099b9 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[80]
    (.letOp (n := 83) (.out 0x1099b9 (popR64Effect 0x1099b9 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[80]
    (.letOp (n := 84) (.exec 0x1099b9 (PopPre 0x1099b9) (popR64Effect 0x1099b9 2 14) (Reg.operands [.gpr 4] [])) #v[80]
    (.letOp (n := 85) (.out 0x1099bb (popR64Effect 0x1099bb 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[83]
    (.letOp (n := 86) (.out 0x1099bb (popR64Effect 0x1099bb 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[83]
    (.letOp (n := 87) (.exec 0x1099bb (PopPre 0x1099bb) (popR64Effect 0x1099bb 2 15) (Reg.operands [.gpr 4] [])) #v[83]
    (.letOp (n := 88) (.out 0x1099bd (popR64Effect 0x1099bd 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[86]
    (.letOp (n := 89) (.out 0x1099bd (popR64Effect 0x1099bd 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[86]
    (.letOp (n := 90) (.exec 0x1099bd (PopPre 0x1099bd) (popR64Effect 0x1099bd 1 5) (Reg.operands [.gpr 4] [])) #v[86]
    (.letOp (n := 91) (.out 0x1099be (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[89]
    (.letOp (n := 92) (.out 0x1099be (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[89]
    (.letOp (n := 93) (.exec 0x1099be (RetPre 0x1099be) (retEffect) (Reg.operands [.gpr 4] [])) #v[89]
    (.terminate (.ret (RegMap.args [(0, 69), (1, 1), (2, 2), (3, 73), (4, 92), (5, 88), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 76), (13, 79), (14, 82), (15, 85), (22, 22), (39, 39), (50, 50), (51, 51)] 94) (some ⟨91, by decide⟩)))))))))))))))))))))))))))))))))))))))))))

def bytes_l109989 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x08, 0x48, 0x83, 0xF0, 0x01, 0x48, 0x0B, 0x44, 0x24, 0x10, 0x48, 0x0B,
    0x44, 0x24, 0x18, 0x48, 0x0B, 0x44, 0x24, 0x20, 0x0F, 0x94, 0xC0, 0x20, 0xD8, 0x41, 0x88, 0x46,
    0x20, 0x4C, 0x89, 0xF0, 0x48, 0x81, 0xC4, 0x58, 0x01, 0x00, 0x00, 0x5B, 0x41, 0x5C, 0x41, 0x5D,
    0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l109989 : ∀ x ∈ codeRange 0x109989 bytes_l109989, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9989 54 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1099c0_7 : Block Op Label signature Reg.count 366 :=
  .letOp (n := 366) (.out 0x109b94 (addR64R64Effect 0x109b94 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0] []) (.reg (.gpr 11))) #v[361, 345]
    (.letOp (n := 367) (.out 0x109b94 (addR64R64Effect 0x109b94 11 0) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 0] []) (.flag .CF)) #v[361, 345]
    (.letOp (n := 368) (.exec 0x109b94 (fun s => s.RIP = 0x109b94) (addR64R64Effect 0x109b94 11 0) (Reg.operands [.gpr 11, .gpr 0] [])) #v[361, 345]
    (.letOp (n := 369) (.out 0x109b97 (movzxR32R8Effect 0x109b97 3 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[364]
    (.letOp (n := 370) (.exec 0x109b97 (fun s => s.RIP = 0x109b97) (movzxR32R8Effect 0x109b97 3 0 1) (Reg.operands [.gpr 1] [])) #v[364]
    (.letOp (n := 371) (.out 0x109b9a (atFlags StatusFlags.CF (adcR64R64Effect 0x109b9a 0 2)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 0))) #v[369, 356, 367]
    (.letOp (n := 372) (.exec 0x109b9a (fun s => s.RIP = 0x109b9a) (atFlags StatusFlags.CF (adcR64R64Effect 0x109b9a 0 2)) (Reg.operands [.gpr 0, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[369, 356, 367]
    (.letOp (n := 373) (.out 0x109b9d (movR64M64Effect 0x109b9d 1 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 374) (.exec 0x109b9d (LoadPre 0x109b9d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x109b9d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109b9d 1 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 375) (.exec 0x109ba2 (StorePre 0x109ba2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x109ba2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109ba2 1 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[373, 65]
    (.letOp (n := 376) (.out 0x109ba7 (movR64M64Effect 0x109ba7 1 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 377) (.exec 0x109ba7 (LoadPre 0x109ba7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x109ba7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109ba7 1 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 378) (.exec 0x109bac (StorePre 0x109bac 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x109bac + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109bac 1 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[376, 65]
    (.letOp (n := 379) (.out 0x109bb1 (movR64M64Effect 0x109bb1 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 380) (.exec 0x109bb1 (LoadPre 0x109bb1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x109bb1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109bb1 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 381) (.exec 0x109bb6 (StorePre 0x109bb6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x109bb6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109bb6 1 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[379, 65]
    (.letOp (n := 382) (.out 0x109bbb (movR64M64Effect 0x109bbb 1 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 383) (.exec 0x109bbb (LoadPre 0x109bbb (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x109bbb + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109bbb 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 384) (.exec 0x109bbf (StorePre 0x109bbf 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x109bbf + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109bbf 1 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[382, 65]
    (.letOp (n := 385) (.exec 0x109bc4 (StorePre 0x109bc4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x109bc4 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109bc4 8 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[315, 65]
    (.letOp (n := 386) (.exec 0x109bc9 (StorePre 0x109bc9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x109bc9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109bc9 15 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[358, 65]
    (.letOp (n := 387) (.exec 0x109bce (StorePre 0x109bce 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x109bce + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109bce 11 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[366, 65]
    (.letOp (n := 388) (.exec 0x109bd3 (StorePre 0x109bd3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x109bd3 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x109bd3 0 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[371, 65]
    (.letOp (n := 389) (.out 0x109bdb (leaR64Effect 0x109bdb 6 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[65]
    (.letOp (n := 390) (.exec 0x109bdb (fun s => s.RIP = 0x109bdb) (leaR64Effect 0x109bdb 6 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 391) (.out 0x109be0 (xorR32R32Effect 0x109be0 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[356, 356]
    (.letOp (n := 392) (.exec 0x109be0 (fun s => s.RIP = 0x109be0) (xorR32R32Effect 0x109be0 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[356, 356]
    (.letOp (n := 393) (.out 0x109be2 (callEffect (fun _ => 0x11b510) 0x109be7) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 394) (.exec 0x109be2 (PushPre 0x109be2 5) (callEffect (fun _ => 0x11b510) 0x109be7) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 395) (.const ⟨64, 0x109be7⟩) #v[]
    (.terminate (.call ⟨.l11b510, RegMap.args [(0, 371), (1, 382), (2, 391), (3, 199), (4, 393), (5, 323), (6, 389), (7, 7), (8, 315), (9, 339), (10, 245), (11, 366), (12, 318), (13, 341), (14, 348), (15, 358), (22, 22), (39, 39), (50, 50), (51, 51)] 396⟩ { target := .l109be7, kept := #v[], arity := rfl, guard := some (Fin.last 395) })))))))))))))))))))))))))))))))

def bytes_l1099c0_7 : List UInt8 :=
  [0x49, 0x01, 0xC3, 0x0F, 0xB6, 0xC1, 0x48, 0x11, 0xD0, 0x48, 0x8B, 0x4C, 0x24, 0x40, 0x48, 0x89,
    0x4C, 0x24, 0x48, 0x48, 0x8B, 0x4C, 0x24, 0x38, 0x48, 0x89, 0x4C, 0x24, 0x50, 0x48, 0x8B, 0x4C,
    0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x58, 0x48, 0x8B, 0x0C, 0x24, 0x48, 0x89, 0x4C, 0x24, 0x60,
    0x4C, 0x89, 0x44, 0x24, 0x68, 0x4C, 0x89, 0x7C, 0x24, 0x70, 0x4C, 0x89, 0x5C, 0x24, 0x78, 0x48,
    0x89, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x74, 0x24, 0x48, 0x31, 0xD2, 0xE8, 0x29,
    0x19, 0x01, 0x00]

theorem code_l1099c0_7 : ∀ x ∈ codeRange 0x109b94 bytes_l1099c0_7, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9b94 83 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1099c0_6 : Block Op Label signature Reg.count 318 :=
  .letOp (n := 318) (.out 0x109b56 (atFlags StatusFlags.CF (adcR64R64Effect 0x109b56 12 11)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 12))) #v[311, 301, 316]
    (.letOp (n := 319) (.out 0x109b56 (atFlags StatusFlags.CF (adcR64R64Effect 0x109b56 12 11)) (Reg.operands [.gpr 12, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[311, 301, 316]
    (.letOp (n := 320) (.exec 0x109b56 (fun s => s.RIP = 0x109b56) (atFlags StatusFlags.CF (adcR64R64Effect 0x109b56 12 11)) (Reg.operands [.gpr 12, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[311, 301, 316]
    (.letOp (n := 321) (.out 0x109b59 (movzxR32R8Effect 0x109b59 4 5 9) (EffectPart.reads (.reg (.gpr 5)) [.gpr 9] []) (.reg (.gpr 5))) #v[304]
    (.letOp (n := 322) (.exec 0x109b59 (fun s => s.RIP = 0x109b59) (movzxR32R8Effect 0x109b59 4 5 9) (Reg.operands [.gpr 9] [])) #v[304]
    (.letOp (n := 323) (.out 0x109b5d (atFlags StatusFlags.CF (adcR64R64Effect 0x109b5d 5 1)) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 5))) #v[321, 299, 319]
    (.letOp (n := 324) (.exec 0x109b5d (fun s => s.RIP = 0x109b5d) (atFlags StatusFlags.CF (adcR64R64Effect 0x109b5d 5 1)) (Reg.operands [.gpr 5, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[321, 299, 319]
    (.letOp (n := 325) (.out 0x109b60 (movR64R64Effect 0x109b60 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[184]
    (.letOp (n := 326) (.exec 0x109b60 (fun s => s.RIP = 0x109b60) (movR64R64Effect 0x109b60 0 6) (Reg.operands [.gpr 6] [])) #v[184]
    (.letOp (n := 327) (.out 0x109b63 (mulR64Effect 0x109b63 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[231, 325]
    (.letOp (n := 328) (.out 0x109b63 (mulR64Effect 0x109b63 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[231, 325]
    (.letOp (n := 329) (.exec 0x109b63 (fun s => s.RIP = 0x109b63) (mulR64Effect 0x109b63 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[231, 325]
    (.letOp (n := 330) (.out 0x109b66 (movR64R64Effect 0x109b66 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[328]
    (.letOp (n := 331) (.exec 0x109b66 (fun s => s.RIP = 0x109b66) (movR64R64Effect 0x109b66 11 2) (Reg.operands [.gpr 2] [])) #v[328]
    (.letOp (n := 332) (.out 0x109b69 (movR64R64Effect 0x109b69 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[327]
    (.letOp (n := 333) (.exec 0x109b69 (fun s => s.RIP = 0x109b69) (movR64R64Effect 0x109b69 15 0) (Reg.operands [.gpr 0] [])) #v[327]
    (.letOp (n := 334) (.out 0x109b6c (movR64R64Effect 0x109b6c 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[199]
    (.letOp (n := 335) (.exec 0x109b6c (fun s => s.RIP = 0x109b6c) (movR64R64Effect 0x109b6c 0 3) (Reg.operands [.gpr 3] [])) #v[199]
    (.letOp (n := 336) (.out 0x109b6f (mulR64Effect 0x109b6f 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[245, 334]
    (.letOp (n := 337) (.out 0x109b6f (mulR64Effect 0x109b6f 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[245, 334]
    (.letOp (n := 338) (.exec 0x109b6f (fun s => s.RIP = 0x109b6f) (mulR64Effect 0x109b6f 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[245, 334]
    (.letOp (n := 339) (.out 0x109b72 (movR64R64Effect 0x109b72 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[337]
    (.letOp (n := 340) (.exec 0x109b72 (fun s => s.RIP = 0x109b72) (movR64R64Effect 0x109b72 9 2) (Reg.operands [.gpr 2] [])) #v[337]
    (.letOp (n := 341) (.out 0x109b75 (movR64R64Effect 0x109b75 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[336]
    (.letOp (n := 342) (.exec 0x109b75 (fun s => s.RIP = 0x109b75) (movR64R64Effect 0x109b75 13 0) (Reg.operands [.gpr 0] [])) #v[336]
    (.letOp (n := 343) (.out 0x109b78 (movR64R64Effect 0x109b78 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[184]
    (.letOp (n := 344) (.exec 0x109b78 (fun s => s.RIP = 0x109b78) (movR64R64Effect 0x109b78 0 6) (Reg.operands [.gpr 6] [])) #v[184]
    (.letOp (n := 345) (.out 0x109b7b (mulR64Effect 0x109b7b 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[245, 343]
    (.letOp (n := 346) (.out 0x109b7b (mulR64Effect 0x109b7b 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[245, 343]
    (.letOp (n := 347) (.exec 0x109b7b (fun s => s.RIP = 0x109b7b) (mulR64Effect 0x109b7b 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[245, 343]
    (.letOp (n := 348) (.out 0x109b7e (movR64R64Effect 0x109b7e 14 7) (EffectPart.reads (.reg (.gpr 14)) [.gpr 7] []) (.reg (.gpr 14))) #v[7]
    (.letOp (n := 349) (.exec 0x109b7e (fun s => s.RIP = 0x109b7e) (movR64R64Effect 0x109b7e 14 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 350) (.out 0x109b81 (addR64R64Effect 0x109b81 15 12) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 12] []) (.reg (.gpr 15))) #v[332, 318]
    (.letOp (n := 351) (.out 0x109b81 (addR64R64Effect 0x109b81 15 12) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 12] []) (.flag .CF)) #v[332, 318]
    (.letOp (n := 352) (.exec 0x109b81 (fun s => s.RIP = 0x109b81) (addR64R64Effect 0x109b81 15 12) (Reg.operands [.gpr 15, .gpr 12] [])) #v[332, 318]
    (.letOp (n := 353) (.out 0x109b84 (atFlags StatusFlags.CF (adcR64R64Effect 0x109b84 11 5)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[330, 323, 351]
    (.letOp (n := 354) (.out 0x109b84 (atFlags StatusFlags.CF (adcR64R64Effect 0x109b84 11 5)) (Reg.operands [.gpr 11, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[330, 323, 351]
    (.letOp (n := 355) (.exec 0x109b84 (fun s => s.RIP = 0x109b84) (atFlags StatusFlags.CF (adcR64R64Effect 0x109b84 11 5)) (Reg.operands [.gpr 11, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[330, 323, 351]
    (.letOp (n := 356) (.out 0x109b87 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x109b87 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[346, 354]
    (.letOp (n := 357) (.exec 0x109b87 (fun s => s.RIP = 0x109b87) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x109b87 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[346, 354]
    (.letOp (n := 358) (.out 0x109b8b (addR64R64Effect 0x109b8b 15 13) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 13] []) (.reg (.gpr 15))) #v[350, 341]
    (.letOp (n := 359) (.out 0x109b8b (addR64R64Effect 0x109b8b 15 13) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 13] []) (.flag .CF)) #v[350, 341]
    (.letOp (n := 360) (.exec 0x109b8b (fun s => s.RIP = 0x109b8b) (addR64R64Effect 0x109b8b 15 13) (Reg.operands [.gpr 15, .gpr 13] [])) #v[350, 341]
    (.letOp (n := 361) (.out 0x109b8e (atFlags StatusFlags.CF (adcR64R64Effect 0x109b8e 11 9)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[353, 339, 359]
    (.letOp (n := 362) (.out 0x109b8e (atFlags StatusFlags.CF (adcR64R64Effect 0x109b8e 11 9)) (Reg.operands [.gpr 11, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[353, 339, 359]
    (.letOp (n := 363) (.exec 0x109b8e (fun s => s.RIP = 0x109b8e) (atFlags StatusFlags.CF (adcR64R64Effect 0x109b8e 11 9)) (Reg.operands [.gpr 11, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[353, 339, 359]
    (.letOp (n := 364) (.out 0x109b91 (atFlags (condHolds 2) (setccR8Effect 0x109b91 3 1)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[299, 362]
    (.letOp (n := 365) (.exec 0x109b91 (fun s => s.RIP = 0x109b91) (atFlags (condHolds 2) (setccR8Effect 0x109b91 3 1)) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[299, 362]
    (b_l1099c0_7))))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l1099c0_6 : List UInt8 :=
  [0x4D, 0x11, 0xDC, 0x41, 0x0F, 0xB6, 0xE9, 0x48, 0x11, 0xCD, 0x48, 0x89, 0xF0, 0x49, 0xF7, 0xE6,
    0x49, 0x89, 0xD3, 0x49, 0x89, 0xC7, 0x48, 0x89, 0xD8, 0x49, 0xF7, 0xE2, 0x49, 0x89, 0xD1, 0x49,
    0x89, 0xC5, 0x48, 0x89, 0xF0, 0x49, 0xF7, 0xE2, 0x49, 0x89, 0xFE, 0x4D, 0x01, 0xE7, 0x49, 0x11,
    0xEB, 0x48, 0x83, 0xD2, 0x00, 0x4D, 0x01, 0xEF, 0x4D, 0x11, 0xCB, 0x0F, 0x92, 0xC1] ++ bytes_l1099c0_7

theorem code_l1099c0_6 : ∀ x ∈ codeRange 0x109b56 bytes_l1099c0_6, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x9b56 62 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1099c0_7

@[cfg_block] def b_l1099c0_5 : Block Op Label signature Reg.count 270 :=
  .letOp (n := 270) (.out 0x109b15 (movR64R64Effect 0x109b15 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[184]
    (.letOp (n := 271) (.exec 0x109b15 (fun s => s.RIP = 0x109b15) (movR64R64Effect 0x109b15 0 6) (Reg.operands [.gpr 6] [])) #v[184]
    (.letOp (n := 272) (.out 0x109b18 (mulM64Effect 0x109b18 5 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[270, 65]
    (.letOp (n := 273) (.out 0x109b18 (mulM64Effect 0x109b18 5 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[270, 65]
    (.letOp (n := 274) (.exec 0x109b18 (LoadPre 0x109b18 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x109b18 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x109b18 5 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[270, 65]
    (.letOp (n := 275) (.out 0x109b1d (movR64R64Effect 0x109b1d 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[273]
    (.letOp (n := 276) (.exec 0x109b1d (fun s => s.RIP = 0x109b1d) (movR64R64Effect 0x109b1d 15 2) (Reg.operands [.gpr 2] [])) #v[273]
    (.letOp (n := 277) (.out 0x109b20 (movR64R64Effect 0x109b20 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[272]
    (.letOp (n := 278) (.exec 0x109b20 (fun s => s.RIP = 0x109b20) (movR64R64Effect 0x109b20 12 0) (Reg.operands [.gpr 0] [])) #v[272]
    (.letOp (n := 279) (.out 0x109b23 (addR64R64Effect 0x109b23 12 11) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 11] []) (.reg (.gpr 12))) #v[277, 263]
    (.letOp (n := 280) (.out 0x109b23 (addR64R64Effect 0x109b23 12 11) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 11] []) (.flag .CF)) #v[277, 263]
    (.letOp (n := 281) (.exec 0x109b23 (fun s => s.RIP = 0x109b23) (addR64R64Effect 0x109b23 12 11) (Reg.operands [.gpr 12, .gpr 11] [])) #v[277, 263]
    (.letOp (n := 282) (.out 0x109b26 (atFlags StatusFlags.CF (adcR64R64Effect 0x109b26 15 9)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 15))) #v[275, 268, 280]
    (.letOp (n := 283) (.out 0x109b26 (atFlags StatusFlags.CF (adcR64R64Effect 0x109b26 15 9)) (Reg.operands [.gpr 15, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[275, 268, 280]
    (.letOp (n := 284) (.exec 0x109b26 (fun s => s.RIP = 0x109b26) (atFlags StatusFlags.CF (adcR64R64Effect 0x109b26 15 9)) (Reg.operands [.gpr 15, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[275, 268, 280]
    (.letOp (n := 285) (.out 0x109b29 (atFlags (condHolds 2) (setccR8Effect 0x109b29 3 1)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[146, 283]
    (.letOp (n := 286) (.exec 0x109b29 (fun s => s.RIP = 0x109b29) (atFlags (condHolds 2) (setccR8Effect 0x109b29 3 1)) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[146, 283]
    (.letOp (n := 287) (.out 0x109b2c (movR64R64Effect 0x109b2c 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[199]
    (.letOp (n := 288) (.exec 0x109b2c (fun s => s.RIP = 0x109b2c) (movR64R64Effect 0x109b2c 0 3) (Reg.operands [.gpr 3] [])) #v[199]
    (.letOp (n := 289) (.out 0x109b2f (mulR64Effect 0x109b2f 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[231, 287]
    (.letOp (n := 290) (.out 0x109b2f (mulR64Effect 0x109b2f 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[231, 287]
    (.letOp (n := 291) (.exec 0x109b2f (fun s => s.RIP = 0x109b2f) (mulR64Effect 0x109b2f 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[231, 287]
    (.letOp (n := 292) (.out 0x109b32 (movR64R64Effect 0x109b32 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[290]
    (.letOp (n := 293) (.exec 0x109b32 (fun s => s.RIP = 0x109b32) (movR64R64Effect 0x109b32 11 2) (Reg.operands [.gpr 2] [])) #v[290]
    (.letOp (n := 294) (.out 0x109b35 (movR64R64Effect 0x109b35 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[289]
    (.letOp (n := 295) (.exec 0x109b35 (fun s => s.RIP = 0x109b35) (movR64R64Effect 0x109b35 13 0) (Reg.operands [.gpr 0] [])) #v[289]
    (.letOp (n := 296) (.out 0x109b38 (addR64R64Effect 0x109b38 13 12) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 12] []) (.reg (.gpr 13))) #v[294, 279]
    (.letOp (n := 297) (.out 0x109b38 (addR64R64Effect 0x109b38 13 12) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 12] []) (.flag .CF)) #v[294, 279]
    (.letOp (n := 298) (.exec 0x109b38 (fun s => s.RIP = 0x109b38) (addR64R64Effect 0x109b38 13 12) (Reg.operands [.gpr 13, .gpr 12] [])) #v[294, 279]
    (.letOp (n := 299) (.out 0x109b3b (movzxR32R8Effect 0x109b3b 3 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[285]
    (.letOp (n := 300) (.exec 0x109b3b (fun s => s.RIP = 0x109b3b) (movzxR32R8Effect 0x109b3b 3 1 1) (Reg.operands [.gpr 1] [])) #v[285]
    (.letOp (n := 301) (.out 0x109b3e (atFlags StatusFlags.CF (adcR64R64Effect 0x109b3e 11 15)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[292, 282, 297]
    (.letOp (n := 302) (.out 0x109b3e (atFlags StatusFlags.CF (adcR64R64Effect 0x109b3e 11 15)) (Reg.operands [.gpr 11, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[292, 282, 297]
    (.letOp (n := 303) (.exec 0x109b3e (fun s => s.RIP = 0x109b3e) (atFlags StatusFlags.CF (adcR64R64Effect 0x109b3e 11 15)) (Reg.operands [.gpr 11, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[292, 282, 297]
    (.letOp (n := 304) (.out 0x109b41 (atFlags (condHolds 2) (setccR8Effect 0x109b41 4 9)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[268, 302]
    (.letOp (n := 305) (.exec 0x109b41 (fun s => s.RIP = 0x109b41) (atFlags (condHolds 2) (setccR8Effect 0x109b41 4 9)) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[268, 302]
    (.letOp (n := 306) (.out 0x109b45 (movR64M64Effect 0x109b45 0 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 307) (.exec 0x109b45 (LoadPre 0x109b45 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x109b45 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109b45 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 308) (.out 0x109b4a (mulR64Effect 0x109b4a 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[245, 306]
    (.letOp (n := 309) (.out 0x109b4a (mulR64Effect 0x109b4a 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[245, 306]
    (.letOp (n := 310) (.exec 0x109b4a (fun s => s.RIP = 0x109b4a) (mulR64Effect 0x109b4a 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[245, 306]
    (.letOp (n := 311) (.out 0x109b4d (movR64R64Effect 0x109b4d 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 2] []) (.reg (.gpr 12))) #v[309]
    (.letOp (n := 312) (.exec 0x109b4d (fun s => s.RIP = 0x109b4d) (movR64R64Effect 0x109b4d 12 2) (Reg.operands [.gpr 2] [])) #v[309]
    (.letOp (n := 313) (.out 0x109b50 (movR64R64Effect 0x109b50 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[308]
    (.letOp (n := 314) (.exec 0x109b50 (fun s => s.RIP = 0x109b50) (movR64R64Effect 0x109b50 8 0) (Reg.operands [.gpr 0] [])) #v[308]
    (.letOp (n := 315) (.out 0x109b53 (addR64R64Effect 0x109b53 8 13) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 13] []) (.reg (.gpr 8))) #v[313, 296]
    (.letOp (n := 316) (.out 0x109b53 (addR64R64Effect 0x109b53 8 13) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 13] []) (.flag .CF)) #v[313, 296]
    (.letOp (n := 317) (.exec 0x109b53 (fun s => s.RIP = 0x109b53) (addR64R64Effect 0x109b53 8 13) (Reg.operands [.gpr 8, .gpr 13] [])) #v[313, 296]
    (b_l1099c0_6))))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l1099c0_5 : List UInt8 :=
  [0x48, 0x89, 0xF0, 0x48, 0xF7, 0x64, 0x24, 0x18, 0x49, 0x89, 0xD7, 0x49, 0x89, 0xC4, 0x4D, 0x01,
    0xDC, 0x4D, 0x11, 0xCF, 0x0F, 0x92, 0xC1, 0x48, 0x89, 0xD8, 0x49, 0xF7, 0xE6, 0x49, 0x89, 0xD3,
    0x49, 0x89, 0xC5, 0x4D, 0x01, 0xE5, 0x0F, 0xB6, 0xC9, 0x4D, 0x11, 0xFB, 0x41, 0x0F, 0x92, 0xC1,
    0x48, 0x8B, 0x44, 0x24, 0x20, 0x49, 0xF7, 0xE2, 0x49, 0x89, 0xD4, 0x49, 0x89, 0xC0, 0x4D, 0x01,
    0xE8] ++ bytes_l1099c0_6

theorem code_l1099c0_5 : ∀ x ∈ codeRange 0x109b15 bytes_l1099c0_5, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x9b15 65 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1099c0_6

@[cfg_block] def b_l1099c0_4 : Block Op Label signature Reg.count 224 :=
  .letOp (n := 224) (.out 0x109ace (addR8Imm8Effect 0x109ace 4 9 0xff) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[212]
    (.letOp (n := 225) (.out 0x109ace (addR8Imm8Effect 0x109ace 4 9 0xff) (EffectPart.reads (.flag .CF) [.gpr 9] []) (.flag .CF)) #v[212]
    (.letOp (n := 226) (.exec 0x109ace (fun s => s.RIP = 0x109ace) (addR8Imm8Effect 0x109ace 4 9 0xff) (Reg.operands [.gpr 9] [])) #v[212]
    (.letOp (n := 227) (.out 0x109ad2 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x109ad2 8 0x0)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[222, 225]
    (.letOp (n := 228) (.exec 0x109ad2 (fun s => s.RIP = 0x109ad2) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x109ad2 8 0x0)) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[222, 225]
    (.letOp (n := 229) (.out 0x109ad6 (movR64R64Effect 0x109ad6 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[146]
    (.letOp (n := 230) (.exec 0x109ad6 (fun s => s.RIP = 0x109ad6) (movR64R64Effect 0x109ad6 0 1) (Reg.operands [.gpr 1] [])) #v[146]
    (.letOp (n := 231) (.out 0x109ad9 (movR64M64Effect 0x109ad9 14 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[65]
    (.letOp (n := 232) (.exec 0x109ad9 (LoadPre 0x109ad9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109ad9 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109ad9 14 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 233) (.out 0x109ade (mulR64Effect 0x109ade 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[231, 229]
    (.letOp (n := 234) (.out 0x109ade (mulR64Effect 0x109ade 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[231, 229]
    (.letOp (n := 235) (.exec 0x109ade (fun s => s.RIP = 0x109ade) (mulR64Effect 0x109ade 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[231, 229]
    (.letOp (n := 236) (.out 0x109ae1 (movR64R64Effect 0x109ae1 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[234]
    (.letOp (n := 237) (.exec 0x109ae1 (fun s => s.RIP = 0x109ae1) (movR64R64Effect 0x109ae1 13 2) (Reg.operands [.gpr 2] [])) #v[234]
    (.letOp (n := 238) (.out 0x109ae4 (movR64R64Effect 0x109ae4 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[233]
    (.letOp (n := 239) (.exec 0x109ae4 (fun s => s.RIP = 0x109ae4) (movR64R64Effect 0x109ae4 5 0) (Reg.operands [.gpr 0] [])) #v[233]
    (.letOp (n := 240) (.out 0x109ae7 (addR64R64Effect 0x109ae7 5 12) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 12] []) (.reg (.gpr 5))) #v[238, 214]
    (.letOp (n := 241) (.out 0x109ae7 (addR64R64Effect 0x109ae7 5 12) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 12] []) (.flag .CF)) #v[238, 214]
    (.letOp (n := 242) (.exec 0x109ae7 (fun s => s.RIP = 0x109ae7) (addR64R64Effect 0x109ae7 5 12) (Reg.operands [.gpr 5, .gpr 12] [])) #v[238, 214]
    (.letOp (n := 243) (.out 0x109aea (movR64M64Effect 0x109aea 0 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 244) (.exec 0x109aea (LoadPre 0x109aea (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x109aea + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109aea 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 245) (.out 0x109aee (movR64M64Effect 0x109aee 10 (.base 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[243]
    (.letOp (n := 246) (.exec 0x109aee (LoadPre 0x109aee (fun s => AddrMode.addr (.base 0 (.d8 0x18)) s (0x109aee + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109aee 10 (.base 0 (.d8 0x18))) (Reg.operands [.gpr 0] [])) #v[243]
    (.letOp (n := 247) (.out 0x109af2 (atFlags StatusFlags.CF (adcR64R64Effect 0x109af2 13 15)) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 13))) #v[236, 217, 241]
    (.letOp (n := 248) (.out 0x109af2 (atFlags StatusFlags.CF (adcR64R64Effect 0x109af2 13 15)) (Reg.operands [.gpr 13, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[236, 217, 241]
    (.letOp (n := 249) (.exec 0x109af2 (fun s => s.RIP = 0x109af2) (atFlags StatusFlags.CF (adcR64R64Effect 0x109af2 13 15)) (Reg.operands [.gpr 13, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[236, 217, 241]
    (.letOp (n := 250) (.out 0x109af5 (atFlags (condHolds 2) (setccR8Effect 0x109af5 4 9)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[224, 248]
    (.letOp (n := 251) (.exec 0x109af5 (fun s => s.RIP = 0x109af5) (atFlags (condHolds 2) (setccR8Effect 0x109af5 4 9)) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[224, 248]
    (.letOp (n := 252) (.out 0x109af9 (movR64M64Effect 0x109af9 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 253) (.exec 0x109af9 (LoadPre 0x109af9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x109af9 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109af9 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 254) (.out 0x109afe (mulR64Effect 0x109afe 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[245, 252]
    (.letOp (n := 255) (.out 0x109afe (mulR64Effect 0x109afe 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[245, 252]
    (.letOp (n := 256) (.exec 0x109afe (fun s => s.RIP = 0x109afe) (mulR64Effect 0x109afe 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[245, 252]
    (.letOp (n := 257) (.out 0x109b01 (movR64R64Effect 0x109b01 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[255]
    (.letOp (n := 258) (.exec 0x109b01 (fun s => s.RIP = 0x109b01) (movR64R64Effect 0x109b01 11 2) (Reg.operands [.gpr 2] [])) #v[255]
    (.letOp (n := 259) (.out 0x109b04 (addR64R64Effect 0x109b04 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[254, 240]
    (.letOp (n := 260) (.out 0x109b04 (addR64R64Effect 0x109b04 0 5) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 5] []) (.flag .CF)) #v[254, 240]
    (.letOp (n := 261) (.exec 0x109b04 (fun s => s.RIP = 0x109b04) (addR64R64Effect 0x109b04 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[254, 240]
    (.letOp (n := 262) (.exec 0x109b07 (StorePre 0x109b07 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x109b07 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x109b07 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[259, 65]
    (.letOp (n := 263) (.out 0x109b0b (atFlags StatusFlags.CF (adcR64R64Effect 0x109b0b 11 13)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[257, 247, 260]
    (.letOp (n := 264) (.out 0x109b0b (atFlags StatusFlags.CF (adcR64R64Effect 0x109b0b 11 13)) (Reg.operands [.gpr 11, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[257, 247, 260]
    (.letOp (n := 265) (.exec 0x109b0b (fun s => s.RIP = 0x109b0b) (atFlags StatusFlags.CF (adcR64R64Effect 0x109b0b 11 13)) (Reg.operands [.gpr 11, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[257, 247, 260]
    (.letOp (n := 266) (.out 0x109b0e (movzxR32R8Effect 0x109b0e 4 9 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[250]
    (.letOp (n := 267) (.exec 0x109b0e (fun s => s.RIP = 0x109b0e) (movzxR32R8Effect 0x109b0e 4 9 9) (Reg.operands [.gpr 9] [])) #v[250]
    (.letOp (n := 268) (.out 0x109b12 (atFlags StatusFlags.CF (adcR64R64Effect 0x109b12 9 8)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[266, 227, 264]
    (.letOp (n := 269) (.exec 0x109b12 (fun s => s.RIP = 0x109b12) (atFlags StatusFlags.CF (adcR64R64Effect 0x109b12 9 8)) (Reg.operands [.gpr 9, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[266, 227, 264]
    (b_l1099c0_5))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l1099c0_4 : List UInt8 :=
  [0x41, 0x80, 0xC1, 0xFF, 0x49, 0x83, 0xD0, 0x00, 0x48, 0x89, 0xC8, 0x4C, 0x8B, 0x74, 0x24, 0x08,
    0x49, 0xF7, 0xE6, 0x49, 0x89, 0xD5, 0x48, 0x89, 0xC5, 0x4C, 0x01, 0xE5, 0x48, 0x8B, 0x04, 0x24,
    0x4C, 0x8B, 0x50, 0x18, 0x4D, 0x11, 0xFD, 0x41, 0x0F, 0x92, 0xC1, 0x48, 0x8B, 0x44, 0x24, 0x28,
    0x49, 0xF7, 0xE2, 0x49, 0x89, 0xD3, 0x48, 0x01, 0xE8, 0x48, 0x89, 0x04, 0x24, 0x4D, 0x11, 0xEB,
    0x45, 0x0F, 0xB6, 0xC9, 0x4D, 0x11, 0xC1] ++ bytes_l1099c0_5

theorem code_l1099c0_4 : ∀ x ∈ codeRange 0x109ace bytes_l1099c0_4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x9ace 71 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1099c0_5

@[cfg_block] def b_l1099c0_3 : Block Op Label signature Reg.count 177 :=
  .letOp (n := 177) (.out 0x109a8a (addR64R64Effect 0x109a8a 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 13] []) (.reg (.gpr 0))) #v[172, 157]
    (.letOp (n := 178) (.out 0x109a8a (addR64R64Effect 0x109a8a 0 13) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 13] []) (.flag .CF)) #v[172, 157]
    (.letOp (n := 179) (.exec 0x109a8a (fun s => s.RIP = 0x109a8a) (addR64R64Effect 0x109a8a 0 13) (Reg.operands [.gpr 0, .gpr 13] [])) #v[172, 157]
    (.letOp (n := 180) (.exec 0x109a8d (StorePre 0x109a8d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x109a8d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109a8d 0 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[177, 65]
    (.letOp (n := 181) (.out 0x109a92 (atFlags StatusFlags.CF (adcR64R64Effect 0x109a92 5 12)) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 5))) #v[175, 165, 178]
    (.letOp (n := 182) (.out 0x109a92 (atFlags StatusFlags.CF (adcR64R64Effect 0x109a92 5 12)) (Reg.operands [.gpr 5, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[175, 165, 178]
    (.letOp (n := 183) (.exec 0x109a92 (fun s => s.RIP = 0x109a92) (atFlags StatusFlags.CF (adcR64R64Effect 0x109a92 5 12)) (Reg.operands [.gpr 5, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[175, 165, 178]
    (.letOp (n := 184) (.out 0x109a95 (movR64M64Effect 0x109a95 6 (.base 14 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[67]
    (.letOp (n := 185) (.exec 0x109a95 (LoadPre 0x109a95 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x109a95 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109a95 6 (.base 14 (.d8 0x18))) (Reg.operands [.gpr 14] [])) #v[67]
    (.letOp (n := 186) (.out 0x109a99 (movzxR32R8Effect 0x109a99 4 10 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[168]
    (.letOp (n := 187) (.exec 0x109a99 (fun s => s.RIP = 0x109a99) (movzxR32R8Effect 0x109a99 4 10 10) (Reg.operands [.gpr 10] [])) #v[168]
    (.letOp (n := 188) (.out 0x109a9d (atFlags StatusFlags.CF (adcR64R64Effect 0x109a9d 10 9)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[186, 142, 182]
    (.letOp (n := 189) (.exec 0x109a9d (fun s => s.RIP = 0x109a9d) (atFlags StatusFlags.CF (adcR64R64Effect 0x109a9d 10 9)) (Reg.operands [.gpr 10, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[186, 142, 182]
    (.letOp (n := 190) (.out 0x109aa0 (movR64R64Effect 0x109aa0 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[184]
    (.letOp (n := 191) (.exec 0x109aa0 (fun s => s.RIP = 0x109aa0) (movR64R64Effect 0x109aa0 0 6) (Reg.operands [.gpr 6] [])) #v[184]
    (.letOp (n := 192) (.out 0x109aa3 (mulR64Effect 0x109aa3 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[69, 190]
    (.letOp (n := 193) (.out 0x109aa3 (mulR64Effect 0x109aa3 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[69, 190]
    (.letOp (n := 194) (.exec 0x109aa3 (fun s => s.RIP = 0x109aa3) (mulR64Effect 0x109aa3 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[69, 190]
    (.letOp (n := 195) (.out 0x109aa6 (movR64R64Effect 0x109aa6 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[193]
    (.letOp (n := 196) (.exec 0x109aa6 (fun s => s.RIP = 0x109aa6) (movR64R64Effect 0x109aa6 15 2) (Reg.operands [.gpr 2] [])) #v[193]
    (.letOp (n := 197) (.out 0x109aa9 (movR64R64Effect 0x109aa9 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[192]
    (.letOp (n := 198) (.exec 0x109aa9 (fun s => s.RIP = 0x109aa9) (movR64R64Effect 0x109aa9 12 0) (Reg.operands [.gpr 0] [])) #v[192]
    (.letOp (n := 199) (.out 0x109aac (movR64M64Effect 0x109aac 3 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[65]
    (.letOp (n := 200) (.exec 0x109aac (LoadPre 0x109aac (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x109aac + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109aac 3 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 201) (.out 0x109ab1 (movR64R64Effect 0x109ab1 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[199]
    (.letOp (n := 202) (.exec 0x109ab1 (fun s => s.RIP = 0x109ab1) (movR64R64Effect 0x109ab1 0 3) (Reg.operands [.gpr 3] [])) #v[199]
    (.letOp (n := 203) (.out 0x109ab4 (mulR64Effect 0x109ab4 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[95, 201]
    (.letOp (n := 204) (.out 0x109ab4 (mulR64Effect 0x109ab4 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[95, 201]
    (.letOp (n := 205) (.exec 0x109ab4 (fun s => s.RIP = 0x109ab4) (mulR64Effect 0x109ab4 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[95, 201]
    (.letOp (n := 206) (.out 0x109ab7 (addR64R64Effect 0x109ab7 12 5) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 5] []) (.reg (.gpr 12))) #v[197, 181]
    (.letOp (n := 207) (.out 0x109ab7 (addR64R64Effect 0x109ab7 12 5) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 5] []) (.flag .CF)) #v[197, 181]
    (.letOp (n := 208) (.exec 0x109ab7 (fun s => s.RIP = 0x109ab7) (addR64R64Effect 0x109ab7 12 5) (Reg.operands [.gpr 12, .gpr 5] [])) #v[197, 181]
    (.letOp (n := 209) (.out 0x109aba (atFlags StatusFlags.CF (adcR64R64Effect 0x109aba 15 10)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 15))) #v[195, 188, 207]
    (.letOp (n := 210) (.out 0x109aba (atFlags StatusFlags.CF (adcR64R64Effect 0x109aba 15 10)) (Reg.operands [.gpr 15, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[195, 188, 207]
    (.letOp (n := 211) (.exec 0x109aba (fun s => s.RIP = 0x109aba) (atFlags StatusFlags.CF (adcR64R64Effect 0x109aba 15 10)) (Reg.operands [.gpr 15, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[195, 188, 207]
    (.letOp (n := 212) (.out 0x109abd (atFlags (condHolds 2) (setccR8Effect 0x109abd 4 9)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[142, 210]
    (.letOp (n := 213) (.exec 0x109abd (fun s => s.RIP = 0x109abd) (atFlags (condHolds 2) (setccR8Effect 0x109abd 4 9)) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[142, 210]
    (.letOp (n := 214) (.out 0x109ac1 (addR64R64Effect 0x109ac1 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 0] []) (.reg (.gpr 12))) #v[206, 203]
    (.letOp (n := 215) (.out 0x109ac1 (addR64R64Effect 0x109ac1 12 0) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 0] []) (.flag .CF)) #v[206, 203]
    (.letOp (n := 216) (.exec 0x109ac1 (fun s => s.RIP = 0x109ac1) (addR64R64Effect 0x109ac1 12 0) (Reg.operands [.gpr 12, .gpr 0] [])) #v[206, 203]
    (.letOp (n := 217) (.out 0x109ac4 (atFlags StatusFlags.CF (adcR64R64Effect 0x109ac4 15 2)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 15))) #v[209, 204, 215]
    (.letOp (n := 218) (.out 0x109ac4 (atFlags StatusFlags.CF (adcR64R64Effect 0x109ac4 15 2)) (Reg.operands [.gpr 15, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[209, 204, 215]
    (.letOp (n := 219) (.exec 0x109ac4 (fun s => s.RIP = 0x109ac4) (atFlags StatusFlags.CF (adcR64R64Effect 0x109ac4 15 2)) (Reg.operands [.gpr 15, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[209, 204, 215]
    (.letOp (n := 220) (.out 0x109ac7 (atFlags (condHolds 2) (setccR8Effect 0x109ac7 3 0)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 0))) #v[203, 218]
    (.letOp (n := 221) (.exec 0x109ac7 (fun s => s.RIP = 0x109ac7) (atFlags (condHolds 2) (setccR8Effect 0x109ac7 3 0)) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[203, 218]
    (.letOp (n := 222) (.out 0x109aca (movzxR32R8Effect 0x109aca 4 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[220]
    (.letOp (n := 223) (.exec 0x109aca (fun s => s.RIP = 0x109aca) (movzxR32R8Effect 0x109aca 4 8 0) (Reg.operands [.gpr 0] [])) #v[220]
    (b_l1099c0_4)))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l1099c0_3 : List UInt8 :=
  [0x4C, 0x01, 0xE8, 0x48, 0x89, 0x44, 0x24, 0x30, 0x4C, 0x11, 0xE5, 0x49, 0x8B, 0x76, 0x18, 0x45,
    0x0F, 0xB6, 0xD2, 0x4D, 0x11, 0xCA, 0x48, 0x89, 0xF0, 0x49, 0xF7, 0xE0, 0x49, 0x89, 0xD7, 0x49,
    0x89, 0xC4, 0x48, 0x8B, 0x5C, 0x24, 0x10, 0x48, 0x89, 0xD8, 0x49, 0xF7, 0xE3, 0x49, 0x01, 0xEC,
    0x4D, 0x11, 0xD7, 0x41, 0x0F, 0x92, 0xC1, 0x49, 0x01, 0xC4, 0x49, 0x11, 0xD7, 0x0F, 0x92, 0xC0,
    0x44, 0x0F, 0xB6, 0xC0] ++ bytes_l1099c0_4

theorem code_l1099c0_3 : ∀ x ∈ codeRange 0x109a8a bytes_l1099c0_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x9a8a 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1099c0_4

@[cfg_block] def b_l1099c0_2 : Block Op Label signature Reg.count 136 :=
  .letOp (n := 136) (.out 0x109a44 (atFlags StatusFlags.CF (adcR64R64Effect 0x109a44 15 0)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 15))) #v[129, 131, 134]
    (.letOp (n := 137) (.exec 0x109a44 (fun s => s.RIP = 0x109a44) (atFlags StatusFlags.CF (adcR64R64Effect 0x109a44 15 0)) (Reg.operands [.gpr 15, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[129, 131, 134]
    (.letOp (n := 138) (.out 0x109a47 (xorR32R32Effect 0x109a47 3 9 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 9] []) (.reg (.gpr 9))) #v[122, 122]
    (.letOp (n := 139) (.exec 0x109a47 (fun s => s.RIP = 0x109a47) (xorR32R32Effect 0x109a47 3 9 9) (Reg.operands [.gpr 9, .gpr 9] [])) #v[122, 122]
    (.letOp (n := 140) (.out 0x109a4a (cmpR64R64Effect 0x109a4a 15 0) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 0] []) (.flag .CF)) #v[136, 131]
    (.letOp (n := 141) (.exec 0x109a4a (fun s => s.RIP = 0x109a4a) (cmpR64R64Effect 0x109a4a 15 0) (Reg.operands [.gpr 15, .gpr 0] [])) #v[136, 131]
    (.letOp (n := 142) (.out 0x109a4d (atFlags (condHolds 2) (setccR8Effect 0x109a4d 4 9)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[138, 140]
    (.letOp (n := 143) (.exec 0x109a4d (fun s => s.RIP = 0x109a4d) (atFlags (condHolds 2) (setccR8Effect 0x109a4d 4 9)) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[138, 140]
    (.letOp (n := 144) (.out 0x109a51 (movR64R64Effect 0x109a51 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[76]
    (.letOp (n := 145) (.exec 0x109a51 (fun s => s.RIP = 0x109a51) (movR64R64Effect 0x109a51 0 13) (Reg.operands [.gpr 13] [])) #v[76]
    (.letOp (n := 146) (.out 0x109a54 (movR64R64Effect 0x109a54 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 13] []) (.reg (.gpr 1))) #v[76]
    (.letOp (n := 147) (.exec 0x109a54 (fun s => s.RIP = 0x109a54) (movR64R64Effect 0x109a54 1 13) (Reg.operands [.gpr 13] [])) #v[76]
    (.letOp (n := 148) (.exec 0x109a57 (StorePre 0x109a57 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x109a57 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109a57 13 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[76, 65]
    (.letOp (n := 149) (.out 0x109a5c (mulR64Effect 0x109a5c 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[95, 144]
    (.letOp (n := 150) (.out 0x109a5c (mulR64Effect 0x109a5c 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[95, 144]
    (.letOp (n := 151) (.exec 0x109a5c (fun s => s.RIP = 0x109a5c) (mulR64Effect 0x109a5c 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[95, 144]
    (.letOp (n := 152) (.exec 0x109a5f (StorePre 0x109a5f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x109a5f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109a5f 11 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[95, 65]
    (.letOp (n := 153) (.out 0x109a64 (movR64R64Effect 0x109a64 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 2] []) (.reg (.gpr 12))) #v[150]
    (.letOp (n := 154) (.exec 0x109a64 (fun s => s.RIP = 0x109a64) (movR64R64Effect 0x109a64 12 2) (Reg.operands [.gpr 2] [])) #v[150]
    (.letOp (n := 155) (.out 0x109a67 (movR64R64Effect 0x109a67 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[149]
    (.letOp (n := 156) (.exec 0x109a67 (fun s => s.RIP = 0x109a67) (movR64R64Effect 0x109a67 13 0) (Reg.operands [.gpr 0] [])) #v[149]
    (.letOp (n := 157) (.out 0x109a6a (addR64R64Effect 0x109a6a 13 10) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 10] []) (.reg (.gpr 13))) #v[155, 133]
    (.letOp (n := 158) (.out 0x109a6a (addR64R64Effect 0x109a6a 13 10) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 10] []) (.flag .CF)) #v[155, 133]
    (.letOp (n := 159) (.exec 0x109a6a (fun s => s.RIP = 0x109a6a) (addR64R64Effect 0x109a6a 13 10) (Reg.operands [.gpr 13, .gpr 10] [])) #v[155, 133]
    (.letOp (n := 160) (.out 0x109a6d (movR64M64Effect 0x109a6d 0 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 161) (.exec 0x109a6d (LoadPre 0x109a6d (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x109a6d + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109a6d 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 162) (.out 0x109a71 (movR64M64Effect 0x109a71 2 (.base 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0] []) (.reg (.gpr 2))) #v[160]
    (.letOp (n := 163) (.exec 0x109a71 (LoadPre 0x109a71 (fun s => AddrMode.addr (.base 0 (.d8 0x10)) s (0x109a71 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109a71 2 (.base 0 (.d8 0x10))) (Reg.operands [.gpr 0] [])) #v[160]
    (.letOp (n := 164) (.exec 0x109a75 (StorePre 0x109a75 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109a75 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109a75 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[162, 65]
    (.letOp (n := 165) (.out 0x109a7a (atFlags StatusFlags.CF (adcR64R64Effect 0x109a7a 12 15)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 12))) #v[153, 136, 158]
    (.letOp (n := 166) (.out 0x109a7a (atFlags StatusFlags.CF (adcR64R64Effect 0x109a7a 12 15)) (Reg.operands [.gpr 12, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[153, 136, 158]
    (.letOp (n := 167) (.exec 0x109a7a (fun s => s.RIP = 0x109a7a) (atFlags StatusFlags.CF (adcR64R64Effect 0x109a7a 12 15)) (Reg.operands [.gpr 12, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[153, 136, 158]
    (.letOp (n := 168) (.out 0x109a7d (atFlags (condHolds 2) (setccR8Effect 0x109a7d 4 10)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[133, 166]
    (.letOp (n := 169) (.exec 0x109a7d (fun s => s.RIP = 0x109a7d) (atFlags (condHolds 2) (setccR8Effect 0x109a7d 4 10)) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[133, 166]
    (.letOp (n := 170) (.out 0x109a81 (movR64R64Effect 0x109a81 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[74]
    (.letOp (n := 171) (.exec 0x109a81 (fun s => s.RIP = 0x109a81) (movR64R64Effect 0x109a81 0 6) (Reg.operands [.gpr 6] [])) #v[74]
    (.letOp (n := 172) (.out 0x109a84 (mulR64Effect 0x109a84 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[162, 170]
    (.letOp (n := 173) (.out 0x109a84 (mulR64Effect 0x109a84 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[162, 170]
    (.letOp (n := 174) (.exec 0x109a84 (fun s => s.RIP = 0x109a84) (mulR64Effect 0x109a84 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[162, 170]
    (.letOp (n := 175) (.out 0x109a87 (movR64R64Effect 0x109a87 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[173]
    (.letOp (n := 176) (.exec 0x109a87 (fun s => s.RIP = 0x109a87) (movR64R64Effect 0x109a87 5 2) (Reg.operands [.gpr 2] [])) #v[173]
    (b_l1099c0_3)))))))))))))))))))))))))))))))))))))))))

def bytes_l1099c0_2 : List UInt8 :=
  [0x49, 0x11, 0xC7, 0x45, 0x31, 0xC9, 0x49, 0x39, 0xC7, 0x41, 0x0F, 0x92, 0xC1, 0x4C, 0x89, 0xE8,
    0x4C, 0x89, 0xE9, 0x4C, 0x89, 0x6C, 0x24, 0x20, 0x49, 0xF7, 0xE3, 0x4C, 0x89, 0x5C, 0x24, 0x18,
    0x49, 0x89, 0xD4, 0x49, 0x89, 0xC5, 0x4D, 0x01, 0xD5, 0x48, 0x8B, 0x04, 0x24, 0x48, 0x8B, 0x50,
    0x10, 0x48, 0x89, 0x54, 0x24, 0x08, 0x4D, 0x11, 0xFC, 0x41, 0x0F, 0x92, 0xC2, 0x48, 0x89, 0xF0,
    0x48, 0xF7, 0xE2, 0x48, 0x89, 0xD5] ++ bytes_l1099c0_3

theorem code_l1099c0_2 : ∀ x ∈ codeRange 0x109a44 bytes_l1099c0_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x9a44 70 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1099c0_3

@[cfg_block] def b_l1099c0_1 : Block Op Label signature Reg.count 93 :=
  .letOp (n := 93) (.out 0x1099fc (movR64R64Effect 0x1099fc 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[89]
    (.letOp (n := 94) (.exec 0x1099fc (fun s => s.RIP = 0x1099fc) (movR64R64Effect 0x1099fc 15 2) (Reg.operands [.gpr 2] [])) #v[89]
    (.letOp (n := 95) (.out 0x1099ff (movR64M64Effect 0x1099ff 11 (.base 11 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11] []) (.reg (.gpr 11))) #v[71]
    (.letOp (n := 96) (.exec 0x1099ff (LoadPre 0x1099ff (fun s => AddrMode.addr (.base 11 (.d8 0x8)) s (0x1099ff + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1099ff 11 (.base 11 (.d8 0x8))) (Reg.operands [.gpr 11] [])) #v[71]
    (.letOp (n := 97) (.out 0x109a03 (leaR64Effect 0x109a03 3 (.sib 9 (some 0) 0 .none)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 9, .gpr 0] []) (.reg (.gpr 3))) #v[83, 88]
    (.letOp (n := 98) (.exec 0x109a03 (fun s => s.RIP = 0x109a03) (leaR64Effect 0x109a03 3 (.sib 9 (some 0) 0 .none)) (Reg.operands [.gpr 9, .gpr 0] [])) #v[83, 88]
    (.letOp (n := 99) (.out 0x109a07 (movR64R64Effect 0x109a07 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[74]
    (.letOp (n := 100) (.exec 0x109a07 (fun s => s.RIP = 0x109a07) (movR64R64Effect 0x109a07 0 6) (Reg.operands [.gpr 6] [])) #v[74]
    (.letOp (n := 101) (.exec 0x109a0a (StorePre 0x109a0a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x109a0a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109a0a 6 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[74, 65]
    (.letOp (n := 102) (.out 0x109a0f (mulR64Effect 0x109a0f 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[95, 99]
    (.letOp (n := 103) (.out 0x109a0f (mulR64Effect 0x109a0f 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[95, 99]
    (.letOp (n := 104) (.exec 0x109a0f (fun s => s.RIP = 0x109a0f) (mulR64Effect 0x109a0f 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[95, 99]
    (.letOp (n := 105) (.out 0x109a12 (movR64R64Effect 0x109a12 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 2] []) (.reg (.gpr 12))) #v[103]
    (.letOp (n := 106) (.exec 0x109a12 (fun s => s.RIP = 0x109a12) (movR64R64Effect 0x109a12 12 2) (Reg.operands [.gpr 2] [])) #v[103]
    (.letOp (n := 107) (.out 0x109a15 (addR64R64Effect 0x109a15 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[102, 97]
    (.letOp (n := 108) (.out 0x109a15 (addR64R64Effect 0x109a15 0 3) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 3] []) (.flag .CF)) #v[102, 97]
    (.letOp (n := 109) (.exec 0x109a15 (fun s => s.RIP = 0x109a15) (addR64R64Effect 0x109a15 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[102, 97]
    (.letOp (n := 110) (.exec 0x109a18 (StorePre 0x109a18 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x109a18 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109a18 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[107, 65]
    (.letOp (n := 111) (.out 0x109a1d (atFlags StatusFlags.CF (adcR64Imm8Effect 0x109a1d 12 0x0)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 12))) #v[105, 108]
    (.letOp (n := 112) (.exec 0x109a1d (fun s => s.RIP = 0x109a1d) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x109a1d 12 0x0)) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[105, 108]
    (.letOp (n := 113) (.out 0x109a21 (addR64R64Effect 0x109a21 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[83, 91]
    (.letOp (n := 114) (.out 0x109a21 (addR64R64Effect 0x109a21 9 10) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 10] []) (.flag .CF)) #v[83, 91]
    (.letOp (n := 115) (.exec 0x109a21 (fun s => s.RIP = 0x109a21) (addR64R64Effect 0x109a21 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[83, 91]
    (.letOp (n := 116) (.out 0x109a24 (movR64M64Effect 0x109a24 0 (.base 14 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[67]
    (.letOp (n := 117) (.exec 0x109a24 (LoadPre 0x109a24 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x109a24 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109a24 0 (.base 14 (.d8 0x10))) (Reg.operands [.gpr 14] [])) #v[67]
    (.letOp (n := 118) (.exec 0x109a28 (StorePre 0x109a28 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x109a28 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109a28 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[116, 65]
    (.letOp (n := 119) (.out 0x109a2d (atFlags StatusFlags.CF (adcR64R64Effect 0x109a2d 12 15)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 12))) #v[111, 93, 114]
    (.letOp (n := 120) (.out 0x109a2d (atFlags StatusFlags.CF (adcR64R64Effect 0x109a2d 12 15)) (Reg.operands [.gpr 12, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[111, 93, 114]
    (.letOp (n := 121) (.exec 0x109a2d (fun s => s.RIP = 0x109a2d) (atFlags StatusFlags.CF (adcR64R64Effect 0x109a2d 12 15)) (Reg.operands [.gpr 12, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[111, 93, 114]
    (.letOp (n := 122) (.out 0x109a30 (atFlags (condHolds 2) (setccR8Effect 0x109a30 4 9)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[113, 120]
    (.letOp (n := 123) (.exec 0x109a30 (fun s => s.RIP = 0x109a30) (atFlags (condHolds 2) (setccR8Effect 0x109a30 4 9)) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[113, 120]
    (.letOp (n := 124) (.out 0x109a34 (mulR64Effect 0x109a34 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[69, 116]
    (.letOp (n := 125) (.out 0x109a34 (mulR64Effect 0x109a34 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[69, 116]
    (.letOp (n := 126) (.exec 0x109a34 (fun s => s.RIP = 0x109a34) (mulR64Effect 0x109a34 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[69, 116]
    (.letOp (n := 127) (.out 0x109a37 (movR64R64Effect 0x109a37 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[124]
    (.letOp (n := 128) (.exec 0x109a37 (fun s => s.RIP = 0x109a37) (movR64R64Effect 0x109a37 10 0) (Reg.operands [.gpr 0] [])) #v[124]
    (.letOp (n := 129) (.out 0x109a3a (movR64R64Effect 0x109a3a 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[125]
    (.letOp (n := 130) (.exec 0x109a3a (fun s => s.RIP = 0x109a3a) (movR64R64Effect 0x109a3a 15 2) (Reg.operands [.gpr 2] [])) #v[125]
    (.letOp (n := 131) (.out 0x109a3d (movzxR32R8Effect 0x109a3d 4 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[122]
    (.letOp (n := 132) (.exec 0x109a3d (fun s => s.RIP = 0x109a3d) (movzxR32R8Effect 0x109a3d 4 0 9) (Reg.operands [.gpr 9] [])) #v[122]
    (.letOp (n := 133) (.out 0x109a41 (addR64R64Effect 0x109a41 10 12) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 12] []) (.reg (.gpr 10))) #v[127, 119]
    (.letOp (n := 134) (.out 0x109a41 (addR64R64Effect 0x109a41 10 12) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 12] []) (.flag .CF)) #v[127, 119]
    (.letOp (n := 135) (.exec 0x109a41 (fun s => s.RIP = 0x109a41) (addR64R64Effect 0x109a41 10 12) (Reg.operands [.gpr 10, .gpr 12] [])) #v[127, 119]
    (b_l1099c0_2)))))))))))))))))))))))))))))))))))))))))))

def bytes_l1099c0_1 : List UInt8 :=
  [0x49, 0x89, 0xD7, 0x4D, 0x8B, 0x5B, 0x08, 0x49, 0x8D, 0x1C, 0x01, 0x48, 0x89, 0xF0, 0x48, 0x89,
    0x74, 0x24, 0x28, 0x49, 0xF7, 0xE3, 0x49, 0x89, 0xD4, 0x48, 0x01, 0xD8, 0x48, 0x89, 0x44, 0x24,
    0x38, 0x49, 0x83, 0xD4, 0x00, 0x4D, 0x01, 0xD1, 0x49, 0x8B, 0x46, 0x10, 0x48, 0x89, 0x44, 0x24,
    0x10, 0x4D, 0x11, 0xFC, 0x41, 0x0F, 0x92, 0xC1, 0x49, 0xF7, 0xE0, 0x49, 0x89, 0xC2, 0x49, 0x89,
    0xD7, 0x41, 0x0F, 0xB6, 0xC1, 0x4D, 0x01, 0xE2] ++ bytes_l1099c0_2

theorem code_l1099c0_1 : ∀ x ∈ codeRange 0x1099fc bytes_l1099c0_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x99fc 72 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1099c0_2

@[cfg_block] def b_l1099c0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1099c0 (pushR64Effect 0x1099c0 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x1099c0 (PushPre 0x1099c0 1) (pushR64Effect 0x1099c0 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x1099c1 (pushR64Effect 0x1099c1 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x1099c1 (PushPre 0x1099c1 2) (pushR64Effect 0x1099c1 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x1099c3 (pushR64Effect 0x1099c3 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x1099c3 (PushPre 0x1099c3 2) (pushR64Effect 0x1099c3 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x1099c5 (pushR64Effect 0x1099c5 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x1099c5 (PushPre 0x1099c5 2) (pushR64Effect 0x1099c5 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x1099c7 (pushR64Effect 0x1099c7 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x1099c7 (PushPre 0x1099c7 2) (pushR64Effect 0x1099c7 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x1099c9 (pushR64Effect 0x1099c9 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x1099c9 (PushPre 0x1099c9 1) (pushR64Effect 0x1099c9 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x1099ca (subR64Imm32Effect 0x1099ca 4 0x88) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x1099ca (fun s => s.RIP = 0x1099ca) (subR64Imm32Effect 0x1099ca 4 0x88) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x1099d1 (movR64R64Effect 0x1099d1 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[2]
    (.letOp (n := 68) (.exec 0x1099d1 (fun s => s.RIP = 0x1099d1) (movR64R64Effect 0x1099d1 14 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 69) (.out 0x1099d4 (movR64M64Effect 0x1099d4 8 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 6] []) (.reg (.gpr 8))) #v[6]
    (.letOp (n := 70) (.exec 0x1099d4 (LoadPre 0x1099d4 (fun s => AddrMode.addr (.base 6 .none) s (0x1099d4 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1099d4 8 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 71) (.out 0x1099d7 (movR64R64Effect 0x1099d7 11 6) (EffectPart.reads (.reg (.gpr 11)) [.gpr 6] []) (.reg (.gpr 11))) #v[6]
    (.letOp (n := 72) (.exec 0x1099d7 (fun s => s.RIP = 0x1099d7) (movR64R64Effect 0x1099d7 11 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 73) (.exec 0x1099da (StorePre 0x1099da 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1099da + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1099da 6 (.sib 4 none 0 .none)) (Reg.operands [.gpr 6, .gpr 4] [])) #v[6, 65]
    (.letOp (n := 74) (.out 0x1099de (movR64M64Effect 0x1099de 6 (.base 2 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[2]
    (.letOp (n := 75) (.exec 0x1099de (LoadPre 0x1099de (fun s => AddrMode.addr (.base 2 .none) s (0x1099de + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1099de 6 (.base 2 .none)) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 76) (.out 0x1099e1 (movR64M64Effect 0x1099e1 13 (.base 2 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[2]
    (.letOp (n := 77) (.exec 0x1099e1 (LoadPre 0x1099e1 (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x1099e1 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1099e1 13 (.base 2 (.d8 0x8))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 78) (.out 0x1099e5 (movR64R64Effect 0x1099e5 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[74]
    (.letOp (n := 79) (.exec 0x1099e5 (fun s => s.RIP = 0x1099e5) (movR64R64Effect 0x1099e5 0 6) (Reg.operands [.gpr 6] [])) #v[74]
    (.letOp (n := 80) (.out 0x1099e8 (mulR64Effect 0x1099e8 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[69, 78]
    (.letOp (n := 81) (.out 0x1099e8 (mulR64Effect 0x1099e8 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[69, 78]
    (.letOp (n := 82) (.exec 0x1099e8 (fun s => s.RIP = 0x1099e8) (mulR64Effect 0x1099e8 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[69, 78]
    (.letOp (n := 83) (.out 0x1099eb (movR64R64Effect 0x1099eb 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[81]
    (.letOp (n := 84) (.exec 0x1099eb (fun s => s.RIP = 0x1099eb) (movR64R64Effect 0x1099eb 9 2) (Reg.operands [.gpr 2] [])) #v[81]
    (.letOp (n := 85) (.exec 0x1099ee (StorePre 0x1099ee 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1099ee + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1099ee 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[80, 65]
    (.letOp (n := 86) (.out 0x1099f3 (movR64R64Effect 0x1099f3 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[76]
    (.letOp (n := 87) (.exec 0x1099f3 (fun s => s.RIP = 0x1099f3) (movR64R64Effect 0x1099f3 0 13) (Reg.operands [.gpr 13] [])) #v[76]
    (.letOp (n := 88) (.out 0x1099f6 (mulR64Effect 0x1099f6 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[69, 86]
    (.letOp (n := 89) (.out 0x1099f6 (mulR64Effect 0x1099f6 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[69, 86]
    (.letOp (n := 90) (.exec 0x1099f6 (fun s => s.RIP = 0x1099f6) (mulR64Effect 0x1099f6 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[69, 86]
    (.letOp (n := 91) (.out 0x1099f9 (movR64R64Effect 0x1099f9 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[88]
    (.letOp (n := 92) (.exec 0x1099f9 (fun s => s.RIP = 0x1099f9) (movR64R64Effect 0x1099f9 10 0) (Reg.operands [.gpr 0] [])) #v[88]
    (b_l1099c0_1))))))))))))))))))))))))))))))))))))))))

def bytes_l1099c0 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0x88, 0x00, 0x00,
    0x00, 0x49, 0x89, 0xD6, 0x4C, 0x8B, 0x06, 0x49, 0x89, 0xF3, 0x48, 0x89, 0x34, 0x24, 0x48, 0x8B,
    0x32, 0x4C, 0x8B, 0x6A, 0x08, 0x48, 0x89, 0xF0, 0x49, 0xF7, 0xE0, 0x49, 0x89, 0xD1, 0x48, 0x89,
    0x44, 0x24, 0x40, 0x4C, 0x89, 0xE8, 0x49, 0xF7, 0xE0, 0x49, 0x89, 0xC2] ++ bytes_l1099c0_1

theorem code_l1099c0 : ∀ x ∈ codeRange 0x1099c0 bytes_l1099c0, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x99c0 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1099c0_1

@[cfg_block] def b_l109be7 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x109be7 (movR64R64Effect 0x109be7 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[14]
    (.letOp (n := 54) (.exec 0x109be7 (fun s => s.RIP = 0x109be7) (movR64R64Effect 0x109be7 0 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 55) (.out 0x109bea (addR64Imm32Effect 0x109bea 4 0x88) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 56) (.exec 0x109bea (fun s => s.RIP = 0x109bea) (addR64Imm32Effect 0x109bea 4 0x88) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x109bf1 (popR64Effect 0x109bf1 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[55]
    (.letOp (n := 58) (.out 0x109bf1 (popR64Effect 0x109bf1 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[55]
    (.letOp (n := 59) (.exec 0x109bf1 (PopPre 0x109bf1) (popR64Effect 0x109bf1 1 3) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 60) (.out 0x109bf2 (popR64Effect 0x109bf2 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[58]
    (.letOp (n := 61) (.out 0x109bf2 (popR64Effect 0x109bf2 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[58]
    (.letOp (n := 62) (.exec 0x109bf2 (PopPre 0x109bf2) (popR64Effect 0x109bf2 2 12) (Reg.operands [.gpr 4] [])) #v[58]
    (.letOp (n := 63) (.out 0x109bf4 (popR64Effect 0x109bf4 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[61]
    (.letOp (n := 64) (.out 0x109bf4 (popR64Effect 0x109bf4 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 65) (.exec 0x109bf4 (PopPre 0x109bf4) (popR64Effect 0x109bf4 2 13) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 66) (.out 0x109bf6 (popR64Effect 0x109bf6 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[64]
    (.letOp (n := 67) (.out 0x109bf6 (popR64Effect 0x109bf6 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[64]
    (.letOp (n := 68) (.exec 0x109bf6 (PopPre 0x109bf6) (popR64Effect 0x109bf6 2 14) (Reg.operands [.gpr 4] [])) #v[64]
    (.letOp (n := 69) (.out 0x109bf8 (popR64Effect 0x109bf8 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[67]
    (.letOp (n := 70) (.out 0x109bf8 (popR64Effect 0x109bf8 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[67]
    (.letOp (n := 71) (.exec 0x109bf8 (PopPre 0x109bf8) (popR64Effect 0x109bf8 2 15) (Reg.operands [.gpr 4] [])) #v[67]
    (.letOp (n := 72) (.out 0x109bfa (popR64Effect 0x109bfa 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[70]
    (.letOp (n := 73) (.out 0x109bfa (popR64Effect 0x109bfa 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[70]
    (.letOp (n := 74) (.exec 0x109bfa (PopPre 0x109bfa) (popR64Effect 0x109bfa 1 5) (Reg.operands [.gpr 4] [])) #v[70]
    (.letOp (n := 75) (.out 0x109bfb (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[73]
    (.letOp (n := 76) (.out 0x109bfb (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[73]
    (.letOp (n := 77) (.exec 0x109bfb (RetPre 0x109bfb) (retEffect) (Reg.operands [.gpr 4] [])) #v[73]
    (.terminate (.ret (RegMap.args [(0, 53), (1, 1), (2, 2), (3, 57), (4, 76), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 78) (some ⟨75, by decide⟩)))))))))))))))))))))))))))

def bytes_l109be7 : List UInt8 :=
  [0x4C, 0x89, 0xF0, 0x48, 0x81, 0xC4, 0x88, 0x00, 0x00, 0x00, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41,
    0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l109be7 : ∀ x ∈ codeRange 0x109be7 bytes_l109be7, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9be7 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109c00_5 : Block Op Label signature Reg.count 243 :=
  .letOp (n := 243) (.out 0x109d52 (andR64R64Effect 0x109d52 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 15] []) (.reg (.gpr 2))) #v[241, 239]
    (.letOp (n := 244) (.exec 0x109d52 (fun s => s.RIP = 0x109d52) (andR64R64Effect 0x109d52 2 15) (Reg.operands [.gpr 2, .gpr 15] [])) #v[241, 239]
    (.letOp (n := 245) (.out 0x109d55 (xorR64R64Effect 0x109d55 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[243, 71]
    (.letOp (n := 246) (.exec 0x109d55 (fun s => s.RIP = 0x109d55) (xorR64R64Effect 0x109d55 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[243, 71]
    (.letOp (n := 247) (.exec 0x109d58 (StorePre 0x109d58 3 (fun s => AddrMode.addr (.base 7 .none) s (0x109d58 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x109d58 1 (.base 7 .none)) (Reg.operands [.gpr 1, .gpr 7] [])) #v[212, 7]
    (.letOp (n := 248) (.exec 0x109d5b (StorePre 0x109d5b 4 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x109d5b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x109d5b 10 (.base 7 (.d8 0x8))) (Reg.operands [.gpr 10, .gpr 7] [])) #v[223, 7]
    (.letOp (n := 249) (.exec 0x109d5f (StorePre 0x109d5f 4 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x109d5f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x109d5f 6 (.base 7 (.d8 0x10))) (Reg.operands [.gpr 6, .gpr 7] [])) #v[234, 7]
    (.letOp (n := 250) (.exec 0x109d63 (StorePre 0x109d63 4 (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x109d63 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x109d63 2 (.base 7 (.d8 0x18))) (Reg.operands [.gpr 2, .gpr 7] [])) #v[245, 7]
    (.letOp (n := 251) (.out 0x109d67 (addR64Imm8Effect 0x109d67 4 0x10) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 252) (.exec 0x109d67 (fun s => s.RIP = 0x109d67) (addR64Imm8Effect 0x109d67 4 0x10) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 253) (.out 0x109d6b (popR64Effect 0x109d6b 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[251]
    (.letOp (n := 254) (.out 0x109d6b (popR64Effect 0x109d6b 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[251]
    (.letOp (n := 255) (.exec 0x109d6b (PopPre 0x109d6b) (popR64Effect 0x109d6b 1 3) (Reg.operands [.gpr 4] [])) #v[251]
    (.letOp (n := 256) (.out 0x109d6c (popR64Effect 0x109d6c 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[254]
    (.letOp (n := 257) (.out 0x109d6c (popR64Effect 0x109d6c 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[254]
    (.letOp (n := 258) (.exec 0x109d6c (PopPre 0x109d6c) (popR64Effect 0x109d6c 2 12) (Reg.operands [.gpr 4] [])) #v[254]
    (.letOp (n := 259) (.out 0x109d6e (popR64Effect 0x109d6e 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[257]
    (.letOp (n := 260) (.out 0x109d6e (popR64Effect 0x109d6e 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[257]
    (.letOp (n := 261) (.exec 0x109d6e (PopPre 0x109d6e) (popR64Effect 0x109d6e 2 13) (Reg.operands [.gpr 4] [])) #v[257]
    (.letOp (n := 262) (.out 0x109d70 (popR64Effect 0x109d70 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[260]
    (.letOp (n := 263) (.out 0x109d70 (popR64Effect 0x109d70 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[260]
    (.letOp (n := 264) (.exec 0x109d70 (PopPre 0x109d70) (popR64Effect 0x109d70 2 14) (Reg.operands [.gpr 4] [])) #v[260]
    (.letOp (n := 265) (.out 0x109d72 (popR64Effect 0x109d72 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[263]
    (.letOp (n := 266) (.out 0x109d72 (popR64Effect 0x109d72 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[263]
    (.letOp (n := 267) (.exec 0x109d72 (PopPre 0x109d72) (popR64Effect 0x109d72 2 15) (Reg.operands [.gpr 4] [])) #v[263]
    (.letOp (n := 268) (.out 0x109d74 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[266]
    (.letOp (n := 269) (.out 0x109d74 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[266]
    (.letOp (n := 270) (.exec 0x109d74 (RetPre 0x109d74) (retEffect) (Reg.operands [.gpr 4] [])) #v[266]
    (.terminate (.ret (RegMap.args [(0, 71), (1, 212), (2, 245), (3, 253), (4, 269), (5, 5), (6, 234), (7, 7), (8, 69), (9, 67), (10, 223), (11, 206), (12, 256), (13, 259), (14, 262), (15, 265), (22, 22), (39, 39), (50, 50), (51, 51)] 271) (some ⟨268, by decide⟩))))))))))))))))))))))))))))))

def bytes_l109c00_5 : List UInt8 :=
  [0x4C, 0x21, 0xFA, 0x48, 0x31, 0xC2, 0x48, 0x89, 0x0F, 0x4C, 0x89, 0x57, 0x08, 0x48, 0x89, 0x77,
    0x10, 0x48, 0x89, 0x57, 0x18, 0x48, 0x83, 0xC4, 0x10, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E,
    0x41, 0x5F, 0xC3]

theorem code_l109c00_5 : ∀ x ∈ codeRange 0x109d52 bytes_l109c00_5, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9d52 35 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109c00_4 : Block Op Label signature Reg.count 206 :=
  .letOp (n := 206) (.out 0x109d0c (xorR64R64Effect 0x109d0c 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 10] []) (.reg (.gpr 11))) #v[77, 65]
    (.letOp (n := 207) (.exec 0x109d0c (fun s => s.RIP = 0x109d0c) (xorR64R64Effect 0x109d0c 11 10) (Reg.operands [.gpr 11, .gpr 10] [])) #v[77, 65]
    (.letOp (n := 208) (.out 0x109d0f (negR64Effect 0x109d0f 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[204]
    (.letOp (n := 209) (.exec 0x109d0f (fun s => s.RIP = 0x109d0f) (negR64Effect 0x109d0f 1) (Reg.operands [.gpr 1] [])) #v[204]
    (.letOp (n := 210) (.out 0x109d12 (andR64R64Effect 0x109d12 1 11) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 11] []) (.reg (.gpr 1))) #v[208, 206]
    (.letOp (n := 211) (.exec 0x109d12 (fun s => s.RIP = 0x109d12) (andR64R64Effect 0x109d12 1 11) (Reg.operands [.gpr 1, .gpr 11] [])) #v[208, 206]
    (.letOp (n := 212) (.out 0x109d15 (xorR64R64Effect 0x109d15 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10] []) (.reg (.gpr 1))) #v[210, 65]
    (.letOp (n := 213) (.exec 0x109d15 (fun s => s.RIP = 0x109d15) (xorR64R64Effect 0x109d15 1 10) (Reg.operands [.gpr 1, .gpr 10] [])) #v[210, 65]
    (.letOp (n := 214) (.exec 0x109d18 (StorePre 0x109d18 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x109d18 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109d18 4 2 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[200, 63]
    (.letOp (n := 215) (.out 0x109d1c (movzxR32M8Effect 0x109d1c 6 10 (.sib 4 none 0 (.d8 0x7))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[63]
    (.letOp (n := 216) (.exec 0x109d1c (LoadPre 0x109d1c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x109d1c + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x109d1c 6 10 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 217) (.out 0x109d22 (xorR64R64Effect 0x109d22 6 9) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 9] []) (.reg (.gpr 6))) #v[111, 67]
    (.letOp (n := 218) (.exec 0x109d22 (fun s => s.RIP = 0x109d22) (xorR64R64Effect 0x109d22 6 9) (Reg.operands [.gpr 6, .gpr 9] [])) #v[111, 67]
    (.letOp (n := 219) (.out 0x109d25 (negR64Effect 0x109d25 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[215]
    (.letOp (n := 220) (.exec 0x109d25 (fun s => s.RIP = 0x109d25) (negR64Effect 0x109d25 10) (Reg.operands [.gpr 10] [])) #v[215]
    (.letOp (n := 221) (.out 0x109d28 (andR64R64Effect 0x109d28 10 6) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 6] []) (.reg (.gpr 10))) #v[219, 217]
    (.letOp (n := 222) (.exec 0x109d28 (fun s => s.RIP = 0x109d28) (andR64R64Effect 0x109d28 10 6) (Reg.operands [.gpr 10, .gpr 6] [])) #v[219, 217]
    (.letOp (n := 223) (.out 0x109d2b (xorR64R64Effect 0x109d2b 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9] []) (.reg (.gpr 10))) #v[221, 67]
    (.letOp (n := 224) (.exec 0x109d2b (fun s => s.RIP = 0x109d2b) (xorR64R64Effect 0x109d2b 10 9) (Reg.operands [.gpr 10, .gpr 9] [])) #v[221, 67]
    (.letOp (n := 225) (.exec 0x109d2e (StorePre 0x109d2e 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x109d2e + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109d2e 4 2 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[200, 63]
    (.letOp (n := 226) (.out 0x109d32 (movzxR32M8Effect 0x109d32 5 6 (.sib 4 none 0 (.d8 0x7))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[63]
    (.letOp (n := 227) (.exec 0x109d32 (LoadPre 0x109d32 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x109d32 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109d32 5 6 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 228) (.out 0x109d37 (xorR64R64Effect 0x109d37 3 8) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 8] []) (.reg (.gpr 3))) #v[140, 69]
    (.letOp (n := 229) (.exec 0x109d37 (fun s => s.RIP = 0x109d37) (xorR64R64Effect 0x109d37 3 8) (Reg.operands [.gpr 3, .gpr 8] [])) #v[140, 69]
    (.letOp (n := 230) (.out 0x109d3a (negR64Effect 0x109d3a 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[226]
    (.letOp (n := 231) (.exec 0x109d3a (fun s => s.RIP = 0x109d3a) (negR64Effect 0x109d3a 6) (Reg.operands [.gpr 6] [])) #v[226]
    (.letOp (n := 232) (.out 0x109d3d (andR64R64Effect 0x109d3d 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 3] []) (.reg (.gpr 6))) #v[230, 228]
    (.letOp (n := 233) (.exec 0x109d3d (fun s => s.RIP = 0x109d3d) (andR64R64Effect 0x109d3d 6 3) (Reg.operands [.gpr 6, .gpr 3] [])) #v[230, 228]
    (.letOp (n := 234) (.out 0x109d40 (xorR64R64Effect 0x109d40 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 8] []) (.reg (.gpr 6))) #v[232, 69]
    (.letOp (n := 235) (.exec 0x109d40 (fun s => s.RIP = 0x109d40) (xorR64R64Effect 0x109d40 6 8) (Reg.operands [.gpr 6, .gpr 8] [])) #v[232, 69]
    (.letOp (n := 236) (.exec 0x109d43 (StorePre 0x109d43 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x109d43 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109d43 4 2 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[200, 63]
    (.letOp (n := 237) (.out 0x109d47 (movzxR32M8Effect 0x109d47 5 2 (.sib 4 none 0 (.d8 0x7))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[63]
    (.letOp (n := 238) (.exec 0x109d47 (LoadPre 0x109d47 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x109d47 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109d47 5 2 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 239) (.out 0x109d4c (xorR64R64Effect 0x109d4c 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 0] []) (.reg (.gpr 15))) #v[171, 71]
    (.letOp (n := 240) (.exec 0x109d4c (fun s => s.RIP = 0x109d4c) (xorR64R64Effect 0x109d4c 15 0) (Reg.operands [.gpr 15, .gpr 0] [])) #v[171, 71]
    (.letOp (n := 241) (.out 0x109d4f (negR64Effect 0x109d4f 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[237]
    (.letOp (n := 242) (.exec 0x109d4f (fun s => s.RIP = 0x109d4f) (negR64Effect 0x109d4f 2) (Reg.operands [.gpr 2] [])) #v[237]
    (b_l109c00_5)))))))))))))))))))))))))))))))))))))

def bytes_l109c00_4 : List UInt8 :=
  [0x4D, 0x31, 0xD3, 0x48, 0xF7, 0xD9, 0x4C, 0x21, 0xD9, 0x4C, 0x31, 0xD1, 0x88, 0x54, 0x24, 0x07,
    0x44, 0x0F, 0xB6, 0x54, 0x24, 0x07, 0x4C, 0x31, 0xCE, 0x49, 0xF7, 0xDA, 0x49, 0x21, 0xF2, 0x4D,
    0x31, 0xCA, 0x88, 0x54, 0x24, 0x07, 0x0F, 0xB6, 0x74, 0x24, 0x07, 0x4C, 0x31, 0xC3, 0x48, 0xF7,
    0xDE, 0x48, 0x21, 0xDE, 0x4C, 0x31, 0xC6, 0x88, 0x54, 0x24, 0x07, 0x0F, 0xB6, 0x54, 0x24, 0x07,
    0x49, 0x31, 0xC7, 0x48, 0xF7, 0xDA] ++ bytes_l109c00_5

theorem code_l109c00_4 : ∀ x ∈ codeRange 0x109d0c bytes_l109c00_4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x9d0c 70 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l109c00_5

@[cfg_block] def b_l109c00_3 : Block Op Label signature Reg.count 169 :=
  .letOp (n := 169) (.out 0x109cc6 (sarR64Effect 0x109cc6 4 15 63) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[161]
    (.letOp (n := 170) (.exec 0x109cc6 (fun s => s.RIP = 0x109cc6) (sarR64Effect 0x109cc6 4 15 63) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[161]
    (.letOp (n := 171) (.out 0x109cca (addR64R64Effect 0x109cca 15 13) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 13] []) (.reg (.gpr 15))) #v[169, 167]
    (.letOp (n := 172) (.exec 0x109cca (fun s => s.RIP = 0x109cca) (addR64R64Effect 0x109cca 15 13) (Reg.operands [.gpr 15, .gpr 13] [])) #v[169, 167]
    (.letOp (n := 173) (.out 0x109ccd (notR64Effect 0x109ccd 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[163]
    (.letOp (n := 174) (.exec 0x109ccd (fun s => s.RIP = 0x109ccd) (notR64Effect 0x109ccd 1) (Reg.operands [.gpr 1] [])) #v[163]
    (.letOp (n := 175) (.out 0x109cd0 (movR64R64Effect 0x109cd0 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[71]
    (.letOp (n := 176) (.exec 0x109cd0 (fun s => s.RIP = 0x109cd0) (movR64R64Effect 0x109cd0 13 0) (Reg.operands [.gpr 0] [])) #v[71]
    (.letOp (n := 177) (.out 0x109cd3 (andR64R64Effect 0x109cd3 13 1) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 1] []) (.reg (.gpr 13))) #v[175, 173]
    (.letOp (n := 178) (.exec 0x109cd3 (fun s => s.RIP = 0x109cd3) (andR64R64Effect 0x109cd3 13 1) (Reg.operands [.gpr 13, .gpr 1] [])) #v[175, 173]
    (.letOp (n := 179) (.out 0x109cd6 (orR64R64Effect 0x109cd6 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[173, 71]
    (.letOp (n := 180) (.exec 0x109cd6 (fun s => s.RIP = 0x109cd6) (orR64R64Effect 0x109cd6 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[173, 71]
    (.letOp (n := 181) (.out 0x109cd9 (andR64R64Effect 0x109cd9 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 15] []) (.reg (.gpr 1))) #v[179, 171]
    (.letOp (n := 182) (.exec 0x109cd9 (fun s => s.RIP = 0x109cd9) (andR64R64Effect 0x109cd9 1 15) (Reg.operands [.gpr 1, .gpr 15] [])) #v[179, 171]
    (.letOp (n := 183) (.out 0x109cdc (orR64R64Effect 0x109cdc 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 13] []) (.reg (.gpr 1))) #v[181, 177]
    (.letOp (n := 184) (.exec 0x109cdc (fun s => s.RIP = 0x109cdc) (orR64R64Effect 0x109cdc 1 13) (Reg.operands [.gpr 1, .gpr 13] [])) #v[181, 177]
    (.letOp (n := 185) (.out 0x109cdf (shrR64Effect 0x109cdf 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[183]
    (.letOp (n := 186) (.exec 0x109cdf (fun s => s.RIP = 0x109cdf) (shrR64Effect 0x109cdf 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[183]
    (.letOp (n := 187) (.exec 0x109ce3 (StorePre 0x109ce3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109ce3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109ce3 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[185, 63]
    (.letOp (n := 188) (.out 0x109ce8 (movR64R64Effect 0x109ce8 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 9] []) (.reg (.gpr 1))) #v[67]
    (.letOp (n := 189) (.exec 0x109ce8 (fun s => s.RIP = 0x109ce8) (movR64R64Effect 0x109ce8 1 9) (Reg.operands [.gpr 9] [])) #v[67]
    (.letOp (n := 190) (.out 0x109ceb (orR64R64Effect 0x109ceb 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10] []) (.reg (.gpr 1))) #v[188, 65]
    (.letOp (n := 191) (.exec 0x109ceb (fun s => s.RIP = 0x109ceb) (orR64R64Effect 0x109ceb 1 10) (Reg.operands [.gpr 1, .gpr 10] [])) #v[188, 65]
    (.letOp (n := 192) (.out 0x109cee (orR64R64Effect 0x109cee 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8] []) (.reg (.gpr 1))) #v[190, 69]
    (.letOp (n := 193) (.exec 0x109cee (fun s => s.RIP = 0x109cee) (orR64R64Effect 0x109cee 1 8) (Reg.operands [.gpr 1, .gpr 8] [])) #v[190, 69]
    (.letOp (n := 194) (.out 0x109cf1 (andR8Imm8Effect 0x109cf1 3 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[93]
    (.letOp (n := 195) (.exec 0x109cf1 (fun s => s.RIP = 0x109cf1) (andR8Imm8Effect 0x109cf1 3 2 0x1) (Reg.operands [.gpr 2] [])) #v[93]
    (.letOp (n := 196) (.out 0x109cf4 (orR64R64Effect 0x109cf4 1 0) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 0] []) (.flag .ZF)) #v[192, 71]
    (.letOp (n := 197) (.exec 0x109cf4 (fun s => s.RIP = 0x109cf4) (orR64R64Effect 0x109cf4 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[192, 71]
    (.letOp (n := 198) (.out 0x109cf7 (movzxR32R8Effect 0x109cf7 3 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[194]
    (.letOp (n := 199) (.exec 0x109cf7 (fun s => s.RIP = 0x109cf7) (movzxR32R8Effect 0x109cf7 3 2 2) (Reg.operands [.gpr 2] [])) #v[194]
    (.letOp (n := 200) (.out 0x109cfa (atFlags (condHolds 4) (cmovR32R32Effect 0x109cfa 4 2 14)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 2))) #v[198, 97, 196]
    (.letOp (n := 201) (.exec 0x109cfa (fun s => s.RIP = 0x109cfa) (atFlags (condHolds 4) (cmovR32R32Effect 0x109cfa 4 2 14)) (Reg.operands [.gpr 2, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[198, 97, 196]
    (.letOp (n := 202) (.exec 0x109cfe (StorePre 0x109cfe 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x109cfe + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109cfe 4 2 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[200, 63]
    (.letOp (n := 203) (.exec 0x109d02 (fun s => s.RIP = 0x109d02) (leaR64Effect 0x109d02 14 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 204) (.out 0x109d07 (movzxR32M8Effect 0x109d07 5 1 (.sib 4 none 0 (.d8 0x7))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[63]
    (.letOp (n := 205) (.exec 0x109d07 (LoadPre 0x109d07 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x109d07 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109d07 5 1 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 4] [])) #v[63]
    (b_l109c00_4)))))))))))))))))))))))))))))))))))))

def bytes_l109c00_3 : List UInt8 :=
  [0x49, 0xC1, 0xFF, 0x3F, 0x4D, 0x01, 0xEF, 0x48, 0xF7, 0xD1, 0x49, 0x89, 0xC5, 0x49, 0x21, 0xCD,
    0x48, 0x09, 0xC1, 0x4C, 0x21, 0xF9, 0x4C, 0x09, 0xE9, 0x48, 0xC1, 0xE9, 0x3F, 0x48, 0x89, 0x4C,
    0x24, 0x08, 0x4C, 0x89, 0xC9, 0x4C, 0x09, 0xD1, 0x4C, 0x09, 0xC1, 0x80, 0xE2, 0x01, 0x48, 0x09,
    0xC1, 0x0F, 0xB6, 0xD2, 0x41, 0x0F, 0x44, 0xD6, 0x88, 0x54, 0x24, 0x07, 0x4C, 0x8D, 0x74, 0x24,
    0x07, 0x0F, 0xB6, 0x4C, 0x24, 0x07] ++ bytes_l109c00_4

theorem code_l109c00_3 : ∀ x ∈ codeRange 0x109cc6 bytes_l109c00_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x9cc6 70 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l109c00_4

@[cfg_block] def b_l109c00_2 : Block Op Label signature Reg.count 130 :=
  .letOp (n := 130) (.out 0x109c80 (subR64M64Effect 0x109c80 3 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 4] []) (.reg (.gpr 3))) #v[128, 63]
    (.letOp (n := 131) (.exec 0x109c80 (LoadPre 0x109c80 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109c80 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x109c80 3 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[128, 63]
    (.letOp (n := 132) (.out 0x109c85 (movR64M64Effect 0x109c85 15 (.base 1 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 1] []) (.reg (.gpr 15))) #v[1]
    (.letOp (n := 133) (.exec 0x109c85 (LoadPre 0x109c85 (fun s => AddrMode.addr (.base 1 (.d8 0x10)) s (0x109c85 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109c85 15 (.base 1 (.d8 0x10))) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 134) (.out 0x109c89 (movR64R64Effect 0x109c89 13 15) (EffectPart.reads (.reg (.gpr 13)) [.gpr 15] []) (.reg (.gpr 13))) #v[132]
    (.letOp (n := 135) (.exec 0x109c89 (fun s => s.RIP = 0x109c89) (movR64R64Effect 0x109c89 13 15) (Reg.operands [.gpr 15] [])) #v[132]
    (.letOp (n := 136) (.out 0x109c8c (subR64R64Effect 0x109c8c 13 8) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 8] []) (.reg (.gpr 13))) #v[134, 69]
    (.letOp (n := 137) (.exec 0x109c8c (fun s => s.RIP = 0x109c8c) (subR64R64Effect 0x109c8c 13 8) (Reg.operands [.gpr 13, .gpr 8] [])) #v[134, 69]
    (.letOp (n := 138) (.out 0x109c8f (sarR64Effect 0x109c8f 4 3 63) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[130]
    (.letOp (n := 139) (.exec 0x109c8f (fun s => s.RIP = 0x109c8f) (sarR64Effect 0x109c8f 4 3 63) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[130]
    (.letOp (n := 140) (.out 0x109c93 (addR64R64Effect 0x109c93 3 13) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 13] []) (.reg (.gpr 3))) #v[138, 136]
    (.letOp (n := 141) (.exec 0x109c93 (fun s => s.RIP = 0x109c93) (addR64R64Effect 0x109c93 3 13) (Reg.operands [.gpr 3, .gpr 13] [])) #v[138, 136]
    (.letOp (n := 142) (.out 0x109c96 (notR64Effect 0x109c96 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15] []) (.reg (.gpr 15))) #v[132]
    (.letOp (n := 143) (.exec 0x109c96 (fun s => s.RIP = 0x109c96) (notR64Effect 0x109c96 15) (Reg.operands [.gpr 15] [])) #v[132]
    (.letOp (n := 144) (.out 0x109c99 (movR64R64Effect 0x109c99 13 8) (EffectPart.reads (.reg (.gpr 13)) [.gpr 8] []) (.reg (.gpr 13))) #v[69]
    (.letOp (n := 145) (.exec 0x109c99 (fun s => s.RIP = 0x109c99) (movR64R64Effect 0x109c99 13 8) (Reg.operands [.gpr 8] [])) #v[69]
    (.letOp (n := 146) (.out 0x109c9c (andR64R64Effect 0x109c9c 13 15) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 15] []) (.reg (.gpr 13))) #v[144, 142]
    (.letOp (n := 147) (.exec 0x109c9c (fun s => s.RIP = 0x109c9c) (andR64R64Effect 0x109c9c 13 15) (Reg.operands [.gpr 13, .gpr 15] [])) #v[144, 142]
    (.letOp (n := 148) (.out 0x109c9f (orR64R64Effect 0x109c9f 15 8) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 8] []) (.reg (.gpr 15))) #v[142, 69]
    (.letOp (n := 149) (.exec 0x109c9f (fun s => s.RIP = 0x109c9f) (orR64R64Effect 0x109c9f 15 8) (Reg.operands [.gpr 15, .gpr 8] [])) #v[142, 69]
    (.letOp (n := 150) (.out 0x109ca2 (andR64R64Effect 0x109ca2 15 3) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 3] []) (.reg (.gpr 15))) #v[148, 140]
    (.letOp (n := 151) (.exec 0x109ca2 (fun s => s.RIP = 0x109ca2) (andR64R64Effect 0x109ca2 15 3) (Reg.operands [.gpr 15, .gpr 3] [])) #v[148, 140]
    (.letOp (n := 152) (.out 0x109ca5 (orR64R64Effect 0x109ca5 15 13) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 13] []) (.reg (.gpr 15))) #v[150, 146]
    (.letOp (n := 153) (.exec 0x109ca5 (fun s => s.RIP = 0x109ca5) (orR64R64Effect 0x109ca5 15 13) (Reg.operands [.gpr 15, .gpr 13] [])) #v[150, 146]
    (.letOp (n := 154) (.out 0x109ca8 (shrR64Effect 0x109ca8 4 15 63) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[152]
    (.letOp (n := 155) (.exec 0x109ca8 (fun s => s.RIP = 0x109ca8) (shrR64Effect 0x109ca8 4 15 63) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[152]
    (.letOp (n := 156) (.exec 0x109cac (StorePre 0x109cac 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109cac + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109cac 15 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[154, 63]
    (.letOp (n := 157) (.out 0x109cb1 (movR64M64Effect 0x109cb1 13 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[63]
    (.letOp (n := 158) (.exec 0x109cb1 (LoadPre 0x109cb1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109cb1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109cb1 13 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 159) (.out 0x109cb6 (xorR32R32Effect 0x109cb6 3 15 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 15] []) (.reg (.gpr 15))) #v[154, 154]
    (.letOp (n := 160) (.exec 0x109cb6 (fun s => s.RIP = 0x109cb6) (xorR32R32Effect 0x109cb6 3 15 15) (Reg.operands [.gpr 15, .gpr 15] [])) #v[154, 154]
    (.letOp (n := 161) (.out 0x109cb9 (subR64R64Effect 0x109cb9 15 13) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 13] []) (.reg (.gpr 15))) #v[159, 157]
    (.letOp (n := 162) (.exec 0x109cb9 (fun s => s.RIP = 0x109cb9) (subR64R64Effect 0x109cb9 15 13) (Reg.operands [.gpr 15, .gpr 13] [])) #v[159, 157]
    (.letOp (n := 163) (.out 0x109cbc (movR64M64Effect 0x109cbc 1 (.base 1 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1]
    (.letOp (n := 164) (.exec 0x109cbc (LoadPre 0x109cbc (fun s => AddrMode.addr (.base 1 (.d8 0x18)) s (0x109cbc + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109cbc 1 (.base 1 (.d8 0x18))) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 165) (.out 0x109cc0 (movR64R64Effect 0x109cc0 13 1) (EffectPart.reads (.reg (.gpr 13)) [.gpr 1] []) (.reg (.gpr 13))) #v[163]
    (.letOp (n := 166) (.exec 0x109cc0 (fun s => s.RIP = 0x109cc0) (movR64R64Effect 0x109cc0 13 1) (Reg.operands [.gpr 1] [])) #v[163]
    (.letOp (n := 167) (.out 0x109cc3 (subR64R64Effect 0x109cc3 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 0] []) (.reg (.gpr 13))) #v[165, 71]
    (.letOp (n := 168) (.exec 0x109cc3 (fun s => s.RIP = 0x109cc3) (subR64R64Effect 0x109cc3 13 0) (Reg.operands [.gpr 13, .gpr 0] [])) #v[165, 71]
    (b_l109c00_3)))))))))))))))))))))))))))))))))))))))

def bytes_l109c00_2 : List UInt8 :=
  [0x48, 0x2B, 0x5C, 0x24, 0x08, 0x4C, 0x8B, 0x79, 0x10, 0x4D, 0x89, 0xFD, 0x4D, 0x29, 0xC5, 0x48,
    0xC1, 0xFB, 0x3F, 0x4C, 0x01, 0xEB, 0x49, 0xF7, 0xD7, 0x4D, 0x89, 0xC5, 0x4D, 0x21, 0xFD, 0x4D,
    0x09, 0xC7, 0x49, 0x21, 0xDF, 0x4D, 0x09, 0xEF, 0x49, 0xC1, 0xEF, 0x3F, 0x4C, 0x89, 0x7C, 0x24,
    0x08, 0x4C, 0x8B, 0x6C, 0x24, 0x08, 0x45, 0x31, 0xFF, 0x4D, 0x29, 0xEF, 0x48, 0x8B, 0x49, 0x18,
    0x49, 0x89, 0xCD, 0x49, 0x29, 0xC5] ++ bytes_l109c00_3

theorem code_l109c00_2 : ∀ x ∈ codeRange 0x109c80 bytes_l109c00_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x9c80 70 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l109c00_3

@[cfg_block] def b_l109c00_1 : Block Op Label signature Reg.count 93 :=
  .letOp (n := 93) (.out 0x109c3b (xorR8M8Effect 0x109c3b 3 2 (.base 6 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[2, 6]
    (.letOp (n := 94) (.exec 0x109c3b (LoadPre 0x109c3b (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x109c3b + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x109c3b 3 2 (.base 6 (.d8 0x20))) (Reg.operands [.gpr 2, .gpr 6] [])) #v[2, 6]
    (.letOp (n := 95) (.exec 0x109c3e (StorePre 0x109c3e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109c3e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109c3e 3 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[91, 63]
    (.letOp (n := 96) (.exec 0x109c43 (fun s => s.RIP = 0x109c43) (leaR64Effect 0x109c43 12 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 97) (.out 0x109c48 (xorR32R32Effect 0x109c48 3 14 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 14] []) (.reg (.gpr 14))) #v[83, 83]
    (.letOp (n := 98) (.exec 0x109c48 (fun s => s.RIP = 0x109c48) (xorR32R32Effect 0x109c48 3 14 14) (Reg.operands [.gpr 14, .gpr 14] [])) #v[83, 83]
    (.letOp (n := 99) (.out 0x109c4b (xorR32R32Effect 0x109c4b 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[6, 6]
    (.letOp (n := 100) (.exec 0x109c4b (fun s => s.RIP = 0x109c4b) (xorR32R32Effect 0x109c4b 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 101) (.out 0x109c4d (subR64M64Effect 0x109c4d 6 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 4] []) (.reg (.gpr 6))) #v[99, 63]
    (.letOp (n := 102) (.exec 0x109c4d (LoadPre 0x109c4d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109c4d + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x109c4d 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[99, 63]
    (.letOp (n := 103) (.out 0x109c52 (movR64M64Effect 0x109c52 3 (.base 1 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 1] []) (.reg (.gpr 3))) #v[1]
    (.letOp (n := 104) (.exec 0x109c52 (LoadPre 0x109c52 (fun s => AddrMode.addr (.base 1 (.d8 0x8)) s (0x109c52 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109c52 3 (.base 1 (.d8 0x8))) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 105) (.out 0x109c56 (movR64R64Effect 0x109c56 15 3) (EffectPart.reads (.reg (.gpr 15)) [.gpr 3] []) (.reg (.gpr 15))) #v[103]
    (.letOp (n := 106) (.exec 0x109c56 (fun s => s.RIP = 0x109c56) (movR64R64Effect 0x109c56 15 3) (Reg.operands [.gpr 3] [])) #v[103]
    (.letOp (n := 107) (.out 0x109c59 (subR64R64Effect 0x109c59 15 9) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 9] []) (.reg (.gpr 15))) #v[105, 67]
    (.letOp (n := 108) (.exec 0x109c59 (fun s => s.RIP = 0x109c59) (subR64R64Effect 0x109c59 15 9) (Reg.operands [.gpr 15, .gpr 9] [])) #v[105, 67]
    (.letOp (n := 109) (.out 0x109c5c (sarR64Effect 0x109c5c 4 6 63) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[101]
    (.letOp (n := 110) (.exec 0x109c5c (fun s => s.RIP = 0x109c5c) (sarR64Effect 0x109c5c 4 6 63) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[101]
    (.letOp (n := 111) (.out 0x109c60 (addR64R64Effect 0x109c60 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 15] []) (.reg (.gpr 6))) #v[109, 107]
    (.letOp (n := 112) (.exec 0x109c60 (fun s => s.RIP = 0x109c60) (addR64R64Effect 0x109c60 6 15) (Reg.operands [.gpr 6, .gpr 15] [])) #v[109, 107]
    (.letOp (n := 113) (.out 0x109c63 (notR64Effect 0x109c63 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[103]
    (.letOp (n := 114) (.exec 0x109c63 (fun s => s.RIP = 0x109c63) (notR64Effect 0x109c63 3) (Reg.operands [.gpr 3] [])) #v[103]
    (.letOp (n := 115) (.out 0x109c66 (movR64R64Effect 0x109c66 15 9) (EffectPart.reads (.reg (.gpr 15)) [.gpr 9] []) (.reg (.gpr 15))) #v[67]
    (.letOp (n := 116) (.exec 0x109c66 (fun s => s.RIP = 0x109c66) (movR64R64Effect 0x109c66 15 9) (Reg.operands [.gpr 9] [])) #v[67]
    (.letOp (n := 117) (.out 0x109c69 (andR64R64Effect 0x109c69 15 3) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 3] []) (.reg (.gpr 15))) #v[115, 113]
    (.letOp (n := 118) (.exec 0x109c69 (fun s => s.RIP = 0x109c69) (andR64R64Effect 0x109c69 15 3) (Reg.operands [.gpr 15, .gpr 3] [])) #v[115, 113]
    (.letOp (n := 119) (.out 0x109c6c (orR64R64Effect 0x109c6c 3 9) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 9] []) (.reg (.gpr 3))) #v[113, 67]
    (.letOp (n := 120) (.exec 0x109c6c (fun s => s.RIP = 0x109c6c) (orR64R64Effect 0x109c6c 3 9) (Reg.operands [.gpr 3, .gpr 9] [])) #v[113, 67]
    (.letOp (n := 121) (.out 0x109c6f (andR64R64Effect 0x109c6f 3 6) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 6] []) (.reg (.gpr 3))) #v[119, 111]
    (.letOp (n := 122) (.exec 0x109c6f (fun s => s.RIP = 0x109c6f) (andR64R64Effect 0x109c6f 3 6) (Reg.operands [.gpr 3, .gpr 6] [])) #v[119, 111]
    (.letOp (n := 123) (.out 0x109c72 (orR64R64Effect 0x109c72 3 15) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 15] []) (.reg (.gpr 3))) #v[121, 117]
    (.letOp (n := 124) (.exec 0x109c72 (fun s => s.RIP = 0x109c72) (orR64R64Effect 0x109c72 3 15) (Reg.operands [.gpr 3, .gpr 15] [])) #v[121, 117]
    (.letOp (n := 125) (.out 0x109c75 (shrR64Effect 0x109c75 4 3 63) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[123]
    (.letOp (n := 126) (.exec 0x109c75 (fun s => s.RIP = 0x109c75) (shrR64Effect 0x109c75 4 3 63) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[123]
    (.letOp (n := 127) (.exec 0x109c79 (StorePre 0x109c79 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109c79 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109c79 3 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[125, 63]
    (.letOp (n := 128) (.out 0x109c7e (xorR32R32Effect 0x109c7e 2 3 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 3] []) (.reg (.gpr 3))) #v[125, 125]
    (.letOp (n := 129) (.exec 0x109c7e (fun s => s.RIP = 0x109c7e) (xorR32R32Effect 0x109c7e 2 3 3) (Reg.operands [.gpr 3, .gpr 3] [])) #v[125, 125]
    (b_l109c00_2)))))))))))))))))))))))))))))))))))))

def bytes_l109c00_1 : List UInt8 :=
  [0x32, 0x56, 0x20, 0x48, 0x89, 0x5C, 0x24, 0x08, 0x4C, 0x8D, 0x64, 0x24, 0x08, 0x45, 0x31, 0xF6,
    0x31, 0xF6, 0x48, 0x2B, 0x74, 0x24, 0x08, 0x48, 0x8B, 0x59, 0x08, 0x49, 0x89, 0xDF, 0x4D, 0x29,
    0xCF, 0x48, 0xC1, 0xFE, 0x3F, 0x4C, 0x01, 0xFE, 0x48, 0xF7, 0xD3, 0x4D, 0x89, 0xCF, 0x49, 0x21,
    0xDF, 0x4C, 0x09, 0xCB, 0x48, 0x21, 0xF3, 0x4C, 0x09, 0xFB, 0x48, 0xC1, 0xEB, 0x3F, 0x48, 0x89,
    0x5C, 0x24, 0x08, 0x31, 0xDB] ++ bytes_l109c00_2

theorem code_l109c00_1 : ∀ x ∈ codeRange 0x109c3b bytes_l109c00_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x9c3b 69 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l109c00_2

@[cfg_block] def b_l109c00 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x109c00 (pushR64Effect 0x109c00 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[4, 15]
    (.letOp (n := 54) (.exec 0x109c00 (PushPre 0x109c00 2) (pushR64Effect 0x109c00 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[4, 15]
    (.letOp (n := 55) (.out 0x109c02 (pushR64Effect 0x109c02 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[53, 14]
    (.letOp (n := 56) (.exec 0x109c02 (PushPre 0x109c02 2) (pushR64Effect 0x109c02 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 57) (.out 0x109c04 (pushR64Effect 0x109c04 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[55, 13]
    (.letOp (n := 58) (.exec 0x109c04 (PushPre 0x109c04 2) (pushR64Effect 0x109c04 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[55, 13]
    (.letOp (n := 59) (.out 0x109c06 (pushR64Effect 0x109c06 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[57, 12]
    (.letOp (n := 60) (.exec 0x109c06 (PushPre 0x109c06 2) (pushR64Effect 0x109c06 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[57, 12]
    (.letOp (n := 61) (.out 0x109c08 (pushR64Effect 0x109c08 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[59, 3]
    (.letOp (n := 62) (.exec 0x109c08 (PushPre 0x109c08 1) (pushR64Effect 0x109c08 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[59, 3]
    (.letOp (n := 63) (.out 0x109c09 (subR64Imm8Effect 0x109c09 4 0x10) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 64) (.exec 0x109c09 (fun s => s.RIP = 0x109c09) (subR64Imm8Effect 0x109c09 4 0x10) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 65) (.out 0x109c0d (movR64M64Effect 0x109c0d 10 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 6] []) (.reg (.gpr 10))) #v[6]
    (.letOp (n := 66) (.exec 0x109c0d (LoadPre 0x109c0d (fun s => AddrMode.addr (.base 6 .none) s (0x109c0d + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x109c0d 10 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 67) (.out 0x109c10 (movR64M64Effect 0x109c10 9 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 6] []) (.reg (.gpr 9))) #v[6]
    (.letOp (n := 68) (.exec 0x109c10 (LoadPre 0x109c10 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x109c10 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109c10 9 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 69) (.out 0x109c14 (movR64M64Effect 0x109c14 8 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 6] []) (.reg (.gpr 8))) #v[6]
    (.letOp (n := 70) (.exec 0x109c14 (LoadPre 0x109c14 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x109c14 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109c14 8 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 71) (.out 0x109c18 (movR64M64Effect 0x109c18 0 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 72) (.exec 0x109c18 (LoadPre 0x109c18 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x109c18 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109c18 0 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 73) (.out 0x109c1c (movR64M64Effect 0x109c1c 3 (.base 1 .none)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 1] []) (.reg (.gpr 3))) #v[1]
    (.letOp (n := 74) (.exec 0x109c1c (LoadPre 0x109c1c (fun s => AddrMode.addr (.base 1 .none) s (0x109c1c + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x109c1c 3 (.base 1 .none)) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 75) (.out 0x109c1f (movR64R64Effect 0x109c1f 11 3) (EffectPart.reads (.reg (.gpr 11)) [.gpr 3] []) (.reg (.gpr 11))) #v[73]
    (.letOp (n := 76) (.exec 0x109c1f (fun s => s.RIP = 0x109c1f) (movR64R64Effect 0x109c1f 11 3) (Reg.operands [.gpr 3] [])) #v[73]
    (.letOp (n := 77) (.out 0x109c22 (subR64R64Effect 0x109c22 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 10] []) (.reg (.gpr 11))) #v[75, 65]
    (.letOp (n := 78) (.exec 0x109c22 (fun s => s.RIP = 0x109c22) (subR64R64Effect 0x109c22 11 10) (Reg.operands [.gpr 11, .gpr 10] [])) #v[75, 65]
    (.letOp (n := 79) (.out 0x109c25 (notR64Effect 0x109c25 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[73]
    (.letOp (n := 80) (.exec 0x109c25 (fun s => s.RIP = 0x109c25) (notR64Effect 0x109c25 3) (Reg.operands [.gpr 3] [])) #v[73]
    (.letOp (n := 81) (.out 0x109c28 (movR64R64Effect 0x109c28 14 10) (EffectPart.reads (.reg (.gpr 14)) [.gpr 10] []) (.reg (.gpr 14))) #v[65]
    (.letOp (n := 82) (.exec 0x109c28 (fun s => s.RIP = 0x109c28) (movR64R64Effect 0x109c28 14 10) (Reg.operands [.gpr 10] [])) #v[65]
    (.letOp (n := 83) (.out 0x109c2b (andR64R64Effect 0x109c2b 14 3) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 3] []) (.reg (.gpr 14))) #v[81, 79]
    (.letOp (n := 84) (.exec 0x109c2b (fun s => s.RIP = 0x109c2b) (andR64R64Effect 0x109c2b 14 3) (Reg.operands [.gpr 14, .gpr 3] [])) #v[81, 79]
    (.letOp (n := 85) (.out 0x109c2e (orR64R64Effect 0x109c2e 3 10) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 10] []) (.reg (.gpr 3))) #v[79, 65]
    (.letOp (n := 86) (.exec 0x109c2e (fun s => s.RIP = 0x109c2e) (orR64R64Effect 0x109c2e 3 10) (Reg.operands [.gpr 3, .gpr 10] [])) #v[79, 65]
    (.letOp (n := 87) (.out 0x109c31 (andR64R64Effect 0x109c31 3 11) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 11] []) (.reg (.gpr 3))) #v[85, 77]
    (.letOp (n := 88) (.exec 0x109c31 (fun s => s.RIP = 0x109c31) (andR64R64Effect 0x109c31 3 11) (Reg.operands [.gpr 3, .gpr 11] [])) #v[85, 77]
    (.letOp (n := 89) (.out 0x109c34 (orR64R64Effect 0x109c34 3 14) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 14] []) (.reg (.gpr 3))) #v[87, 83]
    (.letOp (n := 90) (.exec 0x109c34 (fun s => s.RIP = 0x109c34) (orR64R64Effect 0x109c34 3 14) (Reg.operands [.gpr 3, .gpr 14] [])) #v[87, 83]
    (.letOp (n := 91) (.out 0x109c37 (shrR64Effect 0x109c37 4 3 63) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[89]
    (.letOp (n := 92) (.exec 0x109c37 (fun s => s.RIP = 0x109c37) (shrR64Effect 0x109c37 4 3 63) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[89]
    (b_l109c00_1))))))))))))))))))))))))))))))))))))))))

def bytes_l109c00 : List UInt8 :=
  [0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x83, 0xEC, 0x10, 0x4C, 0x8B, 0x16,
    0x4C, 0x8B, 0x4E, 0x08, 0x4C, 0x8B, 0x46, 0x10, 0x48, 0x8B, 0x46, 0x18, 0x48, 0x8B, 0x19, 0x49,
    0x89, 0xDB, 0x4D, 0x29, 0xD3, 0x48, 0xF7, 0xD3, 0x4D, 0x89, 0xD6, 0x49, 0x21, 0xDE, 0x4C, 0x09,
    0xD3, 0x4C, 0x21, 0xDB, 0x4C, 0x09, 0xF3, 0x48, 0xC1, 0xEB, 0x3F] ++ bytes_l109c00_1

theorem code_l109c00 : ∀ x ∈ codeRange 0x109c00 bytes_l109c00, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x9c00 59 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l109c00_1

@[cfg_block] def b_l109d80 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x109d80 (pushR64Effect 0x109d80 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[4, 15]
    (.letOp (n := 54) (.exec 0x109d80 (PushPre 0x109d80 2) (pushR64Effect 0x109d80 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[4, 15]
    (.letOp (n := 55) (.out 0x109d82 (pushR64Effect 0x109d82 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[53, 14]
    (.letOp (n := 56) (.exec 0x109d82 (PushPre 0x109d82 2) (pushR64Effect 0x109d82 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 57) (.out 0x109d84 (pushR64Effect 0x109d84 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[55, 13]
    (.letOp (n := 58) (.exec 0x109d84 (PushPre 0x109d84 2) (pushR64Effect 0x109d84 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[55, 13]
    (.letOp (n := 59) (.out 0x109d86 (pushR64Effect 0x109d86 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[57, 12]
    (.letOp (n := 60) (.exec 0x109d86 (PushPre 0x109d86 2) (pushR64Effect 0x109d86 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[57, 12]
    (.letOp (n := 61) (.out 0x109d88 (pushR64Effect 0x109d88 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[59, 3]
    (.letOp (n := 62) (.exec 0x109d88 (PushPre 0x109d88 1) (pushR64Effect 0x109d88 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[59, 3]
    (.letOp (n := 63) (.out 0x109d89 (subR64Imm8Effect 0x109d89 4 0x30) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 64) (.exec 0x109d89 (fun s => s.RIP = 0x109d89) (subR64Imm8Effect 0x109d89 4 0x30) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 65) (.out 0x109d8d (movR64R64Effect 0x109d8d 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 66) (.exec 0x109d8d (fun s => s.RIP = 0x109d8d) (movR64R64Effect 0x109d8d 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 67) (.out 0x109d90 (leaR64Effect 0x109d90 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[63]
    (.letOp (n := 68) (.exec 0x109d90 (fun s => s.RIP = 0x109d90) (leaR64Effect 0x109d90 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 69) (.out 0x109d95 (movR64Imm64Effect 0x109d95 1 0xb4f20099aa774ec1) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 70) (.exec 0x109d95 (fun s => s.RIP = 0x109d95) (movR64Imm64Effect 0x109d95 1 0xb4f20099aa774ec1) (Reg.operands [] [])) #v[]
    (.letOp (n := 71) (.out 0x109d9f (movR64Imm32Effect 0x109d9f 2 0x2021a0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 72) (.exec 0x109d9f (fun s => s.RIP = 0x109d9f) (movR64Imm32Effect 0x109d9f 2 0x2021a0) (Reg.operands [] [])) #v[]
    (.letOp (n := 73) (.out 0x109da6 (movR64Imm32Effect 0x109da6 8 0x202180) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 74) (.exec 0x109da6 (fun s => s.RIP = 0x109da6) (movR64Imm32Effect 0x109da6 8 0x202180) (Reg.operands [] [])) #v[]
    (.letOp (n := 75) (.out 0x109dad (callEffect (fun _ => 0x108e30) 0x109db2) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 76) (.exec 0x109dad (PushPre 0x109dad 5) (callEffect (fun _ => 0x108e30) 0x109db2) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 77) (.const ⟨64, 0x109db2⟩) #v[]
    (.terminate (.call ⟨.l108e30, RegMap.args [(1, 69), (2, 71), (3, 65), (4, 75), (5, 5), (6, 6), (7, 67), (8, 73), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 78⟩ { target := .l109db2, kept := #v[], arity := rfl, guard := some (Fin.last 77) }))))))))))))))))))))))))))

def bytes_l109d80 : List UInt8 :=
  [0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x83, 0xEC, 0x30, 0x48, 0x89, 0xFB,
    0x48, 0x8D, 0x7C, 0x24, 0x08, 0x48, 0xB9, 0xC1, 0x4E, 0x77, 0xAA, 0x99, 0x00, 0xF2, 0xB4, 0x48,
    0xC7, 0xC2, 0xA0, 0x21, 0x20, 0x00, 0x49, 0xC7, 0xC0, 0x80, 0x21, 0x20, 0x00, 0xE8, 0x7E, 0xF0,
    0xFF, 0xFF]

theorem code_l109d80 : ∀ x ∈ codeRange 0x109d80 bytes_l109d80, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9d80 50 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109db2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x109db2 (movR64M64Effect 0x109db2 14 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 54) (.exec 0x109db2 (LoadPre 0x109db2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109db2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109db2 14 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x109db7 (movR64M64Effect 0x109db7 15 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 56) (.exec 0x109db7 (LoadPre 0x109db7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x109db7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109db7 15 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x109dbc (movR64M64Effect 0x109dbc 12 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 58) (.exec 0x109dbc (LoadPre 0x109dbc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x109dbc + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109dbc 12 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x109dc1 (movR64M64Effect 0x109dc1 13 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 60) (.exec 0x109dc1 (LoadPre 0x109dc1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x109dc1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109dc1 13 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x109dc6 (movR32M32LowEffect 0x109dc6 7 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 62) (.exec 0x109dc6 (LoadPre 0x109dc6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x109dc6 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x109dc6 7 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x109dca (callEffect (fun _ => 0x127d50) 0x109dcf) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 64) (.exec 0x109dca (PushPre 0x109dca 5) (callEffect (fun _ => 0x127d50) 0x109dcf) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.const ⟨64, 0x109dcf⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 59), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩ { target := .l109dcf, kept := #v[], arity := rfl, guard := some (Fin.last 65) }))))))))))))))

def bytes_l109db2 : List UInt8 :=
  [0x4C, 0x8B, 0x74, 0x24, 0x08, 0x4C, 0x8B, 0x7C, 0x24, 0x10, 0x4C, 0x8B, 0x64, 0x24, 0x18, 0x4C,
    0x8B, 0x6C, 0x24, 0x20, 0x8B, 0x7C, 0x24, 0x28, 0xE8, 0x81, 0xDF, 0x01, 0x00]

theorem code_l109db2 : ∀ x ∈ codeRange 0x109db2 bytes_l109db2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9db2 29 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109dcf_1 : Block Op Label signature Reg.count 86 :=
  .letOp (n := 86) (.out 0x109e10 (movR64R64Effect 0x109e10 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 87) (.exec 0x109e10 (fun s => s.RIP = 0x109e10) (movR64R64Effect 0x109e10 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 88) (.out 0x109e13 (addR64Imm8Effect 0x109e13 4 0x30) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 89) (.exec 0x109e13 (fun s => s.RIP = 0x109e13) (addR64Imm8Effect 0x109e13 4 0x30) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 90) (.out 0x109e17 (popR64Effect 0x109e17 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[88]
    (.letOp (n := 91) (.out 0x109e17 (popR64Effect 0x109e17 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[88]
    (.letOp (n := 92) (.exec 0x109e17 (PopPre 0x109e17) (popR64Effect 0x109e17 1 3) (Reg.operands [.gpr 4] [])) #v[88]
    (.letOp (n := 93) (.out 0x109e18 (popR64Effect 0x109e18 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[91]
    (.letOp (n := 94) (.out 0x109e18 (popR64Effect 0x109e18 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[91]
    (.letOp (n := 95) (.exec 0x109e18 (PopPre 0x109e18) (popR64Effect 0x109e18 2 12) (Reg.operands [.gpr 4] [])) #v[91]
    (.letOp (n := 96) (.out 0x109e1a (popR64Effect 0x109e1a 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[94]
    (.letOp (n := 97) (.out 0x109e1a (popR64Effect 0x109e1a 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[94]
    (.letOp (n := 98) (.exec 0x109e1a (PopPre 0x109e1a) (popR64Effect 0x109e1a 2 13) (Reg.operands [.gpr 4] [])) #v[94]
    (.letOp (n := 99) (.out 0x109e1c (popR64Effect 0x109e1c 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[97]
    (.letOp (n := 100) (.out 0x109e1c (popR64Effect 0x109e1c 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[97]
    (.letOp (n := 101) (.exec 0x109e1c (PopPre 0x109e1c) (popR64Effect 0x109e1c 2 14) (Reg.operands [.gpr 4] [])) #v[97]
    (.letOp (n := 102) (.out 0x109e1e (popR64Effect 0x109e1e 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[100]
    (.letOp (n := 103) (.out 0x109e1e (popR64Effect 0x109e1e 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[100]
    (.letOp (n := 104) (.exec 0x109e1e (PopPre 0x109e1e) (popR64Effect 0x109e1e 2 15) (Reg.operands [.gpr 4] [])) #v[100]
    (.letOp (n := 105) (.out 0x109e20 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[103]
    (.letOp (n := 106) (.out 0x109e20 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[103]
    (.letOp (n := 107) (.exec 0x109e20 (RetPre 0x109e20) (retEffect) (Reg.operands [.gpr 4] [])) #v[103]
    (.terminate (.ret (RegMap.args [(0, 86), (1, 55), (2, 79), (3, 90), (4, 106), (5, 5), (6, 63), (7, 69), (8, 75), (9, 9), (10, 10), (11, 11), (12, 93), (13, 96), (14, 99), (15, 102), (22, 22), (39, 39), (50, 50), (51, 51)] 108) (some ⟨105, by decide⟩))))))))))))))))))))))))

def bytes_l109dcf_1 : List UInt8 :=
  [0x48, 0x89, 0xD8, 0x48, 0x83, 0xC4, 0x30, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F,
    0xC3]

theorem code_l109dcf_1 : ∀ x ∈ codeRange 0x109e10 bytes_l109dcf_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9e10 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109dcf : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x109dcf (StorePre 0x109dcf 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x109dcf + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109dcf 4 0 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[0, 4]
    (.letOp (n := 54) (.exec 0x109dd3 (fun s => s.RIP = 0x109dd3) (leaR64Effect 0x109dd3 1 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x109dd8 (movzxR32M8Effect 0x109dd8 5 1 (.sib 4 none 0 (.d8 0x7))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x109dd8 (LoadPre 0x109dd8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x109dd8 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109dd8 5 1 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x109ddd (xorR32R32Effect 0x109ddd 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[2, 2]
    (.letOp (n := 58) (.exec 0x109ddd (fun s => s.RIP = 0x109ddd) (xorR32R32Effect 0x109ddd 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 59) (.out 0x109ddf (xorR32R32Effect 0x109ddf 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[6, 6]
    (.letOp (n := 60) (.exec 0x109ddf (fun s => s.RIP = 0x109ddf) (xorR32R32Effect 0x109ddf 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 61) (.out 0x109de1 (testR8R8Effect 0x109de1 2 1 1) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 1] []) (.flag .ZF)) #v[55, 55]
    (.letOp (n := 62) (.exec 0x109de1 (fun s => s.RIP = 0x109de1) (testR8R8Effect 0x109de1 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[55, 55]
    (.letOp (n := 63) (.out 0x109de3 (atFlags (condHolds 5) (cmovR64R64Effect 0x109de3 4 6 14)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 6))) #v[59, 14, 61]
    (.letOp (n := 64) (.exec 0x109de3 (fun s => s.RIP = 0x109de3) (atFlags (condHolds 5) (cmovR64R64Effect 0x109de3 4 6 14)) (Reg.operands [.gpr 6, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[59, 14, 61]
    (.letOp (n := 65) (.out 0x109de7 (xorR32R32Effect 0x109de7 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[7, 7]
    (.letOp (n := 66) (.exec 0x109de7 (fun s => s.RIP = 0x109de7) (xorR32R32Effect 0x109de7 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[7, 7]
    (.letOp (n := 67) (.out 0x109de9 (testR8R8Effect 0x109de9 2 1 1) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 1] []) (.flag .ZF)) #v[55, 55]
    (.letOp (n := 68) (.exec 0x109de9 (fun s => s.RIP = 0x109de9) (testR8R8Effect 0x109de9 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[55, 55]
    (.letOp (n := 69) (.out 0x109deb (atFlags (condHolds 5) (cmovR64R64Effect 0x109deb 4 7 15)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 7))) #v[65, 15, 67]
    (.letOp (n := 70) (.exec 0x109deb (fun s => s.RIP = 0x109deb) (atFlags (condHolds 5) (cmovR64R64Effect 0x109deb 4 7 15)) (Reg.operands [.gpr 7, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[65, 15, 67]
    (.letOp (n := 71) (.out 0x109def (xorR32R32Effect 0x109def 3 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 8] []) (.reg (.gpr 8))) #v[8, 8]
    (.letOp (n := 72) (.exec 0x109def (fun s => s.RIP = 0x109def) (xorR32R32Effect 0x109def 3 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[8, 8]
    (.letOp (n := 73) (.out 0x109df2 (testR8R8Effect 0x109df2 2 1 1) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 1] []) (.flag .ZF)) #v[55, 55]
    (.letOp (n := 74) (.exec 0x109df2 (fun s => s.RIP = 0x109df2) (testR8R8Effect 0x109df2 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[55, 55]
    (.letOp (n := 75) (.out 0x109df4 (atFlags (condHolds 5) (cmovR64R64Effect 0x109df4 4 8 12)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 8))) #v[71, 12, 73]
    (.letOp (n := 76) (.exec 0x109df4 (fun s => s.RIP = 0x109df4) (atFlags (condHolds 5) (cmovR64R64Effect 0x109df4 4 8 12)) (Reg.operands [.gpr 8, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[71, 12, 73]
    (.letOp (n := 77) (.out 0x109df8 (testR8R8Effect 0x109df8 2 1 1) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 1] []) (.flag .ZF)) #v[55, 55]
    (.letOp (n := 78) (.exec 0x109df8 (fun s => s.RIP = 0x109df8) (testR8R8Effect 0x109df8 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[55, 55]
    (.letOp (n := 79) (.out 0x109dfa (atFlags (condHolds 5) (cmovR64R64Effect 0x109dfa 4 2 13)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 2))) #v[57, 13, 77]
    (.letOp (n := 80) (.exec 0x109dfa (fun s => s.RIP = 0x109dfa) (atFlags (condHolds 5) (cmovR64R64Effect 0x109dfa 4 2 13)) (Reg.operands [.gpr 2, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[57, 13, 77]
    (.letOp (n := 81) (.exec 0x109dfe (StorePre 0x109dfe 3 (fun s => AddrMode.addr (.base 3 .none) s (0x109dfe + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x109dfe 6 (.base 3 .none)) (Reg.operands [.gpr 6, .gpr 3] [])) #v[63, 3]
    (.letOp (n := 82) (.exec 0x109e01 (StorePre 0x109e01 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x109e01 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x109e01 7 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[69, 3]
    (.letOp (n := 83) (.exec 0x109e05 (StorePre 0x109e05 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x109e05 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x109e05 8 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 8, .gpr 3] [])) #v[75, 3]
    (.letOp (n := 84) (.exec 0x109e09 (StorePre 0x109e09 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x109e09 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x109e09 2 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[79, 3]
    (.letOp (n := 85) (.exec 0x109e0d (StorePre 0x109e0d 3 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x109e0d + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x109e0d 3 0 (.base 3 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (b_l109dcf_1)))))))))))))))))))))))))))))))))

def bytes_l109dcf : List UInt8 :=
  [0x88, 0x44, 0x24, 0x07, 0x48, 0x8D, 0x4C, 0x24, 0x07, 0x0F, 0xB6, 0x4C, 0x24, 0x07, 0x31, 0xD2,
    0x31, 0xF6, 0x84, 0xC9, 0x49, 0x0F, 0x45, 0xF6, 0x31, 0xFF, 0x84, 0xC9, 0x49, 0x0F, 0x45, 0xFF,
    0x45, 0x31, 0xC0, 0x84, 0xC9, 0x4D, 0x0F, 0x45, 0xC4, 0x84, 0xC9, 0x49, 0x0F, 0x45, 0xD5, 0x48,
    0x89, 0x33, 0x48, 0x89, 0x7B, 0x08, 0x4C, 0x89, 0x43, 0x10, 0x48, 0x89, 0x53, 0x18, 0x88, 0x43,
    0x20] ++ bytes_l109dcf_1

theorem code_l109dcf : ∀ x ∈ codeRange 0x109dcf bytes_l109dcf, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x9dcf 65 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l109dcf_1

@[cfg_block] def b_l109e30 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x109e30 (movR64M64Effect 0x109e30 1 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[6]
    (.letOp (n := 54) (.exec 0x109e30 (LoadPre 0x109e30 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x109e30 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109e30 1 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 55) (.out 0x109e34 (bswapR64Effect 0x109e34 3 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 56) (.exec 0x109e34 (fun s => s.RIP = 0x109e34) (bswapR64Effect 0x109e34 3 1) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 57) (.out 0x109e37 (movR64M64Effect 0x109e37 2 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6] []) (.reg (.gpr 2))) #v[6]
    (.letOp (n := 58) (.exec 0x109e37 (LoadPre 0x109e37 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x109e37 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109e37 2 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 59) (.out 0x109e3b (bswapR64Effect 0x109e3b 3 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[57]
    (.letOp (n := 60) (.exec 0x109e3b (fun s => s.RIP = 0x109e3b) (bswapR64Effect 0x109e3b 3 2) (Reg.operands [.gpr 2] [])) #v[57]
    (.letOp (n := 61) (.out 0x109e3e (movR64R64Effect 0x109e3e 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 62) (.exec 0x109e3e (fun s => s.RIP = 0x109e3e) (movR64R64Effect 0x109e3e 0 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 63) (.out 0x109e41 (movR64M64Effect 0x109e41 7 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[6]
    (.letOp (n := 64) (.exec 0x109e41 (LoadPre 0x109e41 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x109e41 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109e41 7 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 65) (.out 0x109e45 (bswapR64Effect 0x109e45 3 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[63]
    (.letOp (n := 66) (.exec 0x109e45 (fun s => s.RIP = 0x109e45) (bswapR64Effect 0x109e45 3 7) (Reg.operands [.gpr 7] [])) #v[63]
    (.letOp (n := 67) (.out 0x109e48 (movR64M64Effect 0x109e48 6 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[6]
    (.letOp (n := 68) (.exec 0x109e48 (LoadPre 0x109e48 (fun s => AddrMode.addr (.base 6 .none) s (0x109e48 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x109e48 6 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 69) (.out 0x109e4b (bswapR64Effect 0x109e4b 3 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[67]
    (.letOp (n := 70) (.exec 0x109e4b (fun s => s.RIP = 0x109e4b) (bswapR64Effect 0x109e4b 3 6) (Reg.operands [.gpr 6] [])) #v[67]
    (.letOp (n := 71) (.exec 0x109e4e (StorePre 0x109e4e 3 (fun s => AddrMode.addr (.base 0 .none) s (0x109e4e + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x109e4e 1 (.base 0 .none)) (Reg.operands [.gpr 1, .gpr 0] [])) #v[55, 61]
    (.letOp (n := 72) (.exec 0x109e51 (StorePre 0x109e51 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x109e51 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x109e51 2 (.base 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 0] [])) #v[59, 61]
    (.letOp (n := 73) (.exec 0x109e55 (StorePre 0x109e55 4 (fun s => AddrMode.addr (.base 0 (.d8 0x10)) s (0x109e55 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x109e55 7 (.base 0 (.d8 0x10))) (Reg.operands [.gpr 7, .gpr 0] [])) #v[65, 61]
    (.letOp (n := 74) (.exec 0x109e59 (StorePre 0x109e59 4 (fun s => AddrMode.addr (.base 0 (.d8 0x18)) s (0x109e59 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x109e59 6 (.base 0 (.d8 0x18))) (Reg.operands [.gpr 6, .gpr 0] [])) #v[69, 61]
    (.letOp (n := 75) (.out 0x109e5d (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[4]
    (.letOp (n := 76) (.out 0x109e5d (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 77) (.exec 0x109e5d (RetPre 0x109e5d) (retEffect) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.ret (RegMap.args [(0, 61), (1, 55), (2, 59), (3, 3), (4, 76), (5, 5), (6, 69), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 78) (some ⟨75, by decide⟩)))))))))))))))))))))))))))

def bytes_l109e30 : List UInt8 :=
  [0x48, 0x8B, 0x4E, 0x18, 0x48, 0x0F, 0xC9, 0x48, 0x8B, 0x56, 0x10, 0x48, 0x0F, 0xCA, 0x48, 0x89,
    0xF8, 0x48, 0x8B, 0x7E, 0x08, 0x48, 0x0F, 0xCF, 0x48, 0x8B, 0x36, 0x48, 0x0F, 0xCE, 0x48, 0x89,
    0x08, 0x48, 0x89, 0x50, 0x08, 0x48, 0x89, 0x78, 0x10, 0x48, 0x89, 0x70, 0x18, 0xC3]

theorem code_l109e30 : ∀ x ∈ codeRange 0x109e30 bytes_l109e30, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9e30 46 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109e60_2 : Block Op Label signature Reg.count 130 :=
  .letOp (n := 130) (.out 0x109eef (addR64R64Effect 0x109eef 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 15] []) (.reg (.gpr 2))) #v[124, 73]
    (.letOp (n := 131) (.exec 0x109eef (fun s => s.RIP = 0x109eef) (addR64R64Effect 0x109eef 2 15) (Reg.operands [.gpr 2, .gpr 15] [])) #v[124, 73]
    (.letOp (n := 132) (.out 0x109ef2 (addR64Imm8Effect 0x109ef2 2 0x2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[130]
    (.letOp (n := 133) (.exec 0x109ef2 (fun s => s.RIP = 0x109ef2) (addR64Imm8Effect 0x109ef2 2 0x2) (Reg.operands [.gpr 2] [])) #v[130]
    (.letOp (n := 134) (.out 0x109ef6 (orR64R64Effect 0x109ef6 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[132, 128]
    (.letOp (n := 135) (.exec 0x109ef6 (fun s => s.RIP = 0x109ef6) (orR64R64Effect 0x109ef6 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[132, 128]
    (.letOp (n := 136) (.out 0x109ef9 (shrR64Effect 0x109ef9 4 2 63) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[134]
    (.letOp (n := 137) (.exec 0x109ef9 (fun s => s.RIP = 0x109ef9) (shrR64Effect 0x109ef9 4 2 63) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[134]
    (.letOp (n := 138) (.exec 0x109efd (StorePre 0x109efd 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109efd + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109efd 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[136, 63]
    (.letOp (n := 139) (.out 0x109f02 (subR64M64Effect 0x109f02 1 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 4] []) (.reg (.gpr 1))) #v[97, 63]
    (.letOp (n := 140) (.exec 0x109f02 (LoadPre 0x109f02 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109f02 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x109f02 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[97, 63]
    (.letOp (n := 141) (.out 0x109f07 (sarR64Effect 0x109f07 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[139]
    (.letOp (n := 142) (.exec 0x109f07 (fun s => s.RIP = 0x109f07) (sarR64Effect 0x109f07 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[139]
    (.letOp (n := 143) (.out 0x109f0b (addR64R64Effect 0x109f0b 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 14] []) (.reg (.gpr 1))) #v[141, 71]
    (.letOp (n := 144) (.exec 0x109f0b (fun s => s.RIP = 0x109f0b) (addR64R64Effect 0x109f0b 1 14) (Reg.operands [.gpr 1, .gpr 14] [])) #v[141, 71]
    (.letOp (n := 145) (.out 0x109f0e (incR64Effect 0x109f0e 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[143]
    (.letOp (n := 146) (.exec 0x109f0e (fun s => s.RIP = 0x109f0e) (incR64Effect 0x109f0e 1) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[143]
    (.letOp (n := 147) (.out 0x109f11 (movR64R64Effect 0x109f11 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14] []) (.reg (.gpr 2))) #v[71]
    (.letOp (n := 148) (.exec 0x109f11 (fun s => s.RIP = 0x109f11) (movR64R64Effect 0x109f11 2 14) (Reg.operands [.gpr 14] [])) #v[71]
    (.letOp (n := 149) (.out 0x109f14 (notR64Effect 0x109f14 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[147]
    (.letOp (n := 150) (.exec 0x109f14 (fun s => s.RIP = 0x109f14) (notR64Effect 0x109f14 2) (Reg.operands [.gpr 2] [])) #v[147]
    (.letOp (n := 151) (.out 0x109f17 (orR64R64Effect 0x109f17 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[149, 145]
    (.letOp (n := 152) (.exec 0x109f17 (fun s => s.RIP = 0x109f17) (orR64R64Effect 0x109f17 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[149, 145]
    (.letOp (n := 153) (.out 0x109f1a (shrR64Effect 0x109f1a 4 2 63) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[151]
    (.letOp (n := 154) (.exec 0x109f1a (fun s => s.RIP = 0x109f1a) (shrR64Effect 0x109f1a 4 2 63) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[151]
    (.letOp (n := 155) (.exec 0x109f1e (StorePre 0x109f1e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109f1e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109f1e 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[153, 63]
    (.letOp (n := 156) (.out 0x109f23 (movzxR32M8Effect 0x109f23 5 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[63]
    (.letOp (n := 157) (.exec 0x109f23 (LoadPre 0x109f23 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109f23 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109f23 5 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 158) (.out 0x109f28 (andAlImm8Effect 0x109f28 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[156]
    (.letOp (n := 159) (.exec 0x109f28 (fun s => s.RIP = 0x109f28) (andAlImm8Effect 0x109f28 0x1) (Reg.operands [.gpr 0] [])) #v[156]
    (.letOp (n := 160) (.out 0x109f2a (movzxR32R8Effect 0x109f2a 3 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[158]
    (.letOp (n := 161) (.exec 0x109f2a (fun s => s.RIP = 0x109f2a) (movzxR32R8Effect 0x109f2a 3 7 0) (Reg.operands [.gpr 0] [])) #v[158]
    (.letOp (n := 162) (.out 0x109f2d (callEffect (fun _ => 0x127d50) 0x109f32) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 163) (.exec 0x109f2d (PushPre 0x109f2d 5) (callEffect (fun _ => 0x127d50) 0x109f32) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 164) (.const ⟨64, 0x109f32⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(0, 158), (1, 145), (2, 153), (3, 65), (4, 162), (5, 5), (6, 128), (7, 160), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)] 165⟩ { target := .l109f32, kept := #v[], arity := rfl, guard := some (Fin.last 164) }))))))))))))))))))))))))))))))))))))

def bytes_l109e60_2 : List UInt8 :=
  [0x4C, 0x01, 0xFA, 0x48, 0x83, 0xC2, 0x02, 0x48, 0x09, 0xF2, 0x48, 0xC1, 0xEA, 0x3F, 0x48, 0x89,
    0x54, 0x24, 0x08, 0x48, 0x2B, 0x4C, 0x24, 0x08, 0x48, 0xC1, 0xF9, 0x3F, 0x4C, 0x01, 0xF1, 0x48,
    0xFF, 0xC1, 0x4C, 0x89, 0xF2, 0x48, 0xF7, 0xD2, 0x48, 0x09, 0xCA, 0x48, 0xC1, 0xEA, 0x3F, 0x48,
    0x89, 0x54, 0x24, 0x08, 0x0F, 0xB6, 0x44, 0x24, 0x08, 0x24, 0x01, 0x0F, 0xB6, 0xF8, 0xE8, 0x1E,
    0xDE, 0x01, 0x00]

theorem code_l109e60_2 : ∀ x ∈ codeRange 0x109eef bytes_l109e60_2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9eef 67 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109e60_1 : Block Op Label signature Reg.count 93 :=
  .letOp (n := 93) (.out 0x109ea1 (shrR64Effect 0x109ea1 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[91]
    (.letOp (n := 94) (.exec 0x109ea1 (fun s => s.RIP = 0x109ea1) (shrR64Effect 0x109ea1 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[91]
    (.letOp (n := 95) (.exec 0x109ea5 (StorePre 0x109ea5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109ea5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109ea5 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[93, 63]
    (.letOp (n := 96) (.exec 0x109eaa (fun s => s.RIP = 0x109eaa) (leaR64Effect 0x109eaa 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 97) (.out 0x109eaf (xorR32R32Effect 0x109eaf 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[93, 93]
    (.letOp (n := 98) (.exec 0x109eaf (fun s => s.RIP = 0x109eaf) (xorR32R32Effect 0x109eaf 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[93, 93]
    (.letOp (n := 99) (.out 0x109eb1 (xorR32R32Effect 0x109eb1 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[2, 2]
    (.letOp (n := 100) (.exec 0x109eb1 (fun s => s.RIP = 0x109eb1) (xorR32R32Effect 0x109eb1 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 101) (.out 0x109eb3 (subR64M64Effect 0x109eb3 2 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 4] []) (.reg (.gpr 2))) #v[99, 63]
    (.letOp (n := 102) (.exec 0x109eb3 (LoadPre 0x109eb3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109eb3 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x109eb3 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[99, 63]
    (.letOp (n := 103) (.out 0x109eb8 (sarR64Effect 0x109eb8 4 2 63) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[101]
    (.letOp (n := 104) (.exec 0x109eb8 (fun s => s.RIP = 0x109eb8) (sarR64Effect 0x109eb8 4 2 63) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[101]
    (.letOp (n := 105) (.out 0x109ebc (movR64Imm64Effect 0x109ebc 6 0x4551231950b75fc5) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 106) (.exec 0x109ebc (fun s => s.RIP = 0x109ebc) (movR64Imm64Effect 0x109ebc 6 0x4551231950b75fc5) (Reg.operands [] [])) #v[]
    (.letOp (n := 107) (.out 0x109ec6 (addR64R64Effect 0x109ec6 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 12] []) (.reg (.gpr 6))) #v[105, 77]
    (.letOp (n := 108) (.exec 0x109ec6 (fun s => s.RIP = 0x109ec6) (addR64R64Effect 0x109ec6 6 12) (Reg.operands [.gpr 6, .gpr 12] [])) #v[105, 77]
    (.letOp (n := 109) (.out 0x109ec9 (addR64R64Effect 0x109ec9 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[107, 103]
    (.letOp (n := 110) (.exec 0x109ec9 (fun s => s.RIP = 0x109ec9) (addR64R64Effect 0x109ec9 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[107, 103]
    (.letOp (n := 111) (.out 0x109ecc (movR64R64Effect 0x109ecc 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12] []) (.reg (.gpr 2))) #v[77]
    (.letOp (n := 112) (.exec 0x109ecc (fun s => s.RIP = 0x109ecc) (movR64R64Effect 0x109ecc 2 12) (Reg.operands [.gpr 12] [])) #v[77]
    (.letOp (n := 113) (.out 0x109ecf (notR64Effect 0x109ecf 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[111]
    (.letOp (n := 114) (.exec 0x109ecf (fun s => s.RIP = 0x109ecf) (notR64Effect 0x109ecf 2) (Reg.operands [.gpr 2] [])) #v[111]
    (.letOp (n := 115) (.out 0x109ed2 (orR64R64Effect 0x109ed2 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[113, 109]
    (.letOp (n := 116) (.exec 0x109ed2 (fun s => s.RIP = 0x109ed2) (orR64R64Effect 0x109ed2 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[113, 109]
    (.letOp (n := 117) (.out 0x109ed5 (shrR64Effect 0x109ed5 4 2 63) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[115]
    (.letOp (n := 118) (.exec 0x109ed5 (fun s => s.RIP = 0x109ed5) (shrR64Effect 0x109ed5 4 2 63) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[115]
    (.letOp (n := 119) (.exec 0x109ed9 (StorePre 0x109ed9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109ed9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109ed9 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[117, 63]
    (.letOp (n := 120) (.out 0x109ede (xorR32R32Effect 0x109ede 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[117, 117]
    (.letOp (n := 121) (.exec 0x109ede (fun s => s.RIP = 0x109ede) (xorR32R32Effect 0x109ede 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[117, 117]
    (.letOp (n := 122) (.out 0x109ee0 (subR64M64Effect 0x109ee0 2 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 4] []) (.reg (.gpr 2))) #v[120, 63]
    (.letOp (n := 123) (.exec 0x109ee0 (LoadPre 0x109ee0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109ee0 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x109ee0 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[120, 63]
    (.letOp (n := 124) (.out 0x109ee5 (sarR64Effect 0x109ee5 4 2 63) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[122]
    (.letOp (n := 125) (.exec 0x109ee5 (fun s => s.RIP = 0x109ee5) (sarR64Effect 0x109ee5 4 2 63) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[122]
    (.letOp (n := 126) (.out 0x109ee9 (movR64R64Effect 0x109ee9 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[73]
    (.letOp (n := 127) (.exec 0x109ee9 (fun s => s.RIP = 0x109ee9) (movR64R64Effect 0x109ee9 6 15) (Reg.operands [.gpr 15] [])) #v[73]
    (.letOp (n := 128) (.out 0x109eec (notR64Effect 0x109eec 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[126]
    (.letOp (n := 129) (.exec 0x109eec (fun s => s.RIP = 0x109eec) (notR64Effect 0x109eec 6) (Reg.operands [.gpr 6] [])) #v[126]
    (b_l109e60_2)))))))))))))))))))))))))))))))))))))

def bytes_l109e60_1 : List UInt8 :=
  [0x48, 0xC1, 0xE9, 0x3F, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x8D, 0x44, 0x24, 0x08, 0x31, 0xC9,
    0x31, 0xD2, 0x48, 0x2B, 0x54, 0x24, 0x08, 0x48, 0xC1, 0xFA, 0x3F, 0x48, 0xBE, 0xC5, 0x5F, 0xB7,
    0x50, 0x19, 0x23, 0x51, 0x45, 0x4C, 0x01, 0xE6, 0x48, 0x01, 0xD6, 0x4C, 0x89, 0xE2, 0x48, 0xF7,
    0xD2, 0x48, 0x09, 0xF2, 0x48, 0xC1, 0xEA, 0x3F, 0x48, 0x89, 0x54, 0x24, 0x08, 0x31, 0xD2, 0x48,
    0x2B, 0x54, 0x24, 0x08, 0x48, 0xC1, 0xFA, 0x3F, 0x4C, 0x89, 0xFE, 0x48, 0xF7, 0xD6] ++ bytes_l109e60_2

theorem code_l109e60_1 : ∀ x ∈ codeRange 0x109ea1 bytes_l109e60_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x9ea1 78 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l109e60_2

@[cfg_block] def b_l109e60 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x109e60 (pushR64Effect 0x109e60 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[4, 15]
    (.letOp (n := 54) (.exec 0x109e60 (PushPre 0x109e60 2) (pushR64Effect 0x109e60 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[4, 15]
    (.letOp (n := 55) (.out 0x109e62 (pushR64Effect 0x109e62 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[53, 14]
    (.letOp (n := 56) (.exec 0x109e62 (PushPre 0x109e62 2) (pushR64Effect 0x109e62 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 57) (.out 0x109e64 (pushR64Effect 0x109e64 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[55, 13]
    (.letOp (n := 58) (.exec 0x109e64 (PushPre 0x109e64 2) (pushR64Effect 0x109e64 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[55, 13]
    (.letOp (n := 59) (.out 0x109e66 (pushR64Effect 0x109e66 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[57, 12]
    (.letOp (n := 60) (.exec 0x109e66 (PushPre 0x109e66 2) (pushR64Effect 0x109e66 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[57, 12]
    (.letOp (n := 61) (.out 0x109e68 (pushR64Effect 0x109e68 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[59, 3]
    (.letOp (n := 62) (.exec 0x109e68 (PushPre 0x109e68 1) (pushR64Effect 0x109e68 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[59, 3]
    (.letOp (n := 63) (.out 0x109e69 (subR64Imm8Effect 0x109e69 4 0x10) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 64) (.exec 0x109e69 (fun s => s.RIP = 0x109e69) (subR64Imm8Effect 0x109e69 4 0x10) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 65) (.out 0x109e6d (movR64R64Effect 0x109e6d 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 66) (.exec 0x109e6d (fun s => s.RIP = 0x109e6d) (movR64R64Effect 0x109e6d 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 67) (.out 0x109e70 (movR64M64Effect 0x109e70 14 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 6] []) (.reg (.gpr 14))) #v[6]
    (.letOp (n := 68) (.exec 0x109e70 (LoadPre 0x109e70 (fun s => AddrMode.addr (.base 6 .none) s (0x109e70 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x109e70 14 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 69) (.out 0x109e73 (movR64M64Effect 0x109e73 15 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 6] []) (.reg (.gpr 15))) #v[6]
    (.letOp (n := 70) (.exec 0x109e73 (LoadPre 0x109e73 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x109e73 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109e73 15 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 71) (.out 0x109e77 (bswapR64Effect 0x109e77 3 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14] []) (.reg (.gpr 14))) #v[67]
    (.letOp (n := 72) (.exec 0x109e77 (fun s => s.RIP = 0x109e77) (bswapR64Effect 0x109e77 3 14) (Reg.operands [.gpr 14] [])) #v[67]
    (.letOp (n := 73) (.out 0x109e7a (bswapR64Effect 0x109e7a 3 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15] []) (.reg (.gpr 15))) #v[69]
    (.letOp (n := 74) (.exec 0x109e7a (fun s => s.RIP = 0x109e7a) (bswapR64Effect 0x109e7a 3 15) (Reg.operands [.gpr 15] [])) #v[69]
    (.letOp (n := 75) (.out 0x109e7d (movR64M64Effect 0x109e7d 12 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 6] []) (.reg (.gpr 12))) #v[6]
    (.letOp (n := 76) (.exec 0x109e7d (LoadPre 0x109e7d (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x109e7d + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109e7d 12 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 77) (.out 0x109e81 (bswapR64Effect 0x109e81 3 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[75]
    (.letOp (n := 78) (.exec 0x109e81 (fun s => s.RIP = 0x109e81) (bswapR64Effect 0x109e81 3 12) (Reg.operands [.gpr 12] [])) #v[75]
    (.letOp (n := 79) (.out 0x109e84 (movR64M64Effect 0x109e84 13 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 6] []) (.reg (.gpr 13))) #v[6]
    (.letOp (n := 80) (.exec 0x109e84 (LoadPre 0x109e84 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x109e84 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109e84 13 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 81) (.out 0x109e88 (bswapR64Effect 0x109e88 3 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[79]
    (.letOp (n := 82) (.exec 0x109e88 (fun s => s.RIP = 0x109e88) (bswapR64Effect 0x109e88 3 13) (Reg.operands [.gpr 13] [])) #v[79]
    (.letOp (n := 83) (.out 0x109e8b (movR64Imm64Effect 0x109e8b 0 0x402da1732fc9bebf) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 84) (.exec 0x109e8b (fun s => s.RIP = 0x109e8b) (movR64Imm64Effect 0x109e8b 0 0x402da1732fc9bebf) (Reg.operands [] [])) #v[]
    (.letOp (n := 85) (.out 0x109e95 (addR64R64Effect 0x109e95 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 13] []) (.reg (.gpr 0))) #v[83, 81]
    (.letOp (n := 86) (.exec 0x109e95 (fun s => s.RIP = 0x109e95) (addR64R64Effect 0x109e95 0 13) (Reg.operands [.gpr 0, .gpr 13] [])) #v[83, 81]
    (.letOp (n := 87) (.out 0x109e98 (movR64R64Effect 0x109e98 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 13] []) (.reg (.gpr 1))) #v[81]
    (.letOp (n := 88) (.exec 0x109e98 (fun s => s.RIP = 0x109e98) (movR64R64Effect 0x109e98 1 13) (Reg.operands [.gpr 13] [])) #v[81]
    (.letOp (n := 89) (.out 0x109e9b (notR64Effect 0x109e9b 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[87]
    (.letOp (n := 90) (.exec 0x109e9b (fun s => s.RIP = 0x109e9b) (notR64Effect 0x109e9b 1) (Reg.operands [.gpr 1] [])) #v[87]
    (.letOp (n := 91) (.out 0x109e9e (orR64R64Effect 0x109e9e 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[89, 85]
    (.letOp (n := 92) (.exec 0x109e9e (fun s => s.RIP = 0x109e9e) (orR64R64Effect 0x109e9e 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[89, 85]
    (b_l109e60_1))))))))))))))))))))))))))))))))))))))))

def bytes_l109e60 : List UInt8 :=
  [0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x83, 0xEC, 0x10, 0x48, 0x89, 0xFB,
    0x4C, 0x8B, 0x36, 0x4C, 0x8B, 0x7E, 0x08, 0x49, 0x0F, 0xCE, 0x49, 0x0F, 0xCF, 0x4C, 0x8B, 0x66,
    0x10, 0x49, 0x0F, 0xCC, 0x4C, 0x8B, 0x6E, 0x18, 0x49, 0x0F, 0xCD, 0x48, 0xB8, 0xBF, 0xBE, 0xC9,
    0x2F, 0x73, 0xA1, 0x2D, 0x40, 0x4C, 0x01, 0xE8, 0x4C, 0x89, 0xE9, 0x48, 0xF7, 0xD1, 0x48, 0x09,
    0xC1] ++ bytes_l109e60_1

theorem code_l109e60 : ∀ x ∈ codeRange 0x109e60 bytes_l109e60, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x9e60 65 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l109e60_1

@[cfg_block] def b_l109f32 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x109f32 (StorePre 0x109f32 3 (fun s => AddrMode.addr (.base 3 .none) s (0x109f32 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x109f32 13 (.base 3 .none)) (Reg.operands [.gpr 13, .gpr 3] [])) #v[13, 3]
    (.letOp (n := 54) (.exec 0x109f35 (StorePre 0x109f35 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x109f35 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x109f35 12 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 12, .gpr 3] [])) #v[12, 3]
    (.letOp (n := 55) (.exec 0x109f39 (StorePre 0x109f39 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x109f39 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x109f39 15 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 15, .gpr 3] [])) #v[15, 3]
    (.letOp (n := 56) (.exec 0x109f3d (StorePre 0x109f3d 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x109f3d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x109f3d 14 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 14, .gpr 3] [])) #v[14, 3]
    (.letOp (n := 57) (.exec 0x109f41 (StorePre 0x109f41 3 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x109f41 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x109f41 3 0 (.base 3 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (.letOp (n := 58) (.out 0x109f44 (movR64R64Effect 0x109f44 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 59) (.exec 0x109f44 (fun s => s.RIP = 0x109f44) (movR64R64Effect 0x109f44 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 60) (.out 0x109f47 (addR64Imm8Effect 0x109f47 4 0x10) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 61) (.exec 0x109f47 (fun s => s.RIP = 0x109f47) (addR64Imm8Effect 0x109f47 4 0x10) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.out 0x109f4b (popR64Effect 0x109f4b 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[60]
    (.letOp (n := 63) (.out 0x109f4b (popR64Effect 0x109f4b 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[60]
    (.letOp (n := 64) (.exec 0x109f4b (PopPre 0x109f4b) (popR64Effect 0x109f4b 1 3) (Reg.operands [.gpr 4] [])) #v[60]
    (.letOp (n := 65) (.out 0x109f4c (popR64Effect 0x109f4c 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[63]
    (.letOp (n := 66) (.out 0x109f4c (popR64Effect 0x109f4c 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 67) (.exec 0x109f4c (PopPre 0x109f4c) (popR64Effect 0x109f4c 2 12) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 68) (.out 0x109f4e (popR64Effect 0x109f4e 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[66]
    (.letOp (n := 69) (.out 0x109f4e (popR64Effect 0x109f4e 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[66]
    (.letOp (n := 70) (.exec 0x109f4e (PopPre 0x109f4e) (popR64Effect 0x109f4e 2 13) (Reg.operands [.gpr 4] [])) #v[66]
    (.letOp (n := 71) (.out 0x109f50 (popR64Effect 0x109f50 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[69]
    (.letOp (n := 72) (.out 0x109f50 (popR64Effect 0x109f50 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[69]
    (.letOp (n := 73) (.exec 0x109f50 (PopPre 0x109f50) (popR64Effect 0x109f50 2 14) (Reg.operands [.gpr 4] [])) #v[69]
    (.letOp (n := 74) (.out 0x109f52 (popR64Effect 0x109f52 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[72]
    (.letOp (n := 75) (.out 0x109f52 (popR64Effect 0x109f52 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[72]
    (.letOp (n := 76) (.exec 0x109f52 (PopPre 0x109f52) (popR64Effect 0x109f52 2 15) (Reg.operands [.gpr 4] [])) #v[72]
    (.letOp (n := 77) (.out 0x109f54 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[75]
    (.letOp (n := 78) (.out 0x109f54 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[75]
    (.letOp (n := 79) (.exec 0x109f54 (RetPre 0x109f54) (retEffect) (Reg.operands [.gpr 4] [])) #v[75]
    (.terminate (.ret (RegMap.args [(0, 58), (1, 1), (2, 2), (3, 62), (4, 78), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 65), (13, 68), (14, 71), (15, 74), (22, 22), (39, 39), (50, 50), (51, 51)] 80) (some ⟨77, by decide⟩)))))))))))))))))))))))))))))

def bytes_l109f32 : List UInt8 :=
  [0x4C, 0x89, 0x2B, 0x4C, 0x89, 0x63, 0x08, 0x4C, 0x89, 0x7B, 0x10, 0x4C, 0x89, 0x73, 0x18, 0x88,
    0x43, 0x20, 0x48, 0x89, 0xD8, 0x48, 0x83, 0xC4, 0x10, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E,
    0x41, 0x5F, 0xC3]

theorem code_l109f32 : ∀ x ∈ codeRange 0x109f32 bytes_l109f32, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9f32 35 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109f60 : Block Op Label signature Reg.count 53 :=
  .terminate (.br ⟨.l1099c0, RegMap.args (entryMap (live .l109f60)) 53⟩)

def bytes_l109f60 : List UInt8 :=
  [0xE9, 0x5B, 0xFA, 0xFF, 0xFF]

theorem code_l109f60 : ∀ x ∈ codeRange 0x109f60 bytes_l109f60, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9f60 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109f70 : Block Op Label signature Reg.count 53 :=
  .terminate (.br ⟨.l1099c0, RegMap.args (entryMap (live .l109f70)) 53⟩)

def bytes_l109f70 : List UInt8 :=
  [0xE9, 0x4B, 0xFA, 0xFF, 0xFF]

theorem code_l109f70 : ∀ x ∈ codeRange 0x109f70 bytes_l109f70, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9f70 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109f80_2 : Block Op Label signature Reg.count 127 :=
  .letOp (n := 127) (.out 0x10a014 (orR64R64Effect 0x10a014 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[125, 120]
    (.letOp (n := 128) (.exec 0x10a014 (fun s => s.RIP = 0x10a014) (orR64R64Effect 0x10a014 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[125, 120]
    (.letOp (n := 129) (.out 0x10a017 (shrR64Effect 0x10a017 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[127]
    (.letOp (n := 130) (.exec 0x10a017 (fun s => s.RIP = 0x10a017) (shrR64Effect 0x10a017 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[127]
    (.letOp (n := 131) (.exec 0x10a01b (StorePre 0x10a01b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10a01b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10a01b 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[129, 65]
    (.letOp (n := 132) (.out 0x10a020 (movR64M64Effect 0x10a020 3 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[65]
    (.letOp (n := 133) (.exec 0x10a020 (LoadPre 0x10a020 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10a020 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10a020 3 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 134) (.out 0x10a025 (movR64M64Effect 0x10a025 15 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 6] []) (.reg (.gpr 15))) #v[6]
    (.letOp (n := 135) (.exec 0x10a025 (LoadPre 0x10a025 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x10a025 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a025 15 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 136) (.out 0x10a029 (decR64Effect 0x10a029 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[132]
    (.letOp (n := 137) (.exec 0x10a029 (fun s => s.RIP = 0x10a029) (decR64Effect 0x10a029 3) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[132]
    (.letOp (n := 138) (.out 0x10a02c (shrR64Effect 0x10a02c 4 3 63) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[136]
    (.letOp (n := 139) (.exec 0x10a02c (fun s => s.RIP = 0x10a02c) (shrR64Effect 0x10a02c 4 3 63) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[136]
    (.letOp (n := 140) (.out 0x10a030 (addR64R64Effect 0x10a030 3 15) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 15] []) (.reg (.gpr 3))) #v[138, 134]
    (.letOp (n := 141) (.exec 0x10a030 (fun s => s.RIP = 0x10a030) (addR64R64Effect 0x10a030 3 15) (Reg.operands [.gpr 3, .gpr 15] [])) #v[138, 134]
    (.letOp (n := 142) (.out 0x10a033 (movR64R64Effect 0x10a033 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 15] []) (.reg (.gpr 1))) #v[134]
    (.letOp (n := 143) (.exec 0x10a033 (fun s => s.RIP = 0x10a033) (movR64R64Effect 0x10a033 1 15) (Reg.operands [.gpr 15] [])) #v[134]
    (.letOp (n := 144) (.out 0x10a036 (notR64Effect 0x10a036 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[142]
    (.letOp (n := 145) (.exec 0x10a036 (fun s => s.RIP = 0x10a036) (notR64Effect 0x10a036 1) (Reg.operands [.gpr 1] [])) #v[142]
    (.letOp (n := 146) (.out 0x10a039 (orR64R64Effect 0x10a039 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 3] []) (.reg (.gpr 1))) #v[144, 140]
    (.letOp (n := 147) (.exec 0x10a039 (fun s => s.RIP = 0x10a039) (orR64R64Effect 0x10a039 1 3) (Reg.operands [.gpr 1, .gpr 3] [])) #v[144, 140]
    (.letOp (n := 148) (.out 0x10a03c (shrR64Effect 0x10a03c 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[146]
    (.letOp (n := 149) (.exec 0x10a03c (fun s => s.RIP = 0x10a03c) (shrR64Effect 0x10a03c 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[146]
    (.letOp (n := 150) (.exec 0x10a040 (StorePre 0x10a040 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10a040 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10a040 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[148, 65]
    (.letOp (n := 151) (.out 0x10a045 (subR64M64Effect 0x10a045 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 4] []) (.reg (.gpr 7))) #v[112, 65]
    (.letOp (n := 152) (.exec 0x10a045 (LoadPre 0x10a045 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10a045 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x10a045 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[112, 65]
    (.letOp (n := 153) (.out 0x10a04a (shrR64Effect 0x10a04a 4 7 63) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[151]
    (.letOp (n := 154) (.exec 0x10a04a (fun s => s.RIP = 0x10a04a) (shrR64Effect 0x10a04a 4 7 63) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[151]
    (.letOp (n := 155) (.out 0x10a04e (callEffect (fun _ => 0x127d50) 0x10a053) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 156) (.exec 0x10a04e (PushPre 0x10a04e 5) (callEffect (fun _ => 0x127d50) 0x10a053) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 157) (.const ⟨64, 0x10a053⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(1, 148), (2, 120), (3, 140), (4, 155), (5, 114), (6, 6), (7, 153), (8, 8), (9, 9), (10, 10), (11, 11), (12, 89), (13, 97), (14, 68), (15, 134), (22, 22), (39, 39), (50, 50), (51, 51)] 158⟩ { target := .l10a053, kept := #v[], arity := rfl, guard := some (Fin.last 157) }))))))))))))))))))))))))))))))))

def bytes_l109f80_2 : List UInt8 :=
  [0x48, 0x09, 0xD1, 0x48, 0xC1, 0xE9, 0x3F, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x8B, 0x5C, 0x24,
    0x08, 0x4C, 0x8B, 0x7E, 0x18, 0x48, 0xFF, 0xCB, 0x48, 0xC1, 0xEB, 0x3F, 0x4C, 0x01, 0xFB, 0x4C,
    0x89, 0xF9, 0x48, 0xF7, 0xD1, 0x48, 0x09, 0xD9, 0x48, 0xC1, 0xE9, 0x3F, 0x48, 0x89, 0x4C, 0x24,
    0x08, 0x48, 0x2B, 0x7C, 0x24, 0x08, 0x48, 0xC1, 0xEF, 0x3F, 0xE8, 0xFD, 0xDC, 0x01, 0x00]

theorem code_l109f80_2 : ∀ x ∈ codeRange 0x10a014 bytes_l109f80_2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xa014 63 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109f80_1 : Block Op Label signature Reg.count 89 :=
  .letOp (n := 89) (.out 0x109fc6 (movR64M64Effect 0x109fc6 12 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 6] []) (.reg (.gpr 12))) #v[6]
    (.letOp (n := 90) (.exec 0x109fc6 (LoadPre 0x109fc6 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x109fc6 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109fc6 12 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 91) (.out 0x109fca (sarR64Effect 0x109fca 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[87]
    (.letOp (n := 92) (.exec 0x109fca (fun s => s.RIP = 0x109fca) (sarR64Effect 0x109fca 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[87]
    (.letOp (n := 93) (.out 0x109fce (movR64Imm64Effect 0x109fce 13 0x4551231950b75fc5) (EffectPart.reads (.reg (.gpr 13)) [] []) (.reg (.gpr 13))) #v[]
    (.letOp (n := 94) (.exec 0x109fce (fun s => s.RIP = 0x109fce) (movR64Imm64Effect 0x109fce 13 0x4551231950b75fc5) (Reg.operands [] [])) #v[]
    (.letOp (n := 95) (.out 0x109fd8 (addR64R64Effect 0x109fd8 13 12) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 12] []) (.reg (.gpr 13))) #v[93, 89]
    (.letOp (n := 96) (.exec 0x109fd8 (fun s => s.RIP = 0x109fd8) (addR64R64Effect 0x109fd8 13 12) (Reg.operands [.gpr 13, .gpr 12] [])) #v[93, 89]
    (.letOp (n := 97) (.out 0x109fdb (addR64R64Effect 0x109fdb 13 1) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 1] []) (.reg (.gpr 13))) #v[95, 91]
    (.letOp (n := 98) (.exec 0x109fdb (fun s => s.RIP = 0x109fdb) (addR64R64Effect 0x109fdb 13 1) (Reg.operands [.gpr 13, .gpr 1] [])) #v[95, 91]
    (.letOp (n := 99) (.out 0x109fde (movR64R64Effect 0x109fde 1 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 12] []) (.reg (.gpr 1))) #v[89]
    (.letOp (n := 100) (.exec 0x109fde (fun s => s.RIP = 0x109fde) (movR64R64Effect 0x109fde 1 12) (Reg.operands [.gpr 12] [])) #v[89]
    (.letOp (n := 101) (.out 0x109fe1 (notR64Effect 0x109fe1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[99]
    (.letOp (n := 102) (.exec 0x109fe1 (fun s => s.RIP = 0x109fe1) (notR64Effect 0x109fe1 1) (Reg.operands [.gpr 1] [])) #v[99]
    (.letOp (n := 103) (.out 0x109fe4 (orR64R64Effect 0x109fe4 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 13] []) (.reg (.gpr 1))) #v[101, 97]
    (.letOp (n := 104) (.exec 0x109fe4 (fun s => s.RIP = 0x109fe4) (orR64R64Effect 0x109fe4 1 13) (Reg.operands [.gpr 1, .gpr 13] [])) #v[101, 97]
    (.letOp (n := 105) (.out 0x109fe7 (shrR64Effect 0x109fe7 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[103]
    (.letOp (n := 106) (.exec 0x109fe7 (fun s => s.RIP = 0x109fe7) (shrR64Effect 0x109fe7 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[103]
    (.letOp (n := 107) (.exec 0x109feb (StorePre 0x109feb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109feb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109feb 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[105, 65]
    (.letOp (n := 108) (.out 0x109ff0 (xorR32R32Effect 0x109ff0 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[105, 105]
    (.letOp (n := 109) (.exec 0x109ff0 (fun s => s.RIP = 0x109ff0) (xorR32R32Effect 0x109ff0 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[105, 105]
    (.letOp (n := 110) (.out 0x109ff2 (subR64M64Effect 0x109ff2 1 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 4] []) (.reg (.gpr 1))) #v[108, 65]
    (.letOp (n := 111) (.exec 0x109ff2 (LoadPre 0x109ff2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109ff2 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x109ff2 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[108, 65]
    (.letOp (n := 112) (.out 0x109ff7 (xorR32R32Effect 0x109ff7 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[7, 7]
    (.letOp (n := 113) (.exec 0x109ff7 (fun s => s.RIP = 0x109ff7) (xorR32R32Effect 0x109ff7 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[7, 7]
    (.letOp (n := 114) (.out 0x109ff9 (movR64M64Effect 0x109ff9 5 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 6] []) (.reg (.gpr 5))) #v[6]
    (.letOp (n := 115) (.exec 0x109ff9 (LoadPre 0x109ff9 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x109ff9 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109ff9 5 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 116) (.out 0x109ffd (sarR64Effect 0x109ffd 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[110]
    (.letOp (n := 117) (.exec 0x109ffd (fun s => s.RIP = 0x109ffd) (sarR64Effect 0x109ffd 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[110]
    (.letOp (n := 118) (.out 0x10a001 (leaR64Effect 0x10a001 2 (.sib 1 (some 5) 0 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 5] []) (.reg (.gpr 2))) #v[116, 114]
    (.letOp (n := 119) (.exec 0x10a001 (fun s => s.RIP = 0x10a001) (leaR64Effect 0x10a001 2 (.sib 1 (some 5) 0 .none)) (Reg.operands [.gpr 1, .gpr 5] [])) #v[116, 114]
    (.letOp (n := 120) (.out 0x10a005 (addR64Imm8Effect 0x10a005 2 0x2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[118]
    (.letOp (n := 121) (.exec 0x10a005 (fun s => s.RIP = 0x10a005) (addR64Imm8Effect 0x10a005 2 0x2) (Reg.operands [.gpr 2] [])) #v[118]
    (.letOp (n := 122) (.exec 0x10a009 (StorePre 0x10a009 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10a009 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10a009 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[120, 65]
    (.letOp (n := 123) (.out 0x10a00e (movR64R64Effect 0x10a00e 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[114]
    (.letOp (n := 124) (.exec 0x10a00e (fun s => s.RIP = 0x10a00e) (movR64R64Effect 0x10a00e 1 5) (Reg.operands [.gpr 5] [])) #v[114]
    (.letOp (n := 125) (.out 0x10a011 (notR64Effect 0x10a011 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[123]
    (.letOp (n := 126) (.exec 0x10a011 (fun s => s.RIP = 0x10a011) (notR64Effect 0x10a011 1) (Reg.operands [.gpr 1] [])) #v[123]
    (b_l109f80_2))))))))))))))))))))))))))))))))))))))

def bytes_l109f80_1 : List UInt8 :=
  [0x4C, 0x8B, 0x66, 0x08, 0x48, 0xC1, 0xF9, 0x3F, 0x49, 0xBD, 0xC5, 0x5F, 0xB7, 0x50, 0x19, 0x23,
    0x51, 0x45, 0x4D, 0x01, 0xE5, 0x49, 0x01, 0xCD, 0x4C, 0x89, 0xE1, 0x48, 0xF7, 0xD1, 0x4C, 0x09,
    0xE9, 0x48, 0xC1, 0xE9, 0x3F, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x31, 0xC9, 0x48, 0x2B, 0x4C, 0x24,
    0x08, 0x31, 0xFF, 0x48, 0x8B, 0x6E, 0x10, 0x48, 0xC1, 0xF9, 0x3F, 0x48, 0x8D, 0x14, 0x29, 0x48,
    0x83, 0xC2, 0x02, 0x48, 0x89, 0x54, 0x24, 0x10, 0x48, 0x89, 0xE9, 0x48, 0xF7, 0xD1] ++ bytes_l109f80_2

theorem code_l109f80_1 : ∀ x ∈ codeRange 0x109fc6 bytes_l109f80_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x9fc6 78 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l109f80_2

@[cfg_block] def b_l109f80 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x109f80 (pushR64Effect 0x109f80 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x109f80 (PushPre 0x109f80 1) (pushR64Effect 0x109f80 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x109f81 (pushR64Effect 0x109f81 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x109f81 (PushPre 0x109f81 2) (pushR64Effect 0x109f81 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x109f83 (pushR64Effect 0x109f83 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x109f83 (PushPre 0x109f83 2) (pushR64Effect 0x109f83 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x109f85 (pushR64Effect 0x109f85 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x109f85 (PushPre 0x109f85 2) (pushR64Effect 0x109f85 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x109f87 (pushR64Effect 0x109f87 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x109f87 (PushPre 0x109f87 2) (pushR64Effect 0x109f87 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x109f89 (pushR64Effect 0x109f89 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x109f89 (PushPre 0x109f89 1) (pushR64Effect 0x109f89 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x109f8a (subR64Imm8Effect 0x109f8a 4 0x28) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x109f8a (fun s => s.RIP = 0x109f8a) (subR64Imm8Effect 0x109f8a 4 0x28) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.exec 0x109f8e (StorePre 0x109f8e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x109f8e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109f8e 7 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[7, 65]
    (.letOp (n := 68) (.out 0x109f93 (movR64M64Effect 0x109f93 14 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 6] []) (.reg (.gpr 14))) #v[6]
    (.letOp (n := 69) (.exec 0x109f93 (LoadPre 0x109f93 (fun s => AddrMode.addr (.base 6 .none) s (0x109f93 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x109f93 14 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 70) (.out 0x109f96 (movR64Imm64Effect 0x109f96 1 0x402da1732fc9bebf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 71) (.exec 0x109f96 (fun s => s.RIP = 0x109f96) (movR64Imm64Effect 0x109f96 1 0x402da1732fc9bebf) (Reg.operands [] [])) #v[]
    (.letOp (n := 72) (.out 0x109fa0 (addR64R64Effect 0x109fa0 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 14] []) (.reg (.gpr 1))) #v[70, 68]
    (.letOp (n := 73) (.exec 0x109fa0 (fun s => s.RIP = 0x109fa0) (addR64R64Effect 0x109fa0 1 14) (Reg.operands [.gpr 1, .gpr 14] [])) #v[70, 68]
    (.letOp (n := 74) (.exec 0x109fa3 (StorePre 0x109fa3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x109fa3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109fa3 1 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[72, 65]
    (.letOp (n := 75) (.out 0x109fa8 (movR64R64Effect 0x109fa8 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[68]
    (.letOp (n := 76) (.exec 0x109fa8 (fun s => s.RIP = 0x109fa8) (movR64R64Effect 0x109fa8 0 14) (Reg.operands [.gpr 14] [])) #v[68]
    (.letOp (n := 77) (.out 0x109fab (notR64Effect 0x109fab 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[75]
    (.letOp (n := 78) (.exec 0x109fab (fun s => s.RIP = 0x109fab) (notR64Effect 0x109fab 0) (Reg.operands [.gpr 0] [])) #v[75]
    (.letOp (n := 79) (.out 0x109fae (orR64R64Effect 0x109fae 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[77, 72]
    (.letOp (n := 80) (.exec 0x109fae (fun s => s.RIP = 0x109fae) (orR64R64Effect 0x109fae 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[77, 72]
    (.letOp (n := 81) (.out 0x109fb1 (shrR64Effect 0x109fb1 4 0 63) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[79]
    (.letOp (n := 82) (.exec 0x109fb1 (fun s => s.RIP = 0x109fb1) (shrR64Effect 0x109fb1 4 0 63) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[79]
    (.letOp (n := 83) (.exec 0x109fb5 (StorePre 0x109fb5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109fb5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109fb5 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[81, 65]
    (.letOp (n := 84) (.exec 0x109fba (fun s => s.RIP = 0x109fba) (leaR64Effect 0x109fba 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 85) (.out 0x109fbf (xorR32R32Effect 0x109fbf 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[72, 72]
    (.letOp (n := 86) (.exec 0x109fbf (fun s => s.RIP = 0x109fbf) (xorR32R32Effect 0x109fbf 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[72, 72]
    (.letOp (n := 87) (.out 0x109fc1 (subR64M64Effect 0x109fc1 1 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 4] []) (.reg (.gpr 1))) #v[85, 65]
    (.letOp (n := 88) (.exec 0x109fc1 (LoadPre 0x109fc1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109fc1 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x109fc1 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[85, 65]
    (b_l109f80_1))))))))))))))))))))))))))))))))))))

def bytes_l109f80 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x83, 0xEC, 0x28, 0x48, 0x89,
    0x7C, 0x24, 0x20, 0x4C, 0x8B, 0x36, 0x48, 0xB9, 0xBF, 0xBE, 0xC9, 0x2F, 0x73, 0xA1, 0x2D, 0x40,
    0x4C, 0x01, 0xF1, 0x48, 0x89, 0x4C, 0x24, 0x18, 0x4C, 0x89, 0xF0, 0x48, 0xF7, 0xD0, 0x48, 0x09,
    0xC8, 0x48, 0xC1, 0xE8, 0x3F, 0x48, 0x89, 0x44, 0x24, 0x08, 0x48, 0x8D, 0x44, 0x24, 0x08, 0x31,
    0xC9, 0x48, 0x2B, 0x4C, 0x24, 0x08] ++ bytes_l109f80_1

theorem code_l109f80 : ∀ x ∈ codeRange 0x109f80 bytes_l109f80, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x9f80 70 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l109f80_1

@[cfg_block] def b_l10a053 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10a053 (notR8Effect 0x10a053 2 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 54) (.exec 0x10a053 (fun s => s.RIP = 0x10a053) (notR8Effect 0x10a053 2 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x10a055 (andAlImm8Effect 0x10a055 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x10a055 (fun s => s.RIP = 0x10a055) (andAlImm8Effect 0x10a055 0x1) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x10a057 (movzxR32R8Effect 0x10a057 3 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[55]
    (.letOp (n := 58) (.exec 0x10a057 (fun s => s.RIP = 0x10a057) (movzxR32R8Effect 0x10a057 3 7 0) (Reg.operands [.gpr 0] [])) #v[55]
    (.letOp (n := 59) (.out 0x10a05a (callEffect (fun _ => 0x127d50) 0x10a05f) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x10a05a (PushPre 0x10a05a 5) (callEffect (fun _ => 0x127d50) 0x10a05f) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x10a05f⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(0, 55), (1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l10a05f, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l10a053 : List UInt8 :=
  [0xF6, 0xD0, 0x24, 0x01, 0x0F, 0xB6, 0xF8, 0xE8, 0xF1, 0xDC, 0x01, 0x00]

theorem code_l10a053 : ∀ x ∈ codeRange 0x10a053 bytes_l10a053, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xa053 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10a05f_1 : Block Op Label signature Reg.count 88 :=
  .letOp (n := 88) (.out 0x10a0a8 (popR64Effect 0x10a0a8 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[86]
    (.letOp (n := 89) (.out 0x10a0a8 (popR64Effect 0x10a0a8 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[86]
    (.letOp (n := 90) (.exec 0x10a0a8 (PopPre 0x10a0a8) (popR64Effect 0x10a0a8 2 12) (Reg.operands [.gpr 4] [])) #v[86]
    (.letOp (n := 91) (.out 0x10a0aa (popR64Effect 0x10a0aa 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[89]
    (.letOp (n := 92) (.out 0x10a0aa (popR64Effect 0x10a0aa 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[89]
    (.letOp (n := 93) (.exec 0x10a0aa (PopPre 0x10a0aa) (popR64Effect 0x10a0aa 2 13) (Reg.operands [.gpr 4] [])) #v[89]
    (.letOp (n := 94) (.out 0x10a0ac (popR64Effect 0x10a0ac 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[92]
    (.letOp (n := 95) (.out 0x10a0ac (popR64Effect 0x10a0ac 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[92]
    (.letOp (n := 96) (.exec 0x10a0ac (PopPre 0x10a0ac) (popR64Effect 0x10a0ac 2 14) (Reg.operands [.gpr 4] [])) #v[92]
    (.letOp (n := 97) (.out 0x10a0ae (popR64Effect 0x10a0ae 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[95]
    (.letOp (n := 98) (.out 0x10a0ae (popR64Effect 0x10a0ae 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[95]
    (.letOp (n := 99) (.exec 0x10a0ae (PopPre 0x10a0ae) (popR64Effect 0x10a0ae 2 15) (Reg.operands [.gpr 4] [])) #v[95]
    (.letOp (n := 100) (.out 0x10a0b0 (popR64Effect 0x10a0b0 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[98]
    (.letOp (n := 101) (.out 0x10a0b0 (popR64Effect 0x10a0b0 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[98]
    (.letOp (n := 102) (.exec 0x10a0b0 (PopPre 0x10a0b0) (popR64Effect 0x10a0b0 1 5) (Reg.operands [.gpr 4] [])) #v[98]
    (.letOp (n := 103) (.out 0x10a0b1 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[101]
    (.letOp (n := 104) (.out 0x10a0b1 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[101]
    (.letOp (n := 105) (.exec 0x10a0b1 (RetPre 0x10a0b1) (retEffect) (Reg.operands [.gpr 4] [])) #v[101]
    (.terminate (.ret (RegMap.args [(0, 77), (1, 67), (2, 2), (3, 85), (4, 104), (5, 100), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 88), (13, 91), (14, 94), (15, 97), (22, 22), (39, 39), (50, 50), (51, 51)] 106) (some ⟨103, by decide⟩))))))))))))))))))))

def bytes_l10a05f_1 : List UInt8 :=
  [0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l10a05f_1 : ∀ x ∈ codeRange 0x10a0a8 bytes_l10a05f_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xa0a8 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10a05f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x10a05f (StorePre 0x10a05f 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x10a05f + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a05f 4 0 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[0, 4]
    (.letOp (n := 54) (.exec 0x10a063 (fun s => s.RIP = 0x10a063) (leaR64Effect 0x10a063 0 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10a068 (movzxR32M8Effect 0x10a068 5 0 (.sib 4 none 0 (.d8 0x7))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 56) (.exec 0x10a068 (LoadPre 0x10a068 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x10a068 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10a068 5 0 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x10a06d (movR64M64Effect 0x10a06d 1 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 58) (.exec 0x10a06d (LoadPre 0x10a06d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10a06d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10a06d 1 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x10a072 (testR8R8Effect 0x10a072 2 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[55, 55]
    (.letOp (n := 60) (.exec 0x10a072 (fun s => s.RIP = 0x10a072) (testR8R8Effect 0x10a072 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[55, 55]
    (.letOp (n := 61) (.out 0x10a074 (atFlags (condHolds 5) (cmovR64R64Effect 0x10a074 4 14 1)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 14))) #v[14, 57, 59]
    (.letOp (n := 62) (.exec 0x10a074 (fun s => s.RIP = 0x10a074) (atFlags (condHolds 5) (cmovR64R64Effect 0x10a074 4 14 1)) (Reg.operands [.gpr 14, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[14, 57, 59]
    (.letOp (n := 63) (.out 0x10a078 (testR8R8Effect 0x10a078 2 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[55, 55]
    (.letOp (n := 64) (.exec 0x10a078 (fun s => s.RIP = 0x10a078) (testR8R8Effect 0x10a078 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[55, 55]
    (.letOp (n := 65) (.out 0x10a07a (atFlags (condHolds 5) (cmovR64R64Effect 0x10a07a 4 12 13)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 12))) #v[12, 13, 63]
    (.letOp (n := 66) (.exec 0x10a07a (fun s => s.RIP = 0x10a07a) (atFlags (condHolds 5) (cmovR64R64Effect 0x10a07a 4 12 13)) (Reg.operands [.gpr 12, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[12, 13, 63]
    (.letOp (n := 67) (.out 0x10a07e (movR64M64Effect 0x10a07e 1 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 68) (.exec 0x10a07e (LoadPre 0x10a07e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10a07e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10a07e 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.out 0x10a083 (testR8R8Effect 0x10a083 2 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[55, 55]
    (.letOp (n := 70) (.exec 0x10a083 (fun s => s.RIP = 0x10a083) (testR8R8Effect 0x10a083 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[55, 55]
    (.letOp (n := 71) (.out 0x10a085 (atFlags (condHolds 5) (cmovR64R64Effect 0x10a085 4 5 1)) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 5))) #v[5, 67, 69]
    (.letOp (n := 72) (.exec 0x10a085 (fun s => s.RIP = 0x10a085) (atFlags (condHolds 5) (cmovR64R64Effect 0x10a085 4 5 1)) (Reg.operands [.gpr 5, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[5, 67, 69]
    (.letOp (n := 73) (.out 0x10a089 (testR8R8Effect 0x10a089 2 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[55, 55]
    (.letOp (n := 74) (.exec 0x10a089 (fun s => s.RIP = 0x10a089) (testR8R8Effect 0x10a089 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[55, 55]
    (.letOp (n := 75) (.out 0x10a08b (atFlags (condHolds 5) (cmovR64R64Effect 0x10a08b 4 15 3)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 15))) #v[15, 3, 73]
    (.letOp (n := 76) (.exec 0x10a08b (fun s => s.RIP = 0x10a08b) (atFlags (condHolds 5) (cmovR64R64Effect 0x10a08b 4 15 3)) (Reg.operands [.gpr 15, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[15, 3, 73]
    (.letOp (n := 77) (.out 0x10a08f (movR64M64Effect 0x10a08f 0 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 78) (.exec 0x10a08f (LoadPre 0x10a08f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10a08f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10a08f 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.exec 0x10a094 (StorePre 0x10a094 3 (fun s => AddrMode.addr (.base 0 .none) s (0x10a094 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x10a094 14 (.base 0 .none)) (Reg.operands [.gpr 14, .gpr 0] [])) #v[61, 77]
    (.letOp (n := 80) (.exec 0x10a097 (StorePre 0x10a097 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x10a097 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10a097 12 (.base 0 (.d8 0x8))) (Reg.operands [.gpr 12, .gpr 0] [])) #v[65, 77]
    (.letOp (n := 81) (.exec 0x10a09b (StorePre 0x10a09b 4 (fun s => AddrMode.addr (.base 0 (.d8 0x10)) s (0x10a09b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10a09b 5 (.base 0 (.d8 0x10))) (Reg.operands [.gpr 5, .gpr 0] [])) #v[71, 77]
    (.letOp (n := 82) (.exec 0x10a09f (StorePre 0x10a09f 4 (fun s => AddrMode.addr (.base 0 (.d8 0x18)) s (0x10a09f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10a09f 15 (.base 0 (.d8 0x18))) (Reg.operands [.gpr 15, .gpr 0] [])) #v[75, 77]
    (.letOp (n := 83) (.out 0x10a0a3 (addR64Imm8Effect 0x10a0a3 4 0x28) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 84) (.exec 0x10a0a3 (fun s => s.RIP = 0x10a0a3) (addR64Imm8Effect 0x10a0a3 4 0x28) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 85) (.out 0x10a0a7 (popR64Effect 0x10a0a7 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[83]
    (.letOp (n := 86) (.out 0x10a0a7 (popR64Effect 0x10a0a7 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[83]
    (.letOp (n := 87) (.exec 0x10a0a7 (PopPre 0x10a0a7) (popR64Effect 0x10a0a7 1 3) (Reg.operands [.gpr 4] [])) #v[83]
    (b_l10a05f_1)))))))))))))))))))))))))))))))))))

def bytes_l10a05f : List UInt8 :=
  [0x88, 0x44, 0x24, 0x07, 0x48, 0x8D, 0x44, 0x24, 0x07, 0x0F, 0xB6, 0x44, 0x24, 0x07, 0x48, 0x8B,
    0x4C, 0x24, 0x18, 0x84, 0xC0, 0x4C, 0x0F, 0x45, 0xF1, 0x84, 0xC0, 0x4D, 0x0F, 0x45, 0xE5, 0x48,
    0x8B, 0x4C, 0x24, 0x10, 0x84, 0xC0, 0x48, 0x0F, 0x45, 0xE9, 0x84, 0xC0, 0x4C, 0x0F, 0x45, 0xFB,
    0x48, 0x8B, 0x44, 0x24, 0x20, 0x4C, 0x89, 0x30, 0x4C, 0x89, 0x60, 0x08, 0x48, 0x89, 0x68, 0x10,
    0x4C, 0x89, 0x78, 0x18, 0x48, 0x83, 0xC4, 0x28, 0x5B] ++ bytes_l10a05f_1

theorem code_l10a05f : ∀ x ∈ codeRange 0x10a05f bytes_l10a05f, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa05f 73 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a05f_1

@[cfg_block] def b_l10a0c0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10a0c0 (pushR64Effect 0x10a0c0 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[4, 15]
    (.letOp (n := 54) (.exec 0x10a0c0 (PushPre 0x10a0c0 2) (pushR64Effect 0x10a0c0 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[4, 15]
    (.letOp (n := 55) (.out 0x10a0c2 (pushR64Effect 0x10a0c2 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[53, 14]
    (.letOp (n := 56) (.exec 0x10a0c2 (PushPre 0x10a0c2 2) (pushR64Effect 0x10a0c2 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 57) (.out 0x10a0c4 (pushR64Effect 0x10a0c4 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[55, 13]
    (.letOp (n := 58) (.exec 0x10a0c4 (PushPre 0x10a0c4 2) (pushR64Effect 0x10a0c4 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[55, 13]
    (.letOp (n := 59) (.out 0x10a0c6 (pushR64Effect 0x10a0c6 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[57, 12]
    (.letOp (n := 60) (.exec 0x10a0c6 (PushPre 0x10a0c6 2) (pushR64Effect 0x10a0c6 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[57, 12]
    (.letOp (n := 61) (.out 0x10a0c8 (pushR64Effect 0x10a0c8 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[59, 3]
    (.letOp (n := 62) (.exec 0x10a0c8 (PushPre 0x10a0c8 1) (pushR64Effect 0x10a0c8 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[59, 3]
    (.letOp (n := 63) (.out 0x10a0c9 (subR64Imm8Effect 0x10a0c9 4 0x30) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 64) (.exec 0x10a0c9 (fun s => s.RIP = 0x10a0c9) (subR64Imm8Effect 0x10a0c9 4 0x30) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 65) (.out 0x10a0cd (movR64R64Effect 0x10a0cd 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 66) (.exec 0x10a0cd (fun s => s.RIP = 0x10a0cd) (movR64R64Effect 0x10a0cd 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 67) (.out 0x10a0d0 (leaR64Effect 0x10a0d0 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[63]
    (.letOp (n := 68) (.exec 0x10a0d0 (fun s => s.RIP = 0x10a0d0) (leaR64Effect 0x10a0d0 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 69) (.out 0x10a0d5 (movR64Imm64Effect 0x10a0d5 1 0xb4f20099aa774ec1) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 70) (.exec 0x10a0d5 (fun s => s.RIP = 0x10a0d5) (movR64Imm64Effect 0x10a0d5 1 0xb4f20099aa774ec1) (Reg.operands [] [])) #v[]
    (.letOp (n := 71) (.out 0x10a0df (movR64Imm32Effect 0x10a0df 2 0x2021a0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 72) (.exec 0x10a0df (fun s => s.RIP = 0x10a0df) (movR64Imm32Effect 0x10a0df 2 0x2021a0) (Reg.operands [] [])) #v[]
    (.letOp (n := 73) (.out 0x10a0e6 (movR64Imm32Effect 0x10a0e6 8 0x202180) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 74) (.exec 0x10a0e6 (fun s => s.RIP = 0x10a0e6) (movR64Imm32Effect 0x10a0e6 8 0x202180) (Reg.operands [] [])) #v[]
    (.letOp (n := 75) (.out 0x10a0ed (callEffect (fun _ => 0x109490) 0x10a0f2) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 76) (.exec 0x10a0ed (PushPre 0x10a0ed 5) (callEffect (fun _ => 0x109490) 0x10a0f2) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 77) (.const ⟨64, 0x10a0f2⟩) #v[]
    (.terminate (.call ⟨.l109490, RegMap.args [(1, 69), (2, 71), (3, 65), (4, 75), (5, 5), (6, 6), (7, 67), (8, 73), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 78⟩ { target := .l10a0f2, kept := #v[], arity := rfl, guard := some (Fin.last 77) }))))))))))))))))))))))))))

def bytes_l10a0c0 : List UInt8 :=
  [0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x83, 0xEC, 0x30, 0x48, 0x89, 0xFB,
    0x48, 0x8D, 0x7C, 0x24, 0x08, 0x48, 0xB9, 0xC1, 0x4E, 0x77, 0xAA, 0x99, 0x00, 0xF2, 0xB4, 0x48,
    0xC7, 0xC2, 0xA0, 0x21, 0x20, 0x00, 0x49, 0xC7, 0xC0, 0x80, 0x21, 0x20, 0x00, 0xE8, 0x9E, 0xF3,
    0xFF, 0xFF]

theorem code_l10a0c0 : ∀ x ∈ codeRange 0x10a0c0 bytes_l10a0c0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xa0c0 50 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10a0f2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10a0f2 (movR64M64Effect 0x10a0f2 14 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 54) (.exec 0x10a0f2 (LoadPre 0x10a0f2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10a0f2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10a0f2 14 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10a0f7 (movR64M64Effect 0x10a0f7 15 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 56) (.exec 0x10a0f7 (LoadPre 0x10a0f7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10a0f7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10a0f7 15 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x10a0fc (movR64M64Effect 0x10a0fc 12 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 58) (.exec 0x10a0fc (LoadPre 0x10a0fc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10a0fc + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10a0fc 12 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x10a101 (movR64M64Effect 0x10a101 13 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 60) (.exec 0x10a101 (LoadPre 0x10a101 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10a101 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10a101 13 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x10a106 (movR32M32LowEffect 0x10a106 7 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 62) (.exec 0x10a106 (LoadPre 0x10a106 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10a106 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x10a106 7 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x10a10a (callEffect (fun _ => 0x127d50) 0x10a10f) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 64) (.exec 0x10a10a (PushPre 0x10a10a 5) (callEffect (fun _ => 0x127d50) 0x10a10f) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.const ⟨64, 0x10a10f⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 59), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩ { target := .l10a10f, kept := #v[], arity := rfl, guard := some (Fin.last 65) }))))))))))))))

def bytes_l10a0f2 : List UInt8 :=
  [0x4C, 0x8B, 0x74, 0x24, 0x08, 0x4C, 0x8B, 0x7C, 0x24, 0x10, 0x4C, 0x8B, 0x64, 0x24, 0x18, 0x4C,
    0x8B, 0x6C, 0x24, 0x20, 0x8B, 0x7C, 0x24, 0x28, 0xE8, 0x41, 0xDC, 0x01, 0x00]

theorem code_l10a0f2 : ∀ x ∈ codeRange 0x10a0f2 bytes_l10a0f2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xa0f2 29 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10a10f_1 : Block Op Label signature Reg.count 86 :=
  .letOp (n := 86) (.out 0x10a150 (movR64R64Effect 0x10a150 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 87) (.exec 0x10a150 (fun s => s.RIP = 0x10a150) (movR64R64Effect 0x10a150 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 88) (.out 0x10a153 (addR64Imm8Effect 0x10a153 4 0x30) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 89) (.exec 0x10a153 (fun s => s.RIP = 0x10a153) (addR64Imm8Effect 0x10a153 4 0x30) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 90) (.out 0x10a157 (popR64Effect 0x10a157 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[88]
    (.letOp (n := 91) (.out 0x10a157 (popR64Effect 0x10a157 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[88]
    (.letOp (n := 92) (.exec 0x10a157 (PopPre 0x10a157) (popR64Effect 0x10a157 1 3) (Reg.operands [.gpr 4] [])) #v[88]
    (.letOp (n := 93) (.out 0x10a158 (popR64Effect 0x10a158 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[91]
    (.letOp (n := 94) (.out 0x10a158 (popR64Effect 0x10a158 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[91]
    (.letOp (n := 95) (.exec 0x10a158 (PopPre 0x10a158) (popR64Effect 0x10a158 2 12) (Reg.operands [.gpr 4] [])) #v[91]
    (.letOp (n := 96) (.out 0x10a15a (popR64Effect 0x10a15a 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[94]
    (.letOp (n := 97) (.out 0x10a15a (popR64Effect 0x10a15a 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[94]
    (.letOp (n := 98) (.exec 0x10a15a (PopPre 0x10a15a) (popR64Effect 0x10a15a 2 13) (Reg.operands [.gpr 4] [])) #v[94]
    (.letOp (n := 99) (.out 0x10a15c (popR64Effect 0x10a15c 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[97]
    (.letOp (n := 100) (.out 0x10a15c (popR64Effect 0x10a15c 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[97]
    (.letOp (n := 101) (.exec 0x10a15c (PopPre 0x10a15c) (popR64Effect 0x10a15c 2 14) (Reg.operands [.gpr 4] [])) #v[97]
    (.letOp (n := 102) (.out 0x10a15e (popR64Effect 0x10a15e 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[100]
    (.letOp (n := 103) (.out 0x10a15e (popR64Effect 0x10a15e 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[100]
    (.letOp (n := 104) (.exec 0x10a15e (PopPre 0x10a15e) (popR64Effect 0x10a15e 2 15) (Reg.operands [.gpr 4] [])) #v[100]
    (.letOp (n := 105) (.out 0x10a160 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[103]
    (.letOp (n := 106) (.out 0x10a160 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[103]
    (.letOp (n := 107) (.exec 0x10a160 (RetPre 0x10a160) (retEffect) (Reg.operands [.gpr 4] [])) #v[103]
    (.terminate (.ret (RegMap.args [(0, 86), (1, 55), (2, 79), (3, 90), (4, 106), (5, 5), (6, 63), (7, 69), (8, 75), (9, 9), (10, 10), (11, 11), (12, 93), (13, 96), (14, 99), (15, 102), (22, 22), (39, 39), (50, 50), (51, 51)] 108) (some ⟨105, by decide⟩))))))))))))))))))))))))

def bytes_l10a10f_1 : List UInt8 :=
  [0x48, 0x89, 0xD8, 0x48, 0x83, 0xC4, 0x30, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F,
    0xC3]

theorem code_l10a10f_1 : ∀ x ∈ codeRange 0x10a150 bytes_l10a10f_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xa150 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10a10f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x10a10f (StorePre 0x10a10f 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x10a10f + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a10f 4 0 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[0, 4]
    (.letOp (n := 54) (.exec 0x10a113 (fun s => s.RIP = 0x10a113) (leaR64Effect 0x10a113 1 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10a118 (movzxR32M8Effect 0x10a118 5 1 (.sib 4 none 0 (.d8 0x7))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x10a118 (LoadPre 0x10a118 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x10a118 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10a118 5 1 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x10a11d (xorR32R32Effect 0x10a11d 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[2, 2]
    (.letOp (n := 58) (.exec 0x10a11d (fun s => s.RIP = 0x10a11d) (xorR32R32Effect 0x10a11d 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 59) (.out 0x10a11f (xorR32R32Effect 0x10a11f 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[6, 6]
    (.letOp (n := 60) (.exec 0x10a11f (fun s => s.RIP = 0x10a11f) (xorR32R32Effect 0x10a11f 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 61) (.out 0x10a121 (testR8R8Effect 0x10a121 2 1 1) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 1] []) (.flag .ZF)) #v[55, 55]
    (.letOp (n := 62) (.exec 0x10a121 (fun s => s.RIP = 0x10a121) (testR8R8Effect 0x10a121 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[55, 55]
    (.letOp (n := 63) (.out 0x10a123 (atFlags (condHolds 5) (cmovR64R64Effect 0x10a123 4 6 14)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 6))) #v[59, 14, 61]
    (.letOp (n := 64) (.exec 0x10a123 (fun s => s.RIP = 0x10a123) (atFlags (condHolds 5) (cmovR64R64Effect 0x10a123 4 6 14)) (Reg.operands [.gpr 6, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[59, 14, 61]
    (.letOp (n := 65) (.out 0x10a127 (xorR32R32Effect 0x10a127 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[7, 7]
    (.letOp (n := 66) (.exec 0x10a127 (fun s => s.RIP = 0x10a127) (xorR32R32Effect 0x10a127 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[7, 7]
    (.letOp (n := 67) (.out 0x10a129 (testR8R8Effect 0x10a129 2 1 1) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 1] []) (.flag .ZF)) #v[55, 55]
    (.letOp (n := 68) (.exec 0x10a129 (fun s => s.RIP = 0x10a129) (testR8R8Effect 0x10a129 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[55, 55]
    (.letOp (n := 69) (.out 0x10a12b (atFlags (condHolds 5) (cmovR64R64Effect 0x10a12b 4 7 15)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 7))) #v[65, 15, 67]
    (.letOp (n := 70) (.exec 0x10a12b (fun s => s.RIP = 0x10a12b) (atFlags (condHolds 5) (cmovR64R64Effect 0x10a12b 4 7 15)) (Reg.operands [.gpr 7, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[65, 15, 67]
    (.letOp (n := 71) (.out 0x10a12f (xorR32R32Effect 0x10a12f 3 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 8] []) (.reg (.gpr 8))) #v[8, 8]
    (.letOp (n := 72) (.exec 0x10a12f (fun s => s.RIP = 0x10a12f) (xorR32R32Effect 0x10a12f 3 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[8, 8]
    (.letOp (n := 73) (.out 0x10a132 (testR8R8Effect 0x10a132 2 1 1) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 1] []) (.flag .ZF)) #v[55, 55]
    (.letOp (n := 74) (.exec 0x10a132 (fun s => s.RIP = 0x10a132) (testR8R8Effect 0x10a132 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[55, 55]
    (.letOp (n := 75) (.out 0x10a134 (atFlags (condHolds 5) (cmovR64R64Effect 0x10a134 4 8 12)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 8))) #v[71, 12, 73]
    (.letOp (n := 76) (.exec 0x10a134 (fun s => s.RIP = 0x10a134) (atFlags (condHolds 5) (cmovR64R64Effect 0x10a134 4 8 12)) (Reg.operands [.gpr 8, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[71, 12, 73]
    (.letOp (n := 77) (.out 0x10a138 (testR8R8Effect 0x10a138 2 1 1) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 1] []) (.flag .ZF)) #v[55, 55]
    (.letOp (n := 78) (.exec 0x10a138 (fun s => s.RIP = 0x10a138) (testR8R8Effect 0x10a138 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[55, 55]
    (.letOp (n := 79) (.out 0x10a13a (atFlags (condHolds 5) (cmovR64R64Effect 0x10a13a 4 2 13)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 2))) #v[57, 13, 77]
    (.letOp (n := 80) (.exec 0x10a13a (fun s => s.RIP = 0x10a13a) (atFlags (condHolds 5) (cmovR64R64Effect 0x10a13a 4 2 13)) (Reg.operands [.gpr 2, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[57, 13, 77]
    (.letOp (n := 81) (.exec 0x10a13e (StorePre 0x10a13e 3 (fun s => AddrMode.addr (.base 3 .none) s (0x10a13e + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x10a13e 6 (.base 3 .none)) (Reg.operands [.gpr 6, .gpr 3] [])) #v[63, 3]
    (.letOp (n := 82) (.exec 0x10a141 (StorePre 0x10a141 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x10a141 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10a141 7 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[69, 3]
    (.letOp (n := 83) (.exec 0x10a145 (StorePre 0x10a145 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x10a145 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10a145 8 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 8, .gpr 3] [])) #v[75, 3]
    (.letOp (n := 84) (.exec 0x10a149 (StorePre 0x10a149 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x10a149 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10a149 2 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[79, 3]
    (.letOp (n := 85) (.exec 0x10a14d (StorePre 0x10a14d 3 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x10a14d + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a14d 3 0 (.base 3 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (b_l10a10f_1)))))))))))))))))))))))))))))))))

def bytes_l10a10f : List UInt8 :=
  [0x88, 0x44, 0x24, 0x07, 0x48, 0x8D, 0x4C, 0x24, 0x07, 0x0F, 0xB6, 0x4C, 0x24, 0x07, 0x31, 0xD2,
    0x31, 0xF6, 0x84, 0xC9, 0x49, 0x0F, 0x45, 0xF6, 0x31, 0xFF, 0x84, 0xC9, 0x49, 0x0F, 0x45, 0xFF,
    0x45, 0x31, 0xC0, 0x84, 0xC9, 0x4D, 0x0F, 0x45, 0xC4, 0x84, 0xC9, 0x49, 0x0F, 0x45, 0xD5, 0x48,
    0x89, 0x33, 0x48, 0x89, 0x7B, 0x08, 0x4C, 0x89, 0x43, 0x10, 0x48, 0x89, 0x53, 0x18, 0x88, 0x43,
    0x20] ++ bytes_l10a10f_1

theorem code_l10a10f : ∀ x ∈ codeRange 0x10a10f bytes_l10a10f, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa10f 65 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a10f_1

@[cfg_block] def b_l10a170_2 : Block Op Label signature Reg.count 128 :=
  .letOp (n := 128) (.out 0x10a209 (movzxR32R8Effect 0x10a209 3 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[126]
    (.letOp (n := 129) (.exec 0x10a209 (fun s => s.RIP = 0x10a209) (movzxR32R8Effect 0x10a209 3 7 0) (Reg.operands [.gpr 0] [])) #v[126]
    (.letOp (n := 130) (.out 0x10a20c (callEffect (fun _ => 0x127d50) 0x10a211) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[53]
    (.letOp (n := 131) (.exec 0x10a20c (PushPre 0x10a20c 5) (callEffect (fun _ => 0x127d50) 0x10a211) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 132) (.const ⟨64, 0x10a211⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(0, 126), (1, 109), (2, 113), (3, 3), (4, 130), (5, 5), (6, 121), (7, 128), (8, 104), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 133⟩ { target := .l10a211, kept := #v[], arity := rfl, guard := some (Fin.last 132) }))))))

def bytes_l10a170_2 : List UInt8 :=
  [0x0F, 0xB6, 0xF8, 0xE8, 0x3F, 0xDB, 0x01, 0x00]

theorem code_l10a170_2 : ∀ x ∈ codeRange 0x10a209 bytes_l10a170_2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xa209 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10a170_1 : Block Op Label signature Reg.count 90 :=
  .letOp (n := 90) (.out 0x10a1be (xorR32R32Effect 0x10a1be 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[71, 71]
    (.letOp (n := 91) (.exec 0x10a1be (fun s => s.RIP = 0x10a1be) (xorR32R32Effect 0x10a1be 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[71, 71]
    (.letOp (n := 92) (.out 0x10a1c0 (movR64M64Effect 0x10a1c0 6 (.base 7 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 7] []) (.reg (.gpr 6))) #v[7]
    (.letOp (n := 93) (.exec 0x10a1c0 (LoadPre 0x10a1c0 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x10a1c0 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a1c0 6 (.base 7 (.d8 0x10))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 94) (.out 0x10a1c4 (sarR64Effect 0x10a1c4 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[88]
    (.letOp (n := 95) (.exec 0x10a1c4 (fun s => s.RIP = 0x10a1c4) (sarR64Effect 0x10a1c4 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[88]
    (.letOp (n := 96) (.out 0x10a1c8 (movR64R64Effect 0x10a1c8 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 6] []) (.reg (.gpr 8))) #v[92]
    (.letOp (n := 97) (.exec 0x10a1c8 (fun s => s.RIP = 0x10a1c8) (movR64R64Effect 0x10a1c8 8 6) (Reg.operands [.gpr 6] [])) #v[92]
    (.letOp (n := 98) (.out 0x10a1cb (notR64Effect 0x10a1cb 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[96]
    (.letOp (n := 99) (.exec 0x10a1cb (fun s => s.RIP = 0x10a1cb) (notR64Effect 0x10a1cb 8) (Reg.operands [.gpr 8] [])) #v[96]
    (.letOp (n := 100) (.out 0x10a1ce (addR64R64Effect 0x10a1ce 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[98, 94]
    (.letOp (n := 101) (.exec 0x10a1ce (fun s => s.RIP = 0x10a1ce) (addR64R64Effect 0x10a1ce 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[98, 94]
    (.letOp (n := 102) (.out 0x10a1d1 (andR64R64Effect 0x10a1d1 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6] []) (.reg (.gpr 8))) #v[100, 92]
    (.letOp (n := 103) (.exec 0x10a1d1 (fun s => s.RIP = 0x10a1d1) (andR64R64Effect 0x10a1d1 8 6) (Reg.operands [.gpr 8, .gpr 6] [])) #v[100, 92]
    (.letOp (n := 104) (.out 0x10a1d4 (shrR64Effect 0x10a1d4 4 8 63) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[102]
    (.letOp (n := 105) (.exec 0x10a1d4 (fun s => s.RIP = 0x10a1d4) (shrR64Effect 0x10a1d4 4 8 63) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[102]
    (.letOp (n := 106) (.exec 0x10a1d8 (StorePre 0x10a1d8 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10a1d8 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10a1d8 8 (.sib 4 none 0 .none)) (Reg.operands [.gpr 8, .gpr 4] [])) #v[104, 53]
    (.letOp (n := 107) (.out 0x10a1dc (subR64M64Effect 0x10a1dc 2 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 4] []) (.reg (.gpr 2))) #v[90, 53]
    (.letOp (n := 108) (.exec 0x10a1dc (LoadPre 0x10a1dc (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10a1dc + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x10a1dc 2 (.sib 4 none 0 .none)) (Reg.operands [.gpr 2, .gpr 4] [])) #v[90, 53]
    (.letOp (n := 109) (.out 0x10a1e0 (movR64M64Effect 0x10a1e0 1 (.base 7 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 7] []) (.reg (.gpr 1))) #v[7]
    (.letOp (n := 110) (.exec 0x10a1e0 (LoadPre 0x10a1e0 (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x10a1e0 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a1e0 1 (.base 7 (.d8 0x18))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 111) (.out 0x10a1e4 (sarR64Effect 0x10a1e4 4 2 63) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[107]
    (.letOp (n := 112) (.exec 0x10a1e4 (fun s => s.RIP = 0x10a1e4) (sarR64Effect 0x10a1e4 4 2 63) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[107]
    (.letOp (n := 113) (.out 0x10a1e8 (subR64R64Effect 0x10a1e8 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[111, 109]
    (.letOp (n := 114) (.exec 0x10a1e8 (fun s => s.RIP = 0x10a1e8) (subR64R64Effect 0x10a1e8 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[111, 109]
    (.letOp (n := 115) (.out 0x10a1eb (movR64Imm64Effect 0x10a1eb 6 0x7fffffffffffffff) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 116) (.exec 0x10a1eb (fun s => s.RIP = 0x10a1eb) (movR64Imm64Effect 0x10a1eb 6 0x7fffffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 117) (.out 0x10a1f5 (addR64R64Effect 0x10a1f5 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[115, 113]
    (.letOp (n := 118) (.exec 0x10a1f5 (fun s => s.RIP = 0x10a1f5) (addR64R64Effect 0x10a1f5 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[115, 113]
    (.letOp (n := 119) (.out 0x10a1f8 (orR64R64Effect 0x10a1f8 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[117, 109]
    (.letOp (n := 120) (.exec 0x10a1f8 (fun s => s.RIP = 0x10a1f8) (orR64R64Effect 0x10a1f8 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[117, 109]
    (.letOp (n := 121) (.out 0x10a1fb (shrR64Effect 0x10a1fb 4 6 63) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[119]
    (.letOp (n := 122) (.exec 0x10a1fb (fun s => s.RIP = 0x10a1fb) (shrR64Effect 0x10a1fb 4 6 63) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[119]
    (.letOp (n := 123) (.exec 0x10a1ff (StorePre 0x10a1ff 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10a1ff + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10a1ff 6 (.sib 4 none 0 .none)) (Reg.operands [.gpr 6, .gpr 4] [])) #v[121, 53]
    (.letOp (n := 124) (.out 0x10a203 (movzxR32M8Effect 0x10a203 4 0 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 125) (.exec 0x10a203 (LoadPre 0x10a203 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10a203 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a203 4 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 126) (.out 0x10a207 (andAlImm8Effect 0x10a207 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[124]
    (.letOp (n := 127) (.exec 0x10a207 (fun s => s.RIP = 0x10a207) (andAlImm8Effect 0x10a207 0x1) (Reg.operands [.gpr 0] [])) #v[124]
    (b_l10a170_2))))))))))))))))))))))))))))))))))))))

def bytes_l10a170_1 : List UInt8 :=
  [0x31, 0xD2, 0x48, 0x8B, 0x77, 0x10, 0x48, 0xC1, 0xF9, 0x3F, 0x49, 0x89, 0xF0, 0x49, 0xF7, 0xD0,
    0x49, 0x01, 0xC8, 0x49, 0x21, 0xF0, 0x49, 0xC1, 0xE8, 0x3F, 0x4C, 0x89, 0x04, 0x24, 0x48, 0x2B,
    0x14, 0x24, 0x48, 0x8B, 0x4F, 0x18, 0x48, 0xC1, 0xFA, 0x3F, 0x48, 0x29, 0xCA, 0x48, 0xBE, 0xFF,
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F, 0x48, 0x01, 0xD6, 0x48, 0x09, 0xCE, 0x48, 0xC1, 0xEE,
    0x3F, 0x48, 0x89, 0x34, 0x24, 0x0F, 0xB6, 0x04, 0x24, 0x24, 0x01] ++ bytes_l10a170_2

theorem code_l10a170_1 : ∀ x ∈ codeRange 0x10a1be bytes_l10a170_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa1be 75 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a170_2

@[cfg_block] def b_l10a170 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10a170 (pushR64Effect 0x10a170 1 0) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 0] []) (.reg (.gpr 4))) #v[4, 0]
    (.letOp (n := 54) (.exec 0x10a170 (PushPre 0x10a170 1) (pushR64Effect 0x10a170 1 0) (Reg.operands [.gpr 4, .gpr 0] [])) #v[4, 0]
    (.letOp (n := 55) (.out 0x10a171 (movR64M64Effect 0x10a171 0 (.base 7 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 56) (.exec 0x10a171 (LoadPre 0x10a171 (fun s => AddrMode.addr (.base 7 .none) s (0x10a171 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x10a171 0 (.base 7 .none)) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 57) (.out 0x10a174 (movR64Imm64Effect 0x10a174 1 0xdfe92f46681b20a0) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 58) (.exec 0x10a174 (fun s => s.RIP = 0x10a174) (movR64Imm64Effect 0x10a174 1 0xdfe92f46681b20a0) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x10a17e (subR64R64Effect 0x10a17e 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[57, 55]
    (.letOp (n := 60) (.exec 0x10a17e (fun s => s.RIP = 0x10a17e) (subR64R64Effect 0x10a17e 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[57, 55]
    (.letOp (n := 61) (.out 0x10a181 (andR64R64Effect 0x10a181 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[59, 55]
    (.letOp (n := 62) (.exec 0x10a181 (fun s => s.RIP = 0x10a181) (andR64R64Effect 0x10a181 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[59, 55]
    (.letOp (n := 63) (.out 0x10a184 (shrR64Effect 0x10a184 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[61]
    (.letOp (n := 64) (.exec 0x10a184 (fun s => s.RIP = 0x10a184) (shrR64Effect 0x10a184 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[61]
    (.letOp (n := 65) (.exec 0x10a188 (StorePre 0x10a188 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10a188 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10a188 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 1, .gpr 4] [])) #v[63, 53]
    (.letOp (n := 66) (.exec 0x10a18c (fun s => s.RIP = 0x10a18c) (movR64R64Effect 0x10a18c 0 4) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 67) (.out 0x10a18f (xorR32R32Effect 0x10a18f 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[63, 63]
    (.letOp (n := 68) (.exec 0x10a18f (fun s => s.RIP = 0x10a18f) (xorR32R32Effect 0x10a18f 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[63, 63]
    (.letOp (n := 69) (.out 0x10a191 (subR64M64Effect 0x10a191 1 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 4] []) (.reg (.gpr 1))) #v[67, 53]
    (.letOp (n := 70) (.exec 0x10a191 (LoadPre 0x10a191 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10a191 + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x10a191 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 1, .gpr 4] [])) #v[67, 53]
    (.letOp (n := 71) (.out 0x10a195 (movR64M64Effect 0x10a195 2 (.base 7 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7] []) (.reg (.gpr 2))) #v[7]
    (.letOp (n := 72) (.exec 0x10a195 (LoadPre 0x10a195 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x10a195 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a195 2 (.base 7 (.d8 0x8))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 73) (.out 0x10a199 (sarR64Effect 0x10a199 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[69]
    (.letOp (n := 74) (.exec 0x10a199 (fun s => s.RIP = 0x10a199) (sarR64Effect 0x10a199 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[69]
    (.letOp (n := 75) (.out 0x10a19d (subR64R64Effect 0x10a19d 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[73, 71]
    (.letOp (n := 76) (.exec 0x10a19d (fun s => s.RIP = 0x10a19d) (subR64R64Effect 0x10a19d 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[73, 71]
    (.letOp (n := 77) (.out 0x10a1a0 (movR64Imm64Effect 0x10a1a0 6 0x5d576e7357a4501d) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 78) (.exec 0x10a1a0 (fun s => s.RIP = 0x10a1a0) (movR64Imm64Effect 0x10a1a0 6 0x5d576e7357a4501d) (Reg.operands [] [])) #v[]
    (.letOp (n := 79) (.out 0x10a1aa (addR64R64Effect 0x10a1aa 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[77, 75]
    (.letOp (n := 80) (.exec 0x10a1aa (fun s => s.RIP = 0x10a1aa) (addR64R64Effect 0x10a1aa 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[77, 75]
    (.letOp (n := 81) (.out 0x10a1ad (orR64R64Effect 0x10a1ad 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[79, 71]
    (.letOp (n := 82) (.exec 0x10a1ad (fun s => s.RIP = 0x10a1ad) (orR64R64Effect 0x10a1ad 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[79, 71]
    (.letOp (n := 83) (.out 0x10a1b0 (shrR64Effect 0x10a1b0 4 6 63) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[81]
    (.letOp (n := 84) (.exec 0x10a1b0 (fun s => s.RIP = 0x10a1b0) (shrR64Effect 0x10a1b0 4 6 63) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[81]
    (.letOp (n := 85) (.exec 0x10a1b4 (StorePre 0x10a1b4 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10a1b4 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10a1b4 6 (.sib 4 none 0 .none)) (Reg.operands [.gpr 6, .gpr 4] [])) #v[83, 53]
    (.letOp (n := 86) (.out 0x10a1b8 (xorR32R32Effect 0x10a1b8 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[75, 75]
    (.letOp (n := 87) (.exec 0x10a1b8 (fun s => s.RIP = 0x10a1b8) (xorR32R32Effect 0x10a1b8 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[75, 75]
    (.letOp (n := 88) (.out 0x10a1ba (subR64M64Effect 0x10a1ba 1 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 4] []) (.reg (.gpr 1))) #v[86, 53]
    (.letOp (n := 89) (.exec 0x10a1ba (LoadPre 0x10a1ba (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10a1ba + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x10a1ba 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 1, .gpr 4] [])) #v[86, 53]
    (b_l10a170_1)))))))))))))))))))))))))))))))))))))

def bytes_l10a170 : List UInt8 :=
  [0x50, 0x48, 0x8B, 0x07, 0x48, 0xB9, 0xA0, 0x20, 0x1B, 0x68, 0x46, 0x2F, 0xE9, 0xDF, 0x48, 0x29,
    0xC1, 0x48, 0x21, 0xC1, 0x48, 0xC1, 0xE9, 0x3F, 0x48, 0x89, 0x0C, 0x24, 0x48, 0x89, 0xE0, 0x31,
    0xC9, 0x48, 0x2B, 0x0C, 0x24, 0x48, 0x8B, 0x57, 0x08, 0x48, 0xC1, 0xF9, 0x3F, 0x48, 0x29, 0xD1,
    0x48, 0xBE, 0x1D, 0x50, 0xA4, 0x57, 0x73, 0x6E, 0x57, 0x5D, 0x48, 0x01, 0xCE, 0x48, 0x09, 0xD6,
    0x48, 0xC1, 0xEE, 0x3F, 0x48, 0x89, 0x34, 0x24, 0x31, 0xC9, 0x48, 0x2B, 0x0C, 0x24] ++ bytes_l10a170_1

theorem code_l10a170 : ∀ x ∈ codeRange 0x10a170 bytes_l10a170, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa170 78 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a170_1

@[cfg_block] def b_l10a211 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10a211 (popR64Effect 0x10a211 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.out 0x10a211 (popR64Effect 0x10a211 1 1) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 55) (.exec 0x10a211 (PopPre 0x10a211) (popR64Effect 0x10a211 1 1) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x10a212 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[54]
    (.letOp (n := 57) (.out 0x10a212 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[54]
    (.letOp (n := 58) (.exec 0x10a212 (RetPre 0x10a212) (retEffect) (Reg.operands [.gpr 4] [])) #v[54]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 53), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 59) (some ⟨56, by decide⟩))))))))

def bytes_l10a211 : List UInt8 :=
  [0x59, 0xC3]

theorem code_l10a211 : ∀ x ∈ codeRange 0x10a211 bytes_l10a211, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xa211 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10a220_1 : Block Op Label signature Reg.count 91 :=
  .letOp (n := 91) (.out 0x10a263 (atFlags (condHolds 5) (cmovR64R64Effect 0x10a263 4 6 2)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 6))) #v[63, 87, 89]
    (.letOp (n := 92) (.exec 0x10a263 (fun s => s.RIP = 0x10a263) (atFlags (condHolds 5) (cmovR64R64Effect 0x10a263 4 6 2)) (Reg.operands [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[63, 87, 89]
    (.letOp (n := 93) (.exec 0x10a267 (StorePre 0x10a267 3 (fun s => AddrMode.addr (.base 0 .none) s (0x10a267 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x10a267 7 (.base 0 .none)) (Reg.operands [.gpr 7, .gpr 0] [])) #v[75, 55]
    (.letOp (n := 94) (.exec 0x10a26a (StorePre 0x10a26a 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x10a26a + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10a26a 8 (.base 0 (.d8 0x8))) (Reg.operands [.gpr 8, .gpr 0] [])) #v[79, 55]
    (.letOp (n := 95) (.exec 0x10a26e (StorePre 0x10a26e 4 (fun s => AddrMode.addr (.base 0 (.d8 0x10)) s (0x10a26e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10a26e 9 (.base 0 (.d8 0x10))) (Reg.operands [.gpr 9, .gpr 0] [])) #v[85, 55]
    (.letOp (n := 96) (.exec 0x10a272 (StorePre 0x10a272 4 (fun s => AddrMode.addr (.base 0 (.d8 0x18)) s (0x10a272 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10a272 6 (.base 0 (.d8 0x18))) (Reg.operands [.gpr 6, .gpr 0] [])) #v[91, 55]
    (.letOp (n := 97) (.out 0x10a276 (addR64Imm8Effect 0x10a276 4 0x1) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[53]
    (.letOp (n := 98) (.exec 0x10a276 (fun s => s.RIP = 0x10a276) (addR64Imm8Effect 0x10a276 4 0x1) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 99) (.out 0x10a27a (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[97]
    (.letOp (n := 100) (.out 0x10a27a (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[97]
    (.letOp (n := 101) (.exec 0x10a27a (RetPre 0x10a27a) (retEffect) (Reg.operands [.gpr 4] [])) #v[97]
    (.terminate (.ret (RegMap.args [(0, 55), (1, 67), (2, 87), (3, 3), (4, 100), (5, 5), (6, 91), (7, 75), (8, 79), (9, 85), (10, 81), (11, 71), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 102) (some ⟨99, by decide⟩)))))))))))))

def bytes_l10a220_1 : List UInt8 :=
  [0x48, 0x0F, 0x45, 0xF2, 0x48, 0x89, 0x38, 0x4C, 0x89, 0x40, 0x08, 0x4C, 0x89, 0x48, 0x10, 0x48,
    0x89, 0x70, 0x18, 0x48, 0x83, 0xC4, 0x01, 0xC3]

theorem code_l10a220_1 : ∀ x ∈ codeRange 0x10a263 bytes_l10a220_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xa263 24 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10a220 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10a220 (subR64Imm8Effect 0x10a220 4 0x1) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 54) (.exec 0x10a220 (fun s => s.RIP = 0x10a220) (subR64Imm8Effect 0x10a220 4 0x1) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10a224 (movR64R64Effect 0x10a224 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 56) (.exec 0x10a224 (fun s => s.RIP = 0x10a224) (movR64R64Effect 0x10a224 0 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 57) (.out 0x10a227 (movR64M64Effect 0x10a227 7 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[6]
    (.letOp (n := 58) (.exec 0x10a227 (LoadPre 0x10a227 (fun s => AddrMode.addr (.base 6 .none) s (0x10a227 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x10a227 7 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 59) (.out 0x10a22a (movR64M64Effect 0x10a22a 8 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 6] []) (.reg (.gpr 8))) #v[6]
    (.letOp (n := 60) (.exec 0x10a22a (LoadPre 0x10a22a (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x10a22a + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a22a 8 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 61) (.out 0x10a22e (movR64M64Effect 0x10a22e 9 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 6] []) (.reg (.gpr 9))) #v[6]
    (.letOp (n := 62) (.exec 0x10a22e (LoadPre 0x10a22e (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x10a22e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a22e 9 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 63) (.out 0x10a232 (movR64M64Effect 0x10a232 6 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[6]
    (.letOp (n := 64) (.exec 0x10a232 (LoadPre 0x10a232 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x10a232 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a232 6 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 65) (.exec 0x10a236 (StorePre 0x10a236 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10a236 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a236 3 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1, 53]
    (.letOp (n := 66) (.exec 0x10a239 (fun s => s.RIP = 0x10a239) (movR64R64Effect 0x10a239 1 4) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 67) (.out 0x10a23c (movzxR32M8Effect 0x10a23c 4 1 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 68) (.exec 0x10a23c (LoadPre 0x10a23c (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10a23c + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a23c 4 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 69) (.out 0x10a240 (movR64M64Effect 0x10a240 10 (.base 2 .none)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[2]
    (.letOp (n := 70) (.exec 0x10a240 (LoadPre 0x10a240 (fun s => AddrMode.addr (.base 2 .none) s (0x10a240 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x10a240 10 (.base 2 .none)) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 71) (.out 0x10a243 (movR64M64Effect 0x10a243 11 (.base 2 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[2]
    (.letOp (n := 72) (.exec 0x10a243 (LoadPre 0x10a243 (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x10a243 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a243 11 (.base 2 (.d8 0x8))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 73) (.out 0x10a247 (testR8R8Effect 0x10a247 2 1 1) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 1] []) (.flag .ZF)) #v[67, 67]
    (.letOp (n := 74) (.exec 0x10a247 (fun s => s.RIP = 0x10a247) (testR8R8Effect 0x10a247 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[67, 67]
    (.letOp (n := 75) (.out 0x10a249 (atFlags (condHolds 5) (cmovR64R64Effect 0x10a249 4 7 10)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 7))) #v[57, 69, 73]
    (.letOp (n := 76) (.exec 0x10a249 (fun s => s.RIP = 0x10a249) (atFlags (condHolds 5) (cmovR64R64Effect 0x10a249 4 7 10)) (Reg.operands [.gpr 7, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[57, 69, 73]
    (.letOp (n := 77) (.out 0x10a24d (testR8R8Effect 0x10a24d 2 1 1) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 1] []) (.flag .ZF)) #v[67, 67]
    (.letOp (n := 78) (.exec 0x10a24d (fun s => s.RIP = 0x10a24d) (testR8R8Effect 0x10a24d 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[67, 67]
    (.letOp (n := 79) (.out 0x10a24f (atFlags (condHolds 5) (cmovR64R64Effect 0x10a24f 4 8 11)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 8))) #v[59, 71, 77]
    (.letOp (n := 80) (.exec 0x10a24f (fun s => s.RIP = 0x10a24f) (atFlags (condHolds 5) (cmovR64R64Effect 0x10a24f 4 8 11)) (Reg.operands [.gpr 8, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[59, 71, 77]
    (.letOp (n := 81) (.out 0x10a253 (movR64M64Effect 0x10a253 10 (.base 2 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[2]
    (.letOp (n := 82) (.exec 0x10a253 (LoadPre 0x10a253 (fun s => AddrMode.addr (.base 2 (.d8 0x10)) s (0x10a253 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a253 10 (.base 2 (.d8 0x10))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 83) (.out 0x10a257 (testR8R8Effect 0x10a257 2 1 1) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 1] []) (.flag .ZF)) #v[67, 67]
    (.letOp (n := 84) (.exec 0x10a257 (fun s => s.RIP = 0x10a257) (testR8R8Effect 0x10a257 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[67, 67]
    (.letOp (n := 85) (.out 0x10a259 (atFlags (condHolds 5) (cmovR64R64Effect 0x10a259 4 9 10)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 9))) #v[61, 81, 83]
    (.letOp (n := 86) (.exec 0x10a259 (fun s => s.RIP = 0x10a259) (atFlags (condHolds 5) (cmovR64R64Effect 0x10a259 4 9 10)) (Reg.operands [.gpr 9, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[61, 81, 83]
    (.letOp (n := 87) (.out 0x10a25d (movR64M64Effect 0x10a25d 2 (.base 2 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[2]
    (.letOp (n := 88) (.exec 0x10a25d (LoadPre 0x10a25d (fun s => AddrMode.addr (.base 2 (.d8 0x18)) s (0x10a25d + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a25d 2 (.base 2 (.d8 0x18))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 89) (.out 0x10a261 (testR8R8Effect 0x10a261 2 1 1) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 1] []) (.flag .ZF)) #v[67, 67]
    (.letOp (n := 90) (.exec 0x10a261 (fun s => s.RIP = 0x10a261) (testR8R8Effect 0x10a261 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[67, 67]
    (b_l10a220_1))))))))))))))))))))))))))))))))))))))

def bytes_l10a220 : List UInt8 :=
  [0x48, 0x83, 0xEC, 0x01, 0x48, 0x89, 0xF8, 0x48, 0x8B, 0x3E, 0x4C, 0x8B, 0x46, 0x08, 0x4C, 0x8B,
    0x4E, 0x10, 0x48, 0x8B, 0x76, 0x18, 0x88, 0x0C, 0x24, 0x48, 0x89, 0xE1, 0x0F, 0xB6, 0x0C, 0x24,
    0x4C, 0x8B, 0x12, 0x4C, 0x8B, 0x5A, 0x08, 0x84, 0xC9, 0x49, 0x0F, 0x45, 0xFA, 0x84, 0xC9, 0x4D,
    0x0F, 0x45, 0xC3, 0x4C, 0x8B, 0x52, 0x10, 0x84, 0xC9, 0x4D, 0x0F, 0x45, 0xCA, 0x48, 0x8B, 0x52,
    0x18, 0x84, 0xC9] ++ bytes_l10a220_1

theorem code_l10a220 : ∀ x ∈ codeRange 0x10a220 bytes_l10a220, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa220 67 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a220_1

@[cfg_block] def b_l10a280 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10a280 (pushR64Effect 0x10a280 1 0) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 0] []) (.reg (.gpr 4))) #v[4, 0]
    (.letOp (n := 54) (.exec 0x10a280 (PushPre 0x10a280 1) (pushR64Effect 0x10a280 1 0) (Reg.operands [.gpr 4, .gpr 0] [])) #v[4, 0]
    (.letOp (n := 55) (.out 0x10a281 (movR64R64Effect 0x10a281 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6] []) (.reg (.gpr 2))) #v[6]
    (.letOp (n := 56) (.exec 0x10a281 (fun s => s.RIP = 0x10a281) (movR64R64Effect 0x10a281 2 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 57) (.out 0x10a284 (movR32Imm32Effect 0x10a284 5 6 0x4) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 58) (.exec 0x10a284 (fun s => s.RIP = 0x10a284) (movR32Imm32Effect 0x10a284 5 6 0x4) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x10a289 (movR32Imm32Effect 0x10a289 5 1 0x4) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 60) (.exec 0x10a289 (fun s => s.RIP = 0x10a289) (movR32Imm32Effect 0x10a289 5 1 0x4) (Reg.operands [] [])) #v[]
    (.letOp (n := 61) (.out 0x10a28e (callEffect (fun _ => 0x127f50) 0x10a293) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[53]
    (.letOp (n := 62) (.exec 0x10a28e (PushPre 0x10a28e 5) (callEffect (fun _ => 0x127f50) 0x10a293) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 63) (.const ⟨64, 0x10a293⟩) #v[]
    (.terminate (.call ⟨.l127f50, RegMap.args [(0, 0), (1, 59), (2, 55), (3, 3), (4, 61), (5, 5), (6, 57), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ { target := .l10a293, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l10a280 : List UInt8 :=
  [0x50, 0x48, 0x89, 0xF2, 0xBE, 0x04, 0x00, 0x00, 0x00, 0xB9, 0x04, 0x00, 0x00, 0x00, 0xE8, 0xBD,
    0xDC, 0x01, 0x00]

theorem code_l10a280 : ∀ x ∈ codeRange 0x10a280 bytes_l10a280, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xa280 19 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10a293 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10a293 (andAlImm8Effect 0x10a293 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 54) (.exec 0x10a293 (fun s => s.RIP = 0x10a293) (andAlImm8Effect 0x10a293 0x1) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x10a295 (movzxR32R8Effect 0x10a295 3 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 56) (.exec 0x10a295 (fun s => s.RIP = 0x10a295) (movzxR32R8Effect 0x10a295 3 7 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x10a298 (popR64Effect 0x10a298 1 0) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x10a298 (PopPre 0x10a298) (popR64Effect 0x10a298 1 0) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.br ⟨.l127d50, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l10a293 : List UInt8 :=
  [0x24, 0x01, 0x0F, 0xB6, 0xF8, 0x58, 0xE9, 0xB2, 0xDA, 0x01, 0x00]

theorem code_l10a293 : ∀ x ∈ codeRange 0x10a293 bytes_l10a293, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xa293 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10a2a0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10a2a0 (pushR64Effect 0x10a2a0 1 0) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 0] []) (.reg (.gpr 4))) #v[4, 0]
    (.letOp (n := 54) (.exec 0x10a2a0 (PushPre 0x10a2a0 1) (pushR64Effect 0x10a2a0 1 0) (Reg.operands [.gpr 4, .gpr 0] [])) #v[4, 0]
    (.letOp (n := 55) (.out 0x10a2a1 (movR64R64Effect 0x10a2a1 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6] []) (.reg (.gpr 2))) #v[6]
    (.letOp (n := 56) (.exec 0x10a2a1 (fun s => s.RIP = 0x10a2a1) (movR64R64Effect 0x10a2a1 2 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 57) (.out 0x10a2a4 (movR32Imm32Effect 0x10a2a4 5 6 0x4) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 58) (.exec 0x10a2a4 (fun s => s.RIP = 0x10a2a4) (movR32Imm32Effect 0x10a2a4 5 6 0x4) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x10a2a9 (movR32Imm32Effect 0x10a2a9 5 1 0x4) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 60) (.exec 0x10a2a9 (fun s => s.RIP = 0x10a2a9) (movR32Imm32Effect 0x10a2a9 5 1 0x4) (Reg.operands [] [])) #v[]
    (.letOp (n := 61) (.out 0x10a2ae (callEffect (fun _ => 0x127f50) 0x10a2b3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[53]
    (.letOp (n := 62) (.exec 0x10a2ae (PushPre 0x10a2ae 5) (callEffect (fun _ => 0x127f50) 0x10a2b3) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 63) (.const ⟨64, 0x10a2b3⟩) #v[]
    (.terminate (.call ⟨.l127f50, RegMap.args [(0, 0), (1, 59), (2, 55), (3, 3), (4, 61), (5, 5), (6, 57), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ { target := .l10a2b3, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l10a2a0 : List UInt8 :=
  [0x50, 0x48, 0x89, 0xF2, 0xBE, 0x04, 0x00, 0x00, 0x00, 0xB9, 0x04, 0x00, 0x00, 0x00, 0xE8, 0x9D,
    0xDC, 0x01, 0x00]

theorem code_l10a2a0 : ∀ x ∈ codeRange 0x10a2a0 bytes_l10a2a0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xa2a0 19 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10a2b3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10a2b3 (andAlImm8Effect 0x10a2b3 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 54) (.exec 0x10a2b3 (fun s => s.RIP = 0x10a2b3) (andAlImm8Effect 0x10a2b3 0x1) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x10a2b5 (movzxR32R8Effect 0x10a2b5 3 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 56) (.exec 0x10a2b5 (fun s => s.RIP = 0x10a2b5) (movzxR32R8Effect 0x10a2b5 3 7 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x10a2b8 (callEffect (fun _ => 0x127d50) 0x10a2bd) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x10a2b8 (PushPre 0x10a2b8 5) (callEffect (fun _ => 0x127d50) 0x10a2bd) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x10a2bd⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ { target := .l10a2bd, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l10a2b3 : List UInt8 :=
  [0x24, 0x01, 0x0F, 0xB6, 0xF8, 0xE8, 0x93, 0xDA, 0x01, 0x00]

theorem code_l10a2b3 : ∀ x ∈ codeRange 0x10a2b3 bytes_l10a2b3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xa2b3 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10a2bd : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10a2bd (testR8R8Effect 0x10a2bd 2 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[0, 0]
    (.letOp (n := 54) (.exec 0x10a2bd (fun s => s.RIP = 0x10a2bd) (testR8R8Effect 0x10a2bd 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.letOp (n := 55) (.out 0x10a2bf (atFlags (condHolds 5) (setccR8Effect 0x10a2bf 3 0)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 0))) #v[0, 53]
    (.letOp (n := 56) (.exec 0x10a2bf (fun s => s.RIP = 0x10a2bf) (atFlags (condHolds 5) (setccR8Effect 0x10a2bf 3 0)) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[0, 53]
    (.letOp (n := 57) (.out 0x10a2c2 (popR64Effect 0x10a2c2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 58) (.out 0x10a2c2 (popR64Effect 0x10a2c2 1 1) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 59) (.exec 0x10a2c2 (PopPre 0x10a2c2) (popR64Effect 0x10a2c2 1 1) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.out 0x10a2c3 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[58]
    (.letOp (n := 61) (.out 0x10a2c3 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[58]
    (.letOp (n := 62) (.exec 0x10a2c3 (RetPre 0x10a2c3) (retEffect) (Reg.operands [.gpr 4] [])) #v[58]
    (.terminate (.ret (RegMap.args [(0, 55), (1, 57), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 63) (some ⟨60, by decide⟩))))))))))))

def bytes_l10a2bd : List UInt8 :=
  [0x84, 0xC0, 0x0F, 0x95, 0xC0, 0x59, 0xC3]

theorem code_l10a2bd : ∀ x ∈ codeRange 0x10a2bd bytes_l10a2bd, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xa2bd 7 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10a2d0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10a2d0 (movR64Imm32Effect 0x10a2d0 2 0x2021a0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 54) (.exec 0x10a2d0 (fun s => s.RIP = 0x10a2d0) (movR64Imm32Effect 0x10a2d0 2 0x2021a0) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l110b80, RegMap.args [(2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l10a2d0 : List UInt8 :=
  [0x48, 0xC7, 0xC2, 0xA0, 0x21, 0x20, 0x00, 0xE9, 0xA4, 0x68, 0x00, 0x00]

theorem code_l10a2d0 : ∀ x ∈ codeRange 0x10a2d0 bytes_l10a2d0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xa2d0 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10a2e0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10a2e0 (movR64Imm32Effect 0x10a2e0 1 0x2021a0) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 54) (.exec 0x10a2e0 (fun s => s.RIP = 0x10a2e0) (movR64Imm32Effect 0x10a2e0 1 0x2021a0) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l1109b0, RegMap.args [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l10a2e0 : List UInt8 :=
  [0x48, 0xC7, 0xC1, 0xA0, 0x21, 0x20, 0x00, 0xE9, 0xC4, 0x66, 0x00, 0x00]

theorem code_l10a2e0 : ∀ x ∈ codeRange 0x10a2e0 bytes_l10a2e0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xa2e0 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10a2f0_4 : Block Op Label signature Reg.count 186 :=
  .letOp (n := 186) (.exec 0x10a3ec (StorePre 0x10a3ec 3 (fun s => AddrMode.addr (.base 7 (.d8 0x1b)) s (0x10a3ec + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a3ec 3 2 (.base 7 (.d8 0x1b))) (Reg.operands [.gpr 2, .gpr 7] [])) #v[184, 7]
    (.letOp (n := 187) (.out 0x10a3ef (movR32R32Effect 0x10a3ef 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[165]
    (.letOp (n := 188) (.exec 0x10a3ef (fun s => s.RIP = 0x10a3ef) (movR32R32Effect 0x10a3ef 2 2 1) (Reg.operands [.gpr 1] [])) #v[165]
    (.letOp (n := 189) (.out 0x10a3f1 (shrR32Effect 0x10a3f1 3 2 24) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[187]
    (.letOp (n := 190) (.exec 0x10a3f1 (fun s => s.RIP = 0x10a3f1) (shrR32Effect 0x10a3f1 3 2 24) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[187]
    (.letOp (n := 191) (.exec 0x10a3f4 (StorePre 0x10a3f4 3 (fun s => AddrMode.addr (.base 7 (.d8 0x1c)) s (0x10a3f4 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a3f4 3 2 (.base 7 (.d8 0x1c))) (Reg.operands [.gpr 2, .gpr 7] [])) #v[189, 7]
    (.letOp (n := 192) (.out 0x10a3f7 (movR32R32Effect 0x10a3f7 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[165]
    (.letOp (n := 193) (.exec 0x10a3f7 (fun s => s.RIP = 0x10a3f7) (movR32R32Effect 0x10a3f7 2 2 1) (Reg.operands [.gpr 1] [])) #v[165]
    (.letOp (n := 194) (.out 0x10a3f9 (shrR32Effect 0x10a3f9 3 2 16) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[192]
    (.letOp (n := 195) (.exec 0x10a3f9 (fun s => s.RIP = 0x10a3f9) (shrR32Effect 0x10a3f9 3 2 16) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[192]
    (.letOp (n := 196) (.exec 0x10a3fc (StorePre 0x10a3fc 3 (fun s => AddrMode.addr (.base 7 (.d8 0x1d)) s (0x10a3fc + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a3fc 3 2 (.base 7 (.d8 0x1d))) (Reg.operands [.gpr 2, .gpr 7] [])) #v[194, 7]
    (.letOp (n := 197) (.exec 0x10a3ff (StorePre 0x10a3ff 3 (fun s => AddrMode.addr (.base 7 (.d8 0x1e)) s (0x10a3ff + BitVec.ofNat 64 3)) 1) (movM8R8NoRexEffect 0x10a3ff 3 5 (.base 7 (.d8 0x1e))) (Reg.operands [.gpr 1, .gpr 7] [])) #v[165, 7]
    (.letOp (n := 198) (.exec 0x10a402 (StorePre 0x10a402 3 (fun s => AddrMode.addr (.base 7 (.d8 0x1f)) s (0x10a402 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a402 3 1 (.base 7 (.d8 0x1f))) (Reg.operands [.gpr 1, .gpr 7] [])) #v[165, 7]
    (.letOp (n := 199) (.out 0x10a405 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[4]
    (.letOp (n := 200) (.out 0x10a405 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 201) (.exec 0x10a405 (RetPre 0x10a405) (retEffect) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.ret (RegMap.args [(0, 53), (1, 165), (2, 194), (3, 3), (4, 200), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 202) (some ⟨199, by decide⟩))))))))))))))))))

def bytes_l10a2f0_4 : List UInt8 :=
  [0x88, 0x57, 0x1B, 0x89, 0xCA, 0xC1, 0xEA, 0x18, 0x88, 0x57, 0x1C, 0x89, 0xCA, 0xC1, 0xEA, 0x10,
    0x88, 0x57, 0x1D, 0x88, 0x6F, 0x1E, 0x88, 0x4F, 0x1F, 0xC3]

theorem code_l10a2f0_4 : ∀ x ∈ codeRange 0x10a3ec bytes_l10a2f0_4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xa3ec 26 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10a2f0_3 : Block Op Label signature Reg.count 153 :=
  .letOp (n := 153) (.out 0x10a3ac (shrR32Effect 0x10a3ac 3 2 24) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[151]
    (.letOp (n := 154) (.exec 0x10a3ac (fun s => s.RIP = 0x10a3ac) (shrR32Effect 0x10a3ac 3 2 24) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[151]
    (.letOp (n := 155) (.exec 0x10a3af (StorePre 0x10a3af 3 (fun s => AddrMode.addr (.base 7 (.d8 0x14)) s (0x10a3af + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a3af 3 2 (.base 7 (.d8 0x14))) (Reg.operands [.gpr 2, .gpr 7] [])) #v[153, 7]
    (.letOp (n := 156) (.out 0x10a3b2 (movR32R32Effect 0x10a3b2 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[129]
    (.letOp (n := 157) (.exec 0x10a3b2 (fun s => s.RIP = 0x10a3b2) (movR32R32Effect 0x10a3b2 2 2 1) (Reg.operands [.gpr 1] [])) #v[129]
    (.letOp (n := 158) (.out 0x10a3b4 (shrR32Effect 0x10a3b4 3 2 16) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[156]
    (.letOp (n := 159) (.exec 0x10a3b4 (fun s => s.RIP = 0x10a3b4) (shrR32Effect 0x10a3b4 3 2 16) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[156]
    (.letOp (n := 160) (.exec 0x10a3b7 (StorePre 0x10a3b7 3 (fun s => AddrMode.addr (.base 7 (.d8 0x15)) s (0x10a3b7 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a3b7 3 2 (.base 7 (.d8 0x15))) (Reg.operands [.gpr 2, .gpr 7] [])) #v[158, 7]
    (.letOp (n := 161) (.exec 0x10a3ba (StorePre 0x10a3ba 3 (fun s => AddrMode.addr (.base 7 (.d8 0x16)) s (0x10a3ba + BitVec.ofNat 64 3)) 1) (movM8R8NoRexEffect 0x10a3ba 3 5 (.base 7 (.d8 0x16))) (Reg.operands [.gpr 1, .gpr 7] [])) #v[129, 7]
    (.letOp (n := 162) (.exec 0x10a3bd (StorePre 0x10a3bd 3 (fun s => AddrMode.addr (.base 7 (.d8 0x17)) s (0x10a3bd + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a3bd 3 1 (.base 7 (.d8 0x17))) (Reg.operands [.gpr 1, .gpr 7] [])) #v[129, 7]
    (.letOp (n := 163) (.out 0x10a3c0 (movR64M64Effect 0x10a3c0 1 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[6]
    (.letOp (n := 164) (.exec 0x10a3c0 (LoadPre 0x10a3c0 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x10a3c0 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a3c0 1 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 165) (.out 0x10a3c4 (bswapR64Effect 0x10a3c4 3 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[163]
    (.letOp (n := 166) (.exec 0x10a3c4 (fun s => s.RIP = 0x10a3c4) (bswapR64Effect 0x10a3c4 3 1) (Reg.operands [.gpr 1] [])) #v[163]
    (.letOp (n := 167) (.out 0x10a3c7 (movR64R64Effect 0x10a3c7 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[165]
    (.letOp (n := 168) (.exec 0x10a3c7 (fun s => s.RIP = 0x10a3c7) (movR64R64Effect 0x10a3c7 2 1) (Reg.operands [.gpr 1] [])) #v[165]
    (.letOp (n := 169) (.out 0x10a3ca (shrR64Effect 0x10a3ca 4 2 56) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[167]
    (.letOp (n := 170) (.exec 0x10a3ca (fun s => s.RIP = 0x10a3ca) (shrR64Effect 0x10a3ca 4 2 56) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[167]
    (.letOp (n := 171) (.exec 0x10a3ce (StorePre 0x10a3ce 3 (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x10a3ce + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a3ce 3 2 (.base 7 (.d8 0x18))) (Reg.operands [.gpr 2, .gpr 7] [])) #v[169, 7]
    (.letOp (n := 172) (.out 0x10a3d1 (movR64R64Effect 0x10a3d1 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[165]
    (.letOp (n := 173) (.exec 0x10a3d1 (fun s => s.RIP = 0x10a3d1) (movR64R64Effect 0x10a3d1 2 1) (Reg.operands [.gpr 1] [])) #v[165]
    (.letOp (n := 174) (.out 0x10a3d4 (shrR64Effect 0x10a3d4 4 2 48) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[172]
    (.letOp (n := 175) (.exec 0x10a3d4 (fun s => s.RIP = 0x10a3d4) (shrR64Effect 0x10a3d4 4 2 48) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[172]
    (.letOp (n := 176) (.exec 0x10a3d8 (StorePre 0x10a3d8 3 (fun s => AddrMode.addr (.base 7 (.d8 0x19)) s (0x10a3d8 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a3d8 3 2 (.base 7 (.d8 0x19))) (Reg.operands [.gpr 2, .gpr 7] [])) #v[174, 7]
    (.letOp (n := 177) (.out 0x10a3db (movR64R64Effect 0x10a3db 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[165]
    (.letOp (n := 178) (.exec 0x10a3db (fun s => s.RIP = 0x10a3db) (movR64R64Effect 0x10a3db 2 1) (Reg.operands [.gpr 1] [])) #v[165]
    (.letOp (n := 179) (.out 0x10a3de (shrR64Effect 0x10a3de 4 2 40) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[177]
    (.letOp (n := 180) (.exec 0x10a3de (fun s => s.RIP = 0x10a3de) (shrR64Effect 0x10a3de 4 2 40) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[177]
    (.letOp (n := 181) (.exec 0x10a3e2 (StorePre 0x10a3e2 3 (fun s => AddrMode.addr (.base 7 (.d8 0x1a)) s (0x10a3e2 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a3e2 3 2 (.base 7 (.d8 0x1a))) (Reg.operands [.gpr 2, .gpr 7] [])) #v[179, 7]
    (.letOp (n := 182) (.out 0x10a3e5 (movR64R64Effect 0x10a3e5 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[165]
    (.letOp (n := 183) (.exec 0x10a3e5 (fun s => s.RIP = 0x10a3e5) (movR64R64Effect 0x10a3e5 2 1) (Reg.operands [.gpr 1] [])) #v[165]
    (.letOp (n := 184) (.out 0x10a3e8 (shrR64Effect 0x10a3e8 4 2 32) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[182]
    (.letOp (n := 185) (.exec 0x10a3e8 (fun s => s.RIP = 0x10a3e8) (shrR64Effect 0x10a3e8 4 2 32) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[182]
    (b_l10a2f0_4)))))))))))))))))))))))))))))))))

def bytes_l10a2f0_3 : List UInt8 :=
  [0xC1, 0xEA, 0x18, 0x88, 0x57, 0x14, 0x89, 0xCA, 0xC1, 0xEA, 0x10, 0x88, 0x57, 0x15, 0x88, 0x6F,
    0x16, 0x88, 0x4F, 0x17, 0x48, 0x8B, 0x4E, 0x18, 0x48, 0x0F, 0xC9, 0x48, 0x89, 0xCA, 0x48, 0xC1,
    0xEA, 0x38, 0x88, 0x57, 0x18, 0x48, 0x89, 0xCA, 0x48, 0xC1, 0xEA, 0x30, 0x88, 0x57, 0x19, 0x48,
    0x89, 0xCA, 0x48, 0xC1, 0xEA, 0x28, 0x88, 0x57, 0x1A, 0x48, 0x89, 0xCA, 0x48, 0xC1, 0xEA, 0x20] ++ bytes_l10a2f0_4

theorem code_l10a2f0_3 : ∀ x ∈ codeRange 0x10a3ac bytes_l10a2f0_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa3ac 64 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a2f0_4

@[cfg_block] def b_l10a2f0_2 : Block Op Label signature Reg.count 120 :=
  .letOp (n := 120) (.out 0x10a36d (movR32R32Effect 0x10a36d 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[91]
    (.letOp (n := 121) (.exec 0x10a36d (fun s => s.RIP = 0x10a36d) (movR32R32Effect 0x10a36d 2 1 2) (Reg.operands [.gpr 2] [])) #v[91]
    (.letOp (n := 122) (.out 0x10a36f (shrR32Effect 0x10a36f 3 1 16) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[120]
    (.letOp (n := 123) (.exec 0x10a36f (fun s => s.RIP = 0x10a36f) (shrR32Effect 0x10a36f 3 1 16) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[120]
    (.letOp (n := 124) (.exec 0x10a372 (StorePre 0x10a372 3 (fun s => AddrMode.addr (.base 7 (.d8 0xd)) s (0x10a372 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a372 3 1 (.base 7 (.d8 0xd))) (Reg.operands [.gpr 1, .gpr 7] [])) #v[122, 7]
    (.letOp (n := 125) (.exec 0x10a375 (StorePre 0x10a375 3 (fun s => AddrMode.addr (.base 7 (.d8 0xe)) s (0x10a375 + BitVec.ofNat 64 3)) 1) (movM8R8NoRexEffect 0x10a375 3 6 (.base 7 (.d8 0xe))) (Reg.operands [.gpr 2, .gpr 7] [])) #v[91, 7]
    (.letOp (n := 126) (.exec 0x10a378 (StorePre 0x10a378 3 (fun s => AddrMode.addr (.base 7 (.d8 0xf)) s (0x10a378 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a378 3 2 (.base 7 (.d8 0xf))) (Reg.operands [.gpr 2, .gpr 7] [])) #v[91, 7]
    (.letOp (n := 127) (.out 0x10a37b (movR64M64Effect 0x10a37b 1 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[6]
    (.letOp (n := 128) (.exec 0x10a37b (LoadPre 0x10a37b (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x10a37b + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a37b 1 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 129) (.out 0x10a37f (bswapR64Effect 0x10a37f 3 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[127]
    (.letOp (n := 130) (.exec 0x10a37f (fun s => s.RIP = 0x10a37f) (bswapR64Effect 0x10a37f 3 1) (Reg.operands [.gpr 1] [])) #v[127]
    (.letOp (n := 131) (.out 0x10a382 (movR64R64Effect 0x10a382 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[129]
    (.letOp (n := 132) (.exec 0x10a382 (fun s => s.RIP = 0x10a382) (movR64R64Effect 0x10a382 2 1) (Reg.operands [.gpr 1] [])) #v[129]
    (.letOp (n := 133) (.out 0x10a385 (shrR64Effect 0x10a385 4 2 56) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[131]
    (.letOp (n := 134) (.exec 0x10a385 (fun s => s.RIP = 0x10a385) (shrR64Effect 0x10a385 4 2 56) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[131]
    (.letOp (n := 135) (.exec 0x10a389 (StorePre 0x10a389 3 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x10a389 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a389 3 2 (.base 7 (.d8 0x10))) (Reg.operands [.gpr 2, .gpr 7] [])) #v[133, 7]
    (.letOp (n := 136) (.out 0x10a38c (movR64R64Effect 0x10a38c 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[129]
    (.letOp (n := 137) (.exec 0x10a38c (fun s => s.RIP = 0x10a38c) (movR64R64Effect 0x10a38c 2 1) (Reg.operands [.gpr 1] [])) #v[129]
    (.letOp (n := 138) (.out 0x10a38f (shrR64Effect 0x10a38f 4 2 48) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[136]
    (.letOp (n := 139) (.exec 0x10a38f (fun s => s.RIP = 0x10a38f) (shrR64Effect 0x10a38f 4 2 48) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[136]
    (.letOp (n := 140) (.exec 0x10a393 (StorePre 0x10a393 3 (fun s => AddrMode.addr (.base 7 (.d8 0x11)) s (0x10a393 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a393 3 2 (.base 7 (.d8 0x11))) (Reg.operands [.gpr 2, .gpr 7] [])) #v[138, 7]
    (.letOp (n := 141) (.out 0x10a396 (movR64R64Effect 0x10a396 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[129]
    (.letOp (n := 142) (.exec 0x10a396 (fun s => s.RIP = 0x10a396) (movR64R64Effect 0x10a396 2 1) (Reg.operands [.gpr 1] [])) #v[129]
    (.letOp (n := 143) (.out 0x10a399 (shrR64Effect 0x10a399 4 2 40) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[141]
    (.letOp (n := 144) (.exec 0x10a399 (fun s => s.RIP = 0x10a399) (shrR64Effect 0x10a399 4 2 40) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[141]
    (.letOp (n := 145) (.exec 0x10a39d (StorePre 0x10a39d 3 (fun s => AddrMode.addr (.base 7 (.d8 0x12)) s (0x10a39d + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a39d 3 2 (.base 7 (.d8 0x12))) (Reg.operands [.gpr 2, .gpr 7] [])) #v[143, 7]
    (.letOp (n := 146) (.out 0x10a3a0 (movR64R64Effect 0x10a3a0 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[129]
    (.letOp (n := 147) (.exec 0x10a3a0 (fun s => s.RIP = 0x10a3a0) (movR64R64Effect 0x10a3a0 2 1) (Reg.operands [.gpr 1] [])) #v[129]
    (.letOp (n := 148) (.out 0x10a3a3 (shrR64Effect 0x10a3a3 4 2 32) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[146]
    (.letOp (n := 149) (.exec 0x10a3a3 (fun s => s.RIP = 0x10a3a3) (shrR64Effect 0x10a3a3 4 2 32) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[146]
    (.letOp (n := 150) (.exec 0x10a3a7 (StorePre 0x10a3a7 3 (fun s => AddrMode.addr (.base 7 (.d8 0x13)) s (0x10a3a7 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a3a7 3 2 (.base 7 (.d8 0x13))) (Reg.operands [.gpr 2, .gpr 7] [])) #v[148, 7]
    (.letOp (n := 151) (.out 0x10a3aa (movR32R32Effect 0x10a3aa 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[129]
    (.letOp (n := 152) (.exec 0x10a3aa (fun s => s.RIP = 0x10a3aa) (movR32R32Effect 0x10a3aa 2 2 1) (Reg.operands [.gpr 1] [])) #v[129]
    (b_l10a2f0_3)))))))))))))))))))))))))))))))))

def bytes_l10a2f0_2 : List UInt8 :=
  [0x89, 0xD1, 0xC1, 0xE9, 0x10, 0x88, 0x4F, 0x0D, 0x88, 0x77, 0x0E, 0x88, 0x57, 0x0F, 0x48, 0x8B,
    0x4E, 0x10, 0x48, 0x0F, 0xC9, 0x48, 0x89, 0xCA, 0x48, 0xC1, 0xEA, 0x38, 0x88, 0x57, 0x10, 0x48,
    0x89, 0xCA, 0x48, 0xC1, 0xEA, 0x30, 0x88, 0x57, 0x11, 0x48, 0x89, 0xCA, 0x48, 0xC1, 0xEA, 0x28,
    0x88, 0x57, 0x12, 0x48, 0x89, 0xCA, 0x48, 0xC1, 0xEA, 0x20, 0x88, 0x57, 0x13, 0x89, 0xCA] ++ bytes_l10a2f0_3

theorem code_l10a2f0_2 : ∀ x ∈ codeRange 0x10a36d bytes_l10a2f0_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa36d 63 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a2f0_3

@[cfg_block] def b_l10a2f0_1 : Block Op Label signature Reg.count 88 :=
  .letOp (n := 88) (.exec 0x10a32d (StorePre 0x10a32d 3 (fun s => AddrMode.addr (.base 7 (.d8 0x5)) s (0x10a32d + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a32d 3 2 (.base 7 (.d8 0x5))) (Reg.operands [.gpr 2, .gpr 7] [])) #v[86, 7]
    (.letOp (n := 89) (.out 0x10a330 (movR64M64Effect 0x10a330 2 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6] []) (.reg (.gpr 2))) #v[6]
    (.letOp (n := 90) (.exec 0x10a330 (LoadPre 0x10a330 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x10a330 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a330 2 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 91) (.out 0x10a334 (bswapR64Effect 0x10a334 3 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[89]
    (.letOp (n := 92) (.exec 0x10a334 (fun s => s.RIP = 0x10a334) (bswapR64Effect 0x10a334 3 2) (Reg.operands [.gpr 2] [])) #v[89]
    (.letOp (n := 93) (.exec 0x10a337 (StorePre 0x10a337 3 (fun s => AddrMode.addr (.base 7 (.d8 0x6)) s (0x10a337 + BitVec.ofNat 64 3)) 1) (movM8R8NoRexEffect 0x10a337 3 5 (.base 7 (.d8 0x6))) (Reg.operands [.gpr 1, .gpr 7] [])) #v[57, 7]
    (.letOp (n := 94) (.exec 0x10a33a (StorePre 0x10a33a 3 (fun s => AddrMode.addr (.base 7 (.d8 0x7)) s (0x10a33a + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a33a 3 1 (.base 7 (.d8 0x7))) (Reg.operands [.gpr 1, .gpr 7] [])) #v[57, 7]
    (.letOp (n := 95) (.out 0x10a33d (movR64R64Effect 0x10a33d 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[91]
    (.letOp (n := 96) (.exec 0x10a33d (fun s => s.RIP = 0x10a33d) (movR64R64Effect 0x10a33d 1 2) (Reg.operands [.gpr 2] [])) #v[91]
    (.letOp (n := 97) (.out 0x10a340 (shrR64Effect 0x10a340 4 1 56) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[95]
    (.letOp (n := 98) (.exec 0x10a340 (fun s => s.RIP = 0x10a340) (shrR64Effect 0x10a340 4 1 56) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[95]
    (.letOp (n := 99) (.exec 0x10a344 (StorePre 0x10a344 3 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x10a344 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a344 3 1 (.base 7 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 7] [])) #v[97, 7]
    (.letOp (n := 100) (.out 0x10a347 (movR64R64Effect 0x10a347 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[91]
    (.letOp (n := 101) (.exec 0x10a347 (fun s => s.RIP = 0x10a347) (movR64R64Effect 0x10a347 1 2) (Reg.operands [.gpr 2] [])) #v[91]
    (.letOp (n := 102) (.out 0x10a34a (shrR64Effect 0x10a34a 4 1 48) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[100]
    (.letOp (n := 103) (.exec 0x10a34a (fun s => s.RIP = 0x10a34a) (shrR64Effect 0x10a34a 4 1 48) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[100]
    (.letOp (n := 104) (.exec 0x10a34e (StorePre 0x10a34e 3 (fun s => AddrMode.addr (.base 7 (.d8 0x9)) s (0x10a34e + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a34e 3 1 (.base 7 (.d8 0x9))) (Reg.operands [.gpr 1, .gpr 7] [])) #v[102, 7]
    (.letOp (n := 105) (.out 0x10a351 (movR64R64Effect 0x10a351 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[91]
    (.letOp (n := 106) (.exec 0x10a351 (fun s => s.RIP = 0x10a351) (movR64R64Effect 0x10a351 1 2) (Reg.operands [.gpr 2] [])) #v[91]
    (.letOp (n := 107) (.out 0x10a354 (shrR64Effect 0x10a354 4 1 40) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[105]
    (.letOp (n := 108) (.exec 0x10a354 (fun s => s.RIP = 0x10a354) (shrR64Effect 0x10a354 4 1 40) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[105]
    (.letOp (n := 109) (.exec 0x10a358 (StorePre 0x10a358 3 (fun s => AddrMode.addr (.base 7 (.d8 0xa)) s (0x10a358 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a358 3 1 (.base 7 (.d8 0xa))) (Reg.operands [.gpr 1, .gpr 7] [])) #v[107, 7]
    (.letOp (n := 110) (.out 0x10a35b (movR64R64Effect 0x10a35b 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[91]
    (.letOp (n := 111) (.exec 0x10a35b (fun s => s.RIP = 0x10a35b) (movR64R64Effect 0x10a35b 1 2) (Reg.operands [.gpr 2] [])) #v[91]
    (.letOp (n := 112) (.out 0x10a35e (shrR64Effect 0x10a35e 4 1 32) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[110]
    (.letOp (n := 113) (.exec 0x10a35e (fun s => s.RIP = 0x10a35e) (shrR64Effect 0x10a35e 4 1 32) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[110]
    (.letOp (n := 114) (.exec 0x10a362 (StorePre 0x10a362 3 (fun s => AddrMode.addr (.base 7 (.d8 0xb)) s (0x10a362 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a362 3 1 (.base 7 (.d8 0xb))) (Reg.operands [.gpr 1, .gpr 7] [])) #v[112, 7]
    (.letOp (n := 115) (.out 0x10a365 (movR32R32Effect 0x10a365 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[91]
    (.letOp (n := 116) (.exec 0x10a365 (fun s => s.RIP = 0x10a365) (movR32R32Effect 0x10a365 2 1 2) (Reg.operands [.gpr 2] [])) #v[91]
    (.letOp (n := 117) (.out 0x10a367 (shrR32Effect 0x10a367 3 1 24) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[115]
    (.letOp (n := 118) (.exec 0x10a367 (fun s => s.RIP = 0x10a367) (shrR32Effect 0x10a367 3 1 24) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[115]
    (.letOp (n := 119) (.exec 0x10a36a (StorePre 0x10a36a 3 (fun s => AddrMode.addr (.base 7 (.d8 0xc)) s (0x10a36a + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a36a 3 1 (.base 7 (.d8 0xc))) (Reg.operands [.gpr 1, .gpr 7] [])) #v[117, 7]
    (b_l10a2f0_2))))))))))))))))))))))))))))))))

def bytes_l10a2f0_1 : List UInt8 :=
  [0x88, 0x57, 0x05, 0x48, 0x8B, 0x56, 0x08, 0x48, 0x0F, 0xCA, 0x88, 0x6F, 0x06, 0x88, 0x4F, 0x07,
    0x48, 0x89, 0xD1, 0x48, 0xC1, 0xE9, 0x38, 0x88, 0x4F, 0x08, 0x48, 0x89, 0xD1, 0x48, 0xC1, 0xE9,
    0x30, 0x88, 0x4F, 0x09, 0x48, 0x89, 0xD1, 0x48, 0xC1, 0xE9, 0x28, 0x88, 0x4F, 0x0A, 0x48, 0x89,
    0xD1, 0x48, 0xC1, 0xE9, 0x20, 0x88, 0x4F, 0x0B, 0x89, 0xD1, 0xC1, 0xE9, 0x18, 0x88, 0x4F, 0x0C] ++ bytes_l10a2f0_2

theorem code_l10a2f0_1 : ∀ x ∈ codeRange 0x10a32d bytes_l10a2f0_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa32d 64 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a2f0_2

@[cfg_block] def b_l10a2f0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10a2f0 (movR64R64Effect 0x10a2f0 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 54) (.exec 0x10a2f0 (fun s => s.RIP = 0x10a2f0) (movR64R64Effect 0x10a2f0 0 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 55) (.out 0x10a2f3 (movR64M64Effect 0x10a2f3 1 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[6]
    (.letOp (n := 56) (.exec 0x10a2f3 (LoadPre 0x10a2f3 (fun s => AddrMode.addr (.base 6 .none) s (0x10a2f3 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x10a2f3 1 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 57) (.out 0x10a2f6 (bswapR64Effect 0x10a2f6 3 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[55]
    (.letOp (n := 58) (.exec 0x10a2f6 (fun s => s.RIP = 0x10a2f6) (bswapR64Effect 0x10a2f6 3 1) (Reg.operands [.gpr 1] [])) #v[55]
    (.letOp (n := 59) (.out 0x10a2f9 (movR64R64Effect 0x10a2f9 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[57]
    (.letOp (n := 60) (.exec 0x10a2f9 (fun s => s.RIP = 0x10a2f9) (movR64R64Effect 0x10a2f9 2 1) (Reg.operands [.gpr 1] [])) #v[57]
    (.letOp (n := 61) (.out 0x10a2fc (shrR64Effect 0x10a2fc 4 2 56) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[59]
    (.letOp (n := 62) (.exec 0x10a2fc (fun s => s.RIP = 0x10a2fc) (shrR64Effect 0x10a2fc 4 2 56) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[59]
    (.letOp (n := 63) (.exec 0x10a300 (StorePre 0x10a300 2 (fun s => AddrMode.addr (.base 7 .none) s (0x10a300 + BitVec.ofNat 64 2)) 1) (movM8R8Effect 0x10a300 2 2 (.base 7 .none)) (Reg.operands [.gpr 2, .gpr 7] [])) #v[61, 7]
    (.letOp (n := 64) (.out 0x10a302 (movR64R64Effect 0x10a302 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[57]
    (.letOp (n := 65) (.exec 0x10a302 (fun s => s.RIP = 0x10a302) (movR64R64Effect 0x10a302 2 1) (Reg.operands [.gpr 1] [])) #v[57]
    (.letOp (n := 66) (.out 0x10a305 (shrR64Effect 0x10a305 4 2 48) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[64]
    (.letOp (n := 67) (.exec 0x10a305 (fun s => s.RIP = 0x10a305) (shrR64Effect 0x10a305 4 2 48) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[64]
    (.letOp (n := 68) (.exec 0x10a309 (StorePre 0x10a309 3 (fun s => AddrMode.addr (.base 7 (.d8 0x1)) s (0x10a309 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a309 3 2 (.base 7 (.d8 0x1))) (Reg.operands [.gpr 2, .gpr 7] [])) #v[66, 7]
    (.letOp (n := 69) (.out 0x10a30c (movR64R64Effect 0x10a30c 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[57]
    (.letOp (n := 70) (.exec 0x10a30c (fun s => s.RIP = 0x10a30c) (movR64R64Effect 0x10a30c 2 1) (Reg.operands [.gpr 1] [])) #v[57]
    (.letOp (n := 71) (.out 0x10a30f (shrR64Effect 0x10a30f 4 2 40) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[69]
    (.letOp (n := 72) (.exec 0x10a30f (fun s => s.RIP = 0x10a30f) (shrR64Effect 0x10a30f 4 2 40) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[69]
    (.letOp (n := 73) (.exec 0x10a313 (StorePre 0x10a313 3 (fun s => AddrMode.addr (.base 7 (.d8 0x2)) s (0x10a313 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a313 3 2 (.base 7 (.d8 0x2))) (Reg.operands [.gpr 2, .gpr 7] [])) #v[71, 7]
    (.letOp (n := 74) (.out 0x10a316 (movR64R64Effect 0x10a316 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[57]
    (.letOp (n := 75) (.exec 0x10a316 (fun s => s.RIP = 0x10a316) (movR64R64Effect 0x10a316 2 1) (Reg.operands [.gpr 1] [])) #v[57]
    (.letOp (n := 76) (.out 0x10a319 (shrR64Effect 0x10a319 4 2 32) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[74]
    (.letOp (n := 77) (.exec 0x10a319 (fun s => s.RIP = 0x10a319) (shrR64Effect 0x10a319 4 2 32) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[74]
    (.letOp (n := 78) (.exec 0x10a31d (StorePre 0x10a31d 3 (fun s => AddrMode.addr (.base 7 (.d8 0x3)) s (0x10a31d + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a31d 3 2 (.base 7 (.d8 0x3))) (Reg.operands [.gpr 2, .gpr 7] [])) #v[76, 7]
    (.letOp (n := 79) (.out 0x10a320 (movR32R32Effect 0x10a320 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[57]
    (.letOp (n := 80) (.exec 0x10a320 (fun s => s.RIP = 0x10a320) (movR32R32Effect 0x10a320 2 2 1) (Reg.operands [.gpr 1] [])) #v[57]
    (.letOp (n := 81) (.out 0x10a322 (shrR32Effect 0x10a322 3 2 24) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[79]
    (.letOp (n := 82) (.exec 0x10a322 (fun s => s.RIP = 0x10a322) (shrR32Effect 0x10a322 3 2 24) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[79]
    (.letOp (n := 83) (.exec 0x10a325 (StorePre 0x10a325 3 (fun s => AddrMode.addr (.base 7 (.d8 0x4)) s (0x10a325 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a325 3 2 (.base 7 (.d8 0x4))) (Reg.operands [.gpr 2, .gpr 7] [])) #v[81, 7]
    (.letOp (n := 84) (.out 0x10a328 (movR32R32Effect 0x10a328 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[57]
    (.letOp (n := 85) (.exec 0x10a328 (fun s => s.RIP = 0x10a328) (movR32R32Effect 0x10a328 2 2 1) (Reg.operands [.gpr 1] [])) #v[57]
    (.letOp (n := 86) (.out 0x10a32a (shrR32Effect 0x10a32a 3 2 16) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[84]
    (.letOp (n := 87) (.exec 0x10a32a (fun s => s.RIP = 0x10a32a) (shrR32Effect 0x10a32a 3 2 16) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[84]
    (b_l10a2f0_1)))))))))))))))))))))))))))))))))))

def bytes_l10a2f0 : List UInt8 :=
  [0x48, 0x89, 0xF8, 0x48, 0x8B, 0x0E, 0x48, 0x0F, 0xC9, 0x48, 0x89, 0xCA, 0x48, 0xC1, 0xEA, 0x38,
    0x88, 0x17, 0x48, 0x89, 0xCA, 0x48, 0xC1, 0xEA, 0x30, 0x88, 0x57, 0x01, 0x48, 0x89, 0xCA, 0x48,
    0xC1, 0xEA, 0x28, 0x88, 0x57, 0x02, 0x48, 0x89, 0xCA, 0x48, 0xC1, 0xEA, 0x20, 0x88, 0x57, 0x03,
    0x89, 0xCA, 0xC1, 0xEA, 0x18, 0x88, 0x57, 0x04, 0x89, 0xCA, 0xC1, 0xEA, 0x10] ++ bytes_l10a2f0_1

theorem code_l10a2f0 : ∀ x ∈ codeRange 0x10a2f0 bytes_l10a2f0, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa2f0 61 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a2f0_1

end K256.Proofs.Signing.LIR
