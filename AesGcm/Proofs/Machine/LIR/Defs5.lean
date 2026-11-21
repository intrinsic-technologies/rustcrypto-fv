import AesGcm.Proofs.Machine.Instructions.Memory16
import AesGcm.Proofs.Machine.Instructions.HighByteStore
import AesGcm.Proofs.Machine.LIR.Labels
import AesGcm.Proofs.Copied.X86Proofs.CFG.EvalAttr
import AesGcm.Proofs.Copied.X86Proofs.Lift.Generated.Footprints

namespace AesGcm.Proofs.Machine.LIR

open AesGcm.Proofs.Machine.Instructions
open X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift

def b_l107315_15 : Block Op Label signature Reg.count 539 :=
  .letOp (n := 539) (.exec 0x1079c0 (StorePre 0x1079c0 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x3a)) s (0x1079c0 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1079c0 5 9 (.sib 0 (some 5) 0 (.d8 0x3a))) (Reg.operands [.gpr 9, .gpr 0, .gpr 5] [])) #v[353, 375, 5]
    (.letOp (n := 540) (.exec 0x1079c5 (StorePre 0x1079c5 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x3b)) s (0x1079c5 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1079c5 5 8 (.sib 0 (some 5) 0 (.d8 0x3b))) (Reg.operands [.gpr 8, .gpr 0, .gpr 5] [])) #v[357, 375, 5]
    (.letOp (n := 541) (.exec 0x1079ca (StorePre 0x1079ca 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x3c)) s (0x1079ca + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1079ca 5 7 (.sib 0 (some 5) 0 (.d8 0x3c))) (Reg.operands [.gpr 7, .gpr 0, .gpr 5] [])) #v[361, 375, 5]
    (.letOp (n := 542) (.exec 0x1079cf (StorePre 0x1079cf 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x3d)) s (0x1079cf + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1079cf 5 6 (.sib 0 (some 5) 0 (.d8 0x3d))) (Reg.operands [.gpr 6, .gpr 0, .gpr 5] [])) #v[365, 375, 5]
    (.letOp (n := 543) (.exec 0x1079d4 (StorePre 0x1079d4 4 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x3e)) s (0x1079d4 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1079d4 4 2 (.sib 0 (some 5) 0 (.d8 0x3e))) (Reg.operands [.gpr 2, .gpr 0, .gpr 5] [])) #v[369, 375, 5]
    (.letOp (n := 544) (.out 0x1079d8 (movR64R64Effect 0x1079d8 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0] []) (.reg (.gpr 2))) #v[375]
    (.letOp (n := 545) (.exec 0x1079d8 (fun s => s.RIP = 0x1079d8) (movR64R64Effect 0x1079d8 2 0) (Reg.operands [.gpr 0] [])) #v[375]
    (.letOp (n := 546) (.exec 0x1079db (StorePre 0x1079db 4 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x3f)) s (0x1079db + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1079db 4 1 (.sib 0 (some 5) 0 (.d8 0x3f))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[373, 375, 5]
    (.letOp (n := 547) (.out 0x1079df (movR64M64Effect 0x1079df 1 (.sib 4 none 0 (.d32 0xe0))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 548) (.exec 0x1079df (LoadPre 0x1079df (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x1079df + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1079df 1 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 549) (.out 0x1079e7 (incR64Effect 0x1079e7 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[547]
    (.letOp (n := 550) (.exec 0x1079e7 (fun s => s.RIP = 0x1079e7) (incR64Effect 0x1079e7 1) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[547]
    (.letOp (n := 551) (.exec 0x1079ea (StorePre 0x1079ea 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x1079ea + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1079ea 1 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[549, 4]
    (.letOp (n := 552) (.out 0x1079f2 (cmpMREffect 0x1079f2 8 64 1 (.sib 4 none 0 (.d32 0x148))) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 4] []) (.flag .ZF)) #v[549, 4]
    (.letOp (n := 553) (.exec 0x1079f2 (LoadPre 0x1079f2 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x148)) s (0x1079f2 + BitVec.ofNat 64 8)) 8) (cmpMREffect 0x1079f2 8 64 1 (.sib 4 none 0 (.d32 0x148))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[549, 4]
    (.letOp (n := 554) (.out 0x1079fa (movR64M64Effect 0x1079fa 9 (.sib 4 none 0 (.d32 0xf8))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 555) (.exec 0x1079fa (LoadPre 0x1079fa (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x1079fa + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1079fa 9 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 556) (.pure (condOp 4)) #v[552]
    (.terminate (.condBr (Fin.last 556) ⟨.l10805f, RegMap.args [(0, 375), (1, 549), (2, 544), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 554), (10, 349), (11, 345), (12, 329), (13, 530), (14, 337), (15, 333), (19, 552), (22, 22), (39, 39), (50, 50), (51, 51)] 557⟩ ⟨.l107a08, RegMap.args [(0, 375), (1, 549), (2, 544), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 554), (10, 349), (11, 345), (12, 329), (13, 530), (14, 337), (15, 333), (19, 552), (22, 22), (39, 39), (50, 50), (51, 51)] 557⟩)))))))))))))))))))

def bytes_l107315_15 : List UInt8 :=
  [0x44, 0x88, 0x4C, 0x28, 0x3A, 0x44, 0x88, 0x44, 0x28, 0x3B, 0x40, 0x88, 0x7C, 0x28, 0x3C, 0x40,
    0x88, 0x74, 0x28, 0x3D, 0x88, 0x54, 0x28, 0x3E, 0x48, 0x89, 0xC2, 0x88, 0x4C, 0x28, 0x3F, 0x48,
    0x8B, 0x8C, 0x24, 0xE0, 0x00, 0x00, 0x00, 0x48, 0xFF, 0xC1, 0x48, 0x89, 0x8C, 0x24, 0xE0, 0x00,
    0x00, 0x00, 0x48, 0x39, 0x8C, 0x24, 0x48, 0x01, 0x00, 0x00, 0x4C, 0x8B, 0x8C, 0x24, 0xF8, 0x00,
    0x00, 0x00, 0x0F, 0x84, 0x57, 0x06, 0x00, 0x00]

theorem code_l107315_15 : ∀ x ∈ codeRange 0x1079c0 bytes_l107315_15, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x79c0 72 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

def b_l107315_14 : Block Op Label signature Reg.count 512 :=
  .letOp (n := 512) (.out 0x107956 (movzxR32M8Effect 0x107956 6 13 (.sib 4 none 0 (.d8 0x4e))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 513) (.exec 0x107956 (LoadPre 0x107956 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4e)) s (0x107956 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x107956 6 13 (.sib 4 none 0 (.d8 0x4e))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 514) (.exec 0x10795c (StorePre 0x10795c 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x2d)) s (0x10795c + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x10795c 5 13 (.sib 0 (some 5) 0 (.d8 0x2d))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[512, 375, 5]
    (.letOp (n := 515) (.out 0x107961 (movzxR32M8Effect 0x107961 6 13 (.sib 4 none 0 (.d8 0x4d))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 516) (.exec 0x107961 (LoadPre 0x107961 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4d)) s (0x107961 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x107961 6 13 (.sib 4 none 0 (.d8 0x4d))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 517) (.exec 0x107967 (StorePre 0x107967 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x2e)) s (0x107967 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x107967 5 13 (.sib 0 (some 5) 0 (.d8 0x2e))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[515, 375, 5]
    (.letOp (n := 518) (.out 0x10796c (movzxR32M8Effect 0x10796c 6 13 (.sib 4 none 0 (.d8 0x4c))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 519) (.exec 0x10796c (LoadPre 0x10796c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4c)) s (0x10796c + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x10796c 6 13 (.sib 4 none 0 (.d8 0x4c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 520) (.exec 0x107972 (StorePre 0x107972 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x2f)) s (0x107972 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x107972 5 13 (.sib 0 (some 5) 0 (.d8 0x2f))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[518, 375, 5]
    (.letOp (n := 521) (.out 0x107977 (movzxR32M8Effect 0x107977 6 13 (.sib 4 none 0 (.d8 0x4b))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 522) (.exec 0x107977 (LoadPre 0x107977 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4b)) s (0x107977 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x107977 6 13 (.sib 4 none 0 (.d8 0x4b))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 523) (.exec 0x10797d (StorePre 0x10797d 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x30)) s (0x10797d + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x10797d 5 13 (.sib 0 (some 5) 0 (.d8 0x30))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[521, 375, 5]
    (.letOp (n := 524) (.out 0x107982 (movzxR32M8Effect 0x107982 6 13 (.sib 4 none 0 (.d8 0x4a))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 525) (.exec 0x107982 (LoadPre 0x107982 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4a)) s (0x107982 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x107982 6 13 (.sib 4 none 0 (.d8 0x4a))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 526) (.exec 0x107988 (StorePre 0x107988 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x31)) s (0x107988 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x107988 5 13 (.sib 0 (some 5) 0 (.d8 0x31))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[524, 375, 5]
    (.letOp (n := 527) (.out 0x10798d (movzxR32M8Effect 0x10798d 6 13 (.sib 4 none 0 (.d8 0x49))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 528) (.exec 0x10798d (LoadPre 0x10798d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x49)) s (0x10798d + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x10798d 6 13 (.sib 4 none 0 (.d8 0x49))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 529) (.exec 0x107993 (StorePre 0x107993 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x32)) s (0x107993 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x107993 5 13 (.sib 0 (some 5) 0 (.d8 0x32))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[527, 375, 5]
    (.letOp (n := 530) (.out 0x107998 (movzxR32M8Effect 0x107998 6 13 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 531) (.exec 0x107998 (LoadPre 0x107998 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x107998 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x107998 6 13 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 532) (.exec 0x10799e (StorePre 0x10799e 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x33)) s (0x10799e + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x10799e 5 13 (.sib 0 (some 5) 0 (.d8 0x33))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[530, 375, 5]
    (.letOp (n := 533) (.exec 0x1079a3 (StorePre 0x1079a3 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x34)) s (0x1079a3 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1079a3 5 12 (.sib 0 (some 5) 0 (.d8 0x34))) (Reg.operands [.gpr 12, .gpr 0, .gpr 5] [])) #v[329, 375, 5]
    (.letOp (n := 534) (.exec 0x1079a8 (StorePre 0x1079a8 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x35)) s (0x1079a8 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1079a8 5 15 (.sib 0 (some 5) 0 (.d8 0x35))) (Reg.operands [.gpr 15, .gpr 0, .gpr 5] [])) #v[333, 375, 5]
    (.letOp (n := 535) (.exec 0x1079ad (StorePre 0x1079ad 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x36)) s (0x1079ad + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1079ad 5 14 (.sib 0 (some 5) 0 (.d8 0x36))) (Reg.operands [.gpr 14, .gpr 0, .gpr 5] [])) #v[337, 375, 5]
    (.letOp (n := 536) (.exec 0x1079b2 (StorePre 0x1079b2 4 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x37)) s (0x1079b2 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1079b2 4 3 (.sib 0 (some 5) 0 (.d8 0x37))) (Reg.operands [.gpr 3, .gpr 0, .gpr 5] [])) #v[341, 375, 5]
    (.letOp (n := 537) (.exec 0x1079b6 (StorePre 0x1079b6 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x38)) s (0x1079b6 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1079b6 5 11 (.sib 0 (some 5) 0 (.d8 0x38))) (Reg.operands [.gpr 11, .gpr 0, .gpr 5] [])) #v[345, 375, 5]
    (.letOp (n := 538) (.exec 0x1079bb (StorePre 0x1079bb 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x39)) s (0x1079bb + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1079bb 5 10 (.sib 0 (some 5) 0 (.d8 0x39))) (Reg.operands [.gpr 10, .gpr 0, .gpr 5] [])) #v[349, 375, 5]
    (b_l107315_15)))))))))))))))))))))))))))

def bytes_l107315_14 : List UInt8 :=
  [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x4E, 0x44, 0x88, 0x6C, 0x28, 0x2D, 0x44, 0x0F, 0xB6, 0x6C, 0x24,
    0x4D, 0x44, 0x88, 0x6C, 0x28, 0x2E, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x4C, 0x44, 0x88, 0x6C, 0x28,
    0x2F, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x4B, 0x44, 0x88, 0x6C, 0x28, 0x30, 0x44, 0x0F, 0xB6, 0x6C,
    0x24, 0x4A, 0x44, 0x88, 0x6C, 0x28, 0x31, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x49, 0x44, 0x88, 0x6C,
    0x28, 0x32, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x48, 0x44, 0x88, 0x6C, 0x28, 0x33, 0x44, 0x88, 0x64,
    0x28, 0x34, 0x44, 0x88, 0x7C, 0x28, 0x35, 0x44, 0x88, 0x74, 0x28, 0x36, 0x88, 0x5C, 0x28, 0x37,
    0x44, 0x88, 0x5C, 0x28, 0x38, 0x44, 0x88, 0x54, 0x28, 0x39] ++ bytes_l107315_15

theorem code_l107315_14 : ∀ x ∈ codeRange 0x107956 bytes_l107315_14, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x7956 106 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l107315_15

def b_l107315_13 : Block Op Label signature Reg.count 482 :=
  .letOp (n := 482) (.out 0x1078e8 (movzxR32M8Effect 0x1078e8 6 13 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 483) (.exec 0x1078e8 (LoadPre 0x1078e8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1078e8 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1078e8 6 13 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 484) (.exec 0x1078ee (StorePre 0x1078ee 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x23)) s (0x1078ee + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1078ee 5 13 (.sib 0 (some 5) 0 (.d8 0x23))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[482, 375, 5]
    (.letOp (n := 485) (.out 0x1078f3 (movzxR32M8Effect 0x1078f3 6 13 (.sib 4 none 0 (.d8 0x57))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 486) (.exec 0x1078f3 (LoadPre 0x1078f3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x57)) s (0x1078f3 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1078f3 6 13 (.sib 4 none 0 (.d8 0x57))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 487) (.exec 0x1078f9 (StorePre 0x1078f9 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x24)) s (0x1078f9 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1078f9 5 13 (.sib 0 (some 5) 0 (.d8 0x24))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[485, 375, 5]
    (.letOp (n := 488) (.out 0x1078fe (movzxR32M8Effect 0x1078fe 6 13 (.sib 4 none 0 (.d8 0x56))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 489) (.exec 0x1078fe (LoadPre 0x1078fe (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x56)) s (0x1078fe + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1078fe 6 13 (.sib 4 none 0 (.d8 0x56))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 490) (.exec 0x107904 (StorePre 0x107904 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x25)) s (0x107904 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x107904 5 13 (.sib 0 (some 5) 0 (.d8 0x25))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[488, 375, 5]
    (.letOp (n := 491) (.out 0x107909 (movzxR32M8Effect 0x107909 6 13 (.sib 4 none 0 (.d8 0x55))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 492) (.exec 0x107909 (LoadPre 0x107909 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x55)) s (0x107909 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x107909 6 13 (.sib 4 none 0 (.d8 0x55))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 493) (.exec 0x10790f (StorePre 0x10790f 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x26)) s (0x10790f + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x10790f 5 13 (.sib 0 (some 5) 0 (.d8 0x26))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[491, 375, 5]
    (.letOp (n := 494) (.out 0x107914 (movzxR32M8Effect 0x107914 6 13 (.sib 4 none 0 (.d8 0x54))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 495) (.exec 0x107914 (LoadPre 0x107914 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x54)) s (0x107914 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x107914 6 13 (.sib 4 none 0 (.d8 0x54))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 496) (.exec 0x10791a (StorePre 0x10791a 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x27)) s (0x10791a + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x10791a 5 13 (.sib 0 (some 5) 0 (.d8 0x27))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[494, 375, 5]
    (.letOp (n := 497) (.out 0x10791f (movzxR32M8Effect 0x10791f 6 13 (.sib 4 none 0 (.d8 0x53))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 498) (.exec 0x10791f (LoadPre 0x10791f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x53)) s (0x10791f + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x10791f 6 13 (.sib 4 none 0 (.d8 0x53))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 499) (.exec 0x107925 (StorePre 0x107925 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x28)) s (0x107925 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x107925 5 13 (.sib 0 (some 5) 0 (.d8 0x28))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[497, 375, 5]
    (.letOp (n := 500) (.out 0x10792a (movzxR32M8Effect 0x10792a 6 13 (.sib 4 none 0 (.d8 0x52))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 501) (.exec 0x10792a (LoadPre 0x10792a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x52)) s (0x10792a + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x10792a 6 13 (.sib 4 none 0 (.d8 0x52))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 502) (.exec 0x107930 (StorePre 0x107930 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x29)) s (0x107930 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x107930 5 13 (.sib 0 (some 5) 0 (.d8 0x29))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[500, 375, 5]
    (.letOp (n := 503) (.out 0x107935 (movzxR32M8Effect 0x107935 6 13 (.sib 4 none 0 (.d8 0x51))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 504) (.exec 0x107935 (LoadPre 0x107935 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x51)) s (0x107935 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x107935 6 13 (.sib 4 none 0 (.d8 0x51))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 505) (.exec 0x10793b (StorePre 0x10793b 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x2a)) s (0x10793b + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x10793b 5 13 (.sib 0 (some 5) 0 (.d8 0x2a))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[503, 375, 5]
    (.letOp (n := 506) (.out 0x107940 (movzxR32M8Effect 0x107940 6 13 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 507) (.exec 0x107940 (LoadPre 0x107940 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x107940 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x107940 6 13 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 508) (.exec 0x107946 (StorePre 0x107946 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x2b)) s (0x107946 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x107946 5 13 (.sib 0 (some 5) 0 (.d8 0x2b))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[506, 375, 5]
    (.letOp (n := 509) (.out 0x10794b (movzxR32M8Effect 0x10794b 6 13 (.sib 4 none 0 (.d8 0x4f))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 510) (.exec 0x10794b (LoadPre 0x10794b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4f)) s (0x10794b + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x10794b 6 13 (.sib 4 none 0 (.d8 0x4f))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 511) (.exec 0x107951 (StorePre 0x107951 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x2c)) s (0x107951 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x107951 5 13 (.sib 0 (some 5) 0 (.d8 0x2c))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[509, 375, 5]
    (b_l107315_14))))))))))))))))))))))))))))))

def bytes_l107315_13 : List UInt8 :=
  [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x58, 0x44, 0x88, 0x6C, 0x28, 0x23, 0x44, 0x0F, 0xB6, 0x6C, 0x24,
    0x57, 0x44, 0x88, 0x6C, 0x28, 0x24, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x56, 0x44, 0x88, 0x6C, 0x28,
    0x25, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x55, 0x44, 0x88, 0x6C, 0x28, 0x26, 0x44, 0x0F, 0xB6, 0x6C,
    0x24, 0x54, 0x44, 0x88, 0x6C, 0x28, 0x27, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x53, 0x44, 0x88, 0x6C,
    0x28, 0x28, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x52, 0x44, 0x88, 0x6C, 0x28, 0x29, 0x44, 0x0F, 0xB6,
    0x6C, 0x24, 0x51, 0x44, 0x88, 0x6C, 0x28, 0x2A, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x50, 0x44, 0x88,
    0x6C, 0x28, 0x2B, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x4F, 0x44, 0x88, 0x6C, 0x28, 0x2C] ++ bytes_l107315_14

theorem code_l107315_13 : ∀ x ∈ codeRange 0x1078e8 bytes_l107315_13, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x78e8 110 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l107315_14

def b_l107315_12 : Block Op Label signature Reg.count 452 :=
  .letOp (n := 452) (.out 0x10787a (movzxR32M8Effect 0x10787a 6 13 (.sib 4 none 0 (.d8 0x62))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 453) (.exec 0x10787a (LoadPre 0x10787a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x62)) s (0x10787a + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x10787a 6 13 (.sib 4 none 0 (.d8 0x62))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 454) (.exec 0x107880 (StorePre 0x107880 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x19)) s (0x107880 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x107880 5 13 (.sib 0 (some 5) 0 (.d8 0x19))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[452, 375, 5]
    (.letOp (n := 455) (.out 0x107885 (movzxR32M8Effect 0x107885 6 13 (.sib 4 none 0 (.d8 0x61))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 456) (.exec 0x107885 (LoadPre 0x107885 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x61)) s (0x107885 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x107885 6 13 (.sib 4 none 0 (.d8 0x61))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 457) (.exec 0x10788b (StorePre 0x10788b 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x1a)) s (0x10788b + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x10788b 5 13 (.sib 0 (some 5) 0 (.d8 0x1a))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[455, 375, 5]
    (.letOp (n := 458) (.out 0x107890 (movzxR32M8Effect 0x107890 6 13 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 459) (.exec 0x107890 (LoadPre 0x107890 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x107890 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x107890 6 13 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 460) (.exec 0x107896 (StorePre 0x107896 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x1b)) s (0x107896 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x107896 5 13 (.sib 0 (some 5) 0 (.d8 0x1b))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[458, 375, 5]
    (.letOp (n := 461) (.out 0x10789b (movzxR32M8Effect 0x10789b 6 13 (.sib 4 none 0 (.d8 0x5f))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 462) (.exec 0x10789b (LoadPre 0x10789b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5f)) s (0x10789b + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x10789b 6 13 (.sib 4 none 0 (.d8 0x5f))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 463) (.exec 0x1078a1 (StorePre 0x1078a1 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x1c)) s (0x1078a1 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1078a1 5 13 (.sib 0 (some 5) 0 (.d8 0x1c))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[461, 375, 5]
    (.letOp (n := 464) (.out 0x1078a6 (movzxR32M8Effect 0x1078a6 6 13 (.sib 4 none 0 (.d8 0x5e))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 465) (.exec 0x1078a6 (LoadPre 0x1078a6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5e)) s (0x1078a6 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1078a6 6 13 (.sib 4 none 0 (.d8 0x5e))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 466) (.exec 0x1078ac (StorePre 0x1078ac 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x1d)) s (0x1078ac + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1078ac 5 13 (.sib 0 (some 5) 0 (.d8 0x1d))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[464, 375, 5]
    (.letOp (n := 467) (.out 0x1078b1 (movzxR32M8Effect 0x1078b1 6 13 (.sib 4 none 0 (.d8 0x5d))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 468) (.exec 0x1078b1 (LoadPre 0x1078b1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5d)) s (0x1078b1 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1078b1 6 13 (.sib 4 none 0 (.d8 0x5d))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 469) (.exec 0x1078b7 (StorePre 0x1078b7 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x1e)) s (0x1078b7 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1078b7 5 13 (.sib 0 (some 5) 0 (.d8 0x1e))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[467, 375, 5]
    (.letOp (n := 470) (.out 0x1078bc (movzxR32M8Effect 0x1078bc 6 13 (.sib 4 none 0 (.d8 0x5c))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 471) (.exec 0x1078bc (LoadPre 0x1078bc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5c)) s (0x1078bc + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1078bc 6 13 (.sib 4 none 0 (.d8 0x5c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 472) (.exec 0x1078c2 (StorePre 0x1078c2 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x1f)) s (0x1078c2 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1078c2 5 13 (.sib 0 (some 5) 0 (.d8 0x1f))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[470, 375, 5]
    (.letOp (n := 473) (.out 0x1078c7 (movzxR32M8Effect 0x1078c7 6 13 (.sib 4 none 0 (.d8 0x5b))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 474) (.exec 0x1078c7 (LoadPre 0x1078c7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5b)) s (0x1078c7 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1078c7 6 13 (.sib 4 none 0 (.d8 0x5b))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 475) (.exec 0x1078cd (StorePre 0x1078cd 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x20)) s (0x1078cd + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1078cd 5 13 (.sib 0 (some 5) 0 (.d8 0x20))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[473, 375, 5]
    (.letOp (n := 476) (.out 0x1078d2 (movzxR32M8Effect 0x1078d2 6 13 (.sib 4 none 0 (.d8 0x5a))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 477) (.exec 0x1078d2 (LoadPre 0x1078d2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5a)) s (0x1078d2 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1078d2 6 13 (.sib 4 none 0 (.d8 0x5a))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 478) (.exec 0x1078d8 (StorePre 0x1078d8 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x21)) s (0x1078d8 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1078d8 5 13 (.sib 0 (some 5) 0 (.d8 0x21))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[476, 375, 5]
    (.letOp (n := 479) (.out 0x1078dd (movzxR32M8Effect 0x1078dd 6 13 (.sib 4 none 0 (.d8 0x59))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 480) (.exec 0x1078dd (LoadPre 0x1078dd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x59)) s (0x1078dd + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1078dd 6 13 (.sib 4 none 0 (.d8 0x59))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 481) (.exec 0x1078e3 (StorePre 0x1078e3 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x22)) s (0x1078e3 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1078e3 5 13 (.sib 0 (some 5) 0 (.d8 0x22))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[479, 375, 5]
    (b_l107315_13))))))))))))))))))))))))))))))

def bytes_l107315_12 : List UInt8 :=
  [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x62, 0x44, 0x88, 0x6C, 0x28, 0x19, 0x44, 0x0F, 0xB6, 0x6C, 0x24,
    0x61, 0x44, 0x88, 0x6C, 0x28, 0x1A, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x60, 0x44, 0x88, 0x6C, 0x28,
    0x1B, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x5F, 0x44, 0x88, 0x6C, 0x28, 0x1C, 0x44, 0x0F, 0xB6, 0x6C,
    0x24, 0x5E, 0x44, 0x88, 0x6C, 0x28, 0x1D, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x5D, 0x44, 0x88, 0x6C,
    0x28, 0x1E, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x5C, 0x44, 0x88, 0x6C, 0x28, 0x1F, 0x44, 0x0F, 0xB6,
    0x6C, 0x24, 0x5B, 0x44, 0x88, 0x6C, 0x28, 0x20, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x5A, 0x44, 0x88,
    0x6C, 0x28, 0x21, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x59, 0x44, 0x88, 0x6C, 0x28, 0x22] ++ bytes_l107315_13

theorem code_l107315_12 : ∀ x ∈ codeRange 0x10787a bytes_l107315_12, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x787a 110 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l107315_13

def b_l107315_11 : Block Op Label signature Reg.count 422 :=
  .letOp (n := 422) (.out 0x107809 (movzxR32M8Effect 0x107809 6 13 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 423) (.exec 0x107809 (LoadPre 0x107809 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x107809 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x107809 6 13 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 424) (.exec 0x10780f (StorePre 0x10780f 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0xf)) s (0x10780f + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x10780f 5 13 (.sib 0 (some 5) 0 (.d8 0xf))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[422, 375, 5]
    (.letOp (n := 425) (.out 0x107814 (movzxR32M8Effect 0x107814 9 13 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 426) (.exec 0x107814 (LoadPre 0x107814 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x107814 + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x107814 9 13 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 427) (.exec 0x10781d (StorePre 0x10781d 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x10)) s (0x10781d + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x10781d 5 13 (.sib 0 (some 5) 0 (.d8 0x10))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[425, 375, 5]
    (.letOp (n := 428) (.out 0x107822 (movzxR32M8Effect 0x107822 6 13 (.sib 4 none 0 (.d8 0x6a))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 429) (.exec 0x107822 (LoadPre 0x107822 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6a)) s (0x107822 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x107822 6 13 (.sib 4 none 0 (.d8 0x6a))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 430) (.exec 0x107828 (StorePre 0x107828 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x11)) s (0x107828 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x107828 5 13 (.sib 0 (some 5) 0 (.d8 0x11))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[428, 375, 5]
    (.letOp (n := 431) (.out 0x10782d (movzxR32M8Effect 0x10782d 6 13 (.sib 4 none 0 (.d8 0x69))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 432) (.exec 0x10782d (LoadPre 0x10782d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x69)) s (0x10782d + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x10782d 6 13 (.sib 4 none 0 (.d8 0x69))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 433) (.exec 0x107833 (StorePre 0x107833 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x12)) s (0x107833 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x107833 5 13 (.sib 0 (some 5) 0 (.d8 0x12))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[431, 375, 5]
    (.letOp (n := 434) (.out 0x107838 (movzxR32M8Effect 0x107838 6 13 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 435) (.exec 0x107838 (LoadPre 0x107838 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x107838 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x107838 6 13 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 436) (.exec 0x10783e (StorePre 0x10783e 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x13)) s (0x10783e + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x10783e 5 13 (.sib 0 (some 5) 0 (.d8 0x13))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[434, 375, 5]
    (.letOp (n := 437) (.out 0x107843 (movzxR32M8Effect 0x107843 6 13 (.sib 4 none 0 (.d8 0x67))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 438) (.exec 0x107843 (LoadPre 0x107843 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x67)) s (0x107843 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x107843 6 13 (.sib 4 none 0 (.d8 0x67))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 439) (.exec 0x107849 (StorePre 0x107849 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x14)) s (0x107849 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x107849 5 13 (.sib 0 (some 5) 0 (.d8 0x14))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[437, 375, 5]
    (.letOp (n := 440) (.out 0x10784e (movzxR32M8Effect 0x10784e 6 13 (.sib 4 none 0 (.d8 0x66))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 441) (.exec 0x10784e (LoadPre 0x10784e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x66)) s (0x10784e + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x10784e 6 13 (.sib 4 none 0 (.d8 0x66))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 442) (.exec 0x107854 (StorePre 0x107854 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x15)) s (0x107854 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x107854 5 13 (.sib 0 (some 5) 0 (.d8 0x15))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[440, 375, 5]
    (.letOp (n := 443) (.out 0x107859 (movzxR32M8Effect 0x107859 6 13 (.sib 4 none 0 (.d8 0x65))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 444) (.exec 0x107859 (LoadPre 0x107859 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x65)) s (0x107859 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x107859 6 13 (.sib 4 none 0 (.d8 0x65))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 445) (.exec 0x10785f (StorePre 0x10785f 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x16)) s (0x10785f + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x10785f 5 13 (.sib 0 (some 5) 0 (.d8 0x16))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[443, 375, 5]
    (.letOp (n := 446) (.out 0x107864 (movzxR32M8Effect 0x107864 6 13 (.sib 4 none 0 (.d8 0x64))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 447) (.exec 0x107864 (LoadPre 0x107864 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x64)) s (0x107864 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x107864 6 13 (.sib 4 none 0 (.d8 0x64))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 448) (.exec 0x10786a (StorePre 0x10786a 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x17)) s (0x10786a + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x10786a 5 13 (.sib 0 (some 5) 0 (.d8 0x17))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[446, 375, 5]
    (.letOp (n := 449) (.out 0x10786f (movzxR32M8Effect 0x10786f 6 13 (.sib 4 none 0 (.d8 0x63))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 450) (.exec 0x10786f (LoadPre 0x10786f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x63)) s (0x10786f + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x10786f 6 13 (.sib 4 none 0 (.d8 0x63))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 451) (.exec 0x107875 (StorePre 0x107875 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x18)) s (0x107875 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x107875 5 13 (.sib 0 (some 5) 0 (.d8 0x18))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[449, 375, 5]
    (b_l107315_12))))))))))))))))))))))))))))))

def bytes_l107315_11 : List UInt8 :=
  [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x78, 0x44, 0x88, 0x6C, 0x28, 0x0F, 0x44, 0x0F, 0xB6, 0xAC, 0x24,
    0x90, 0x00, 0x00, 0x00, 0x44, 0x88, 0x6C, 0x28, 0x10, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x6A, 0x44,
    0x88, 0x6C, 0x28, 0x11, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x69, 0x44, 0x88, 0x6C, 0x28, 0x12, 0x44,
    0x0F, 0xB6, 0x6C, 0x24, 0x68, 0x44, 0x88, 0x6C, 0x28, 0x13, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x67,
    0x44, 0x88, 0x6C, 0x28, 0x14, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x66, 0x44, 0x88, 0x6C, 0x28, 0x15,
    0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x65, 0x44, 0x88, 0x6C, 0x28, 0x16, 0x44, 0x0F, 0xB6, 0x6C, 0x24,
    0x64, 0x44, 0x88, 0x6C, 0x28, 0x17, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x63, 0x44, 0x88, 0x6C, 0x28,
    0x18] ++ bytes_l107315_12

theorem code_l107315_11 : ∀ x ∈ codeRange 0x107809 bytes_l107315_11, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x7809 113 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l107315_12

def b_l107315_10 : Block Op Label signature Reg.count 392 :=
  .letOp (n := 392) (.out 0x107795 (movzxR32M8Effect 0x107795 6 13 (.sib 4 none 0 (.d8 0x72))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 393) (.exec 0x107795 (LoadPre 0x107795 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x72)) s (0x107795 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x107795 6 13 (.sib 4 none 0 (.d8 0x72))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 394) (.exec 0x10779b (StorePre 0x10779b 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x5)) s (0x10779b + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x10779b 5 13 (.sib 0 (some 5) 0 (.d8 0x5))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[392, 375, 5]
    (.letOp (n := 395) (.out 0x1077a0 (movzxR32M8Effect 0x1077a0 6 13 (.sib 4 none 0 (.d8 0x71))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 396) (.exec 0x1077a0 (LoadPre 0x1077a0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x71)) s (0x1077a0 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1077a0 6 13 (.sib 4 none 0 (.d8 0x71))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 397) (.exec 0x1077a6 (StorePre 0x1077a6 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x6)) s (0x1077a6 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1077a6 5 13 (.sib 0 (some 5) 0 (.d8 0x6))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[395, 375, 5]
    (.letOp (n := 398) (.out 0x1077ab (movzxR32M8Effect 0x1077ab 6 13 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 399) (.exec 0x1077ab (LoadPre 0x1077ab (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x1077ab + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1077ab 6 13 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 400) (.exec 0x1077b1 (StorePre 0x1077b1 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x7)) s (0x1077b1 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1077b1 5 13 (.sib 0 (some 5) 0 (.d8 0x7))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[398, 375, 5]
    (.letOp (n := 401) (.out 0x1077b6 (movzxR32M8Effect 0x1077b6 6 13 (.sib 4 none 0 (.d8 0x6f))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 402) (.exec 0x1077b6 (LoadPre 0x1077b6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6f)) s (0x1077b6 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1077b6 6 13 (.sib 4 none 0 (.d8 0x6f))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 403) (.exec 0x1077bc (StorePre 0x1077bc 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x8)) s (0x1077bc + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1077bc 5 13 (.sib 0 (some 5) 0 (.d8 0x8))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[401, 375, 5]
    (.letOp (n := 404) (.out 0x1077c1 (movzxR32M8Effect 0x1077c1 6 13 (.sib 4 none 0 (.d8 0x6e))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 405) (.exec 0x1077c1 (LoadPre 0x1077c1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6e)) s (0x1077c1 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1077c1 6 13 (.sib 4 none 0 (.d8 0x6e))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 406) (.exec 0x1077c7 (StorePre 0x1077c7 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x9)) s (0x1077c7 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1077c7 5 13 (.sib 0 (some 5) 0 (.d8 0x9))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[404, 375, 5]
    (.letOp (n := 407) (.out 0x1077cc (movzxR32M8Effect 0x1077cc 6 13 (.sib 4 none 0 (.d8 0x6d))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 408) (.exec 0x1077cc (LoadPre 0x1077cc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6d)) s (0x1077cc + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1077cc 6 13 (.sib 4 none 0 (.d8 0x6d))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 409) (.exec 0x1077d2 (StorePre 0x1077d2 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0xa)) s (0x1077d2 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1077d2 5 13 (.sib 0 (some 5) 0 (.d8 0xa))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[407, 375, 5]
    (.letOp (n := 410) (.out 0x1077d7 (movzxR32M8Effect 0x1077d7 6 13 (.sib 4 none 0 (.d8 0x6c))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 411) (.exec 0x1077d7 (LoadPre 0x1077d7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6c)) s (0x1077d7 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1077d7 6 13 (.sib 4 none 0 (.d8 0x6c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 412) (.exec 0x1077dd (StorePre 0x1077dd 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0xb)) s (0x1077dd + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1077dd 5 13 (.sib 0 (some 5) 0 (.d8 0xb))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[410, 375, 5]
    (.letOp (n := 413) (.out 0x1077e2 (movzxR32M8Effect 0x1077e2 6 13 (.sib 4 none 0 (.d8 0x6b))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 414) (.exec 0x1077e2 (LoadPre 0x1077e2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6b)) s (0x1077e2 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1077e2 6 13 (.sib 4 none 0 (.d8 0x6b))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 415) (.exec 0x1077e8 (StorePre 0x1077e8 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0xc)) s (0x1077e8 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1077e8 5 13 (.sib 0 (some 5) 0 (.d8 0xc))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[413, 375, 5]
    (.letOp (n := 416) (.out 0x1077ed (movzxR32M8Effect 0x1077ed 9 13 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 417) (.exec 0x1077ed (LoadPre 0x1077ed (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1077ed + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x1077ed 9 13 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 418) (.exec 0x1077f6 (StorePre 0x1077f6 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0xd)) s (0x1077f6 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1077f6 5 13 (.sib 0 (some 5) 0 (.d8 0xd))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[416, 375, 5]
    (.letOp (n := 419) (.out 0x1077fb (movzxR32M8Effect 0x1077fb 9 13 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 420) (.exec 0x1077fb (LoadPre 0x1077fb (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1077fb + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x1077fb 9 13 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 421) (.exec 0x107804 (StorePre 0x107804 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0xe)) s (0x107804 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x107804 5 13 (.sib 0 (some 5) 0 (.d8 0xe))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[419, 375, 5]
    (b_l107315_11))))))))))))))))))))))))))))))

def bytes_l107315_10 : List UInt8 :=
  [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x72, 0x44, 0x88, 0x6C, 0x28, 0x05, 0x44, 0x0F, 0xB6, 0x6C, 0x24,
    0x71, 0x44, 0x88, 0x6C, 0x28, 0x06, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x70, 0x44, 0x88, 0x6C, 0x28,
    0x07, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x6F, 0x44, 0x88, 0x6C, 0x28, 0x08, 0x44, 0x0F, 0xB6, 0x6C,
    0x24, 0x6E, 0x44, 0x88, 0x6C, 0x28, 0x09, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x6D, 0x44, 0x88, 0x6C,
    0x28, 0x0A, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x6C, 0x44, 0x88, 0x6C, 0x28, 0x0B, 0x44, 0x0F, 0xB6,
    0x6C, 0x24, 0x6B, 0x44, 0x88, 0x6C, 0x28, 0x0C, 0x44, 0x0F, 0xB6, 0xAC, 0x24, 0x88, 0x00, 0x00,
    0x00, 0x44, 0x88, 0x6C, 0x28, 0x0D, 0x44, 0x0F, 0xB6, 0xAC, 0x24, 0x80, 0x00, 0x00, 0x00, 0x44,
    0x88, 0x6C, 0x28, 0x0E] ++ bytes_l107315_11

theorem code_l107315_10 : ∀ x ∈ codeRange 0x107795 bytes_l107315_10, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x7795 116 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l107315_11

def b_l107315_9 : Block Op Label signature Reg.count 357 :=
  .letOp (n := 357) (.out 0x107720 (xorR8M8Effect 0x107720 5 8 (.sib 0 (some 5) 0 (.d8 0x3b))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0, .gpr 5] []) (.reg (.gpr 8))) #v[355, 91, 5]
    (.letOp (n := 358) (.exec 0x107720 (LoadPre 0x107720 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x3b)) s (0x107720 + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x107720 5 8 (.sib 0 (some 5) 0 (.d8 0x3b))) (Reg.operands [.gpr 8, .gpr 0, .gpr 5] [])) #v[355, 91, 5]
    (.letOp (n := 359) (.out 0x107725 (movzxR32M8Effect 0x107725 8 7 (.sib 4 none 0 (.d32 0xd4))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 360) (.exec 0x107725 (LoadPre 0x107725 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd4)) s (0x107725 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107725 8 7 (.sib 4 none 0 (.d32 0xd4))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 361) (.out 0x10772d (xorR8M8Effect 0x10772d 5 7 (.sib 0 (some 5) 0 (.d8 0x3c))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0, .gpr 5] []) (.reg (.gpr 7))) #v[359, 91, 5]
    (.letOp (n := 362) (.exec 0x10772d (LoadPre 0x10772d (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x3c)) s (0x10772d + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x10772d 5 7 (.sib 0 (some 5) 0 (.d8 0x3c))) (Reg.operands [.gpr 7, .gpr 0, .gpr 5] [])) #v[359, 91, 5]
    (.letOp (n := 363) (.out 0x107732 (movzxR32M8Effect 0x107732 8 6 (.sib 4 none 0 (.d32 0xd5))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 364) (.exec 0x107732 (LoadPre 0x107732 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd5)) s (0x107732 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107732 8 6 (.sib 4 none 0 (.d32 0xd5))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 365) (.out 0x10773a (xorR8M8Effect 0x10773a 5 6 (.sib 0 (some 5) 0 (.d8 0x3d))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0, .gpr 5] []) (.reg (.gpr 6))) #v[363, 91, 5]
    (.letOp (n := 366) (.exec 0x10773a (LoadPre 0x10773a (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x3d)) s (0x10773a + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x10773a 5 6 (.sib 0 (some 5) 0 (.d8 0x3d))) (Reg.operands [.gpr 6, .gpr 0, .gpr 5] [])) #v[363, 91, 5]
    (.letOp (n := 367) (.out 0x10773f (movzxR32M8Effect 0x10773f 8 2 (.sib 4 none 0 (.d32 0xd6))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 368) (.exec 0x10773f (LoadPre 0x10773f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd6)) s (0x10773f + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x10773f 8 2 (.sib 4 none 0 (.d32 0xd6))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 369) (.out 0x107747 (xorR8M8Effect 0x107747 4 2 (.sib 0 (some 5) 0 (.d8 0x3e))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0, .gpr 5] []) (.reg (.gpr 2))) #v[367, 91, 5]
    (.letOp (n := 370) (.exec 0x107747 (LoadPre 0x107747 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x3e)) s (0x107747 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x107747 4 2 (.sib 0 (some 5) 0 (.d8 0x3e))) (Reg.operands [.gpr 2, .gpr 0, .gpr 5] [])) #v[367, 91, 5]
    (.letOp (n := 371) (.out 0x10774b (movzxR32M8Effect 0x10774b 8 1 (.sib 4 none 0 (.d32 0xd7))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 372) (.exec 0x10774b (LoadPre 0x10774b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd7)) s (0x10774b + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x10774b 8 1 (.sib 4 none 0 (.d32 0xd7))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 373) (.out 0x107753 (xorR8M8Effect 0x107753 4 1 (.sib 0 (some 5) 0 (.d8 0x3f))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[371, 91, 5]
    (.letOp (n := 374) (.exec 0x107753 (LoadPre 0x107753 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x3f)) s (0x107753 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x107753 4 1 (.sib 0 (some 5) 0 (.d8 0x3f))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[371, 91, 5]
    (.letOp (n := 375) (.out 0x107757 (movR64M64Effect 0x107757 0 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 376) (.exec 0x107757 (LoadPre 0x107757 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x107757 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107757 0 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 377) (.out 0x10775f (movzxR32M8Effect 0x10775f 6 13 (.sib 4 none 0 (.d8 0x77))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 378) (.exec 0x10775f (LoadPre 0x10775f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x77)) s (0x10775f + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x10775f 6 13 (.sib 4 none 0 (.d8 0x77))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 379) (.exec 0x107765 (StorePre 0x107765 4 (fun s => AddrMode.addr (.sib 0 (some 5) 0 .none) s (0x107765 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x107765 4 13 (.sib 0 (some 5) 0 .none)) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[377, 375, 5]
    (.letOp (n := 380) (.out 0x107769 (movzxR32M8Effect 0x107769 6 13 (.sib 4 none 0 (.d8 0x76))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 381) (.exec 0x107769 (LoadPre 0x107769 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x76)) s (0x107769 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x107769 6 13 (.sib 4 none 0 (.d8 0x76))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 382) (.exec 0x10776f (StorePre 0x10776f 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x1)) s (0x10776f + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x10776f 5 13 (.sib 0 (some 5) 0 (.d8 0x1))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[380, 375, 5]
    (.letOp (n := 383) (.out 0x107774 (movzxR32M8Effect 0x107774 6 13 (.sib 4 none 0 (.d8 0x75))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 384) (.exec 0x107774 (LoadPre 0x107774 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x75)) s (0x107774 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x107774 6 13 (.sib 4 none 0 (.d8 0x75))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 385) (.exec 0x10777a (StorePre 0x10777a 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x2)) s (0x10777a + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x10777a 5 13 (.sib 0 (some 5) 0 (.d8 0x2))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[383, 375, 5]
    (.letOp (n := 386) (.out 0x10777f (movzxR32M8Effect 0x10777f 6 13 (.sib 4 none 0 (.d8 0x74))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 387) (.exec 0x10777f (LoadPre 0x10777f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x74)) s (0x10777f + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x10777f 6 13 (.sib 4 none 0 (.d8 0x74))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 388) (.exec 0x107785 (StorePre 0x107785 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x3)) s (0x107785 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x107785 5 13 (.sib 0 (some 5) 0 (.d8 0x3))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[386, 375, 5]
    (.letOp (n := 389) (.out 0x10778a (movzxR32M8Effect 0x10778a 6 13 (.sib 4 none 0 (.d8 0x73))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 390) (.exec 0x10778a (LoadPre 0x10778a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x73)) s (0x10778a + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x10778a 6 13 (.sib 4 none 0 (.d8 0x73))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 391) (.exec 0x107790 (StorePre 0x107790 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x4)) s (0x107790 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x107790 5 13 (.sib 0 (some 5) 0 (.d8 0x4))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[389, 375, 5]
    (b_l107315_10)))))))))))))))))))))))))))))))))))

def bytes_l107315_9 : List UInt8 :=
  [0x44, 0x32, 0x44, 0x28, 0x3B, 0x0F, 0xB6, 0xBC, 0x24, 0xD4, 0x00, 0x00, 0x00, 0x40, 0x32, 0x7C,
    0x28, 0x3C, 0x0F, 0xB6, 0xB4, 0x24, 0xD5, 0x00, 0x00, 0x00, 0x40, 0x32, 0x74, 0x28, 0x3D, 0x0F,
    0xB6, 0x94, 0x24, 0xD6, 0x00, 0x00, 0x00, 0x32, 0x54, 0x28, 0x3E, 0x0F, 0xB6, 0x8C, 0x24, 0xD7,
    0x00, 0x00, 0x00, 0x32, 0x4C, 0x28, 0x3F, 0x48, 0x8B, 0x84, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x44,
    0x0F, 0xB6, 0x6C, 0x24, 0x77, 0x44, 0x88, 0x2C, 0x28, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x76, 0x44,
    0x88, 0x6C, 0x28, 0x01, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x75, 0x44, 0x88, 0x6C, 0x28, 0x02, 0x44,
    0x0F, 0xB6, 0x6C, 0x24, 0x74, 0x44, 0x88, 0x6C, 0x28, 0x03, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x73,
    0x44, 0x88, 0x6C, 0x28, 0x04] ++ bytes_l107315_10

theorem code_l107315_9 : ∀ x ∈ codeRange 0x107720 bytes_l107315_9, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x7720 117 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l107315_10

def b_l107315_8 : Block Op Label signature Reg.count 319 :=
  .letOp (n := 319) (.out 0x10769f (xorR8M8Effect 0x10769f 4 1 (.sib 0 (some 5) 0 (.d8 0x32))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[317, 91, 5]
    (.letOp (n := 320) (.exec 0x10769f (LoadPre 0x10769f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x32)) s (0x10769f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10769f 4 1 (.sib 0 (some 5) 0 (.d8 0x32))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[317, 91, 5]
    (.letOp (n := 321) (.exec 0x1076a3 (StorePre 0x1076a3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x49)) s (0x1076a3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1076a3 4 1 (.sib 4 none 0 (.d8 0x49))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[319, 4]
    (.letOp (n := 322) (.out 0x1076a7 (movzxR32M8Effect 0x1076a7 8 1 (.sib 4 none 0 (.d32 0xcb))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 323) (.exec 0x1076a7 (LoadPre 0x1076a7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xcb)) s (0x1076a7 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1076a7 8 1 (.sib 4 none 0 (.d32 0xcb))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 324) (.out 0x1076af (xorR8M8Effect 0x1076af 4 1 (.sib 0 (some 5) 0 (.d8 0x33))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[322, 91, 5]
    (.letOp (n := 325) (.exec 0x1076af (LoadPre 0x1076af (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x33)) s (0x1076af + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1076af 4 1 (.sib 0 (some 5) 0 (.d8 0x33))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[322, 91, 5]
    (.letOp (n := 326) (.exec 0x1076b3 (StorePre 0x1076b3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1076b3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1076b3 4 1 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[324, 4]
    (.letOp (n := 327) (.out 0x1076b7 (movzxR32M8Effect 0x1076b7 9 12 (.sib 4 none 0 (.d32 0xcc))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 328) (.exec 0x1076b7 (LoadPre 0x1076b7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xcc)) s (0x1076b7 + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x1076b7 9 12 (.sib 4 none 0 (.d32 0xcc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 329) (.out 0x1076c0 (xorR8M8Effect 0x1076c0 5 12 (.sib 0 (some 5) 0 (.d8 0x34))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 0, .gpr 5] []) (.reg (.gpr 12))) #v[327, 91, 5]
    (.letOp (n := 330) (.exec 0x1076c0 (LoadPre 0x1076c0 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x34)) s (0x1076c0 + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x1076c0 5 12 (.sib 0 (some 5) 0 (.d8 0x34))) (Reg.operands [.gpr 12, .gpr 0, .gpr 5] [])) #v[327, 91, 5]
    (.letOp (n := 331) (.out 0x1076c5 (movzxR32M8Effect 0x1076c5 9 15 (.sib 4 none 0 (.d32 0xcd))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 332) (.exec 0x1076c5 (LoadPre 0x1076c5 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xcd)) s (0x1076c5 + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x1076c5 9 15 (.sib 4 none 0 (.d32 0xcd))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 333) (.out 0x1076ce (xorR8M8Effect 0x1076ce 5 15 (.sib 0 (some 5) 0 (.d8 0x35))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 0, .gpr 5] []) (.reg (.gpr 15))) #v[331, 91, 5]
    (.letOp (n := 334) (.exec 0x1076ce (LoadPre 0x1076ce (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x35)) s (0x1076ce + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x1076ce 5 15 (.sib 0 (some 5) 0 (.d8 0x35))) (Reg.operands [.gpr 15, .gpr 0, .gpr 5] [])) #v[331, 91, 5]
    (.letOp (n := 335) (.out 0x1076d3 (movzxR32M8Effect 0x1076d3 9 14 (.sib 4 none 0 (.d32 0xce))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 336) (.exec 0x1076d3 (LoadPre 0x1076d3 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xce)) s (0x1076d3 + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x1076d3 9 14 (.sib 4 none 0 (.d32 0xce))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 337) (.out 0x1076dc (xorR8M8Effect 0x1076dc 5 14 (.sib 0 (some 5) 0 (.d8 0x36))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 0, .gpr 5] []) (.reg (.gpr 14))) #v[335, 91, 5]
    (.letOp (n := 338) (.exec 0x1076dc (LoadPre 0x1076dc (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x36)) s (0x1076dc + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x1076dc 5 14 (.sib 0 (some 5) 0 (.d8 0x36))) (Reg.operands [.gpr 14, .gpr 0, .gpr 5] [])) #v[335, 91, 5]
    (.letOp (n := 339) (.out 0x1076e1 (movzxR32M8Effect 0x1076e1 8 3 (.sib 4 none 0 (.d32 0xcf))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 340) (.exec 0x1076e1 (LoadPre 0x1076e1 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xcf)) s (0x1076e1 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1076e1 8 3 (.sib 4 none 0 (.d32 0xcf))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 341) (.out 0x1076e9 (xorR8M8Effect 0x1076e9 4 3 (.sib 0 (some 5) 0 (.d8 0x37))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0, .gpr 5] []) (.reg (.gpr 3))) #v[339, 91, 5]
    (.letOp (n := 342) (.exec 0x1076e9 (LoadPre 0x1076e9 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x37)) s (0x1076e9 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1076e9 4 3 (.sib 0 (some 5) 0 (.d8 0x37))) (Reg.operands [.gpr 3, .gpr 0, .gpr 5] [])) #v[339, 91, 5]
    (.letOp (n := 343) (.out 0x1076ed (movzxR32M8Effect 0x1076ed 9 11 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 344) (.exec 0x1076ed (LoadPre 0x1076ed (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x1076ed + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x1076ed 9 11 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 345) (.out 0x1076f6 (xorR8M8Effect 0x1076f6 5 11 (.sib 0 (some 5) 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0, .gpr 5] []) (.reg (.gpr 11))) #v[343, 91, 5]
    (.letOp (n := 346) (.exec 0x1076f6 (LoadPre 0x1076f6 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x38)) s (0x1076f6 + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x1076f6 5 11 (.sib 0 (some 5) 0 (.d8 0x38))) (Reg.operands [.gpr 11, .gpr 0, .gpr 5] [])) #v[343, 91, 5]
    (.letOp (n := 347) (.out 0x1076fb (movzxR32M8Effect 0x1076fb 9 10 (.sib 4 none 0 (.d32 0xd1))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 348) (.exec 0x1076fb (LoadPre 0x1076fb (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd1)) s (0x1076fb + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x1076fb 9 10 (.sib 4 none 0 (.d32 0xd1))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 349) (.out 0x107704 (xorR8M8Effect 0x107704 5 10 (.sib 0 (some 5) 0 (.d8 0x39))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0, .gpr 5] []) (.reg (.gpr 10))) #v[347, 91, 5]
    (.letOp (n := 350) (.exec 0x107704 (LoadPre 0x107704 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x39)) s (0x107704 + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x107704 5 10 (.sib 0 (some 5) 0 (.d8 0x39))) (Reg.operands [.gpr 10, .gpr 0, .gpr 5] [])) #v[347, 91, 5]
    (.letOp (n := 351) (.out 0x107709 (movzxR32M8Effect 0x107709 9 9 (.sib 4 none 0 (.d32 0xd2))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 352) (.exec 0x107709 (LoadPre 0x107709 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd2)) s (0x107709 + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x107709 9 9 (.sib 4 none 0 (.d32 0xd2))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 353) (.out 0x107712 (xorR8M8Effect 0x107712 5 9 (.sib 0 (some 5) 0 (.d8 0x3a))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0, .gpr 5] []) (.reg (.gpr 9))) #v[351, 91, 5]
    (.letOp (n := 354) (.exec 0x107712 (LoadPre 0x107712 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x3a)) s (0x107712 + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x107712 5 9 (.sib 0 (some 5) 0 (.d8 0x3a))) (Reg.operands [.gpr 9, .gpr 0, .gpr 5] [])) #v[351, 91, 5]
    (.letOp (n := 355) (.out 0x107717 (movzxR32M8Effect 0x107717 9 8 (.sib 4 none 0 (.d32 0xd3))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 356) (.exec 0x107717 (LoadPre 0x107717 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd3)) s (0x107717 + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x107717 9 8 (.sib 4 none 0 (.d32 0xd3))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l107315_9))))))))))))))))))))))))))))))))))))))

def bytes_l107315_8 : List UInt8 :=
  [0x32, 0x4C, 0x28, 0x32, 0x88, 0x4C, 0x24, 0x49, 0x0F, 0xB6, 0x8C, 0x24, 0xCB, 0x00, 0x00, 0x00,
    0x32, 0x4C, 0x28, 0x33, 0x88, 0x4C, 0x24, 0x48, 0x44, 0x0F, 0xB6, 0xA4, 0x24, 0xCC, 0x00, 0x00,
    0x00, 0x44, 0x32, 0x64, 0x28, 0x34, 0x44, 0x0F, 0xB6, 0xBC, 0x24, 0xCD, 0x00, 0x00, 0x00, 0x44,
    0x32, 0x7C, 0x28, 0x35, 0x44, 0x0F, 0xB6, 0xB4, 0x24, 0xCE, 0x00, 0x00, 0x00, 0x44, 0x32, 0x74,
    0x28, 0x36, 0x0F, 0xB6, 0x9C, 0x24, 0xCF, 0x00, 0x00, 0x00, 0x32, 0x5C, 0x28, 0x37, 0x44, 0x0F,
    0xB6, 0x9C, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x44, 0x32, 0x5C, 0x28, 0x38, 0x44, 0x0F, 0xB6, 0x94,
    0x24, 0xD1, 0x00, 0x00, 0x00, 0x44, 0x32, 0x54, 0x28, 0x39, 0x44, 0x0F, 0xB6, 0x8C, 0x24, 0xD2,
    0x00, 0x00, 0x00, 0x44, 0x32, 0x4C, 0x28, 0x3A, 0x44, 0x0F, 0xB6, 0x84, 0x24, 0xD3, 0x00, 0x00,
    0x00] ++ bytes_l107315_9

theorem code_l107315_8 : ∀ x ∈ codeRange 0x10769f bytes_l107315_8, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x769f 129 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l107315_9

def b_l107315_7 : Block Op Label signature Reg.count 286 :=
  .letOp (n := 286) (.exec 0x107633 (StorePre 0x107633 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x107633 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x107633 4 1 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[284, 4]
    (.letOp (n := 287) (.out 0x107637 (movzxR32M8Effect 0x107637 8 1 (.sib 4 none 0 (.d32 0xc4))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 288) (.exec 0x107637 (LoadPre 0x107637 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc4)) s (0x107637 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107637 8 1 (.sib 4 none 0 (.d32 0xc4))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 289) (.out 0x10763f (xorR8M8Effect 0x10763f 4 1 (.sib 0 (some 5) 0 (.d8 0x2c))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[287, 91, 5]
    (.letOp (n := 290) (.exec 0x10763f (LoadPre 0x10763f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x2c)) s (0x10763f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10763f 4 1 (.sib 0 (some 5) 0 (.d8 0x2c))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[287, 91, 5]
    (.letOp (n := 291) (.exec 0x107643 (StorePre 0x107643 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4f)) s (0x107643 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x107643 4 1 (.sib 4 none 0 (.d8 0x4f))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[289, 4]
    (.letOp (n := 292) (.out 0x107647 (movzxR32M8Effect 0x107647 8 1 (.sib 4 none 0 (.d32 0xc5))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 293) (.exec 0x107647 (LoadPre 0x107647 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc5)) s (0x107647 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107647 8 1 (.sib 4 none 0 (.d32 0xc5))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 294) (.out 0x10764f (xorR8M8Effect 0x10764f 4 1 (.sib 0 (some 5) 0 (.d8 0x2d))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[292, 91, 5]
    (.letOp (n := 295) (.exec 0x10764f (LoadPre 0x10764f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x2d)) s (0x10764f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10764f 4 1 (.sib 0 (some 5) 0 (.d8 0x2d))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[292, 91, 5]
    (.letOp (n := 296) (.exec 0x107653 (StorePre 0x107653 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4e)) s (0x107653 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x107653 4 1 (.sib 4 none 0 (.d8 0x4e))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[294, 4]
    (.letOp (n := 297) (.out 0x107657 (movzxR32M8Effect 0x107657 8 1 (.sib 4 none 0 (.d32 0xc6))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 298) (.exec 0x107657 (LoadPre 0x107657 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc6)) s (0x107657 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107657 8 1 (.sib 4 none 0 (.d32 0xc6))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 299) (.out 0x10765f (xorR8M8Effect 0x10765f 4 1 (.sib 0 (some 5) 0 (.d8 0x2e))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[297, 91, 5]
    (.letOp (n := 300) (.exec 0x10765f (LoadPre 0x10765f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x2e)) s (0x10765f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10765f 4 1 (.sib 0 (some 5) 0 (.d8 0x2e))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[297, 91, 5]
    (.letOp (n := 301) (.exec 0x107663 (StorePre 0x107663 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4d)) s (0x107663 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x107663 4 1 (.sib 4 none 0 (.d8 0x4d))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[299, 4]
    (.letOp (n := 302) (.out 0x107667 (movzxR32M8Effect 0x107667 8 1 (.sib 4 none 0 (.d32 0xc7))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 303) (.exec 0x107667 (LoadPre 0x107667 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc7)) s (0x107667 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107667 8 1 (.sib 4 none 0 (.d32 0xc7))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 304) (.out 0x10766f (xorR8M8Effect 0x10766f 4 1 (.sib 0 (some 5) 0 (.d8 0x2f))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[302, 91, 5]
    (.letOp (n := 305) (.exec 0x10766f (LoadPre 0x10766f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x2f)) s (0x10766f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10766f 4 1 (.sib 0 (some 5) 0 (.d8 0x2f))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[302, 91, 5]
    (.letOp (n := 306) (.exec 0x107673 (StorePre 0x107673 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4c)) s (0x107673 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x107673 4 1 (.sib 4 none 0 (.d8 0x4c))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[304, 4]
    (.letOp (n := 307) (.out 0x107677 (movzxR32M8Effect 0x107677 8 1 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 308) (.exec 0x107677 (LoadPre 0x107677 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x107677 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107677 8 1 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 309) (.out 0x10767f (xorR8M8Effect 0x10767f 4 1 (.sib 0 (some 5) 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[307, 91, 5]
    (.letOp (n := 310) (.exec 0x10767f (LoadPre 0x10767f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x30)) s (0x10767f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10767f 4 1 (.sib 0 (some 5) 0 (.d8 0x30))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[307, 91, 5]
    (.letOp (n := 311) (.exec 0x107683 (StorePre 0x107683 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4b)) s (0x107683 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x107683 4 1 (.sib 4 none 0 (.d8 0x4b))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[309, 4]
    (.letOp (n := 312) (.out 0x107687 (movzxR32M8Effect 0x107687 8 1 (.sib 4 none 0 (.d32 0xc9))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 313) (.exec 0x107687 (LoadPre 0x107687 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc9)) s (0x107687 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107687 8 1 (.sib 4 none 0 (.d32 0xc9))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 314) (.out 0x10768f (xorR8M8Effect 0x10768f 4 1 (.sib 0 (some 5) 0 (.d8 0x31))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[312, 91, 5]
    (.letOp (n := 315) (.exec 0x10768f (LoadPre 0x10768f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x31)) s (0x10768f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10768f 4 1 (.sib 0 (some 5) 0 (.d8 0x31))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[312, 91, 5]
    (.letOp (n := 316) (.exec 0x107693 (StorePre 0x107693 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4a)) s (0x107693 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x107693 4 1 (.sib 4 none 0 (.d8 0x4a))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[314, 4]
    (.letOp (n := 317) (.out 0x107697 (movzxR32M8Effect 0x107697 8 1 (.sib 4 none 0 (.d32 0xca))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 318) (.exec 0x107697 (LoadPre 0x107697 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xca)) s (0x107697 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107697 8 1 (.sib 4 none 0 (.d32 0xca))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l107315_8)))))))))))))))))))))))))))))))))

def bytes_l107315_7 : List UInt8 :=
  [0x88, 0x4C, 0x24, 0x50, 0x0F, 0xB6, 0x8C, 0x24, 0xC4, 0x00, 0x00, 0x00, 0x32, 0x4C, 0x28, 0x2C,
    0x88, 0x4C, 0x24, 0x4F, 0x0F, 0xB6, 0x8C, 0x24, 0xC5, 0x00, 0x00, 0x00, 0x32, 0x4C, 0x28, 0x2D,
    0x88, 0x4C, 0x24, 0x4E, 0x0F, 0xB6, 0x8C, 0x24, 0xC6, 0x00, 0x00, 0x00, 0x32, 0x4C, 0x28, 0x2E,
    0x88, 0x4C, 0x24, 0x4D, 0x0F, 0xB6, 0x8C, 0x24, 0xC7, 0x00, 0x00, 0x00, 0x32, 0x4C, 0x28, 0x2F,
    0x88, 0x4C, 0x24, 0x4C, 0x0F, 0xB6, 0x8C, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x32, 0x4C, 0x28, 0x30,
    0x88, 0x4C, 0x24, 0x4B, 0x0F, 0xB6, 0x8C, 0x24, 0xC9, 0x00, 0x00, 0x00, 0x32, 0x4C, 0x28, 0x31,
    0x88, 0x4C, 0x24, 0x4A, 0x0F, 0xB6, 0x8C, 0x24, 0xCA, 0x00, 0x00, 0x00] ++ bytes_l107315_8

theorem code_l107315_7 : ∀ x ∈ codeRange 0x107633 bytes_l107315_7, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x7633 108 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l107315_8

def b_l107315_6 : Block Op Label signature Reg.count 252 :=
  .letOp (n := 252) (.out 0x1075c7 (movzxR32M8Effect 0x1075c7 8 1 (.sib 4 none 0 (.d32 0xbd))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 253) (.exec 0x1075c7 (LoadPre 0x1075c7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xbd)) s (0x1075c7 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1075c7 8 1 (.sib 4 none 0 (.d32 0xbd))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 254) (.out 0x1075cf (xorR8M8Effect 0x1075cf 4 1 (.sib 0 (some 5) 0 (.d8 0x25))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[252, 91, 5]
    (.letOp (n := 255) (.exec 0x1075cf (LoadPre 0x1075cf (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x25)) s (0x1075cf + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1075cf 4 1 (.sib 0 (some 5) 0 (.d8 0x25))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[252, 91, 5]
    (.letOp (n := 256) (.exec 0x1075d3 (StorePre 0x1075d3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x56)) s (0x1075d3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1075d3 4 1 (.sib 4 none 0 (.d8 0x56))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[254, 4]
    (.letOp (n := 257) (.out 0x1075d7 (movzxR32M8Effect 0x1075d7 8 1 (.sib 4 none 0 (.d32 0xbe))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 258) (.exec 0x1075d7 (LoadPre 0x1075d7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xbe)) s (0x1075d7 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1075d7 8 1 (.sib 4 none 0 (.d32 0xbe))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 259) (.out 0x1075df (xorR8M8Effect 0x1075df 4 1 (.sib 0 (some 5) 0 (.d8 0x26))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[257, 91, 5]
    (.letOp (n := 260) (.exec 0x1075df (LoadPre 0x1075df (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x26)) s (0x1075df + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1075df 4 1 (.sib 0 (some 5) 0 (.d8 0x26))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[257, 91, 5]
    (.letOp (n := 261) (.exec 0x1075e3 (StorePre 0x1075e3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x55)) s (0x1075e3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1075e3 4 1 (.sib 4 none 0 (.d8 0x55))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[259, 4]
    (.letOp (n := 262) (.out 0x1075e7 (movzxR32M8Effect 0x1075e7 8 1 (.sib 4 none 0 (.d32 0xbf))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 263) (.exec 0x1075e7 (LoadPre 0x1075e7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xbf)) s (0x1075e7 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1075e7 8 1 (.sib 4 none 0 (.d32 0xbf))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 264) (.out 0x1075ef (xorR8M8Effect 0x1075ef 4 1 (.sib 0 (some 5) 0 (.d8 0x27))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[262, 91, 5]
    (.letOp (n := 265) (.exec 0x1075ef (LoadPre 0x1075ef (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x27)) s (0x1075ef + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1075ef 4 1 (.sib 0 (some 5) 0 (.d8 0x27))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[262, 91, 5]
    (.letOp (n := 266) (.exec 0x1075f3 (StorePre 0x1075f3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x54)) s (0x1075f3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1075f3 4 1 (.sib 4 none 0 (.d8 0x54))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[264, 4]
    (.letOp (n := 267) (.out 0x1075f7 (movzxR32M8Effect 0x1075f7 8 1 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 268) (.exec 0x1075f7 (LoadPre 0x1075f7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x1075f7 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1075f7 8 1 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 269) (.out 0x1075ff (xorR8M8Effect 0x1075ff 4 1 (.sib 0 (some 5) 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[267, 91, 5]
    (.letOp (n := 270) (.exec 0x1075ff (LoadPre 0x1075ff (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x28)) s (0x1075ff + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1075ff 4 1 (.sib 0 (some 5) 0 (.d8 0x28))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[267, 91, 5]
    (.letOp (n := 271) (.exec 0x107603 (StorePre 0x107603 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x53)) s (0x107603 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x107603 4 1 (.sib 4 none 0 (.d8 0x53))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[269, 4]
    (.letOp (n := 272) (.out 0x107607 (movzxR32M8Effect 0x107607 8 1 (.sib 4 none 0 (.d32 0xc1))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 273) (.exec 0x107607 (LoadPre 0x107607 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc1)) s (0x107607 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107607 8 1 (.sib 4 none 0 (.d32 0xc1))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 274) (.out 0x10760f (xorR8M8Effect 0x10760f 4 1 (.sib 0 (some 5) 0 (.d8 0x29))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[272, 91, 5]
    (.letOp (n := 275) (.exec 0x10760f (LoadPre 0x10760f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x29)) s (0x10760f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10760f 4 1 (.sib 0 (some 5) 0 (.d8 0x29))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[272, 91, 5]
    (.letOp (n := 276) (.exec 0x107613 (StorePre 0x107613 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x52)) s (0x107613 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x107613 4 1 (.sib 4 none 0 (.d8 0x52))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[274, 4]
    (.letOp (n := 277) (.out 0x107617 (movzxR32M8Effect 0x107617 8 1 (.sib 4 none 0 (.d32 0xc2))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 278) (.exec 0x107617 (LoadPre 0x107617 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc2)) s (0x107617 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107617 8 1 (.sib 4 none 0 (.d32 0xc2))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 279) (.out 0x10761f (xorR8M8Effect 0x10761f 4 1 (.sib 0 (some 5) 0 (.d8 0x2a))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[277, 91, 5]
    (.letOp (n := 280) (.exec 0x10761f (LoadPre 0x10761f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x2a)) s (0x10761f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10761f 4 1 (.sib 0 (some 5) 0 (.d8 0x2a))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[277, 91, 5]
    (.letOp (n := 281) (.exec 0x107623 (StorePre 0x107623 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x51)) s (0x107623 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x107623 4 1 (.sib 4 none 0 (.d8 0x51))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[279, 4]
    (.letOp (n := 282) (.out 0x107627 (movzxR32M8Effect 0x107627 8 1 (.sib 4 none 0 (.d32 0xc3))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 283) (.exec 0x107627 (LoadPre 0x107627 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc3)) s (0x107627 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107627 8 1 (.sib 4 none 0 (.d32 0xc3))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 284) (.out 0x10762f (xorR8M8Effect 0x10762f 4 1 (.sib 0 (some 5) 0 (.d8 0x2b))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[282, 91, 5]
    (.letOp (n := 285) (.exec 0x10762f (LoadPre 0x10762f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x2b)) s (0x10762f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10762f 4 1 (.sib 0 (some 5) 0 (.d8 0x2b))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[282, 91, 5]
    (b_l107315_7))))))))))))))))))))))))))))))))))

def bytes_l107315_6 : List UInt8 :=
  [0x0F, 0xB6, 0x8C, 0x24, 0xBD, 0x00, 0x00, 0x00, 0x32, 0x4C, 0x28, 0x25, 0x88, 0x4C, 0x24, 0x56,
    0x0F, 0xB6, 0x8C, 0x24, 0xBE, 0x00, 0x00, 0x00, 0x32, 0x4C, 0x28, 0x26, 0x88, 0x4C, 0x24, 0x55,
    0x0F, 0xB6, 0x8C, 0x24, 0xBF, 0x00, 0x00, 0x00, 0x32, 0x4C, 0x28, 0x27, 0x88, 0x4C, 0x24, 0x54,
    0x0F, 0xB6, 0x8C, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x32, 0x4C, 0x28, 0x28, 0x88, 0x4C, 0x24, 0x53,
    0x0F, 0xB6, 0x8C, 0x24, 0xC1, 0x00, 0x00, 0x00, 0x32, 0x4C, 0x28, 0x29, 0x88, 0x4C, 0x24, 0x52,
    0x0F, 0xB6, 0x8C, 0x24, 0xC2, 0x00, 0x00, 0x00, 0x32, 0x4C, 0x28, 0x2A, 0x88, 0x4C, 0x24, 0x51,
    0x0F, 0xB6, 0x8C, 0x24, 0xC3, 0x00, 0x00, 0x00, 0x32, 0x4C, 0x28, 0x2B] ++ bytes_l107315_7

theorem code_l107315_6 : ∀ x ∈ codeRange 0x1075c7 bytes_l107315_6, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x75c7 108 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l107315_7

def b_l107315_5 : Block Op Label signature Reg.count 219 :=
  .letOp (n := 219) (.out 0x10755f (xorR8M8Effect 0x10755f 4 1 (.sib 0 (some 5) 0 (.d8 0x1e))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[217, 91, 5]
    (.letOp (n := 220) (.exec 0x10755f (LoadPre 0x10755f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x1e)) s (0x10755f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10755f 4 1 (.sib 0 (some 5) 0 (.d8 0x1e))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[217, 91, 5]
    (.letOp (n := 221) (.exec 0x107563 (StorePre 0x107563 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5d)) s (0x107563 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x107563 4 1 (.sib 4 none 0 (.d8 0x5d))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[219, 4]
    (.letOp (n := 222) (.out 0x107567 (movzxR32M8Effect 0x107567 8 1 (.sib 4 none 0 (.d32 0xb7))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 223) (.exec 0x107567 (LoadPre 0x107567 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb7)) s (0x107567 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107567 8 1 (.sib 4 none 0 (.d32 0xb7))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 224) (.out 0x10756f (xorR8M8Effect 0x10756f 4 1 (.sib 0 (some 5) 0 (.d8 0x1f))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[222, 91, 5]
    (.letOp (n := 225) (.exec 0x10756f (LoadPre 0x10756f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x1f)) s (0x10756f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10756f 4 1 (.sib 0 (some 5) 0 (.d8 0x1f))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[222, 91, 5]
    (.letOp (n := 226) (.exec 0x107573 (StorePre 0x107573 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5c)) s (0x107573 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x107573 4 1 (.sib 4 none 0 (.d8 0x5c))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[224, 4]
    (.letOp (n := 227) (.out 0x107577 (movzxR32M8Effect 0x107577 8 1 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 228) (.exec 0x107577 (LoadPre 0x107577 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x107577 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107577 8 1 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 229) (.out 0x10757f (xorR8M8Effect 0x10757f 4 1 (.sib 0 (some 5) 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[227, 91, 5]
    (.letOp (n := 230) (.exec 0x10757f (LoadPre 0x10757f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x20)) s (0x10757f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10757f 4 1 (.sib 0 (some 5) 0 (.d8 0x20))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[227, 91, 5]
    (.letOp (n := 231) (.exec 0x107583 (StorePre 0x107583 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5b)) s (0x107583 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x107583 4 1 (.sib 4 none 0 (.d8 0x5b))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[229, 4]
    (.letOp (n := 232) (.out 0x107587 (movzxR32M8Effect 0x107587 8 1 (.sib 4 none 0 (.d32 0xb9))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 233) (.exec 0x107587 (LoadPre 0x107587 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb9)) s (0x107587 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107587 8 1 (.sib 4 none 0 (.d32 0xb9))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 234) (.out 0x10758f (xorR8M8Effect 0x10758f 4 1 (.sib 0 (some 5) 0 (.d8 0x21))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[232, 91, 5]
    (.letOp (n := 235) (.exec 0x10758f (LoadPre 0x10758f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x21)) s (0x10758f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10758f 4 1 (.sib 0 (some 5) 0 (.d8 0x21))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[232, 91, 5]
    (.letOp (n := 236) (.exec 0x107593 (StorePre 0x107593 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5a)) s (0x107593 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x107593 4 1 (.sib 4 none 0 (.d8 0x5a))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[234, 4]
    (.letOp (n := 237) (.out 0x107597 (movzxR32M8Effect 0x107597 8 1 (.sib 4 none 0 (.d32 0xba))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 238) (.exec 0x107597 (LoadPre 0x107597 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xba)) s (0x107597 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107597 8 1 (.sib 4 none 0 (.d32 0xba))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 239) (.out 0x10759f (xorR8M8Effect 0x10759f 4 1 (.sib 0 (some 5) 0 (.d8 0x22))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[237, 91, 5]
    (.letOp (n := 240) (.exec 0x10759f (LoadPre 0x10759f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x22)) s (0x10759f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10759f 4 1 (.sib 0 (some 5) 0 (.d8 0x22))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[237, 91, 5]
    (.letOp (n := 241) (.exec 0x1075a3 (StorePre 0x1075a3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x59)) s (0x1075a3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1075a3 4 1 (.sib 4 none 0 (.d8 0x59))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[239, 4]
    (.letOp (n := 242) (.out 0x1075a7 (movzxR32M8Effect 0x1075a7 8 1 (.sib 4 none 0 (.d32 0xbb))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 243) (.exec 0x1075a7 (LoadPre 0x1075a7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xbb)) s (0x1075a7 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1075a7 8 1 (.sib 4 none 0 (.d32 0xbb))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 244) (.out 0x1075af (xorR8M8Effect 0x1075af 4 1 (.sib 0 (some 5) 0 (.d8 0x23))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[242, 91, 5]
    (.letOp (n := 245) (.exec 0x1075af (LoadPre 0x1075af (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x23)) s (0x1075af + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1075af 4 1 (.sib 0 (some 5) 0 (.d8 0x23))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[242, 91, 5]
    (.letOp (n := 246) (.exec 0x1075b3 (StorePre 0x1075b3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1075b3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1075b3 4 1 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[244, 4]
    (.letOp (n := 247) (.out 0x1075b7 (movzxR32M8Effect 0x1075b7 8 1 (.sib 4 none 0 (.d32 0xbc))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 248) (.exec 0x1075b7 (LoadPre 0x1075b7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xbc)) s (0x1075b7 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1075b7 8 1 (.sib 4 none 0 (.d32 0xbc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 249) (.out 0x1075bf (xorR8M8Effect 0x1075bf 4 1 (.sib 0 (some 5) 0 (.d8 0x24))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[247, 91, 5]
    (.letOp (n := 250) (.exec 0x1075bf (LoadPre 0x1075bf (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x24)) s (0x1075bf + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1075bf 4 1 (.sib 0 (some 5) 0 (.d8 0x24))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[247, 91, 5]
    (.letOp (n := 251) (.exec 0x1075c3 (StorePre 0x1075c3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x57)) s (0x1075c3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1075c3 4 1 (.sib 4 none 0 (.d8 0x57))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[249, 4]
    (b_l107315_6)))))))))))))))))))))))))))))))))

def bytes_l107315_5 : List UInt8 :=
  [0x32, 0x4C, 0x28, 0x1E, 0x88, 0x4C, 0x24, 0x5D, 0x0F, 0xB6, 0x8C, 0x24, 0xB7, 0x00, 0x00, 0x00,
    0x32, 0x4C, 0x28, 0x1F, 0x88, 0x4C, 0x24, 0x5C, 0x0F, 0xB6, 0x8C, 0x24, 0xB8, 0x00, 0x00, 0x00,
    0x32, 0x4C, 0x28, 0x20, 0x88, 0x4C, 0x24, 0x5B, 0x0F, 0xB6, 0x8C, 0x24, 0xB9, 0x00, 0x00, 0x00,
    0x32, 0x4C, 0x28, 0x21, 0x88, 0x4C, 0x24, 0x5A, 0x0F, 0xB6, 0x8C, 0x24, 0xBA, 0x00, 0x00, 0x00,
    0x32, 0x4C, 0x28, 0x22, 0x88, 0x4C, 0x24, 0x59, 0x0F, 0xB6, 0x8C, 0x24, 0xBB, 0x00, 0x00, 0x00,
    0x32, 0x4C, 0x28, 0x23, 0x88, 0x4C, 0x24, 0x58, 0x0F, 0xB6, 0x8C, 0x24, 0xBC, 0x00, 0x00, 0x00,
    0x32, 0x4C, 0x28, 0x24, 0x88, 0x4C, 0x24, 0x57] ++ bytes_l107315_6

theorem code_l107315_5 : ∀ x ∈ codeRange 0x10755f bytes_l107315_5, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x755f 104 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l107315_6

def b_l107315_4 : Block Op Label signature Reg.count 186 :=
  .letOp (n := 186) (.exec 0x1074f3 (StorePre 0x1074f3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x64)) s (0x1074f3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1074f3 4 1 (.sib 4 none 0 (.d8 0x64))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[184, 4]
    (.letOp (n := 187) (.out 0x1074f7 (movzxR32M8Effect 0x1074f7 8 1 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 188) (.exec 0x1074f7 (LoadPre 0x1074f7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x1074f7 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1074f7 8 1 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 189) (.out 0x1074ff (xorR8M8Effect 0x1074ff 4 1 (.sib 0 (some 5) 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[187, 91, 5]
    (.letOp (n := 190) (.exec 0x1074ff (LoadPre 0x1074ff (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x18)) s (0x1074ff + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1074ff 4 1 (.sib 0 (some 5) 0 (.d8 0x18))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[187, 91, 5]
    (.letOp (n := 191) (.exec 0x107503 (StorePre 0x107503 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x63)) s (0x107503 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x107503 4 1 (.sib 4 none 0 (.d8 0x63))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[189, 4]
    (.letOp (n := 192) (.out 0x107507 (movzxR32M8Effect 0x107507 8 1 (.sib 4 none 0 (.d32 0xb1))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 193) (.exec 0x107507 (LoadPre 0x107507 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb1)) s (0x107507 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107507 8 1 (.sib 4 none 0 (.d32 0xb1))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 194) (.out 0x10750f (xorR8M8Effect 0x10750f 4 1 (.sib 0 (some 5) 0 (.d8 0x19))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[192, 91, 5]
    (.letOp (n := 195) (.exec 0x10750f (LoadPre 0x10750f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x19)) s (0x10750f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10750f 4 1 (.sib 0 (some 5) 0 (.d8 0x19))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[192, 91, 5]
    (.letOp (n := 196) (.exec 0x107513 (StorePre 0x107513 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x62)) s (0x107513 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x107513 4 1 (.sib 4 none 0 (.d8 0x62))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[194, 4]
    (.letOp (n := 197) (.out 0x107517 (movzxR32M8Effect 0x107517 8 1 (.sib 4 none 0 (.d32 0xb2))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 198) (.exec 0x107517 (LoadPre 0x107517 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb2)) s (0x107517 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107517 8 1 (.sib 4 none 0 (.d32 0xb2))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 199) (.out 0x10751f (xorR8M8Effect 0x10751f 4 1 (.sib 0 (some 5) 0 (.d8 0x1a))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[197, 91, 5]
    (.letOp (n := 200) (.exec 0x10751f (LoadPre 0x10751f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x1a)) s (0x10751f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10751f 4 1 (.sib 0 (some 5) 0 (.d8 0x1a))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[197, 91, 5]
    (.letOp (n := 201) (.exec 0x107523 (StorePre 0x107523 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x61)) s (0x107523 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x107523 4 1 (.sib 4 none 0 (.d8 0x61))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[199, 4]
    (.letOp (n := 202) (.out 0x107527 (movzxR32M8Effect 0x107527 8 1 (.sib 4 none 0 (.d32 0xb3))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 203) (.exec 0x107527 (LoadPre 0x107527 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb3)) s (0x107527 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107527 8 1 (.sib 4 none 0 (.d32 0xb3))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 204) (.out 0x10752f (xorR8M8Effect 0x10752f 4 1 (.sib 0 (some 5) 0 (.d8 0x1b))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[202, 91, 5]
    (.letOp (n := 205) (.exec 0x10752f (LoadPre 0x10752f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x1b)) s (0x10752f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10752f 4 1 (.sib 0 (some 5) 0 (.d8 0x1b))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[202, 91, 5]
    (.letOp (n := 206) (.exec 0x107533 (StorePre 0x107533 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x107533 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x107533 4 1 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[204, 4]
    (.letOp (n := 207) (.out 0x107537 (movzxR32M8Effect 0x107537 8 1 (.sib 4 none 0 (.d32 0xb4))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 208) (.exec 0x107537 (LoadPre 0x107537 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb4)) s (0x107537 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107537 8 1 (.sib 4 none 0 (.d32 0xb4))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 209) (.out 0x10753f (xorR8M8Effect 0x10753f 4 1 (.sib 0 (some 5) 0 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[207, 91, 5]
    (.letOp (n := 210) (.exec 0x10753f (LoadPre 0x10753f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x1c)) s (0x10753f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10753f 4 1 (.sib 0 (some 5) 0 (.d8 0x1c))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[207, 91, 5]
    (.letOp (n := 211) (.exec 0x107543 (StorePre 0x107543 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5f)) s (0x107543 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x107543 4 1 (.sib 4 none 0 (.d8 0x5f))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[209, 4]
    (.letOp (n := 212) (.out 0x107547 (movzxR32M8Effect 0x107547 8 1 (.sib 4 none 0 (.d32 0xb5))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 213) (.exec 0x107547 (LoadPre 0x107547 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb5)) s (0x107547 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107547 8 1 (.sib 4 none 0 (.d32 0xb5))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 214) (.out 0x10754f (xorR8M8Effect 0x10754f 4 1 (.sib 0 (some 5) 0 (.d8 0x1d))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[212, 91, 5]
    (.letOp (n := 215) (.exec 0x10754f (LoadPre 0x10754f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x1d)) s (0x10754f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10754f 4 1 (.sib 0 (some 5) 0 (.d8 0x1d))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[212, 91, 5]
    (.letOp (n := 216) (.exec 0x107553 (StorePre 0x107553 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5e)) s (0x107553 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x107553 4 1 (.sib 4 none 0 (.d8 0x5e))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[214, 4]
    (.letOp (n := 217) (.out 0x107557 (movzxR32M8Effect 0x107557 8 1 (.sib 4 none 0 (.d32 0xb6))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 218) (.exec 0x107557 (LoadPre 0x107557 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb6)) s (0x107557 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107557 8 1 (.sib 4 none 0 (.d32 0xb6))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l107315_5)))))))))))))))))))))))))))))))))

def bytes_l107315_4 : List UInt8 :=
  [0x88, 0x4C, 0x24, 0x64, 0x0F, 0xB6, 0x8C, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x32, 0x4C, 0x28, 0x18,
    0x88, 0x4C, 0x24, 0x63, 0x0F, 0xB6, 0x8C, 0x24, 0xB1, 0x00, 0x00, 0x00, 0x32, 0x4C, 0x28, 0x19,
    0x88, 0x4C, 0x24, 0x62, 0x0F, 0xB6, 0x8C, 0x24, 0xB2, 0x00, 0x00, 0x00, 0x32, 0x4C, 0x28, 0x1A,
    0x88, 0x4C, 0x24, 0x61, 0x0F, 0xB6, 0x8C, 0x24, 0xB3, 0x00, 0x00, 0x00, 0x32, 0x4C, 0x28, 0x1B,
    0x88, 0x4C, 0x24, 0x60, 0x0F, 0xB6, 0x8C, 0x24, 0xB4, 0x00, 0x00, 0x00, 0x32, 0x4C, 0x28, 0x1C,
    0x88, 0x4C, 0x24, 0x5F, 0x0F, 0xB6, 0x8C, 0x24, 0xB5, 0x00, 0x00, 0x00, 0x32, 0x4C, 0x28, 0x1D,
    0x88, 0x4C, 0x24, 0x5E, 0x0F, 0xB6, 0x8C, 0x24, 0xB6, 0x00, 0x00, 0x00] ++ bytes_l107315_5

theorem code_l107315_4 : ∀ x ∈ codeRange 0x1074f3 bytes_l107315_4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x74f3 108 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l107315_5

def b_l107315_3 : Block Op Label signature Reg.count 152 :=
  .letOp (n := 152) (.out 0x107487 (movzxR32M8Effect 0x107487 8 1 (.sib 4 none 0 (.d32 0xa9))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 153) (.exec 0x107487 (LoadPre 0x107487 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa9)) s (0x107487 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107487 8 1 (.sib 4 none 0 (.d32 0xa9))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 154) (.out 0x10748f (xorR8M8Effect 0x10748f 4 1 (.sib 0 (some 5) 0 (.d8 0x11))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[152, 91, 5]
    (.letOp (n := 155) (.exec 0x10748f (LoadPre 0x10748f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x11)) s (0x10748f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10748f 4 1 (.sib 0 (some 5) 0 (.d8 0x11))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[152, 91, 5]
    (.letOp (n := 156) (.exec 0x107493 (StorePre 0x107493 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6a)) s (0x107493 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x107493 4 1 (.sib 4 none 0 (.d8 0x6a))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[154, 4]
    (.letOp (n := 157) (.out 0x107497 (movzxR32M8Effect 0x107497 8 1 (.sib 4 none 0 (.d32 0xaa))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 158) (.exec 0x107497 (LoadPre 0x107497 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xaa)) s (0x107497 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107497 8 1 (.sib 4 none 0 (.d32 0xaa))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 159) (.out 0x10749f (xorR8M8Effect 0x10749f 4 1 (.sib 0 (some 5) 0 (.d8 0x12))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[157, 91, 5]
    (.letOp (n := 160) (.exec 0x10749f (LoadPre 0x10749f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x12)) s (0x10749f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10749f 4 1 (.sib 0 (some 5) 0 (.d8 0x12))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[157, 91, 5]
    (.letOp (n := 161) (.exec 0x1074a3 (StorePre 0x1074a3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x69)) s (0x1074a3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1074a3 4 1 (.sib 4 none 0 (.d8 0x69))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[159, 4]
    (.letOp (n := 162) (.out 0x1074a7 (movzxR32M8Effect 0x1074a7 8 1 (.sib 4 none 0 (.d32 0xab))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 163) (.exec 0x1074a7 (LoadPre 0x1074a7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xab)) s (0x1074a7 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1074a7 8 1 (.sib 4 none 0 (.d32 0xab))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 164) (.out 0x1074af (xorR8M8Effect 0x1074af 4 1 (.sib 0 (some 5) 0 (.d8 0x13))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[162, 91, 5]
    (.letOp (n := 165) (.exec 0x1074af (LoadPre 0x1074af (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x13)) s (0x1074af + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1074af 4 1 (.sib 0 (some 5) 0 (.d8 0x13))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[162, 91, 5]
    (.letOp (n := 166) (.exec 0x1074b3 (StorePre 0x1074b3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x1074b3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1074b3 4 1 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[164, 4]
    (.letOp (n := 167) (.out 0x1074b7 (movzxR32M8Effect 0x1074b7 8 1 (.sib 4 none 0 (.d32 0xac))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 168) (.exec 0x1074b7 (LoadPre 0x1074b7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xac)) s (0x1074b7 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1074b7 8 1 (.sib 4 none 0 (.d32 0xac))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 169) (.out 0x1074bf (xorR8M8Effect 0x1074bf 4 1 (.sib 0 (some 5) 0 (.d8 0x14))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[167, 91, 5]
    (.letOp (n := 170) (.exec 0x1074bf (LoadPre 0x1074bf (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x14)) s (0x1074bf + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1074bf 4 1 (.sib 0 (some 5) 0 (.d8 0x14))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[167, 91, 5]
    (.letOp (n := 171) (.exec 0x1074c3 (StorePre 0x1074c3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x67)) s (0x1074c3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1074c3 4 1 (.sib 4 none 0 (.d8 0x67))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[169, 4]
    (.letOp (n := 172) (.out 0x1074c7 (movzxR32M8Effect 0x1074c7 8 1 (.sib 4 none 0 (.d32 0xad))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 173) (.exec 0x1074c7 (LoadPre 0x1074c7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xad)) s (0x1074c7 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1074c7 8 1 (.sib 4 none 0 (.d32 0xad))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 174) (.out 0x1074cf (xorR8M8Effect 0x1074cf 4 1 (.sib 0 (some 5) 0 (.d8 0x15))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[172, 91, 5]
    (.letOp (n := 175) (.exec 0x1074cf (LoadPre 0x1074cf (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x15)) s (0x1074cf + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1074cf 4 1 (.sib 0 (some 5) 0 (.d8 0x15))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[172, 91, 5]
    (.letOp (n := 176) (.exec 0x1074d3 (StorePre 0x1074d3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x66)) s (0x1074d3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1074d3 4 1 (.sib 4 none 0 (.d8 0x66))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[174, 4]
    (.letOp (n := 177) (.out 0x1074d7 (movzxR32M8Effect 0x1074d7 8 1 (.sib 4 none 0 (.d32 0xae))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 178) (.exec 0x1074d7 (LoadPre 0x1074d7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xae)) s (0x1074d7 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1074d7 8 1 (.sib 4 none 0 (.d32 0xae))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 179) (.out 0x1074df (xorR8M8Effect 0x1074df 4 1 (.sib 0 (some 5) 0 (.d8 0x16))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[177, 91, 5]
    (.letOp (n := 180) (.exec 0x1074df (LoadPre 0x1074df (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x16)) s (0x1074df + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1074df 4 1 (.sib 0 (some 5) 0 (.d8 0x16))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[177, 91, 5]
    (.letOp (n := 181) (.exec 0x1074e3 (StorePre 0x1074e3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x65)) s (0x1074e3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1074e3 4 1 (.sib 4 none 0 (.d8 0x65))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[179, 4]
    (.letOp (n := 182) (.out 0x1074e7 (movzxR32M8Effect 0x1074e7 8 1 (.sib 4 none 0 (.d32 0xaf))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 183) (.exec 0x1074e7 (LoadPre 0x1074e7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xaf)) s (0x1074e7 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1074e7 8 1 (.sib 4 none 0 (.d32 0xaf))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 184) (.out 0x1074ef (xorR8M8Effect 0x1074ef 4 1 (.sib 0 (some 5) 0 (.d8 0x17))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[182, 91, 5]
    (.letOp (n := 185) (.exec 0x1074ef (LoadPre 0x1074ef (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x17)) s (0x1074ef + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1074ef 4 1 (.sib 0 (some 5) 0 (.d8 0x17))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[182, 91, 5]
    (b_l107315_4))))))))))))))))))))))))))))))))))

def bytes_l107315_3 : List UInt8 :=
  [0x0F, 0xB6, 0x8C, 0x24, 0xA9, 0x00, 0x00, 0x00, 0x32, 0x4C, 0x28, 0x11, 0x88, 0x4C, 0x24, 0x6A,
    0x0F, 0xB6, 0x8C, 0x24, 0xAA, 0x00, 0x00, 0x00, 0x32, 0x4C, 0x28, 0x12, 0x88, 0x4C, 0x24, 0x69,
    0x0F, 0xB6, 0x8C, 0x24, 0xAB, 0x00, 0x00, 0x00, 0x32, 0x4C, 0x28, 0x13, 0x88, 0x4C, 0x24, 0x68,
    0x0F, 0xB6, 0x8C, 0x24, 0xAC, 0x00, 0x00, 0x00, 0x32, 0x4C, 0x28, 0x14, 0x88, 0x4C, 0x24, 0x67,
    0x0F, 0xB6, 0x8C, 0x24, 0xAD, 0x00, 0x00, 0x00, 0x32, 0x4C, 0x28, 0x15, 0x88, 0x4C, 0x24, 0x66,
    0x0F, 0xB6, 0x8C, 0x24, 0xAE, 0x00, 0x00, 0x00, 0x32, 0x4C, 0x28, 0x16, 0x88, 0x4C, 0x24, 0x65,
    0x0F, 0xB6, 0x8C, 0x24, 0xAF, 0x00, 0x00, 0x00, 0x32, 0x4C, 0x28, 0x17] ++ bytes_l107315_4

theorem code_l107315_3 : ∀ x ∈ codeRange 0x107487 bytes_l107315_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x7487 108 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l107315_4

def b_l107315_2 : Block Op Label signature Reg.count 120 :=
  .letOp (n := 120) (.out 0x107419 (xorR8M8Effect 0x107419 5 14 (.sib 0 (some 5) 0 (.d8 0x9))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 0, .gpr 5] []) (.reg (.gpr 14))) #v[71, 91, 5]
    (.letOp (n := 121) (.exec 0x107419 (LoadPre 0x107419 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x9)) s (0x107419 + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x107419 5 14 (.sib 0 (some 5) 0 (.d8 0x9))) (Reg.operands [.gpr 14, .gpr 0, .gpr 5] [])) #v[71, 91, 5]
    (.letOp (n := 122) (.exec 0x10741e (StorePre 0x10741e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6e)) s (0x10741e + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x10741e 5 14 (.sib 4 none 0 (.d8 0x6e))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[120, 4]
    (.letOp (n := 123) (.out 0x107423 (xorR8M8Effect 0x107423 5 15 (.sib 0 (some 5) 0 (.d8 0xa))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 0, .gpr 5] []) (.reg (.gpr 15))) #v[73, 91, 5]
    (.letOp (n := 124) (.exec 0x107423 (LoadPre 0x107423 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0xa)) s (0x107423 + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x107423 5 15 (.sib 0 (some 5) 0 (.d8 0xa))) (Reg.operands [.gpr 15, .gpr 0, .gpr 5] [])) #v[73, 91, 5]
    (.letOp (n := 125) (.exec 0x107428 (StorePre 0x107428 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6d)) s (0x107428 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x107428 5 15 (.sib 4 none 0 (.d8 0x6d))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[123, 4]
    (.letOp (n := 126) (.out 0x10742d (xorR8M8Effect 0x10742d 5 12 (.sib 0 (some 5) 0 (.d8 0xb))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 0, .gpr 5] []) (.reg (.gpr 12))) #v[75, 91, 5]
    (.letOp (n := 127) (.exec 0x10742d (LoadPre 0x10742d (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0xb)) s (0x10742d + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x10742d 5 12 (.sib 0 (some 5) 0 (.d8 0xb))) (Reg.operands [.gpr 12, .gpr 0, .gpr 5] [])) #v[75, 91, 5]
    (.letOp (n := 128) (.exec 0x107432 (StorePre 0x107432 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6c)) s (0x107432 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x107432 5 12 (.sib 4 none 0 (.d8 0x6c))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[126, 4]
    (.letOp (n := 129) (.out 0x107437 (xorR8M8Effect 0x107437 5 13 (.sib 0 (some 5) 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 0, .gpr 5] []) (.reg (.gpr 13))) #v[77, 91, 5]
    (.letOp (n := 130) (.exec 0x107437 (LoadPre 0x107437 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0xc)) s (0x107437 + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x107437 5 13 (.sib 0 (some 5) 0 (.d8 0xc))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[77, 91, 5]
    (.letOp (n := 131) (.exec 0x10743c (StorePre 0x10743c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6b)) s (0x10743c + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x10743c 5 13 (.sib 4 none 0 (.d8 0x6b))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[129, 4]
    (.letOp (n := 132) (.out 0x107441 (movzxR32M8Effect 0x107441 8 1 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 133) (.exec 0x107441 (LoadPre 0x107441 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x107441 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107441 8 1 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 134) (.out 0x107449 (xorR8M8Effect 0x107449 4 1 (.sib 0 (some 5) 0 (.d8 0xd))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[132, 91, 5]
    (.letOp (n := 135) (.exec 0x107449 (LoadPre 0x107449 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0xd)) s (0x107449 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x107449 4 1 (.sib 0 (some 5) 0 (.d8 0xd))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[132, 91, 5]
    (.letOp (n := 136) (.exec 0x10744d (StorePre 0x10744d 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10744d + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x10744d 7 1 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[134, 4]
    (.letOp (n := 137) (.out 0x107454 (movzxR32M8Effect 0x107454 8 1 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 138) (.exec 0x107454 (LoadPre 0x107454 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x107454 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107454 8 1 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 139) (.out 0x10745c (xorR8M8Effect 0x10745c 4 1 (.sib 0 (some 5) 0 (.d8 0xe))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[137, 91, 5]
    (.letOp (n := 140) (.exec 0x10745c (LoadPre 0x10745c (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0xe)) s (0x10745c + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10745c 4 1 (.sib 0 (some 5) 0 (.d8 0xe))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[137, 91, 5]
    (.letOp (n := 141) (.exec 0x107460 (StorePre 0x107460 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x107460 + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x107460 7 1 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[139, 4]
    (.letOp (n := 142) (.out 0x107467 (movzxR32M8Effect 0x107467 5 1 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 143) (.exec 0x107467 (LoadPre 0x107467 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x107467 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x107467 5 1 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 144) (.out 0x10746c (xorR8M8Effect 0x10746c 4 1 (.sib 0 (some 5) 0 (.d8 0xf))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[142, 91, 5]
    (.letOp (n := 145) (.exec 0x10746c (LoadPre 0x10746c (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0xf)) s (0x10746c + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10746c 4 1 (.sib 0 (some 5) 0 (.d8 0xf))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[142, 91, 5]
    (.letOp (n := 146) (.exec 0x107470 (StorePre 0x107470 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x107470 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x107470 4 1 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[144, 4]
    (.letOp (n := 147) (.out 0x107474 (movzxR32M8Effect 0x107474 8 1 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 148) (.exec 0x107474 (LoadPre 0x107474 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x107474 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107474 8 1 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 149) (.out 0x10747c (xorR8M8Effect 0x10747c 4 1 (.sib 0 (some 5) 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[147, 91, 5]
    (.letOp (n := 150) (.exec 0x10747c (LoadPre 0x10747c (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x10)) s (0x10747c + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10747c 4 1 (.sib 0 (some 5) 0 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[147, 91, 5]
    (.letOp (n := 151) (.exec 0x107480 (StorePre 0x107480 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x107480 + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x107480 7 1 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[149, 4]
    (b_l107315_3))))))))))))))))))))))))))))))))

def bytes_l107315_2 : List UInt8 :=
  [0x44, 0x32, 0x74, 0x28, 0x09, 0x44, 0x88, 0x74, 0x24, 0x6E, 0x44, 0x32, 0x7C, 0x28, 0x0A, 0x44,
    0x88, 0x7C, 0x24, 0x6D, 0x44, 0x32, 0x64, 0x28, 0x0B, 0x44, 0x88, 0x64, 0x24, 0x6C, 0x44, 0x32,
    0x6C, 0x28, 0x0C, 0x44, 0x88, 0x6C, 0x24, 0x6B, 0x0F, 0xB6, 0x8C, 0x24, 0x88, 0x00, 0x00, 0x00,
    0x32, 0x4C, 0x28, 0x0D, 0x88, 0x8C, 0x24, 0x88, 0x00, 0x00, 0x00, 0x0F, 0xB6, 0x8C, 0x24, 0x80,
    0x00, 0x00, 0x00, 0x32, 0x4C, 0x28, 0x0E, 0x88, 0x8C, 0x24, 0x80, 0x00, 0x00, 0x00, 0x0F, 0xB6,
    0x4C, 0x24, 0x78, 0x32, 0x4C, 0x28, 0x0F, 0x88, 0x4C, 0x24, 0x78, 0x0F, 0xB6, 0x8C, 0x24, 0x90,
    0x00, 0x00, 0x00, 0x32, 0x4C, 0x28, 0x10, 0x88, 0x8C, 0x24, 0x90, 0x00, 0x00, 0x00] ++ bytes_l107315_3

theorem code_l107315_2 : ∀ x ∈ codeRange 0x107419 bytes_l107315_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x7419 110 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l107315_3

def b_l107315_1 : Block Op Label signature Reg.count 90 :=
  .letOp (n := 90) (.exec 0x1073b7 (StorePre 0x1073b7 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x1073b7 + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x1073b7 7 0 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[88, 4]
    (.letOp (n := 91) (.out 0x1073be (movR64M64Effect 0x1073be 0 (.sib 4 none 0 (.d32 0xf0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 92) (.exec 0x1073be (LoadPre 0x1073be (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x1073be + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1073be 0 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 93) (.out 0x1073c6 (xorR8M8Effect 0x1073c6 3 1 (.sib 0 (some 5) 0 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[53, 91, 5]
    (.letOp (n := 94) (.exec 0x1073c6 (LoadPre 0x1073c6 (fun s => AddrMode.addr (.sib 0 (some 5) 0 .none) s (0x1073c6 + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x1073c6 3 1 (.sib 0 (some 5) 0 .none)) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[53, 91, 5]
    (.letOp (n := 95) (.exec 0x1073c9 (StorePre 0x1073c9 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x77)) s (0x1073c9 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1073c9 4 1 (.sib 4 none 0 (.d8 0x77))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[93, 4]
    (.letOp (n := 96) (.out 0x1073cd (xorR8M8Effect 0x1073cd 4 2 (.sib 0 (some 5) 0 (.d8 0x1))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0, .gpr 5] []) (.reg (.gpr 2))) #v[55, 91, 5]
    (.letOp (n := 97) (.exec 0x1073cd (LoadPre 0x1073cd (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x1)) s (0x1073cd + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1073cd 4 2 (.sib 0 (some 5) 0 (.d8 0x1))) (Reg.operands [.gpr 2, .gpr 0, .gpr 5] [])) #v[55, 91, 5]
    (.letOp (n := 98) (.exec 0x1073d1 (StorePre 0x1073d1 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x76)) s (0x1073d1 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1073d1 4 2 (.sib 4 none 0 (.d8 0x76))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[96, 4]
    (.letOp (n := 99) (.out 0x1073d5 (xorR8M8Effect 0x1073d5 5 6 (.sib 0 (some 5) 0 (.d8 0x2))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0, .gpr 5] []) (.reg (.gpr 6))) #v[57, 91, 5]
    (.letOp (n := 100) (.exec 0x1073d5 (LoadPre 0x1073d5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x2)) s (0x1073d5 + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x1073d5 5 6 (.sib 0 (some 5) 0 (.d8 0x2))) (Reg.operands [.gpr 6, .gpr 0, .gpr 5] [])) #v[57, 91, 5]
    (.letOp (n := 101) (.exec 0x1073da (StorePre 0x1073da 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x75)) s (0x1073da + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1073da 5 6 (.sib 4 none 0 (.d8 0x75))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[99, 4]
    (.letOp (n := 102) (.out 0x1073df (xorR8M8Effect 0x1073df 5 7 (.sib 0 (some 5) 0 (.d8 0x3))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0, .gpr 5] []) (.reg (.gpr 7))) #v[59, 91, 5]
    (.letOp (n := 103) (.exec 0x1073df (LoadPre 0x1073df (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x3)) s (0x1073df + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x1073df 5 7 (.sib 0 (some 5) 0 (.d8 0x3))) (Reg.operands [.gpr 7, .gpr 0, .gpr 5] [])) #v[59, 91, 5]
    (.letOp (n := 104) (.exec 0x1073e4 (StorePre 0x1073e4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x74)) s (0x1073e4 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1073e4 5 7 (.sib 4 none 0 (.d8 0x74))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[102, 4]
    (.letOp (n := 105) (.out 0x1073e9 (xorR8M8Effect 0x1073e9 5 8 (.sib 0 (some 5) 0 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0, .gpr 5] []) (.reg (.gpr 8))) #v[61, 91, 5]
    (.letOp (n := 106) (.exec 0x1073e9 (LoadPre 0x1073e9 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x4)) s (0x1073e9 + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x1073e9 5 8 (.sib 0 (some 5) 0 (.d8 0x4))) (Reg.operands [.gpr 8, .gpr 0, .gpr 5] [])) #v[61, 91, 5]
    (.letOp (n := 107) (.exec 0x1073ee (StorePre 0x1073ee 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x73)) s (0x1073ee + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1073ee 5 8 (.sib 4 none 0 (.d8 0x73))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[105, 4]
    (.letOp (n := 108) (.out 0x1073f3 (xorR8M8Effect 0x1073f3 5 9 (.sib 0 (some 5) 0 (.d8 0x5))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0, .gpr 5] []) (.reg (.gpr 9))) #v[63, 91, 5]
    (.letOp (n := 109) (.exec 0x1073f3 (LoadPre 0x1073f3 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x5)) s (0x1073f3 + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x1073f3 5 9 (.sib 0 (some 5) 0 (.d8 0x5))) (Reg.operands [.gpr 9, .gpr 0, .gpr 5] [])) #v[63, 91, 5]
    (.letOp (n := 110) (.exec 0x1073f8 (StorePre 0x1073f8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x72)) s (0x1073f8 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1073f8 5 9 (.sib 4 none 0 (.d8 0x72))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[108, 4]
    (.letOp (n := 111) (.out 0x1073fd (xorR8M8Effect 0x1073fd 5 10 (.sib 0 (some 5) 0 (.d8 0x6))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0, .gpr 5] []) (.reg (.gpr 10))) #v[65, 91, 5]
    (.letOp (n := 112) (.exec 0x1073fd (LoadPre 0x1073fd (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x6)) s (0x1073fd + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x1073fd 5 10 (.sib 0 (some 5) 0 (.d8 0x6))) (Reg.operands [.gpr 10, .gpr 0, .gpr 5] [])) #v[65, 91, 5]
    (.letOp (n := 113) (.exec 0x107402 (StorePre 0x107402 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x71)) s (0x107402 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x107402 5 10 (.sib 4 none 0 (.d8 0x71))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[111, 4]
    (.letOp (n := 114) (.out 0x107407 (xorR8M8Effect 0x107407 5 11 (.sib 0 (some 5) 0 (.d8 0x7))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0, .gpr 5] []) (.reg (.gpr 11))) #v[67, 91, 5]
    (.letOp (n := 115) (.exec 0x107407 (LoadPre 0x107407 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x7)) s (0x107407 + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x107407 5 11 (.sib 0 (some 5) 0 (.d8 0x7))) (Reg.operands [.gpr 11, .gpr 0, .gpr 5] [])) #v[67, 91, 5]
    (.letOp (n := 116) (.exec 0x10740c (StorePre 0x10740c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x10740c + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x10740c 5 11 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[114, 4]
    (.letOp (n := 117) (.out 0x107411 (xorR8M8Effect 0x107411 4 3 (.sib 0 (some 5) 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0, .gpr 5] []) (.reg (.gpr 3))) #v[69, 91, 5]
    (.letOp (n := 118) (.exec 0x107411 (LoadPre 0x107411 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x8)) s (0x107411 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x107411 4 3 (.sib 0 (some 5) 0 (.d8 0x8))) (Reg.operands [.gpr 3, .gpr 0, .gpr 5] [])) #v[69, 91, 5]
    (.letOp (n := 119) (.exec 0x107415 (StorePre 0x107415 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6f)) s (0x107415 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x107415 4 3 (.sib 4 none 0 (.d8 0x6f))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[117, 4]
    (b_l107315_2))))))))))))))))))))))))))))))

def bytes_l107315_1 : List UInt8 :=
  [0x88, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x84, 0x24, 0xF0, 0x00, 0x00, 0x00, 0x32,
    0x0C, 0x28, 0x88, 0x4C, 0x24, 0x77, 0x32, 0x54, 0x28, 0x01, 0x88, 0x54, 0x24, 0x76, 0x40, 0x32,
    0x74, 0x28, 0x02, 0x40, 0x88, 0x74, 0x24, 0x75, 0x40, 0x32, 0x7C, 0x28, 0x03, 0x40, 0x88, 0x7C,
    0x24, 0x74, 0x44, 0x32, 0x44, 0x28, 0x04, 0x44, 0x88, 0x44, 0x24, 0x73, 0x44, 0x32, 0x4C, 0x28,
    0x05, 0x44, 0x88, 0x4C, 0x24, 0x72, 0x44, 0x32, 0x54, 0x28, 0x06, 0x44, 0x88, 0x54, 0x24, 0x71,
    0x44, 0x32, 0x5C, 0x28, 0x07, 0x44, 0x88, 0x5C, 0x24, 0x70, 0x32, 0x5C, 0x28, 0x08, 0x88, 0x5C,
    0x24, 0x6F] ++ bytes_l107315_2

theorem code_l107315_1 : ∀ x ∈ codeRange 0x1073b7 bytes_l107315_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x73b7 98 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l107315_2

def b_l107315 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x107315 (movzxR32M8Effect 0x107315 8 1 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x107315 (LoadPre 0x107315 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x107315 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107315 8 1 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10731d (movzxR32M8Effect 0x10731d 8 2 (.sib 4 none 0 (.d32 0x99))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 56) (.exec 0x10731d (LoadPre 0x10731d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x99)) s (0x10731d + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x10731d 8 2 (.sib 4 none 0 (.d32 0x99))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x107325 (movzxR32M8Effect 0x107325 8 6 (.sib 4 none 0 (.d32 0x9a))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 58) (.exec 0x107325 (LoadPre 0x107325 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9a)) s (0x107325 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107325 8 6 (.sib 4 none 0 (.d32 0x9a))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x10732d (movzxR32M8Effect 0x10732d 8 7 (.sib 4 none 0 (.d32 0x9b))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 60) (.exec 0x10732d (LoadPre 0x10732d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9b)) s (0x10732d + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x10732d 8 7 (.sib 4 none 0 (.d32 0x9b))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x107335 (movzxR32M8Effect 0x107335 9 8 (.sib 4 none 0 (.d32 0x9c))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 62) (.exec 0x107335 (LoadPre 0x107335 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9c)) s (0x107335 + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x107335 9 8 (.sib 4 none 0 (.d32 0x9c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x10733e (movzxR32M8Effect 0x10733e 9 9 (.sib 4 none 0 (.d32 0x9d))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 64) (.exec 0x10733e (LoadPre 0x10733e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9d)) s (0x10733e + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x10733e 9 9 (.sib 4 none 0 (.d32 0x9d))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x107347 (movzxR32M8Effect 0x107347 9 10 (.sib 4 none 0 (.d32 0x9e))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 66) (.exec 0x107347 (LoadPre 0x107347 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9e)) s (0x107347 + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x107347 9 10 (.sib 4 none 0 (.d32 0x9e))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x107350 (movzxR32M8Effect 0x107350 9 11 (.sib 4 none 0 (.d32 0x9f))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 68) (.exec 0x107350 (LoadPre 0x107350 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9f)) s (0x107350 + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x107350 9 11 (.sib 4 none 0 (.d32 0x9f))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.out 0x107359 (movzxR32M8Effect 0x107359 8 3 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 70) (.exec 0x107359 (LoadPre 0x107359 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x107359 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107359 8 3 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.out 0x107361 (movzxR32M8Effect 0x107361 9 14 (.sib 4 none 0 (.d32 0xa1))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 72) (.exec 0x107361 (LoadPre 0x107361 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa1)) s (0x107361 + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x107361 9 14 (.sib 4 none 0 (.d32 0xa1))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.out 0x10736a (movzxR32M8Effect 0x10736a 9 15 (.sib 4 none 0 (.d32 0xa2))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 74) (.exec 0x10736a (LoadPre 0x10736a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa2)) s (0x10736a + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x10736a 9 15 (.sib 4 none 0 (.d32 0xa2))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.out 0x107373 (movzxR32M8Effect 0x107373 9 12 (.sib 4 none 0 (.d32 0xa3))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 76) (.exec 0x107373 (LoadPre 0x107373 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa3)) s (0x107373 + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x107373 9 12 (.sib 4 none 0 (.d32 0xa3))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 77) (.out 0x10737c (movzxR32M8Effect 0x10737c 9 13 (.sib 4 none 0 (.d32 0xa4))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 78) (.exec 0x10737c (LoadPre 0x10737c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa4)) s (0x10737c + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x10737c 9 13 (.sib 4 none 0 (.d32 0xa4))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.out 0x107385 (movzxR32M8Effect 0x107385 8 0 (.sib 4 none 0 (.d32 0xa5))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 80) (.exec 0x107385 (LoadPre 0x107385 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa5)) s (0x107385 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107385 8 0 (.sib 4 none 0 (.d32 0xa5))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 81) (.exec 0x10738d (StorePre 0x10738d 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10738d + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x10738d 7 0 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[79, 4]
    (.letOp (n := 82) (.out 0x107394 (movzxR32M8Effect 0x107394 8 0 (.sib 4 none 0 (.d32 0xa6))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 83) (.exec 0x107394 (LoadPre 0x107394 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa6)) s (0x107394 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x107394 8 0 (.sib 4 none 0 (.d32 0xa6))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 84) (.exec 0x10739c (StorePre 0x10739c 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10739c + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x10739c 7 0 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[82, 4]
    (.letOp (n := 85) (.out 0x1073a3 (movzxR32M8Effect 0x1073a3 8 0 (.sib 4 none 0 (.d32 0xa7))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 86) (.exec 0x1073a3 (LoadPre 0x1073a3 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa7)) s (0x1073a3 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1073a3 8 0 (.sib 4 none 0 (.d32 0xa7))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 87) (.exec 0x1073ab (StorePre 0x1073ab 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1073ab + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1073ab 4 0 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[85, 4]
    (.letOp (n := 88) (.out 0x1073af (movzxR32M8Effect 0x1073af 8 0 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 89) (.exec 0x1073af (LoadPre 0x1073af (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x1073af + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1073af 8 0 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l107315_1)))))))))))))))))))))))))))))))))))))

def bytes_l107315 : List UInt8 :=
  [0x0F, 0xB6, 0x8C, 0x24, 0x98, 0x00, 0x00, 0x00, 0x0F, 0xB6, 0x94, 0x24, 0x99, 0x00, 0x00, 0x00,
    0x0F, 0xB6, 0xB4, 0x24, 0x9A, 0x00, 0x00, 0x00, 0x0F, 0xB6, 0xBC, 0x24, 0x9B, 0x00, 0x00, 0x00,
    0x44, 0x0F, 0xB6, 0x84, 0x24, 0x9C, 0x00, 0x00, 0x00, 0x44, 0x0F, 0xB6, 0x8C, 0x24, 0x9D, 0x00,
    0x00, 0x00, 0x44, 0x0F, 0xB6, 0x94, 0x24, 0x9E, 0x00, 0x00, 0x00, 0x44, 0x0F, 0xB6, 0x9C, 0x24,
    0x9F, 0x00, 0x00, 0x00, 0x0F, 0xB6, 0x9C, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x44, 0x0F, 0xB6, 0xB4,
    0x24, 0xA1, 0x00, 0x00, 0x00, 0x44, 0x0F, 0xB6, 0xBC, 0x24, 0xA2, 0x00, 0x00, 0x00, 0x44, 0x0F,
    0xB6, 0xA4, 0x24, 0xA3, 0x00, 0x00, 0x00, 0x44, 0x0F, 0xB6, 0xAC, 0x24, 0xA4, 0x00, 0x00, 0x00,
    0x0F, 0xB6, 0x84, 0x24, 0xA5, 0x00, 0x00, 0x00, 0x88, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, 0x0F,
    0xB6, 0x84, 0x24, 0xA6, 0x00, 0x00, 0x00, 0x88, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x0F, 0xB6,
    0x84, 0x24, 0xA7, 0x00, 0x00, 0x00, 0x88, 0x44, 0x24, 0x78, 0x0F, 0xB6, 0x84, 0x24, 0xA8, 0x00,
    0x00, 0x00] ++ bytes_l107315_1

theorem code_l107315 : ∀ x ∈ codeRange 0x107315 bytes_l107315, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x7315 162 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l107315_1

@[cfg_block] def b_l107a08_2 : Block Op Label signature Reg.count 108 :=
  .letOp (n := 108) (.out 0x107afb (movR32Imm32Effect 0x107afb 5 6 0x8) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 109) (.exec 0x107afb (fun s => s.RIP = 0x107afb) (movR32Imm32Effect 0x107afb 5 6 0x8) (Reg.operands [] [])) #v[]
    (.letOp (n := 110) (.out 0x107b00 (leaR64Effect 0x107b00 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 111) (.exec 0x107b00 (fun s => s.RIP = 0x107b00) (leaR64Effect 0x107b00 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 112) (.out 0x107b05 (leaR64Effect 0x107b05 2 (.sib 4 none 0 (.d32 0x100))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 113) (.exec 0x107b05 (fun s => s.RIP = 0x107b05) (leaR64Effect 0x107b05 2 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 114) (.out 0x107b0d (callEffect (fun _ => 0x10a690) 0x107b12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 115) (.exec 0x107b0d (PushPre 0x107b0d 5) (callEffect (fun _ => 0x10a690) 0x107b12) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 116) (.const ⟨64, 0x107b12⟩) #v[]
    (.terminate (.call ⟨.l10a690, RegMap.args [(0, 93), (1, 57), (2, 112), (3, 3), (4, 114), (5, 5), (6, 108), (7, 110), (8, 81), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 117⟩ { target := .l107b12, kept := #v[], arity := rfl, guard := some (Fin.last 116) }))))))))))

def bytes_l107a08_2 : List UInt8 :=
  [0xBE, 0x08, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x7C, 0x24, 0x08, 0x48, 0x8D, 0x94, 0x24, 0x00, 0x01,
    0x00, 0x00, 0xE8, 0x7E, 0x2B, 0x00, 0x00]

theorem code_l107a08_2 : ∀ x ∈ codeRange 0x107afb bytes_l107a08_2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x7afb 23 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l107a08_1 : Block Op Label signature Reg.count 84 :=
  .letOp (n := 84) (.exec 0x107a73 (StorePre 0x107a73 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x124)) s (0x107a73 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x107a73 2 (.sib 4 none 0 (.d32 0x124))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 85) (.exec 0x107a7a (StorePre 0x107a7a 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x107a7a + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x107a7a 6 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 86) (.exec 0x107a81 (StorePre 0x107a81 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x12c)) s (0x107a81 + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x107a81 8 (.sib 4 none 0 (.d32 0x12c))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[81, 4]
    (.letOp (n := 87) (.out 0x107a89 (addR32R32Effect 0x107a89 2 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[55, 53]
    (.letOp (n := 88) (.exec 0x107a89 (fun s => s.RIP = 0x107a89) (addR32R32Effect 0x107a89 2 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[55, 53]
    (.letOp (n := 89) (.out 0x107a8b (addR32Imm8Effect 0x107a8b 3 7 0x3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[87]
    (.letOp (n := 90) (.exec 0x107a8b (fun s => s.RIP = 0x107a8b) (addR32Imm8Effect 0x107a8b 3 7 0x3) (Reg.operands [.gpr 7] [])) #v[87]
    (.letOp (n := 91) (.out 0x107a8e (bswapR32Effect 0x107a8e 2 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[89]
    (.letOp (n := 92) (.exec 0x107a8e (fun s => s.RIP = 0x107a8e) (bswapR32Effect 0x107a8e 2 7) (Reg.operands [.gpr 7] [])) #v[89]
    (.letOp (n := 93) (.out 0x107a90 (addR32Imm8Effect 0x107a90 3 0 0x4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 94) (.exec 0x107a90 (fun s => s.RIP = 0x107a90) (addR32Imm8Effect 0x107a90 3 0 0x4) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 95) (.exec 0x107a93 (StorePre 0x107a93 4 (fun s => AddrMode.addr (.base 9 (.d8 0x10)) s (0x107a93 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x107a93 0 (.base 9 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 9] [])) #v[93, 9]
    (.letOp (n := 96) (.exec 0x107a97 (StorePre 0x107a97 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x107a97 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x107a97 1 (.sib 4 none 0 (.d32 0x130))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 97) (.exec 0x107a9e (StorePre 0x107a9e 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x134)) s (0x107a9e + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x107a9e 2 (.sib 4 none 0 (.d32 0x134))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 98) (.exec 0x107aa5 (StorePre 0x107aa5 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x138)) s (0x107aa5 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x107aa5 6 (.sib 4 none 0 (.d32 0x138))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 99) (.exec 0x107aac (StorePre 0x107aac 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x13c)) s (0x107aac + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x107aac 7 (.sib 4 none 0 (.d32 0x13c))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[91, 4]
    (.letOp (n := 100) (.exec 0x107ab3 (StorePre 0x107ab3 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x107ab3 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x107ab3 (.sib 4 none 0 (.d8 0x40)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 101) (.exec 0x107abc (StorePre 0x107abc 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x107abc + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x107abc (.sib 4 none 0 (.d8 0x38)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 102) (.exec 0x107ac5 (StorePre 0x107ac5 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x107ac5 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x107ac5 (.sib 4 none 0 (.d8 0x30)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 103) (.exec 0x107ace (StorePre 0x107ace 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x107ace + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x107ace (.sib 4 none 0 (.d8 0x28)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 104) (.exec 0x107ad7 (StorePre 0x107ad7 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x107ad7 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x107ad7 (.sib 4 none 0 (.d8 0x20)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 105) (.exec 0x107ae0 (StorePre 0x107ae0 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x107ae0 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x107ae0 (.sib 4 none 0 (.d8 0x18)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 106) (.exec 0x107ae9 (StorePre 0x107ae9 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x107ae9 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x107ae9 (.sib 4 none 0 (.d8 0x10)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 107) (.exec 0x107af2 (StorePre 0x107af2 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x107af2 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x107af2 (.sib 4 none 0 (.d8 0x8)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l107a08_2))))))))))))))))))))))))

def bytes_l107a08_1 : List UInt8 :=
  [0x89, 0x94, 0x24, 0x24, 0x01, 0x00, 0x00, 0x89, 0xB4, 0x24, 0x28, 0x01, 0x00, 0x00, 0x44, 0x89,
    0x84, 0x24, 0x2C, 0x01, 0x00, 0x00, 0x01, 0xC7, 0x83, 0xC7, 0x03, 0x0F, 0xCF, 0x83, 0xC0, 0x04,
    0x41, 0x89, 0x41, 0x10, 0x89, 0x8C, 0x24, 0x30, 0x01, 0x00, 0x00, 0x89, 0x94, 0x24, 0x34, 0x01,
    0x00, 0x00, 0x89, 0xB4, 0x24, 0x38, 0x01, 0x00, 0x00, 0x89, 0xBC, 0x24, 0x3C, 0x01, 0x00, 0x00,
    0x48, 0xC7, 0x44, 0x24, 0x40, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x38, 0x00, 0x00,
    0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x30, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x28,
    0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x20, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44,
    0x24, 0x18, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x10, 0x00, 0x00, 0x00, 0x00, 0x48,
    0xC7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00] ++ bytes_l107a08_2

theorem code_l107a08_1 : ∀ x ∈ codeRange 0x107a73 bytes_l107a08_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x7a73 136 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l107a08_2

@[cfg_block] def b_l107a08 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x107a08 (movR32M32Effect 0x107a08 0 (.base 9 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[9]
    (.letOp (n := 54) (.exec 0x107a08 (LoadPre 0x107a08 (fun s => AddrMode.addr (.base 9 (.d8 0x10)) s (0x107a08 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x107a08 0 (.base 9 (.d8 0x10))) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 55) (.out 0x107a0c (movR32M32Effect 0x107a0c 7 (.base 9 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 9] []) (.reg (.gpr 7))) #v[9]
    (.letOp (n := 56) (.exec 0x107a0c (LoadPre 0x107a0c (fun s => AddrMode.addr (.base 9 (.d8 0xc)) s (0x107a0c + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x107a0c 7 (.base 9 (.d8 0xc))) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 57) (.out 0x107a10 (movR32M32Effect 0x107a10 1 (.base 9 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 9] []) (.reg (.gpr 1))) #v[9]
    (.letOp (n := 58) (.exec 0x107a10 (LoadPre 0x107a10 (fun s => AddrMode.addr (.base 9 .none) s (0x107a10 + BitVec.ofNat 64 3)) 4) (movR32M32Effect 0x107a10 1 (.base 9 .none)) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 59) (.out 0x107a13 (movR32M32Effect 0x107a13 2 (.base 9 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9] []) (.reg (.gpr 2))) #v[9]
    (.letOp (n := 60) (.exec 0x107a13 (LoadPre 0x107a13 (fun s => AddrMode.addr (.base 9 (.d8 0x4)) s (0x107a13 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x107a13 2 (.base 9 (.d8 0x4))) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 61) (.out 0x107a17 (movR32M32Effect 0x107a17 6 (.base 9 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 9] []) (.reg (.gpr 6))) #v[9]
    (.letOp (n := 62) (.exec 0x107a17 (LoadPre 0x107a17 (fun s => AddrMode.addr (.base 9 (.d8 0x8)) s (0x107a17 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x107a17 6 (.base 9 (.d8 0x8))) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 63) (.out 0x107a1b (leaR32Effect 0x107a1b 4 8 (.sib 7 (some 0) 0 .none)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 7, .gpr 0] []) (.reg (.gpr 8))) #v[55, 53]
    (.letOp (n := 64) (.exec 0x107a1b (fun s => s.RIP = 0x107a1b) (leaR32Effect 0x107a1b 4 8 (.sib 7 (some 0) 0 .none)) (Reg.operands [.gpr 7, .gpr 0] [])) #v[55, 53]
    (.letOp (n := 65) (.out 0x107a1f (bswapR32Effect 0x107a1f 3 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[63]
    (.letOp (n := 66) (.exec 0x107a1f (fun s => s.RIP = 0x107a1f) (bswapR32Effect 0x107a1f 3 8) (Reg.operands [.gpr 8] [])) #v[63]
    (.letOp (n := 67) (.exec 0x107a22 (StorePre 0x107a22 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x107a22 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x107a22 1 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 68) (.exec 0x107a29 (StorePre 0x107a29 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x104)) s (0x107a29 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x107a29 2 (.sib 4 none 0 (.d32 0x104))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 69) (.exec 0x107a30 (StorePre 0x107a30 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x107a30 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x107a30 6 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 70) (.exec 0x107a37 (StorePre 0x107a37 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x10c)) s (0x107a37 + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x107a37 8 (.sib 4 none 0 (.d32 0x10c))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 71) (.out 0x107a3f (leaR32Effect 0x107a3f 5 8 (.sib 7 (some 0) 0 (.d8 0x1))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 7, .gpr 0] []) (.reg (.gpr 8))) #v[55, 53]
    (.letOp (n := 72) (.exec 0x107a3f (fun s => s.RIP = 0x107a3f) (leaR32Effect 0x107a3f 5 8 (.sib 7 (some 0) 0 (.d8 0x1))) (Reg.operands [.gpr 7, .gpr 0] [])) #v[55, 53]
    (.letOp (n := 73) (.out 0x107a44 (bswapR32Effect 0x107a44 3 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[71]
    (.letOp (n := 74) (.exec 0x107a44 (fun s => s.RIP = 0x107a44) (bswapR32Effect 0x107a44 3 8) (Reg.operands [.gpr 8] [])) #v[71]
    (.letOp (n := 75) (.exec 0x107a47 (StorePre 0x107a47 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x107a47 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x107a47 1 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 76) (.exec 0x107a4e (StorePre 0x107a4e 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x114)) s (0x107a4e + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x107a4e 2 (.sib 4 none 0 (.d32 0x114))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 77) (.exec 0x107a55 (StorePre 0x107a55 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x107a55 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x107a55 6 (.sib 4 none 0 (.d32 0x118))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 78) (.exec 0x107a5c (StorePre 0x107a5c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x11c)) s (0x107a5c + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x107a5c 8 (.sib 4 none 0 (.d32 0x11c))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[73, 4]
    (.letOp (n := 79) (.out 0x107a64 (leaR32Effect 0x107a64 5 8 (.sib 7 (some 0) 0 (.d8 0x2))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 7, .gpr 0] []) (.reg (.gpr 8))) #v[55, 53]
    (.letOp (n := 80) (.exec 0x107a64 (fun s => s.RIP = 0x107a64) (leaR32Effect 0x107a64 5 8 (.sib 7 (some 0) 0 (.d8 0x2))) (Reg.operands [.gpr 7, .gpr 0] [])) #v[55, 53]
    (.letOp (n := 81) (.out 0x107a69 (bswapR32Effect 0x107a69 3 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[79]
    (.letOp (n := 82) (.exec 0x107a69 (fun s => s.RIP = 0x107a69) (bswapR32Effect 0x107a69 3 8) (Reg.operands [.gpr 8] [])) #v[79]
    (.letOp (n := 83) (.exec 0x107a6c (StorePre 0x107a6c 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x107a6c + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x107a6c 1 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[57, 4]
    (b_l107a08_1)))))))))))))))))))))))))))))))

def bytes_l107a08 : List UInt8 :=
  [0x41, 0x8B, 0x41, 0x10, 0x41, 0x8B, 0x79, 0x0C, 0x41, 0x8B, 0x09, 0x41, 0x8B, 0x51, 0x04, 0x41,
    0x8B, 0x71, 0x08, 0x44, 0x8D, 0x04, 0x07, 0x41, 0x0F, 0xC8, 0x89, 0x8C, 0x24, 0x00, 0x01, 0x00,
    0x00, 0x89, 0x94, 0x24, 0x04, 0x01, 0x00, 0x00, 0x89, 0xB4, 0x24, 0x08, 0x01, 0x00, 0x00, 0x44,
    0x89, 0x84, 0x24, 0x0C, 0x01, 0x00, 0x00, 0x44, 0x8D, 0x44, 0x07, 0x01, 0x41, 0x0F, 0xC8, 0x89,
    0x8C, 0x24, 0x10, 0x01, 0x00, 0x00, 0x89, 0x94, 0x24, 0x14, 0x01, 0x00, 0x00, 0x89, 0xB4, 0x24,
    0x18, 0x01, 0x00, 0x00, 0x44, 0x89, 0x84, 0x24, 0x1C, 0x01, 0x00, 0x00, 0x44, 0x8D, 0x44, 0x07,
    0x02, 0x41, 0x0F, 0xC8, 0x89, 0x8C, 0x24, 0x20, 0x01, 0x00, 0x00] ++ bytes_l107a08_1

theorem code_l107a08 : ∀ x ∈ codeRange 0x107a08 bytes_l107a08, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x7a08 107 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l107a08_1

@[cfg_block] def b_l107b12 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x107b12 (movR64M64Effect 0x107b12 0 (.sib 4 none 0 (.d32 0x158))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x107b12 (LoadPre 0x107b12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x158)) s (0x107b12 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107b12 0 (.sib 4 none 0 (.d32 0x158))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x107b1a (StorePre 0x107b1a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x107b1a + BitVec.ofNat 64 5)) 8) (xorMREffect 0x107b1a 5 64 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x107b1f (movR64M64Effect 0x107b1f 0 (.sib 4 none 0 (.d32 0x160))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x107b1f (LoadPre 0x107b1f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x160)) s (0x107b1f + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107b1f 0 (.sib 4 none 0 (.d32 0x160))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x107b27 (StorePre 0x107b27 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x107b27 + BitVec.ofNat 64 5)) 8) (xorMREffect 0x107b27 5 64 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x107b2c (movR64M64Effect 0x107b2c 0 (.sib 4 none 0 (.d32 0x168))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x107b2c (LoadPre 0x107b2c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x168)) s (0x107b2c + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107b2c 0 (.sib 4 none 0 (.d32 0x168))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x107b34 (StorePre 0x107b34 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x107b34 + BitVec.ofNat 64 5)) 8) (xorMREffect 0x107b34 5 64 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x107b39 (movR64M64Effect 0x107b39 0 (.sib 4 none 0 (.d32 0x170))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x107b39 (LoadPre 0x107b39 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x170)) s (0x107b39 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107b39 0 (.sib 4 none 0 (.d32 0x170))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x107b41 (StorePre 0x107b41 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x107b41 + BitVec.ofNat 64 5)) 8) (xorMREffect 0x107b41 5 64 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x107b46 (movR64M64Effect 0x107b46 0 (.sib 4 none 0 (.d32 0x178))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 66) (.exec 0x107b46 (LoadPre 0x107b46 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x178)) s (0x107b46 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107b46 0 (.sib 4 none 0 (.d32 0x178))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x107b4e (StorePre 0x107b4e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x107b4e + BitVec.ofNat 64 5)) 8) (xorMREffect 0x107b4e 5 64 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x107b53 (movR64M64Effect 0x107b53 0 (.sib 4 none 0 (.d32 0x180))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 69) (.exec 0x107b53 (LoadPre 0x107b53 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x180)) s (0x107b53 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107b53 0 (.sib 4 none 0 (.d32 0x180))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.exec 0x107b5b (StorePre 0x107b5b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x107b5b + BitVec.ofNat 64 5)) 8) (xorMREffect 0x107b5b 5 64 0 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[68, 4]
    (.letOp (n := 71) (.out 0x107b60 (movR64M64Effect 0x107b60 0 (.sib 4 none 0 (.d32 0x188))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 72) (.exec 0x107b60 (LoadPre 0x107b60 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x188)) s (0x107b60 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107b60 0 (.sib 4 none 0 (.d32 0x188))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.exec 0x107b68 (StorePre 0x107b68 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x107b68 + BitVec.ofNat 64 5)) 8) (xorMREffect 0x107b68 5 64 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[71, 4]
    (.letOp (n := 74) (.out 0x107b6d (movR64M64Effect 0x107b6d 14 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 75) (.exec 0x107b6d (LoadPre 0x107b6d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x107b6d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107b6d 14 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 76) (.out 0x107b72 (xorR32R32Effect 0x107b72 2 5 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 5] []) (.reg (.gpr 5))) #v[5, 5]
    (.letOp (n := 77) (.exec 0x107b72 (fun s => s.RIP = 0x107b72) (xorR32R32Effect 0x107b72 2 5 5) (Reg.operands [.gpr 5, .gpr 5] [])) #v[5, 5]
    (.letOp (n := 78) (.exec 0x107b74 (fun s => s.RIP = 0x107b74) (fun _ => nopEffect 0x107b74 12) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l107b80, RegMap.args [(0, 71), (4, 4), (5, 76), (12, 12), (13, 13), (14, 74), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 79⟩)))))))))))))))))))))))))))

def bytes_l107b12 : List UInt8 :=
  [0x48, 0x8B, 0x84, 0x24, 0x58, 0x01, 0x00, 0x00, 0x48, 0x31, 0x44, 0x24, 0x08, 0x48, 0x8B, 0x84,
    0x24, 0x60, 0x01, 0x00, 0x00, 0x48, 0x31, 0x44, 0x24, 0x10, 0x48, 0x8B, 0x84, 0x24, 0x68, 0x01,
    0x00, 0x00, 0x48, 0x31, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x84, 0x24, 0x70, 0x01, 0x00, 0x00, 0x48,
    0x31, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x84, 0x24, 0x78, 0x01, 0x00, 0x00, 0x48, 0x31, 0x44, 0x24,
    0x28, 0x48, 0x8B, 0x84, 0x24, 0x80, 0x01, 0x00, 0x00, 0x48, 0x31, 0x44, 0x24, 0x30, 0x48, 0x8B,
    0x84, 0x24, 0x88, 0x01, 0x00, 0x00, 0x48, 0x31, 0x44, 0x24, 0x38, 0x4C, 0x8B, 0x74, 0x24, 0x40,
    0x31, 0xED, 0x66, 0x66, 0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem code_l107b12 : ∀ x ∈ codeRange 0x107b12 bytes_l107b12, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x7b12 110 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l107b80 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x107b80 (xorR64M64Effect 0x107b80 14 (.sib 4 (some 5) 3 (.d32 0x190))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 4, .gpr 5] []) (.reg (.gpr 14))) #v[14, 4, 5]
    (.letOp (n := 54) (.exec 0x107b80 (LoadPre 0x107b80 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x190)) s (0x107b80 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x107b80 14 (.sib 4 (some 5) 3 (.d32 0x190))) (Reg.operands [.gpr 14, .gpr 4, .gpr 5] [])) #v[14, 4, 5]
    (.letOp (n := 55) (.exec 0x107b88 (StorePre 0x107b88 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x107b88 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107b88 14 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x107b8d (movR32Imm32Effect 0x107b8d 5 6 0x8) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 57) (.exec 0x107b8d (fun s => s.RIP = 0x107b8d) (movR32Imm32Effect 0x107b8d 5 6 0x8) (Reg.operands [] [])) #v[]
    (.letOp (n := 58) (.out 0x107b92 (leaR64Effect 0x107b92 3 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 59) (.exec 0x107b92 (fun s => s.RIP = 0x107b92) (leaR64Effect 0x107b92 3 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.out 0x107b97 (movR64R64Effect 0x107b97 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[58]
    (.letOp (n := 61) (.exec 0x107b97 (fun s => s.RIP = 0x107b97) (movR64R64Effect 0x107b97 7 3) (Reg.operands [.gpr 3] [])) #v[58]
    (.letOp (n := 62) (.out 0x107b9a (callEffect (fun _ => 0x100e90) 0x107b9f) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 63) (.exec 0x107b9a (PushPre 0x107b9a 5) (callEffect (fun _ => 0x100e90) 0x107b9f) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.const ⟨64, 0x107b9f⟩) #v[]
    (.terminate (.call ⟨.l100e90, RegMap.args [(3, 58), (4, 62), (5, 5), (6, 56), (7, 60), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 65⟩ { target := .l107b9f, kept := #v[], arity := rfl, guard := some (Fin.last 64) })))))))))))))

def bytes_l107b80 : List UInt8 :=
  [0x4C, 0x33, 0xB4, 0xEC, 0x90, 0x01, 0x00, 0x00, 0x4C, 0x89, 0x74, 0x24, 0x40, 0xBE, 0x08, 0x00,
    0x00, 0x00, 0x48, 0x8D, 0x5C, 0x24, 0x08, 0x48, 0x89, 0xDF, 0xE8, 0xF1, 0x92, 0xFF, 0xFF]

theorem code_l107b80 : ∀ x ∈ codeRange 0x107b80 bytes_l107b80, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x7b80 31 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l107b9f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x107b9f (movR64R64Effect 0x107b9f 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 54) (.exec 0x107b9f (fun s => s.RIP = 0x107b9f) (movR64R64Effect 0x107b9f 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x107ba2 (callEffect (fun _ => 0x1002a0) 0x107ba7) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 56) (.exec 0x107ba2 (PushPre 0x107ba2 5) (callEffect (fun _ => 0x1002a0) 0x107ba7) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.const ⟨64, 0x107ba7⟩) #v[]
    (.terminate (.call ⟨.l1002a0, RegMap.args [(3, 3), (4, 55), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ { target := .l107ba7, kept := #v[], arity := rfl, guard := some (Fin.last 57) }))))))

def bytes_l107b9f : List UInt8 :=
  [0x48, 0x89, 0xDF, 0xE8, 0xF9, 0x86, 0xFF, 0xFF]

theorem code_l107b9f : ∀ x ∈ codeRange 0x107b9f bytes_l107b9f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x7b9f 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l107ba7_1 : Block Op Label signature Reg.count 87 :=
  .letOp (n := 87) (.exec 0x107c20 (StorePre 0x107c20 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x107c20 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107c20 1 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[85, 4]
    (.letOp (n := 88) (.out 0x107c25 (movR64M64Effect 0x107c25 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 89) (.exec 0x107c25 (LoadPre 0x107c25 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x107c25 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107c25 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 90) (.out 0x107c2a (xorR64M64Effect 0x107c2a 0 (.sib 4 (some 5) 3 (.d32 0x1d0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4, .gpr 5] []) (.reg (.gpr 0))) #v[88, 4, 5]
    (.letOp (n := 91) (.exec 0x107c2a (LoadPre 0x107c2a (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x1d0)) s (0x107c2a + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x107c2a 0 (.sib 4 (some 5) 3 (.d32 0x1d0))) (Reg.operands [.gpr 0, .gpr 4, .gpr 5] [])) #v[88, 4, 5]
    (.letOp (n := 92) (.exec 0x107c32 (StorePre 0x107c32 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x107c32 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107c32 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[90, 4]
    (.letOp (n := 93) (.out 0x107c37 (cmpR64Imm8Effect 0x107c37 5 0x40) (EffectPart.reads (.flag .ZF) [.gpr 5] []) (.flag .ZF)) #v[5]
    (.letOp (n := 94) (.exec 0x107c37 (fun s => s.RIP = 0x107c37) (cmpR64Imm8Effect 0x107c37 5 0x40) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 95) (.pure (condOp 4)) #v[93]
    (.terminate (.condBr (Fin.last 95) ⟨.l107170, RegMap.args [(0, 90), (1, 85), (2, 80), (3, 3), (4, 4), (5, 5), (6, 75), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (19, 93), (22, 22), (39, 39), (50, 50), (51, 51)] 96⟩ ⟨.l107c41, RegMap.args [(0, 90), (1, 85), (2, 80), (3, 3), (4, 4), (5, 5), (6, 75), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (19, 93), (22, 22), (39, 39), (50, 50), (51, 51)] 96⟩))))))))))

def bytes_l107ba7_1 : List UInt8 :=
  [0x48, 0x89, 0x4C, 0x24, 0x38, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48, 0x33, 0x84, 0xEC, 0xD0, 0x01,
    0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x40, 0x48, 0x83, 0xFD, 0x40, 0x0F, 0x84, 0x2F, 0xF5, 0xFF,
    0xFF]

theorem code_l107ba7_1 : ∀ x ∈ codeRange 0x107c20 bytes_l107ba7_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x7c20 33 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l107ba7 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x107ba7 (movR64M64Effect 0x107ba7 10 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 54) (.exec 0x107ba7 (LoadPre 0x107ba7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x107ba7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107ba7 10 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x107bac (movR64M64Effect 0x107bac 9 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 56) (.exec 0x107bac (LoadPre 0x107bac (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x107bac + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107bac 9 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x107bb1 (xorR64M64Effect 0x107bb1 10 (.sib 4 (some 5) 3 (.d32 0x198))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 4, .gpr 5] []) (.reg (.gpr 10))) #v[53, 4, 5]
    (.letOp (n := 58) (.exec 0x107bb1 (LoadPre 0x107bb1 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x198)) s (0x107bb1 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x107bb1 10 (.sib 4 (some 5) 3 (.d32 0x198))) (Reg.operands [.gpr 10, .gpr 4, .gpr 5] [])) #v[53, 4, 5]
    (.letOp (n := 59) (.exec 0x107bb9 (StorePre 0x107bb9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x107bb9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107bb9 10 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 60) (.out 0x107bbe (xorR64M64Effect 0x107bbe 9 (.sib 4 (some 5) 3 (.d32 0x1a0))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 4, .gpr 5] []) (.reg (.gpr 9))) #v[55, 4, 5]
    (.letOp (n := 61) (.exec 0x107bbe (LoadPre 0x107bbe (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x1a0)) s (0x107bbe + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x107bbe 9 (.sib 4 (some 5) 3 (.d32 0x1a0))) (Reg.operands [.gpr 9, .gpr 4, .gpr 5] [])) #v[55, 4, 5]
    (.letOp (n := 62) (.exec 0x107bc6 (StorePre 0x107bc6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x107bc6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107bc6 9 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[60, 4]
    (.letOp (n := 63) (.out 0x107bcb (movR64M64Effect 0x107bcb 8 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 64) (.exec 0x107bcb (LoadPre 0x107bcb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x107bcb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107bcb 8 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x107bd0 (xorR64M64Effect 0x107bd0 8 (.sib 4 (some 5) 3 (.d32 0x1a8))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 4, .gpr 5] []) (.reg (.gpr 8))) #v[63, 4, 5]
    (.letOp (n := 66) (.exec 0x107bd0 (LoadPre 0x107bd0 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x1a8)) s (0x107bd0 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x107bd0 8 (.sib 4 (some 5) 3 (.d32 0x1a8))) (Reg.operands [.gpr 8, .gpr 4, .gpr 5] [])) #v[63, 4, 5]
    (.letOp (n := 67) (.exec 0x107bd8 (StorePre 0x107bd8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x107bd8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107bd8 8 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x107bdd (movR64M64Effect 0x107bdd 7 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 69) (.exec 0x107bdd (LoadPre 0x107bdd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x107bdd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107bdd 7 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.out 0x107be2 (xorR64M64Effect 0x107be2 7 (.sib 4 (some 5) 3 (.d32 0x1b0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 4, .gpr 5] []) (.reg (.gpr 7))) #v[68, 4, 5]
    (.letOp (n := 71) (.exec 0x107be2 (LoadPre 0x107be2 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x1b0)) s (0x107be2 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x107be2 7 (.sib 4 (some 5) 3 (.d32 0x1b0))) (Reg.operands [.gpr 7, .gpr 4, .gpr 5] [])) #v[68, 4, 5]
    (.letOp (n := 72) (.exec 0x107bea (StorePre 0x107bea 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x107bea + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107bea 7 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[70, 4]
    (.letOp (n := 73) (.out 0x107bef (movR64M64Effect 0x107bef 6 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 74) (.exec 0x107bef (LoadPre 0x107bef (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x107bef + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107bef 6 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.out 0x107bf4 (xorR64M64Effect 0x107bf4 6 (.sib 4 (some 5) 3 (.d32 0x1b8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 4, .gpr 5] []) (.reg (.gpr 6))) #v[73, 4, 5]
    (.letOp (n := 76) (.exec 0x107bf4 (LoadPre 0x107bf4 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x1b8)) s (0x107bf4 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x107bf4 6 (.sib 4 (some 5) 3 (.d32 0x1b8))) (Reg.operands [.gpr 6, .gpr 4, .gpr 5] [])) #v[73, 4, 5]
    (.letOp (n := 77) (.exec 0x107bfc (StorePre 0x107bfc 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x107bfc + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107bfc 6 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[75, 4]
    (.letOp (n := 78) (.out 0x107c01 (movR64M64Effect 0x107c01 2 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 79) (.exec 0x107c01 (LoadPre 0x107c01 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x107c01 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107c01 2 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 80) (.out 0x107c06 (xorR64M64Effect 0x107c06 2 (.sib 4 (some 5) 3 (.d32 0x1c0))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 4, .gpr 5] []) (.reg (.gpr 2))) #v[78, 4, 5]
    (.letOp (n := 81) (.exec 0x107c06 (LoadPre 0x107c06 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x1c0)) s (0x107c06 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x107c06 2 (.sib 4 (some 5) 3 (.d32 0x1c0))) (Reg.operands [.gpr 2, .gpr 4, .gpr 5] [])) #v[78, 4, 5]
    (.letOp (n := 82) (.exec 0x107c0e (StorePre 0x107c0e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x107c0e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107c0e 2 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[80, 4]
    (.letOp (n := 83) (.out 0x107c13 (movR64M64Effect 0x107c13 1 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 84) (.exec 0x107c13 (LoadPre 0x107c13 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x107c13 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107c13 1 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 85) (.out 0x107c18 (xorR64M64Effect 0x107c18 1 (.sib 4 (some 5) 3 (.d32 0x1c8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 4, .gpr 5] []) (.reg (.gpr 1))) #v[83, 4, 5]
    (.letOp (n := 86) (.exec 0x107c18 (LoadPre 0x107c18 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x1c8)) s (0x107c18 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x107c18 1 (.sib 4 (some 5) 3 (.d32 0x1c8))) (Reg.operands [.gpr 1, .gpr 4, .gpr 5] [])) #v[83, 4, 5]
    (b_l107ba7_1))))))))))))))))))))))))))))))))))

def bytes_l107ba7 : List UInt8 :=
  [0x4C, 0x8B, 0x54, 0x24, 0x08, 0x4C, 0x8B, 0x4C, 0x24, 0x10, 0x4C, 0x33, 0x94, 0xEC, 0x98, 0x01,
    0x00, 0x00, 0x4C, 0x89, 0x54, 0x24, 0x08, 0x4C, 0x33, 0x8C, 0xEC, 0xA0, 0x01, 0x00, 0x00, 0x4C,
    0x89, 0x4C, 0x24, 0x10, 0x4C, 0x8B, 0x44, 0x24, 0x18, 0x4C, 0x33, 0x84, 0xEC, 0xA8, 0x01, 0x00,
    0x00, 0x4C, 0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x7C, 0x24, 0x20, 0x48, 0x33, 0xBC, 0xEC, 0xB0,
    0x01, 0x00, 0x00, 0x48, 0x89, 0x7C, 0x24, 0x20, 0x48, 0x8B, 0x74, 0x24, 0x28, 0x48, 0x33, 0xB4,
    0xEC, 0xB8, 0x01, 0x00, 0x00, 0x48, 0x89, 0x74, 0x24, 0x28, 0x48, 0x8B, 0x54, 0x24, 0x30, 0x48,
    0x33, 0x94, 0xEC, 0xC0, 0x01, 0x00, 0x00, 0x48, 0x89, 0x54, 0x24, 0x30, 0x48, 0x8B, 0x4C, 0x24,
    0x38, 0x48, 0x33, 0x8C, 0xEC, 0xC8, 0x01, 0x00, 0x00] ++ bytes_l107ba7_1

theorem code_l107ba7 : ∀ x ∈ codeRange 0x107ba7 bytes_l107ba7, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x7ba7 121 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l107ba7_1

@[cfg_block] def b_l107c41 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x107c41 (movR32Imm32Effect 0x107c41 5 6 0x8) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 54) (.exec 0x107c41 (fun s => s.RIP = 0x107c41) (movR32Imm32Effect 0x107c41 5 6 0x8) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x107c46 (leaR64Effect 0x107c46 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 56) (.exec 0x107c46 (fun s => s.RIP = 0x107c46) (leaR64Effect 0x107c46 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x107c4b (callEffect (fun _ => 0x100e90) 0x107c50) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x107c4b (PushPre 0x107c4b 5) (callEffect (fun _ => 0x100e90) 0x107c50) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x107c50⟩) #v[]
    (.terminate (.call ⟨.l100e90, RegMap.args [(3, 3), (4, 57), (5, 5), (6, 53), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ { target := .l107c50, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l107c41 : List UInt8 :=
  [0xBE, 0x08, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x7C, 0x24, 0x08, 0xE8, 0x40, 0x92, 0xFF, 0xFF]

theorem code_l107c41 : ∀ x ∈ codeRange 0x107c41 bytes_l107c41, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x7c41 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l107c50_6 : Block Op Label signature Reg.count 283 :=
  .letOp (n := 283) (.out 0x107e48 (movR64M64Effect 0x107e48 2 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 284) (.exec 0x107e48 (LoadPre 0x107e48 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x107e48 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107e48 2 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 285) (.out 0x107e50 (xorR64R64Effect 0x107e50 2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 13] []) (.reg (.gpr 2))) #v[283, 167]
    (.letOp (n := 286) (.exec 0x107e50 (fun s => s.RIP = 0x107e50) (xorR64R64Effect 0x107e50 2 13) (Reg.operands [.gpr 2, .gpr 13] [])) #v[283, 167]
    (.letOp (n := 287) (.out 0x107e53 (xorR64R64Effect 0x107e53 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 13] []) (.reg (.gpr 6))) #v[272, 167]
    (.letOp (n := 288) (.exec 0x107e53 (fun s => s.RIP = 0x107e53) (xorR64R64Effect 0x107e53 6 13) (Reg.operands [.gpr 6, .gpr 13] [])) #v[272, 167]
    (.letOp (n := 289) (.out 0x107e56 (movR64R64Effect 0x107e56 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[285]
    (.letOp (n := 290) (.exec 0x107e56 (fun s => s.RIP = 0x107e56) (movR64R64Effect 0x107e56 0 2) (Reg.operands [.gpr 2] [])) #v[285]
    (.letOp (n := 291) (.out 0x107e59 (rolR64Effect 0x107e59 4 0 32) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[289]
    (.letOp (n := 292) (.exec 0x107e59 (fun s => s.RIP = 0x107e59) (rolR64Effect 0x107e59 4 0 32) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[289]
    (.letOp (n := 293) (.out 0x107e5d (xorR64M64Effect 0x107e5d 0 (.sib 4 (some 5) 3 (.d32 0x208))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4, .gpr 5] []) (.reg (.gpr 0))) #v[291, 4, 5]
    (.letOp (n := 294) (.exec 0x107e5d (LoadPre 0x107e5d (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x208)) s (0x107e5d + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x107e5d 0 (.sib 4 (some 5) 3 (.d32 0x208))) (Reg.operands [.gpr 0, .gpr 4, .gpr 5] [])) #v[291, 4, 5]
    (.letOp (n := 295) (.out 0x107e65 (xorR64R64Effect 0x107e65 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[287, 293]
    (.letOp (n := 296) (.exec 0x107e65 (fun s => s.RIP = 0x107e65) (xorR64R64Effect 0x107e65 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[287, 293]
    (.letOp (n := 297) (.exec 0x107e68 (StorePre 0x107e68 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x107e68 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107e68 6 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[295, 4]
    (.letOp (n := 298) (.out 0x107e6d (xorR64R64Effect 0x107e6d 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[285, 187]
    (.letOp (n := 299) (.exec 0x107e6d (fun s => s.RIP = 0x107e6d) (xorR64R64Effect 0x107e6d 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[285, 187]
    (.letOp (n := 300) (.out 0x107e70 (rolR64Effect 0x107e70 4 14 32) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[191]
    (.letOp (n := 301) (.exec 0x107e70 (fun s => s.RIP = 0x107e70) (rolR64Effect 0x107e70 4 14 32) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[191]
    (.letOp (n := 302) (.out 0x107e74 (xorR64M64Effect 0x107e74 14 (.sib 4 (some 5) 3 (.d32 0x210))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 4, .gpr 5] []) (.reg (.gpr 14))) #v[300, 4, 5]
    (.letOp (n := 303) (.exec 0x107e74 (LoadPre 0x107e74 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x210)) s (0x107e74 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x107e74 14 (.sib 4 (some 5) 3 (.d32 0x210))) (Reg.operands [.gpr 14, .gpr 4, .gpr 5] [])) #v[300, 4, 5]
    (.letOp (n := 304) (.out 0x107e7c (xorR64R64Effect 0x107e7c 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 14] []) (.reg (.gpr 2))) #v[298, 302]
    (.letOp (n := 305) (.exec 0x107e7c (fun s => s.RIP = 0x107e7c) (xorR64R64Effect 0x107e7c 2 14) (Reg.operands [.gpr 2, .gpr 14] [])) #v[298, 302]
    (.letOp (n := 306) (.exec 0x107e7f (StorePre 0x107e7f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x107e7f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107e7f 2 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[304, 4]
    (.letOp (n := 307) (.out 0x107e84 (movR32Imm32Effect 0x107e84 5 6 0x8) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 308) (.exec 0x107e84 (fun s => s.RIP = 0x107e84) (movR32Imm32Effect 0x107e84 5 6 0x8) (Reg.operands [] [])) #v[]
    (.letOp (n := 309) (.out 0x107e89 (leaR64Effect 0x107e89 3 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 310) (.exec 0x107e89 (fun s => s.RIP = 0x107e89) (leaR64Effect 0x107e89 3 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 311) (.out 0x107e8e (movR64R64Effect 0x107e8e 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[309]
    (.letOp (n := 312) (.exec 0x107e8e (fun s => s.RIP = 0x107e8e) (movR64R64Effect 0x107e8e 7 3) (Reg.operands [.gpr 3] [])) #v[309]
    (.letOp (n := 313) (.out 0x107e91 (callEffect (fun _ => 0x100e90) 0x107e96) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 314) (.exec 0x107e91 (PushPre 0x107e91 5) (callEffect (fun _ => 0x100e90) 0x107e96) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 315) (.const ⟨64, 0x107e96⟩) #v[]
    (.terminate (.call ⟨.l100e90, RegMap.args [(0, 293), (1, 187), (2, 304), (3, 309), (4, 313), (5, 5), (6, 307), (7, 311), (8, 280), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 302), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)] 316⟩ { target := .l107e96, kept := #v[], arity := rfl, guard := some (Fin.last 315) }))))))))))))))))))))))))))))))))))

def bytes_l107c50_6 : List UInt8 :=
  [0x48, 0x8B, 0x94, 0x24, 0x88, 0x00, 0x00, 0x00, 0x4C, 0x31, 0xEA, 0x4C, 0x31, 0xEE, 0x48, 0x89,
    0xD0, 0x48, 0xC1, 0xC0, 0x20, 0x48, 0x33, 0x84, 0xEC, 0x08, 0x02, 0x00, 0x00, 0x48, 0x31, 0xC6,
    0x48, 0x89, 0x74, 0x24, 0x38, 0x48, 0x31, 0xCA, 0x49, 0xC1, 0xC6, 0x20, 0x4C, 0x33, 0xB4, 0xEC,
    0x10, 0x02, 0x00, 0x00, 0x4C, 0x31, 0xF2, 0x48, 0x89, 0x54, 0x24, 0x40, 0xBE, 0x08, 0x00, 0x00,
    0x00, 0x48, 0x8D, 0x5C, 0x24, 0x08, 0x48, 0x89, 0xDF, 0xE8, 0xFA, 0x8F, 0xFF, 0xFF]

theorem code_l107c50_6 : ∀ x ∈ codeRange 0x107e48 bytes_l107c50_6, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x7e48 78 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l107c50_5 : Block Op Label signature Reg.count 246 :=
  .letOp (n := 246) (.out 0x107dee (movR64M64Effect 0x107dee 8 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 247) (.exec 0x107dee (LoadPre 0x107dee (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x107dee + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107dee 8 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 248) (.out 0x107df3 (xorR64R64Effect 0x107df3 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2] []) (.reg (.gpr 8))) #v[246, 138]
    (.letOp (n := 249) (.exec 0x107df3 (fun s => s.RIP = 0x107df3) (xorR64R64Effect 0x107df3 8 2) (Reg.operands [.gpr 8, .gpr 2] [])) #v[246, 138]
    (.letOp (n := 250) (.exec 0x107df6 (StorePre 0x107df6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x107df6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107df6 7 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[244, 4]
    (.letOp (n := 251) (.out 0x107dfb (movR64R64Effect 0x107dfb 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[248]
    (.letOp (n := 252) (.exec 0x107dfb (fun s => s.RIP = 0x107dfb) (movR64R64Effect 0x107dfb 0 8) (Reg.operands [.gpr 8] [])) #v[248]
    (.letOp (n := 253) (.out 0x107dfe (rolR64Effect 0x107dfe 4 0 32) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[251]
    (.letOp (n := 254) (.exec 0x107dfe (fun s => s.RIP = 0x107dfe) (rolR64Effect 0x107dfe 4 0 32) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[251]
    (.letOp (n := 255) (.out 0x107e02 (xorR64R64Effect 0x107e02 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[231, 138]
    (.letOp (n := 256) (.exec 0x107e02 (fun s => s.RIP = 0x107e02) (xorR64R64Effect 0x107e02 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[231, 138]
    (.letOp (n := 257) (.out 0x107e05 (xorR64M64Effect 0x107e05 0 (.sib 4 (some 5) 3 (.d32 0x1f8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4, .gpr 5] []) (.reg (.gpr 0))) #v[253, 4, 5]
    (.letOp (n := 258) (.exec 0x107e05 (LoadPre 0x107e05 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x1f8)) s (0x107e05 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x107e05 0 (.sib 4 (some 5) 3 (.d32 0x1f8))) (Reg.operands [.gpr 0, .gpr 4, .gpr 5] [])) #v[253, 4, 5]
    (.letOp (n := 259) (.out 0x107e0d (xorR64R64Effect 0x107e0d 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 14] []) (.reg (.gpr 6))) #v[255, 191]
    (.letOp (n := 260) (.exec 0x107e0d (fun s => s.RIP = 0x107e0d) (xorR64R64Effect 0x107e0d 6 14) (Reg.operands [.gpr 6, .gpr 14] [])) #v[255, 191]
    (.letOp (n := 261) (.out 0x107e10 (xorR64R64Effect 0x107e10 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[259, 257]
    (.letOp (n := 262) (.exec 0x107e10 (fun s => s.RIP = 0x107e10) (xorR64R64Effect 0x107e10 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[259, 257]
    (.letOp (n := 263) (.out 0x107e13 (movR64M64Effect 0x107e13 2 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 264) (.exec 0x107e13 (LoadPre 0x107e13 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x107e13 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107e13 2 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 265) (.out 0x107e1b (movR64M64Effect 0x107e1b 7 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 266) (.exec 0x107e1b (LoadPre 0x107e1b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x107e1b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107e1b 7 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 267) (.out 0x107e23 (xorR64R64Effect 0x107e23 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 7] []) (.reg (.gpr 2))) #v[263, 265]
    (.letOp (n := 268) (.exec 0x107e23 (fun s => s.RIP = 0x107e23) (xorR64R64Effect 0x107e23 2 7) (Reg.operands [.gpr 2, .gpr 7] [])) #v[263, 265]
    (.letOp (n := 269) (.exec 0x107e26 (StorePre 0x107e26 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x107e26 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107e26 6 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[261, 4]
    (.letOp (n := 270) (.out 0x107e2b (movR64R64Effect 0x107e2b 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[267]
    (.letOp (n := 271) (.exec 0x107e2b (fun s => s.RIP = 0x107e2b) (movR64R64Effect 0x107e2b 0 2) (Reg.operands [.gpr 2] [])) #v[267]
    (.letOp (n := 272) (.out 0x107e2e (movR64R64Effect 0x107e2e 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[267]
    (.letOp (n := 273) (.exec 0x107e2e (fun s => s.RIP = 0x107e2e) (movR64R64Effect 0x107e2e 6 2) (Reg.operands [.gpr 2] [])) #v[267]
    (.letOp (n := 274) (.out 0x107e31 (rolR64Effect 0x107e31 4 0 32) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[270]
    (.letOp (n := 275) (.exec 0x107e31 (fun s => s.RIP = 0x107e31) (rolR64Effect 0x107e31 4 0 32) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[270]
    (.letOp (n := 276) (.out 0x107e35 (xorR64M64Effect 0x107e35 0 (.sib 4 (some 5) 3 (.d32 0x200))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4, .gpr 5] []) (.reg (.gpr 0))) #v[274, 4, 5]
    (.letOp (n := 277) (.exec 0x107e35 (LoadPre 0x107e35 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x200)) s (0x107e35 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x107e35 0 (.sib 4 (some 5) 3 (.d32 0x200))) (Reg.operands [.gpr 0, .gpr 4, .gpr 5] [])) #v[274, 4, 5]
    (.letOp (n := 278) (.out 0x107e3d (xorR64R64Effect 0x107e3d 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 7] []) (.reg (.gpr 8))) #v[248, 265]
    (.letOp (n := 279) (.exec 0x107e3d (fun s => s.RIP = 0x107e3d) (xorR64R64Effect 0x107e3d 8 7) (Reg.operands [.gpr 8, .gpr 7] [])) #v[248, 265]
    (.letOp (n := 280) (.out 0x107e40 (xorR64R64Effect 0x107e40 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[278, 276]
    (.letOp (n := 281) (.exec 0x107e40 (fun s => s.RIP = 0x107e40) (xorR64R64Effect 0x107e40 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[278, 276]
    (.letOp (n := 282) (.exec 0x107e43 (StorePre 0x107e43 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x107e43 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107e43 8 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[280, 4]
    (b_l107c50_6)))))))))))))))))))))))))))))))))))))

def bytes_l107c50_5 : List UInt8 :=
  [0x4C, 0x8B, 0x44, 0x24, 0x78, 0x49, 0x31, 0xD0, 0x48, 0x89, 0x7C, 0x24, 0x20, 0x4C, 0x89, 0xC0,
    0x48, 0xC1, 0xC0, 0x20, 0x48, 0x31, 0xD6, 0x48, 0x33, 0x84, 0xEC, 0xF8, 0x01, 0x00, 0x00, 0x4C,
    0x31, 0xF6, 0x48, 0x31, 0xC6, 0x48, 0x8B, 0x94, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0x8B, 0xBC,
    0x24, 0x90, 0x00, 0x00, 0x00, 0x48, 0x31, 0xFA, 0x48, 0x89, 0x74, 0x24, 0x28, 0x48, 0x89, 0xD0,
    0x48, 0x89, 0xD6, 0x48, 0xC1, 0xC0, 0x20, 0x48, 0x33, 0x84, 0xEC, 0x00, 0x02, 0x00, 0x00, 0x49,
    0x31, 0xF8, 0x49, 0x31, 0xC0, 0x4C, 0x89, 0x44, 0x24, 0x30] ++ bytes_l107c50_6

theorem code_l107c50_5 : ∀ x ∈ codeRange 0x107dee bytes_l107c50_5, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x7dee 90 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l107c50_6

@[cfg_block] def b_l107c50_4 : Block Op Label signature Reg.count 208 :=
  .letOp (n := 208) (.out 0x107d9c (movR64R64Effect 0x107d9c 8 11) (EffectPart.reads (.reg (.gpr 8)) [.gpr 11] []) (.reg (.gpr 8))) #v[204]
    (.letOp (n := 209) (.exec 0x107d9c (fun s => s.RIP = 0x107d9c) (movR64R64Effect 0x107d9c 8 11) (Reg.operands [.gpr 11] [])) #v[204]
    (.letOp (n := 210) (.out 0x107d9f (rolR64Effect 0x107d9f 4 8 32) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[208]
    (.letOp (n := 211) (.exec 0x107d9f (fun s => s.RIP = 0x107d9f) (rolR64Effect 0x107d9f 4 8 32) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[208]
    (.letOp (n := 212) (.out 0x107da3 (xorR64M64Effect 0x107da3 8 (.sib 4 (some 5) 3 (.d32 0x1e0))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 4, .gpr 5] []) (.reg (.gpr 8))) #v[210, 4, 5]
    (.letOp (n := 213) (.exec 0x107da3 (LoadPre 0x107da3 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x1e0)) s (0x107da3 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x107da3 8 (.sib 4 (some 5) 3 (.d32 0x1e0))) (Reg.operands [.gpr 8, .gpr 4, .gpr 5] [])) #v[210, 4, 5]
    (.letOp (n := 214) (.out 0x107dab (xorR64R64Effect 0x107dab 3 14) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 14] []) (.reg (.gpr 3))) #v[206, 191]
    (.letOp (n := 215) (.exec 0x107dab (fun s => s.RIP = 0x107dab) (xorR64R64Effect 0x107dab 3 14) (Reg.operands [.gpr 3, .gpr 14] [])) #v[206, 191]
    (.letOp (n := 216) (.out 0x107dae (xorR64R64Effect 0x107dae 3 8) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 8] []) (.reg (.gpr 3))) #v[214, 212]
    (.letOp (n := 217) (.exec 0x107dae (fun s => s.RIP = 0x107dae) (xorR64R64Effect 0x107dae 3 8) (Reg.operands [.gpr 3, .gpr 8] [])) #v[214, 212]
    (.letOp (n := 218) (.exec 0x107db1 (StorePre 0x107db1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x107db1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107db1 3 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[216, 4]
    (.letOp (n := 219) (.out 0x107db6 (xorR64R64Effect 0x107db6 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[57, 111]
    (.letOp (n := 220) (.exec 0x107db6 (fun s => s.RIP = 0x107db6) (xorR64R64Effect 0x107db6 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[57, 111]
    (.letOp (n := 221) (.out 0x107db9 (xorR64R64Effect 0x107db9 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0] []) (.reg (.gpr 11))) #v[204, 111]
    (.letOp (n := 222) (.exec 0x107db9 (fun s => s.RIP = 0x107db9) (xorR64R64Effect 0x107db9 11 0) (Reg.operands [.gpr 11, .gpr 0] [])) #v[204, 111]
    (.letOp (n := 223) (.out 0x107dbc (movR64R64Effect 0x107dbc 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[219]
    (.letOp (n := 224) (.exec 0x107dbc (fun s => s.RIP = 0x107dbc) (movR64R64Effect 0x107dbc 0 7) (Reg.operands [.gpr 7] [])) #v[219]
    (.letOp (n := 225) (.out 0x107dbf (rolR64Effect 0x107dbf 4 0 32) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[223]
    (.letOp (n := 226) (.exec 0x107dbf (fun s => s.RIP = 0x107dbf) (rolR64Effect 0x107dbf 4 0 32) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[223]
    (.letOp (n := 227) (.out 0x107dc3 (xorR64M64Effect 0x107dc3 0 (.sib 4 (some 5) 3 (.d32 0x1e8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4, .gpr 5] []) (.reg (.gpr 0))) #v[225, 4, 5]
    (.letOp (n := 228) (.exec 0x107dc3 (LoadPre 0x107dc3 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x1e8)) s (0x107dc3 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x107dc3 0 (.sib 4 (some 5) 3 (.d32 0x1e8))) (Reg.operands [.gpr 0, .gpr 4, .gpr 5] [])) #v[225, 4, 5]
    (.letOp (n := 229) (.out 0x107dcb (xorR64R64Effect 0x107dcb 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0] []) (.reg (.gpr 11))) #v[221, 227]
    (.letOp (n := 230) (.exec 0x107dcb (fun s => s.RIP = 0x107dcb) (xorR64R64Effect 0x107dcb 11 0) (Reg.operands [.gpr 11, .gpr 0] [])) #v[221, 227]
    (.letOp (n := 231) (.out 0x107dce (xorR64R64Effect 0x107dce 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 15] []) (.reg (.gpr 6))) #v[59, 125]
    (.letOp (n := 232) (.exec 0x107dce (fun s => s.RIP = 0x107dce) (xorR64R64Effect 0x107dce 6 15) (Reg.operands [.gpr 6, .gpr 15] [])) #v[59, 125]
    (.letOp (n := 233) (.exec 0x107dd1 (StorePre 0x107dd1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x107dd1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107dd1 11 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[229, 4]
    (.letOp (n := 234) (.out 0x107dd6 (movR64R64Effect 0x107dd6 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[231]
    (.letOp (n := 235) (.exec 0x107dd6 (fun s => s.RIP = 0x107dd6) (movR64R64Effect 0x107dd6 0 6) (Reg.operands [.gpr 6] [])) #v[231]
    (.letOp (n := 236) (.out 0x107dd9 (rolR64Effect 0x107dd9 4 0 32) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[234]
    (.letOp (n := 237) (.exec 0x107dd9 (fun s => s.RIP = 0x107dd9) (rolR64Effect 0x107dd9 4 0 32) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[234]
    (.letOp (n := 238) (.out 0x107ddd (xorR64M64Effect 0x107ddd 0 (.sib 4 (some 5) 3 (.d32 0x1f0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4, .gpr 5] []) (.reg (.gpr 0))) #v[236, 4, 5]
    (.letOp (n := 239) (.exec 0x107ddd (LoadPre 0x107ddd (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x1f0)) s (0x107ddd + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x107ddd 0 (.sib 4 (some 5) 3 (.d32 0x1f0))) (Reg.operands [.gpr 0, .gpr 4, .gpr 5] [])) #v[236, 4, 5]
    (.letOp (n := 240) (.out 0x107de5 (xorR64R64Effect 0x107de5 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 15] []) (.reg (.gpr 7))) #v[219, 125]
    (.letOp (n := 241) (.exec 0x107de5 (fun s => s.RIP = 0x107de5) (xorR64R64Effect 0x107de5 7 15) (Reg.operands [.gpr 7, .gpr 15] [])) #v[219, 125]
    (.letOp (n := 242) (.out 0x107de8 (xorR64R64Effect 0x107de8 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 14] []) (.reg (.gpr 7))) #v[240, 191]
    (.letOp (n := 243) (.exec 0x107de8 (fun s => s.RIP = 0x107de8) (xorR64R64Effect 0x107de8 7 14) (Reg.operands [.gpr 7, .gpr 14] [])) #v[240, 191]
    (.letOp (n := 244) (.out 0x107deb (xorR64R64Effect 0x107deb 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[242, 238]
    (.letOp (n := 245) (.exec 0x107deb (fun s => s.RIP = 0x107deb) (xorR64R64Effect 0x107deb 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[242, 238]
    (b_l107c50_5))))))))))))))))))))))))))))))))))))))

def bytes_l107c50_4 : List UInt8 :=
  [0x4D, 0x89, 0xD8, 0x49, 0xC1, 0xC0, 0x20, 0x4C, 0x33, 0x84, 0xEC, 0xE0, 0x01, 0x00, 0x00, 0x4C,
    0x31, 0xF3, 0x4C, 0x31, 0xC3, 0x48, 0x89, 0x5C, 0x24, 0x10, 0x48, 0x31, 0xC7, 0x49, 0x31, 0xC3,
    0x48, 0x89, 0xF8, 0x48, 0xC1, 0xC0, 0x20, 0x48, 0x33, 0x84, 0xEC, 0xE8, 0x01, 0x00, 0x00, 0x49,
    0x31, 0xC3, 0x4C, 0x31, 0xFE, 0x4C, 0x89, 0x5C, 0x24, 0x18, 0x48, 0x89, 0xF0, 0x48, 0xC1, 0xC0,
    0x20, 0x48, 0x33, 0x84, 0xEC, 0xF0, 0x01, 0x00, 0x00, 0x4C, 0x31, 0xFF, 0x4C, 0x31, 0xF7, 0x48,
    0x31, 0xC7] ++ bytes_l107c50_5

theorem code_l107c50_4 : ∀ x ∈ codeRange 0x107d9c bytes_l107c50_4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x7d9c 82 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l107c50_5

@[cfg_block] def b_l107c50_3 : Block Op Label signature Reg.count 169 :=
  .letOp (n := 169) (.out 0x107d46 (movR64M64Effect 0x107d46 14 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 170) (.exec 0x107d46 (LoadPre 0x107d46 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x107d46 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107d46 14 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 171) (.out 0x107d4b (movR64R64Effect 0x107d4b 10 14) (EffectPart.reads (.reg (.gpr 10)) [.gpr 14] []) (.reg (.gpr 10))) #v[169]
    (.letOp (n := 172) (.exec 0x107d4b (fun s => s.RIP = 0x107d4b) (movR64R64Effect 0x107d4b 10 14) (Reg.operands [.gpr 14] [])) #v[169]
    (.letOp (n := 173) (.out 0x107d4e (rolR64Effect 0x107d4e 4 10 40) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[171]
    (.letOp (n := 174) (.exec 0x107d4e (fun s => s.RIP = 0x107d4e) (rolR64Effect 0x107d4e 4 10 40) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[171]
    (.letOp (n := 175) (.out 0x107d52 (movR64Imm64Effect 0x107d52 1 0xff00ff00ff00ff) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 176) (.exec 0x107d52 (fun s => s.RIP = 0x107d52) (movR64Imm64Effect 0x107d52 1 0xff00ff00ff00ff) (Reg.operands [] [])) #v[]
    (.letOp (n := 177) (.out 0x107d5c (andR64R64Effect 0x107d5c 10 1) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 1] []) (.reg (.gpr 10))) #v[173, 175]
    (.letOp (n := 178) (.exec 0x107d5c (fun s => s.RIP = 0x107d5c) (andR64R64Effect 0x107d5c 10 1) (Reg.operands [.gpr 10, .gpr 1] [])) #v[173, 175]
    (.letOp (n := 179) (.out 0x107d5f (movR64R64Effect 0x107d5f 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[169]
    (.letOp (n := 180) (.exec 0x107d5f (fun s => s.RIP = 0x107d5f) (movR64R64Effect 0x107d5f 1 14) (Reg.operands [.gpr 14] [])) #v[169]
    (.letOp (n := 181) (.out 0x107d62 (rolR64Effect 0x107d62 4 1 56) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[179]
    (.letOp (n := 182) (.exec 0x107d62 (fun s => s.RIP = 0x107d62) (rolR64Effect 0x107d62 4 1 56) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[179]
    (.letOp (n := 183) (.out 0x107d66 (movR64Imm64Effect 0x107d66 12 0xff00ff00ff00ff00) (EffectPart.reads (.reg (.gpr 12)) [] []) (.reg (.gpr 12))) #v[]
    (.letOp (n := 184) (.exec 0x107d66 (fun s => s.RIP = 0x107d66) (movR64Imm64Effect 0x107d66 12 0xff00ff00ff00ff00) (Reg.operands [] [])) #v[]
    (.letOp (n := 185) (.out 0x107d70 (andR64R64Effect 0x107d70 1 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 12] []) (.reg (.gpr 1))) #v[181, 183]
    (.letOp (n := 186) (.exec 0x107d70 (fun s => s.RIP = 0x107d70) (andR64R64Effect 0x107d70 1 12) (Reg.operands [.gpr 1, .gpr 12] [])) #v[181, 183]
    (.letOp (n := 187) (.out 0x107d73 (orR64R64Effect 0x107d73 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10] []) (.reg (.gpr 1))) #v[185, 177]
    (.letOp (n := 188) (.exec 0x107d73 (fun s => s.RIP = 0x107d73) (orR64R64Effect 0x107d73 1 10) (Reg.operands [.gpr 1, .gpr 10] [])) #v[185, 177]
    (.letOp (n := 189) (.out 0x107d76 (xorR64R64Effect 0x107d76 3 9) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 9] []) (.reg (.gpr 3))) #v[53, 83]
    (.letOp (n := 190) (.exec 0x107d76 (fun s => s.RIP = 0x107d76) (xorR64R64Effect 0x107d76 3 9) (Reg.operands [.gpr 3, .gpr 9] [])) #v[53, 83]
    (.letOp (n := 191) (.out 0x107d79 (xorR64R64Effect 0x107d79 14 1) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 1] []) (.reg (.gpr 14))) #v[169, 187]
    (.letOp (n := 192) (.exec 0x107d79 (fun s => s.RIP = 0x107d79) (xorR64R64Effect 0x107d79 14 1) (Reg.operands [.gpr 14, .gpr 1] [])) #v[169, 187]
    (.letOp (n := 193) (.out 0x107d7c (movR64R64Effect 0x107d7c 10 3) (EffectPart.reads (.reg (.gpr 10)) [.gpr 3] []) (.reg (.gpr 10))) #v[189]
    (.letOp (n := 194) (.exec 0x107d7c (fun s => s.RIP = 0x107d7c) (movR64R64Effect 0x107d7c 10 3) (Reg.operands [.gpr 3] [])) #v[189]
    (.letOp (n := 195) (.out 0x107d7f (rolR64Effect 0x107d7f 4 10 32) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[193]
    (.letOp (n := 196) (.exec 0x107d7f (fun s => s.RIP = 0x107d7f) (rolR64Effect 0x107d7f 4 10 32) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[193]
    (.letOp (n := 197) (.out 0x107d83 (xorR64M64Effect 0x107d83 10 (.sib 4 (some 5) 3 (.d32 0x1d8))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 4, .gpr 5] []) (.reg (.gpr 10))) #v[195, 4, 5]
    (.letOp (n := 198) (.exec 0x107d83 (LoadPre 0x107d83 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x1d8)) s (0x107d83 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x107d83 10 (.sib 4 (some 5) 3 (.d32 0x1d8))) (Reg.operands [.gpr 10, .gpr 4, .gpr 5] [])) #v[195, 4, 5]
    (.letOp (n := 199) (.out 0x107d8b (xorR64R64Effect 0x107d8b 9 14) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 14] []) (.reg (.gpr 9))) #v[83, 191]
    (.letOp (n := 200) (.exec 0x107d8b (fun s => s.RIP = 0x107d8b) (xorR64R64Effect 0x107d8b 9 14) (Reg.operands [.gpr 9, .gpr 14] [])) #v[83, 191]
    (.letOp (n := 201) (.out 0x107d8e (xorR64R64Effect 0x107d8e 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[199, 197]
    (.letOp (n := 202) (.exec 0x107d8e (fun s => s.RIP = 0x107d8e) (xorR64R64Effect 0x107d8e 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[199, 197]
    (.letOp (n := 203) (.exec 0x107d91 (StorePre 0x107d91 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x107d91 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107d91 9 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[201, 4]
    (.letOp (n := 204) (.out 0x107d96 (xorR64R64Effect 0x107d96 11 8) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 8] []) (.reg (.gpr 11))) #v[55, 101]
    (.letOp (n := 205) (.exec 0x107d96 (fun s => s.RIP = 0x107d96) (xorR64R64Effect 0x107d96 11 8) (Reg.operands [.gpr 11, .gpr 8] [])) #v[55, 101]
    (.letOp (n := 206) (.out 0x107d99 (xorR64R64Effect 0x107d99 3 8) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 8] []) (.reg (.gpr 3))) #v[189, 101]
    (.letOp (n := 207) (.exec 0x107d99 (fun s => s.RIP = 0x107d99) (xorR64R64Effect 0x107d99 3 8) (Reg.operands [.gpr 3, .gpr 8] [])) #v[189, 101]
    (b_l107c50_4)))))))))))))))))))))))))))))))))))))))

def bytes_l107c50_3 : List UInt8 :=
  [0x4C, 0x8B, 0x74, 0x24, 0x40, 0x4D, 0x89, 0xF2, 0x49, 0xC1, 0xC2, 0x28, 0x48, 0xB9, 0xFF, 0x00,
    0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0x49, 0x21, 0xCA, 0x4C, 0x89, 0xF1, 0x48, 0xC1, 0xC1, 0x38,
    0x49, 0xBC, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x4C, 0x21, 0xE1, 0x4C, 0x09, 0xD1,
    0x4C, 0x31, 0xCB, 0x49, 0x31, 0xCE, 0x49, 0x89, 0xDA, 0x49, 0xC1, 0xC2, 0x20, 0x4C, 0x33, 0x94,
    0xEC, 0xD8, 0x01, 0x00, 0x00, 0x4D, 0x31, 0xF1, 0x4D, 0x31, 0xD1, 0x4C, 0x89, 0x4C, 0x24, 0x08,
    0x4D, 0x31, 0xC3, 0x4C, 0x31, 0xC3] ++ bytes_l107c50_4

theorem code_l107c50_3 : ∀ x ∈ codeRange 0x107d46 bytes_l107c50_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x7d46 86 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l107c50_4

@[cfg_block] def b_l107c50_2 : Block Op Label signature Reg.count 132 :=
  .letOp (n := 132) (.out 0x107cef (andR64R64Effect 0x107cef 10 13) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 13] []) (.reg (.gpr 10))) #v[130, 71]
    (.letOp (n := 133) (.exec 0x107cef (fun s => s.RIP = 0x107cef) (andR64R64Effect 0x107cef 10 13) (Reg.operands [.gpr 10, .gpr 13] [])) #v[130, 71]
    (.letOp (n := 134) (.out 0x107cf2 (rolR64Effect 0x107cf2 4 2 56) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[127]
    (.letOp (n := 135) (.exec 0x107cf2 (fun s => s.RIP = 0x107cf2) (rolR64Effect 0x107cf2 4 2 56) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[127]
    (.letOp (n := 136) (.out 0x107cf6 (andR64R64Effect 0x107cf6 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[134, 79]
    (.letOp (n := 137) (.exec 0x107cf6 (fun s => s.RIP = 0x107cf6) (andR64R64Effect 0x107cf6 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[134, 79]
    (.letOp (n := 138) (.out 0x107cf9 (orR64R64Effect 0x107cf9 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 10] []) (.reg (.gpr 2))) #v[136, 132]
    (.letOp (n := 139) (.exec 0x107cf9 (fun s => s.RIP = 0x107cf9) (orR64R64Effect 0x107cf9 2 10) (Reg.operands [.gpr 2, .gpr 10] [])) #v[136, 132]
    (.letOp (n := 140) (.exec 0x107cfc (StorePre 0x107cfc 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x107cfc + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107cfc 12 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[63, 4]
    (.letOp (n := 141) (.out 0x107d04 (movR64R64Effect 0x107d04 10 12) (EffectPart.reads (.reg (.gpr 10)) [.gpr 12] []) (.reg (.gpr 10))) #v[63]
    (.letOp (n := 142) (.exec 0x107d04 (fun s => s.RIP = 0x107d04) (movR64R64Effect 0x107d04 10 12) (Reg.operands [.gpr 12] [])) #v[63]
    (.letOp (n := 143) (.out 0x107d07 (rolR64Effect 0x107d07 4 10 40) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[141]
    (.letOp (n := 144) (.exec 0x107d07 (fun s => s.RIP = 0x107d07) (rolR64Effect 0x107d07 4 10 40) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[141]
    (.letOp (n := 145) (.out 0x107d0b (andR64R64Effect 0x107d0b 10 13) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 13] []) (.reg (.gpr 10))) #v[143, 71]
    (.letOp (n := 146) (.exec 0x107d0b (fun s => s.RIP = 0x107d0b) (andR64R64Effect 0x107d0b 10 13) (Reg.operands [.gpr 10, .gpr 13] [])) #v[143, 71]
    (.letOp (n := 147) (.out 0x107d0e (rolR64Effect 0x107d0e 4 12 56) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[63]
    (.letOp (n := 148) (.exec 0x107d0e (fun s => s.RIP = 0x107d0e) (rolR64Effect 0x107d0e 4 12 56) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[63]
    (.letOp (n := 149) (.out 0x107d12 (andR64R64Effect 0x107d12 12 1) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 1] []) (.reg (.gpr 12))) #v[147, 79]
    (.letOp (n := 150) (.exec 0x107d12 (fun s => s.RIP = 0x107d12) (andR64R64Effect 0x107d12 12 1) (Reg.operands [.gpr 12, .gpr 1] [])) #v[147, 79]
    (.letOp (n := 151) (.out 0x107d15 (movR64R64Effect 0x107d15 13 14) (EffectPart.reads (.reg (.gpr 13)) [.gpr 14] []) (.reg (.gpr 13))) #v[65]
    (.letOp (n := 152) (.exec 0x107d15 (fun s => s.RIP = 0x107d15) (movR64R64Effect 0x107d15 13 14) (Reg.operands [.gpr 14] [])) #v[65]
    (.letOp (n := 153) (.exec 0x107d18 (StorePre 0x107d18 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x107d18 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107d18 14 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 154) (.out 0x107d20 (rolR64Effect 0x107d20 4 14 40) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[65]
    (.letOp (n := 155) (.exec 0x107d20 (fun s => s.RIP = 0x107d20) (rolR64Effect 0x107d20 4 14 40) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[65]
    (.letOp (n := 156) (.out 0x107d24 (orR64R64Effect 0x107d24 12 10) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 10] []) (.reg (.gpr 12))) #v[149, 145]
    (.letOp (n := 157) (.exec 0x107d24 (fun s => s.RIP = 0x107d24) (orR64R64Effect 0x107d24 12 10) (Reg.operands [.gpr 12, .gpr 10] [])) #v[149, 145]
    (.letOp (n := 158) (.exec 0x107d27 (StorePre 0x107d27 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x107d27 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107d27 12 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[156, 4]
    (.letOp (n := 159) (.out 0x107d2f (rolR64Effect 0x107d2f 4 13 56) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[151]
    (.letOp (n := 160) (.exec 0x107d2f (fun s => s.RIP = 0x107d2f) (rolR64Effect 0x107d2f 4 13 56) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[151]
    (.letOp (n := 161) (.out 0x107d33 (movR64Imm64Effect 0x107d33 10 0xff00ff00ff00ff) (EffectPart.reads (.reg (.gpr 10)) [] []) (.reg (.gpr 10))) #v[]
    (.letOp (n := 162) (.exec 0x107d33 (fun s => s.RIP = 0x107d33) (movR64Imm64Effect 0x107d33 10 0xff00ff00ff00ff) (Reg.operands [] [])) #v[]
    (.letOp (n := 163) (.out 0x107d3d (andR64R64Effect 0x107d3d 14 10) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 10] []) (.reg (.gpr 14))) #v[154, 161]
    (.letOp (n := 164) (.exec 0x107d3d (fun s => s.RIP = 0x107d3d) (andR64R64Effect 0x107d3d 14 10) (Reg.operands [.gpr 14, .gpr 10] [])) #v[154, 161]
    (.letOp (n := 165) (.out 0x107d40 (andR64R64Effect 0x107d40 13 1) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 1] []) (.reg (.gpr 13))) #v[159, 79]
    (.letOp (n := 166) (.exec 0x107d40 (fun s => s.RIP = 0x107d40) (andR64R64Effect 0x107d40 13 1) (Reg.operands [.gpr 13, .gpr 1] [])) #v[159, 79]
    (.letOp (n := 167) (.out 0x107d43 (orR64R64Effect 0x107d43 13 14) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 14] []) (.reg (.gpr 13))) #v[165, 163]
    (.letOp (n := 168) (.exec 0x107d43 (fun s => s.RIP = 0x107d43) (orR64R64Effect 0x107d43 13 14) (Reg.operands [.gpr 13, .gpr 14] [])) #v[165, 163]
    (b_l107c50_3)))))))))))))))))))))))))))))))))))))

def bytes_l107c50_2 : List UInt8 :=
  [0x4D, 0x21, 0xEA, 0x48, 0xC1, 0xC2, 0x38, 0x48, 0x21, 0xCA, 0x4C, 0x09, 0xD2, 0x4C, 0x89, 0xA4,
    0x24, 0x80, 0x00, 0x00, 0x00, 0x4D, 0x89, 0xE2, 0x49, 0xC1, 0xC2, 0x28, 0x4D, 0x21, 0xEA, 0x49,
    0xC1, 0xC4, 0x38, 0x49, 0x21, 0xCC, 0x4D, 0x89, 0xF5, 0x4C, 0x89, 0xB4, 0x24, 0x88, 0x00, 0x00,
    0x00, 0x49, 0xC1, 0xC6, 0x28, 0x4D, 0x09, 0xD4, 0x4C, 0x89, 0xA4, 0x24, 0x90, 0x00, 0x00, 0x00,
    0x49, 0xC1, 0xC5, 0x38, 0x49, 0xBA, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0x4D, 0x21,
    0xD6, 0x49, 0x21, 0xCD, 0x4D, 0x09, 0xF5] ++ bytes_l107c50_3

theorem code_l107c50_2 : ∀ x ∈ codeRange 0x107cef bytes_l107c50_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x7cef 87 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l107c50_3

@[cfg_block] def b_l107c50_1 : Block Op Label signature Reg.count 93 :=
  .letOp (n := 93) (.out 0x107cab (rolR64Effect 0x107cab 4 8 56) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[91]
    (.letOp (n := 94) (.exec 0x107cab (fun s => s.RIP = 0x107cab) (rolR64Effect 0x107cab 4 8 56) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[91]
    (.letOp (n := 95) (.out 0x107caf (andR64R64Effect 0x107caf 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[93, 79]
    (.letOp (n := 96) (.exec 0x107caf (fun s => s.RIP = 0x107caf) (andR64R64Effect 0x107caf 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[93, 79]
    (.letOp (n := 97) (.out 0x107cb2 (movR64R64Effect 0x107cb2 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7] []) (.reg (.gpr 2))) #v[57]
    (.letOp (n := 98) (.exec 0x107cb2 (fun s => s.RIP = 0x107cb2) (movR64R64Effect 0x107cb2 2 7) (Reg.operands [.gpr 7] [])) #v[57]
    (.letOp (n := 99) (.out 0x107cb5 (rolR64Effect 0x107cb5 4 2 40) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[97]
    (.letOp (n := 100) (.exec 0x107cb5 (fun s => s.RIP = 0x107cb5) (rolR64Effect 0x107cb5 4 2 40) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[97]
    (.letOp (n := 101) (.out 0x107cb9 (orR64R64Effect 0x107cb9 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[95, 89]
    (.letOp (n := 102) (.exec 0x107cb9 (fun s => s.RIP = 0x107cb9) (orR64R64Effect 0x107cb9 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[95, 89]
    (.letOp (n := 103) (.out 0x107cbc (movR64R64Effect 0x107cbc 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[57]
    (.letOp (n := 104) (.exec 0x107cbc (fun s => s.RIP = 0x107cbc) (movR64R64Effect 0x107cbc 0 7) (Reg.operands [.gpr 7] [])) #v[57]
    (.letOp (n := 105) (.out 0x107cbf (rolR64Effect 0x107cbf 4 0 56) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[103]
    (.letOp (n := 106) (.exec 0x107cbf (fun s => s.RIP = 0x107cbf) (rolR64Effect 0x107cbf 4 0 56) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[103]
    (.letOp (n := 107) (.out 0x107cc3 (andR64R64Effect 0x107cc3 2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 13] []) (.reg (.gpr 2))) #v[99, 71]
    (.letOp (n := 108) (.exec 0x107cc3 (fun s => s.RIP = 0x107cc3) (andR64R64Effect 0x107cc3 2 13) (Reg.operands [.gpr 2, .gpr 13] [])) #v[99, 71]
    (.letOp (n := 109) (.out 0x107cc6 (andR64R64Effect 0x107cc6 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[105, 79]
    (.letOp (n := 110) (.exec 0x107cc6 (fun s => s.RIP = 0x107cc6) (andR64R64Effect 0x107cc6 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[105, 79]
    (.letOp (n := 111) (.out 0x107cc9 (orR64R64Effect 0x107cc9 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[109, 107]
    (.letOp (n := 112) (.exec 0x107cc9 (fun s => s.RIP = 0x107cc9) (orR64R64Effect 0x107cc9 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[109, 107]
    (.letOp (n := 113) (.out 0x107ccc (movR64R64Effect 0x107ccc 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6] []) (.reg (.gpr 2))) #v[59]
    (.letOp (n := 114) (.exec 0x107ccc (fun s => s.RIP = 0x107ccc) (movR64R64Effect 0x107ccc 2 6) (Reg.operands [.gpr 6] [])) #v[59]
    (.letOp (n := 115) (.out 0x107ccf (rolR64Effect 0x107ccf 4 2 40) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[113]
    (.letOp (n := 116) (.exec 0x107ccf (fun s => s.RIP = 0x107ccf) (rolR64Effect 0x107ccf 4 2 40) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[113]
    (.letOp (n := 117) (.out 0x107cd3 (andR64R64Effect 0x107cd3 2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 13] []) (.reg (.gpr 2))) #v[115, 71]
    (.letOp (n := 118) (.exec 0x107cd3 (fun s => s.RIP = 0x107cd3) (andR64R64Effect 0x107cd3 2 13) (Reg.operands [.gpr 2, .gpr 13] [])) #v[115, 71]
    (.letOp (n := 119) (.out 0x107cd6 (movR64R64Effect 0x107cd6 15 6) (EffectPart.reads (.reg (.gpr 15)) [.gpr 6] []) (.reg (.gpr 15))) #v[59]
    (.letOp (n := 120) (.exec 0x107cd6 (fun s => s.RIP = 0x107cd6) (movR64R64Effect 0x107cd6 15 6) (Reg.operands [.gpr 6] [])) #v[59]
    (.letOp (n := 121) (.out 0x107cd9 (rolR64Effect 0x107cd9 4 15 56) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[119]
    (.letOp (n := 122) (.exec 0x107cd9 (fun s => s.RIP = 0x107cd9) (rolR64Effect 0x107cd9 4 15 56) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[119]
    (.letOp (n := 123) (.out 0x107cdd (andR64R64Effect 0x107cdd 15 1) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 1] []) (.reg (.gpr 15))) #v[121, 79]
    (.letOp (n := 124) (.exec 0x107cdd (fun s => s.RIP = 0x107cdd) (andR64R64Effect 0x107cdd 15 1) (Reg.operands [.gpr 15, .gpr 1] [])) #v[121, 79]
    (.letOp (n := 125) (.out 0x107ce0 (orR64R64Effect 0x107ce0 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 2] []) (.reg (.gpr 15))) #v[123, 117]
    (.letOp (n := 126) (.exec 0x107ce0 (fun s => s.RIP = 0x107ce0) (orR64R64Effect 0x107ce0 15 2) (Reg.operands [.gpr 15, .gpr 2] [])) #v[123, 117]
    (.letOp (n := 127) (.out 0x107ce3 (movR64R64Effect 0x107ce3 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10] []) (.reg (.gpr 2))) #v[61]
    (.letOp (n := 128) (.exec 0x107ce3 (fun s => s.RIP = 0x107ce3) (movR64R64Effect 0x107ce3 2 10) (Reg.operands [.gpr 10] [])) #v[61]
    (.letOp (n := 129) (.exec 0x107ce6 (StorePre 0x107ce6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x107ce6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107ce6 10 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 130) (.out 0x107ceb (rolR64Effect 0x107ceb 4 10 40) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[61]
    (.letOp (n := 131) (.exec 0x107ceb (fun s => s.RIP = 0x107ceb) (rolR64Effect 0x107ceb 4 10 40) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[61]
    (b_l107c50_2)))))))))))))))))))))))))))))))))))))))

def bytes_l107c50_1 : List UInt8 :=
  [0x49, 0xC1, 0xC0, 0x38, 0x49, 0x21, 0xC8, 0x48, 0x89, 0xFA, 0x48, 0xC1, 0xC2, 0x28, 0x49, 0x09,
    0xC0, 0x48, 0x89, 0xF8, 0x48, 0xC1, 0xC0, 0x38, 0x4C, 0x21, 0xEA, 0x48, 0x21, 0xC8, 0x48, 0x09,
    0xD0, 0x48, 0x89, 0xF2, 0x48, 0xC1, 0xC2, 0x28, 0x4C, 0x21, 0xEA, 0x49, 0x89, 0xF7, 0x49, 0xC1,
    0xC7, 0x38, 0x49, 0x21, 0xCF, 0x49, 0x09, 0xD7, 0x4C, 0x89, 0xD2, 0x4C, 0x89, 0x54, 0x24, 0x78,
    0x49, 0xC1, 0xC2, 0x28] ++ bytes_l107c50_2

theorem code_l107c50_1 : ∀ x ∈ codeRange 0x107cab bytes_l107c50_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x7cab 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l107c50_2

@[cfg_block] def b_l107c50 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x107c50 (movR64M64Effect 0x107c50 3 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 54) (.exec 0x107c50 (LoadPre 0x107c50 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x107c50 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107c50 3 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x107c55 (movR64M64Effect 0x107c55 11 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 56) (.exec 0x107c55 (LoadPre 0x107c55 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x107c55 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107c55 11 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x107c5a (movR64M64Effect 0x107c5a 7 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 58) (.exec 0x107c5a (LoadPre 0x107c5a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x107c5a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107c5a 7 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x107c5f (movR64M64Effect 0x107c5f 6 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 60) (.exec 0x107c5f (LoadPre 0x107c5f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x107c5f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107c5f 6 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x107c64 (movR64M64Effect 0x107c64 10 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 62) (.exec 0x107c64 (LoadPre 0x107c64 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x107c64 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107c64 10 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x107c69 (movR64M64Effect 0x107c69 12 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 64) (.exec 0x107c69 (LoadPre 0x107c69 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x107c69 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107c69 12 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x107c6e (movR64M64Effect 0x107c6e 14 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 66) (.exec 0x107c6e (LoadPre 0x107c6e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x107c6e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107c6e 14 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x107c73 (movR64R64Effect 0x107c73 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 68) (.exec 0x107c73 (fun s => s.RIP = 0x107c73) (movR64R64Effect 0x107c73 0 3) (Reg.operands [.gpr 3] [])) #v[53]
    (.letOp (n := 69) (.out 0x107c76 (rolR64Effect 0x107c76 4 0 40) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[67]
    (.letOp (n := 70) (.exec 0x107c76 (fun s => s.RIP = 0x107c76) (rolR64Effect 0x107c76 4 0 40) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[67]
    (.letOp (n := 71) (.out 0x107c7a (movR64Imm64Effect 0x107c7a 13 0xff00ff00ff00ff) (EffectPart.reads (.reg (.gpr 13)) [] []) (.reg (.gpr 13))) #v[]
    (.letOp (n := 72) (.exec 0x107c7a (fun s => s.RIP = 0x107c7a) (movR64Imm64Effect 0x107c7a 13 0xff00ff00ff00ff) (Reg.operands [] [])) #v[]
    (.letOp (n := 73) (.out 0x107c84 (andR64R64Effect 0x107c84 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 13] []) (.reg (.gpr 0))) #v[69, 71]
    (.letOp (n := 74) (.exec 0x107c84 (fun s => s.RIP = 0x107c84) (andR64R64Effect 0x107c84 0 13) (Reg.operands [.gpr 0, .gpr 13] [])) #v[69, 71]
    (.letOp (n := 75) (.out 0x107c87 (movR64R64Effect 0x107c87 9 3) (EffectPart.reads (.reg (.gpr 9)) [.gpr 3] []) (.reg (.gpr 9))) #v[53]
    (.letOp (n := 76) (.exec 0x107c87 (fun s => s.RIP = 0x107c87) (movR64R64Effect 0x107c87 9 3) (Reg.operands [.gpr 3] [])) #v[53]
    (.letOp (n := 77) (.out 0x107c8a (rolR64Effect 0x107c8a 4 9 56) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[75]
    (.letOp (n := 78) (.exec 0x107c8a (fun s => s.RIP = 0x107c8a) (rolR64Effect 0x107c8a 4 9 56) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[75]
    (.letOp (n := 79) (.out 0x107c8e (movR64Imm64Effect 0x107c8e 1 0xff00ff00ff00ff00) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 80) (.exec 0x107c8e (fun s => s.RIP = 0x107c8e) (movR64Imm64Effect 0x107c8e 1 0xff00ff00ff00ff00) (Reg.operands [] [])) #v[]
    (.letOp (n := 81) (.out 0x107c98 (andR64R64Effect 0x107c98 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1] []) (.reg (.gpr 9))) #v[77, 79]
    (.letOp (n := 82) (.exec 0x107c98 (fun s => s.RIP = 0x107c98) (andR64R64Effect 0x107c98 9 1) (Reg.operands [.gpr 9, .gpr 1] [])) #v[77, 79]
    (.letOp (n := 83) (.out 0x107c9b (orR64R64Effect 0x107c9b 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0] []) (.reg (.gpr 9))) #v[81, 73]
    (.letOp (n := 84) (.exec 0x107c9b (fun s => s.RIP = 0x107c9b) (orR64R64Effect 0x107c9b 9 0) (Reg.operands [.gpr 9, .gpr 0] [])) #v[81, 73]
    (.letOp (n := 85) (.out 0x107c9e (movR64R64Effect 0x107c9e 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[55]
    (.letOp (n := 86) (.exec 0x107c9e (fun s => s.RIP = 0x107c9e) (movR64R64Effect 0x107c9e 0 11) (Reg.operands [.gpr 11] [])) #v[55]
    (.letOp (n := 87) (.out 0x107ca1 (rolR64Effect 0x107ca1 4 0 40) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[85]
    (.letOp (n := 88) (.exec 0x107ca1 (fun s => s.RIP = 0x107ca1) (rolR64Effect 0x107ca1 4 0 40) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[85]
    (.letOp (n := 89) (.out 0x107ca5 (andR64R64Effect 0x107ca5 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 13] []) (.reg (.gpr 0))) #v[87, 71]
    (.letOp (n := 90) (.exec 0x107ca5 (fun s => s.RIP = 0x107ca5) (andR64R64Effect 0x107ca5 0 13) (Reg.operands [.gpr 0, .gpr 13] [])) #v[87, 71]
    (.letOp (n := 91) (.out 0x107ca8 (movR64R64Effect 0x107ca8 8 11) (EffectPart.reads (.reg (.gpr 8)) [.gpr 11] []) (.reg (.gpr 8))) #v[55]
    (.letOp (n := 92) (.exec 0x107ca8 (fun s => s.RIP = 0x107ca8) (movR64R64Effect 0x107ca8 8 11) (Reg.operands [.gpr 11] [])) #v[55]
    (b_l107c50_1))))))))))))))))))))))))))))))))))))))))

def bytes_l107c50 : List UInt8 :=
  [0x48, 0x8B, 0x5C, 0x24, 0x08, 0x4C, 0x8B, 0x5C, 0x24, 0x10, 0x48, 0x8B, 0x7C, 0x24, 0x18, 0x48,
    0x8B, 0x74, 0x24, 0x20, 0x4C, 0x8B, 0x54, 0x24, 0x28, 0x4C, 0x8B, 0x64, 0x24, 0x30, 0x4C, 0x8B,
    0x74, 0x24, 0x38, 0x48, 0x89, 0xD8, 0x48, 0xC1, 0xC0, 0x28, 0x49, 0xBD, 0xFF, 0x00, 0xFF, 0x00,
    0xFF, 0x00, 0xFF, 0x00, 0x4C, 0x21, 0xE8, 0x49, 0x89, 0xD9, 0x49, 0xC1, 0xC1, 0x38, 0x48, 0xB9,
    0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x49, 0x21, 0xC9, 0x49, 0x09, 0xC1, 0x4C, 0x89,
    0xD8, 0x48, 0xC1, 0xC0, 0x28, 0x4C, 0x21, 0xE8, 0x4D, 0x89, 0xD8] ++ bytes_l107c50_1

theorem code_l107c50 : ∀ x ∈ codeRange 0x107c50 bytes_l107c50, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x7c50 91 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l107c50_1

@[cfg_block] def b_l107e96 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x107e96 (movR64R64Effect 0x107e96 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 54) (.exec 0x107e96 (fun s => s.RIP = 0x107e96) (movR64R64Effect 0x107e96 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x107e99 (callEffect (fun _ => 0x100830) 0x107e9e) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 56) (.exec 0x107e99 (PushPre 0x107e99 5) (callEffect (fun _ => 0x100830) 0x107e9e) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.const ⟨64, 0x107e9e⟩) #v[]
    (.terminate (.call ⟨.l100830, RegMap.args [(3, 3), (4, 55), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ { target := .l107e9e, kept := #v[], arity := rfl, guard := some (Fin.last 57) }))))))

def bytes_l107e96 : List UInt8 :=
  [0x48, 0x89, 0xDF, 0xE8, 0x92, 0x89, 0xFF, 0xFF]

theorem code_l107e96 : ∀ x ∈ codeRange 0x107e96 bytes_l107e96, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x7e96 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l107e9e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x107e9e (movR64M64Effect 0x107e9e 0 (.sib 4 (some 5) 3 (.d32 0x218))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4, .gpr 5] []) (.reg (.gpr 0))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x107e9e (LoadPre 0x107e9e (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x218)) s (0x107e9e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107e9e 0 (.sib 4 (some 5) 3 (.d32 0x218))) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.exec 0x107ea6 (StorePre 0x107ea6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x107ea6 + BitVec.ofNat 64 5)) 8) (xorMREffect 0x107ea6 5 64 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x107eab (movR64M64Effect 0x107eab 0 (.sib 4 (some 5) 3 (.d32 0x220))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4, .gpr 5] []) (.reg (.gpr 0))) #v[4, 5]
    (.letOp (n := 57) (.exec 0x107eab (LoadPre 0x107eab (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x220)) s (0x107eab + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107eab 0 (.sib 4 (some 5) 3 (.d32 0x220))) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 58) (.exec 0x107eb3 (StorePre 0x107eb3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x107eb3 + BitVec.ofNat 64 5)) 8) (xorMREffect 0x107eb3 5 64 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x107eb8 (movR64M64Effect 0x107eb8 0 (.sib 4 (some 5) 3 (.d32 0x228))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4, .gpr 5] []) (.reg (.gpr 0))) #v[4, 5]
    (.letOp (n := 60) (.exec 0x107eb8 (LoadPre 0x107eb8 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x228)) s (0x107eb8 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107eb8 0 (.sib 4 (some 5) 3 (.d32 0x228))) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 61) (.exec 0x107ec0 (StorePre 0x107ec0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x107ec0 + BitVec.ofNat 64 5)) 8) (xorMREffect 0x107ec0 5 64 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x107ec5 (movR64M64Effect 0x107ec5 0 (.sib 4 (some 5) 3 (.d32 0x230))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4, .gpr 5] []) (.reg (.gpr 0))) #v[4, 5]
    (.letOp (n := 63) (.exec 0x107ec5 (LoadPre 0x107ec5 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x230)) s (0x107ec5 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107ec5 0 (.sib 4 (some 5) 3 (.d32 0x230))) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 64) (.exec 0x107ecd (StorePre 0x107ecd 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x107ecd + BitVec.ofNat 64 5)) 8) (xorMREffect 0x107ecd 5 64 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x107ed2 (movR64M64Effect 0x107ed2 0 (.sib 4 (some 5) 3 (.d32 0x238))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4, .gpr 5] []) (.reg (.gpr 0))) #v[4, 5]
    (.letOp (n := 66) (.exec 0x107ed2 (LoadPre 0x107ed2 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x238)) s (0x107ed2 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107ed2 0 (.sib 4 (some 5) 3 (.d32 0x238))) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 67) (.exec 0x107eda (StorePre 0x107eda 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x107eda + BitVec.ofNat 64 5)) 8) (xorMREffect 0x107eda 5 64 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x107edf (movR64M64Effect 0x107edf 0 (.sib 4 (some 5) 3 (.d32 0x240))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4, .gpr 5] []) (.reg (.gpr 0))) #v[4, 5]
    (.letOp (n := 69) (.exec 0x107edf (LoadPre 0x107edf (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x240)) s (0x107edf + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107edf 0 (.sib 4 (some 5) 3 (.d32 0x240))) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 70) (.exec 0x107ee7 (StorePre 0x107ee7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x107ee7 + BitVec.ofNat 64 5)) 8) (xorMREffect 0x107ee7 5 64 0 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[68, 4]
    (.letOp (n := 71) (.out 0x107eec (movR64M64Effect 0x107eec 0 (.sib 4 (some 5) 3 (.d32 0x248))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4, .gpr 5] []) (.reg (.gpr 0))) #v[4, 5]
    (.letOp (n := 72) (.exec 0x107eec (LoadPre 0x107eec (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x248)) s (0x107eec + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107eec 0 (.sib 4 (some 5) 3 (.d32 0x248))) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 73) (.exec 0x107ef4 (StorePre 0x107ef4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x107ef4 + BitVec.ofNat 64 5)) 8) (xorMREffect 0x107ef4 5 64 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[71, 4]
    (.letOp (n := 74) (.out 0x107ef9 (movR64M64Effect 0x107ef9 0 (.sib 4 (some 5) 3 (.d32 0x250))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4, .gpr 5] []) (.reg (.gpr 0))) #v[4, 5]
    (.letOp (n := 75) (.exec 0x107ef9 (LoadPre 0x107ef9 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x250)) s (0x107ef9 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107ef9 0 (.sib 4 (some 5) 3 (.d32 0x250))) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 76) (.exec 0x107f01 (StorePre 0x107f01 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x107f01 + BitVec.ofNat 64 5)) 8) (xorMREffect 0x107f01 5 64 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[74, 4]
    (.letOp (n := 77) (.out 0x107f06 (movR32Imm32Effect 0x107f06 5 6 0x8) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 78) (.exec 0x107f06 (fun s => s.RIP = 0x107f06) (movR32Imm32Effect 0x107f06 5 6 0x8) (Reg.operands [] [])) #v[]
    (.letOp (n := 79) (.out 0x107f0b (movR64R64Effect 0x107f0b 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 80) (.exec 0x107f0b (fun s => s.RIP = 0x107f0b) (movR64R64Effect 0x107f0b 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 81) (.out 0x107f0e (callEffect (fun _ => 0x100e90) 0x107f13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 82) (.exec 0x107f0e (PushPre 0x107f0e 5) (callEffect (fun _ => 0x100e90) 0x107f13) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 83) (.const ⟨64, 0x107f13⟩) #v[]
    (.terminate (.call ⟨.l100e90, RegMap.args [(0, 74), (3, 3), (4, 81), (5, 5), (6, 77), (7, 79), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 84⟩ { target := .l107f13, kept := #v[], arity := rfl, guard := some (Fin.last 83) }))))))))))))))))))))))))))))))))

def bytes_l107e9e : List UInt8 :=
  [0x48, 0x8B, 0x84, 0xEC, 0x18, 0x02, 0x00, 0x00, 0x48, 0x31, 0x44, 0x24, 0x08, 0x48, 0x8B, 0x84,
    0xEC, 0x20, 0x02, 0x00, 0x00, 0x48, 0x31, 0x44, 0x24, 0x10, 0x48, 0x8B, 0x84, 0xEC, 0x28, 0x02,
    0x00, 0x00, 0x48, 0x31, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x84, 0xEC, 0x30, 0x02, 0x00, 0x00, 0x48,
    0x31, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x84, 0xEC, 0x38, 0x02, 0x00, 0x00, 0x48, 0x31, 0x44, 0x24,
    0x28, 0x48, 0x8B, 0x84, 0xEC, 0x40, 0x02, 0x00, 0x00, 0x48, 0x31, 0x44, 0x24, 0x30, 0x48, 0x8B,
    0x84, 0xEC, 0x48, 0x02, 0x00, 0x00, 0x48, 0x31, 0x44, 0x24, 0x38, 0x48, 0x8B, 0x84, 0xEC, 0x50,
    0x02, 0x00, 0x00, 0x48, 0x31, 0x44, 0x24, 0x40, 0xBE, 0x08, 0x00, 0x00, 0x00, 0x48, 0x89, 0xDF,
    0xE8, 0x7D, 0x8F, 0xFF, 0xFF]

theorem code_l107e9e : ∀ x ∈ codeRange 0x107e9e bytes_l107e9e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x7e9e 117 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l107f13_4 : Block Op Label signature Reg.count 205 :=
  .letOp (n := 205) (.out 0x108056 (addR64Imm8Effect 0x108056 5 0x20) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5] []) (.reg (.gpr 5))) #v[5]
    (.letOp (n := 206) (.exec 0x108056 (fun s => s.RIP = 0x108056) (addR64Imm8Effect 0x108056 5 0x20) (Reg.operands [.gpr 5] [])) #v[5]
    (.terminate (.br ⟨.l107b80, RegMap.args [(0, 198), (1, 193), (2, 89), (3, 202), (4, 4), (5, 205), (6, 191), (7, 176), (8, 151), (9, 167), (10, 71), (11, 149), (12, 135), (13, 156), (14, 137), (15, 165), (22, 22), (39, 39), (50, 50), (51, 51)] 207⟩)))

def bytes_l107f13_4 : List UInt8 :=
  [0x48, 0x83, 0xC5, 0x20, 0xE9, 0x21, 0xFB, 0xFF, 0xFF]

theorem code_l107f13_4 : ∀ x ∈ codeRange 0x108056 bytes_l107f13_4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x8056 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l107f13_3 : Block Op Label signature Reg.count 169 :=
  .letOp (n := 169) (.exec 0x107fff (StorePre 0x107fff 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x107fff + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107fff 9 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[167, 4]
    (.letOp (n := 170) (.out 0x108004 (movR64R64Effect 0x108004 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 1] []) (.reg (.gpr 6))) #v[99]
    (.letOp (n := 171) (.exec 0x108004 (fun s => s.RIP = 0x108004) (movR64R64Effect 0x108004 6 1) (Reg.operands [.gpr 1] [])) #v[99]
    (.letOp (n := 172) (.out 0x108007 (rolR64Effect 0x108007 4 6 32) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[170]
    (.letOp (n := 173) (.exec 0x108007 (fun s => s.RIP = 0x108007) (rolR64Effect 0x108007 4 6 32) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[170]
    (.letOp (n := 174) (.out 0x10800b (xorR64M64Effect 0x10800b 6 (.sib 4 (some 5) 3 (.d32 0x278))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 4, .gpr 5] []) (.reg (.gpr 6))) #v[172, 4, 5]
    (.letOp (n := 175) (.exec 0x10800b (LoadPre 0x10800b (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x278)) s (0x10800b + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x10800b 6 (.sib 4 (some 5) 3 (.d32 0x278))) (Reg.operands [.gpr 6, .gpr 4, .gpr 5] [])) #v[172, 4, 5]
    (.letOp (n := 176) (.out 0x108013 (xorR64R64Effect 0x108013 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[127, 174]
    (.letOp (n := 177) (.exec 0x108013 (fun s => s.RIP = 0x108013) (xorR64R64Effect 0x108013 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[127, 174]
    (.letOp (n := 178) (.exec 0x108016 (StorePre 0x108016 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x108016 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108016 7 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[176, 4]
    (.letOp (n := 179) (.out 0x10801b (movR64R64Effect 0x10801b 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[141]
    (.letOp (n := 180) (.exec 0x10801b (fun s => s.RIP = 0x10801b) (movR64R64Effect 0x10801b 6 3) (Reg.operands [.gpr 3] [])) #v[141]
    (.letOp (n := 181) (.out 0x10801e (rolR64Effect 0x10801e 4 6 48) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[179]
    (.letOp (n := 182) (.exec 0x10801e (fun s => s.RIP = 0x10801e) (rolR64Effect 0x10801e 4 6 48) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[179]
    (.letOp (n := 183) (.out 0x108022 (xorR64R64Effect 0x108022 3 6) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 6] []) (.reg (.gpr 3))) #v[141, 181]
    (.letOp (n := 184) (.exec 0x108022 (fun s => s.RIP = 0x108022) (xorR64R64Effect 0x108022 3 6) (Reg.operands [.gpr 3, .gpr 6] [])) #v[141, 181]
    (.letOp (n := 185) (.out 0x108025 (xorR64R64Effect 0x108025 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[99, 181]
    (.letOp (n := 186) (.exec 0x108025 (fun s => s.RIP = 0x108025) (xorR64R64Effect 0x108025 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[99, 181]
    (.letOp (n := 187) (.out 0x108028 (movR64R64Effect 0x108028 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[183]
    (.letOp (n := 188) (.exec 0x108028 (fun s => s.RIP = 0x108028) (movR64R64Effect 0x108028 6 3) (Reg.operands [.gpr 3] [])) #v[183]
    (.letOp (n := 189) (.out 0x10802b (rolR64Effect 0x10802b 4 6 32) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[187]
    (.letOp (n := 190) (.exec 0x10802b (fun s => s.RIP = 0x10802b) (rolR64Effect 0x10802b 4 6 32) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[187]
    (.letOp (n := 191) (.out 0x10802f (xorR64M64Effect 0x10802f 6 (.sib 4 (some 5) 3 (.d32 0x280))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 4, .gpr 5] []) (.reg (.gpr 6))) #v[189, 4, 5]
    (.letOp (n := 192) (.exec 0x10802f (LoadPre 0x10802f (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x280)) s (0x10802f + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x10802f 6 (.sib 4 (some 5) 3 (.d32 0x280))) (Reg.operands [.gpr 6, .gpr 4, .gpr 5] [])) #v[189, 4, 5]
    (.letOp (n := 193) (.out 0x108037 (xorR64R64Effect 0x108037 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[185, 191]
    (.letOp (n := 194) (.exec 0x108037 (fun s => s.RIP = 0x108037) (xorR64R64Effect 0x108037 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[185, 191]
    (.letOp (n := 195) (.exec 0x10803a (StorePre 0x10803a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10803a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10803a 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[193, 4]
    (.letOp (n := 196) (.out 0x10803f (rolR64Effect 0x10803f 4 0 32) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[131]
    (.letOp (n := 197) (.exec 0x10803f (fun s => s.RIP = 0x10803f) (rolR64Effect 0x10803f 4 0 32) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[131]
    (.letOp (n := 198) (.out 0x108043 (xorR64M64Effect 0x108043 0 (.sib 4 (some 5) 3 (.d32 0x288))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4, .gpr 5] []) (.reg (.gpr 0))) #v[196, 4, 5]
    (.letOp (n := 199) (.exec 0x108043 (LoadPre 0x108043 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x288)) s (0x108043 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x108043 0 (.sib 4 (some 5) 3 (.d32 0x288))) (Reg.operands [.gpr 0, .gpr 4, .gpr 5] [])) #v[196, 4, 5]
    (.letOp (n := 200) (.out 0x10804b (xorR64R64Effect 0x10804b 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 2] []) (.reg (.gpr 3))) #v[183, 89]
    (.letOp (n := 201) (.exec 0x10804b (fun s => s.RIP = 0x10804b) (xorR64R64Effect 0x10804b 3 2) (Reg.operands [.gpr 3, .gpr 2] [])) #v[183, 89]
    (.letOp (n := 202) (.out 0x10804e (xorR64R64Effect 0x10804e 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0] []) (.reg (.gpr 3))) #v[200, 198]
    (.letOp (n := 203) (.exec 0x10804e (fun s => s.RIP = 0x10804e) (xorR64R64Effect 0x10804e 3 0) (Reg.operands [.gpr 3, .gpr 0] [])) #v[200, 198]
    (.letOp (n := 204) (.exec 0x108051 (StorePre 0x108051 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x108051 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108051 3 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[202, 4]
    (b_l107f13_4))))))))))))))))))))))))))))))))))))

def bytes_l107f13_3 : List UInt8 :=
  [0x4C, 0x89, 0x4C, 0x24, 0x20, 0x48, 0x89, 0xCE, 0x48, 0xC1, 0xC6, 0x20, 0x48, 0x33, 0xB4, 0xEC,
    0x78, 0x02, 0x00, 0x00, 0x48, 0x31, 0xF7, 0x48, 0x89, 0x7C, 0x24, 0x28, 0x48, 0x89, 0xDE, 0x48,
    0xC1, 0xC6, 0x30, 0x48, 0x31, 0xF3, 0x48, 0x31, 0xF1, 0x48, 0x89, 0xDE, 0x48, 0xC1, 0xC6, 0x20,
    0x48, 0x33, 0xB4, 0xEC, 0x80, 0x02, 0x00, 0x00, 0x48, 0x31, 0xF1, 0x48, 0x89, 0x4C, 0x24, 0x30,
    0x48, 0xC1, 0xC0, 0x20, 0x48, 0x33, 0x84, 0xEC, 0x88, 0x02, 0x00, 0x00, 0x48, 0x31, 0xD3, 0x48,
    0x31, 0xC3, 0x48, 0x89, 0x5C, 0x24, 0x38] ++ bytes_l107f13_4

theorem code_l107f13_3 : ∀ x ∈ codeRange 0x107fff bytes_l107f13_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x7fff 87 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l107f13_4

@[cfg_block] def b_l107f13_2 : Block Op Label signature Reg.count 133 :=
  .letOp (n := 133) (.out 0x107fa2 (xorR64R64Effect 0x107fa2 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 0] []) (.reg (.gpr 14))) #v[115, 131]
    (.letOp (n := 134) (.exec 0x107fa2 (fun s => s.RIP = 0x107fa2) (xorR64R64Effect 0x107fa2 14 0) (Reg.operands [.gpr 14, .gpr 0] [])) #v[115, 131]
    (.letOp (n := 135) (.out 0x107fa5 (xorR64M64Effect 0x107fa5 12 (.sib 4 (some 5) 3 (.d32 0x258))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 4, .gpr 5] []) (.reg (.gpr 12))) #v[117, 4, 5]
    (.letOp (n := 136) (.exec 0x107fa5 (LoadPre 0x107fa5 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x258)) s (0x107fa5 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x107fa5 12 (.sib 4 (some 5) 3 (.d32 0x258))) (Reg.operands [.gpr 12, .gpr 4, .gpr 5] [])) #v[117, 4, 5]
    (.letOp (n := 137) (.out 0x107fad (xorR64R64Effect 0x107fad 14 3) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 3] []) (.reg (.gpr 14))) #v[133, 129]
    (.letOp (n := 138) (.exec 0x107fad (fun s => s.RIP = 0x107fad) (xorR64R64Effect 0x107fad 14 3) (Reg.operands [.gpr 14, .gpr 3] [])) #v[133, 129]
    (.letOp (n := 139) (.out 0x107fb0 (xorR64R64Effect 0x107fb0 11 12) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 12] []) (.reg (.gpr 11))) #v[121, 135]
    (.letOp (n := 140) (.exec 0x107fb0 (fun s => s.RIP = 0x107fb0) (xorR64R64Effect 0x107fb0 11 12) (Reg.operands [.gpr 11, .gpr 12] [])) #v[121, 135]
    (.letOp (n := 141) (.out 0x107fb3 (movR64M64Effect 0x107fb3 3 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 142) (.exec 0x107fb3 (LoadPre 0x107fb3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x107fb3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107fb3 3 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 143) (.exec 0x107fb8 (StorePre 0x107fb8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x107fb8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107fb8 14 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[137, 4]
    (.letOp (n := 144) (.exec 0x107fbd (StorePre 0x107fbd 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x107fbd + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107fbd 11 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[139, 4]
    (.letOp (n := 145) (.out 0x107fc2 (movR64R64Effect 0x107fc2 11 6) (EffectPart.reads (.reg (.gpr 11)) [.gpr 6] []) (.reg (.gpr 11))) #v[93]
    (.letOp (n := 146) (.exec 0x107fc2 (fun s => s.RIP = 0x107fc2) (movR64R64Effect 0x107fc2 11 6) (Reg.operands [.gpr 6] [])) #v[93]
    (.letOp (n := 147) (.out 0x107fc5 (rolR64Effect 0x107fc5 4 11 32) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[145]
    (.letOp (n := 148) (.exec 0x107fc5 (fun s => s.RIP = 0x107fc5) (rolR64Effect 0x107fc5 4 11 32) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[145]
    (.letOp (n := 149) (.out 0x107fc9 (xorR64M64Effect 0x107fc9 11 (.sib 4 (some 5) 3 (.d32 0x260))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 4, .gpr 5] []) (.reg (.gpr 11))) #v[147, 4, 5]
    (.letOp (n := 150) (.exec 0x107fc9 (LoadPre 0x107fc9 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x260)) s (0x107fc9 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x107fc9 11 (.sib 4 (some 5) 3 (.d32 0x260))) (Reg.operands [.gpr 11, .gpr 4, .gpr 5] [])) #v[147, 4, 5]
    (.letOp (n := 151) (.out 0x107fd1 (xorR64R64Effect 0x107fd1 8 11) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 11] []) (.reg (.gpr 8))) #v[123, 149]
    (.letOp (n := 152) (.exec 0x107fd1 (fun s => s.RIP = 0x107fd1) (xorR64R64Effect 0x107fd1 8 11) (Reg.operands [.gpr 8, .gpr 11] [])) #v[123, 149]
    (.letOp (n := 153) (.exec 0x107fd4 (StorePre 0x107fd4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x107fd4 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107fd4 8 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[151, 4]
    (.letOp (n := 154) (.out 0x107fd9 (rolR64Effect 0x107fd9 4 13 32) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[105]
    (.letOp (n := 155) (.exec 0x107fd9 (fun s => s.RIP = 0x107fd9) (rolR64Effect 0x107fd9 4 13 32) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[105]
    (.letOp (n := 156) (.out 0x107fdd (xorR64M64Effect 0x107fdd 13 (.sib 4 (some 5) 3 (.d32 0x268))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 4, .gpr 5] []) (.reg (.gpr 13))) #v[154, 4, 5]
    (.letOp (n := 157) (.exec 0x107fdd (LoadPre 0x107fdd (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x268)) s (0x107fdd + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x107fdd 13 (.sib 4 (some 5) 3 (.d32 0x268))) (Reg.operands [.gpr 13, .gpr 4, .gpr 5] [])) #v[154, 4, 5]
    (.letOp (n := 158) (.out 0x107fe5 (xorR64R64Effect 0x107fe5 6 10) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 10] []) (.reg (.gpr 6))) #v[93, 71]
    (.letOp (n := 159) (.exec 0x107fe5 (fun s => s.RIP = 0x107fe5) (xorR64R64Effect 0x107fe5 6 10) (Reg.operands [.gpr 6, .gpr 10] [])) #v[93, 71]
    (.letOp (n := 160) (.out 0x107fe8 (xorR64R64Effect 0x107fe8 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 13] []) (.reg (.gpr 6))) #v[158, 156]
    (.letOp (n := 161) (.exec 0x107fe8 (fun s => s.RIP = 0x107fe8) (xorR64R64Effect 0x107fe8 6 13) (Reg.operands [.gpr 6, .gpr 13] [])) #v[158, 156]
    (.letOp (n := 162) (.out 0x107feb (rolR64Effect 0x107feb 4 15 32) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[109]
    (.letOp (n := 163) (.exec 0x107feb (fun s => s.RIP = 0x107feb) (rolR64Effect 0x107feb 4 15 32) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[109]
    (.letOp (n := 164) (.exec 0x107fef (StorePre 0x107fef 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x107fef + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107fef 6 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[160, 4]
    (.letOp (n := 165) (.out 0x107ff4 (xorR64M64Effect 0x107ff4 15 (.sib 4 (some 5) 3 (.d32 0x270))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 4, .gpr 5] []) (.reg (.gpr 15))) #v[162, 4, 5]
    (.letOp (n := 166) (.exec 0x107ff4 (LoadPre 0x107ff4 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x270)) s (0x107ff4 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x107ff4 15 (.sib 4 (some 5) 3 (.d32 0x270))) (Reg.operands [.gpr 15, .gpr 4, .gpr 5] [])) #v[162, 4, 5]
    (.letOp (n := 167) (.out 0x107ffc (xorR64R64Effect 0x107ffc 9 15) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 15] []) (.reg (.gpr 9))) #v[125, 165]
    (.letOp (n := 168) (.exec 0x107ffc (fun s => s.RIP = 0x107ffc) (xorR64R64Effect 0x107ffc 9 15) (Reg.operands [.gpr 9, .gpr 15] [])) #v[125, 165]
    (b_l107f13_3))))))))))))))))))))))))))))))))))))

def bytes_l107f13_2 : List UInt8 :=
  [0x49, 0x31, 0xC6, 0x4C, 0x33, 0xA4, 0xEC, 0x58, 0x02, 0x00, 0x00, 0x49, 0x31, 0xDE, 0x4D, 0x31,
    0xE3, 0x48, 0x8B, 0x5C, 0x24, 0x30, 0x4C, 0x89, 0x74, 0x24, 0x40, 0x4C, 0x89, 0x5C, 0x24, 0x08,
    0x49, 0x89, 0xF3, 0x49, 0xC1, 0xC3, 0x20, 0x4C, 0x33, 0x9C, 0xEC, 0x60, 0x02, 0x00, 0x00, 0x4D,
    0x31, 0xD8, 0x4C, 0x89, 0x44, 0x24, 0x10, 0x49, 0xC1, 0xC5, 0x20, 0x4C, 0x33, 0xAC, 0xEC, 0x68,
    0x02, 0x00, 0x00, 0x4C, 0x31, 0xD6, 0x4C, 0x31, 0xEE, 0x49, 0xC1, 0xC7, 0x20, 0x48, 0x89, 0x74,
    0x24, 0x18, 0x4C, 0x33, 0xBC, 0xEC, 0x70, 0x02, 0x00, 0x00, 0x4D, 0x31, 0xF9] ++ bytes_l107f13_3

theorem code_l107f13_2 : ∀ x ∈ codeRange 0x107fa2 bytes_l107f13_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x7fa2 93 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l107f13_3

@[cfg_block] def b_l107f13_1 : Block Op Label signature Reg.count 93 :=
  .letOp (n := 93) (.out 0x107f63 (xorR64R64Effect 0x107f63 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 13] []) (.reg (.gpr 6))) #v[55, 65]
    (.letOp (n := 94) (.exec 0x107f63 (fun s => s.RIP = 0x107f63) (xorR64R64Effect 0x107f63 6 13) (Reg.operands [.gpr 6, .gpr 13] [])) #v[55, 65]
    (.letOp (n := 95) (.out 0x107f66 (xorR64R64Effect 0x107f66 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[61, 71]
    (.letOp (n := 96) (.exec 0x107f66 (fun s => s.RIP = 0x107f66) (xorR64R64Effect 0x107f66 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[61, 71]
    (.letOp (n := 97) (.out 0x107f69 (xorR64R64Effect 0x107f69 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 15] []) (.reg (.gpr 7))) #v[67, 77]
    (.letOp (n := 98) (.exec 0x107f69 (fun s => s.RIP = 0x107f69) (xorR64R64Effect 0x107f69 7 15) (Reg.operands [.gpr 7, .gpr 15] [])) #v[67, 77]
    (.letOp (n := 99) (.out 0x107f6c (xorR64R64Effect 0x107f6c 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 14] []) (.reg (.gpr 1))) #v[73, 83]
    (.letOp (n := 100) (.exec 0x107f6c (fun s => s.RIP = 0x107f6c) (xorR64R64Effect 0x107f6c 1 14) (Reg.operands [.gpr 1, .gpr 14] [])) #v[73, 83]
    (.letOp (n := 101) (.out 0x107f6f (movR64R64Effect 0x107f6f 12 8) (EffectPart.reads (.reg (.gpr 12)) [.gpr 8] []) (.reg (.gpr 12))) #v[91]
    (.letOp (n := 102) (.exec 0x107f6f (fun s => s.RIP = 0x107f6f) (movR64R64Effect 0x107f6f 12 8) (Reg.operands [.gpr 8] [])) #v[91]
    (.letOp (n := 103) (.out 0x107f72 (xorR64R64Effect 0x107f72 8 13) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 13] []) (.reg (.gpr 8))) #v[91, 65]
    (.letOp (n := 104) (.exec 0x107f72 (fun s => s.RIP = 0x107f72) (xorR64R64Effect 0x107f72 8 13) (Reg.operands [.gpr 8, .gpr 13] [])) #v[91, 65]
    (.letOp (n := 105) (.out 0x107f75 (movR64R64Effect 0x107f75 13 9) (EffectPart.reads (.reg (.gpr 13)) [.gpr 9] []) (.reg (.gpr 13))) #v[95]
    (.letOp (n := 106) (.exec 0x107f75 (fun s => s.RIP = 0x107f75) (movR64R64Effect 0x107f75 13 9) (Reg.operands [.gpr 9] [])) #v[95]
    (.letOp (n := 107) (.out 0x107f78 (xorR64R64Effect 0x107f78 9 15) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 15] []) (.reg (.gpr 9))) #v[95, 77]
    (.letOp (n := 108) (.exec 0x107f78 (fun s => s.RIP = 0x107f78) (xorR64R64Effect 0x107f78 9 15) (Reg.operands [.gpr 9, .gpr 15] [])) #v[95, 77]
    (.letOp (n := 109) (.out 0x107f7b (movR64R64Effect 0x107f7b 15 7) (EffectPart.reads (.reg (.gpr 15)) [.gpr 7] []) (.reg (.gpr 15))) #v[97]
    (.letOp (n := 110) (.exec 0x107f7b (fun s => s.RIP = 0x107f7b) (movR64R64Effect 0x107f7b 15 7) (Reg.operands [.gpr 7] [])) #v[97]
    (.letOp (n := 111) (.out 0x107f7e (xorR64R64Effect 0x107f7e 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 14] []) (.reg (.gpr 7))) #v[97, 83]
    (.letOp (n := 112) (.exec 0x107f7e (fun s => s.RIP = 0x107f7e) (xorR64R64Effect 0x107f7e 7 14) (Reg.operands [.gpr 7, .gpr 14] [])) #v[97, 83]
    (.letOp (n := 113) (.out 0x107f81 (movR64R64Effect 0x107f81 14 3) (EffectPart.reads (.reg (.gpr 14)) [.gpr 3] []) (.reg (.gpr 14))) #v[85]
    (.letOp (n := 114) (.exec 0x107f81 (fun s => s.RIP = 0x107f81) (movR64R64Effect 0x107f81 14 3) (Reg.operands [.gpr 3] [])) #v[85]
    (.letOp (n := 115) (.out 0x107f84 (rolR64Effect 0x107f84 4 14 48) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[113]
    (.letOp (n := 116) (.exec 0x107f84 (fun s => s.RIP = 0x107f84) (rolR64Effect 0x107f84 4 14 48) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[113]
    (.letOp (n := 117) (.out 0x107f88 (rolR64Effect 0x107f88 4 12 32) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[101]
    (.letOp (n := 118) (.exec 0x107f88 (fun s => s.RIP = 0x107f88) (rolR64Effect 0x107f88 4 12 32) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[101]
    (.letOp (n := 119) (.out 0x107f8c (xorR64R64Effect 0x107f8c 3 14) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 14] []) (.reg (.gpr 3))) #v[85, 115]
    (.letOp (n := 120) (.exec 0x107f8c (fun s => s.RIP = 0x107f8c) (xorR64R64Effect 0x107f8c 3 14) (Reg.operands [.gpr 3, .gpr 14] [])) #v[85, 115]
    (.letOp (n := 121) (.out 0x107f8f (xorR64R64Effect 0x107f8f 11 3) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 3] []) (.reg (.gpr 11))) #v[59, 119]
    (.letOp (n := 122) (.exec 0x107f8f (fun s => s.RIP = 0x107f8f) (xorR64R64Effect 0x107f8f 11 3) (Reg.operands [.gpr 11, .gpr 3] [])) #v[59, 119]
    (.letOp (n := 123) (.out 0x107f92 (xorR64R64Effect 0x107f92 8 3) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 3] []) (.reg (.gpr 8))) #v[103, 119]
    (.letOp (n := 124) (.exec 0x107f92 (fun s => s.RIP = 0x107f92) (xorR64R64Effect 0x107f92 8 3) (Reg.operands [.gpr 8, .gpr 3] [])) #v[103, 119]
    (.letOp (n := 125) (.out 0x107f95 (xorR64R64Effect 0x107f95 9 3) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 3] []) (.reg (.gpr 9))) #v[107, 119]
    (.letOp (n := 126) (.exec 0x107f95 (fun s => s.RIP = 0x107f95) (xorR64R64Effect 0x107f95 9 3) (Reg.operands [.gpr 9, .gpr 3] [])) #v[107, 119]
    (.letOp (n := 127) (.out 0x107f98 (xorR64R64Effect 0x107f98 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 3] []) (.reg (.gpr 7))) #v[111, 119]
    (.letOp (n := 128) (.exec 0x107f98 (fun s => s.RIP = 0x107f98) (xorR64R64Effect 0x107f98 7 3) (Reg.operands [.gpr 7, .gpr 3] [])) #v[111, 119]
    (.letOp (n := 129) (.out 0x107f9b (rolR64Effect 0x107f9b 4 3 32) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[119]
    (.letOp (n := 130) (.exec 0x107f9b (fun s => s.RIP = 0x107f9b) (rolR64Effect 0x107f9b 4 3 32) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[119]
    (.letOp (n := 131) (.out 0x107f9f (xorR64R64Effect 0x107f9f 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[79, 89]
    (.letOp (n := 132) (.exec 0x107f9f (fun s => s.RIP = 0x107f9f) (xorR64R64Effect 0x107f9f 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[79, 89]
    (b_l107f13_2))))))))))))))))))))))))))))))))))))))))

def bytes_l107f13_1 : List UInt8 :=
  [0x4C, 0x31, 0xEE, 0x4D, 0x31, 0xD1, 0x4C, 0x31, 0xFF, 0x4C, 0x31, 0xF1, 0x4D, 0x89, 0xC4, 0x4D,
    0x31, 0xE8, 0x4D, 0x89, 0xCD, 0x4D, 0x31, 0xF9, 0x49, 0x89, 0xFF, 0x4C, 0x31, 0xF7, 0x49, 0x89,
    0xDE, 0x49, 0xC1, 0xC6, 0x30, 0x49, 0xC1, 0xC4, 0x20, 0x4C, 0x31, 0xF3, 0x49, 0x31, 0xDB, 0x49,
    0x31, 0xD8, 0x49, 0x31, 0xD9, 0x48, 0x31, 0xDF, 0x48, 0xC1, 0xC3, 0x20, 0x48, 0x31, 0xD0] ++ bytes_l107f13_2

theorem code_l107f13_1 : ∀ x ∈ codeRange 0x107f63 bytes_l107f13_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x7f63 63 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l107f13_2

@[cfg_block] def b_l107f13 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x107f13 (movR64M64Effect 0x107f13 8 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 54) (.exec 0x107f13 (LoadPre 0x107f13 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x107f13 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107f13 8 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x107f18 (movR64M64Effect 0x107f18 6 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 56) (.exec 0x107f18 (LoadPre 0x107f18 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x107f18 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107f18 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x107f1d (movR64R64Effect 0x107f1d 11 8) (EffectPart.reads (.reg (.gpr 11)) [.gpr 8] []) (.reg (.gpr 11))) #v[53]
    (.letOp (n := 58) (.exec 0x107f1d (fun s => s.RIP = 0x107f1d) (movR64R64Effect 0x107f1d 11 8) (Reg.operands [.gpr 8] [])) #v[53]
    (.letOp (n := 59) (.out 0x107f20 (rolR64Effect 0x107f20 4 11 48) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[57]
    (.letOp (n := 60) (.exec 0x107f20 (fun s => s.RIP = 0x107f20) (rolR64Effect 0x107f20 4 11 48) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[57]
    (.letOp (n := 61) (.out 0x107f24 (movR64M64Effect 0x107f24 9 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 62) (.exec 0x107f24 (LoadPre 0x107f24 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x107f24 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107f24 9 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x107f29 (movR64R64Effect 0x107f29 13 6) (EffectPart.reads (.reg (.gpr 13)) [.gpr 6] []) (.reg (.gpr 13))) #v[55]
    (.letOp (n := 64) (.exec 0x107f29 (fun s => s.RIP = 0x107f29) (movR64R64Effect 0x107f29 13 6) (Reg.operands [.gpr 6] [])) #v[55]
    (.letOp (n := 65) (.out 0x107f2c (rolR64Effect 0x107f2c 4 13 48) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[63]
    (.letOp (n := 66) (.exec 0x107f2c (fun s => s.RIP = 0x107f2c) (rolR64Effect 0x107f2c 4 13 48) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[63]
    (.letOp (n := 67) (.out 0x107f30 (movR64M64Effect 0x107f30 7 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 68) (.exec 0x107f30 (LoadPre 0x107f30 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x107f30 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107f30 7 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.out 0x107f35 (movR64R64Effect 0x107f35 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 9] []) (.reg (.gpr 10))) #v[61]
    (.letOp (n := 70) (.exec 0x107f35 (fun s => s.RIP = 0x107f35) (movR64R64Effect 0x107f35 10 9) (Reg.operands [.gpr 9] [])) #v[61]
    (.letOp (n := 71) (.out 0x107f38 (rolR64Effect 0x107f38 4 10 48) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[69]
    (.letOp (n := 72) (.exec 0x107f38 (fun s => s.RIP = 0x107f38) (rolR64Effect 0x107f38 4 10 48) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[69]
    (.letOp (n := 73) (.out 0x107f3c (movR64M64Effect 0x107f3c 1 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 74) (.exec 0x107f3c (LoadPre 0x107f3c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x107f3c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107f3c 1 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.out 0x107f41 (movR64R64Effect 0x107f41 15 7) (EffectPart.reads (.reg (.gpr 15)) [.gpr 7] []) (.reg (.gpr 15))) #v[67]
    (.letOp (n := 76) (.exec 0x107f41 (fun s => s.RIP = 0x107f41) (movR64R64Effect 0x107f41 15 7) (Reg.operands [.gpr 7] [])) #v[67]
    (.letOp (n := 77) (.out 0x107f44 (rolR64Effect 0x107f44 4 15 48) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[75]
    (.letOp (n := 78) (.exec 0x107f44 (fun s => s.RIP = 0x107f44) (rolR64Effect 0x107f44 4 15 48) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[75]
    (.letOp (n := 79) (.out 0x107f48 (movR64M64Effect 0x107f48 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 80) (.exec 0x107f48 (LoadPre 0x107f48 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x107f48 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107f48 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 81) (.out 0x107f4d (movR64R64Effect 0x107f4d 14 1) (EffectPart.reads (.reg (.gpr 14)) [.gpr 1] []) (.reg (.gpr 14))) #v[73]
    (.letOp (n := 82) (.exec 0x107f4d (fun s => s.RIP = 0x107f4d) (movR64R64Effect 0x107f4d 14 1) (Reg.operands [.gpr 1] [])) #v[73]
    (.letOp (n := 83) (.out 0x107f50 (rolR64Effect 0x107f50 4 14 48) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[81]
    (.letOp (n := 84) (.exec 0x107f50 (fun s => s.RIP = 0x107f50) (rolR64Effect 0x107f50 4 14 48) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[81]
    (.letOp (n := 85) (.out 0x107f54 (movR64M64Effect 0x107f54 3 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 86) (.exec 0x107f54 (LoadPre 0x107f54 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x107f54 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107f54 3 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 87) (.out 0x107f59 (movR64R64Effect 0x107f59 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0] []) (.reg (.gpr 2))) #v[79]
    (.letOp (n := 88) (.exec 0x107f59 (fun s => s.RIP = 0x107f59) (movR64R64Effect 0x107f59 2 0) (Reg.operands [.gpr 0] [])) #v[79]
    (.letOp (n := 89) (.out 0x107f5c (rolR64Effect 0x107f5c 4 2 48) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[87]
    (.letOp (n := 90) (.exec 0x107f5c (fun s => s.RIP = 0x107f5c) (rolR64Effect 0x107f5c 4 2 48) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[87]
    (.letOp (n := 91) (.out 0x107f60 (xorR64R64Effect 0x107f60 8 11) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 11] []) (.reg (.gpr 8))) #v[53, 59]
    (.letOp (n := 92) (.exec 0x107f60 (fun s => s.RIP = 0x107f60) (xorR64R64Effect 0x107f60 8 11) (Reg.operands [.gpr 8, .gpr 11] [])) #v[53, 59]
    (b_l107f13_1))))))))))))))))))))))))))))))))))))))))

def bytes_l107f13 : List UInt8 :=
  [0x4C, 0x8B, 0x44, 0x24, 0x08, 0x48, 0x8B, 0x74, 0x24, 0x10, 0x4D, 0x89, 0xC3, 0x49, 0xC1, 0xC3,
    0x30, 0x4C, 0x8B, 0x4C, 0x24, 0x18, 0x49, 0x89, 0xF5, 0x49, 0xC1, 0xC5, 0x30, 0x48, 0x8B, 0x7C,
    0x24, 0x20, 0x4D, 0x89, 0xCA, 0x49, 0xC1, 0xC2, 0x30, 0x48, 0x8B, 0x4C, 0x24, 0x28, 0x49, 0x89,
    0xFF, 0x49, 0xC1, 0xC7, 0x30, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x49, 0x89, 0xCE, 0x49, 0xC1, 0xC6,
    0x30, 0x48, 0x8B, 0x5C, 0x24, 0x40, 0x48, 0x89, 0xC2, 0x48, 0xC1, 0xC2, 0x30, 0x4D, 0x31, 0xD8] ++ bytes_l107f13_1

theorem code_l107f13 : ∀ x ∈ codeRange 0x107f13 bytes_l107f13, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x7f13 80 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l107f13_1

@[cfg_block] def b_l10805f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x10805f (StorePre 0x10805f 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10805f + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10805f (.sib 4 none 0 (.d8 0x40)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.exec 0x108068 (StorePre 0x108068 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x108068 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x108068 (.sib 4 none 0 (.d8 0x38)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x108071 (StorePre 0x108071 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x108071 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x108071 (.sib 4 none 0 (.d8 0x30)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.exec 0x10807a (StorePre 0x10807a 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10807a + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10807a (.sib 4 none 0 (.d8 0x28)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x108083 (StorePre 0x108083 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x108083 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x108083 (.sib 4 none 0 (.d8 0x20)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x10808c (StorePre 0x10808c 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10808c + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10808c (.sib 4 none 0 (.d8 0x18)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.exec 0x108095 (StorePre 0x108095 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108095 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x108095 (.sib 4 none 0 (.d8 0x10)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.exec 0x10809e (StorePre 0x10809e 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10809e + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10809e (.sib 4 none 0 (.d8 0x8)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x1080a7 (movR64M64Effect 0x1080a7 12 (.sib 4 none 0 (.d32 0xe8))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 62) (.exec 0x1080a7 (LoadPre 0x1080a7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x1080a7 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1080a7 12 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x1080af (testR64R64Effect 0x1080af 12 12) (EffectPart.reads (.flag .ZF) [.gpr 12, .gpr 12] []) (.flag .ZF)) #v[61, 61]
    (.letOp (n := 64) (.exec 0x1080af (fun s => s.RIP = 0x1080af) (testR64R64Effect 0x1080af 12 12) (Reg.operands [.gpr 12, .gpr 12] [])) #v[61, 61]
    (.letOp (n := 65) (.out 0x1080b2 (movR64M64Effect 0x1080b2 5 (.sib 4 none 0 (.d32 0xf0))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 66) (.exec 0x1080b2 (LoadPre 0x1080b2 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x1080b2 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1080b2 5 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.pure (condOp 4)) #v[63]
    (.terminate (.condBr (Fin.last 67) ⟨.l1084c1, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 65), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 61), (13, 13), (19, 63), (22, 22), (39, 39), (50, 50), (51, 51)] 68⟩ ⟨.l1080c0, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 65), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 61), (13, 13), (19, 63), (22, 22), (39, 39), (50, 50), (51, 51)] 68⟩))))))))))))))))

def bytes_l10805f : List UInt8 :=
  [0x48, 0xC7, 0x44, 0x24, 0x40, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x38, 0x00, 0x00,
    0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x30, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x28,
    0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x20, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44,
    0x24, 0x18, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x10, 0x00, 0x00, 0x00, 0x00, 0x48,
    0xC7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00, 0x4C, 0x8B, 0xA4, 0x24, 0xE8, 0x00, 0x00, 0x00,
    0x4D, 0x85, 0xE4, 0x48, 0x8B, 0xAC, 0x24, 0xF0, 0x00, 0x00, 0x00, 0x0F, 0x84, 0x01, 0x04, 0x00,
    0x00]

theorem code_l10805f : ∀ x ∈ codeRange 0x10805f bytes_l10805f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x805f 97 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1080c0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1080c0 (movR64Imm64Effect 0x1080c0 0 0xffffffffffffffc) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 54) (.exec 0x1080c0 (fun s => s.RIP = 0x1080c0) (movR64Imm64Effect 0x1080c0 0 0xffffffffffffffc) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x1080ca (movR64M64Effect 0x1080ca 1 (.sib 4 none 0 (.d32 0x140))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x1080ca (LoadPre 0x1080ca (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x1080ca + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1080ca 1 (.sib 4 none 0 (.d32 0x140))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1080d2 (andR64R64Effect 0x1080d2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[55, 53]
    (.letOp (n := 58) (.exec 0x1080d2 (fun s => s.RIP = 0x1080d2) (andR64R64Effect 0x1080d2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[55, 53]
    (.letOp (n := 59) (.out 0x1080d5 (shlR64Effect 0x1080d5 4 1 4) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[57]
    (.letOp (n := 60) (.exec 0x1080d5 (fun s => s.RIP = 0x1080d5) (shlR64Effect 0x1080d5 4 1 4) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[57]
    (.letOp (n := 61) (.out 0x1080d9 (addR64R64Effect 0x1080d9 5 1) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 1] []) (.reg (.gpr 5))) #v[5, 59]
    (.letOp (n := 62) (.exec 0x1080d9 (fun s => s.RIP = 0x1080d9) (addR64R64Effect 0x1080d9 5 1) (Reg.operands [.gpr 5, .gpr 1] [])) #v[5, 59]
    (.letOp (n := 63) (.out 0x1080dc (addR64R64Effect 0x1080dc 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[2, 59]
    (.letOp (n := 64) (.exec 0x1080dc (fun s => s.RIP = 0x1080dc) (addR64R64Effect 0x1080dc 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[2, 59]
    (.letOp (n := 65) (.exec 0x1080df (StorePre 0x1080df 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x1080df + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1080df 2 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[63, 4]
    (.letOp (n := 66) (.out 0x1080e7 (shlR32Effect 0x1080e7 4 12 4) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[12]
    (.letOp (n := 67) (.exec 0x1080e7 (fun s => s.RIP = 0x1080e7) (shlR32Effect 0x1080e7 4 12 4) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[12]
    (.letOp (n := 68) (.out 0x1080eb (movR64M64Effect 0x1080eb 3 (.sib 4 none 0 (.d32 0x150))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 69) (.exec 0x1080eb (LoadPre 0x1080eb (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x150)) s (0x1080eb + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1080eb 3 (.sib 4 none 0 (.d32 0x150))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.out 0x1080f3 (xorR32R32Effect 0x1080f3 3 13 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 13] []) (.reg (.gpr 13))) #v[13, 13]
    (.letOp (n := 71) (.exec 0x1080f3 (fun s => s.RIP = 0x1080f3) (xorR32R32Effect 0x1080f3 3 13 13) (Reg.operands [.gpr 13, .gpr 13] [])) #v[13, 13]
    (.letOp (n := 72) (.out 0x1080f6 (leaR64Effect 0x1080f6 14 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 73) (.exec 0x1080f6 (fun s => s.RIP = 0x1080f6) (leaR64Effect 0x1080f6 14 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.out 0x1080fe (leaR64Effect 0x1080fe 15 (.sib 4 none 0 (.d32 0x100))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 75) (.exec 0x1080fe (fun s => s.RIP = 0x1080fe) (leaR64Effect 0x1080fe 15 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 76) (.exec 0x108106 (fun s => s.RIP = 0x108106) (fun _ => nopEffect 0x108106 10) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l108110, RegMap.args [(0, 53), (1, 59), (2, 63), (3, 68), (4, 4), (5, 61), (9, 9), (12, 66), (13, 70), (14, 72), (15, 74), (22, 22), (39, 39), (50, 50), (51, 51)] 77⟩)))))))))))))))))))))))))

def bytes_l1080c0 : List UInt8 :=
  [0x48, 0xB8, 0xFC, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x48, 0x8B, 0x8C, 0x24, 0x40, 0x01,
    0x00, 0x00, 0x48, 0x21, 0xC1, 0x48, 0xC1, 0xE1, 0x04, 0x48, 0x01, 0xCD, 0x48, 0x01, 0xCA, 0x48,
    0x89, 0x94, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x41, 0xC1, 0xE4, 0x04, 0x48, 0x8B, 0x9C, 0x24, 0x50,
    0x01, 0x00, 0x00, 0x45, 0x31, 0xED, 0x4C, 0x8D, 0xB4, 0x24, 0x98, 0x00, 0x00, 0x00, 0x4C, 0x8D,
    0xBC, 0x24, 0x00, 0x01, 0x00, 0x00, 0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem code_l1080c0 : ∀ x ∈ codeRange 0x1080c0 bytes_l1080c0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x80c0 80 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l108110 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x108110 (movR32M32Effect 0x108110 0 (.base 9 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[9]
    (.letOp (n := 54) (.exec 0x108110 (LoadPre 0x108110 (fun s => AddrMode.addr (.base 9 (.d8 0x10)) s (0x108110 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x108110 0 (.base 9 (.d8 0x10))) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 55) (.out 0x108114 (movR64M64Effect 0x108114 1 (.base 9 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 9] []) (.reg (.gpr 1))) #v[9]
    (.letOp (n := 56) (.exec 0x108114 (LoadPre 0x108114 (fun s => AddrMode.addr (.base 9 .none) s (0x108114 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x108114 1 (.base 9 .none)) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 57) (.out 0x108117 (movR32M32Effect 0x108117 2 (.base 9 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9] []) (.reg (.gpr 2))) #v[9]
    (.letOp (n := 58) (.exec 0x108117 (LoadPre 0x108117 (fun s => AddrMode.addr (.base 9 (.d8 0x8)) s (0x108117 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x108117 2 (.base 9 (.d8 0x8))) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 59) (.out 0x10811b (movR32M32Effect 0x10811b 6 (.base 9 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 9] []) (.reg (.gpr 6))) #v[9]
    (.letOp (n := 60) (.exec 0x10811b (LoadPre 0x10811b (fun s => AddrMode.addr (.base 9 (.d8 0xc)) s (0x10811b + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x10811b 6 (.base 9 (.d8 0xc))) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 61) (.out 0x10811f (addR32R32Effect 0x10811f 2 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[59, 53]
    (.letOp (n := 62) (.exec 0x10811f (fun s => s.RIP = 0x10811f) (addR32R32Effect 0x10811f 2 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[59, 53]
    (.letOp (n := 63) (.out 0x108121 (bswapR32Effect 0x108121 2 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[61]
    (.letOp (n := 64) (.exec 0x108121 (fun s => s.RIP = 0x108121) (bswapR32Effect 0x108121 2 6) (Reg.operands [.gpr 6] [])) #v[61]
    (.letOp (n := 65) (.out 0x108123 (incR32Effect 0x108123 2 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 66) (.exec 0x108123 (fun s => s.RIP = 0x108123) (incR32Effect 0x108123 2 0) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 67) (.exec 0x108125 (StorePre 0x108125 4 (fun s => AddrMode.addr (.base 9 (.d8 0x10)) s (0x108125 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x108125 0 (.base 9 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 9] [])) #v[65, 9]
    (.letOp (n := 68) (.exec 0x108129 (StorePre 0x108129 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x108129 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108129 1 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 69) (.exec 0x108131 (StorePre 0x108131 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x108131 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x108131 2 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 70) (.exec 0x108138 (StorePre 0x108138 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x10c)) s (0x108138 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x108138 6 (.sib 4 none 0 (.d32 0x10c))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[63, 4]
    (.letOp (n := 71) (.out 0x10813f (movR64R64Effect 0x10813f 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 72) (.exec 0x10813f (fun s => s.RIP = 0x10813f) (movR64R64Effect 0x10813f 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 73) (.out 0x108142 (movR64R64Effect 0x108142 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[3]
    (.letOp (n := 74) (.exec 0x108142 (fun s => s.RIP = 0x108142) (movR64R64Effect 0x108142 6 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 75) (.out 0x108145 (movR64R64Effect 0x108145 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15] []) (.reg (.gpr 2))) #v[15]
    (.letOp (n := 76) (.exec 0x108145 (fun s => s.RIP = 0x108145) (movR64R64Effect 0x108145 2 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 77) (.out 0x108148 (callEffect (fun _ => 0x105100) 0x10814d) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 78) (.exec 0x108148 (PushPre 0x108148 5) (callEffect (fun _ => 0x105100) 0x10814d) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.const ⟨64, 0x10814d⟩) #v[]
    (.terminate (.call ⟨.l105100, RegMap.args [(0, 65), (1, 55), (2, 75), (3, 3), (4, 77), (5, 5), (6, 73), (7, 71), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 80⟩ { target := .l10814d, kept := #v[], arity := rfl, guard := some (Fin.last 79) }))))))))))))))))))))))))))))

def bytes_l108110 : List UInt8 :=
  [0x41, 0x8B, 0x41, 0x10, 0x49, 0x8B, 0x09, 0x41, 0x8B, 0x51, 0x08, 0x41, 0x8B, 0x71, 0x0C, 0x01,
    0xC6, 0x0F, 0xCE, 0xFF, 0xC0, 0x41, 0x89, 0x41, 0x10, 0x48, 0x89, 0x8C, 0x24, 0x00, 0x01, 0x00,
    0x00, 0x89, 0x94, 0x24, 0x08, 0x01, 0x00, 0x00, 0x89, 0xB4, 0x24, 0x0C, 0x01, 0x00, 0x00, 0x4C,
    0x89, 0xF7, 0x48, 0x89, 0xDE, 0x4C, 0x89, 0xFA, 0xE8, 0xB3, 0xCF, 0xFF, 0xFF]

theorem code_l108110 : ∀ x ∈ codeRange 0x108110 bytes_l108110, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x8110 61 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10814d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10814d (movR64M64Effect 0x10814d 9 (.sib 4 none 0 (.d32 0xf8))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 54) (.exec 0x10814d (LoadPre 0x10814d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x10814d + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10814d 9 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x108155 (movR64M64Effect 0x108155 0 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 56) (.exec 0x108155 (LoadPre 0x108155 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x108155 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x108155 0 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x10815d (movR64M64Effect 0x10815d 1 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 58) (.exec 0x10815d (LoadPre 0x10815d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x10815d + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10815d 1 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.exec 0x108165 (StorePre 0x108165 5 (fun s => AddrMode.addr (.sib 4 (some 13) 0 (.d8 0x10)) s (0x108165 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108165 1 (.sib 4 (some 13) 0 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 4, .gpr 13] [])) #v[57, 4, 13]
    (.letOp (n := 60) (.exec 0x10816a (StorePre 0x10816a 5 (fun s => AddrMode.addr (.sib 4 (some 13) 0 (.d8 0x8)) s (0x10816a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10816a 0 (.sib 4 (some 13) 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4, .gpr 13] [])) #v[55, 4, 13]
    (.letOp (n := 61) (.out 0x10816f (addR64Imm8Effect 0x10816f 13 0x10) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[13]
    (.letOp (n := 62) (.exec 0x10816f (fun s => s.RIP = 0x10816f) (addR64Imm8Effect 0x10816f 13 0x10) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 63) (.out 0x108173 (cmpR64R64Effect 0x108173 12 13) (EffectPart.reads (.flag .ZF) [.gpr 12, .gpr 13] []) (.flag .ZF)) #v[12, 61]
    (.letOp (n := 64) (.exec 0x108173 (fun s => s.RIP = 0x108173) (cmpR64R64Effect 0x108173 12 13) (Reg.operands [.gpr 12, .gpr 13] [])) #v[12, 61]
    (.letOp (n := 65) (.pure (condOp 5)) #v[63]
    (.terminate (.condBr (Fin.last 65) ⟨.l108110, RegMap.args [(0, 55), (1, 57), (3, 3), (4, 4), (5, 5), (9, 53), (12, 12), (13, 61), (14, 14), (15, 15), (19, 63), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩ ⟨.l108178, RegMap.args [(0, 55), (1, 57), (3, 3), (4, 4), (5, 5), (9, 53), (12, 12), (13, 61), (14, 14), (15, 15), (19, 63), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩))))))))))))))

def bytes_l10814d : List UInt8 :=
  [0x4C, 0x8B, 0x8C, 0x24, 0xF8, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00,
    0x48, 0x8B, 0x8C, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x4A, 0x89, 0x4C, 0x2C, 0x10, 0x4A, 0x89, 0x44,
    0x2C, 0x08, 0x49, 0x83, 0xC5, 0x10, 0x4D, 0x39, 0xEC, 0x75, 0x98]

theorem code_l10814d : ∀ x ∈ codeRange 0x10814d bytes_l10814d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x814d 43 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l108178_3 : Block Op Label signature Reg.count 153 :=
  .letOp (n := 153) (.pure (condOp 4)) #v[151]
    (.terminate (.condBr (Fin.last 153) ⟨.l1084c1, RegMap.args [(0, 149), (1, 121), (2, 97), (3, 95), (4, 4), (5, 101), (6, 134), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 113), (13, 117), (14, 105), (15, 109), (19, 151), (22, 22), (39, 39), (50, 50), (51, 51)] 154⟩ ⟨.l108299, RegMap.args [(0, 149), (1, 121), (2, 97), (3, 95), (4, 4), (5, 101), (6, 134), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 113), (13, 117), (14, 105), (15, 109), (19, 151), (22, 22), (39, 39), (50, 50), (51, 51)] 154⟩))

def bytes_l108178_3 : List UInt8 :=
  [0x0F, 0x84, 0x28, 0x02, 0x00, 0x00]

theorem code_l108178_3 : ∀ x ∈ codeRange 0x108293 bytes_l108178_3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x8293 6 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l108178_2 : Block Op Label signature Reg.count 128 :=
  .letOp (n := 128) (.out 0x108239 (movzxR32M8Effect 0x108239 8 6 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 129) (.exec 0x108239 (LoadPre 0x108239 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x108239 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108239 8 6 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 130) (.exec 0x108241 (StorePre 0x108241 4 (fun s => AddrMode.addr (.base 0 (.d8 0x1)) s (0x108241 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108241 4 6 (.base 0 (.d8 0x1))) (Reg.operands [.gpr 6, .gpr 0] [])) #v[128, 123]
    (.letOp (n := 131) (.out 0x108245 (movzxR32M8Effect 0x108245 5 6 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 132) (.exec 0x108245 (LoadPre 0x108245 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x108245 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x108245 5 6 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 133) (.exec 0x10824a (StorePre 0x10824a 4 (fun s => AddrMode.addr (.base 0 (.d8 0x2)) s (0x10824a + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10824a 4 6 (.base 0 (.d8 0x2))) (Reg.operands [.gpr 6, .gpr 0] [])) #v[131, 123]
    (.letOp (n := 134) (.out 0x10824e (movzxR32M8Effect 0x10824e 8 6 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 135) (.exec 0x10824e (LoadPre 0x10824e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x10824e + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x10824e 8 6 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 136) (.exec 0x108256 (StorePre 0x108256 4 (fun s => AddrMode.addr (.base 0 (.d8 0x3)) s (0x108256 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108256 4 6 (.base 0 (.d8 0x3))) (Reg.operands [.gpr 6, .gpr 0] [])) #v[134, 123]
    (.letOp (n := 137) (.exec 0x10825a (StorePre 0x10825a 4 (fun s => AddrMode.addr (.base 0 (.d8 0x4)) s (0x10825a + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10825a 4 7 (.base 0 (.d8 0x4))) (Reg.operands [.gpr 7, .gpr 0] [])) #v[75, 123]
    (.letOp (n := 138) (.exec 0x10825e (StorePre 0x10825e 4 (fun s => AddrMode.addr (.base 0 (.d8 0x5)) s (0x10825e + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10825e 4 8 (.base 0 (.d8 0x5))) (Reg.operands [.gpr 8, .gpr 0] [])) #v[79, 123]
    (.letOp (n := 139) (.exec 0x108262 (StorePre 0x108262 4 (fun s => AddrMode.addr (.base 0 (.d8 0x6)) s (0x108262 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108262 4 9 (.base 0 (.d8 0x6))) (Reg.operands [.gpr 9, .gpr 0] [])) #v[83, 123]
    (.letOp (n := 140) (.exec 0x108266 (StorePre 0x108266 4 (fun s => AddrMode.addr (.base 0 (.d8 0x7)) s (0x108266 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108266 4 10 (.base 0 (.d8 0x7))) (Reg.operands [.gpr 10, .gpr 0] [])) #v[87, 123]
    (.letOp (n := 141) (.exec 0x10826a (StorePre 0x10826a 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x10826a + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10826a 4 11 (.base 0 (.d8 0x8))) (Reg.operands [.gpr 11, .gpr 0] [])) #v[91, 123]
    (.letOp (n := 142) (.exec 0x10826e (StorePre 0x10826e 3 (fun s => AddrMode.addr (.base 0 (.d8 0x9)) s (0x10826e + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10826e 3 3 (.base 0 (.d8 0x9))) (Reg.operands [.gpr 3, .gpr 0] [])) #v[95, 123]
    (.letOp (n := 143) (.exec 0x108271 (StorePre 0x108271 4 (fun s => AddrMode.addr (.base 0 (.d8 0xa)) s (0x108271 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108271 4 5 (.base 0 (.d8 0xa))) (Reg.operands [.gpr 5, .gpr 0] [])) #v[101, 123]
    (.letOp (n := 144) (.exec 0x108275 (StorePre 0x108275 4 (fun s => AddrMode.addr (.base 0 (.d8 0xb)) s (0x108275 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108275 4 14 (.base 0 (.d8 0xb))) (Reg.operands [.gpr 14, .gpr 0] [])) #v[105, 123]
    (.letOp (n := 145) (.exec 0x108279 (StorePre 0x108279 4 (fun s => AddrMode.addr (.base 0 (.d8 0xc)) s (0x108279 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108279 4 15 (.base 0 (.d8 0xc))) (Reg.operands [.gpr 15, .gpr 0] [])) #v[109, 123]
    (.letOp (n := 146) (.exec 0x10827d (StorePre 0x10827d 4 (fun s => AddrMode.addr (.base 0 (.d8 0xd)) s (0x10827d + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10827d 4 12 (.base 0 (.d8 0xd))) (Reg.operands [.gpr 12, .gpr 0] [])) #v[113, 123]
    (.letOp (n := 147) (.exec 0x108281 (StorePre 0x108281 4 (fun s => AddrMode.addr (.base 0 (.d8 0xe)) s (0x108281 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108281 4 13 (.base 0 (.d8 0xe))) (Reg.operands [.gpr 13, .gpr 0] [])) #v[117, 123]
    (.letOp (n := 148) (.exec 0x108285 (StorePre 0x108285 3 (fun s => AddrMode.addr (.base 0 (.d8 0xf)) s (0x108285 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x108285 3 1 (.base 0 (.d8 0xf))) (Reg.operands [.gpr 1, .gpr 0] [])) #v[121, 123]
    (.letOp (n := 149) (.out 0x108288 (movR64M64Effect 0x108288 0 (.sib 4 none 0 (.d32 0xe8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 150) (.exec 0x108288 (LoadPre 0x108288 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x108288 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x108288 0 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 151) (.out 0x108290 (cmpR32Imm8Effect 0x108290 3 0 0x1) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[149]
    (.letOp (n := 152) (.exec 0x108290 (fun s => s.RIP = 0x108290) (cmpR32Imm8Effect 0x108290 3 0 0x1) (Reg.operands [.gpr 0] [])) #v[149]
    (b_l108178_3)))))))))))))))))))))))))

def bytes_l108178_2 : List UInt8 :=
  [0x0F, 0xB6, 0xB4, 0x24, 0x80, 0x00, 0x00, 0x00, 0x40, 0x88, 0x70, 0x01, 0x0F, 0xB6, 0x74, 0x24,
    0x78, 0x40, 0x88, 0x70, 0x02, 0x0F, 0xB6, 0xB4, 0x24, 0x90, 0x00, 0x00, 0x00, 0x40, 0x88, 0x70,
    0x03, 0x40, 0x88, 0x78, 0x04, 0x44, 0x88, 0x40, 0x05, 0x44, 0x88, 0x48, 0x06, 0x44, 0x88, 0x50,
    0x07, 0x44, 0x88, 0x58, 0x08, 0x88, 0x58, 0x09, 0x40, 0x88, 0x68, 0x0A, 0x44, 0x88, 0x70, 0x0B,
    0x44, 0x88, 0x78, 0x0C, 0x44, 0x88, 0x60, 0x0D, 0x44, 0x88, 0x68, 0x0E, 0x88, 0x48, 0x0F, 0x48,
    0x8B, 0x84, 0x24, 0xE8, 0x00, 0x00, 0x00, 0x83, 0xF8, 0x01] ++ bytes_l108178_3

theorem code_l108178_2 : ∀ x ∈ codeRange 0x108239 bytes_l108178_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x8239 90 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l108178_3

@[cfg_block] def b_l108178_1 : Block Op Label signature Reg.count 89 :=
  .letOp (n := 89) (.out 0x1081d8 (movzxR32M8Effect 0x1081d8 6 11 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 90) (.exec 0x1081d8 (LoadPre 0x1081d8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1081d8 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1081d8 6 11 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 91) (.out 0x1081de (xorR8M8Effect 0x1081de 4 11 (.base 5 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 5] []) (.reg (.gpr 11))) #v[89, 5]
    (.letOp (n := 92) (.exec 0x1081de (LoadPre 0x1081de (fun s => AddrMode.addr (.base 5 (.d8 0x8)) s (0x1081de + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1081de 4 11 (.base 5 (.d8 0x8))) (Reg.operands [.gpr 11, .gpr 5] [])) #v[89, 5]
    (.letOp (n := 93) (.out 0x1081e2 (movzxR32M8Effect 0x1081e2 5 3 (.sib 4 none 0 (.d8 0x11))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 94) (.exec 0x1081e2 (LoadPre 0x1081e2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x11)) s (0x1081e2 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1081e2 5 3 (.sib 4 none 0 (.d8 0x11))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 95) (.out 0x1081e7 (xorR8M8Effect 0x1081e7 3 3 (.base 5 (.d8 0x9))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 5] []) (.reg (.gpr 3))) #v[93, 5]
    (.letOp (n := 96) (.exec 0x1081e7 (LoadPre 0x1081e7 (fun s => AddrMode.addr (.base 5 (.d8 0x9)) s (0x1081e7 + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x1081e7 3 3 (.base 5 (.d8 0x9))) (Reg.operands [.gpr 3, .gpr 5] [])) #v[93, 5]
    (.letOp (n := 97) (.out 0x1081ea (movR64R64Effect 0x1081ea 2 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5] []) (.reg (.gpr 2))) #v[5]
    (.letOp (n := 98) (.exec 0x1081ea (fun s => s.RIP = 0x1081ea) (movR64R64Effect 0x1081ea 2 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 99) (.out 0x1081ed (movzxR32M8Effect 0x1081ed 5 5 (.sib 4 none 0 (.d8 0x12))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 100) (.exec 0x1081ed (LoadPre 0x1081ed (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x12)) s (0x1081ed + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1081ed 5 5 (.sib 4 none 0 (.d8 0x12))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 101) (.out 0x1081f2 (xorR8M8Effect 0x1081f2 4 5 (.base 2 (.d8 0xa))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 2] []) (.reg (.gpr 5))) #v[99, 97]
    (.letOp (n := 102) (.exec 0x1081f2 (LoadPre 0x1081f2 (fun s => AddrMode.addr (.base 2 (.d8 0xa)) s (0x1081f2 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1081f2 4 5 (.base 2 (.d8 0xa))) (Reg.operands [.gpr 5, .gpr 2] [])) #v[99, 97]
    (.letOp (n := 103) (.out 0x1081f6 (movzxR32M8Effect 0x1081f6 6 14 (.sib 4 none 0 (.d8 0x13))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 104) (.exec 0x1081f6 (LoadPre 0x1081f6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x13)) s (0x1081f6 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1081f6 6 14 (.sib 4 none 0 (.d8 0x13))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 105) (.out 0x1081fc (xorR8M8Effect 0x1081fc 4 14 (.base 2 (.d8 0xb))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 2] []) (.reg (.gpr 14))) #v[103, 97]
    (.letOp (n := 106) (.exec 0x1081fc (LoadPre 0x1081fc (fun s => AddrMode.addr (.base 2 (.d8 0xb)) s (0x1081fc + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1081fc 4 14 (.base 2 (.d8 0xb))) (Reg.operands [.gpr 14, .gpr 2] [])) #v[103, 97]
    (.letOp (n := 107) (.out 0x108200 (movzxR32M8Effect 0x108200 6 15 (.sib 4 none 0 (.d8 0x14))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 108) (.exec 0x108200 (LoadPre 0x108200 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x108200 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108200 6 15 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 109) (.out 0x108206 (xorR8M8Effect 0x108206 4 15 (.base 2 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 2] []) (.reg (.gpr 15))) #v[107, 97]
    (.letOp (n := 110) (.exec 0x108206 (LoadPre 0x108206 (fun s => AddrMode.addr (.base 2 (.d8 0xc)) s (0x108206 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108206 4 15 (.base 2 (.d8 0xc))) (Reg.operands [.gpr 15, .gpr 2] [])) #v[107, 97]
    (.letOp (n := 111) (.out 0x10820a (movzxR32M8Effect 0x10820a 6 12 (.sib 4 none 0 (.d8 0x15))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 112) (.exec 0x10820a (LoadPre 0x10820a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x15)) s (0x10820a + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x10820a 6 12 (.sib 4 none 0 (.d8 0x15))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 113) (.out 0x108210 (xorR8M8Effect 0x108210 4 12 (.base 2 (.d8 0xd))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 2] []) (.reg (.gpr 12))) #v[111, 97]
    (.letOp (n := 114) (.exec 0x108210 (LoadPre 0x108210 (fun s => AddrMode.addr (.base 2 (.d8 0xd)) s (0x108210 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108210 4 12 (.base 2 (.d8 0xd))) (Reg.operands [.gpr 12, .gpr 2] [])) #v[111, 97]
    (.letOp (n := 115) (.out 0x108214 (movzxR32M8Effect 0x108214 6 13 (.sib 4 none 0 (.d8 0x16))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 116) (.exec 0x108214 (LoadPre 0x108214 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x16)) s (0x108214 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108214 6 13 (.sib 4 none 0 (.d8 0x16))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 117) (.out 0x10821a (xorR8M8Effect 0x10821a 4 13 (.base 2 (.d8 0xe))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 2] []) (.reg (.gpr 13))) #v[115, 97]
    (.letOp (n := 118) (.exec 0x10821a (LoadPre 0x10821a (fun s => AddrMode.addr (.base 2 (.d8 0xe)) s (0x10821a + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10821a 4 13 (.base 2 (.d8 0xe))) (Reg.operands [.gpr 13, .gpr 2] [])) #v[115, 97]
    (.letOp (n := 119) (.out 0x10821e (movzxR32M8Effect 0x10821e 5 1 (.sib 4 none 0 (.d8 0x17))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 120) (.exec 0x10821e (LoadPre 0x10821e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x17)) s (0x10821e + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10821e 5 1 (.sib 4 none 0 (.d8 0x17))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 121) (.out 0x108223 (xorR8M8Effect 0x108223 3 1 (.base 2 (.d8 0xf))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[119, 97]
    (.letOp (n := 122) (.exec 0x108223 (LoadPre 0x108223 (fun s => AddrMode.addr (.base 2 (.d8 0xf)) s (0x108223 + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x108223 3 1 (.base 2 (.d8 0xf))) (Reg.operands [.gpr 1, .gpr 2] [])) #v[119, 97]
    (.letOp (n := 123) (.out 0x108226 (movR64M64Effect 0x108226 0 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 124) (.exec 0x108226 (LoadPre 0x108226 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x108226 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x108226 0 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 125) (.out 0x10822e (movzxR32M8Effect 0x10822e 8 6 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 126) (.exec 0x10822e (LoadPre 0x10822e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10822e + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x10822e 8 6 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 127) (.exec 0x108236 (StorePre 0x108236 3 (fun s => AddrMode.addr (.base 0 .none) s (0x108236 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x108236 3 6 (.base 0 .none)) (Reg.operands [.gpr 6, .gpr 0] [])) #v[125, 123]
    (b_l108178_2)))))))))))))))))))))))))))))))))))))))

def bytes_l108178_1 : List UInt8 :=
  [0x44, 0x0F, 0xB6, 0x5C, 0x24, 0x10, 0x44, 0x32, 0x5D, 0x08, 0x0F, 0xB6, 0x5C, 0x24, 0x11, 0x32,
    0x5D, 0x09, 0x48, 0x89, 0xEA, 0x0F, 0xB6, 0x6C, 0x24, 0x12, 0x40, 0x32, 0x6A, 0x0A, 0x44, 0x0F,
    0xB6, 0x74, 0x24, 0x13, 0x44, 0x32, 0x72, 0x0B, 0x44, 0x0F, 0xB6, 0x7C, 0x24, 0x14, 0x44, 0x32,
    0x7A, 0x0C, 0x44, 0x0F, 0xB6, 0x64, 0x24, 0x15, 0x44, 0x32, 0x62, 0x0D, 0x44, 0x0F, 0xB6, 0x6C,
    0x24, 0x16, 0x44, 0x32, 0x6A, 0x0E, 0x0F, 0xB6, 0x4C, 0x24, 0x17, 0x32, 0x4A, 0x0F, 0x48, 0x8B,
    0x84, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x0F, 0xB6, 0xB4, 0x24, 0x88, 0x00, 0x00, 0x00, 0x40, 0x88,
    0x30] ++ bytes_l108178_2

theorem code_l108178_1 : ∀ x ∈ codeRange 0x1081d8 bytes_l108178_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x81d8 97 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l108178_2

@[cfg_block] def b_l108178 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x108178 (movzxR32M8Effect 0x108178 5 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x108178 (LoadPre 0x108178 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x108178 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x108178 5 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10817d (movzxR32M8Effect 0x10817d 5 1 (.sib 4 none 0 (.d8 0x9))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x10817d (LoadPre 0x10817d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x9)) s (0x10817d + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10817d 5 1 (.sib 4 none 0 (.d8 0x9))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x108182 (xorR8M8Effect 0x108182 3 0 (.base 5 (.d8 0x0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[53, 5]
    (.letOp (n := 58) (.exec 0x108182 (LoadPre 0x108182 (fun s => AddrMode.addr (.base 5 (.d8 0x0)) s (0x108182 + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x108182 3 0 (.base 5 (.d8 0x0))) (Reg.operands [.gpr 0, .gpr 5] [])) #v[53, 5]
    (.letOp (n := 59) (.exec 0x108185 (StorePre 0x108185 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x108185 + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x108185 7 0 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 60) (.out 0x10818c (xorR8M8Effect 0x10818c 3 1 (.base 5 (.d8 0x1))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 5] []) (.reg (.gpr 1))) #v[55, 5]
    (.letOp (n := 61) (.exec 0x10818c (LoadPre 0x10818c (fun s => AddrMode.addr (.base 5 (.d8 0x1)) s (0x10818c + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x10818c 3 1 (.base 5 (.d8 0x1))) (Reg.operands [.gpr 1, .gpr 5] [])) #v[55, 5]
    (.letOp (n := 62) (.exec 0x10818f (StorePre 0x10818f 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10818f + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x10818f 7 1 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[60, 4]
    (.letOp (n := 63) (.out 0x108196 (movzxR32M8Effect 0x108196 5 0 (.sib 4 none 0 (.d8 0xa))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 64) (.exec 0x108196 (LoadPre 0x108196 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xa)) s (0x108196 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x108196 5 0 (.sib 4 none 0 (.d8 0xa))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x10819b (xorR8M8Effect 0x10819b 3 0 (.base 5 (.d8 0x2))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[63, 5]
    (.letOp (n := 66) (.exec 0x10819b (LoadPre 0x10819b (fun s => AddrMode.addr (.base 5 (.d8 0x2)) s (0x10819b + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x10819b 3 0 (.base 5 (.d8 0x2))) (Reg.operands [.gpr 0, .gpr 5] [])) #v[63, 5]
    (.letOp (n := 67) (.exec 0x10819e (StorePre 0x10819e 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10819e + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10819e 4 0 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x1081a2 (movzxR32M8Effect 0x1081a2 5 0 (.sib 4 none 0 (.d8 0xb))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 69) (.exec 0x1081a2 (LoadPre 0x1081a2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xb)) s (0x1081a2 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1081a2 5 0 (.sib 4 none 0 (.d8 0xb))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.out 0x1081a7 (xorR8M8Effect 0x1081a7 3 0 (.base 5 (.d8 0x3))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[68, 5]
    (.letOp (n := 71) (.exec 0x1081a7 (LoadPre 0x1081a7 (fun s => AddrMode.addr (.base 5 (.d8 0x3)) s (0x1081a7 + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x1081a7 3 0 (.base 5 (.d8 0x3))) (Reg.operands [.gpr 0, .gpr 5] [])) #v[68, 5]
    (.letOp (n := 72) (.exec 0x1081aa (StorePre 0x1081aa 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x1081aa + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x1081aa 7 0 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[70, 4]
    (.letOp (n := 73) (.out 0x1081b1 (movzxR32M8Effect 0x1081b1 5 7 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 74) (.exec 0x1081b1 (LoadPre 0x1081b1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x1081b1 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1081b1 5 7 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.out 0x1081b6 (xorR8M8Effect 0x1081b6 4 7 (.base 5 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 5] []) (.reg (.gpr 7))) #v[73, 5]
    (.letOp (n := 76) (.exec 0x1081b6 (LoadPre 0x1081b6 (fun s => AddrMode.addr (.base 5 (.d8 0x4)) s (0x1081b6 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1081b6 4 7 (.base 5 (.d8 0x4))) (Reg.operands [.gpr 7, .gpr 5] [])) #v[73, 5]
    (.letOp (n := 77) (.out 0x1081ba (movzxR32M8Effect 0x1081ba 6 8 (.sib 4 none 0 (.d8 0xd))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 78) (.exec 0x1081ba (LoadPre 0x1081ba (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xd)) s (0x1081ba + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1081ba 6 8 (.sib 4 none 0 (.d8 0xd))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.out 0x1081c0 (xorR8M8Effect 0x1081c0 4 8 (.base 5 (.d8 0x5))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 5] []) (.reg (.gpr 8))) #v[77, 5]
    (.letOp (n := 80) (.exec 0x1081c0 (LoadPre 0x1081c0 (fun s => AddrMode.addr (.base 5 (.d8 0x5)) s (0x1081c0 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1081c0 4 8 (.base 5 (.d8 0x5))) (Reg.operands [.gpr 8, .gpr 5] [])) #v[77, 5]
    (.letOp (n := 81) (.out 0x1081c4 (movzxR32M8Effect 0x1081c4 6 9 (.sib 4 none 0 (.d8 0xe))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 82) (.exec 0x1081c4 (LoadPre 0x1081c4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x1081c4 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1081c4 6 9 (.sib 4 none 0 (.d8 0xe))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 83) (.out 0x1081ca (xorR8M8Effect 0x1081ca 4 9 (.base 5 (.d8 0x6))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 5] []) (.reg (.gpr 9))) #v[81, 5]
    (.letOp (n := 84) (.exec 0x1081ca (LoadPre 0x1081ca (fun s => AddrMode.addr (.base 5 (.d8 0x6)) s (0x1081ca + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1081ca 4 9 (.base 5 (.d8 0x6))) (Reg.operands [.gpr 9, .gpr 5] [])) #v[81, 5]
    (.letOp (n := 85) (.out 0x1081ce (movzxR32M8Effect 0x1081ce 6 10 (.sib 4 none 0 (.d8 0xf))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 86) (.exec 0x1081ce (LoadPre 0x1081ce (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x1081ce + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1081ce 6 10 (.sib 4 none 0 (.d8 0xf))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 87) (.out 0x1081d4 (xorR8M8Effect 0x1081d4 4 10 (.base 5 (.d8 0x7))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 5] []) (.reg (.gpr 10))) #v[85, 5]
    (.letOp (n := 88) (.exec 0x1081d4 (LoadPre 0x1081d4 (fun s => AddrMode.addr (.base 5 (.d8 0x7)) s (0x1081d4 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1081d4 4 10 (.base 5 (.d8 0x7))) (Reg.operands [.gpr 10, .gpr 5] [])) #v[85, 5]
    (b_l108178_1))))))))))))))))))))))))))))))))))))

def bytes_l108178 : List UInt8 :=
  [0x0F, 0xB6, 0x44, 0x24, 0x08, 0x0F, 0xB6, 0x4C, 0x24, 0x09, 0x32, 0x45, 0x00, 0x88, 0x84, 0x24,
    0x88, 0x00, 0x00, 0x00, 0x32, 0x4D, 0x01, 0x88, 0x8C, 0x24, 0x80, 0x00, 0x00, 0x00, 0x0F, 0xB6,
    0x44, 0x24, 0x0A, 0x32, 0x45, 0x02, 0x88, 0x44, 0x24, 0x78, 0x0F, 0xB6, 0x44, 0x24, 0x0B, 0x32,
    0x45, 0x03, 0x88, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00, 0x0F, 0xB6, 0x7C, 0x24, 0x0C, 0x40, 0x32,
    0x7D, 0x04, 0x44, 0x0F, 0xB6, 0x44, 0x24, 0x0D, 0x44, 0x32, 0x45, 0x05, 0x44, 0x0F, 0xB6, 0x4C,
    0x24, 0x0E, 0x44, 0x32, 0x4D, 0x06, 0x44, 0x0F, 0xB6, 0x54, 0x24, 0x0F, 0x44, 0x32, 0x55, 0x07] ++ bytes_l108178_1

theorem code_l108178 : ∀ x ∈ codeRange 0x108178 bytes_l108178, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x8178 96 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l108178_1

@[cfg_block] def b_l108299_3 : Block Op Label signature Reg.count 153 :=
  .letOp (n := 153) (.pure (condOp 4)) #v[151]
    (.terminate (.condBr (Fin.last 153) ⟨.l1084c1, RegMap.args [(0, 119), (1, 131), (2, 2), (3, 95), (4, 4), (5, 99), (6, 136), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (13, 115), (14, 103), (15, 107), (19, 151), (22, 22), (39, 39), (50, 50), (51, 51)] 154⟩ ⟨.l1083c7, RegMap.args [(0, 119), (1, 131), (2, 2), (3, 95), (4, 4), (5, 99), (6, 136), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (13, 115), (14, 103), (15, 107), (19, 151), (22, 22), (39, 39), (50, 50), (51, 51)] 154⟩))

def bytes_l108299_3 : List UInt8 :=
  [0x0F, 0x84, 0xFA, 0x00, 0x00, 0x00]

theorem code_l108299_3 : ∀ x ∈ codeRange 0x1083c1 bytes_l108299_3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x83c1 6 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l108299_2 : Block Op Label signature Reg.count 128 :=
  .letOp (n := 128) (.out 0x108362 (movzxR32M8Effect 0x108362 8 6 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 129) (.exec 0x108362 (LoadPre 0x108362 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x108362 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108362 8 6 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 130) (.exec 0x10836a (StorePre 0x10836a 4 (fun s => AddrMode.addr (.base 1 (.d8 0x11)) s (0x10836a + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10836a 4 6 (.base 1 (.d8 0x11))) (Reg.operands [.gpr 6, .gpr 1] [])) #v[128, 126]
    (.letOp (n := 131) (.out 0x10836e (movR64M64Effect 0x10836e 1 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 132) (.exec 0x10836e (LoadPre 0x10836e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x10836e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10836e 1 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 133) (.out 0x108376 (movzxR32M8Effect 0x108376 5 6 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 134) (.exec 0x108376 (LoadPre 0x108376 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x108376 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x108376 5 6 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 135) (.exec 0x10837b (StorePre 0x10837b 4 (fun s => AddrMode.addr (.base 1 (.d8 0x12)) s (0x10837b + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10837b 4 6 (.base 1 (.d8 0x12))) (Reg.operands [.gpr 6, .gpr 1] [])) #v[133, 131]
    (.letOp (n := 136) (.out 0x10837f (movzxR32M8Effect 0x10837f 8 6 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 137) (.exec 0x10837f (LoadPre 0x10837f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x10837f + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x10837f 8 6 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 138) (.exec 0x108387 (StorePre 0x108387 4 (fun s => AddrMode.addr (.base 1 (.d8 0x13)) s (0x108387 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108387 4 6 (.base 1 (.d8 0x13))) (Reg.operands [.gpr 6, .gpr 1] [])) #v[136, 131]
    (.letOp (n := 139) (.exec 0x10838b (StorePre 0x10838b 4 (fun s => AddrMode.addr (.base 1 (.d8 0x14)) s (0x10838b + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10838b 4 7 (.base 1 (.d8 0x14))) (Reg.operands [.gpr 7, .gpr 1] [])) #v[75, 131]
    (.letOp (n := 140) (.exec 0x10838f (StorePre 0x10838f 4 (fun s => AddrMode.addr (.base 1 (.d8 0x15)) s (0x10838f + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10838f 4 8 (.base 1 (.d8 0x15))) (Reg.operands [.gpr 8, .gpr 1] [])) #v[79, 131]
    (.letOp (n := 141) (.exec 0x108393 (StorePre 0x108393 4 (fun s => AddrMode.addr (.base 1 (.d8 0x16)) s (0x108393 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108393 4 9 (.base 1 (.d8 0x16))) (Reg.operands [.gpr 9, .gpr 1] [])) #v[83, 131]
    (.letOp (n := 142) (.exec 0x108397 (StorePre 0x108397 4 (fun s => AddrMode.addr (.base 1 (.d8 0x17)) s (0x108397 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108397 4 10 (.base 1 (.d8 0x17))) (Reg.operands [.gpr 10, .gpr 1] [])) #v[87, 131]
    (.letOp (n := 143) (.exec 0x10839b (StorePre 0x10839b 4 (fun s => AddrMode.addr (.base 1 (.d8 0x18)) s (0x10839b + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10839b 4 11 (.base 1 (.d8 0x18))) (Reg.operands [.gpr 11, .gpr 1] [])) #v[91, 131]
    (.letOp (n := 144) (.exec 0x10839f (StorePre 0x10839f 3 (fun s => AddrMode.addr (.base 1 (.d8 0x19)) s (0x10839f + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10839f 3 3 (.base 1 (.d8 0x19))) (Reg.operands [.gpr 3, .gpr 1] [])) #v[95, 131]
    (.letOp (n := 145) (.exec 0x1083a2 (StorePre 0x1083a2 4 (fun s => AddrMode.addr (.base 1 (.d8 0x1a)) s (0x1083a2 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1083a2 4 5 (.base 1 (.d8 0x1a))) (Reg.operands [.gpr 5, .gpr 1] [])) #v[99, 131]
    (.letOp (n := 146) (.exec 0x1083a6 (StorePre 0x1083a6 4 (fun s => AddrMode.addr (.base 1 (.d8 0x1b)) s (0x1083a6 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1083a6 4 14 (.base 1 (.d8 0x1b))) (Reg.operands [.gpr 14, .gpr 1] [])) #v[103, 131]
    (.letOp (n := 147) (.exec 0x1083aa (StorePre 0x1083aa 4 (fun s => AddrMode.addr (.base 1 (.d8 0x1c)) s (0x1083aa + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1083aa 4 15 (.base 1 (.d8 0x1c))) (Reg.operands [.gpr 15, .gpr 1] [])) #v[107, 131]
    (.letOp (n := 148) (.exec 0x1083ae (StorePre 0x1083ae 4 (fun s => AddrMode.addr (.base 1 (.d8 0x1d)) s (0x1083ae + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1083ae 4 12 (.base 1 (.d8 0x1d))) (Reg.operands [.gpr 12, .gpr 1] [])) #v[111, 131]
    (.letOp (n := 149) (.exec 0x1083b2 (StorePre 0x1083b2 4 (fun s => AddrMode.addr (.base 1 (.d8 0x1e)) s (0x1083b2 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1083b2 4 13 (.base 1 (.d8 0x1e))) (Reg.operands [.gpr 13, .gpr 1] [])) #v[115, 131]
    (.letOp (n := 150) (.exec 0x1083b6 (StorePre 0x1083b6 3 (fun s => AddrMode.addr (.base 1 (.d8 0x1f)) s (0x1083b6 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x1083b6 3 0 (.base 1 (.d8 0x1f))) (Reg.operands [.gpr 0, .gpr 1] [])) #v[119, 131]
    (.letOp (n := 151) (.out 0x1083b9 (cmpMImm8Effect 0x1083b9 8 32 (.sib 4 none 0 (.d32 0xe8)) 0x2) (EffectPart.reads (.flag .ZF) [.gpr 4] []) (.flag .ZF)) #v[4]
    (.letOp (n := 152) (.exec 0x1083b9 (LoadPre 0x1083b9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x1083b9 + BitVec.ofNat 64 8)) 4) (cmpMImm8Effect 0x1083b9 8 32 (.sib 4 none 0 (.d32 0xe8)) 0x2) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l108299_3)))))))))))))))))))))))))

def bytes_l108299_2 : List UInt8 :=
  [0x0F, 0xB6, 0xB4, 0x24, 0x80, 0x00, 0x00, 0x00, 0x40, 0x88, 0x71, 0x11, 0x48, 0x8B, 0x8C, 0x24,
    0xD8, 0x00, 0x00, 0x00, 0x0F, 0xB6, 0x74, 0x24, 0x78, 0x40, 0x88, 0x71, 0x12, 0x0F, 0xB6, 0xB4,
    0x24, 0x90, 0x00, 0x00, 0x00, 0x40, 0x88, 0x71, 0x13, 0x40, 0x88, 0x79, 0x14, 0x44, 0x88, 0x41,
    0x15, 0x44, 0x88, 0x49, 0x16, 0x44, 0x88, 0x51, 0x17, 0x44, 0x88, 0x59, 0x18, 0x88, 0x59, 0x19,
    0x40, 0x88, 0x69, 0x1A, 0x44, 0x88, 0x71, 0x1B, 0x44, 0x88, 0x79, 0x1C, 0x44, 0x88, 0x61, 0x1D,
    0x44, 0x88, 0x69, 0x1E, 0x88, 0x41, 0x1F, 0x83, 0xBC, 0x24, 0xE8, 0x00, 0x00, 0x00, 0x02] ++ bytes_l108299_3

theorem code_l108299_2 : ∀ x ∈ codeRange 0x108362 bytes_l108299_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x8362 95 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l108299_3

@[cfg_block] def b_l108299_1 : Block Op Label signature Reg.count 89 :=
  .letOp (n := 89) (.out 0x1082fb (movzxR32M8Effect 0x1082fb 6 11 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 90) (.exec 0x1082fb (LoadPre 0x1082fb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1082fb + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1082fb 6 11 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 91) (.out 0x108301 (xorR8M8Effect 0x108301 4 11 (.base 2 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 2] []) (.reg (.gpr 11))) #v[89, 2]
    (.letOp (n := 92) (.exec 0x108301 (LoadPre 0x108301 (fun s => AddrMode.addr (.base 2 (.d8 0x18)) s (0x108301 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108301 4 11 (.base 2 (.d8 0x18))) (Reg.operands [.gpr 11, .gpr 2] [])) #v[89, 2]
    (.letOp (n := 93) (.out 0x108305 (movzxR32M8Effect 0x108305 5 3 (.sib 4 none 0 (.d8 0x21))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 94) (.exec 0x108305 (LoadPre 0x108305 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x21)) s (0x108305 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x108305 5 3 (.sib 4 none 0 (.d8 0x21))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 95) (.out 0x10830a (xorR8M8Effect 0x10830a 3 3 (.base 2 (.d8 0x19))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 2] []) (.reg (.gpr 3))) #v[93, 2]
    (.letOp (n := 96) (.exec 0x10830a (LoadPre 0x10830a (fun s => AddrMode.addr (.base 2 (.d8 0x19)) s (0x10830a + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x10830a 3 3 (.base 2 (.d8 0x19))) (Reg.operands [.gpr 3, .gpr 2] [])) #v[93, 2]
    (.letOp (n := 97) (.out 0x10830d (movzxR32M8Effect 0x10830d 5 5 (.sib 4 none 0 (.d8 0x22))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 98) (.exec 0x10830d (LoadPre 0x10830d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x22)) s (0x10830d + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10830d 5 5 (.sib 4 none 0 (.d8 0x22))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 99) (.out 0x108312 (xorR8M8Effect 0x108312 4 5 (.base 2 (.d8 0x1a))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 2] []) (.reg (.gpr 5))) #v[97, 2]
    (.letOp (n := 100) (.exec 0x108312 (LoadPre 0x108312 (fun s => AddrMode.addr (.base 2 (.d8 0x1a)) s (0x108312 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108312 4 5 (.base 2 (.d8 0x1a))) (Reg.operands [.gpr 5, .gpr 2] [])) #v[97, 2]
    (.letOp (n := 101) (.out 0x108316 (movzxR32M8Effect 0x108316 6 14 (.sib 4 none 0 (.d8 0x23))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 102) (.exec 0x108316 (LoadPre 0x108316 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x23)) s (0x108316 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108316 6 14 (.sib 4 none 0 (.d8 0x23))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 103) (.out 0x10831c (xorR8M8Effect 0x10831c 4 14 (.base 2 (.d8 0x1b))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 2] []) (.reg (.gpr 14))) #v[101, 2]
    (.letOp (n := 104) (.exec 0x10831c (LoadPre 0x10831c (fun s => AddrMode.addr (.base 2 (.d8 0x1b)) s (0x10831c + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10831c 4 14 (.base 2 (.d8 0x1b))) (Reg.operands [.gpr 14, .gpr 2] [])) #v[101, 2]
    (.letOp (n := 105) (.out 0x108320 (movzxR32M8Effect 0x108320 6 15 (.sib 4 none 0 (.d8 0x24))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 106) (.exec 0x108320 (LoadPre 0x108320 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x108320 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108320 6 15 (.sib 4 none 0 (.d8 0x24))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 107) (.out 0x108326 (xorR8M8Effect 0x108326 4 15 (.base 2 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 2] []) (.reg (.gpr 15))) #v[105, 2]
    (.letOp (n := 108) (.exec 0x108326 (LoadPre 0x108326 (fun s => AddrMode.addr (.base 2 (.d8 0x1c)) s (0x108326 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108326 4 15 (.base 2 (.d8 0x1c))) (Reg.operands [.gpr 15, .gpr 2] [])) #v[105, 2]
    (.letOp (n := 109) (.out 0x10832a (movzxR32M8Effect 0x10832a 6 12 (.sib 4 none 0 (.d8 0x25))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 110) (.exec 0x10832a (LoadPre 0x10832a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x25)) s (0x10832a + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x10832a 6 12 (.sib 4 none 0 (.d8 0x25))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 111) (.out 0x108330 (xorR8M8Effect 0x108330 4 12 (.base 2 (.d8 0x1d))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 2] []) (.reg (.gpr 12))) #v[109, 2]
    (.letOp (n := 112) (.exec 0x108330 (LoadPre 0x108330 (fun s => AddrMode.addr (.base 2 (.d8 0x1d)) s (0x108330 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108330 4 12 (.base 2 (.d8 0x1d))) (Reg.operands [.gpr 12, .gpr 2] [])) #v[109, 2]
    (.letOp (n := 113) (.out 0x108334 (movzxR32M8Effect 0x108334 6 13 (.sib 4 none 0 (.d8 0x26))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 114) (.exec 0x108334 (LoadPre 0x108334 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x26)) s (0x108334 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108334 6 13 (.sib 4 none 0 (.d8 0x26))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 115) (.out 0x10833a (xorR8M8Effect 0x10833a 4 13 (.base 2 (.d8 0x1e))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 2] []) (.reg (.gpr 13))) #v[113, 2]
    (.letOp (n := 116) (.exec 0x10833a (LoadPre 0x10833a (fun s => AddrMode.addr (.base 2 (.d8 0x1e)) s (0x10833a + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10833a 4 13 (.base 2 (.d8 0x1e))) (Reg.operands [.gpr 13, .gpr 2] [])) #v[113, 2]
    (.letOp (n := 117) (.out 0x10833e (movzxR32M8Effect 0x10833e 5 0 (.sib 4 none 0 (.d8 0x27))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 118) (.exec 0x10833e (LoadPre 0x10833e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x27)) s (0x10833e + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10833e 5 0 (.sib 4 none 0 (.d8 0x27))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 119) (.out 0x108343 (xorR8M8Effect 0x108343 3 0 (.base 2 (.d8 0x1f))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[117, 2]
    (.letOp (n := 120) (.exec 0x108343 (LoadPre 0x108343 (fun s => AddrMode.addr (.base 2 (.d8 0x1f)) s (0x108343 + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x108343 3 0 (.base 2 (.d8 0x1f))) (Reg.operands [.gpr 0, .gpr 2] [])) #v[117, 2]
    (.letOp (n := 121) (.out 0x108346 (movR64M64Effect 0x108346 1 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 122) (.exec 0x108346 (LoadPre 0x108346 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x108346 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x108346 1 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 123) (.out 0x10834e (movzxR32M8Effect 0x10834e 8 6 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 124) (.exec 0x10834e (LoadPre 0x10834e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10834e + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x10834e 8 6 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 125) (.exec 0x108356 (StorePre 0x108356 4 (fun s => AddrMode.addr (.base 1 (.d8 0x10)) s (0x108356 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108356 4 6 (.base 1 (.d8 0x10))) (Reg.operands [.gpr 6, .gpr 1] [])) #v[123, 121]
    (.letOp (n := 126) (.out 0x10835a (movR64M64Effect 0x10835a 1 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 127) (.exec 0x10835a (LoadPre 0x10835a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x10835a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10835a 1 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l108299_2)))))))))))))))))))))))))))))))))))))))

def bytes_l108299_1 : List UInt8 :=
  [0x44, 0x0F, 0xB6, 0x5C, 0x24, 0x20, 0x44, 0x32, 0x5A, 0x18, 0x0F, 0xB6, 0x5C, 0x24, 0x21, 0x32,
    0x5A, 0x19, 0x0F, 0xB6, 0x6C, 0x24, 0x22, 0x40, 0x32, 0x6A, 0x1A, 0x44, 0x0F, 0xB6, 0x74, 0x24,
    0x23, 0x44, 0x32, 0x72, 0x1B, 0x44, 0x0F, 0xB6, 0x7C, 0x24, 0x24, 0x44, 0x32, 0x7A, 0x1C, 0x44,
    0x0F, 0xB6, 0x64, 0x24, 0x25, 0x44, 0x32, 0x62, 0x1D, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x26, 0x44,
    0x32, 0x6A, 0x1E, 0x0F, 0xB6, 0x44, 0x24, 0x27, 0x32, 0x42, 0x1F, 0x48, 0x8B, 0x8C, 0x24, 0xD8,
    0x00, 0x00, 0x00, 0x0F, 0xB6, 0xB4, 0x24, 0x88, 0x00, 0x00, 0x00, 0x40, 0x88, 0x71, 0x10, 0x48,
    0x8B, 0x8C, 0x24, 0xD8, 0x00, 0x00, 0x00] ++ bytes_l108299_2

theorem code_l108299_1 : ∀ x ∈ codeRange 0x1082fb bytes_l108299_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x82fb 103 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l108299_2

@[cfg_block] def b_l108299 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x108299 (movzxR32M8Effect 0x108299 5 1 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x108299 (LoadPre 0x108299 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x108299 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x108299 5 1 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10829e (movzxR32M8Effect 0x10829e 5 6 (.sib 4 none 0 (.d8 0x19))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 56) (.exec 0x10829e (LoadPre 0x10829e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x19)) s (0x10829e + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10829e 5 6 (.sib 4 none 0 (.d8 0x19))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1082a3 (xorR8M8Effect 0x1082a3 3 1 (.base 2 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[53, 2]
    (.letOp (n := 58) (.exec 0x1082a3 (LoadPre 0x1082a3 (fun s => AddrMode.addr (.base 2 (.d8 0x10)) s (0x1082a3 + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x1082a3 3 1 (.base 2 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 2] [])) #v[53, 2]
    (.letOp (n := 59) (.exec 0x1082a6 (StorePre 0x1082a6 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1082a6 + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x1082a6 7 1 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 60) (.out 0x1082ad (xorR8M8Effect 0x1082ad 4 6 (.base 2 (.d8 0x11))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[55, 2]
    (.letOp (n := 61) (.exec 0x1082ad (LoadPre 0x1082ad (fun s => AddrMode.addr (.base 2 (.d8 0x11)) s (0x1082ad + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1082ad 4 6 (.base 2 (.d8 0x11))) (Reg.operands [.gpr 6, .gpr 2] [])) #v[55, 2]
    (.letOp (n := 62) (.exec 0x1082b1 (StorePre 0x1082b1 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1082b1 + BitVec.ofNat 64 8)) 1) (movM8R8Effect 0x1082b1 8 6 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[60, 4]
    (.letOp (n := 63) (.out 0x1082b9 (movzxR32M8Effect 0x1082b9 5 1 (.sib 4 none 0 (.d8 0x1a))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 64) (.exec 0x1082b9 (LoadPre 0x1082b9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1a)) s (0x1082b9 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1082b9 5 1 (.sib 4 none 0 (.d8 0x1a))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x1082be (xorR8M8Effect 0x1082be 3 1 (.base 2 (.d8 0x12))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[63, 2]
    (.letOp (n := 66) (.exec 0x1082be (LoadPre 0x1082be (fun s => AddrMode.addr (.base 2 (.d8 0x12)) s (0x1082be + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x1082be 3 1 (.base 2 (.d8 0x12))) (Reg.operands [.gpr 1, .gpr 2] [])) #v[63, 2]
    (.letOp (n := 67) (.exec 0x1082c1 (StorePre 0x1082c1 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1082c1 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1082c1 4 1 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x1082c5 (movzxR32M8Effect 0x1082c5 5 1 (.sib 4 none 0 (.d8 0x1b))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 69) (.exec 0x1082c5 (LoadPre 0x1082c5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1b)) s (0x1082c5 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1082c5 5 1 (.sib 4 none 0 (.d8 0x1b))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.out 0x1082ca (xorR8M8Effect 0x1082ca 3 1 (.base 2 (.d8 0x13))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[68, 2]
    (.letOp (n := 71) (.exec 0x1082ca (LoadPre 0x1082ca (fun s => AddrMode.addr (.base 2 (.d8 0x13)) s (0x1082ca + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x1082ca 3 1 (.base 2 (.d8 0x13))) (Reg.operands [.gpr 1, .gpr 2] [])) #v[68, 2]
    (.letOp (n := 72) (.exec 0x1082cd (StorePre 0x1082cd 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x1082cd + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x1082cd 7 1 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[70, 4]
    (.letOp (n := 73) (.out 0x1082d4 (movzxR32M8Effect 0x1082d4 5 7 (.sib 4 none 0 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 74) (.exec 0x1082d4 (LoadPre 0x1082d4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x1082d4 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1082d4 5 7 (.sib 4 none 0 (.d8 0x1c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.out 0x1082d9 (xorR8M8Effect 0x1082d9 4 7 (.base 2 (.d8 0x14))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2] []) (.reg (.gpr 7))) #v[73, 2]
    (.letOp (n := 76) (.exec 0x1082d9 (LoadPre 0x1082d9 (fun s => AddrMode.addr (.base 2 (.d8 0x14)) s (0x1082d9 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1082d9 4 7 (.base 2 (.d8 0x14))) (Reg.operands [.gpr 7, .gpr 2] [])) #v[73, 2]
    (.letOp (n := 77) (.out 0x1082dd (movzxR32M8Effect 0x1082dd 6 8 (.sib 4 none 0 (.d8 0x1d))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 78) (.exec 0x1082dd (LoadPre 0x1082dd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1d)) s (0x1082dd + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1082dd 6 8 (.sib 4 none 0 (.d8 0x1d))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.out 0x1082e3 (xorR8M8Effect 0x1082e3 4 8 (.base 2 (.d8 0x15))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2] []) (.reg (.gpr 8))) #v[77, 2]
    (.letOp (n := 80) (.exec 0x1082e3 (LoadPre 0x1082e3 (fun s => AddrMode.addr (.base 2 (.d8 0x15)) s (0x1082e3 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1082e3 4 8 (.base 2 (.d8 0x15))) (Reg.operands [.gpr 8, .gpr 2] [])) #v[77, 2]
    (.letOp (n := 81) (.out 0x1082e7 (movzxR32M8Effect 0x1082e7 6 9 (.sib 4 none 0 (.d8 0x1e))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 82) (.exec 0x1082e7 (LoadPre 0x1082e7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1e)) s (0x1082e7 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1082e7 6 9 (.sib 4 none 0 (.d8 0x1e))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 83) (.out 0x1082ed (xorR8M8Effect 0x1082ed 4 9 (.base 2 (.d8 0x16))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2] []) (.reg (.gpr 9))) #v[81, 2]
    (.letOp (n := 84) (.exec 0x1082ed (LoadPre 0x1082ed (fun s => AddrMode.addr (.base 2 (.d8 0x16)) s (0x1082ed + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1082ed 4 9 (.base 2 (.d8 0x16))) (Reg.operands [.gpr 9, .gpr 2] [])) #v[81, 2]
    (.letOp (n := 85) (.out 0x1082f1 (movzxR32M8Effect 0x1082f1 6 10 (.sib 4 none 0 (.d8 0x1f))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 86) (.exec 0x1082f1 (LoadPre 0x1082f1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1f)) s (0x1082f1 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1082f1 6 10 (.sib 4 none 0 (.d8 0x1f))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 87) (.out 0x1082f7 (xorR8M8Effect 0x1082f7 4 10 (.base 2 (.d8 0x17))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2] []) (.reg (.gpr 10))) #v[85, 2]
    (.letOp (n := 88) (.exec 0x1082f7 (LoadPre 0x1082f7 (fun s => AddrMode.addr (.base 2 (.d8 0x17)) s (0x1082f7 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1082f7 4 10 (.base 2 (.d8 0x17))) (Reg.operands [.gpr 10, .gpr 2] [])) #v[85, 2]
    (b_l108299_1))))))))))))))))))))))))))))))))))))

def bytes_l108299 : List UInt8 :=
  [0x0F, 0xB6, 0x4C, 0x24, 0x18, 0x0F, 0xB6, 0x74, 0x24, 0x19, 0x32, 0x4A, 0x10, 0x88, 0x8C, 0x24,
    0x88, 0x00, 0x00, 0x00, 0x40, 0x32, 0x72, 0x11, 0x40, 0x88, 0xB4, 0x24, 0x80, 0x00, 0x00, 0x00,
    0x0F, 0xB6, 0x4C, 0x24, 0x1A, 0x32, 0x4A, 0x12, 0x88, 0x4C, 0x24, 0x78, 0x0F, 0xB6, 0x4C, 0x24,
    0x1B, 0x32, 0x4A, 0x13, 0x88, 0x8C, 0x24, 0x90, 0x00, 0x00, 0x00, 0x0F, 0xB6, 0x7C, 0x24, 0x1C,
    0x40, 0x32, 0x7A, 0x14, 0x44, 0x0F, 0xB6, 0x44, 0x24, 0x1D, 0x44, 0x32, 0x42, 0x15, 0x44, 0x0F,
    0xB6, 0x4C, 0x24, 0x1E, 0x44, 0x32, 0x4A, 0x16, 0x44, 0x0F, 0xB6, 0x54, 0x24, 0x1F, 0x44, 0x32,
    0x52, 0x17] ++ bytes_l108299_1

theorem code_l108299 : ∀ x ∈ codeRange 0x108299 bytes_l108299, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x8299 98 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l108299_1

@[cfg_block] def b_l1083c7_2 : Block Op Label signature Reg.count 128 :=
  .letOp (n := 128) (.out 0x108487 (movzxR32M8Effect 0x108487 5 2 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 129) (.exec 0x108487 (LoadPre 0x108487 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x108487 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x108487 5 2 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 130) (.exec 0x10848c (StorePre 0x10848c 3 (fun s => AddrMode.addr (.base 0 (.d8 0x22)) s (0x10848c + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10848c 3 2 (.base 0 (.d8 0x22))) (Reg.operands [.gpr 2, .gpr 0] [])) #v[128, 55]
    (.letOp (n := 131) (.exec 0x10848f (StorePre 0x10848f 4 (fun s => AddrMode.addr (.base 0 (.d8 0x23)) s (0x10848f + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10848f 4 6 (.base 0 (.d8 0x23))) (Reg.operands [.gpr 6, .gpr 0] [])) #v[72, 55]
    (.letOp (n := 132) (.exec 0x108493 (StorePre 0x108493 4 (fun s => AddrMode.addr (.base 0 (.d8 0x24)) s (0x108493 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108493 4 7 (.base 0 (.d8 0x24))) (Reg.operands [.gpr 7, .gpr 0] [])) #v[76, 55]
    (.letOp (n := 133) (.exec 0x108497 (StorePre 0x108497 4 (fun s => AddrMode.addr (.base 0 (.d8 0x25)) s (0x108497 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108497 4 8 (.base 0 (.d8 0x25))) (Reg.operands [.gpr 8, .gpr 0] [])) #v[80, 55]
    (.letOp (n := 134) (.exec 0x10849b (StorePre 0x10849b 4 (fun s => AddrMode.addr (.base 0 (.d8 0x26)) s (0x10849b + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10849b 4 9 (.base 0 (.d8 0x26))) (Reg.operands [.gpr 9, .gpr 0] [])) #v[84, 55]
    (.letOp (n := 135) (.exec 0x10849f (StorePre 0x10849f 4 (fun s => AddrMode.addr (.base 0 (.d8 0x27)) s (0x10849f + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10849f 4 10 (.base 0 (.d8 0x27))) (Reg.operands [.gpr 10, .gpr 0] [])) #v[88, 55]
    (.letOp (n := 136) (.exec 0x1084a3 (StorePre 0x1084a3 4 (fun s => AddrMode.addr (.base 0 (.d8 0x28)) s (0x1084a3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1084a3 4 11 (.base 0 (.d8 0x28))) (Reg.operands [.gpr 11, .gpr 0] [])) #v[92, 55]
    (.letOp (n := 137) (.exec 0x1084a7 (StorePre 0x1084a7 3 (fun s => AddrMode.addr (.base 0 (.d8 0x29)) s (0x1084a7 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x1084a7 3 3 (.base 0 (.d8 0x29))) (Reg.operands [.gpr 3, .gpr 0] [])) #v[96, 55]
    (.letOp (n := 138) (.exec 0x1084aa (StorePre 0x1084aa 4 (fun s => AddrMode.addr (.base 0 (.d8 0x2a)) s (0x1084aa + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1084aa 4 5 (.base 0 (.d8 0x2a))) (Reg.operands [.gpr 5, .gpr 0] [])) #v[100, 55]
    (.letOp (n := 139) (.exec 0x1084ae (StorePre 0x1084ae 4 (fun s => AddrMode.addr (.base 0 (.d8 0x2b)) s (0x1084ae + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1084ae 4 14 (.base 0 (.d8 0x2b))) (Reg.operands [.gpr 14, .gpr 0] [])) #v[104, 55]
    (.letOp (n := 140) (.exec 0x1084b2 (StorePre 0x1084b2 4 (fun s => AddrMode.addr (.base 0 (.d8 0x2c)) s (0x1084b2 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1084b2 4 15 (.base 0 (.d8 0x2c))) (Reg.operands [.gpr 15, .gpr 0] [])) #v[108, 55]
    (.letOp (n := 141) (.exec 0x1084b6 (StorePre 0x1084b6 4 (fun s => AddrMode.addr (.base 0 (.d8 0x2d)) s (0x1084b6 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1084b6 4 12 (.base 0 (.d8 0x2d))) (Reg.operands [.gpr 12, .gpr 0] [])) #v[112, 55]
    (.letOp (n := 142) (.exec 0x1084ba (StorePre 0x1084ba 4 (fun s => AddrMode.addr (.base 0 (.d8 0x2e)) s (0x1084ba + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1084ba 4 13 (.base 0 (.d8 0x2e))) (Reg.operands [.gpr 13, .gpr 0] [])) #v[116, 55]
    (.letOp (n := 143) (.exec 0x1084be (StorePre 0x1084be 3 (fun s => AddrMode.addr (.base 0 (.d8 0x2f)) s (0x1084be + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x1084be 3 1 (.base 0 (.d8 0x2f))) (Reg.operands [.gpr 1, .gpr 0] [])) #v[120, 55]
    (.terminate (.br ⟨.l1084c1, RegMap.args [(0, 55), (1, 120), (2, 128), (3, 96), (4, 4), (5, 100), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (12, 112), (13, 116), (14, 104), (15, 108), (22, 22), (39, 39), (50, 50), (51, 51)] 144⟩)))))))))))))))))

def bytes_l1083c7_2 : List UInt8 :=
  [0x0F, 0xB6, 0x54, 0x24, 0x78, 0x88, 0x50, 0x22, 0x40, 0x88, 0x70, 0x23, 0x40, 0x88, 0x78, 0x24,
    0x44, 0x88, 0x40, 0x25, 0x44, 0x88, 0x48, 0x26, 0x44, 0x88, 0x50, 0x27, 0x44, 0x88, 0x58, 0x28,
    0x88, 0x58, 0x29, 0x40, 0x88, 0x68, 0x2A, 0x44, 0x88, 0x70, 0x2B, 0x44, 0x88, 0x78, 0x2C, 0x44,
    0x88, 0x60, 0x2D, 0x44, 0x88, 0x68, 0x2E, 0x88, 0x48, 0x2F]

theorem code_l1083c7_2 : ∀ x ∈ codeRange 0x108487 bytes_l1083c7_2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x8487 58 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1083c7_1 : Block Op Label signature Reg.count 90 :=
  .letOp (n := 90) (.out 0x108426 (movzxR32M8Effect 0x108426 6 11 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 91) (.exec 0x108426 (LoadPre 0x108426 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x108426 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108426 6 11 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 92) (.out 0x10842c (xorR8M8Effect 0x10842c 4 11 (.base 2 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 2] []) (.reg (.gpr 11))) #v[90, 2]
    (.letOp (n := 93) (.exec 0x10842c (LoadPre 0x10842c (fun s => AddrMode.addr (.base 2 (.d8 0x28)) s (0x10842c + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10842c 4 11 (.base 2 (.d8 0x28))) (Reg.operands [.gpr 11, .gpr 2] [])) #v[90, 2]
    (.letOp (n := 94) (.out 0x108430 (movzxR32M8Effect 0x108430 5 3 (.sib 4 none 0 (.d8 0x31))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 95) (.exec 0x108430 (LoadPre 0x108430 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x31)) s (0x108430 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x108430 5 3 (.sib 4 none 0 (.d8 0x31))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 96) (.out 0x108435 (xorR8M8Effect 0x108435 3 3 (.base 2 (.d8 0x29))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 2] []) (.reg (.gpr 3))) #v[94, 2]
    (.letOp (n := 97) (.exec 0x108435 (LoadPre 0x108435 (fun s => AddrMode.addr (.base 2 (.d8 0x29)) s (0x108435 + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x108435 3 3 (.base 2 (.d8 0x29))) (Reg.operands [.gpr 3, .gpr 2] [])) #v[94, 2]
    (.letOp (n := 98) (.out 0x108438 (movzxR32M8Effect 0x108438 5 5 (.sib 4 none 0 (.d8 0x32))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 99) (.exec 0x108438 (LoadPre 0x108438 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x32)) s (0x108438 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x108438 5 5 (.sib 4 none 0 (.d8 0x32))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 100) (.out 0x10843d (xorR8M8Effect 0x10843d 4 5 (.base 2 (.d8 0x2a))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 2] []) (.reg (.gpr 5))) #v[98, 2]
    (.letOp (n := 101) (.exec 0x10843d (LoadPre 0x10843d (fun s => AddrMode.addr (.base 2 (.d8 0x2a)) s (0x10843d + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10843d 4 5 (.base 2 (.d8 0x2a))) (Reg.operands [.gpr 5, .gpr 2] [])) #v[98, 2]
    (.letOp (n := 102) (.out 0x108441 (movzxR32M8Effect 0x108441 6 14 (.sib 4 none 0 (.d8 0x33))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 103) (.exec 0x108441 (LoadPre 0x108441 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x33)) s (0x108441 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108441 6 14 (.sib 4 none 0 (.d8 0x33))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 104) (.out 0x108447 (xorR8M8Effect 0x108447 4 14 (.base 2 (.d8 0x2b))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 2] []) (.reg (.gpr 14))) #v[102, 2]
    (.letOp (n := 105) (.exec 0x108447 (LoadPre 0x108447 (fun s => AddrMode.addr (.base 2 (.d8 0x2b)) s (0x108447 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108447 4 14 (.base 2 (.d8 0x2b))) (Reg.operands [.gpr 14, .gpr 2] [])) #v[102, 2]
    (.letOp (n := 106) (.out 0x10844b (movzxR32M8Effect 0x10844b 6 15 (.sib 4 none 0 (.d8 0x34))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 107) (.exec 0x10844b (LoadPre 0x10844b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x10844b + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x10844b 6 15 (.sib 4 none 0 (.d8 0x34))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 108) (.out 0x108451 (xorR8M8Effect 0x108451 4 15 (.base 2 (.d8 0x2c))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 2] []) (.reg (.gpr 15))) #v[106, 2]
    (.letOp (n := 109) (.exec 0x108451 (LoadPre 0x108451 (fun s => AddrMode.addr (.base 2 (.d8 0x2c)) s (0x108451 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108451 4 15 (.base 2 (.d8 0x2c))) (Reg.operands [.gpr 15, .gpr 2] [])) #v[106, 2]
    (.letOp (n := 110) (.out 0x108455 (movzxR32M8Effect 0x108455 6 12 (.sib 4 none 0 (.d8 0x35))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 111) (.exec 0x108455 (LoadPre 0x108455 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x35)) s (0x108455 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108455 6 12 (.sib 4 none 0 (.d8 0x35))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 112) (.out 0x10845b (xorR8M8Effect 0x10845b 4 12 (.base 2 (.d8 0x2d))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 2] []) (.reg (.gpr 12))) #v[110, 2]
    (.letOp (n := 113) (.exec 0x10845b (LoadPre 0x10845b (fun s => AddrMode.addr (.base 2 (.d8 0x2d)) s (0x10845b + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10845b 4 12 (.base 2 (.d8 0x2d))) (Reg.operands [.gpr 12, .gpr 2] [])) #v[110, 2]
    (.letOp (n := 114) (.out 0x10845f (movzxR32M8Effect 0x10845f 6 13 (.sib 4 none 0 (.d8 0x36))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 115) (.exec 0x10845f (LoadPre 0x10845f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x36)) s (0x10845f + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x10845f 6 13 (.sib 4 none 0 (.d8 0x36))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 116) (.out 0x108465 (xorR8M8Effect 0x108465 4 13 (.base 2 (.d8 0x2e))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 2] []) (.reg (.gpr 13))) #v[114, 2]
    (.letOp (n := 117) (.exec 0x108465 (LoadPre 0x108465 (fun s => AddrMode.addr (.base 2 (.d8 0x2e)) s (0x108465 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108465 4 13 (.base 2 (.d8 0x2e))) (Reg.operands [.gpr 13, .gpr 2] [])) #v[114, 2]
    (.letOp (n := 118) (.out 0x108469 (movzxR32M8Effect 0x108469 5 1 (.sib 4 none 0 (.d8 0x37))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 119) (.exec 0x108469 (LoadPre 0x108469 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x37)) s (0x108469 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x108469 5 1 (.sib 4 none 0 (.d8 0x37))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 120) (.out 0x10846e (xorR8M8Effect 0x10846e 3 1 (.base 2 (.d8 0x2f))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[118, 2]
    (.letOp (n := 121) (.exec 0x10846e (LoadPre 0x10846e (fun s => AddrMode.addr (.base 2 (.d8 0x2f)) s (0x10846e + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x10846e 3 1 (.base 2 (.d8 0x2f))) (Reg.operands [.gpr 1, .gpr 2] [])) #v[118, 2]
    (.letOp (n := 122) (.out 0x108471 (movzxR32M8Effect 0x108471 8 2 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 123) (.exec 0x108471 (LoadPre 0x108471 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x108471 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108471 8 2 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 124) (.exec 0x108479 (StorePre 0x108479 3 (fun s => AddrMode.addr (.base 0 (.d8 0x20)) s (0x108479 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x108479 3 2 (.base 0 (.d8 0x20))) (Reg.operands [.gpr 2, .gpr 0] [])) #v[122, 55]
    (.letOp (n := 125) (.out 0x10847c (movzxR32M8Effect 0x10847c 8 2 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 126) (.exec 0x10847c (LoadPre 0x10847c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10847c + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x10847c 8 2 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 127) (.exec 0x108484 (StorePre 0x108484 3 (fun s => AddrMode.addr (.base 0 (.d8 0x21)) s (0x108484 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x108484 3 2 (.base 0 (.d8 0x21))) (Reg.operands [.gpr 2, .gpr 0] [])) #v[125, 55]
    (b_l1083c7_2))))))))))))))))))))))))))))))))))))))

def bytes_l1083c7_1 : List UInt8 :=
  [0x44, 0x0F, 0xB6, 0x5C, 0x24, 0x30, 0x44, 0x32, 0x5A, 0x28, 0x0F, 0xB6, 0x5C, 0x24, 0x31, 0x32,
    0x5A, 0x29, 0x0F, 0xB6, 0x6C, 0x24, 0x32, 0x40, 0x32, 0x6A, 0x2A, 0x44, 0x0F, 0xB6, 0x74, 0x24,
    0x33, 0x44, 0x32, 0x72, 0x2B, 0x44, 0x0F, 0xB6, 0x7C, 0x24, 0x34, 0x44, 0x32, 0x7A, 0x2C, 0x44,
    0x0F, 0xB6, 0x64, 0x24, 0x35, 0x44, 0x32, 0x62, 0x2D, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x36, 0x44,
    0x32, 0x6A, 0x2E, 0x0F, 0xB6, 0x4C, 0x24, 0x37, 0x32, 0x4A, 0x2F, 0x0F, 0xB6, 0x94, 0x24, 0x88,
    0x00, 0x00, 0x00, 0x88, 0x50, 0x20, 0x0F, 0xB6, 0x94, 0x24, 0x80, 0x00, 0x00, 0x00, 0x88, 0x50,
    0x21] ++ bytes_l1083c7_2

theorem code_l1083c7_1 : ∀ x ∈ codeRange 0x108426 bytes_l1083c7_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x8426 97 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1083c7_2

@[cfg_block] def b_l1083c7 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1083c7 (movzxR32M8Effect 0x1083c7 5 6 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 54) (.exec 0x1083c7 (LoadPre 0x1083c7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1083c7 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1083c7 5 6 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1083cc (movR64R64Effect 0x1083cc 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[1]
    (.letOp (n := 56) (.exec 0x1083cc (fun s => s.RIP = 0x1083cc) (movR64R64Effect 0x1083cc 0 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 57) (.out 0x1083cf (movzxR32M8Effect 0x1083cf 5 1 (.sib 4 none 0 (.d8 0x29))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 58) (.exec 0x1083cf (LoadPre 0x1083cf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x29)) s (0x1083cf + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1083cf 5 1 (.sib 4 none 0 (.d8 0x29))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x1083d4 (xorR8M8Effect 0x1083d4 4 6 (.base 2 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[53, 2]
    (.letOp (n := 60) (.exec 0x1083d4 (LoadPre 0x1083d4 (fun s => AddrMode.addr (.base 2 (.d8 0x20)) s (0x1083d4 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1083d4 4 6 (.base 2 (.d8 0x20))) (Reg.operands [.gpr 6, .gpr 2] [])) #v[53, 2]
    (.letOp (n := 61) (.exec 0x1083d8 (StorePre 0x1083d8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1083d8 + BitVec.ofNat 64 8)) 1) (movM8R8Effect 0x1083d8 8 6 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x1083e0 (xorR8M8Effect 0x1083e0 3 1 (.base 2 (.d8 0x21))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[57, 2]
    (.letOp (n := 63) (.exec 0x1083e0 (LoadPre 0x1083e0 (fun s => AddrMode.addr (.base 2 (.d8 0x21)) s (0x1083e0 + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x1083e0 3 1 (.base 2 (.d8 0x21))) (Reg.operands [.gpr 1, .gpr 2] [])) #v[57, 2]
    (.letOp (n := 64) (.exec 0x1083e3 (StorePre 0x1083e3 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1083e3 + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x1083e3 7 1 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x1083ea (movzxR32M8Effect 0x1083ea 5 1 (.sib 4 none 0 (.d8 0x2a))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 66) (.exec 0x1083ea (LoadPre 0x1083ea (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2a)) s (0x1083ea + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1083ea 5 1 (.sib 4 none 0 (.d8 0x2a))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x1083ef (xorR8M8Effect 0x1083ef 3 1 (.base 2 (.d8 0x22))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[65, 2]
    (.letOp (n := 68) (.exec 0x1083ef (LoadPre 0x1083ef (fun s => AddrMode.addr (.base 2 (.d8 0x22)) s (0x1083ef + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x1083ef 3 1 (.base 2 (.d8 0x22))) (Reg.operands [.gpr 1, .gpr 2] [])) #v[65, 2]
    (.letOp (n := 69) (.exec 0x1083f2 (StorePre 0x1083f2 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1083f2 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1083f2 4 1 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[67, 4]
    (.letOp (n := 70) (.out 0x1083f6 (movzxR32M8Effect 0x1083f6 5 6 (.sib 4 none 0 (.d8 0x2b))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 71) (.exec 0x1083f6 (LoadPre 0x1083f6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2b)) s (0x1083f6 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1083f6 5 6 (.sib 4 none 0 (.d8 0x2b))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.out 0x1083fb (xorR8M8Effect 0x1083fb 4 6 (.base 2 (.d8 0x23))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[70, 2]
    (.letOp (n := 73) (.exec 0x1083fb (LoadPre 0x1083fb (fun s => AddrMode.addr (.base 2 (.d8 0x23)) s (0x1083fb + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1083fb 4 6 (.base 2 (.d8 0x23))) (Reg.operands [.gpr 6, .gpr 2] [])) #v[70, 2]
    (.letOp (n := 74) (.out 0x1083ff (movzxR32M8Effect 0x1083ff 5 7 (.sib 4 none 0 (.d8 0x2c))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 75) (.exec 0x1083ff (LoadPre 0x1083ff (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x1083ff + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1083ff 5 7 (.sib 4 none 0 (.d8 0x2c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 76) (.out 0x108404 (xorR8M8Effect 0x108404 4 7 (.base 2 (.d8 0x24))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2] []) (.reg (.gpr 7))) #v[74, 2]
    (.letOp (n := 77) (.exec 0x108404 (LoadPre 0x108404 (fun s => AddrMode.addr (.base 2 (.d8 0x24)) s (0x108404 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108404 4 7 (.base 2 (.d8 0x24))) (Reg.operands [.gpr 7, .gpr 2] [])) #v[74, 2]
    (.letOp (n := 78) (.out 0x108408 (movzxR32M8Effect 0x108408 6 8 (.sib 4 none 0 (.d8 0x2d))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 79) (.exec 0x108408 (LoadPre 0x108408 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2d)) s (0x108408 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108408 6 8 (.sib 4 none 0 (.d8 0x2d))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 80) (.out 0x10840e (xorR8M8Effect 0x10840e 4 8 (.base 2 (.d8 0x25))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2] []) (.reg (.gpr 8))) #v[78, 2]
    (.letOp (n := 81) (.exec 0x10840e (LoadPre 0x10840e (fun s => AddrMode.addr (.base 2 (.d8 0x25)) s (0x10840e + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10840e 4 8 (.base 2 (.d8 0x25))) (Reg.operands [.gpr 8, .gpr 2] [])) #v[78, 2]
    (.letOp (n := 82) (.out 0x108412 (movzxR32M8Effect 0x108412 6 9 (.sib 4 none 0 (.d8 0x2e))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 83) (.exec 0x108412 (LoadPre 0x108412 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2e)) s (0x108412 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108412 6 9 (.sib 4 none 0 (.d8 0x2e))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 84) (.out 0x108418 (xorR8M8Effect 0x108418 4 9 (.base 2 (.d8 0x26))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2] []) (.reg (.gpr 9))) #v[82, 2]
    (.letOp (n := 85) (.exec 0x108418 (LoadPre 0x108418 (fun s => AddrMode.addr (.base 2 (.d8 0x26)) s (0x108418 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108418 4 9 (.base 2 (.d8 0x26))) (Reg.operands [.gpr 9, .gpr 2] [])) #v[82, 2]
    (.letOp (n := 86) (.out 0x10841c (movzxR32M8Effect 0x10841c 6 10 (.sib 4 none 0 (.d8 0x2f))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 87) (.exec 0x10841c (LoadPre 0x10841c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2f)) s (0x10841c + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x10841c 6 10 (.sib 4 none 0 (.d8 0x2f))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 88) (.out 0x108422 (xorR8M8Effect 0x108422 4 10 (.base 2 (.d8 0x27))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2] []) (.reg (.gpr 10))) #v[86, 2]
    (.letOp (n := 89) (.exec 0x108422 (LoadPre 0x108422 (fun s => AddrMode.addr (.base 2 (.d8 0x27)) s (0x108422 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108422 4 10 (.base 2 (.d8 0x27))) (Reg.operands [.gpr 10, .gpr 2] [])) #v[86, 2]
    (b_l1083c7_1)))))))))))))))))))))))))))))))))))))

def bytes_l1083c7 : List UInt8 :=
  [0x0F, 0xB6, 0x74, 0x24, 0x28, 0x48, 0x89, 0xC8, 0x0F, 0xB6, 0x4C, 0x24, 0x29, 0x40, 0x32, 0x72,
    0x20, 0x40, 0x88, 0xB4, 0x24, 0x88, 0x00, 0x00, 0x00, 0x32, 0x4A, 0x21, 0x88, 0x8C, 0x24, 0x80,
    0x00, 0x00, 0x00, 0x0F, 0xB6, 0x4C, 0x24, 0x2A, 0x32, 0x4A, 0x22, 0x88, 0x4C, 0x24, 0x78, 0x0F,
    0xB6, 0x74, 0x24, 0x2B, 0x40, 0x32, 0x72, 0x23, 0x0F, 0xB6, 0x7C, 0x24, 0x2C, 0x40, 0x32, 0x7A,
    0x24, 0x44, 0x0F, 0xB6, 0x44, 0x24, 0x2D, 0x44, 0x32, 0x42, 0x25, 0x44, 0x0F, 0xB6, 0x4C, 0x24,
    0x2E, 0x44, 0x32, 0x4A, 0x26, 0x44, 0x0F, 0xB6, 0x54, 0x24, 0x2F, 0x44, 0x32, 0x52, 0x27] ++ bytes_l1083c7_1

theorem code_l1083c7 : ∀ x ∈ codeRange 0x1083c7 bytes_l1083c7, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x83c7 95 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1083c7_1

@[cfg_block] def b_l1084c1 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1084c1 (addR64Imm32Effect 0x1084c1 4 0x6d8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 54) (.exec 0x1084c1 (fun s => s.RIP = 0x1084c1) (addR64Imm32Effect 0x1084c1 4 0x6d8) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1084c8 (popR64Effect 0x1084c8 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[53]
    (.letOp (n := 56) (.out 0x1084c8 (popR64Effect 0x1084c8 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[53]
    (.letOp (n := 57) (.exec 0x1084c8 (PopPre 0x1084c8) (popR64Effect 0x1084c8 1 3) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 58) (.out 0x1084c9 (popR64Effect 0x1084c9 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[56]
    (.letOp (n := 59) (.out 0x1084c9 (popR64Effect 0x1084c9 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[56]
    (.letOp (n := 60) (.exec 0x1084c9 (PopPre 0x1084c9) (popR64Effect 0x1084c9 2 12) (Reg.operands [.gpr 4] [])) #v[56]
    (.letOp (n := 61) (.out 0x1084cb (popR64Effect 0x1084cb 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[59]
    (.letOp (n := 62) (.out 0x1084cb (popR64Effect 0x1084cb 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 63) (.exec 0x1084cb (PopPre 0x1084cb) (popR64Effect 0x1084cb 2 13) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 64) (.out 0x1084cd (popR64Effect 0x1084cd 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[62]
    (.letOp (n := 65) (.out 0x1084cd (popR64Effect 0x1084cd 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[62]
    (.letOp (n := 66) (.exec 0x1084cd (PopPre 0x1084cd) (popR64Effect 0x1084cd 2 14) (Reg.operands [.gpr 4] [])) #v[62]
    (.letOp (n := 67) (.out 0x1084cf (popR64Effect 0x1084cf 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[65]
    (.letOp (n := 68) (.out 0x1084cf (popR64Effect 0x1084cf 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 69) (.exec 0x1084cf (PopPre 0x1084cf) (popR64Effect 0x1084cf 2 15) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 70) (.out 0x1084d1 (popR64Effect 0x1084d1 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[68]
    (.letOp (n := 71) (.out 0x1084d1 (popR64Effect 0x1084d1 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[68]
    (.letOp (n := 72) (.exec 0x1084d1 (PopPre 0x1084d1) (popR64Effect 0x1084d1 1 5) (Reg.operands [.gpr 4] [])) #v[68]
    (.letOp (n := 73) (.out 0x1084d2 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[71]
    (.letOp (n := 74) (.out 0x1084d2 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[71]
    (.letOp (n := 75) (.exec 0x1084d2 (RetPre 0x1084d2) (retEffect) (Reg.operands [.gpr 4] [])) #v[71]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 2), (3, 55), (4, 74), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 76) (some ⟨73, by decide⟩)))))))))))))))))))))))))

def bytes_l1084c1 : List UInt8 :=
  [0x48, 0x81, 0xC4, 0xD8, 0x06, 0x00, 0x00, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F,
    0x5D, 0xC3]

theorem code_l1084c1 : ∀ x ∈ codeRange 0x1084c1 bytes_l1084c1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x84c1 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1084e0 : Block Op Label signature Reg.count 53 :=
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
    (.letOp (n := 65) (.out 0x1084ea (subR64Imm32Effect 0x1084ea 4 0x8d8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x1084ea (fun s => s.RIP = 0x1084ea) (subR64Imm32Effect 0x1084ea 4 0x8d8) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x1084f1 (movR64R64Effect 0x1084f1 3 6) (EffectPart.reads (.reg (.gpr 3)) [.gpr 6] []) (.reg (.gpr 3))) #v[6]
    (.letOp (n := 68) (.exec 0x1084f1 (fun s => s.RIP = 0x1084f1) (movR64R64Effect 0x1084f1 3 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 69) (.out 0x1084f4 (movR64M64Effect 0x1084f4 0 (.base 7 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 70) (.exec 0x1084f4 (LoadPre 0x1084f4 (fun s => AddrMode.addr (.base 7 .none) s (0x1084f4 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1084f4 0 (.base 7 .none)) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 71) (.out 0x1084f7 (xorR32R32Effect 0x1084f7 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[1, 1]
    (.letOp (n := 72) (.exec 0x1084f7 (fun s => s.RIP = 0x1084f7) (xorR32R32Effect 0x1084f7 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[1, 1]
    (.letOp (n := 73) (.out 0x1084f9 (movR64Imm64Effect 0x1084f9 2 0x1000001000) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 74) (.exec 0x1084f9 (fun s => s.RIP = 0x1084f9) (movR64Imm64Effect 0x1084f9 2 0x1000001000) (Reg.operands [] [])) #v[]
    (.letOp (n := 75) (.out 0x108503 (movR64Imm64Effect 0x108503 6 0xf000f000f000f) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 76) (.exec 0x108503 (fun s => s.RIP = 0x108503) (movR64Imm64Effect 0x108503 6 0xf000f000f000f) (Reg.operands [] [])) #v[]
    (.letOp (n := 77) (.out 0x10850d (movR64Imm64Effect 0x10850d 7 0x1111111111111111) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 78) (.exec 0x10850d (fun s => s.RIP = 0x10850d) (movR64Imm64Effect 0x10850d 7 0x1111111111111111) (Reg.operands [] [])) #v[]
    (.letOp (n := 79) (.exec 0x108517 (fun s => s.RIP = 0x108517) (fun _ => nopEffect 0x108517 9) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l108520, RegMap.args [(0, 69), (1, 71), (2, 73), (3, 67), (4, 65), (5, 5), (6, 75), (7, 77), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 80⟩))))))))))))))))))))))))))))

def bytes_l1084e0 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0xD8, 0x08, 0x00,
    0x00, 0x48, 0x89, 0xF3, 0x48, 0x8B, 0x07, 0x31, 0xC9, 0x48, 0xBA, 0x00, 0x10, 0x00, 0x00, 0x10,
    0x00, 0x00, 0x00, 0x48, 0xBE, 0x0F, 0x00, 0x0F, 0x00, 0x0F, 0x00, 0x0F, 0x00, 0x48, 0xBF, 0x11,
    0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x66, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem code_l1084e0 : ∀ x ∈ codeRange 0x1084e0 bytes_l1084e0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x84e0 64 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l108520_1 : Block Op Label signature Reg.count 92 :=
  .letOp (n := 92) (.pure (condOp 5)) #v[90]
    (.terminate (.condBr (Fin.last 92) ⟨.l108520, RegMap.args [(0, 0), (1, 88), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 85), (9, 71), (10, 75), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 90), (22, 22), (39, 39), (50, 50), (51, 51)] 93⟩ ⟨.l10856d, RegMap.args [(0, 0), (1, 88), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 85), (9, 71), (10, 75), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 90), (22, 22), (39, 39), (50, 50), (51, 51)] 93⟩))

def bytes_l108520_1 : List UInt8 :=
  [0x75, 0xB3]

theorem code_l108520_1 : ∀ x ∈ codeRange 0x10856b bytes_l108520_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x856b 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l108520 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x108520 (movzxR32M16Effect 0x108520 5 8 (.sib 0 (some 1) 1 .none)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0, .gpr 1] []) (.reg (.gpr 8))) #v[0, 1]
    (.letOp (n := 54) (.exec 0x108520 (LoadPre 0x108520 (fun s => AddrMode.addr (.sib 0 (some 1) 1 .none) s (0x108520 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x108520 5 8 (.sib 0 (some 1) 1 .none)) (Reg.operands [.gpr 0, .gpr 1] [])) #v[0, 1]
    (.letOp (n := 55) (.out 0x108525 (movR64R64Effect 0x108525 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 8] []) (.reg (.gpr 9))) #v[53]
    (.letOp (n := 56) (.exec 0x108525 (fun s => s.RIP = 0x108525) (movR64R64Effect 0x108525 9 8) (Reg.operands [.gpr 8] [])) #v[53]
    (.letOp (n := 57) (.out 0x108528 (shlR64Effect 0x108528 4 9 24) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[55]
    (.letOp (n := 58) (.exec 0x108528 (fun s => s.RIP = 0x108528) (shlR64Effect 0x108528 4 9 24) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[55]
    (.letOp (n := 59) (.out 0x10852c (orR64R64Effect 0x10852c 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8] []) (.reg (.gpr 9))) #v[57, 53]
    (.letOp (n := 60) (.exec 0x10852c (fun s => s.RIP = 0x10852c) (orR64R64Effect 0x10852c 9 8) (Reg.operands [.gpr 9, .gpr 8] [])) #v[57, 53]
    (.letOp (n := 61) (.out 0x10852f (imulR64R64Effect 0x10852f 4 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2] []) (.reg (.gpr 8))) #v[53, 2]
    (.letOp (n := 62) (.exec 0x10852f (fun s => s.RIP = 0x10852f) (imulR64R64Effect 0x10852f 4 8 2) (Reg.operands [.gpr 8, .gpr 2] [])) #v[53, 2]
    (.letOp (n := 63) (.out 0x108533 (orR64R64Effect 0x108533 8 9) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 9] []) (.reg (.gpr 8))) #v[61, 59]
    (.letOp (n := 64) (.exec 0x108533 (fun s => s.RIP = 0x108533) (orR64R64Effect 0x108533 8 9) (Reg.operands [.gpr 8, .gpr 9] [])) #v[61, 59]
    (.letOp (n := 65) (.out 0x108536 (andR64R64Effect 0x108536 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6] []) (.reg (.gpr 8))) #v[63, 6]
    (.letOp (n := 66) (.exec 0x108536 (fun s => s.RIP = 0x108536) (andR64R64Effect 0x108536 8 6) (Reg.operands [.gpr 8, .gpr 6] [])) #v[63, 6]
    (.letOp (n := 67) (.out 0x108539 (movR64R64Effect 0x108539 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 8] []) (.reg (.gpr 9))) #v[65]
    (.letOp (n := 68) (.exec 0x108539 (fun s => s.RIP = 0x108539) (movR64R64Effect 0x108539 9 8) (Reg.operands [.gpr 8] [])) #v[65]
    (.letOp (n := 69) (.out 0x10853c (shlR64Effect 0x10853c 4 9 6) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[67]
    (.letOp (n := 70) (.exec 0x10853c (fun s => s.RIP = 0x10853c) (shlR64Effect 0x10853c 4 9 6) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[67]
    (.letOp (n := 71) (.out 0x108540 (orR64R64Effect 0x108540 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8] []) (.reg (.gpr 9))) #v[69, 65]
    (.letOp (n := 72) (.exec 0x108540 (fun s => s.RIP = 0x108540) (orR64R64Effect 0x108540 9 8) (Reg.operands [.gpr 9, .gpr 8] [])) #v[69, 65]
    (.letOp (n := 73) (.out 0x108543 (movR64R64Effect 0x108543 10 8) (EffectPart.reads (.reg (.gpr 10)) [.gpr 8] []) (.reg (.gpr 10))) #v[65]
    (.letOp (n := 74) (.exec 0x108543 (fun s => s.RIP = 0x108543) (movR64R64Effect 0x108543 10 8) (Reg.operands [.gpr 8] [])) #v[65]
    (.letOp (n := 75) (.out 0x108546 (shlR64Effect 0x108546 4 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[73]
    (.letOp (n := 76) (.exec 0x108546 (fun s => s.RIP = 0x108546) (shlR64Effect 0x108546 4 10 9) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[73]
    (.letOp (n := 77) (.out 0x10854a (leaR64Effect 0x10854a 8 (.sib 10 (some 8) 3 .none)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 10, .gpr 8] []) (.reg (.gpr 8))) #v[75, 65]
    (.letOp (n := 78) (.exec 0x10854a (fun s => s.RIP = 0x10854a) (leaR64Effect 0x10854a 8 (.sib 10 (some 8) 3 .none)) (Reg.operands [.gpr 10, .gpr 8] [])) #v[75, 65]
    (.letOp (n := 79) (.out 0x10854e (orR64R64Effect 0x10854e 8 9) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 9] []) (.reg (.gpr 8))) #v[77, 71]
    (.letOp (n := 80) (.exec 0x10854e (fun s => s.RIP = 0x10854e) (orR64R64Effect 0x10854e 8 9) (Reg.operands [.gpr 8, .gpr 9] [])) #v[77, 71]
    (.letOp (n := 81) (.out 0x108551 (andR64R64Effect 0x108551 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 7] []) (.reg (.gpr 8))) #v[79, 7]
    (.letOp (n := 82) (.exec 0x108551 (fun s => s.RIP = 0x108551) (andR64R64Effect 0x108551 8 7) (Reg.operands [.gpr 8, .gpr 7] [])) #v[79, 7]
    (.letOp (n := 83) (.out 0x108554 (leaR64Effect 0x108554 8 (.sib 8 (some 8) 2 .none)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 8] []) (.reg (.gpr 8))) #v[81, 81]
    (.letOp (n := 84) (.exec 0x108554 (fun s => s.RIP = 0x108554) (leaR64Effect 0x108554 8 (.sib 8 (some 8) 2 .none)) (Reg.operands [.gpr 8, .gpr 8] [])) #v[81, 81]
    (.letOp (n := 85) (.out 0x108558 (leaR64Effect 0x108558 8 (.sib 8 (some 8) 1 .none)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 8] []) (.reg (.gpr 8))) #v[83, 83]
    (.letOp (n := 86) (.exec 0x108558 (fun s => s.RIP = 0x108558) (leaR64Effect 0x108558 8 (.sib 8 (some 8) 1 .none)) (Reg.operands [.gpr 8, .gpr 8] [])) #v[83, 83]
    (.letOp (n := 87) (.exec 0x10855c (StorePre 0x10855c 8 (fun s => AddrMode.addr (.sib 4 (some 1) 3 (.d32 0x518)) s (0x10855c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10855c 8 (.sib 4 (some 1) 3 (.d32 0x518))) (Reg.operands [.gpr 8, .gpr 4, .gpr 1] [])) #v[85, 4, 1]
    (.letOp (n := 88) (.out 0x108564 (incR64Effect 0x108564 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1]
    (.letOp (n := 89) (.exec 0x108564 (fun s => s.RIP = 0x108564) (incR64Effect 0x108564 1) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1]
    (.letOp (n := 90) (.out 0x108567 (cmpR64Imm8Effect 0x108567 1 0x78) (EffectPart.reads (.flag .ZF) [.gpr 1] []) (.flag .ZF)) #v[88]
    (.letOp (n := 91) (.exec 0x108567 (fun s => s.RIP = 0x108567) (cmpR64Imm8Effect 0x108567 1 0x78) (Reg.operands [.gpr 1] [])) #v[88]
    (b_l108520_1)))))))))))))))))))))))))))))))))))))))

def bytes_l108520 : List UInt8 :=
  [0x44, 0x0F, 0xB7, 0x04, 0x48, 0x4D, 0x89, 0xC1, 0x49, 0xC1, 0xE1, 0x18, 0x4D, 0x09, 0xC1, 0x4C,
    0x0F, 0xAF, 0xC2, 0x4D, 0x09, 0xC8, 0x49, 0x21, 0xF0, 0x4D, 0x89, 0xC1, 0x49, 0xC1, 0xE1, 0x06,
    0x4D, 0x09, 0xC1, 0x4D, 0x89, 0xC2, 0x49, 0xC1, 0xE2, 0x09, 0x4F, 0x8D, 0x04, 0xC2, 0x4D, 0x09,
    0xC8, 0x49, 0x21, 0xF8, 0x4F, 0x8D, 0x04, 0x80, 0x4F, 0x8D, 0x04, 0x40, 0x4C, 0x89, 0x84, 0xCC,
    0x18, 0x05, 0x00, 0x00, 0x48, 0xFF, 0xC1, 0x48, 0x83, 0xF9, 0x78] ++ bytes_l108520_1

theorem code_l108520 : ∀ x ∈ codeRange 0x108520 bytes_l108520, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x8520 75 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l108520_1

@[cfg_block] def b_l10856d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x10856d (StorePre 0x10856d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x150)) s (0x10856d + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10856d 0 (.sib 4 none 0 (.d32 0x150))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[0, 4]
    (.letOp (n := 54) (.out 0x108575 (leaR64Effect 0x108575 7 (.sib 4 none 0 (.d32 0x158))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 55) (.exec 0x108575 (fun s => s.RIP = 0x108575) (leaR64Effect 0x108575 7 (.sib 4 none 0 (.d32 0x158))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x10857d (leaR64Effect 0x10857d 6 (.sib 4 none 0 (.d32 0x518))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 57) (.exec 0x10857d (fun s => s.RIP = 0x10857d) (leaR64Effect 0x10857d 6 (.sib 4 none 0 (.d32 0x518))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.out 0x108585 (movR32Imm32Effect 0x108585 5 2 0x3c0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 59) (.exec 0x108585 (fun s => s.RIP = 0x108585) (movR32Imm32Effect 0x108585 5 2 0x3c0) (Reg.operands [] [])) #v[]
    (.letOp (n := 60) (.out 0x10858a (callEffect (callMemPtr 0x10858a (.rip 0xf8c78)) (0x10858a + BitVec.ofNat 64 (callMemLen (.rip 0xf8c78)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 61) (.exec 0x10858a (GoesTo (CallMemPre 0x10858a (.rip 0xf8c78)) (callEffect (callMemPtr 0x10858a (.rip 0xf8c78)) (0x10858a + BitVec.ofNat 64 (callMemLen (.rip 0xf8c78)))) 0x103f00) (callEffect (callMemPtr 0x10858a (.rip 0xf8c78)) (0x10858a + BitVec.ofNat 64 (callMemLen (.rip 0xf8c78)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.const ⟨64, 0x108590⟩) #v[]
    (.terminate (.call ⟨.l103f00, RegMap.args [(0, 0), (2, 58), (3, 3), (4, 60), (5, 5), (6, 56), (7, 54), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 63⟩ { target := .l108590, kept := #v[], arity := rfl, guard := some (Fin.last 62) })))))))))))

def bytes_l10856d : List UInt8 :=
  [0x48, 0x89, 0x84, 0x24, 0x50, 0x01, 0x00, 0x00, 0x48, 0x8D, 0xBC, 0x24, 0x58, 0x01, 0x00, 0x00,
    0x48, 0x8D, 0xB4, 0x24, 0x18, 0x05, 0x00, 0x00, 0xBA, 0xC0, 0x03, 0x00, 0x00, 0xFF, 0x15, 0x78,
    0x8C, 0x0F, 0x00]

theorem code_l10856d : ∀ x ∈ codeRange 0x10856d bytes_l10856d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x856d 35 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l108590 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x108590 (movR64M64Effect 0x108590 9 (.base 3 .none)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 3] []) (.reg (.gpr 9))) #v[3]
    (.letOp (n := 54) (.exec 0x108590 (LoadPre 0x108590 (fun s => AddrMode.addr (.base 3 .none) s (0x108590 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x108590 9 (.base 3 .none)) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x108593 (movR64M64Effect 0x108593 0 (.base 3 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 56) (.exec 0x108593 (LoadPre 0x108593 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x108593 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x108593 0 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 57) (.exec 0x108597 (StorePre 0x108597 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x108597 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108597 0 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 58) (.out 0x10859f (movR64M64Effect 0x10859f 2 (.base 3 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3] []) (.reg (.gpr 2))) #v[3]
    (.letOp (n := 59) (.exec 0x10859f (LoadPre 0x10859f (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x10859f + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10859f 2 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 60) (.out 0x1085a3 (movR64M64Effect 0x1085a3 0 (.base 3 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 61) (.exec 0x1085a3 (LoadPre 0x1085a3 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x1085a3 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1085a3 0 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 62) (.out 0x1085a7 (movR64R64Effect 0x1085a7 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[60]
    (.letOp (n := 63) (.exec 0x1085a7 (fun s => s.RIP = 0x1085a7) (movR64R64Effect 0x1085a7 1 0) (Reg.operands [.gpr 0] [])) #v[60]
    (.letOp (n := 64) (.out 0x1085aa (shrR64Effect 0x1085aa 4 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[62]
    (.letOp (n := 65) (.exec 0x1085aa (fun s => s.RIP = 0x1085aa) (shrR64Effect 0x1085aa 4 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[62]
    (.letOp (n := 66) (.exec 0x1085ae (StorePre 0x1085ae 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x1085ae + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1085ae 0 (.sib 4 none 0 (.d32 0x140))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[60, 4]
    (.letOp (n := 67) (.out 0x1085b6 (andR32Imm8Effect 0x1085b6 3 0 0x3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[60]
    (.letOp (n := 68) (.exec 0x1085b6 (fun s => s.RIP = 0x1085b6) (andR32Imm8Effect 0x1085b6 3 0 0x3) (Reg.operands [.gpr 0] [])) #v[60]
    (.letOp (n := 69) (.exec 0x1085b9 (StorePre 0x1085b9 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x1085b9 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1085b9 0 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[67, 4]
    (.letOp (n := 70) (.exec 0x1085c1 (StorePre 0x1085c1 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x148)) s (0x1085c1 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1085c1 1 (.sib 4 none 0 (.d32 0x148))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 71) (.out 0x1085c9 (testR64R64Effect 0x1085c9 1 1) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 1] []) (.flag .ZF)) #v[64, 64]
    (.letOp (n := 72) (.exec 0x1085c9 (fun s => s.RIP = 0x1085c9) (testR64R64Effect 0x1085c9 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[64, 64]
    (.letOp (n := 73) (.exec 0x1085cc (StorePre 0x1085cc 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x1085cc + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1085cc 9 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 74) (.pure (condOp 4)) #v[71]
    (.terminate (.condBr (Fin.last 74) ⟨.l109509, RegMap.args [(0, 67), (1, 64), (2, 58), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 71), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ ⟨.l1085da, RegMap.args [(0, 67), (1, 64), (2, 58), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 71), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩)))))))))))))))))))))))

def bytes_l108590 : List UInt8 :=
  [0x4C, 0x8B, 0x0B, 0x48, 0x8B, 0x43, 0x08, 0x48, 0x89, 0x84, 0x24, 0xF0, 0x00, 0x00, 0x00, 0x48,
    0x8B, 0x53, 0x10, 0x48, 0x8B, 0x43, 0x18, 0x48, 0x89, 0xC1, 0x48, 0xC1, 0xE9, 0x02, 0x48, 0x89,
    0x84, 0x24, 0x40, 0x01, 0x00, 0x00, 0x83, 0xE0, 0x03, 0x48, 0x89, 0x84, 0x24, 0xE8, 0x00, 0x00,
    0x00, 0x48, 0x89, 0x8C, 0x24, 0x48, 0x01, 0x00, 0x00, 0x48, 0x85, 0xC9, 0x4C, 0x89, 0x8C, 0x24,
    0xF8, 0x00, 0x00, 0x00, 0x0F, 0x84, 0x2F, 0x0F, 0x00, 0x00]

theorem code_l108590 : ∀ x ∈ codeRange 0x108590 bytes_l108590, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x8590 74 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1085da : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1085da (StorePre 0x1085da 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x1085da + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1085da (.sib 4 none 0 (.d32 0xe0)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.exec 0x1085e6 (StorePre 0x1085e6 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x1085e6 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1085e6 2 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2, 4]
    (.terminate (.br ⟨.l108e98, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l1085da : List UInt8 :=
  [0x48, 0xC7, 0x84, 0x24, 0xE0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0x89, 0x94, 0x24,
    0xD8, 0x00, 0x00, 0x00, 0xE9, 0xA5, 0x08, 0x00, 0x00]

theorem code_l1085da : ∀ x ∈ codeRange 0x1085da bytes_l1085da, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x85da 25 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l108600_3 : Block Op Label signature Reg.count 166 :=
  .letOp (n := 166) (.out 0x1086df (xorR64R64Effect 0x1086df 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[164, 1]
    (.letOp (n := 167) (.exec 0x1086df (fun s => s.RIP = 0x1086df) (xorR64R64Effect 0x1086df 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[164, 1]
    (.letOp (n := 168) (.out 0x1086e2 (andR64R64Effect 0x1086e2 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 14] []) (.reg (.gpr 2))) #v[166, 64]
    (.letOp (n := 169) (.exec 0x1086e2 (fun s => s.RIP = 0x1086e2) (andR64R64Effect 0x1086e2 2 14) (Reg.operands [.gpr 2, .gpr 14] [])) #v[166, 64]
    (.letOp (n := 170) (.out 0x1086e5 (movR64R64Effect 0x1086e5 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[168]
    (.letOp (n := 171) (.exec 0x1086e5 (fun s => s.RIP = 0x1086e5) (movR64R64Effect 0x1086e5 6 2) (Reg.operands [.gpr 2] [])) #v[168]
    (.letOp (n := 172) (.out 0x1086e8 (shlR64Effect 0x1086e8 4 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[170]
    (.letOp (n := 173) (.exec 0x1086e8 (fun s => s.RIP = 0x1086e8) (shlR64Effect 0x1086e8 4 6 8) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[170]
    (.letOp (n := 174) (.out 0x1086ec (addR64R64Effect 0x1086ec 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[172, 168]
    (.letOp (n := 175) (.exec 0x1086ec (fun s => s.RIP = 0x1086ec) (addR64R64Effect 0x1086ec 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[172, 168]
    (.letOp (n := 176) (.out 0x1086ef (xorR64R64Effect 0x1086ef 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[174, 1]
    (.letOp (n := 177) (.exec 0x1086ef (fun s => s.RIP = 0x1086ef) (xorR64R64Effect 0x1086ef 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[174, 1]
    (.letOp (n := 178) (.exec 0x1086f2 (StorePre 0x1086f2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1086f2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1086f2 6 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[176, 4]
    (.letOp (n := 179) (.out 0x1086f7 (movR64R64Effect 0x1086f7 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[0]
    (.letOp (n := 180) (.exec 0x1086f7 (fun s => s.RIP = 0x1086f7) (movR64R64Effect 0x1086f7 1 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 181) (.out 0x1086fa (shrR64Effect 0x1086fa 4 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[179]
    (.letOp (n := 182) (.exec 0x1086fa (fun s => s.RIP = 0x1086fa) (shrR64Effect 0x1086fa 4 1 8) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[179]
    (.letOp (n := 183) (.out 0x1086fe (xorR64R64Effect 0x1086fe 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[181, 0]
    (.letOp (n := 184) (.exec 0x1086fe (fun s => s.RIP = 0x1086fe) (xorR64R64Effect 0x1086fe 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[181, 0]
    (.letOp (n := 185) (.out 0x108701 (andR64R64Effect 0x108701 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 14] []) (.reg (.gpr 1))) #v[183, 64]
    (.letOp (n := 186) (.exec 0x108701 (fun s => s.RIP = 0x108701) (andR64R64Effect 0x108701 1 14) (Reg.operands [.gpr 1, .gpr 14] [])) #v[183, 64]
    (.letOp (n := 187) (.out 0x108704 (movR64R64Effect 0x108704 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[185]
    (.letOp (n := 188) (.exec 0x108704 (fun s => s.RIP = 0x108704) (movR64R64Effect 0x108704 2 1) (Reg.operands [.gpr 1] [])) #v[185]
    (.letOp (n := 189) (.out 0x108707 (shlR64Effect 0x108707 4 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[187]
    (.letOp (n := 190) (.exec 0x108707 (fun s => s.RIP = 0x108707) (shlR64Effect 0x108707 4 2 8) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[187]
    (.letOp (n := 191) (.out 0x10870b (addR64R64Effect 0x10870b 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[189, 185]
    (.letOp (n := 192) (.exec 0x10870b (fun s => s.RIP = 0x10870b) (addR64R64Effect 0x10870b 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[189, 185]
    (.letOp (n := 193) (.out 0x10870e (xorR64R64Effect 0x10870e 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[191, 0]
    (.letOp (n := 194) (.exec 0x10870e (fun s => s.RIP = 0x10870e) (xorR64R64Effect 0x10870e 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[191, 0]
    (.letOp (n := 195) (.exec 0x108711 (StorePre 0x108711 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x108711 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108711 2 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[193, 4]
    (.letOp (n := 196) (.out 0x108716 (movR32Imm32Effect 0x108716 5 6 0x8) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 197) (.exec 0x108716 (fun s => s.RIP = 0x108716) (movR32Imm32Effect 0x108716 5 6 0x8) (Reg.operands [] [])) #v[]
    (.letOp (n := 198) (.out 0x10871b (leaR64Effect 0x10871b 3 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 199) (.exec 0x10871b (fun s => s.RIP = 0x10871b) (leaR64Effect 0x10871b 3 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 200) (.out 0x108720 (movR64R64Effect 0x108720 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[198]
    (.letOp (n := 201) (.exec 0x108720 (fun s => s.RIP = 0x108720) (movR64R64Effect 0x108720 7 3) (Reg.operands [.gpr 3] [])) #v[198]
    (.letOp (n := 202) (.out 0x108723 (callEffect (fun _ => 0x100e90) 0x108728) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 203) (.exec 0x108723 (PushPre 0x108723 5) (callEffect (fun _ => 0x100e90) 0x108728) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 204) (.const ⟨64, 0x108728⟩) #v[]
    (.terminate (.call ⟨.l100e90, RegMap.args [(0, 0), (1, 185), (2, 193), (3, 198), (4, 202), (5, 56), (6, 196), (7, 200), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 205⟩ { target := .l108728, kept := #v[], arity := rfl, guard := some (Fin.last 204) }))))))))))))))))))))))))))))))))))))))))

def bytes_l108600_3 : List UInt8 :=
  [0x48, 0x31, 0xCA, 0x4C, 0x21, 0xF2, 0x48, 0x89, 0xD6, 0x48, 0xC1, 0xE6, 0x08, 0x48, 0x01, 0xD6,
    0x48, 0x31, 0xCE, 0x48, 0x89, 0x74, 0x24, 0x38, 0x48, 0x89, 0xC1, 0x48, 0xC1, 0xE9, 0x08, 0x48,
    0x31, 0xC1, 0x4C, 0x21, 0xF1, 0x48, 0x89, 0xCA, 0x48, 0xC1, 0xE2, 0x08, 0x48, 0x01, 0xCA, 0x48,
    0x31, 0xC2, 0x48, 0x89, 0x54, 0x24, 0x40, 0xBE, 0x08, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x5C, 0x24,
    0x08, 0x48, 0x89, 0xDF, 0xE8, 0x68, 0x87, 0xFF, 0xFF]

theorem code_l108600_3 : ∀ x ∈ codeRange 0x1086df bytes_l108600_3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x86df 73 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l108600_2 : Block Op Label signature Reg.count 128 :=
  .letOp (n := 128) (.out 0x10869a (movR64R64Effect 0x10869a 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[6]
    (.letOp (n := 129) (.exec 0x10869a (fun s => s.RIP = 0x10869a) (movR64R64Effect 0x10869a 7 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 130) (.out 0x10869d (shrR64Effect 0x10869d 4 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[128]
    (.letOp (n := 131) (.exec 0x10869d (fun s => s.RIP = 0x10869d) (shrR64Effect 0x10869d 4 7 8) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[128]
    (.letOp (n := 132) (.out 0x1086a1 (xorR64R64Effect 0x1086a1 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[130, 6]
    (.letOp (n := 133) (.exec 0x1086a1 (fun s => s.RIP = 0x1086a1) (xorR64R64Effect 0x1086a1 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[130, 6]
    (.letOp (n := 134) (.out 0x1086a4 (andR64R64Effect 0x1086a4 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 14] []) (.reg (.gpr 7))) #v[132, 64]
    (.letOp (n := 135) (.exec 0x1086a4 (fun s => s.RIP = 0x1086a4) (andR64R64Effect 0x1086a4 7 14) (Reg.operands [.gpr 7, .gpr 14] [])) #v[132, 64]
    (.letOp (n := 136) (.out 0x1086a7 (movR64R64Effect 0x1086a7 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 7] []) (.reg (.gpr 8))) #v[134]
    (.letOp (n := 137) (.exec 0x1086a7 (fun s => s.RIP = 0x1086a7) (movR64R64Effect 0x1086a7 8 7) (Reg.operands [.gpr 7] [])) #v[134]
    (.letOp (n := 138) (.out 0x1086aa (shlR64Effect 0x1086aa 4 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[136]
    (.letOp (n := 139) (.exec 0x1086aa (fun s => s.RIP = 0x1086aa) (shlR64Effect 0x1086aa 4 8 8) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[136]
    (.letOp (n := 140) (.out 0x1086ae (addR64R64Effect 0x1086ae 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 7] []) (.reg (.gpr 8))) #v[138, 134]
    (.letOp (n := 141) (.exec 0x1086ae (fun s => s.RIP = 0x1086ae) (addR64R64Effect 0x1086ae 8 7) (Reg.operands [.gpr 8, .gpr 7] [])) #v[138, 134]
    (.letOp (n := 142) (.out 0x1086b1 (xorR64R64Effect 0x1086b1 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6] []) (.reg (.gpr 8))) #v[140, 6]
    (.letOp (n := 143) (.exec 0x1086b1 (fun s => s.RIP = 0x1086b1) (xorR64R64Effect 0x1086b1 8 6) (Reg.operands [.gpr 8, .gpr 6] [])) #v[140, 6]
    (.letOp (n := 144) (.exec 0x1086b4 (StorePre 0x1086b4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1086b4 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1086b4 8 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[142, 4]
    (.letOp (n := 145) (.out 0x1086b9 (movR64R64Effect 0x1086b9 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[2]
    (.letOp (n := 146) (.exec 0x1086b9 (fun s => s.RIP = 0x1086b9) (movR64R64Effect 0x1086b9 6 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 147) (.out 0x1086bc (shrR64Effect 0x1086bc 4 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[145]
    (.letOp (n := 148) (.exec 0x1086bc (fun s => s.RIP = 0x1086bc) (shrR64Effect 0x1086bc 4 6 8) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[145]
    (.letOp (n := 149) (.out 0x1086c0 (xorR64R64Effect 0x1086c0 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[147, 2]
    (.letOp (n := 150) (.exec 0x1086c0 (fun s => s.RIP = 0x1086c0) (xorR64R64Effect 0x1086c0 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[147, 2]
    (.letOp (n := 151) (.out 0x1086c3 (andR64R64Effect 0x1086c3 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 14] []) (.reg (.gpr 6))) #v[149, 64]
    (.letOp (n := 152) (.exec 0x1086c3 (fun s => s.RIP = 0x1086c3) (andR64R64Effect 0x1086c3 6 14) (Reg.operands [.gpr 6, .gpr 14] [])) #v[149, 64]
    (.letOp (n := 153) (.out 0x1086c6 (movR64R64Effect 0x1086c6 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[151]
    (.letOp (n := 154) (.exec 0x1086c6 (fun s => s.RIP = 0x1086c6) (movR64R64Effect 0x1086c6 7 6) (Reg.operands [.gpr 6] [])) #v[151]
    (.letOp (n := 155) (.out 0x1086c9 (shlR64Effect 0x1086c9 4 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[153]
    (.letOp (n := 156) (.exec 0x1086c9 (fun s => s.RIP = 0x1086c9) (shlR64Effect 0x1086c9 4 7 8) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[153]
    (.letOp (n := 157) (.out 0x1086cd (addR64R64Effect 0x1086cd 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[155, 151]
    (.letOp (n := 158) (.exec 0x1086cd (fun s => s.RIP = 0x1086cd) (addR64R64Effect 0x1086cd 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[155, 151]
    (.letOp (n := 159) (.out 0x1086d0 (xorR64R64Effect 0x1086d0 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2] []) (.reg (.gpr 7))) #v[157, 2]
    (.letOp (n := 160) (.exec 0x1086d0 (fun s => s.RIP = 0x1086d0) (xorR64R64Effect 0x1086d0 7 2) (Reg.operands [.gpr 7, .gpr 2] [])) #v[157, 2]
    (.letOp (n := 161) (.exec 0x1086d3 (StorePre 0x1086d3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1086d3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1086d3 7 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[159, 4]
    (.letOp (n := 162) (.out 0x1086d8 (movR64R64Effect 0x1086d8 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[1]
    (.letOp (n := 163) (.exec 0x1086d8 (fun s => s.RIP = 0x1086d8) (movR64R64Effect 0x1086d8 2 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 164) (.out 0x1086db (shrR64Effect 0x1086db 4 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[162]
    (.letOp (n := 165) (.exec 0x1086db (fun s => s.RIP = 0x1086db) (shrR64Effect 0x1086db 4 2 8) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[162]
    (b_l108600_3))))))))))))))))))))))))))))))))))))))

def bytes_l108600_2 : List UInt8 :=
  [0x48, 0x89, 0xF7, 0x48, 0xC1, 0xEF, 0x08, 0x48, 0x31, 0xF7, 0x4C, 0x21, 0xF7, 0x49, 0x89, 0xF8,
    0x49, 0xC1, 0xE0, 0x08, 0x49, 0x01, 0xF8, 0x49, 0x31, 0xF0, 0x4C, 0x89, 0x44, 0x24, 0x28, 0x48,
    0x89, 0xD6, 0x48, 0xC1, 0xEE, 0x08, 0x48, 0x31, 0xD6, 0x4C, 0x21, 0xF6, 0x48, 0x89, 0xF7, 0x48,
    0xC1, 0xE7, 0x08, 0x48, 0x01, 0xF7, 0x48, 0x31, 0xD7, 0x48, 0x89, 0x7C, 0x24, 0x30, 0x48, 0x89,
    0xCA, 0x48, 0xC1, 0xEA, 0x08] ++ bytes_l108600_3

theorem code_l108600_2 : ∀ x ∈ codeRange 0x10869a bytes_l108600_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x869a 69 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l108600_3

@[cfg_block] def b_l108600_1 : Block Op Label signature Reg.count 91 :=
  .letOp (n := 91) (.out 0x108654 (xorR64R64Effect 0x108654 11 9) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 9] []) (.reg (.gpr 11))) #v[89, 9]
    (.letOp (n := 92) (.exec 0x108654 (fun s => s.RIP = 0x108654) (xorR64R64Effect 0x108654 11 9) (Reg.operands [.gpr 11, .gpr 9] [])) #v[89, 9]
    (.letOp (n := 93) (.exec 0x108657 (StorePre 0x108657 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108657 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108657 11 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[91, 4]
    (.letOp (n := 94) (.out 0x10865c (movR64R64Effect 0x10865c 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 8] []) (.reg (.gpr 9))) #v[8]
    (.letOp (n := 95) (.exec 0x10865c (fun s => s.RIP = 0x10865c) (movR64R64Effect 0x10865c 9 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 96) (.out 0x10865f (shrR64Effect 0x10865f 4 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[94]
    (.letOp (n := 97) (.exec 0x10865f (fun s => s.RIP = 0x10865f) (shrR64Effect 0x10865f 4 9 8) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[94]
    (.letOp (n := 98) (.out 0x108663 (xorR64R64Effect 0x108663 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8] []) (.reg (.gpr 9))) #v[96, 8]
    (.letOp (n := 99) (.exec 0x108663 (fun s => s.RIP = 0x108663) (xorR64R64Effect 0x108663 9 8) (Reg.operands [.gpr 9, .gpr 8] [])) #v[96, 8]
    (.letOp (n := 100) (.out 0x108666 (andR64R64Effect 0x108666 9 14) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 14] []) (.reg (.gpr 9))) #v[98, 64]
    (.letOp (n := 101) (.exec 0x108666 (fun s => s.RIP = 0x108666) (andR64R64Effect 0x108666 9 14) (Reg.operands [.gpr 9, .gpr 14] [])) #v[98, 64]
    (.letOp (n := 102) (.out 0x108669 (movR64R64Effect 0x108669 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 9] []) (.reg (.gpr 10))) #v[100]
    (.letOp (n := 103) (.exec 0x108669 (fun s => s.RIP = 0x108669) (movR64R64Effect 0x108669 10 9) (Reg.operands [.gpr 9] [])) #v[100]
    (.letOp (n := 104) (.out 0x10866c (shlR64Effect 0x10866c 4 10 8) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[102]
    (.letOp (n := 105) (.exec 0x10866c (fun s => s.RIP = 0x10866c) (shlR64Effect 0x10866c 4 10 8) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[102]
    (.letOp (n := 106) (.out 0x108670 (addR64R64Effect 0x108670 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9] []) (.reg (.gpr 10))) #v[104, 100]
    (.letOp (n := 107) (.exec 0x108670 (fun s => s.RIP = 0x108670) (addR64R64Effect 0x108670 10 9) (Reg.operands [.gpr 10, .gpr 9] [])) #v[104, 100]
    (.letOp (n := 108) (.out 0x108673 (xorR64R64Effect 0x108673 10 8) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 8] []) (.reg (.gpr 10))) #v[106, 8]
    (.letOp (n := 109) (.exec 0x108673 (fun s => s.RIP = 0x108673) (xorR64R64Effect 0x108673 10 8) (Reg.operands [.gpr 10, .gpr 8] [])) #v[106, 8]
    (.letOp (n := 110) (.exec 0x108676 (StorePre 0x108676 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x108676 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108676 10 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[108, 4]
    (.letOp (n := 111) (.out 0x10867b (movR64R64Effect 0x10867b 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 7] []) (.reg (.gpr 8))) #v[7]
    (.letOp (n := 112) (.exec 0x10867b (fun s => s.RIP = 0x10867b) (movR64R64Effect 0x10867b 8 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 113) (.out 0x10867e (shrR64Effect 0x10867e 4 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[111]
    (.letOp (n := 114) (.exec 0x10867e (fun s => s.RIP = 0x10867e) (shrR64Effect 0x10867e 4 8 8) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[111]
    (.letOp (n := 115) (.out 0x108682 (xorR64R64Effect 0x108682 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 7] []) (.reg (.gpr 8))) #v[113, 7]
    (.letOp (n := 116) (.exec 0x108682 (fun s => s.RIP = 0x108682) (xorR64R64Effect 0x108682 8 7) (Reg.operands [.gpr 8, .gpr 7] [])) #v[113, 7]
    (.letOp (n := 117) (.out 0x108685 (andR64R64Effect 0x108685 8 14) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 14] []) (.reg (.gpr 8))) #v[115, 64]
    (.letOp (n := 118) (.exec 0x108685 (fun s => s.RIP = 0x108685) (andR64R64Effect 0x108685 8 14) (Reg.operands [.gpr 8, .gpr 14] [])) #v[115, 64]
    (.letOp (n := 119) (.out 0x108688 (movR64R64Effect 0x108688 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 8] []) (.reg (.gpr 9))) #v[117]
    (.letOp (n := 120) (.exec 0x108688 (fun s => s.RIP = 0x108688) (movR64R64Effect 0x108688 9 8) (Reg.operands [.gpr 8] [])) #v[117]
    (.letOp (n := 121) (.out 0x10868b (shlR64Effect 0x10868b 4 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[119]
    (.letOp (n := 122) (.exec 0x10868b (fun s => s.RIP = 0x10868b) (shlR64Effect 0x10868b 4 9 8) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[119]
    (.letOp (n := 123) (.out 0x10868f (addR64R64Effect 0x10868f 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8] []) (.reg (.gpr 9))) #v[121, 117]
    (.letOp (n := 124) (.exec 0x10868f (fun s => s.RIP = 0x10868f) (addR64R64Effect 0x10868f 9 8) (Reg.operands [.gpr 9, .gpr 8] [])) #v[121, 117]
    (.letOp (n := 125) (.out 0x108692 (xorR64R64Effect 0x108692 9 7) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 7] []) (.reg (.gpr 9))) #v[123, 7]
    (.letOp (n := 126) (.exec 0x108692 (fun s => s.RIP = 0x108692) (xorR64R64Effect 0x108692 9 7) (Reg.operands [.gpr 9, .gpr 7] [])) #v[123, 7]
    (.letOp (n := 127) (.exec 0x108695 (StorePre 0x108695 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x108695 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108695 9 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[125, 4]
    (b_l108600_2)))))))))))))))))))))))))))))))))))))

def bytes_l108600_1 : List UInt8 :=
  [0x4D, 0x31, 0xCB, 0x4C, 0x89, 0x5C, 0x24, 0x10, 0x4D, 0x89, 0xC1, 0x49, 0xC1, 0xE9, 0x08, 0x4D,
    0x31, 0xC1, 0x4D, 0x21, 0xF1, 0x4D, 0x89, 0xCA, 0x49, 0xC1, 0xE2, 0x08, 0x4D, 0x01, 0xCA, 0x4D,
    0x31, 0xC2, 0x4C, 0x89, 0x54, 0x24, 0x18, 0x49, 0x89, 0xF8, 0x49, 0xC1, 0xE8, 0x08, 0x49, 0x31,
    0xF8, 0x4D, 0x21, 0xF0, 0x4D, 0x89, 0xC1, 0x49, 0xC1, 0xE1, 0x08, 0x4D, 0x01, 0xC1, 0x49, 0x31,
    0xF9, 0x4C, 0x89, 0x4C, 0x24, 0x20] ++ bytes_l108600_2

theorem code_l108600_1 : ∀ x ∈ codeRange 0x108654 bytes_l108600_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x8654 70 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l108600_2

@[cfg_block] def b_l108600 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x108600 (movR64M64Effect 0x108600 5 (.sib 4 none 0 (.d32 0xe0))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 54) (.exec 0x108600 (LoadPre 0x108600 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x108600 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x108600 5 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x108608 (StorePre 0x108608 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x108608 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108608 5 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x108610 (shlR64Effect 0x108610 4 5 6) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[53]
    (.letOp (n := 57) (.exec 0x108610 (fun s => s.RIP = 0x108610) (shlR64Effect 0x108610 4 5 6) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 58) (.out 0x108614 (movR64R64Effect 0x108614 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 10] []) (.reg (.gpr 11))) #v[10]
    (.letOp (n := 59) (.exec 0x108614 (fun s => s.RIP = 0x108614) (movR64R64Effect 0x108614 11 10) (Reg.operands [.gpr 10] [])) #v[10]
    (.letOp (n := 60) (.out 0x108617 (shrR64Effect 0x108617 4 11 8) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[58]
    (.letOp (n := 61) (.exec 0x108617 (fun s => s.RIP = 0x108617) (shrR64Effect 0x108617 4 11 8) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[58]
    (.letOp (n := 62) (.out 0x10861b (xorR64R64Effect 0x10861b 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 10] []) (.reg (.gpr 11))) #v[60, 10]
    (.letOp (n := 63) (.exec 0x10861b (fun s => s.RIP = 0x10861b) (xorR64R64Effect 0x10861b 11 10) (Reg.operands [.gpr 11, .gpr 10] [])) #v[60, 10]
    (.letOp (n := 64) (.out 0x10861e (movR64Imm64Effect 0x10861e 14 0xff000000ff0000) (EffectPart.reads (.reg (.gpr 14)) [] []) (.reg (.gpr 14))) #v[]
    (.letOp (n := 65) (.exec 0x10861e (fun s => s.RIP = 0x10861e) (movR64Imm64Effect 0x10861e 14 0xff000000ff0000) (Reg.operands [] [])) #v[]
    (.letOp (n := 66) (.out 0x108628 (andR64R64Effect 0x108628 11 14) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 14] []) (.reg (.gpr 11))) #v[62, 64]
    (.letOp (n := 67) (.exec 0x108628 (fun s => s.RIP = 0x108628) (andR64R64Effect 0x108628 11 14) (Reg.operands [.gpr 11, .gpr 14] [])) #v[62, 64]
    (.letOp (n := 68) (.out 0x10862b (movR64R64Effect 0x10862b 3 11) (EffectPart.reads (.reg (.gpr 3)) [.gpr 11] []) (.reg (.gpr 3))) #v[66]
    (.letOp (n := 69) (.exec 0x10862b (fun s => s.RIP = 0x10862b) (movR64R64Effect 0x10862b 3 11) (Reg.operands [.gpr 11] [])) #v[66]
    (.letOp (n := 70) (.out 0x10862e (shlR64Effect 0x10862e 4 3 8) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[68]
    (.letOp (n := 71) (.exec 0x10862e (fun s => s.RIP = 0x10862e) (shlR64Effect 0x10862e 4 3 8) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[68]
    (.letOp (n := 72) (.out 0x108632 (addR64R64Effect 0x108632 3 11) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 11] []) (.reg (.gpr 3))) #v[70, 66]
    (.letOp (n := 73) (.exec 0x108632 (fun s => s.RIP = 0x108632) (addR64R64Effect 0x108632 3 11) (Reg.operands [.gpr 3, .gpr 11] [])) #v[70, 66]
    (.letOp (n := 74) (.out 0x108635 (xorR64R64Effect 0x108635 3 10) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 10] []) (.reg (.gpr 3))) #v[72, 10]
    (.letOp (n := 75) (.exec 0x108635 (fun s => s.RIP = 0x108635) (xorR64R64Effect 0x108635 3 10) (Reg.operands [.gpr 3, .gpr 10] [])) #v[72, 10]
    (.letOp (n := 76) (.exec 0x108638 (StorePre 0x108638 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x108638 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108638 3 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[74, 4]
    (.letOp (n := 77) (.out 0x10863d (movR64R64Effect 0x10863d 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 9] []) (.reg (.gpr 10))) #v[9]
    (.letOp (n := 78) (.exec 0x10863d (fun s => s.RIP = 0x10863d) (movR64R64Effect 0x10863d 10 9) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 79) (.out 0x108640 (shrR64Effect 0x108640 4 10 8) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[77]
    (.letOp (n := 80) (.exec 0x108640 (fun s => s.RIP = 0x108640) (shrR64Effect 0x108640 4 10 8) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[77]
    (.letOp (n := 81) (.out 0x108644 (xorR64R64Effect 0x108644 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9] []) (.reg (.gpr 10))) #v[79, 9]
    (.letOp (n := 82) (.exec 0x108644 (fun s => s.RIP = 0x108644) (xorR64R64Effect 0x108644 10 9) (Reg.operands [.gpr 10, .gpr 9] [])) #v[79, 9]
    (.letOp (n := 83) (.out 0x108647 (andR64R64Effect 0x108647 10 14) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 14] []) (.reg (.gpr 10))) #v[81, 64]
    (.letOp (n := 84) (.exec 0x108647 (fun s => s.RIP = 0x108647) (andR64R64Effect 0x108647 10 14) (Reg.operands [.gpr 10, .gpr 14] [])) #v[81, 64]
    (.letOp (n := 85) (.out 0x10864a (movR64R64Effect 0x10864a 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 10] []) (.reg (.gpr 11))) #v[83]
    (.letOp (n := 86) (.exec 0x10864a (fun s => s.RIP = 0x10864a) (movR64R64Effect 0x10864a 11 10) (Reg.operands [.gpr 10] [])) #v[83]
    (.letOp (n := 87) (.out 0x10864d (shlR64Effect 0x10864d 4 11 8) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[85]
    (.letOp (n := 88) (.exec 0x10864d (fun s => s.RIP = 0x10864d) (shlR64Effect 0x10864d 4 11 8) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[85]
    (.letOp (n := 89) (.out 0x108651 (addR64R64Effect 0x108651 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 10] []) (.reg (.gpr 11))) #v[87, 83]
    (.letOp (n := 90) (.exec 0x108651 (fun s => s.RIP = 0x108651) (addR64R64Effect 0x108651 11 10) (Reg.operands [.gpr 11, .gpr 10] [])) #v[87, 83]
    (b_l108600_1))))))))))))))))))))))))))))))))))))))

def bytes_l108600 : List UInt8 :=
  [0x48, 0x8B, 0xAC, 0x24, 0xE0, 0x00, 0x00, 0x00, 0x48, 0x89, 0xAC, 0x24, 0xE0, 0x00, 0x00, 0x00,
    0x48, 0xC1, 0xE5, 0x06, 0x4D, 0x89, 0xD3, 0x49, 0xC1, 0xEB, 0x08, 0x4D, 0x31, 0xD3, 0x49, 0xBE,
    0x00, 0x00, 0xFF, 0x00, 0x00, 0x00, 0xFF, 0x00, 0x4D, 0x21, 0xF3, 0x4C, 0x89, 0xDB, 0x48, 0xC1,
    0xE3, 0x08, 0x4C, 0x01, 0xDB, 0x4C, 0x31, 0xD3, 0x48, 0x89, 0x5C, 0x24, 0x08, 0x4D, 0x89, 0xCA,
    0x49, 0xC1, 0xEA, 0x08, 0x4D, 0x31, 0xCA, 0x4D, 0x21, 0xF2, 0x4D, 0x89, 0xD3, 0x49, 0xC1, 0xE3,
    0x08, 0x4D, 0x01, 0xD3] ++ bytes_l108600_1

theorem code_l108600 : ∀ x ∈ codeRange 0x108600 bytes_l108600, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x8600 84 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l108600_1

@[cfg_block] def b_l108728 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x108728 (movR64M64Effect 0x108728 0 (.sib 4 none 0 (.d32 0x4d8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x108728 (LoadPre 0x108728 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x4d8)) s (0x108728 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x108728 0 (.sib 4 none 0 (.d32 0x4d8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x108730 (StorePre 0x108730 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x108730 + BitVec.ofNat 64 5)) 8) (xorMREffect 0x108730 5 64 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x108735 (movR64M64Effect 0x108735 0 (.sib 4 none 0 (.d32 0x4e0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x108735 (LoadPre 0x108735 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x4e0)) s (0x108735 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x108735 0 (.sib 4 none 0 (.d32 0x4e0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x10873d (StorePre 0x10873d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10873d + BitVec.ofNat 64 5)) 8) (xorMREffect 0x10873d 5 64 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x108742 (movR64M64Effect 0x108742 0 (.sib 4 none 0 (.d32 0x4e8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x108742 (LoadPre 0x108742 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x4e8)) s (0x108742 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x108742 0 (.sib 4 none 0 (.d32 0x4e8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x10874a (StorePre 0x10874a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10874a + BitVec.ofNat 64 5)) 8) (xorMREffect 0x10874a 5 64 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x10874f (movR64M64Effect 0x10874f 0 (.sib 4 none 0 (.d32 0x4f0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x10874f (LoadPre 0x10874f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x4f0)) s (0x10874f + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10874f 0 (.sib 4 none 0 (.d32 0x4f0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x108757 (StorePre 0x108757 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x108757 + BitVec.ofNat 64 5)) 8) (xorMREffect 0x108757 5 64 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x10875c (movR64M64Effect 0x10875c 0 (.sib 4 none 0 (.d32 0x4f8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 66) (.exec 0x10875c (LoadPre 0x10875c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x4f8)) s (0x10875c + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10875c 0 (.sib 4 none 0 (.d32 0x4f8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x108764 (StorePre 0x108764 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x108764 + BitVec.ofNat 64 5)) 8) (xorMREffect 0x108764 5 64 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x108769 (movR64M64Effect 0x108769 0 (.sib 4 none 0 (.d32 0x500))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 69) (.exec 0x108769 (LoadPre 0x108769 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x500)) s (0x108769 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x108769 0 (.sib 4 none 0 (.d32 0x500))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.exec 0x108771 (StorePre 0x108771 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x108771 + BitVec.ofNat 64 5)) 8) (xorMREffect 0x108771 5 64 0 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[68, 4]
    (.letOp (n := 71) (.out 0x108776 (movR64M64Effect 0x108776 0 (.sib 4 none 0 (.d32 0x508))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 72) (.exec 0x108776 (LoadPre 0x108776 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x508)) s (0x108776 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x108776 0 (.sib 4 none 0 (.d32 0x508))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.exec 0x10877e (StorePre 0x10877e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10877e + BitVec.ofNat 64 5)) 8) (xorMREffect 0x10877e 5 64 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[71, 4]
    (.letOp (n := 74) (.out 0x108783 (movR64M64Effect 0x108783 0 (.sib 4 none 0 (.d32 0x510))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 75) (.exec 0x108783 (LoadPre 0x108783 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x510)) s (0x108783 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x108783 0 (.sib 4 none 0 (.d32 0x510))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 76) (.exec 0x10878b (StorePre 0x10878b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10878b + BitVec.ofNat 64 5)) 8) (xorMREffect 0x10878b 5 64 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[74, 4]
    (.letOp (n := 77) (.out 0x108790 (movR32Imm32Effect 0x108790 5 2 0x8) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 78) (.exec 0x108790 (fun s => s.RIP = 0x108790) (movR32Imm32Effect 0x108790 5 2 0x8) (Reg.operands [] [])) #v[]
    (.letOp (n := 79) (.out 0x108795 (leaR64Effect 0x108795 7 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 80) (.exec 0x108795 (fun s => s.RIP = 0x108795) (leaR64Effect 0x108795 7 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 81) (.out 0x10879d (movR64R64Effect 0x10879d 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[3]
    (.letOp (n := 82) (.exec 0x10879d (fun s => s.RIP = 0x10879d) (movR64R64Effect 0x10879d 6 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 83) (.out 0x1087a0 (callEffect (fun _ => 0x10a210) 0x1087a5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 84) (.exec 0x1087a0 (PushPre 0x1087a0 5) (callEffect (fun _ => 0x10a210) 0x1087a5) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 85) (.const ⟨64, 0x1087a5⟩) #v[]
    (.terminate (.call ⟨.l10a210, RegMap.args [(0, 74), (2, 77), (3, 3), (4, 83), (5, 5), (6, 81), (7, 79), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 86⟩ { target := .l1087a5, kept := #v[], arity := rfl, guard := some (Fin.last 85) }))))))))))))))))))))))))))))))))))

def bytes_l108728 : List UInt8 :=
  [0x48, 0x8B, 0x84, 0x24, 0xD8, 0x04, 0x00, 0x00, 0x48, 0x31, 0x44, 0x24, 0x08, 0x48, 0x8B, 0x84,
    0x24, 0xE0, 0x04, 0x00, 0x00, 0x48, 0x31, 0x44, 0x24, 0x10, 0x48, 0x8B, 0x84, 0x24, 0xE8, 0x04,
    0x00, 0x00, 0x48, 0x31, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x84, 0x24, 0xF0, 0x04, 0x00, 0x00, 0x48,
    0x31, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x84, 0x24, 0xF8, 0x04, 0x00, 0x00, 0x48, 0x31, 0x44, 0x24,
    0x28, 0x48, 0x8B, 0x84, 0x24, 0x00, 0x05, 0x00, 0x00, 0x48, 0x31, 0x44, 0x24, 0x30, 0x48, 0x8B,
    0x84, 0x24, 0x08, 0x05, 0x00, 0x00, 0x48, 0x31, 0x44, 0x24, 0x38, 0x48, 0x8B, 0x84, 0x24, 0x10,
    0x05, 0x00, 0x00, 0x48, 0x31, 0x44, 0x24, 0x40, 0xBA, 0x08, 0x00, 0x00, 0x00, 0x48, 0x8D, 0xBC,
    0x24, 0x98, 0x00, 0x00, 0x00, 0x48, 0x89, 0xDE, 0xE8, 0x6B, 0x1A, 0x00, 0x00]

theorem code_l108728 : ∀ x ∈ codeRange 0x108728 bytes_l108728, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x8728 125 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

def b_l1087a5_15 : Block Op Label signature Reg.count 539 :=
  .letOp (n := 539) (.exec 0x108e50 (StorePre 0x108e50 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x3a)) s (0x108e50 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108e50 5 9 (.sib 0 (some 5) 0 (.d8 0x3a))) (Reg.operands [.gpr 9, .gpr 0, .gpr 5] [])) #v[353, 375, 5]
    (.letOp (n := 540) (.exec 0x108e55 (StorePre 0x108e55 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x3b)) s (0x108e55 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108e55 5 8 (.sib 0 (some 5) 0 (.d8 0x3b))) (Reg.operands [.gpr 8, .gpr 0, .gpr 5] [])) #v[357, 375, 5]
    (.letOp (n := 541) (.exec 0x108e5a (StorePre 0x108e5a 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x3c)) s (0x108e5a + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108e5a 5 7 (.sib 0 (some 5) 0 (.d8 0x3c))) (Reg.operands [.gpr 7, .gpr 0, .gpr 5] [])) #v[361, 375, 5]
    (.letOp (n := 542) (.exec 0x108e5f (StorePre 0x108e5f 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x3d)) s (0x108e5f + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108e5f 5 6 (.sib 0 (some 5) 0 (.d8 0x3d))) (Reg.operands [.gpr 6, .gpr 0, .gpr 5] [])) #v[365, 375, 5]
    (.letOp (n := 543) (.exec 0x108e64 (StorePre 0x108e64 4 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x3e)) s (0x108e64 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108e64 4 2 (.sib 0 (some 5) 0 (.d8 0x3e))) (Reg.operands [.gpr 2, .gpr 0, .gpr 5] [])) #v[369, 375, 5]
    (.letOp (n := 544) (.out 0x108e68 (movR64R64Effect 0x108e68 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0] []) (.reg (.gpr 2))) #v[375]
    (.letOp (n := 545) (.exec 0x108e68 (fun s => s.RIP = 0x108e68) (movR64R64Effect 0x108e68 2 0) (Reg.operands [.gpr 0] [])) #v[375]
    (.letOp (n := 546) (.exec 0x108e6b (StorePre 0x108e6b 4 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x3f)) s (0x108e6b + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108e6b 4 1 (.sib 0 (some 5) 0 (.d8 0x3f))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[373, 375, 5]
    (.letOp (n := 547) (.out 0x108e6f (movR64M64Effect 0x108e6f 1 (.sib 4 none 0 (.d32 0xe0))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 548) (.exec 0x108e6f (LoadPre 0x108e6f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x108e6f + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x108e6f 1 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 549) (.out 0x108e77 (incR64Effect 0x108e77 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[547]
    (.letOp (n := 550) (.exec 0x108e77 (fun s => s.RIP = 0x108e77) (incR64Effect 0x108e77 1) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[547]
    (.letOp (n := 551) (.exec 0x108e7a (StorePre 0x108e7a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x108e7a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108e7a 1 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[549, 4]
    (.letOp (n := 552) (.out 0x108e82 (cmpMREffect 0x108e82 8 64 1 (.sib 4 none 0 (.d32 0x148))) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 4] []) (.flag .ZF)) #v[549, 4]
    (.letOp (n := 553) (.exec 0x108e82 (LoadPre 0x108e82 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x148)) s (0x108e82 + BitVec.ofNat 64 8)) 8) (cmpMREffect 0x108e82 8 64 1 (.sib 4 none 0 (.d32 0x148))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[549, 4]
    (.letOp (n := 554) (.out 0x108e8a (movR64M64Effect 0x108e8a 9 (.sib 4 none 0 (.d32 0xf8))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 555) (.exec 0x108e8a (LoadPre 0x108e8a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x108e8a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x108e8a 9 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 556) (.pure (condOp 4)) #v[552]
    (.terminate (.condBr (Fin.last 556) ⟨.l109509, RegMap.args [(0, 375), (1, 549), (2, 544), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 554), (10, 349), (11, 345), (12, 329), (13, 530), (14, 337), (15, 333), (19, 552), (22, 22), (39, 39), (50, 50), (51, 51)] 557⟩ ⟨.l108e98, RegMap.args [(0, 375), (1, 549), (2, 544), (3, 341), (4, 4), (5, 5), (6, 365), (7, 361), (8, 357), (9, 554), (10, 349), (11, 345), (12, 329), (13, 530), (14, 337), (15, 333), (19, 552), (22, 22), (39, 39), (50, 50), (51, 51)] 557⟩)))))))))))))))))))

def bytes_l1087a5_15 : List UInt8 :=
  [0x44, 0x88, 0x4C, 0x28, 0x3A, 0x44, 0x88, 0x44, 0x28, 0x3B, 0x40, 0x88, 0x7C, 0x28, 0x3C, 0x40,
    0x88, 0x74, 0x28, 0x3D, 0x88, 0x54, 0x28, 0x3E, 0x48, 0x89, 0xC2, 0x88, 0x4C, 0x28, 0x3F, 0x48,
    0x8B, 0x8C, 0x24, 0xE0, 0x00, 0x00, 0x00, 0x48, 0xFF, 0xC1, 0x48, 0x89, 0x8C, 0x24, 0xE0, 0x00,
    0x00, 0x00, 0x48, 0x39, 0x8C, 0x24, 0x48, 0x01, 0x00, 0x00, 0x4C, 0x8B, 0x8C, 0x24, 0xF8, 0x00,
    0x00, 0x00, 0x0F, 0x84, 0x71, 0x06, 0x00, 0x00]

theorem code_l1087a5_15 : ∀ x ∈ codeRange 0x108e50 bytes_l1087a5_15, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x8e50 72 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

def b_l1087a5_14 : Block Op Label signature Reg.count 512 :=
  .letOp (n := 512) (.out 0x108de6 (movzxR32M8Effect 0x108de6 6 13 (.sib 4 none 0 (.d8 0x4e))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 513) (.exec 0x108de6 (LoadPre 0x108de6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4e)) s (0x108de6 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108de6 6 13 (.sib 4 none 0 (.d8 0x4e))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 514) (.exec 0x108dec (StorePre 0x108dec 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x2d)) s (0x108dec + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108dec 5 13 (.sib 0 (some 5) 0 (.d8 0x2d))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[512, 375, 5]
    (.letOp (n := 515) (.out 0x108df1 (movzxR32M8Effect 0x108df1 6 13 (.sib 4 none 0 (.d8 0x4d))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 516) (.exec 0x108df1 (LoadPre 0x108df1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4d)) s (0x108df1 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108df1 6 13 (.sib 4 none 0 (.d8 0x4d))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 517) (.exec 0x108df7 (StorePre 0x108df7 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x2e)) s (0x108df7 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108df7 5 13 (.sib 0 (some 5) 0 (.d8 0x2e))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[515, 375, 5]
    (.letOp (n := 518) (.out 0x108dfc (movzxR32M8Effect 0x108dfc 6 13 (.sib 4 none 0 (.d8 0x4c))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 519) (.exec 0x108dfc (LoadPre 0x108dfc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4c)) s (0x108dfc + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108dfc 6 13 (.sib 4 none 0 (.d8 0x4c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 520) (.exec 0x108e02 (StorePre 0x108e02 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x2f)) s (0x108e02 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108e02 5 13 (.sib 0 (some 5) 0 (.d8 0x2f))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[518, 375, 5]
    (.letOp (n := 521) (.out 0x108e07 (movzxR32M8Effect 0x108e07 6 13 (.sib 4 none 0 (.d8 0x4b))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 522) (.exec 0x108e07 (LoadPre 0x108e07 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4b)) s (0x108e07 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108e07 6 13 (.sib 4 none 0 (.d8 0x4b))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 523) (.exec 0x108e0d (StorePre 0x108e0d 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x30)) s (0x108e0d + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108e0d 5 13 (.sib 0 (some 5) 0 (.d8 0x30))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[521, 375, 5]
    (.letOp (n := 524) (.out 0x108e12 (movzxR32M8Effect 0x108e12 6 13 (.sib 4 none 0 (.d8 0x4a))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 525) (.exec 0x108e12 (LoadPre 0x108e12 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4a)) s (0x108e12 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108e12 6 13 (.sib 4 none 0 (.d8 0x4a))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 526) (.exec 0x108e18 (StorePre 0x108e18 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x31)) s (0x108e18 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108e18 5 13 (.sib 0 (some 5) 0 (.d8 0x31))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[524, 375, 5]
    (.letOp (n := 527) (.out 0x108e1d (movzxR32M8Effect 0x108e1d 6 13 (.sib 4 none 0 (.d8 0x49))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 528) (.exec 0x108e1d (LoadPre 0x108e1d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x49)) s (0x108e1d + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108e1d 6 13 (.sib 4 none 0 (.d8 0x49))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 529) (.exec 0x108e23 (StorePre 0x108e23 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x32)) s (0x108e23 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108e23 5 13 (.sib 0 (some 5) 0 (.d8 0x32))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[527, 375, 5]
    (.letOp (n := 530) (.out 0x108e28 (movzxR32M8Effect 0x108e28 6 13 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 531) (.exec 0x108e28 (LoadPre 0x108e28 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x108e28 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108e28 6 13 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 532) (.exec 0x108e2e (StorePre 0x108e2e 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x33)) s (0x108e2e + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108e2e 5 13 (.sib 0 (some 5) 0 (.d8 0x33))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[530, 375, 5]
    (.letOp (n := 533) (.exec 0x108e33 (StorePre 0x108e33 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x34)) s (0x108e33 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108e33 5 12 (.sib 0 (some 5) 0 (.d8 0x34))) (Reg.operands [.gpr 12, .gpr 0, .gpr 5] [])) #v[329, 375, 5]
    (.letOp (n := 534) (.exec 0x108e38 (StorePre 0x108e38 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x35)) s (0x108e38 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108e38 5 15 (.sib 0 (some 5) 0 (.d8 0x35))) (Reg.operands [.gpr 15, .gpr 0, .gpr 5] [])) #v[333, 375, 5]
    (.letOp (n := 535) (.exec 0x108e3d (StorePre 0x108e3d 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x36)) s (0x108e3d + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108e3d 5 14 (.sib 0 (some 5) 0 (.d8 0x36))) (Reg.operands [.gpr 14, .gpr 0, .gpr 5] [])) #v[337, 375, 5]
    (.letOp (n := 536) (.exec 0x108e42 (StorePre 0x108e42 4 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x37)) s (0x108e42 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108e42 4 3 (.sib 0 (some 5) 0 (.d8 0x37))) (Reg.operands [.gpr 3, .gpr 0, .gpr 5] [])) #v[341, 375, 5]
    (.letOp (n := 537) (.exec 0x108e46 (StorePre 0x108e46 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x38)) s (0x108e46 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108e46 5 11 (.sib 0 (some 5) 0 (.d8 0x38))) (Reg.operands [.gpr 11, .gpr 0, .gpr 5] [])) #v[345, 375, 5]
    (.letOp (n := 538) (.exec 0x108e4b (StorePre 0x108e4b 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x39)) s (0x108e4b + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108e4b 5 10 (.sib 0 (some 5) 0 (.d8 0x39))) (Reg.operands [.gpr 10, .gpr 0, .gpr 5] [])) #v[349, 375, 5]
    (b_l1087a5_15)))))))))))))))))))))))))))

def bytes_l1087a5_14 : List UInt8 :=
  [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x4E, 0x44, 0x88, 0x6C, 0x28, 0x2D, 0x44, 0x0F, 0xB6, 0x6C, 0x24,
    0x4D, 0x44, 0x88, 0x6C, 0x28, 0x2E, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x4C, 0x44, 0x88, 0x6C, 0x28,
    0x2F, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x4B, 0x44, 0x88, 0x6C, 0x28, 0x30, 0x44, 0x0F, 0xB6, 0x6C,
    0x24, 0x4A, 0x44, 0x88, 0x6C, 0x28, 0x31, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x49, 0x44, 0x88, 0x6C,
    0x28, 0x32, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x48, 0x44, 0x88, 0x6C, 0x28, 0x33, 0x44, 0x88, 0x64,
    0x28, 0x34, 0x44, 0x88, 0x7C, 0x28, 0x35, 0x44, 0x88, 0x74, 0x28, 0x36, 0x88, 0x5C, 0x28, 0x37,
    0x44, 0x88, 0x5C, 0x28, 0x38, 0x44, 0x88, 0x54, 0x28, 0x39] ++ bytes_l1087a5_15

theorem code_l1087a5_14 : ∀ x ∈ codeRange 0x108de6 bytes_l1087a5_14, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x8de6 106 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1087a5_15

def b_l1087a5_13 : Block Op Label signature Reg.count 482 :=
  .letOp (n := 482) (.out 0x108d78 (movzxR32M8Effect 0x108d78 6 13 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 483) (.exec 0x108d78 (LoadPre 0x108d78 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x108d78 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108d78 6 13 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 484) (.exec 0x108d7e (StorePre 0x108d7e 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x23)) s (0x108d7e + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108d7e 5 13 (.sib 0 (some 5) 0 (.d8 0x23))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[482, 375, 5]
    (.letOp (n := 485) (.out 0x108d83 (movzxR32M8Effect 0x108d83 6 13 (.sib 4 none 0 (.d8 0x57))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 486) (.exec 0x108d83 (LoadPre 0x108d83 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x57)) s (0x108d83 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108d83 6 13 (.sib 4 none 0 (.d8 0x57))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 487) (.exec 0x108d89 (StorePre 0x108d89 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x24)) s (0x108d89 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108d89 5 13 (.sib 0 (some 5) 0 (.d8 0x24))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[485, 375, 5]
    (.letOp (n := 488) (.out 0x108d8e (movzxR32M8Effect 0x108d8e 6 13 (.sib 4 none 0 (.d8 0x56))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 489) (.exec 0x108d8e (LoadPre 0x108d8e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x56)) s (0x108d8e + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108d8e 6 13 (.sib 4 none 0 (.d8 0x56))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 490) (.exec 0x108d94 (StorePre 0x108d94 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x25)) s (0x108d94 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108d94 5 13 (.sib 0 (some 5) 0 (.d8 0x25))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[488, 375, 5]
    (.letOp (n := 491) (.out 0x108d99 (movzxR32M8Effect 0x108d99 6 13 (.sib 4 none 0 (.d8 0x55))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 492) (.exec 0x108d99 (LoadPre 0x108d99 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x55)) s (0x108d99 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108d99 6 13 (.sib 4 none 0 (.d8 0x55))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 493) (.exec 0x108d9f (StorePre 0x108d9f 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x26)) s (0x108d9f + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108d9f 5 13 (.sib 0 (some 5) 0 (.d8 0x26))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[491, 375, 5]
    (.letOp (n := 494) (.out 0x108da4 (movzxR32M8Effect 0x108da4 6 13 (.sib 4 none 0 (.d8 0x54))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 495) (.exec 0x108da4 (LoadPre 0x108da4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x54)) s (0x108da4 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108da4 6 13 (.sib 4 none 0 (.d8 0x54))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 496) (.exec 0x108daa (StorePre 0x108daa 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x27)) s (0x108daa + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108daa 5 13 (.sib 0 (some 5) 0 (.d8 0x27))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[494, 375, 5]
    (.letOp (n := 497) (.out 0x108daf (movzxR32M8Effect 0x108daf 6 13 (.sib 4 none 0 (.d8 0x53))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 498) (.exec 0x108daf (LoadPre 0x108daf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x53)) s (0x108daf + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108daf 6 13 (.sib 4 none 0 (.d8 0x53))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 499) (.exec 0x108db5 (StorePre 0x108db5 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x28)) s (0x108db5 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108db5 5 13 (.sib 0 (some 5) 0 (.d8 0x28))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[497, 375, 5]
    (.letOp (n := 500) (.out 0x108dba (movzxR32M8Effect 0x108dba 6 13 (.sib 4 none 0 (.d8 0x52))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 501) (.exec 0x108dba (LoadPre 0x108dba (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x52)) s (0x108dba + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108dba 6 13 (.sib 4 none 0 (.d8 0x52))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 502) (.exec 0x108dc0 (StorePre 0x108dc0 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x29)) s (0x108dc0 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108dc0 5 13 (.sib 0 (some 5) 0 (.d8 0x29))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[500, 375, 5]
    (.letOp (n := 503) (.out 0x108dc5 (movzxR32M8Effect 0x108dc5 6 13 (.sib 4 none 0 (.d8 0x51))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 504) (.exec 0x108dc5 (LoadPre 0x108dc5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x51)) s (0x108dc5 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108dc5 6 13 (.sib 4 none 0 (.d8 0x51))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 505) (.exec 0x108dcb (StorePre 0x108dcb 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x2a)) s (0x108dcb + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108dcb 5 13 (.sib 0 (some 5) 0 (.d8 0x2a))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[503, 375, 5]
    (.letOp (n := 506) (.out 0x108dd0 (movzxR32M8Effect 0x108dd0 6 13 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 507) (.exec 0x108dd0 (LoadPre 0x108dd0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x108dd0 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108dd0 6 13 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 508) (.exec 0x108dd6 (StorePre 0x108dd6 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x2b)) s (0x108dd6 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108dd6 5 13 (.sib 0 (some 5) 0 (.d8 0x2b))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[506, 375, 5]
    (.letOp (n := 509) (.out 0x108ddb (movzxR32M8Effect 0x108ddb 6 13 (.sib 4 none 0 (.d8 0x4f))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 510) (.exec 0x108ddb (LoadPre 0x108ddb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4f)) s (0x108ddb + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108ddb 6 13 (.sib 4 none 0 (.d8 0x4f))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 511) (.exec 0x108de1 (StorePre 0x108de1 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x2c)) s (0x108de1 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108de1 5 13 (.sib 0 (some 5) 0 (.d8 0x2c))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[509, 375, 5]
    (b_l1087a5_14))))))))))))))))))))))))))))))

def bytes_l1087a5_13 : List UInt8 :=
  [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x58, 0x44, 0x88, 0x6C, 0x28, 0x23, 0x44, 0x0F, 0xB6, 0x6C, 0x24,
    0x57, 0x44, 0x88, 0x6C, 0x28, 0x24, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x56, 0x44, 0x88, 0x6C, 0x28,
    0x25, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x55, 0x44, 0x88, 0x6C, 0x28, 0x26, 0x44, 0x0F, 0xB6, 0x6C,
    0x24, 0x54, 0x44, 0x88, 0x6C, 0x28, 0x27, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x53, 0x44, 0x88, 0x6C,
    0x28, 0x28, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x52, 0x44, 0x88, 0x6C, 0x28, 0x29, 0x44, 0x0F, 0xB6,
    0x6C, 0x24, 0x51, 0x44, 0x88, 0x6C, 0x28, 0x2A, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x50, 0x44, 0x88,
    0x6C, 0x28, 0x2B, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x4F, 0x44, 0x88, 0x6C, 0x28, 0x2C] ++ bytes_l1087a5_14

theorem code_l1087a5_13 : ∀ x ∈ codeRange 0x108d78 bytes_l1087a5_13, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x8d78 110 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1087a5_14

def b_l1087a5_12 : Block Op Label signature Reg.count 452 :=
  .letOp (n := 452) (.out 0x108d0a (movzxR32M8Effect 0x108d0a 6 13 (.sib 4 none 0 (.d8 0x62))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 453) (.exec 0x108d0a (LoadPre 0x108d0a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x62)) s (0x108d0a + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108d0a 6 13 (.sib 4 none 0 (.d8 0x62))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 454) (.exec 0x108d10 (StorePre 0x108d10 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x19)) s (0x108d10 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108d10 5 13 (.sib 0 (some 5) 0 (.d8 0x19))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[452, 375, 5]
    (.letOp (n := 455) (.out 0x108d15 (movzxR32M8Effect 0x108d15 6 13 (.sib 4 none 0 (.d8 0x61))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 456) (.exec 0x108d15 (LoadPre 0x108d15 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x61)) s (0x108d15 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108d15 6 13 (.sib 4 none 0 (.d8 0x61))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 457) (.exec 0x108d1b (StorePre 0x108d1b 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x1a)) s (0x108d1b + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108d1b 5 13 (.sib 0 (some 5) 0 (.d8 0x1a))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[455, 375, 5]
    (.letOp (n := 458) (.out 0x108d20 (movzxR32M8Effect 0x108d20 6 13 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 459) (.exec 0x108d20 (LoadPre 0x108d20 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x108d20 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108d20 6 13 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 460) (.exec 0x108d26 (StorePre 0x108d26 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x1b)) s (0x108d26 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108d26 5 13 (.sib 0 (some 5) 0 (.d8 0x1b))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[458, 375, 5]
    (.letOp (n := 461) (.out 0x108d2b (movzxR32M8Effect 0x108d2b 6 13 (.sib 4 none 0 (.d8 0x5f))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 462) (.exec 0x108d2b (LoadPre 0x108d2b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5f)) s (0x108d2b + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108d2b 6 13 (.sib 4 none 0 (.d8 0x5f))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 463) (.exec 0x108d31 (StorePre 0x108d31 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x1c)) s (0x108d31 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108d31 5 13 (.sib 0 (some 5) 0 (.d8 0x1c))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[461, 375, 5]
    (.letOp (n := 464) (.out 0x108d36 (movzxR32M8Effect 0x108d36 6 13 (.sib 4 none 0 (.d8 0x5e))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 465) (.exec 0x108d36 (LoadPre 0x108d36 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5e)) s (0x108d36 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108d36 6 13 (.sib 4 none 0 (.d8 0x5e))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 466) (.exec 0x108d3c (StorePre 0x108d3c 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x1d)) s (0x108d3c + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108d3c 5 13 (.sib 0 (some 5) 0 (.d8 0x1d))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[464, 375, 5]
    (.letOp (n := 467) (.out 0x108d41 (movzxR32M8Effect 0x108d41 6 13 (.sib 4 none 0 (.d8 0x5d))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 468) (.exec 0x108d41 (LoadPre 0x108d41 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5d)) s (0x108d41 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108d41 6 13 (.sib 4 none 0 (.d8 0x5d))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 469) (.exec 0x108d47 (StorePre 0x108d47 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x1e)) s (0x108d47 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108d47 5 13 (.sib 0 (some 5) 0 (.d8 0x1e))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[467, 375, 5]
    (.letOp (n := 470) (.out 0x108d4c (movzxR32M8Effect 0x108d4c 6 13 (.sib 4 none 0 (.d8 0x5c))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 471) (.exec 0x108d4c (LoadPre 0x108d4c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5c)) s (0x108d4c + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108d4c 6 13 (.sib 4 none 0 (.d8 0x5c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 472) (.exec 0x108d52 (StorePre 0x108d52 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x1f)) s (0x108d52 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108d52 5 13 (.sib 0 (some 5) 0 (.d8 0x1f))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[470, 375, 5]
    (.letOp (n := 473) (.out 0x108d57 (movzxR32M8Effect 0x108d57 6 13 (.sib 4 none 0 (.d8 0x5b))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 474) (.exec 0x108d57 (LoadPre 0x108d57 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5b)) s (0x108d57 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108d57 6 13 (.sib 4 none 0 (.d8 0x5b))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 475) (.exec 0x108d5d (StorePre 0x108d5d 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x20)) s (0x108d5d + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108d5d 5 13 (.sib 0 (some 5) 0 (.d8 0x20))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[473, 375, 5]
    (.letOp (n := 476) (.out 0x108d62 (movzxR32M8Effect 0x108d62 6 13 (.sib 4 none 0 (.d8 0x5a))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 477) (.exec 0x108d62 (LoadPre 0x108d62 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5a)) s (0x108d62 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108d62 6 13 (.sib 4 none 0 (.d8 0x5a))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 478) (.exec 0x108d68 (StorePre 0x108d68 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x21)) s (0x108d68 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108d68 5 13 (.sib 0 (some 5) 0 (.d8 0x21))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[476, 375, 5]
    (.letOp (n := 479) (.out 0x108d6d (movzxR32M8Effect 0x108d6d 6 13 (.sib 4 none 0 (.d8 0x59))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 480) (.exec 0x108d6d (LoadPre 0x108d6d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x59)) s (0x108d6d + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108d6d 6 13 (.sib 4 none 0 (.d8 0x59))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 481) (.exec 0x108d73 (StorePre 0x108d73 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x22)) s (0x108d73 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108d73 5 13 (.sib 0 (some 5) 0 (.d8 0x22))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[479, 375, 5]
    (b_l1087a5_13))))))))))))))))))))))))))))))

def bytes_l1087a5_12 : List UInt8 :=
  [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x62, 0x44, 0x88, 0x6C, 0x28, 0x19, 0x44, 0x0F, 0xB6, 0x6C, 0x24,
    0x61, 0x44, 0x88, 0x6C, 0x28, 0x1A, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x60, 0x44, 0x88, 0x6C, 0x28,
    0x1B, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x5F, 0x44, 0x88, 0x6C, 0x28, 0x1C, 0x44, 0x0F, 0xB6, 0x6C,
    0x24, 0x5E, 0x44, 0x88, 0x6C, 0x28, 0x1D, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x5D, 0x44, 0x88, 0x6C,
    0x28, 0x1E, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x5C, 0x44, 0x88, 0x6C, 0x28, 0x1F, 0x44, 0x0F, 0xB6,
    0x6C, 0x24, 0x5B, 0x44, 0x88, 0x6C, 0x28, 0x20, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x5A, 0x44, 0x88,
    0x6C, 0x28, 0x21, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x59, 0x44, 0x88, 0x6C, 0x28, 0x22] ++ bytes_l1087a5_13

theorem code_l1087a5_12 : ∀ x ∈ codeRange 0x108d0a bytes_l1087a5_12, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x8d0a 110 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1087a5_13

def b_l1087a5_11 : Block Op Label signature Reg.count 422 :=
  .letOp (n := 422) (.out 0x108c96 (movzxR32M8Effect 0x108c96 9 13 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 423) (.exec 0x108c96 (LoadPre 0x108c96 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x108c96 + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x108c96 9 13 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 424) (.exec 0x108c9f (StorePre 0x108c9f 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0xf)) s (0x108c9f + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108c9f 5 13 (.sib 0 (some 5) 0 (.d8 0xf))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[422, 375, 5]
    (.letOp (n := 425) (.out 0x108ca4 (movzxR32M8Effect 0x108ca4 9 13 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 426) (.exec 0x108ca4 (LoadPre 0x108ca4 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x108ca4 + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x108ca4 9 13 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 427) (.exec 0x108cad (StorePre 0x108cad 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x10)) s (0x108cad + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108cad 5 13 (.sib 0 (some 5) 0 (.d8 0x10))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[425, 375, 5]
    (.letOp (n := 428) (.out 0x108cb2 (movzxR32M8Effect 0x108cb2 6 13 (.sib 4 none 0 (.d8 0x6a))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 429) (.exec 0x108cb2 (LoadPre 0x108cb2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6a)) s (0x108cb2 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108cb2 6 13 (.sib 4 none 0 (.d8 0x6a))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 430) (.exec 0x108cb8 (StorePre 0x108cb8 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x11)) s (0x108cb8 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108cb8 5 13 (.sib 0 (some 5) 0 (.d8 0x11))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[428, 375, 5]
    (.letOp (n := 431) (.out 0x108cbd (movzxR32M8Effect 0x108cbd 6 13 (.sib 4 none 0 (.d8 0x69))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 432) (.exec 0x108cbd (LoadPre 0x108cbd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x69)) s (0x108cbd + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108cbd 6 13 (.sib 4 none 0 (.d8 0x69))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 433) (.exec 0x108cc3 (StorePre 0x108cc3 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x12)) s (0x108cc3 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108cc3 5 13 (.sib 0 (some 5) 0 (.d8 0x12))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[431, 375, 5]
    (.letOp (n := 434) (.out 0x108cc8 (movzxR32M8Effect 0x108cc8 6 13 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 435) (.exec 0x108cc8 (LoadPre 0x108cc8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x108cc8 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108cc8 6 13 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 436) (.exec 0x108cce (StorePre 0x108cce 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x13)) s (0x108cce + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108cce 5 13 (.sib 0 (some 5) 0 (.d8 0x13))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[434, 375, 5]
    (.letOp (n := 437) (.out 0x108cd3 (movzxR32M8Effect 0x108cd3 6 13 (.sib 4 none 0 (.d8 0x67))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 438) (.exec 0x108cd3 (LoadPre 0x108cd3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x67)) s (0x108cd3 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108cd3 6 13 (.sib 4 none 0 (.d8 0x67))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 439) (.exec 0x108cd9 (StorePre 0x108cd9 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x14)) s (0x108cd9 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108cd9 5 13 (.sib 0 (some 5) 0 (.d8 0x14))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[437, 375, 5]
    (.letOp (n := 440) (.out 0x108cde (movzxR32M8Effect 0x108cde 6 13 (.sib 4 none 0 (.d8 0x66))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 441) (.exec 0x108cde (LoadPre 0x108cde (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x66)) s (0x108cde + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108cde 6 13 (.sib 4 none 0 (.d8 0x66))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 442) (.exec 0x108ce4 (StorePre 0x108ce4 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x15)) s (0x108ce4 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108ce4 5 13 (.sib 0 (some 5) 0 (.d8 0x15))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[440, 375, 5]
    (.letOp (n := 443) (.out 0x108ce9 (movzxR32M8Effect 0x108ce9 6 13 (.sib 4 none 0 (.d8 0x65))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 444) (.exec 0x108ce9 (LoadPre 0x108ce9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x65)) s (0x108ce9 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108ce9 6 13 (.sib 4 none 0 (.d8 0x65))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 445) (.exec 0x108cef (StorePre 0x108cef 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x16)) s (0x108cef + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108cef 5 13 (.sib 0 (some 5) 0 (.d8 0x16))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[443, 375, 5]
    (.letOp (n := 446) (.out 0x108cf4 (movzxR32M8Effect 0x108cf4 6 13 (.sib 4 none 0 (.d8 0x64))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 447) (.exec 0x108cf4 (LoadPre 0x108cf4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x64)) s (0x108cf4 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108cf4 6 13 (.sib 4 none 0 (.d8 0x64))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 448) (.exec 0x108cfa (StorePre 0x108cfa 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x17)) s (0x108cfa + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108cfa 5 13 (.sib 0 (some 5) 0 (.d8 0x17))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[446, 375, 5]
    (.letOp (n := 449) (.out 0x108cff (movzxR32M8Effect 0x108cff 6 13 (.sib 4 none 0 (.d8 0x63))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 450) (.exec 0x108cff (LoadPre 0x108cff (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x63)) s (0x108cff + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108cff 6 13 (.sib 4 none 0 (.d8 0x63))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 451) (.exec 0x108d05 (StorePre 0x108d05 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x18)) s (0x108d05 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108d05 5 13 (.sib 0 (some 5) 0 (.d8 0x18))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[449, 375, 5]
    (b_l1087a5_12))))))))))))))))))))))))))))))

def bytes_l1087a5_11 : List UInt8 :=
  [0x44, 0x0F, 0xB6, 0xAC, 0x24, 0x88, 0x00, 0x00, 0x00, 0x44, 0x88, 0x6C, 0x28, 0x0F, 0x44, 0x0F,
    0xB6, 0xAC, 0x24, 0x90, 0x00, 0x00, 0x00, 0x44, 0x88, 0x6C, 0x28, 0x10, 0x44, 0x0F, 0xB6, 0x6C,
    0x24, 0x6A, 0x44, 0x88, 0x6C, 0x28, 0x11, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x69, 0x44, 0x88, 0x6C,
    0x28, 0x12, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x68, 0x44, 0x88, 0x6C, 0x28, 0x13, 0x44, 0x0F, 0xB6,
    0x6C, 0x24, 0x67, 0x44, 0x88, 0x6C, 0x28, 0x14, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x66, 0x44, 0x88,
    0x6C, 0x28, 0x15, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x65, 0x44, 0x88, 0x6C, 0x28, 0x16, 0x44, 0x0F,
    0xB6, 0x6C, 0x24, 0x64, 0x44, 0x88, 0x6C, 0x28, 0x17, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x63, 0x44,
    0x88, 0x6C, 0x28, 0x18] ++ bytes_l1087a5_12

theorem code_l1087a5_11 : ∀ x ∈ codeRange 0x108c96 bytes_l1087a5_11, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x8c96 116 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1087a5_12

def b_l1087a5_10 : Block Op Label signature Reg.count 392 :=
  .letOp (n := 392) (.out 0x108c25 (movzxR32M8Effect 0x108c25 6 13 (.sib 4 none 0 (.d8 0x72))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 393) (.exec 0x108c25 (LoadPre 0x108c25 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x72)) s (0x108c25 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108c25 6 13 (.sib 4 none 0 (.d8 0x72))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 394) (.exec 0x108c2b (StorePre 0x108c2b 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x5)) s (0x108c2b + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108c2b 5 13 (.sib 0 (some 5) 0 (.d8 0x5))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[392, 375, 5]
    (.letOp (n := 395) (.out 0x108c30 (movzxR32M8Effect 0x108c30 6 13 (.sib 4 none 0 (.d8 0x71))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 396) (.exec 0x108c30 (LoadPre 0x108c30 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x71)) s (0x108c30 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108c30 6 13 (.sib 4 none 0 (.d8 0x71))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 397) (.exec 0x108c36 (StorePre 0x108c36 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x6)) s (0x108c36 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108c36 5 13 (.sib 0 (some 5) 0 (.d8 0x6))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[395, 375, 5]
    (.letOp (n := 398) (.out 0x108c3b (movzxR32M8Effect 0x108c3b 6 13 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 399) (.exec 0x108c3b (LoadPre 0x108c3b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x108c3b + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108c3b 6 13 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 400) (.exec 0x108c41 (StorePre 0x108c41 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x7)) s (0x108c41 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108c41 5 13 (.sib 0 (some 5) 0 (.d8 0x7))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[398, 375, 5]
    (.letOp (n := 401) (.out 0x108c46 (movzxR32M8Effect 0x108c46 6 13 (.sib 4 none 0 (.d8 0x6f))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 402) (.exec 0x108c46 (LoadPre 0x108c46 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6f)) s (0x108c46 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108c46 6 13 (.sib 4 none 0 (.d8 0x6f))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 403) (.exec 0x108c4c (StorePre 0x108c4c 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x8)) s (0x108c4c + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108c4c 5 13 (.sib 0 (some 5) 0 (.d8 0x8))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[401, 375, 5]
    (.letOp (n := 404) (.out 0x108c51 (movzxR32M8Effect 0x108c51 6 13 (.sib 4 none 0 (.d8 0x6e))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 405) (.exec 0x108c51 (LoadPre 0x108c51 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6e)) s (0x108c51 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108c51 6 13 (.sib 4 none 0 (.d8 0x6e))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 406) (.exec 0x108c57 (StorePre 0x108c57 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x9)) s (0x108c57 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108c57 5 13 (.sib 0 (some 5) 0 (.d8 0x9))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[404, 375, 5]
    (.letOp (n := 407) (.out 0x108c5c (movzxR32M8Effect 0x108c5c 6 13 (.sib 4 none 0 (.d8 0x6d))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 408) (.exec 0x108c5c (LoadPre 0x108c5c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6d)) s (0x108c5c + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108c5c 6 13 (.sib 4 none 0 (.d8 0x6d))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 409) (.exec 0x108c62 (StorePre 0x108c62 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0xa)) s (0x108c62 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108c62 5 13 (.sib 0 (some 5) 0 (.d8 0xa))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[407, 375, 5]
    (.letOp (n := 410) (.out 0x108c67 (movzxR32M8Effect 0x108c67 6 13 (.sib 4 none 0 (.d8 0x6c))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 411) (.exec 0x108c67 (LoadPre 0x108c67 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6c)) s (0x108c67 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108c67 6 13 (.sib 4 none 0 (.d8 0x6c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 412) (.exec 0x108c6d (StorePre 0x108c6d 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0xb)) s (0x108c6d + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108c6d 5 13 (.sib 0 (some 5) 0 (.d8 0xb))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[410, 375, 5]
    (.letOp (n := 413) (.out 0x108c72 (movzxR32M8Effect 0x108c72 6 13 (.sib 4 none 0 (.d8 0x6b))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 414) (.exec 0x108c72 (LoadPre 0x108c72 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6b)) s (0x108c72 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108c72 6 13 (.sib 4 none 0 (.d8 0x6b))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 415) (.exec 0x108c78 (StorePre 0x108c78 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0xc)) s (0x108c78 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108c78 5 13 (.sib 0 (some 5) 0 (.d8 0xc))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[413, 375, 5]
    (.letOp (n := 416) (.out 0x108c7d (movzxR32M8Effect 0x108c7d 9 13 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 417) (.exec 0x108c7d (LoadPre 0x108c7d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x108c7d + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x108c7d 9 13 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 418) (.exec 0x108c86 (StorePre 0x108c86 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0xd)) s (0x108c86 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108c86 5 13 (.sib 0 (some 5) 0 (.d8 0xd))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[416, 375, 5]
    (.letOp (n := 419) (.out 0x108c8b (movzxR32M8Effect 0x108c8b 6 13 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 420) (.exec 0x108c8b (LoadPre 0x108c8b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x108c8b + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108c8b 6 13 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 421) (.exec 0x108c91 (StorePre 0x108c91 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0xe)) s (0x108c91 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108c91 5 13 (.sib 0 (some 5) 0 (.d8 0xe))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[419, 375, 5]
    (b_l1087a5_11))))))))))))))))))))))))))))))

def bytes_l1087a5_10 : List UInt8 :=
  [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x72, 0x44, 0x88, 0x6C, 0x28, 0x05, 0x44, 0x0F, 0xB6, 0x6C, 0x24,
    0x71, 0x44, 0x88, 0x6C, 0x28, 0x06, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x70, 0x44, 0x88, 0x6C, 0x28,
    0x07, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x6F, 0x44, 0x88, 0x6C, 0x28, 0x08, 0x44, 0x0F, 0xB6, 0x6C,
    0x24, 0x6E, 0x44, 0x88, 0x6C, 0x28, 0x09, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x6D, 0x44, 0x88, 0x6C,
    0x28, 0x0A, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x6C, 0x44, 0x88, 0x6C, 0x28, 0x0B, 0x44, 0x0F, 0xB6,
    0x6C, 0x24, 0x6B, 0x44, 0x88, 0x6C, 0x28, 0x0C, 0x44, 0x0F, 0xB6, 0xAC, 0x24, 0x80, 0x00, 0x00,
    0x00, 0x44, 0x88, 0x6C, 0x28, 0x0D, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x78, 0x44, 0x88, 0x6C, 0x28,
    0x0E] ++ bytes_l1087a5_11

theorem code_l1087a5_10 : ∀ x ∈ codeRange 0x108c25 bytes_l1087a5_10, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x8c25 113 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1087a5_11

def b_l1087a5_9 : Block Op Label signature Reg.count 357 :=
  .letOp (n := 357) (.out 0x108bb0 (xorR8M8Effect 0x108bb0 5 8 (.sib 0 (some 5) 0 (.d8 0x3b))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0, .gpr 5] []) (.reg (.gpr 8))) #v[355, 91, 5]
    (.letOp (n := 358) (.exec 0x108bb0 (LoadPre 0x108bb0 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x3b)) s (0x108bb0 + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x108bb0 5 8 (.sib 0 (some 5) 0 (.d8 0x3b))) (Reg.operands [.gpr 8, .gpr 0, .gpr 5] [])) #v[355, 91, 5]
    (.letOp (n := 359) (.out 0x108bb5 (movzxR32M8Effect 0x108bb5 8 7 (.sib 4 none 0 (.d32 0xd4))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 360) (.exec 0x108bb5 (LoadPre 0x108bb5 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd4)) s (0x108bb5 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108bb5 8 7 (.sib 4 none 0 (.d32 0xd4))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 361) (.out 0x108bbd (xorR8M8Effect 0x108bbd 5 7 (.sib 0 (some 5) 0 (.d8 0x3c))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0, .gpr 5] []) (.reg (.gpr 7))) #v[359, 91, 5]
    (.letOp (n := 362) (.exec 0x108bbd (LoadPre 0x108bbd (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x3c)) s (0x108bbd + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x108bbd 5 7 (.sib 0 (some 5) 0 (.d8 0x3c))) (Reg.operands [.gpr 7, .gpr 0, .gpr 5] [])) #v[359, 91, 5]
    (.letOp (n := 363) (.out 0x108bc2 (movzxR32M8Effect 0x108bc2 8 6 (.sib 4 none 0 (.d32 0xd5))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 364) (.exec 0x108bc2 (LoadPre 0x108bc2 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd5)) s (0x108bc2 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108bc2 8 6 (.sib 4 none 0 (.d32 0xd5))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 365) (.out 0x108bca (xorR8M8Effect 0x108bca 5 6 (.sib 0 (some 5) 0 (.d8 0x3d))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0, .gpr 5] []) (.reg (.gpr 6))) #v[363, 91, 5]
    (.letOp (n := 366) (.exec 0x108bca (LoadPre 0x108bca (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x3d)) s (0x108bca + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x108bca 5 6 (.sib 0 (some 5) 0 (.d8 0x3d))) (Reg.operands [.gpr 6, .gpr 0, .gpr 5] [])) #v[363, 91, 5]
    (.letOp (n := 367) (.out 0x108bcf (movzxR32M8Effect 0x108bcf 8 2 (.sib 4 none 0 (.d32 0xd6))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 368) (.exec 0x108bcf (LoadPre 0x108bcf (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd6)) s (0x108bcf + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108bcf 8 2 (.sib 4 none 0 (.d32 0xd6))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 369) (.out 0x108bd7 (xorR8M8Effect 0x108bd7 4 2 (.sib 0 (some 5) 0 (.d8 0x3e))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0, .gpr 5] []) (.reg (.gpr 2))) #v[367, 91, 5]
    (.letOp (n := 370) (.exec 0x108bd7 (LoadPre 0x108bd7 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x3e)) s (0x108bd7 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108bd7 4 2 (.sib 0 (some 5) 0 (.d8 0x3e))) (Reg.operands [.gpr 2, .gpr 0, .gpr 5] [])) #v[367, 91, 5]
    (.letOp (n := 371) (.out 0x108bdb (movzxR32M8Effect 0x108bdb 8 1 (.sib 4 none 0 (.d32 0xd7))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 372) (.exec 0x108bdb (LoadPre 0x108bdb (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd7)) s (0x108bdb + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108bdb 8 1 (.sib 4 none 0 (.d32 0xd7))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 373) (.out 0x108be3 (xorR8M8Effect 0x108be3 4 1 (.sib 0 (some 5) 0 (.d8 0x3f))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[371, 91, 5]
    (.letOp (n := 374) (.exec 0x108be3 (LoadPre 0x108be3 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x3f)) s (0x108be3 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108be3 4 1 (.sib 0 (some 5) 0 (.d8 0x3f))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[371, 91, 5]
    (.letOp (n := 375) (.out 0x108be7 (movR64M64Effect 0x108be7 0 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 376) (.exec 0x108be7 (LoadPre 0x108be7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x108be7 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x108be7 0 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 377) (.out 0x108bef (movzxR32M8Effect 0x108bef 6 13 (.sib 4 none 0 (.d8 0x77))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 378) (.exec 0x108bef (LoadPre 0x108bef (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x77)) s (0x108bef + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108bef 6 13 (.sib 4 none 0 (.d8 0x77))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 379) (.exec 0x108bf5 (StorePre 0x108bf5 4 (fun s => AddrMode.addr (.sib 0 (some 5) 0 .none) s (0x108bf5 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108bf5 4 13 (.sib 0 (some 5) 0 .none)) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[377, 375, 5]
    (.letOp (n := 380) (.out 0x108bf9 (movzxR32M8Effect 0x108bf9 6 13 (.sib 4 none 0 (.d8 0x76))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 381) (.exec 0x108bf9 (LoadPre 0x108bf9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x76)) s (0x108bf9 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108bf9 6 13 (.sib 4 none 0 (.d8 0x76))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 382) (.exec 0x108bff (StorePre 0x108bff 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x1)) s (0x108bff + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108bff 5 13 (.sib 0 (some 5) 0 (.d8 0x1))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[380, 375, 5]
    (.letOp (n := 383) (.out 0x108c04 (movzxR32M8Effect 0x108c04 6 13 (.sib 4 none 0 (.d8 0x75))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 384) (.exec 0x108c04 (LoadPre 0x108c04 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x75)) s (0x108c04 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108c04 6 13 (.sib 4 none 0 (.d8 0x75))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 385) (.exec 0x108c0a (StorePre 0x108c0a 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x2)) s (0x108c0a + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108c0a 5 13 (.sib 0 (some 5) 0 (.d8 0x2))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[383, 375, 5]
    (.letOp (n := 386) (.out 0x108c0f (movzxR32M8Effect 0x108c0f 6 13 (.sib 4 none 0 (.d8 0x74))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 387) (.exec 0x108c0f (LoadPre 0x108c0f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x74)) s (0x108c0f + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108c0f 6 13 (.sib 4 none 0 (.d8 0x74))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 388) (.exec 0x108c15 (StorePre 0x108c15 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x3)) s (0x108c15 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108c15 5 13 (.sib 0 (some 5) 0 (.d8 0x3))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[386, 375, 5]
    (.letOp (n := 389) (.out 0x108c1a (movzxR32M8Effect 0x108c1a 6 13 (.sib 4 none 0 (.d8 0x73))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 390) (.exec 0x108c1a (LoadPre 0x108c1a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x73)) s (0x108c1a + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108c1a 6 13 (.sib 4 none 0 (.d8 0x73))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 391) (.exec 0x108c20 (StorePre 0x108c20 5 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x4)) s (0x108c20 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108c20 5 13 (.sib 0 (some 5) 0 (.d8 0x4))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[389, 375, 5]
    (b_l1087a5_10)))))))))))))))))))))))))))))))))))

def bytes_l1087a5_9 : List UInt8 :=
  [0x44, 0x32, 0x44, 0x28, 0x3B, 0x0F, 0xB6, 0xBC, 0x24, 0xD4, 0x00, 0x00, 0x00, 0x40, 0x32, 0x7C,
    0x28, 0x3C, 0x0F, 0xB6, 0xB4, 0x24, 0xD5, 0x00, 0x00, 0x00, 0x40, 0x32, 0x74, 0x28, 0x3D, 0x0F,
    0xB6, 0x94, 0x24, 0xD6, 0x00, 0x00, 0x00, 0x32, 0x54, 0x28, 0x3E, 0x0F, 0xB6, 0x8C, 0x24, 0xD7,
    0x00, 0x00, 0x00, 0x32, 0x4C, 0x28, 0x3F, 0x48, 0x8B, 0x84, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x44,
    0x0F, 0xB6, 0x6C, 0x24, 0x77, 0x44, 0x88, 0x2C, 0x28, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x76, 0x44,
    0x88, 0x6C, 0x28, 0x01, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x75, 0x44, 0x88, 0x6C, 0x28, 0x02, 0x44,
    0x0F, 0xB6, 0x6C, 0x24, 0x74, 0x44, 0x88, 0x6C, 0x28, 0x03, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x73,
    0x44, 0x88, 0x6C, 0x28, 0x04] ++ bytes_l1087a5_10

theorem code_l1087a5_9 : ∀ x ∈ codeRange 0x108bb0 bytes_l1087a5_9, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x8bb0 117 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1087a5_10

def b_l1087a5_8 : Block Op Label signature Reg.count 319 :=
  .letOp (n := 319) (.out 0x108b2f (xorR8M8Effect 0x108b2f 4 1 (.sib 0 (some 5) 0 (.d8 0x32))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[317, 91, 5]
    (.letOp (n := 320) (.exec 0x108b2f (LoadPre 0x108b2f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x32)) s (0x108b2f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108b2f 4 1 (.sib 0 (some 5) 0 (.d8 0x32))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[317, 91, 5]
    (.letOp (n := 321) (.exec 0x108b33 (StorePre 0x108b33 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x49)) s (0x108b33 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108b33 4 1 (.sib 4 none 0 (.d8 0x49))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[319, 4]
    (.letOp (n := 322) (.out 0x108b37 (movzxR32M8Effect 0x108b37 8 1 (.sib 4 none 0 (.d32 0xcb))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 323) (.exec 0x108b37 (LoadPre 0x108b37 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xcb)) s (0x108b37 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108b37 8 1 (.sib 4 none 0 (.d32 0xcb))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 324) (.out 0x108b3f (xorR8M8Effect 0x108b3f 4 1 (.sib 0 (some 5) 0 (.d8 0x33))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[322, 91, 5]
    (.letOp (n := 325) (.exec 0x108b3f (LoadPre 0x108b3f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x33)) s (0x108b3f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108b3f 4 1 (.sib 0 (some 5) 0 (.d8 0x33))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[322, 91, 5]
    (.letOp (n := 326) (.exec 0x108b43 (StorePre 0x108b43 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x108b43 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108b43 4 1 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[324, 4]
    (.letOp (n := 327) (.out 0x108b47 (movzxR32M8Effect 0x108b47 9 12 (.sib 4 none 0 (.d32 0xcc))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 328) (.exec 0x108b47 (LoadPre 0x108b47 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xcc)) s (0x108b47 + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x108b47 9 12 (.sib 4 none 0 (.d32 0xcc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 329) (.out 0x108b50 (xorR8M8Effect 0x108b50 5 12 (.sib 0 (some 5) 0 (.d8 0x34))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 0, .gpr 5] []) (.reg (.gpr 12))) #v[327, 91, 5]
    (.letOp (n := 330) (.exec 0x108b50 (LoadPre 0x108b50 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x34)) s (0x108b50 + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x108b50 5 12 (.sib 0 (some 5) 0 (.d8 0x34))) (Reg.operands [.gpr 12, .gpr 0, .gpr 5] [])) #v[327, 91, 5]
    (.letOp (n := 331) (.out 0x108b55 (movzxR32M8Effect 0x108b55 9 15 (.sib 4 none 0 (.d32 0xcd))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 332) (.exec 0x108b55 (LoadPre 0x108b55 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xcd)) s (0x108b55 + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x108b55 9 15 (.sib 4 none 0 (.d32 0xcd))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 333) (.out 0x108b5e (xorR8M8Effect 0x108b5e 5 15 (.sib 0 (some 5) 0 (.d8 0x35))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 0, .gpr 5] []) (.reg (.gpr 15))) #v[331, 91, 5]
    (.letOp (n := 334) (.exec 0x108b5e (LoadPre 0x108b5e (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x35)) s (0x108b5e + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x108b5e 5 15 (.sib 0 (some 5) 0 (.d8 0x35))) (Reg.operands [.gpr 15, .gpr 0, .gpr 5] [])) #v[331, 91, 5]
    (.letOp (n := 335) (.out 0x108b63 (movzxR32M8Effect 0x108b63 9 14 (.sib 4 none 0 (.d32 0xce))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 336) (.exec 0x108b63 (LoadPre 0x108b63 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xce)) s (0x108b63 + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x108b63 9 14 (.sib 4 none 0 (.d32 0xce))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 337) (.out 0x108b6c (xorR8M8Effect 0x108b6c 5 14 (.sib 0 (some 5) 0 (.d8 0x36))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 0, .gpr 5] []) (.reg (.gpr 14))) #v[335, 91, 5]
    (.letOp (n := 338) (.exec 0x108b6c (LoadPre 0x108b6c (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x36)) s (0x108b6c + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x108b6c 5 14 (.sib 0 (some 5) 0 (.d8 0x36))) (Reg.operands [.gpr 14, .gpr 0, .gpr 5] [])) #v[335, 91, 5]
    (.letOp (n := 339) (.out 0x108b71 (movzxR32M8Effect 0x108b71 8 3 (.sib 4 none 0 (.d32 0xcf))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 340) (.exec 0x108b71 (LoadPre 0x108b71 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xcf)) s (0x108b71 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108b71 8 3 (.sib 4 none 0 (.d32 0xcf))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 341) (.out 0x108b79 (xorR8M8Effect 0x108b79 4 3 (.sib 0 (some 5) 0 (.d8 0x37))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0, .gpr 5] []) (.reg (.gpr 3))) #v[339, 91, 5]
    (.letOp (n := 342) (.exec 0x108b79 (LoadPre 0x108b79 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x37)) s (0x108b79 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108b79 4 3 (.sib 0 (some 5) 0 (.d8 0x37))) (Reg.operands [.gpr 3, .gpr 0, .gpr 5] [])) #v[339, 91, 5]
    (.letOp (n := 343) (.out 0x108b7d (movzxR32M8Effect 0x108b7d 9 11 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 344) (.exec 0x108b7d (LoadPre 0x108b7d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x108b7d + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x108b7d 9 11 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 345) (.out 0x108b86 (xorR8M8Effect 0x108b86 5 11 (.sib 0 (some 5) 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0, .gpr 5] []) (.reg (.gpr 11))) #v[343, 91, 5]
    (.letOp (n := 346) (.exec 0x108b86 (LoadPre 0x108b86 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x38)) s (0x108b86 + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x108b86 5 11 (.sib 0 (some 5) 0 (.d8 0x38))) (Reg.operands [.gpr 11, .gpr 0, .gpr 5] [])) #v[343, 91, 5]
    (.letOp (n := 347) (.out 0x108b8b (movzxR32M8Effect 0x108b8b 9 10 (.sib 4 none 0 (.d32 0xd1))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 348) (.exec 0x108b8b (LoadPre 0x108b8b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd1)) s (0x108b8b + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x108b8b 9 10 (.sib 4 none 0 (.d32 0xd1))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 349) (.out 0x108b94 (xorR8M8Effect 0x108b94 5 10 (.sib 0 (some 5) 0 (.d8 0x39))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0, .gpr 5] []) (.reg (.gpr 10))) #v[347, 91, 5]
    (.letOp (n := 350) (.exec 0x108b94 (LoadPre 0x108b94 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x39)) s (0x108b94 + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x108b94 5 10 (.sib 0 (some 5) 0 (.d8 0x39))) (Reg.operands [.gpr 10, .gpr 0, .gpr 5] [])) #v[347, 91, 5]
    (.letOp (n := 351) (.out 0x108b99 (movzxR32M8Effect 0x108b99 9 9 (.sib 4 none 0 (.d32 0xd2))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 352) (.exec 0x108b99 (LoadPre 0x108b99 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd2)) s (0x108b99 + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x108b99 9 9 (.sib 4 none 0 (.d32 0xd2))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 353) (.out 0x108ba2 (xorR8M8Effect 0x108ba2 5 9 (.sib 0 (some 5) 0 (.d8 0x3a))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0, .gpr 5] []) (.reg (.gpr 9))) #v[351, 91, 5]
    (.letOp (n := 354) (.exec 0x108ba2 (LoadPre 0x108ba2 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x3a)) s (0x108ba2 + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x108ba2 5 9 (.sib 0 (some 5) 0 (.d8 0x3a))) (Reg.operands [.gpr 9, .gpr 0, .gpr 5] [])) #v[351, 91, 5]
    (.letOp (n := 355) (.out 0x108ba7 (movzxR32M8Effect 0x108ba7 9 8 (.sib 4 none 0 (.d32 0xd3))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 356) (.exec 0x108ba7 (LoadPre 0x108ba7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd3)) s (0x108ba7 + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x108ba7 9 8 (.sib 4 none 0 (.d32 0xd3))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l1087a5_9))))))))))))))))))))))))))))))))))))))

def bytes_l1087a5_8 : List UInt8 :=
  [0x32, 0x4C, 0x28, 0x32, 0x88, 0x4C, 0x24, 0x49, 0x0F, 0xB6, 0x8C, 0x24, 0xCB, 0x00, 0x00, 0x00,
    0x32, 0x4C, 0x28, 0x33, 0x88, 0x4C, 0x24, 0x48, 0x44, 0x0F, 0xB6, 0xA4, 0x24, 0xCC, 0x00, 0x00,
    0x00, 0x44, 0x32, 0x64, 0x28, 0x34, 0x44, 0x0F, 0xB6, 0xBC, 0x24, 0xCD, 0x00, 0x00, 0x00, 0x44,
    0x32, 0x7C, 0x28, 0x35, 0x44, 0x0F, 0xB6, 0xB4, 0x24, 0xCE, 0x00, 0x00, 0x00, 0x44, 0x32, 0x74,
    0x28, 0x36, 0x0F, 0xB6, 0x9C, 0x24, 0xCF, 0x00, 0x00, 0x00, 0x32, 0x5C, 0x28, 0x37, 0x44, 0x0F,
    0xB6, 0x9C, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x44, 0x32, 0x5C, 0x28, 0x38, 0x44, 0x0F, 0xB6, 0x94,
    0x24, 0xD1, 0x00, 0x00, 0x00, 0x44, 0x32, 0x54, 0x28, 0x39, 0x44, 0x0F, 0xB6, 0x8C, 0x24, 0xD2,
    0x00, 0x00, 0x00, 0x44, 0x32, 0x4C, 0x28, 0x3A, 0x44, 0x0F, 0xB6, 0x84, 0x24, 0xD3, 0x00, 0x00,
    0x00] ++ bytes_l1087a5_9

theorem code_l1087a5_8 : ∀ x ∈ codeRange 0x108b2f bytes_l1087a5_8, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x8b2f 129 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1087a5_9

def b_l1087a5_7 : Block Op Label signature Reg.count 286 :=
  .letOp (n := 286) (.exec 0x108ac3 (StorePre 0x108ac3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x108ac3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108ac3 4 1 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[284, 4]
    (.letOp (n := 287) (.out 0x108ac7 (movzxR32M8Effect 0x108ac7 8 1 (.sib 4 none 0 (.d32 0xc4))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 288) (.exec 0x108ac7 (LoadPre 0x108ac7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc4)) s (0x108ac7 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108ac7 8 1 (.sib 4 none 0 (.d32 0xc4))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 289) (.out 0x108acf (xorR8M8Effect 0x108acf 4 1 (.sib 0 (some 5) 0 (.d8 0x2c))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[287, 91, 5]
    (.letOp (n := 290) (.exec 0x108acf (LoadPre 0x108acf (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x2c)) s (0x108acf + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108acf 4 1 (.sib 0 (some 5) 0 (.d8 0x2c))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[287, 91, 5]
    (.letOp (n := 291) (.exec 0x108ad3 (StorePre 0x108ad3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4f)) s (0x108ad3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108ad3 4 1 (.sib 4 none 0 (.d8 0x4f))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[289, 4]
    (.letOp (n := 292) (.out 0x108ad7 (movzxR32M8Effect 0x108ad7 8 1 (.sib 4 none 0 (.d32 0xc5))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 293) (.exec 0x108ad7 (LoadPre 0x108ad7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc5)) s (0x108ad7 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108ad7 8 1 (.sib 4 none 0 (.d32 0xc5))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 294) (.out 0x108adf (xorR8M8Effect 0x108adf 4 1 (.sib 0 (some 5) 0 (.d8 0x2d))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[292, 91, 5]
    (.letOp (n := 295) (.exec 0x108adf (LoadPre 0x108adf (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x2d)) s (0x108adf + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108adf 4 1 (.sib 0 (some 5) 0 (.d8 0x2d))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[292, 91, 5]
    (.letOp (n := 296) (.exec 0x108ae3 (StorePre 0x108ae3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4e)) s (0x108ae3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108ae3 4 1 (.sib 4 none 0 (.d8 0x4e))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[294, 4]
    (.letOp (n := 297) (.out 0x108ae7 (movzxR32M8Effect 0x108ae7 8 1 (.sib 4 none 0 (.d32 0xc6))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 298) (.exec 0x108ae7 (LoadPre 0x108ae7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc6)) s (0x108ae7 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108ae7 8 1 (.sib 4 none 0 (.d32 0xc6))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 299) (.out 0x108aef (xorR8M8Effect 0x108aef 4 1 (.sib 0 (some 5) 0 (.d8 0x2e))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[297, 91, 5]
    (.letOp (n := 300) (.exec 0x108aef (LoadPre 0x108aef (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x2e)) s (0x108aef + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108aef 4 1 (.sib 0 (some 5) 0 (.d8 0x2e))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[297, 91, 5]
    (.letOp (n := 301) (.exec 0x108af3 (StorePre 0x108af3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4d)) s (0x108af3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108af3 4 1 (.sib 4 none 0 (.d8 0x4d))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[299, 4]
    (.letOp (n := 302) (.out 0x108af7 (movzxR32M8Effect 0x108af7 8 1 (.sib 4 none 0 (.d32 0xc7))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 303) (.exec 0x108af7 (LoadPre 0x108af7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc7)) s (0x108af7 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108af7 8 1 (.sib 4 none 0 (.d32 0xc7))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 304) (.out 0x108aff (xorR8M8Effect 0x108aff 4 1 (.sib 0 (some 5) 0 (.d8 0x2f))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[302, 91, 5]
    (.letOp (n := 305) (.exec 0x108aff (LoadPre 0x108aff (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x2f)) s (0x108aff + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108aff 4 1 (.sib 0 (some 5) 0 (.d8 0x2f))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[302, 91, 5]
    (.letOp (n := 306) (.exec 0x108b03 (StorePre 0x108b03 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4c)) s (0x108b03 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108b03 4 1 (.sib 4 none 0 (.d8 0x4c))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[304, 4]
    (.letOp (n := 307) (.out 0x108b07 (movzxR32M8Effect 0x108b07 8 1 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 308) (.exec 0x108b07 (LoadPre 0x108b07 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x108b07 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108b07 8 1 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 309) (.out 0x108b0f (xorR8M8Effect 0x108b0f 4 1 (.sib 0 (some 5) 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[307, 91, 5]
    (.letOp (n := 310) (.exec 0x108b0f (LoadPre 0x108b0f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x30)) s (0x108b0f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108b0f 4 1 (.sib 0 (some 5) 0 (.d8 0x30))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[307, 91, 5]
    (.letOp (n := 311) (.exec 0x108b13 (StorePre 0x108b13 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4b)) s (0x108b13 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108b13 4 1 (.sib 4 none 0 (.d8 0x4b))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[309, 4]
    (.letOp (n := 312) (.out 0x108b17 (movzxR32M8Effect 0x108b17 8 1 (.sib 4 none 0 (.d32 0xc9))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 313) (.exec 0x108b17 (LoadPre 0x108b17 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc9)) s (0x108b17 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108b17 8 1 (.sib 4 none 0 (.d32 0xc9))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 314) (.out 0x108b1f (xorR8M8Effect 0x108b1f 4 1 (.sib 0 (some 5) 0 (.d8 0x31))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[312, 91, 5]
    (.letOp (n := 315) (.exec 0x108b1f (LoadPre 0x108b1f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x31)) s (0x108b1f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108b1f 4 1 (.sib 0 (some 5) 0 (.d8 0x31))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[312, 91, 5]
    (.letOp (n := 316) (.exec 0x108b23 (StorePre 0x108b23 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4a)) s (0x108b23 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108b23 4 1 (.sib 4 none 0 (.d8 0x4a))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[314, 4]
    (.letOp (n := 317) (.out 0x108b27 (movzxR32M8Effect 0x108b27 8 1 (.sib 4 none 0 (.d32 0xca))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 318) (.exec 0x108b27 (LoadPre 0x108b27 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xca)) s (0x108b27 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108b27 8 1 (.sib 4 none 0 (.d32 0xca))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l1087a5_8)))))))))))))))))))))))))))))))))

def bytes_l1087a5_7 : List UInt8 :=
  [0x88, 0x4C, 0x24, 0x50, 0x0F, 0xB6, 0x8C, 0x24, 0xC4, 0x00, 0x00, 0x00, 0x32, 0x4C, 0x28, 0x2C,
    0x88, 0x4C, 0x24, 0x4F, 0x0F, 0xB6, 0x8C, 0x24, 0xC5, 0x00, 0x00, 0x00, 0x32, 0x4C, 0x28, 0x2D,
    0x88, 0x4C, 0x24, 0x4E, 0x0F, 0xB6, 0x8C, 0x24, 0xC6, 0x00, 0x00, 0x00, 0x32, 0x4C, 0x28, 0x2E,
    0x88, 0x4C, 0x24, 0x4D, 0x0F, 0xB6, 0x8C, 0x24, 0xC7, 0x00, 0x00, 0x00, 0x32, 0x4C, 0x28, 0x2F,
    0x88, 0x4C, 0x24, 0x4C, 0x0F, 0xB6, 0x8C, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x32, 0x4C, 0x28, 0x30,
    0x88, 0x4C, 0x24, 0x4B, 0x0F, 0xB6, 0x8C, 0x24, 0xC9, 0x00, 0x00, 0x00, 0x32, 0x4C, 0x28, 0x31,
    0x88, 0x4C, 0x24, 0x4A, 0x0F, 0xB6, 0x8C, 0x24, 0xCA, 0x00, 0x00, 0x00] ++ bytes_l1087a5_8

theorem code_l1087a5_7 : ∀ x ∈ codeRange 0x108ac3 bytes_l1087a5_7, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x8ac3 108 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1087a5_8

def b_l1087a5_6 : Block Op Label signature Reg.count 252 :=
  .letOp (n := 252) (.out 0x108a57 (movzxR32M8Effect 0x108a57 8 1 (.sib 4 none 0 (.d32 0xbd))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 253) (.exec 0x108a57 (LoadPre 0x108a57 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xbd)) s (0x108a57 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108a57 8 1 (.sib 4 none 0 (.d32 0xbd))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 254) (.out 0x108a5f (xorR8M8Effect 0x108a5f 4 1 (.sib 0 (some 5) 0 (.d8 0x25))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[252, 91, 5]
    (.letOp (n := 255) (.exec 0x108a5f (LoadPre 0x108a5f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x25)) s (0x108a5f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108a5f 4 1 (.sib 0 (some 5) 0 (.d8 0x25))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[252, 91, 5]
    (.letOp (n := 256) (.exec 0x108a63 (StorePre 0x108a63 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x56)) s (0x108a63 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108a63 4 1 (.sib 4 none 0 (.d8 0x56))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[254, 4]
    (.letOp (n := 257) (.out 0x108a67 (movzxR32M8Effect 0x108a67 8 1 (.sib 4 none 0 (.d32 0xbe))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 258) (.exec 0x108a67 (LoadPre 0x108a67 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xbe)) s (0x108a67 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108a67 8 1 (.sib 4 none 0 (.d32 0xbe))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 259) (.out 0x108a6f (xorR8M8Effect 0x108a6f 4 1 (.sib 0 (some 5) 0 (.d8 0x26))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[257, 91, 5]
    (.letOp (n := 260) (.exec 0x108a6f (LoadPre 0x108a6f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x26)) s (0x108a6f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108a6f 4 1 (.sib 0 (some 5) 0 (.d8 0x26))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[257, 91, 5]
    (.letOp (n := 261) (.exec 0x108a73 (StorePre 0x108a73 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x55)) s (0x108a73 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108a73 4 1 (.sib 4 none 0 (.d8 0x55))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[259, 4]
    (.letOp (n := 262) (.out 0x108a77 (movzxR32M8Effect 0x108a77 8 1 (.sib 4 none 0 (.d32 0xbf))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 263) (.exec 0x108a77 (LoadPre 0x108a77 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xbf)) s (0x108a77 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108a77 8 1 (.sib 4 none 0 (.d32 0xbf))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 264) (.out 0x108a7f (xorR8M8Effect 0x108a7f 4 1 (.sib 0 (some 5) 0 (.d8 0x27))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[262, 91, 5]
    (.letOp (n := 265) (.exec 0x108a7f (LoadPre 0x108a7f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x27)) s (0x108a7f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108a7f 4 1 (.sib 0 (some 5) 0 (.d8 0x27))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[262, 91, 5]
    (.letOp (n := 266) (.exec 0x108a83 (StorePre 0x108a83 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x54)) s (0x108a83 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108a83 4 1 (.sib 4 none 0 (.d8 0x54))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[264, 4]
    (.letOp (n := 267) (.out 0x108a87 (movzxR32M8Effect 0x108a87 8 1 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 268) (.exec 0x108a87 (LoadPre 0x108a87 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x108a87 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108a87 8 1 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 269) (.out 0x108a8f (xorR8M8Effect 0x108a8f 4 1 (.sib 0 (some 5) 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[267, 91, 5]
    (.letOp (n := 270) (.exec 0x108a8f (LoadPre 0x108a8f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x28)) s (0x108a8f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108a8f 4 1 (.sib 0 (some 5) 0 (.d8 0x28))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[267, 91, 5]
    (.letOp (n := 271) (.exec 0x108a93 (StorePre 0x108a93 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x53)) s (0x108a93 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108a93 4 1 (.sib 4 none 0 (.d8 0x53))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[269, 4]
    (.letOp (n := 272) (.out 0x108a97 (movzxR32M8Effect 0x108a97 8 1 (.sib 4 none 0 (.d32 0xc1))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 273) (.exec 0x108a97 (LoadPre 0x108a97 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc1)) s (0x108a97 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108a97 8 1 (.sib 4 none 0 (.d32 0xc1))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 274) (.out 0x108a9f (xorR8M8Effect 0x108a9f 4 1 (.sib 0 (some 5) 0 (.d8 0x29))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[272, 91, 5]
    (.letOp (n := 275) (.exec 0x108a9f (LoadPre 0x108a9f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x29)) s (0x108a9f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108a9f 4 1 (.sib 0 (some 5) 0 (.d8 0x29))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[272, 91, 5]
    (.letOp (n := 276) (.exec 0x108aa3 (StorePre 0x108aa3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x52)) s (0x108aa3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108aa3 4 1 (.sib 4 none 0 (.d8 0x52))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[274, 4]
    (.letOp (n := 277) (.out 0x108aa7 (movzxR32M8Effect 0x108aa7 8 1 (.sib 4 none 0 (.d32 0xc2))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 278) (.exec 0x108aa7 (LoadPre 0x108aa7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc2)) s (0x108aa7 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108aa7 8 1 (.sib 4 none 0 (.d32 0xc2))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 279) (.out 0x108aaf (xorR8M8Effect 0x108aaf 4 1 (.sib 0 (some 5) 0 (.d8 0x2a))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[277, 91, 5]
    (.letOp (n := 280) (.exec 0x108aaf (LoadPre 0x108aaf (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x2a)) s (0x108aaf + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108aaf 4 1 (.sib 0 (some 5) 0 (.d8 0x2a))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[277, 91, 5]
    (.letOp (n := 281) (.exec 0x108ab3 (StorePre 0x108ab3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x51)) s (0x108ab3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108ab3 4 1 (.sib 4 none 0 (.d8 0x51))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[279, 4]
    (.letOp (n := 282) (.out 0x108ab7 (movzxR32M8Effect 0x108ab7 8 1 (.sib 4 none 0 (.d32 0xc3))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 283) (.exec 0x108ab7 (LoadPre 0x108ab7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc3)) s (0x108ab7 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108ab7 8 1 (.sib 4 none 0 (.d32 0xc3))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 284) (.out 0x108abf (xorR8M8Effect 0x108abf 4 1 (.sib 0 (some 5) 0 (.d8 0x2b))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[282, 91, 5]
    (.letOp (n := 285) (.exec 0x108abf (LoadPre 0x108abf (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x2b)) s (0x108abf + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108abf 4 1 (.sib 0 (some 5) 0 (.d8 0x2b))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[282, 91, 5]
    (b_l1087a5_7))))))))))))))))))))))))))))))))))

def bytes_l1087a5_6 : List UInt8 :=
  [0x0F, 0xB6, 0x8C, 0x24, 0xBD, 0x00, 0x00, 0x00, 0x32, 0x4C, 0x28, 0x25, 0x88, 0x4C, 0x24, 0x56,
    0x0F, 0xB6, 0x8C, 0x24, 0xBE, 0x00, 0x00, 0x00, 0x32, 0x4C, 0x28, 0x26, 0x88, 0x4C, 0x24, 0x55,
    0x0F, 0xB6, 0x8C, 0x24, 0xBF, 0x00, 0x00, 0x00, 0x32, 0x4C, 0x28, 0x27, 0x88, 0x4C, 0x24, 0x54,
    0x0F, 0xB6, 0x8C, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x32, 0x4C, 0x28, 0x28, 0x88, 0x4C, 0x24, 0x53,
    0x0F, 0xB6, 0x8C, 0x24, 0xC1, 0x00, 0x00, 0x00, 0x32, 0x4C, 0x28, 0x29, 0x88, 0x4C, 0x24, 0x52,
    0x0F, 0xB6, 0x8C, 0x24, 0xC2, 0x00, 0x00, 0x00, 0x32, 0x4C, 0x28, 0x2A, 0x88, 0x4C, 0x24, 0x51,
    0x0F, 0xB6, 0x8C, 0x24, 0xC3, 0x00, 0x00, 0x00, 0x32, 0x4C, 0x28, 0x2B] ++ bytes_l1087a5_7

theorem code_l1087a5_6 : ∀ x ∈ codeRange 0x108a57 bytes_l1087a5_6, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x8a57 108 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1087a5_7

def b_l1087a5_5 : Block Op Label signature Reg.count 219 :=
  .letOp (n := 219) (.out 0x1089ef (xorR8M8Effect 0x1089ef 4 1 (.sib 0 (some 5) 0 (.d8 0x1e))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[217, 91, 5]
    (.letOp (n := 220) (.exec 0x1089ef (LoadPre 0x1089ef (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x1e)) s (0x1089ef + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1089ef 4 1 (.sib 0 (some 5) 0 (.d8 0x1e))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[217, 91, 5]
    (.letOp (n := 221) (.exec 0x1089f3 (StorePre 0x1089f3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5d)) s (0x1089f3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1089f3 4 1 (.sib 4 none 0 (.d8 0x5d))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[219, 4]
    (.letOp (n := 222) (.out 0x1089f7 (movzxR32M8Effect 0x1089f7 8 1 (.sib 4 none 0 (.d32 0xb7))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 223) (.exec 0x1089f7 (LoadPre 0x1089f7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb7)) s (0x1089f7 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1089f7 8 1 (.sib 4 none 0 (.d32 0xb7))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 224) (.out 0x1089ff (xorR8M8Effect 0x1089ff 4 1 (.sib 0 (some 5) 0 (.d8 0x1f))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[222, 91, 5]
    (.letOp (n := 225) (.exec 0x1089ff (LoadPre 0x1089ff (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x1f)) s (0x1089ff + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1089ff 4 1 (.sib 0 (some 5) 0 (.d8 0x1f))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[222, 91, 5]
    (.letOp (n := 226) (.exec 0x108a03 (StorePre 0x108a03 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5c)) s (0x108a03 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108a03 4 1 (.sib 4 none 0 (.d8 0x5c))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[224, 4]
    (.letOp (n := 227) (.out 0x108a07 (movzxR32M8Effect 0x108a07 8 1 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 228) (.exec 0x108a07 (LoadPre 0x108a07 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x108a07 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108a07 8 1 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 229) (.out 0x108a0f (xorR8M8Effect 0x108a0f 4 1 (.sib 0 (some 5) 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[227, 91, 5]
    (.letOp (n := 230) (.exec 0x108a0f (LoadPre 0x108a0f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x20)) s (0x108a0f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108a0f 4 1 (.sib 0 (some 5) 0 (.d8 0x20))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[227, 91, 5]
    (.letOp (n := 231) (.exec 0x108a13 (StorePre 0x108a13 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5b)) s (0x108a13 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108a13 4 1 (.sib 4 none 0 (.d8 0x5b))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[229, 4]
    (.letOp (n := 232) (.out 0x108a17 (movzxR32M8Effect 0x108a17 8 1 (.sib 4 none 0 (.d32 0xb9))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 233) (.exec 0x108a17 (LoadPre 0x108a17 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb9)) s (0x108a17 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108a17 8 1 (.sib 4 none 0 (.d32 0xb9))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 234) (.out 0x108a1f (xorR8M8Effect 0x108a1f 4 1 (.sib 0 (some 5) 0 (.d8 0x21))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[232, 91, 5]
    (.letOp (n := 235) (.exec 0x108a1f (LoadPre 0x108a1f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x21)) s (0x108a1f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108a1f 4 1 (.sib 0 (some 5) 0 (.d8 0x21))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[232, 91, 5]
    (.letOp (n := 236) (.exec 0x108a23 (StorePre 0x108a23 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5a)) s (0x108a23 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108a23 4 1 (.sib 4 none 0 (.d8 0x5a))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[234, 4]
    (.letOp (n := 237) (.out 0x108a27 (movzxR32M8Effect 0x108a27 8 1 (.sib 4 none 0 (.d32 0xba))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 238) (.exec 0x108a27 (LoadPre 0x108a27 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xba)) s (0x108a27 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108a27 8 1 (.sib 4 none 0 (.d32 0xba))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 239) (.out 0x108a2f (xorR8M8Effect 0x108a2f 4 1 (.sib 0 (some 5) 0 (.d8 0x22))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[237, 91, 5]
    (.letOp (n := 240) (.exec 0x108a2f (LoadPre 0x108a2f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x22)) s (0x108a2f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108a2f 4 1 (.sib 0 (some 5) 0 (.d8 0x22))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[237, 91, 5]
    (.letOp (n := 241) (.exec 0x108a33 (StorePre 0x108a33 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x59)) s (0x108a33 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108a33 4 1 (.sib 4 none 0 (.d8 0x59))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[239, 4]
    (.letOp (n := 242) (.out 0x108a37 (movzxR32M8Effect 0x108a37 8 1 (.sib 4 none 0 (.d32 0xbb))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 243) (.exec 0x108a37 (LoadPre 0x108a37 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xbb)) s (0x108a37 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108a37 8 1 (.sib 4 none 0 (.d32 0xbb))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 244) (.out 0x108a3f (xorR8M8Effect 0x108a3f 4 1 (.sib 0 (some 5) 0 (.d8 0x23))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[242, 91, 5]
    (.letOp (n := 245) (.exec 0x108a3f (LoadPre 0x108a3f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x23)) s (0x108a3f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108a3f 4 1 (.sib 0 (some 5) 0 (.d8 0x23))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[242, 91, 5]
    (.letOp (n := 246) (.exec 0x108a43 (StorePre 0x108a43 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x108a43 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108a43 4 1 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[244, 4]
    (.letOp (n := 247) (.out 0x108a47 (movzxR32M8Effect 0x108a47 8 1 (.sib 4 none 0 (.d32 0xbc))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 248) (.exec 0x108a47 (LoadPre 0x108a47 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xbc)) s (0x108a47 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108a47 8 1 (.sib 4 none 0 (.d32 0xbc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 249) (.out 0x108a4f (xorR8M8Effect 0x108a4f 4 1 (.sib 0 (some 5) 0 (.d8 0x24))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[247, 91, 5]
    (.letOp (n := 250) (.exec 0x108a4f (LoadPre 0x108a4f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x24)) s (0x108a4f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x108a4f 4 1 (.sib 0 (some 5) 0 (.d8 0x24))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[247, 91, 5]
    (.letOp (n := 251) (.exec 0x108a53 (StorePre 0x108a53 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x57)) s (0x108a53 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108a53 4 1 (.sib 4 none 0 (.d8 0x57))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[249, 4]
    (b_l1087a5_6)))))))))))))))))))))))))))))))))

def bytes_l1087a5_5 : List UInt8 :=
  [0x32, 0x4C, 0x28, 0x1E, 0x88, 0x4C, 0x24, 0x5D, 0x0F, 0xB6, 0x8C, 0x24, 0xB7, 0x00, 0x00, 0x00,
    0x32, 0x4C, 0x28, 0x1F, 0x88, 0x4C, 0x24, 0x5C, 0x0F, 0xB6, 0x8C, 0x24, 0xB8, 0x00, 0x00, 0x00,
    0x32, 0x4C, 0x28, 0x20, 0x88, 0x4C, 0x24, 0x5B, 0x0F, 0xB6, 0x8C, 0x24, 0xB9, 0x00, 0x00, 0x00,
    0x32, 0x4C, 0x28, 0x21, 0x88, 0x4C, 0x24, 0x5A, 0x0F, 0xB6, 0x8C, 0x24, 0xBA, 0x00, 0x00, 0x00,
    0x32, 0x4C, 0x28, 0x22, 0x88, 0x4C, 0x24, 0x59, 0x0F, 0xB6, 0x8C, 0x24, 0xBB, 0x00, 0x00, 0x00,
    0x32, 0x4C, 0x28, 0x23, 0x88, 0x4C, 0x24, 0x58, 0x0F, 0xB6, 0x8C, 0x24, 0xBC, 0x00, 0x00, 0x00,
    0x32, 0x4C, 0x28, 0x24, 0x88, 0x4C, 0x24, 0x57] ++ bytes_l1087a5_6

theorem code_l1087a5_5 : ∀ x ∈ codeRange 0x1089ef bytes_l1087a5_5, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x89ef 104 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1087a5_6

def b_l1087a5_4 : Block Op Label signature Reg.count 186 :=
  .letOp (n := 186) (.exec 0x108983 (StorePre 0x108983 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x64)) s (0x108983 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108983 4 1 (.sib 4 none 0 (.d8 0x64))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[184, 4]
    (.letOp (n := 187) (.out 0x108987 (movzxR32M8Effect 0x108987 8 1 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 188) (.exec 0x108987 (LoadPre 0x108987 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x108987 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108987 8 1 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 189) (.out 0x10898f (xorR8M8Effect 0x10898f 4 1 (.sib 0 (some 5) 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[187, 91, 5]
    (.letOp (n := 190) (.exec 0x10898f (LoadPre 0x10898f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x18)) s (0x10898f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10898f 4 1 (.sib 0 (some 5) 0 (.d8 0x18))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[187, 91, 5]
    (.letOp (n := 191) (.exec 0x108993 (StorePre 0x108993 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x63)) s (0x108993 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108993 4 1 (.sib 4 none 0 (.d8 0x63))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[189, 4]
    (.letOp (n := 192) (.out 0x108997 (movzxR32M8Effect 0x108997 8 1 (.sib 4 none 0 (.d32 0xb1))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 193) (.exec 0x108997 (LoadPre 0x108997 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb1)) s (0x108997 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108997 8 1 (.sib 4 none 0 (.d32 0xb1))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 194) (.out 0x10899f (xorR8M8Effect 0x10899f 4 1 (.sib 0 (some 5) 0 (.d8 0x19))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[192, 91, 5]
    (.letOp (n := 195) (.exec 0x10899f (LoadPre 0x10899f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x19)) s (0x10899f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10899f 4 1 (.sib 0 (some 5) 0 (.d8 0x19))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[192, 91, 5]
    (.letOp (n := 196) (.exec 0x1089a3 (StorePre 0x1089a3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x62)) s (0x1089a3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1089a3 4 1 (.sib 4 none 0 (.d8 0x62))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[194, 4]
    (.letOp (n := 197) (.out 0x1089a7 (movzxR32M8Effect 0x1089a7 8 1 (.sib 4 none 0 (.d32 0xb2))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 198) (.exec 0x1089a7 (LoadPre 0x1089a7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb2)) s (0x1089a7 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1089a7 8 1 (.sib 4 none 0 (.d32 0xb2))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 199) (.out 0x1089af (xorR8M8Effect 0x1089af 4 1 (.sib 0 (some 5) 0 (.d8 0x1a))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[197, 91, 5]
    (.letOp (n := 200) (.exec 0x1089af (LoadPre 0x1089af (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x1a)) s (0x1089af + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1089af 4 1 (.sib 0 (some 5) 0 (.d8 0x1a))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[197, 91, 5]
    (.letOp (n := 201) (.exec 0x1089b3 (StorePre 0x1089b3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x61)) s (0x1089b3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1089b3 4 1 (.sib 4 none 0 (.d8 0x61))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[199, 4]
    (.letOp (n := 202) (.out 0x1089b7 (movzxR32M8Effect 0x1089b7 8 1 (.sib 4 none 0 (.d32 0xb3))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 203) (.exec 0x1089b7 (LoadPre 0x1089b7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb3)) s (0x1089b7 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1089b7 8 1 (.sib 4 none 0 (.d32 0xb3))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 204) (.out 0x1089bf (xorR8M8Effect 0x1089bf 4 1 (.sib 0 (some 5) 0 (.d8 0x1b))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[202, 91, 5]
    (.letOp (n := 205) (.exec 0x1089bf (LoadPre 0x1089bf (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x1b)) s (0x1089bf + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1089bf 4 1 (.sib 0 (some 5) 0 (.d8 0x1b))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[202, 91, 5]
    (.letOp (n := 206) (.exec 0x1089c3 (StorePre 0x1089c3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1089c3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1089c3 4 1 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[204, 4]
    (.letOp (n := 207) (.out 0x1089c7 (movzxR32M8Effect 0x1089c7 8 1 (.sib 4 none 0 (.d32 0xb4))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 208) (.exec 0x1089c7 (LoadPre 0x1089c7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb4)) s (0x1089c7 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1089c7 8 1 (.sib 4 none 0 (.d32 0xb4))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 209) (.out 0x1089cf (xorR8M8Effect 0x1089cf 4 1 (.sib 0 (some 5) 0 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[207, 91, 5]
    (.letOp (n := 210) (.exec 0x1089cf (LoadPre 0x1089cf (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x1c)) s (0x1089cf + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1089cf 4 1 (.sib 0 (some 5) 0 (.d8 0x1c))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[207, 91, 5]
    (.letOp (n := 211) (.exec 0x1089d3 (StorePre 0x1089d3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5f)) s (0x1089d3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1089d3 4 1 (.sib 4 none 0 (.d8 0x5f))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[209, 4]
    (.letOp (n := 212) (.out 0x1089d7 (movzxR32M8Effect 0x1089d7 8 1 (.sib 4 none 0 (.d32 0xb5))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 213) (.exec 0x1089d7 (LoadPre 0x1089d7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb5)) s (0x1089d7 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1089d7 8 1 (.sib 4 none 0 (.d32 0xb5))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 214) (.out 0x1089df (xorR8M8Effect 0x1089df 4 1 (.sib 0 (some 5) 0 (.d8 0x1d))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[212, 91, 5]
    (.letOp (n := 215) (.exec 0x1089df (LoadPre 0x1089df (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x1d)) s (0x1089df + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1089df 4 1 (.sib 0 (some 5) 0 (.d8 0x1d))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[212, 91, 5]
    (.letOp (n := 216) (.exec 0x1089e3 (StorePre 0x1089e3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5e)) s (0x1089e3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1089e3 4 1 (.sib 4 none 0 (.d8 0x5e))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[214, 4]
    (.letOp (n := 217) (.out 0x1089e7 (movzxR32M8Effect 0x1089e7 8 1 (.sib 4 none 0 (.d32 0xb6))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 218) (.exec 0x1089e7 (LoadPre 0x1089e7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb6)) s (0x1089e7 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1089e7 8 1 (.sib 4 none 0 (.d32 0xb6))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l1087a5_5)))))))))))))))))))))))))))))))))

def bytes_l1087a5_4 : List UInt8 :=
  [0x88, 0x4C, 0x24, 0x64, 0x0F, 0xB6, 0x8C, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x32, 0x4C, 0x28, 0x18,
    0x88, 0x4C, 0x24, 0x63, 0x0F, 0xB6, 0x8C, 0x24, 0xB1, 0x00, 0x00, 0x00, 0x32, 0x4C, 0x28, 0x19,
    0x88, 0x4C, 0x24, 0x62, 0x0F, 0xB6, 0x8C, 0x24, 0xB2, 0x00, 0x00, 0x00, 0x32, 0x4C, 0x28, 0x1A,
    0x88, 0x4C, 0x24, 0x61, 0x0F, 0xB6, 0x8C, 0x24, 0xB3, 0x00, 0x00, 0x00, 0x32, 0x4C, 0x28, 0x1B,
    0x88, 0x4C, 0x24, 0x60, 0x0F, 0xB6, 0x8C, 0x24, 0xB4, 0x00, 0x00, 0x00, 0x32, 0x4C, 0x28, 0x1C,
    0x88, 0x4C, 0x24, 0x5F, 0x0F, 0xB6, 0x8C, 0x24, 0xB5, 0x00, 0x00, 0x00, 0x32, 0x4C, 0x28, 0x1D,
    0x88, 0x4C, 0x24, 0x5E, 0x0F, 0xB6, 0x8C, 0x24, 0xB6, 0x00, 0x00, 0x00] ++ bytes_l1087a5_5

theorem code_l1087a5_4 : ∀ x ∈ codeRange 0x108983 bytes_l1087a5_4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x8983 108 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1087a5_5

def b_l1087a5_3 : Block Op Label signature Reg.count 152 :=
  .letOp (n := 152) (.out 0x108917 (movzxR32M8Effect 0x108917 8 1 (.sib 4 none 0 (.d32 0xa9))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 153) (.exec 0x108917 (LoadPre 0x108917 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa9)) s (0x108917 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108917 8 1 (.sib 4 none 0 (.d32 0xa9))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 154) (.out 0x10891f (xorR8M8Effect 0x10891f 4 1 (.sib 0 (some 5) 0 (.d8 0x11))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[152, 91, 5]
    (.letOp (n := 155) (.exec 0x10891f (LoadPre 0x10891f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x11)) s (0x10891f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10891f 4 1 (.sib 0 (some 5) 0 (.d8 0x11))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[152, 91, 5]
    (.letOp (n := 156) (.exec 0x108923 (StorePre 0x108923 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6a)) s (0x108923 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108923 4 1 (.sib 4 none 0 (.d8 0x6a))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[154, 4]
    (.letOp (n := 157) (.out 0x108927 (movzxR32M8Effect 0x108927 8 1 (.sib 4 none 0 (.d32 0xaa))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 158) (.exec 0x108927 (LoadPre 0x108927 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xaa)) s (0x108927 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108927 8 1 (.sib 4 none 0 (.d32 0xaa))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 159) (.out 0x10892f (xorR8M8Effect 0x10892f 4 1 (.sib 0 (some 5) 0 (.d8 0x12))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[157, 91, 5]
    (.letOp (n := 160) (.exec 0x10892f (LoadPre 0x10892f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x12)) s (0x10892f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10892f 4 1 (.sib 0 (some 5) 0 (.d8 0x12))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[157, 91, 5]
    (.letOp (n := 161) (.exec 0x108933 (StorePre 0x108933 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x69)) s (0x108933 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108933 4 1 (.sib 4 none 0 (.d8 0x69))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[159, 4]
    (.letOp (n := 162) (.out 0x108937 (movzxR32M8Effect 0x108937 8 1 (.sib 4 none 0 (.d32 0xab))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 163) (.exec 0x108937 (LoadPre 0x108937 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xab)) s (0x108937 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108937 8 1 (.sib 4 none 0 (.d32 0xab))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 164) (.out 0x10893f (xorR8M8Effect 0x10893f 4 1 (.sib 0 (some 5) 0 (.d8 0x13))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[162, 91, 5]
    (.letOp (n := 165) (.exec 0x10893f (LoadPre 0x10893f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x13)) s (0x10893f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10893f 4 1 (.sib 0 (some 5) 0 (.d8 0x13))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[162, 91, 5]
    (.letOp (n := 166) (.exec 0x108943 (StorePre 0x108943 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x108943 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108943 4 1 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[164, 4]
    (.letOp (n := 167) (.out 0x108947 (movzxR32M8Effect 0x108947 8 1 (.sib 4 none 0 (.d32 0xac))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 168) (.exec 0x108947 (LoadPre 0x108947 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xac)) s (0x108947 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108947 8 1 (.sib 4 none 0 (.d32 0xac))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 169) (.out 0x10894f (xorR8M8Effect 0x10894f 4 1 (.sib 0 (some 5) 0 (.d8 0x14))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[167, 91, 5]
    (.letOp (n := 170) (.exec 0x10894f (LoadPre 0x10894f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x14)) s (0x10894f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10894f 4 1 (.sib 0 (some 5) 0 (.d8 0x14))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[167, 91, 5]
    (.letOp (n := 171) (.exec 0x108953 (StorePre 0x108953 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x67)) s (0x108953 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108953 4 1 (.sib 4 none 0 (.d8 0x67))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[169, 4]
    (.letOp (n := 172) (.out 0x108957 (movzxR32M8Effect 0x108957 8 1 (.sib 4 none 0 (.d32 0xad))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 173) (.exec 0x108957 (LoadPre 0x108957 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xad)) s (0x108957 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108957 8 1 (.sib 4 none 0 (.d32 0xad))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 174) (.out 0x10895f (xorR8M8Effect 0x10895f 4 1 (.sib 0 (some 5) 0 (.d8 0x15))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[172, 91, 5]
    (.letOp (n := 175) (.exec 0x10895f (LoadPre 0x10895f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x15)) s (0x10895f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10895f 4 1 (.sib 0 (some 5) 0 (.d8 0x15))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[172, 91, 5]
    (.letOp (n := 176) (.exec 0x108963 (StorePre 0x108963 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x66)) s (0x108963 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108963 4 1 (.sib 4 none 0 (.d8 0x66))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[174, 4]
    (.letOp (n := 177) (.out 0x108967 (movzxR32M8Effect 0x108967 8 1 (.sib 4 none 0 (.d32 0xae))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 178) (.exec 0x108967 (LoadPre 0x108967 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xae)) s (0x108967 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108967 8 1 (.sib 4 none 0 (.d32 0xae))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 179) (.out 0x10896f (xorR8M8Effect 0x10896f 4 1 (.sib 0 (some 5) 0 (.d8 0x16))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[177, 91, 5]
    (.letOp (n := 180) (.exec 0x10896f (LoadPre 0x10896f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x16)) s (0x10896f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10896f 4 1 (.sib 0 (some 5) 0 (.d8 0x16))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[177, 91, 5]
    (.letOp (n := 181) (.exec 0x108973 (StorePre 0x108973 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x65)) s (0x108973 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108973 4 1 (.sib 4 none 0 (.d8 0x65))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[179, 4]
    (.letOp (n := 182) (.out 0x108977 (movzxR32M8Effect 0x108977 8 1 (.sib 4 none 0 (.d32 0xaf))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 183) (.exec 0x108977 (LoadPre 0x108977 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xaf)) s (0x108977 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108977 8 1 (.sib 4 none 0 (.d32 0xaf))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 184) (.out 0x10897f (xorR8M8Effect 0x10897f 4 1 (.sib 0 (some 5) 0 (.d8 0x17))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[182, 91, 5]
    (.letOp (n := 185) (.exec 0x10897f (LoadPre 0x10897f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x17)) s (0x10897f + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10897f 4 1 (.sib 0 (some 5) 0 (.d8 0x17))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[182, 91, 5]
    (b_l1087a5_4))))))))))))))))))))))))))))))))))

def bytes_l1087a5_3 : List UInt8 :=
  [0x0F, 0xB6, 0x8C, 0x24, 0xA9, 0x00, 0x00, 0x00, 0x32, 0x4C, 0x28, 0x11, 0x88, 0x4C, 0x24, 0x6A,
    0x0F, 0xB6, 0x8C, 0x24, 0xAA, 0x00, 0x00, 0x00, 0x32, 0x4C, 0x28, 0x12, 0x88, 0x4C, 0x24, 0x69,
    0x0F, 0xB6, 0x8C, 0x24, 0xAB, 0x00, 0x00, 0x00, 0x32, 0x4C, 0x28, 0x13, 0x88, 0x4C, 0x24, 0x68,
    0x0F, 0xB6, 0x8C, 0x24, 0xAC, 0x00, 0x00, 0x00, 0x32, 0x4C, 0x28, 0x14, 0x88, 0x4C, 0x24, 0x67,
    0x0F, 0xB6, 0x8C, 0x24, 0xAD, 0x00, 0x00, 0x00, 0x32, 0x4C, 0x28, 0x15, 0x88, 0x4C, 0x24, 0x66,
    0x0F, 0xB6, 0x8C, 0x24, 0xAE, 0x00, 0x00, 0x00, 0x32, 0x4C, 0x28, 0x16, 0x88, 0x4C, 0x24, 0x65,
    0x0F, 0xB6, 0x8C, 0x24, 0xAF, 0x00, 0x00, 0x00, 0x32, 0x4C, 0x28, 0x17] ++ bytes_l1087a5_4

theorem code_l1087a5_3 : ∀ x ∈ codeRange 0x108917 bytes_l1087a5_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x8917 108 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1087a5_4

def b_l1087a5_2 : Block Op Label signature Reg.count 120 :=
  .letOp (n := 120) (.out 0x1088a9 (xorR8M8Effect 0x1088a9 5 14 (.sib 0 (some 5) 0 (.d8 0x9))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 0, .gpr 5] []) (.reg (.gpr 14))) #v[71, 91, 5]
    (.letOp (n := 121) (.exec 0x1088a9 (LoadPre 0x1088a9 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x9)) s (0x1088a9 + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x1088a9 5 14 (.sib 0 (some 5) 0 (.d8 0x9))) (Reg.operands [.gpr 14, .gpr 0, .gpr 5] [])) #v[71, 91, 5]
    (.letOp (n := 122) (.exec 0x1088ae (StorePre 0x1088ae 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6e)) s (0x1088ae + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1088ae 5 14 (.sib 4 none 0 (.d8 0x6e))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[120, 4]
    (.letOp (n := 123) (.out 0x1088b3 (xorR8M8Effect 0x1088b3 5 15 (.sib 0 (some 5) 0 (.d8 0xa))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 0, .gpr 5] []) (.reg (.gpr 15))) #v[73, 91, 5]
    (.letOp (n := 124) (.exec 0x1088b3 (LoadPre 0x1088b3 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0xa)) s (0x1088b3 + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x1088b3 5 15 (.sib 0 (some 5) 0 (.d8 0xa))) (Reg.operands [.gpr 15, .gpr 0, .gpr 5] [])) #v[73, 91, 5]
    (.letOp (n := 125) (.exec 0x1088b8 (StorePre 0x1088b8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6d)) s (0x1088b8 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1088b8 5 15 (.sib 4 none 0 (.d8 0x6d))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[123, 4]
    (.letOp (n := 126) (.out 0x1088bd (xorR8M8Effect 0x1088bd 5 12 (.sib 0 (some 5) 0 (.d8 0xb))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 0, .gpr 5] []) (.reg (.gpr 12))) #v[75, 91, 5]
    (.letOp (n := 127) (.exec 0x1088bd (LoadPre 0x1088bd (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0xb)) s (0x1088bd + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x1088bd 5 12 (.sib 0 (some 5) 0 (.d8 0xb))) (Reg.operands [.gpr 12, .gpr 0, .gpr 5] [])) #v[75, 91, 5]
    (.letOp (n := 128) (.exec 0x1088c2 (StorePre 0x1088c2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6c)) s (0x1088c2 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1088c2 5 12 (.sib 4 none 0 (.d8 0x6c))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[126, 4]
    (.letOp (n := 129) (.out 0x1088c7 (xorR8M8Effect 0x1088c7 5 13 (.sib 0 (some 5) 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 0, .gpr 5] []) (.reg (.gpr 13))) #v[77, 91, 5]
    (.letOp (n := 130) (.exec 0x1088c7 (LoadPre 0x1088c7 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0xc)) s (0x1088c7 + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x1088c7 5 13 (.sib 0 (some 5) 0 (.d8 0xc))) (Reg.operands [.gpr 13, .gpr 0, .gpr 5] [])) #v[77, 91, 5]
    (.letOp (n := 131) (.exec 0x1088cc (StorePre 0x1088cc 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6b)) s (0x1088cc + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1088cc 5 13 (.sib 4 none 0 (.d8 0x6b))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[129, 4]
    (.letOp (n := 132) (.out 0x1088d1 (movzxR32M8Effect 0x1088d1 8 1 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 133) (.exec 0x1088d1 (LoadPre 0x1088d1 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1088d1 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1088d1 8 1 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 134) (.out 0x1088d9 (xorR8M8Effect 0x1088d9 4 1 (.sib 0 (some 5) 0 (.d8 0xd))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[132, 91, 5]
    (.letOp (n := 135) (.exec 0x1088d9 (LoadPre 0x1088d9 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0xd)) s (0x1088d9 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1088d9 4 1 (.sib 0 (some 5) 0 (.d8 0xd))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[132, 91, 5]
    (.letOp (n := 136) (.exec 0x1088dd (StorePre 0x1088dd 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1088dd + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x1088dd 7 1 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[134, 4]
    (.letOp (n := 137) (.out 0x1088e4 (movzxR32M8Effect 0x1088e4 5 1 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 138) (.exec 0x1088e4 (LoadPre 0x1088e4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1088e4 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1088e4 5 1 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 139) (.out 0x1088e9 (xorR8M8Effect 0x1088e9 4 1 (.sib 0 (some 5) 0 (.d8 0xe))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[137, 91, 5]
    (.letOp (n := 140) (.exec 0x1088e9 (LoadPre 0x1088e9 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0xe)) s (0x1088e9 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1088e9 4 1 (.sib 0 (some 5) 0 (.d8 0xe))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[137, 91, 5]
    (.letOp (n := 141) (.exec 0x1088ed (StorePre 0x1088ed 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1088ed + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1088ed 4 1 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[139, 4]
    (.letOp (n := 142) (.out 0x1088f1 (movzxR32M8Effect 0x1088f1 8 1 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 143) (.exec 0x1088f1 (LoadPre 0x1088f1 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1088f1 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1088f1 8 1 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 144) (.out 0x1088f9 (xorR8M8Effect 0x1088f9 4 1 (.sib 0 (some 5) 0 (.d8 0xf))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[142, 91, 5]
    (.letOp (n := 145) (.exec 0x1088f9 (LoadPre 0x1088f9 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0xf)) s (0x1088f9 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1088f9 4 1 (.sib 0 (some 5) 0 (.d8 0xf))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[142, 91, 5]
    (.letOp (n := 146) (.exec 0x1088fd (StorePre 0x1088fd 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1088fd + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x1088fd 7 1 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[144, 4]
    (.letOp (n := 147) (.out 0x108904 (movzxR32M8Effect 0x108904 8 1 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 148) (.exec 0x108904 (LoadPre 0x108904 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x108904 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108904 8 1 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 149) (.out 0x10890c (xorR8M8Effect 0x10890c 4 1 (.sib 0 (some 5) 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[147, 91, 5]
    (.letOp (n := 150) (.exec 0x10890c (LoadPre 0x10890c (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x10)) s (0x10890c + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10890c 4 1 (.sib 0 (some 5) 0 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[147, 91, 5]
    (.letOp (n := 151) (.exec 0x108910 (StorePre 0x108910 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x108910 + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x108910 7 1 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[149, 4]
    (b_l1087a5_3))))))))))))))))))))))))))))))))

def bytes_l1087a5_2 : List UInt8 :=
  [0x44, 0x32, 0x74, 0x28, 0x09, 0x44, 0x88, 0x74, 0x24, 0x6E, 0x44, 0x32, 0x7C, 0x28, 0x0A, 0x44,
    0x88, 0x7C, 0x24, 0x6D, 0x44, 0x32, 0x64, 0x28, 0x0B, 0x44, 0x88, 0x64, 0x24, 0x6C, 0x44, 0x32,
    0x6C, 0x28, 0x0C, 0x44, 0x88, 0x6C, 0x24, 0x6B, 0x0F, 0xB6, 0x8C, 0x24, 0x80, 0x00, 0x00, 0x00,
    0x32, 0x4C, 0x28, 0x0D, 0x88, 0x8C, 0x24, 0x80, 0x00, 0x00, 0x00, 0x0F, 0xB6, 0x4C, 0x24, 0x78,
    0x32, 0x4C, 0x28, 0x0E, 0x88, 0x4C, 0x24, 0x78, 0x0F, 0xB6, 0x8C, 0x24, 0x88, 0x00, 0x00, 0x00,
    0x32, 0x4C, 0x28, 0x0F, 0x88, 0x8C, 0x24, 0x88, 0x00, 0x00, 0x00, 0x0F, 0xB6, 0x8C, 0x24, 0x90,
    0x00, 0x00, 0x00, 0x32, 0x4C, 0x28, 0x10, 0x88, 0x8C, 0x24, 0x90, 0x00, 0x00, 0x00] ++ bytes_l1087a5_3

theorem code_l1087a5_2 : ∀ x ∈ codeRange 0x1088a9 bytes_l1087a5_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x88a9 110 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1087a5_3

def b_l1087a5_1 : Block Op Label signature Reg.count 90 :=
  .letOp (n := 90) (.exec 0x108847 (StorePre 0x108847 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x108847 + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x108847 7 0 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[88, 4]
    (.letOp (n := 91) (.out 0x10884e (movR64M64Effect 0x10884e 0 (.sib 4 none 0 (.d32 0xf0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 92) (.exec 0x10884e (LoadPre 0x10884e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x10884e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10884e 0 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 93) (.out 0x108856 (xorR8M8Effect 0x108856 3 1 (.sib 0 (some 5) 0 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0, .gpr 5] []) (.reg (.gpr 1))) #v[53, 91, 5]
    (.letOp (n := 94) (.exec 0x108856 (LoadPre 0x108856 (fun s => AddrMode.addr (.sib 0 (some 5) 0 .none) s (0x108856 + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x108856 3 1 (.sib 0 (some 5) 0 .none)) (Reg.operands [.gpr 1, .gpr 0, .gpr 5] [])) #v[53, 91, 5]
    (.letOp (n := 95) (.exec 0x108859 (StorePre 0x108859 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x77)) s (0x108859 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108859 4 1 (.sib 4 none 0 (.d8 0x77))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[93, 4]
    (.letOp (n := 96) (.out 0x10885d (xorR8M8Effect 0x10885d 4 2 (.sib 0 (some 5) 0 (.d8 0x1))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0, .gpr 5] []) (.reg (.gpr 2))) #v[55, 91, 5]
    (.letOp (n := 97) (.exec 0x10885d (LoadPre 0x10885d (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x1)) s (0x10885d + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10885d 4 2 (.sib 0 (some 5) 0 (.d8 0x1))) (Reg.operands [.gpr 2, .gpr 0, .gpr 5] [])) #v[55, 91, 5]
    (.letOp (n := 98) (.exec 0x108861 (StorePre 0x108861 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x76)) s (0x108861 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108861 4 2 (.sib 4 none 0 (.d8 0x76))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[96, 4]
    (.letOp (n := 99) (.out 0x108865 (xorR8M8Effect 0x108865 5 6 (.sib 0 (some 5) 0 (.d8 0x2))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0, .gpr 5] []) (.reg (.gpr 6))) #v[57, 91, 5]
    (.letOp (n := 100) (.exec 0x108865 (LoadPre 0x108865 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x2)) s (0x108865 + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x108865 5 6 (.sib 0 (some 5) 0 (.d8 0x2))) (Reg.operands [.gpr 6, .gpr 0, .gpr 5] [])) #v[57, 91, 5]
    (.letOp (n := 101) (.exec 0x10886a (StorePre 0x10886a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x75)) s (0x10886a + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x10886a 5 6 (.sib 4 none 0 (.d8 0x75))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[99, 4]
    (.letOp (n := 102) (.out 0x10886f (xorR8M8Effect 0x10886f 5 7 (.sib 0 (some 5) 0 (.d8 0x3))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0, .gpr 5] []) (.reg (.gpr 7))) #v[59, 91, 5]
    (.letOp (n := 103) (.exec 0x10886f (LoadPre 0x10886f (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x3)) s (0x10886f + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x10886f 5 7 (.sib 0 (some 5) 0 (.d8 0x3))) (Reg.operands [.gpr 7, .gpr 0, .gpr 5] [])) #v[59, 91, 5]
    (.letOp (n := 104) (.exec 0x108874 (StorePre 0x108874 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x74)) s (0x108874 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108874 5 7 (.sib 4 none 0 (.d8 0x74))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[102, 4]
    (.letOp (n := 105) (.out 0x108879 (xorR8M8Effect 0x108879 5 8 (.sib 0 (some 5) 0 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0, .gpr 5] []) (.reg (.gpr 8))) #v[61, 91, 5]
    (.letOp (n := 106) (.exec 0x108879 (LoadPre 0x108879 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x4)) s (0x108879 + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x108879 5 8 (.sib 0 (some 5) 0 (.d8 0x4))) (Reg.operands [.gpr 8, .gpr 0, .gpr 5] [])) #v[61, 91, 5]
    (.letOp (n := 107) (.exec 0x10887e (StorePre 0x10887e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x73)) s (0x10887e + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x10887e 5 8 (.sib 4 none 0 (.d8 0x73))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[105, 4]
    (.letOp (n := 108) (.out 0x108883 (xorR8M8Effect 0x108883 5 9 (.sib 0 (some 5) 0 (.d8 0x5))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0, .gpr 5] []) (.reg (.gpr 9))) #v[63, 91, 5]
    (.letOp (n := 109) (.exec 0x108883 (LoadPre 0x108883 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x5)) s (0x108883 + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x108883 5 9 (.sib 0 (some 5) 0 (.d8 0x5))) (Reg.operands [.gpr 9, .gpr 0, .gpr 5] [])) #v[63, 91, 5]
    (.letOp (n := 110) (.exec 0x108888 (StorePre 0x108888 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x72)) s (0x108888 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108888 5 9 (.sib 4 none 0 (.d8 0x72))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[108, 4]
    (.letOp (n := 111) (.out 0x10888d (xorR8M8Effect 0x10888d 5 10 (.sib 0 (some 5) 0 (.d8 0x6))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0, .gpr 5] []) (.reg (.gpr 10))) #v[65, 91, 5]
    (.letOp (n := 112) (.exec 0x10888d (LoadPre 0x10888d (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x6)) s (0x10888d + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x10888d 5 10 (.sib 0 (some 5) 0 (.d8 0x6))) (Reg.operands [.gpr 10, .gpr 0, .gpr 5] [])) #v[65, 91, 5]
    (.letOp (n := 113) (.exec 0x108892 (StorePre 0x108892 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x71)) s (0x108892 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108892 5 10 (.sib 4 none 0 (.d8 0x71))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[111, 4]
    (.letOp (n := 114) (.out 0x108897 (xorR8M8Effect 0x108897 5 11 (.sib 0 (some 5) 0 (.d8 0x7))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0, .gpr 5] []) (.reg (.gpr 11))) #v[67, 91, 5]
    (.letOp (n := 115) (.exec 0x108897 (LoadPre 0x108897 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x7)) s (0x108897 + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x108897 5 11 (.sib 0 (some 5) 0 (.d8 0x7))) (Reg.operands [.gpr 11, .gpr 0, .gpr 5] [])) #v[67, 91, 5]
    (.letOp (n := 116) (.exec 0x10889c (StorePre 0x10889c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x10889c + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x10889c 5 11 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[114, 4]
    (.letOp (n := 117) (.out 0x1088a1 (xorR8M8Effect 0x1088a1 4 3 (.sib 0 (some 5) 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0, .gpr 5] []) (.reg (.gpr 3))) #v[69, 91, 5]
    (.letOp (n := 118) (.exec 0x1088a1 (LoadPre 0x1088a1 (fun s => AddrMode.addr (.sib 0 (some 5) 0 (.d8 0x8)) s (0x1088a1 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1088a1 4 3 (.sib 0 (some 5) 0 (.d8 0x8))) (Reg.operands [.gpr 3, .gpr 0, .gpr 5] [])) #v[69, 91, 5]
    (.letOp (n := 119) (.exec 0x1088a5 (StorePre 0x1088a5 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6f)) s (0x1088a5 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1088a5 4 3 (.sib 4 none 0 (.d8 0x6f))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[117, 4]
    (b_l1087a5_2))))))))))))))))))))))))))))))

def bytes_l1087a5_1 : List UInt8 :=
  [0x88, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x84, 0x24, 0xF0, 0x00, 0x00, 0x00, 0x32,
    0x0C, 0x28, 0x88, 0x4C, 0x24, 0x77, 0x32, 0x54, 0x28, 0x01, 0x88, 0x54, 0x24, 0x76, 0x40, 0x32,
    0x74, 0x28, 0x02, 0x40, 0x88, 0x74, 0x24, 0x75, 0x40, 0x32, 0x7C, 0x28, 0x03, 0x40, 0x88, 0x7C,
    0x24, 0x74, 0x44, 0x32, 0x44, 0x28, 0x04, 0x44, 0x88, 0x44, 0x24, 0x73, 0x44, 0x32, 0x4C, 0x28,
    0x05, 0x44, 0x88, 0x4C, 0x24, 0x72, 0x44, 0x32, 0x54, 0x28, 0x06, 0x44, 0x88, 0x54, 0x24, 0x71,
    0x44, 0x32, 0x5C, 0x28, 0x07, 0x44, 0x88, 0x5C, 0x24, 0x70, 0x32, 0x5C, 0x28, 0x08, 0x88, 0x5C,
    0x24, 0x6F] ++ bytes_l1087a5_2

theorem code_l1087a5_1 : ∀ x ∈ codeRange 0x108847 bytes_l1087a5_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x8847 98 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1087a5_2

def b_l1087a5 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1087a5 (movzxR32M8Effect 0x1087a5 8 1 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x1087a5 (LoadPre 0x1087a5 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x1087a5 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1087a5 8 1 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1087ad (movzxR32M8Effect 0x1087ad 8 2 (.sib 4 none 0 (.d32 0x99))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 56) (.exec 0x1087ad (LoadPre 0x1087ad (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x99)) s (0x1087ad + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1087ad 8 2 (.sib 4 none 0 (.d32 0x99))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1087b5 (movzxR32M8Effect 0x1087b5 8 6 (.sib 4 none 0 (.d32 0x9a))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 58) (.exec 0x1087b5 (LoadPre 0x1087b5 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9a)) s (0x1087b5 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1087b5 8 6 (.sib 4 none 0 (.d32 0x9a))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x1087bd (movzxR32M8Effect 0x1087bd 8 7 (.sib 4 none 0 (.d32 0x9b))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 60) (.exec 0x1087bd (LoadPre 0x1087bd (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9b)) s (0x1087bd + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1087bd 8 7 (.sib 4 none 0 (.d32 0x9b))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x1087c5 (movzxR32M8Effect 0x1087c5 9 8 (.sib 4 none 0 (.d32 0x9c))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 62) (.exec 0x1087c5 (LoadPre 0x1087c5 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9c)) s (0x1087c5 + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x1087c5 9 8 (.sib 4 none 0 (.d32 0x9c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x1087ce (movzxR32M8Effect 0x1087ce 9 9 (.sib 4 none 0 (.d32 0x9d))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 64) (.exec 0x1087ce (LoadPre 0x1087ce (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9d)) s (0x1087ce + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x1087ce 9 9 (.sib 4 none 0 (.d32 0x9d))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x1087d7 (movzxR32M8Effect 0x1087d7 9 10 (.sib 4 none 0 (.d32 0x9e))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 66) (.exec 0x1087d7 (LoadPre 0x1087d7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9e)) s (0x1087d7 + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x1087d7 9 10 (.sib 4 none 0 (.d32 0x9e))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x1087e0 (movzxR32M8Effect 0x1087e0 9 11 (.sib 4 none 0 (.d32 0x9f))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 68) (.exec 0x1087e0 (LoadPre 0x1087e0 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9f)) s (0x1087e0 + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x1087e0 9 11 (.sib 4 none 0 (.d32 0x9f))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.out 0x1087e9 (movzxR32M8Effect 0x1087e9 8 3 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 70) (.exec 0x1087e9 (LoadPre 0x1087e9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x1087e9 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1087e9 8 3 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.out 0x1087f1 (movzxR32M8Effect 0x1087f1 9 14 (.sib 4 none 0 (.d32 0xa1))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 72) (.exec 0x1087f1 (LoadPre 0x1087f1 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa1)) s (0x1087f1 + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x1087f1 9 14 (.sib 4 none 0 (.d32 0xa1))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.out 0x1087fa (movzxR32M8Effect 0x1087fa 9 15 (.sib 4 none 0 (.d32 0xa2))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 74) (.exec 0x1087fa (LoadPre 0x1087fa (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa2)) s (0x1087fa + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x1087fa 9 15 (.sib 4 none 0 (.d32 0xa2))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.out 0x108803 (movzxR32M8Effect 0x108803 9 12 (.sib 4 none 0 (.d32 0xa3))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 76) (.exec 0x108803 (LoadPre 0x108803 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa3)) s (0x108803 + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x108803 9 12 (.sib 4 none 0 (.d32 0xa3))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 77) (.out 0x10880c (movzxR32M8Effect 0x10880c 9 13 (.sib 4 none 0 (.d32 0xa4))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 78) (.exec 0x10880c (LoadPre 0x10880c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa4)) s (0x10880c + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x10880c 9 13 (.sib 4 none 0 (.d32 0xa4))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.out 0x108815 (movzxR32M8Effect 0x108815 8 0 (.sib 4 none 0 (.d32 0xa5))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 80) (.exec 0x108815 (LoadPre 0x108815 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa5)) s (0x108815 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108815 8 0 (.sib 4 none 0 (.d32 0xa5))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 81) (.exec 0x10881d (StorePre 0x10881d 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10881d + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x10881d 7 0 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[79, 4]
    (.letOp (n := 82) (.out 0x108824 (movzxR32M8Effect 0x108824 8 0 (.sib 4 none 0 (.d32 0xa6))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 83) (.exec 0x108824 (LoadPre 0x108824 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa6)) s (0x108824 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108824 8 0 (.sib 4 none 0 (.d32 0xa6))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 84) (.exec 0x10882c (StorePre 0x10882c 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10882c + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10882c 4 0 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[82, 4]
    (.letOp (n := 85) (.out 0x108830 (movzxR32M8Effect 0x108830 8 0 (.sib 4 none 0 (.d32 0xa7))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 86) (.exec 0x108830 (LoadPre 0x108830 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa7)) s (0x108830 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x108830 8 0 (.sib 4 none 0 (.d32 0xa7))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 87) (.exec 0x108838 (StorePre 0x108838 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x108838 + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x108838 7 0 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[85, 4]
    (.letOp (n := 88) (.out 0x10883f (movzxR32M8Effect 0x10883f 8 0 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 89) (.exec 0x10883f (LoadPre 0x10883f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x10883f + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x10883f 8 0 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l1087a5_1)))))))))))))))))))))))))))))))))))))

def bytes_l1087a5 : List UInt8 :=
  [0x0F, 0xB6, 0x8C, 0x24, 0x98, 0x00, 0x00, 0x00, 0x0F, 0xB6, 0x94, 0x24, 0x99, 0x00, 0x00, 0x00,
    0x0F, 0xB6, 0xB4, 0x24, 0x9A, 0x00, 0x00, 0x00, 0x0F, 0xB6, 0xBC, 0x24, 0x9B, 0x00, 0x00, 0x00,
    0x44, 0x0F, 0xB6, 0x84, 0x24, 0x9C, 0x00, 0x00, 0x00, 0x44, 0x0F, 0xB6, 0x8C, 0x24, 0x9D, 0x00,
    0x00, 0x00, 0x44, 0x0F, 0xB6, 0x94, 0x24, 0x9E, 0x00, 0x00, 0x00, 0x44, 0x0F, 0xB6, 0x9C, 0x24,
    0x9F, 0x00, 0x00, 0x00, 0x0F, 0xB6, 0x9C, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x44, 0x0F, 0xB6, 0xB4,
    0x24, 0xA1, 0x00, 0x00, 0x00, 0x44, 0x0F, 0xB6, 0xBC, 0x24, 0xA2, 0x00, 0x00, 0x00, 0x44, 0x0F,
    0xB6, 0xA4, 0x24, 0xA3, 0x00, 0x00, 0x00, 0x44, 0x0F, 0xB6, 0xAC, 0x24, 0xA4, 0x00, 0x00, 0x00,
    0x0F, 0xB6, 0x84, 0x24, 0xA5, 0x00, 0x00, 0x00, 0x88, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x0F,
    0xB6, 0x84, 0x24, 0xA6, 0x00, 0x00, 0x00, 0x88, 0x44, 0x24, 0x78, 0x0F, 0xB6, 0x84, 0x24, 0xA7,
    0x00, 0x00, 0x00, 0x88, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, 0x0F, 0xB6, 0x84, 0x24, 0xA8, 0x00,
    0x00, 0x00] ++ bytes_l1087a5_1

theorem code_l1087a5 : ∀ x ∈ codeRange 0x1087a5 bytes_l1087a5, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x87a5 162 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1087a5_1

@[cfg_block] def b_l108e98_2 : Block Op Label signature Reg.count 108 :=
  .letOp (n := 108) (.out 0x108f8b (movR32Imm32Effect 0x108f8b 5 6 0x8) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 109) (.exec 0x108f8b (fun s => s.RIP = 0x108f8b) (movR32Imm32Effect 0x108f8b 5 6 0x8) (Reg.operands [] [])) #v[]
    (.letOp (n := 110) (.out 0x108f90 (leaR64Effect 0x108f90 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 111) (.exec 0x108f90 (fun s => s.RIP = 0x108f90) (leaR64Effect 0x108f90 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 112) (.out 0x108f95 (leaR64Effect 0x108f95 2 (.sib 4 none 0 (.d32 0x100))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 113) (.exec 0x108f95 (fun s => s.RIP = 0x108f95) (leaR64Effect 0x108f95 2 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 114) (.out 0x108f9d (callEffect (fun _ => 0x10a690) 0x108fa2) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 115) (.exec 0x108f9d (PushPre 0x108f9d 5) (callEffect (fun _ => 0x10a690) 0x108fa2) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 116) (.const ⟨64, 0x108fa2⟩) #v[]
    (.terminate (.call ⟨.l10a690, RegMap.args [(0, 93), (1, 57), (2, 112), (3, 3), (4, 114), (5, 5), (6, 108), (7, 110), (8, 81), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 117⟩ { target := .l108fa2, kept := #v[], arity := rfl, guard := some (Fin.last 116) }))))))))))

def bytes_l108e98_2 : List UInt8 :=
  [0xBE, 0x08, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x7C, 0x24, 0x08, 0x48, 0x8D, 0x94, 0x24, 0x00, 0x01,
    0x00, 0x00, 0xE8, 0xEE, 0x16, 0x00, 0x00]

theorem code_l108e98_2 : ∀ x ∈ codeRange 0x108f8b bytes_l108e98_2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x8f8b 23 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l108e98_1 : Block Op Label signature Reg.count 84 :=
  .letOp (n := 84) (.exec 0x108f03 (StorePre 0x108f03 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x124)) s (0x108f03 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x108f03 2 (.sib 4 none 0 (.d32 0x124))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 85) (.exec 0x108f0a (StorePre 0x108f0a 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x108f0a + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x108f0a 6 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 86) (.exec 0x108f11 (StorePre 0x108f11 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x12c)) s (0x108f11 + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x108f11 8 (.sib 4 none 0 (.d32 0x12c))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[81, 4]
    (.letOp (n := 87) (.out 0x108f19 (addR32R32Effect 0x108f19 2 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[55, 53]
    (.letOp (n := 88) (.exec 0x108f19 (fun s => s.RIP = 0x108f19) (addR32R32Effect 0x108f19 2 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[55, 53]
    (.letOp (n := 89) (.out 0x108f1b (addR32Imm8Effect 0x108f1b 3 7 0x3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[87]
    (.letOp (n := 90) (.exec 0x108f1b (fun s => s.RIP = 0x108f1b) (addR32Imm8Effect 0x108f1b 3 7 0x3) (Reg.operands [.gpr 7] [])) #v[87]
    (.letOp (n := 91) (.out 0x108f1e (bswapR32Effect 0x108f1e 2 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[89]
    (.letOp (n := 92) (.exec 0x108f1e (fun s => s.RIP = 0x108f1e) (bswapR32Effect 0x108f1e 2 7) (Reg.operands [.gpr 7] [])) #v[89]
    (.letOp (n := 93) (.out 0x108f20 (addR32Imm8Effect 0x108f20 3 0 0x4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 94) (.exec 0x108f20 (fun s => s.RIP = 0x108f20) (addR32Imm8Effect 0x108f20 3 0 0x4) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 95) (.exec 0x108f23 (StorePre 0x108f23 4 (fun s => AddrMode.addr (.base 9 (.d8 0x10)) s (0x108f23 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x108f23 0 (.base 9 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 9] [])) #v[93, 9]
    (.letOp (n := 96) (.exec 0x108f27 (StorePre 0x108f27 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x108f27 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x108f27 1 (.sib 4 none 0 (.d32 0x130))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 97) (.exec 0x108f2e (StorePre 0x108f2e 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x134)) s (0x108f2e + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x108f2e 2 (.sib 4 none 0 (.d32 0x134))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 98) (.exec 0x108f35 (StorePre 0x108f35 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x138)) s (0x108f35 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x108f35 6 (.sib 4 none 0 (.d32 0x138))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 99) (.exec 0x108f3c (StorePre 0x108f3c 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x13c)) s (0x108f3c + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x108f3c 7 (.sib 4 none 0 (.d32 0x13c))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[91, 4]
    (.letOp (n := 100) (.exec 0x108f43 (StorePre 0x108f43 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x108f43 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x108f43 (.sib 4 none 0 (.d8 0x40)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 101) (.exec 0x108f4c (StorePre 0x108f4c 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x108f4c + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x108f4c (.sib 4 none 0 (.d8 0x38)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 102) (.exec 0x108f55 (StorePre 0x108f55 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x108f55 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x108f55 (.sib 4 none 0 (.d8 0x30)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 103) (.exec 0x108f5e (StorePre 0x108f5e 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x108f5e + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x108f5e (.sib 4 none 0 (.d8 0x28)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 104) (.exec 0x108f67 (StorePre 0x108f67 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x108f67 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x108f67 (.sib 4 none 0 (.d8 0x20)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 105) (.exec 0x108f70 (StorePre 0x108f70 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x108f70 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x108f70 (.sib 4 none 0 (.d8 0x18)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 106) (.exec 0x108f79 (StorePre 0x108f79 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108f79 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x108f79 (.sib 4 none 0 (.d8 0x10)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 107) (.exec 0x108f82 (StorePre 0x108f82 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x108f82 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x108f82 (.sib 4 none 0 (.d8 0x8)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l108e98_2))))))))))))))))))))))))

def bytes_l108e98_1 : List UInt8 :=
  [0x89, 0x94, 0x24, 0x24, 0x01, 0x00, 0x00, 0x89, 0xB4, 0x24, 0x28, 0x01, 0x00, 0x00, 0x44, 0x89,
    0x84, 0x24, 0x2C, 0x01, 0x00, 0x00, 0x01, 0xC7, 0x83, 0xC7, 0x03, 0x0F, 0xCF, 0x83, 0xC0, 0x04,
    0x41, 0x89, 0x41, 0x10, 0x89, 0x8C, 0x24, 0x30, 0x01, 0x00, 0x00, 0x89, 0x94, 0x24, 0x34, 0x01,
    0x00, 0x00, 0x89, 0xB4, 0x24, 0x38, 0x01, 0x00, 0x00, 0x89, 0xBC, 0x24, 0x3C, 0x01, 0x00, 0x00,
    0x48, 0xC7, 0x44, 0x24, 0x40, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x38, 0x00, 0x00,
    0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x30, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x28,
    0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x20, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44,
    0x24, 0x18, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x10, 0x00, 0x00, 0x00, 0x00, 0x48,
    0xC7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00] ++ bytes_l108e98_2

theorem code_l108e98_1 : ∀ x ∈ codeRange 0x108f03 bytes_l108e98_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x8f03 136 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l108e98_2

@[cfg_block] def b_l108e98 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x108e98 (movR32M32Effect 0x108e98 0 (.base 9 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[9]
    (.letOp (n := 54) (.exec 0x108e98 (LoadPre 0x108e98 (fun s => AddrMode.addr (.base 9 (.d8 0x10)) s (0x108e98 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x108e98 0 (.base 9 (.d8 0x10))) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 55) (.out 0x108e9c (movR32M32Effect 0x108e9c 7 (.base 9 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 9] []) (.reg (.gpr 7))) #v[9]
    (.letOp (n := 56) (.exec 0x108e9c (LoadPre 0x108e9c (fun s => AddrMode.addr (.base 9 (.d8 0xc)) s (0x108e9c + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x108e9c 7 (.base 9 (.d8 0xc))) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 57) (.out 0x108ea0 (movR32M32Effect 0x108ea0 1 (.base 9 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 9] []) (.reg (.gpr 1))) #v[9]
    (.letOp (n := 58) (.exec 0x108ea0 (LoadPre 0x108ea0 (fun s => AddrMode.addr (.base 9 .none) s (0x108ea0 + BitVec.ofNat 64 3)) 4) (movR32M32Effect 0x108ea0 1 (.base 9 .none)) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 59) (.out 0x108ea3 (movR32M32Effect 0x108ea3 2 (.base 9 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9] []) (.reg (.gpr 2))) #v[9]
    (.letOp (n := 60) (.exec 0x108ea3 (LoadPre 0x108ea3 (fun s => AddrMode.addr (.base 9 (.d8 0x4)) s (0x108ea3 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x108ea3 2 (.base 9 (.d8 0x4))) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 61) (.out 0x108ea7 (movR32M32Effect 0x108ea7 6 (.base 9 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 9] []) (.reg (.gpr 6))) #v[9]
    (.letOp (n := 62) (.exec 0x108ea7 (LoadPre 0x108ea7 (fun s => AddrMode.addr (.base 9 (.d8 0x8)) s (0x108ea7 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x108ea7 6 (.base 9 (.d8 0x8))) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 63) (.out 0x108eab (leaR32Effect 0x108eab 4 8 (.sib 7 (some 0) 0 .none)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 7, .gpr 0] []) (.reg (.gpr 8))) #v[55, 53]
    (.letOp (n := 64) (.exec 0x108eab (fun s => s.RIP = 0x108eab) (leaR32Effect 0x108eab 4 8 (.sib 7 (some 0) 0 .none)) (Reg.operands [.gpr 7, .gpr 0] [])) #v[55, 53]
    (.letOp (n := 65) (.out 0x108eaf (bswapR32Effect 0x108eaf 3 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[63]
    (.letOp (n := 66) (.exec 0x108eaf (fun s => s.RIP = 0x108eaf) (bswapR32Effect 0x108eaf 3 8) (Reg.operands [.gpr 8] [])) #v[63]
    (.letOp (n := 67) (.exec 0x108eb2 (StorePre 0x108eb2 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x108eb2 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x108eb2 1 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 68) (.exec 0x108eb9 (StorePre 0x108eb9 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x104)) s (0x108eb9 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x108eb9 2 (.sib 4 none 0 (.d32 0x104))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 69) (.exec 0x108ec0 (StorePre 0x108ec0 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x108ec0 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x108ec0 6 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 70) (.exec 0x108ec7 (StorePre 0x108ec7 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x10c)) s (0x108ec7 + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x108ec7 8 (.sib 4 none 0 (.d32 0x10c))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 71) (.out 0x108ecf (leaR32Effect 0x108ecf 5 8 (.sib 7 (some 0) 0 (.d8 0x1))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 7, .gpr 0] []) (.reg (.gpr 8))) #v[55, 53]
    (.letOp (n := 72) (.exec 0x108ecf (fun s => s.RIP = 0x108ecf) (leaR32Effect 0x108ecf 5 8 (.sib 7 (some 0) 0 (.d8 0x1))) (Reg.operands [.gpr 7, .gpr 0] [])) #v[55, 53]
    (.letOp (n := 73) (.out 0x108ed4 (bswapR32Effect 0x108ed4 3 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[71]
    (.letOp (n := 74) (.exec 0x108ed4 (fun s => s.RIP = 0x108ed4) (bswapR32Effect 0x108ed4 3 8) (Reg.operands [.gpr 8] [])) #v[71]
    (.letOp (n := 75) (.exec 0x108ed7 (StorePre 0x108ed7 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x108ed7 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x108ed7 1 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 76) (.exec 0x108ede (StorePre 0x108ede 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x114)) s (0x108ede + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x108ede 2 (.sib 4 none 0 (.d32 0x114))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 77) (.exec 0x108ee5 (StorePre 0x108ee5 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x108ee5 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x108ee5 6 (.sib 4 none 0 (.d32 0x118))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 78) (.exec 0x108eec (StorePre 0x108eec 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x11c)) s (0x108eec + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x108eec 8 (.sib 4 none 0 (.d32 0x11c))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[73, 4]
    (.letOp (n := 79) (.out 0x108ef4 (leaR32Effect 0x108ef4 5 8 (.sib 7 (some 0) 0 (.d8 0x2))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 7, .gpr 0] []) (.reg (.gpr 8))) #v[55, 53]
    (.letOp (n := 80) (.exec 0x108ef4 (fun s => s.RIP = 0x108ef4) (leaR32Effect 0x108ef4 5 8 (.sib 7 (some 0) 0 (.d8 0x2))) (Reg.operands [.gpr 7, .gpr 0] [])) #v[55, 53]
    (.letOp (n := 81) (.out 0x108ef9 (bswapR32Effect 0x108ef9 3 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[79]
    (.letOp (n := 82) (.exec 0x108ef9 (fun s => s.RIP = 0x108ef9) (bswapR32Effect 0x108ef9 3 8) (Reg.operands [.gpr 8] [])) #v[79]
    (.letOp (n := 83) (.exec 0x108efc (StorePre 0x108efc 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x108efc + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x108efc 1 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[57, 4]
    (b_l108e98_1)))))))))))))))))))))))))))))))

def bytes_l108e98 : List UInt8 :=
  [0x41, 0x8B, 0x41, 0x10, 0x41, 0x8B, 0x79, 0x0C, 0x41, 0x8B, 0x09, 0x41, 0x8B, 0x51, 0x04, 0x41,
    0x8B, 0x71, 0x08, 0x44, 0x8D, 0x04, 0x07, 0x41, 0x0F, 0xC8, 0x89, 0x8C, 0x24, 0x00, 0x01, 0x00,
    0x00, 0x89, 0x94, 0x24, 0x04, 0x01, 0x00, 0x00, 0x89, 0xB4, 0x24, 0x08, 0x01, 0x00, 0x00, 0x44,
    0x89, 0x84, 0x24, 0x0C, 0x01, 0x00, 0x00, 0x44, 0x8D, 0x44, 0x07, 0x01, 0x41, 0x0F, 0xC8, 0x89,
    0x8C, 0x24, 0x10, 0x01, 0x00, 0x00, 0x89, 0x94, 0x24, 0x14, 0x01, 0x00, 0x00, 0x89, 0xB4, 0x24,
    0x18, 0x01, 0x00, 0x00, 0x44, 0x89, 0x84, 0x24, 0x1C, 0x01, 0x00, 0x00, 0x44, 0x8D, 0x44, 0x07,
    0x02, 0x41, 0x0F, 0xC8, 0x89, 0x8C, 0x24, 0x20, 0x01, 0x00, 0x00] ++ bytes_l108e98_1

theorem code_l108e98 : ∀ x ∈ codeRange 0x108e98 bytes_l108e98, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x8e98 107 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l108e98_1

@[cfg_block] def b_l108fa2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x108fa2 (movR64M64Effect 0x108fa2 0 (.sib 4 none 0 (.d32 0x158))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x108fa2 (LoadPre 0x108fa2 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x158)) s (0x108fa2 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x108fa2 0 (.sib 4 none 0 (.d32 0x158))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x108faa (StorePre 0x108faa 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x108faa + BitVec.ofNat 64 5)) 8) (xorMREffect 0x108faa 5 64 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x108faf (movR64M64Effect 0x108faf 0 (.sib 4 none 0 (.d32 0x160))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x108faf (LoadPre 0x108faf (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x160)) s (0x108faf + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x108faf 0 (.sib 4 none 0 (.d32 0x160))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x108fb7 (StorePre 0x108fb7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108fb7 + BitVec.ofNat 64 5)) 8) (xorMREffect 0x108fb7 5 64 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x108fbc (movR64M64Effect 0x108fbc 0 (.sib 4 none 0 (.d32 0x168))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x108fbc (LoadPre 0x108fbc (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x168)) s (0x108fbc + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x108fbc 0 (.sib 4 none 0 (.d32 0x168))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x108fc4 (StorePre 0x108fc4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x108fc4 + BitVec.ofNat 64 5)) 8) (xorMREffect 0x108fc4 5 64 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x108fc9 (movR64M64Effect 0x108fc9 0 (.sib 4 none 0 (.d32 0x170))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x108fc9 (LoadPre 0x108fc9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x170)) s (0x108fc9 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x108fc9 0 (.sib 4 none 0 (.d32 0x170))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x108fd1 (StorePre 0x108fd1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x108fd1 + BitVec.ofNat 64 5)) 8) (xorMREffect 0x108fd1 5 64 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x108fd6 (movR64M64Effect 0x108fd6 0 (.sib 4 none 0 (.d32 0x178))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 66) (.exec 0x108fd6 (LoadPre 0x108fd6 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x178)) s (0x108fd6 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x108fd6 0 (.sib 4 none 0 (.d32 0x178))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x108fde (StorePre 0x108fde 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x108fde + BitVec.ofNat 64 5)) 8) (xorMREffect 0x108fde 5 64 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x108fe3 (movR64M64Effect 0x108fe3 0 (.sib 4 none 0 (.d32 0x180))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 69) (.exec 0x108fe3 (LoadPre 0x108fe3 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x180)) s (0x108fe3 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x108fe3 0 (.sib 4 none 0 (.d32 0x180))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.exec 0x108feb (StorePre 0x108feb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x108feb + BitVec.ofNat 64 5)) 8) (xorMREffect 0x108feb 5 64 0 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[68, 4]
    (.letOp (n := 71) (.out 0x108ff0 (movR64M64Effect 0x108ff0 0 (.sib 4 none 0 (.d32 0x188))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 72) (.exec 0x108ff0 (LoadPre 0x108ff0 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x188)) s (0x108ff0 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x108ff0 0 (.sib 4 none 0 (.d32 0x188))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.exec 0x108ff8 (StorePre 0x108ff8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x108ff8 + BitVec.ofNat 64 5)) 8) (xorMREffect 0x108ff8 5 64 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[71, 4]
    (.letOp (n := 74) (.out 0x108ffd (movR64M64Effect 0x108ffd 15 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 75) (.exec 0x108ffd (LoadPre 0x108ffd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x108ffd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x108ffd 15 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 76) (.out 0x109002 (movR32Imm32Effect 0x109002 5 5 0x8) (EffectPart.reads (.reg (.gpr 5)) [] []) (.reg (.gpr 5))) #v[]
    (.letOp (n := 77) (.exec 0x109002 (fun s => s.RIP = 0x109002) (movR32Imm32Effect 0x109002 5 5 0x8) (Reg.operands [] [])) #v[]
    (.letOp (n := 78) (.exec 0x109007 (fun s => s.RIP = 0x109007) (fun _ => nopEffect 0x109007 9) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l109010, RegMap.args [(0, 71), (4, 4), (5, 76), (12, 12), (13, 13), (14, 14), (15, 74), (22, 22), (39, 39), (50, 50), (51, 51)] 79⟩)))))))))))))))))))))))))))

def bytes_l108fa2 : List UInt8 :=
  [0x48, 0x8B, 0x84, 0x24, 0x58, 0x01, 0x00, 0x00, 0x48, 0x31, 0x44, 0x24, 0x08, 0x48, 0x8B, 0x84,
    0x24, 0x60, 0x01, 0x00, 0x00, 0x48, 0x31, 0x44, 0x24, 0x10, 0x48, 0x8B, 0x84, 0x24, 0x68, 0x01,
    0x00, 0x00, 0x48, 0x31, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x84, 0x24, 0x70, 0x01, 0x00, 0x00, 0x48,
    0x31, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x84, 0x24, 0x78, 0x01, 0x00, 0x00, 0x48, 0x31, 0x44, 0x24,
    0x28, 0x48, 0x8B, 0x84, 0x24, 0x80, 0x01, 0x00, 0x00, 0x48, 0x31, 0x44, 0x24, 0x30, 0x48, 0x8B,
    0x84, 0x24, 0x88, 0x01, 0x00, 0x00, 0x48, 0x31, 0x44, 0x24, 0x38, 0x4C, 0x8B, 0x7C, 0x24, 0x40,
    0xBD, 0x08, 0x00, 0x00, 0x00, 0x66, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem code_l108fa2 : ∀ x ∈ codeRange 0x108fa2 bytes_l108fa2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x8fa2 110 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109010 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x109010 (xorR64M64Effect 0x109010 15 (.sib 4 (some 5) 3 (.d32 0x150))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 4, .gpr 5] []) (.reg (.gpr 15))) #v[15, 4, 5]
    (.letOp (n := 54) (.exec 0x109010 (LoadPre 0x109010 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x150)) s (0x109010 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x109010 15 (.sib 4 (some 5) 3 (.d32 0x150))) (Reg.operands [.gpr 15, .gpr 4, .gpr 5] [])) #v[15, 4, 5]
    (.letOp (n := 55) (.exec 0x109018 (StorePre 0x109018 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x109018 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109018 15 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x10901d (movR32Imm32Effect 0x10901d 5 6 0x8) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 57) (.exec 0x10901d (fun s => s.RIP = 0x10901d) (movR32Imm32Effect 0x10901d 5 6 0x8) (Reg.operands [] [])) #v[]
    (.letOp (n := 58) (.out 0x109022 (leaR64Effect 0x109022 3 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 59) (.exec 0x109022 (fun s => s.RIP = 0x109022) (leaR64Effect 0x109022 3 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.out 0x109027 (movR64R64Effect 0x109027 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[58]
    (.letOp (n := 61) (.exec 0x109027 (fun s => s.RIP = 0x109027) (movR64R64Effect 0x109027 7 3) (Reg.operands [.gpr 3] [])) #v[58]
    (.letOp (n := 62) (.out 0x10902a (callEffect (fun _ => 0x100e90) 0x10902f) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 63) (.exec 0x10902a (PushPre 0x10902a 5) (callEffect (fun _ => 0x100e90) 0x10902f) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.const ⟨64, 0x10902f⟩) #v[]
    (.terminate (.call ⟨.l100e90, RegMap.args [(3, 58), (4, 62), (5, 5), (6, 56), (7, 60), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 65⟩ { target := .l10902f, kept := #v[], arity := rfl, guard := some (Fin.last 64) })))))))))))))

def bytes_l109010 : List UInt8 :=
  [0x4C, 0x33, 0xBC, 0xEC, 0x50, 0x01, 0x00, 0x00, 0x4C, 0x89, 0x7C, 0x24, 0x40, 0xBE, 0x08, 0x00,
    0x00, 0x00, 0x48, 0x8D, 0x5C, 0x24, 0x08, 0x48, 0x89, 0xDF, 0xE8, 0x61, 0x7E, 0xFF, 0xFF]

theorem code_l109010 : ∀ x ∈ codeRange 0x109010 bytes_l109010, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9010 31 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10902f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10902f (movR64R64Effect 0x10902f 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 54) (.exec 0x10902f (fun s => s.RIP = 0x10902f) (movR64R64Effect 0x10902f 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x109032 (callEffect (fun _ => 0x1002a0) 0x109037) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 56) (.exec 0x109032 (PushPre 0x109032 5) (callEffect (fun _ => 0x1002a0) 0x109037) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.const ⟨64, 0x109037⟩) #v[]
    (.terminate (.call ⟨.l1002a0, RegMap.args [(3, 3), (4, 55), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ { target := .l109037, kept := #v[], arity := rfl, guard := some (Fin.last 57) }))))))

def bytes_l10902f : List UInt8 :=
  [0x48, 0x89, 0xDF, 0xE8, 0x69, 0x72, 0xFF, 0xFF]

theorem code_l10902f : ∀ x ∈ codeRange 0x10902f bytes_l10902f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x902f 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109037_1 : Block Op Label signature Reg.count 87 :=
  .letOp (n := 87) (.exec 0x1090b0 (StorePre 0x1090b0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1090b0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1090b0 1 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[85, 4]
    (.letOp (n := 88) (.out 0x1090b5 (movR64M64Effect 0x1090b5 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 89) (.exec 0x1090b5 (LoadPre 0x1090b5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1090b5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1090b5 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 90) (.out 0x1090ba (xorR64M64Effect 0x1090ba 0 (.sib 4 (some 5) 3 (.d32 0x190))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4, .gpr 5] []) (.reg (.gpr 0))) #v[88, 4, 5]
    (.letOp (n := 91) (.exec 0x1090ba (LoadPre 0x1090ba (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x190)) s (0x1090ba + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x1090ba 0 (.sib 4 (some 5) 3 (.d32 0x190))) (Reg.operands [.gpr 0, .gpr 4, .gpr 5] [])) #v[88, 4, 5]
    (.letOp (n := 92) (.exec 0x1090c2 (StorePre 0x1090c2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1090c2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1090c2 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[90, 4]
    (.letOp (n := 93) (.out 0x1090c7 (cmpR64Imm8Effect 0x1090c7 5 0x68) (EffectPart.reads (.flag .ZF) [.gpr 5] []) (.flag .ZF)) #v[5]
    (.letOp (n := 94) (.exec 0x1090c7 (fun s => s.RIP = 0x1090c7) (cmpR64Imm8Effect 0x1090c7 5 0x68) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 95) (.pure (condOp 4)) #v[93]
    (.terminate (.condBr (Fin.last 95) ⟨.l108600, RegMap.args [(0, 90), (1, 85), (2, 80), (3, 3), (4, 4), (5, 5), (6, 75), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (19, 93), (22, 22), (39, 39), (50, 50), (51, 51)] 96⟩ ⟨.l1090d1, RegMap.args [(0, 90), (1, 85), (2, 80), (3, 3), (4, 4), (5, 5), (6, 75), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (19, 93), (22, 22), (39, 39), (50, 50), (51, 51)] 96⟩))))))))))

def bytes_l109037_1 : List UInt8 :=
  [0x48, 0x89, 0x4C, 0x24, 0x38, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48, 0x33, 0x84, 0xEC, 0x90, 0x01,
    0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x40, 0x48, 0x83, 0xFD, 0x68, 0x0F, 0x84, 0x2F, 0xF5, 0xFF,
    0xFF]

theorem code_l109037_1 : ∀ x ∈ codeRange 0x1090b0 bytes_l109037_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x90b0 33 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109037 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x109037 (movR64M64Effect 0x109037 10 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 54) (.exec 0x109037 (LoadPre 0x109037 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109037 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109037 10 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10903c (movR64M64Effect 0x10903c 9 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 56) (.exec 0x10903c (LoadPre 0x10903c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10903c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10903c 9 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x109041 (xorR64M64Effect 0x109041 10 (.sib 4 (some 5) 3 (.d32 0x158))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 4, .gpr 5] []) (.reg (.gpr 10))) #v[53, 4, 5]
    (.letOp (n := 58) (.exec 0x109041 (LoadPre 0x109041 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x158)) s (0x109041 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x109041 10 (.sib 4 (some 5) 3 (.d32 0x158))) (Reg.operands [.gpr 10, .gpr 4, .gpr 5] [])) #v[53, 4, 5]
    (.letOp (n := 59) (.exec 0x109049 (StorePre 0x109049 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109049 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109049 10 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 60) (.out 0x10904e (xorR64M64Effect 0x10904e 9 (.sib 4 (some 5) 3 (.d32 0x160))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 4, .gpr 5] []) (.reg (.gpr 9))) #v[55, 4, 5]
    (.letOp (n := 61) (.exec 0x10904e (LoadPre 0x10904e (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x160)) s (0x10904e + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x10904e 9 (.sib 4 (some 5) 3 (.d32 0x160))) (Reg.operands [.gpr 9, .gpr 4, .gpr 5] [])) #v[55, 4, 5]
    (.letOp (n := 62) (.exec 0x109056 (StorePre 0x109056 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x109056 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109056 9 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[60, 4]
    (.letOp (n := 63) (.out 0x10905b (movR64M64Effect 0x10905b 8 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 64) (.exec 0x10905b (LoadPre 0x10905b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10905b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10905b 8 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x109060 (xorR64M64Effect 0x109060 8 (.sib 4 (some 5) 3 (.d32 0x168))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 4, .gpr 5] []) (.reg (.gpr 8))) #v[63, 4, 5]
    (.letOp (n := 66) (.exec 0x109060 (LoadPre 0x109060 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x168)) s (0x109060 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x109060 8 (.sib 4 (some 5) 3 (.d32 0x168))) (Reg.operands [.gpr 8, .gpr 4, .gpr 5] [])) #v[63, 4, 5]
    (.letOp (n := 67) (.exec 0x109068 (StorePre 0x109068 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x109068 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109068 8 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x10906d (movR64M64Effect 0x10906d 7 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 69) (.exec 0x10906d (LoadPre 0x10906d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10906d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10906d 7 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.out 0x109072 (xorR64M64Effect 0x109072 7 (.sib 4 (some 5) 3 (.d32 0x170))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 4, .gpr 5] []) (.reg (.gpr 7))) #v[68, 4, 5]
    (.letOp (n := 71) (.exec 0x109072 (LoadPre 0x109072 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x170)) s (0x109072 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x109072 7 (.sib 4 (some 5) 3 (.d32 0x170))) (Reg.operands [.gpr 7, .gpr 4, .gpr 5] [])) #v[68, 4, 5]
    (.letOp (n := 72) (.exec 0x10907a (StorePre 0x10907a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10907a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10907a 7 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[70, 4]
    (.letOp (n := 73) (.out 0x10907f (movR64M64Effect 0x10907f 6 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 74) (.exec 0x10907f (LoadPre 0x10907f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10907f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10907f 6 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.out 0x109084 (xorR64M64Effect 0x109084 6 (.sib 4 (some 5) 3 (.d32 0x178))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 4, .gpr 5] []) (.reg (.gpr 6))) #v[73, 4, 5]
    (.letOp (n := 76) (.exec 0x109084 (LoadPre 0x109084 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x178)) s (0x109084 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x109084 6 (.sib 4 (some 5) 3 (.d32 0x178))) (Reg.operands [.gpr 6, .gpr 4, .gpr 5] [])) #v[73, 4, 5]
    (.letOp (n := 77) (.exec 0x10908c (StorePre 0x10908c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10908c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10908c 6 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[75, 4]
    (.letOp (n := 78) (.out 0x109091 (movR64M64Effect 0x109091 2 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 79) (.exec 0x109091 (LoadPre 0x109091 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x109091 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109091 2 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 80) (.out 0x109096 (xorR64M64Effect 0x109096 2 (.sib 4 (some 5) 3 (.d32 0x180))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 4, .gpr 5] []) (.reg (.gpr 2))) #v[78, 4, 5]
    (.letOp (n := 81) (.exec 0x109096 (LoadPre 0x109096 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x180)) s (0x109096 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x109096 2 (.sib 4 (some 5) 3 (.d32 0x180))) (Reg.operands [.gpr 2, .gpr 4, .gpr 5] [])) #v[78, 4, 5]
    (.letOp (n := 82) (.exec 0x10909e (StorePre 0x10909e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10909e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10909e 2 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[80, 4]
    (.letOp (n := 83) (.out 0x1090a3 (movR64M64Effect 0x1090a3 1 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 84) (.exec 0x1090a3 (LoadPre 0x1090a3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1090a3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1090a3 1 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 85) (.out 0x1090a8 (xorR64M64Effect 0x1090a8 1 (.sib 4 (some 5) 3 (.d32 0x188))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 4, .gpr 5] []) (.reg (.gpr 1))) #v[83, 4, 5]
    (.letOp (n := 86) (.exec 0x1090a8 (LoadPre 0x1090a8 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x188)) s (0x1090a8 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x1090a8 1 (.sib 4 (some 5) 3 (.d32 0x188))) (Reg.operands [.gpr 1, .gpr 4, .gpr 5] [])) #v[83, 4, 5]
    (b_l109037_1))))))))))))))))))))))))))))))))))

def bytes_l109037 : List UInt8 :=
  [0x4C, 0x8B, 0x54, 0x24, 0x08, 0x4C, 0x8B, 0x4C, 0x24, 0x10, 0x4C, 0x33, 0x94, 0xEC, 0x58, 0x01,
    0x00, 0x00, 0x4C, 0x89, 0x54, 0x24, 0x08, 0x4C, 0x33, 0x8C, 0xEC, 0x60, 0x01, 0x00, 0x00, 0x4C,
    0x89, 0x4C, 0x24, 0x10, 0x4C, 0x8B, 0x44, 0x24, 0x18, 0x4C, 0x33, 0x84, 0xEC, 0x68, 0x01, 0x00,
    0x00, 0x4C, 0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x7C, 0x24, 0x20, 0x48, 0x33, 0xBC, 0xEC, 0x70,
    0x01, 0x00, 0x00, 0x48, 0x89, 0x7C, 0x24, 0x20, 0x48, 0x8B, 0x74, 0x24, 0x28, 0x48, 0x33, 0xB4,
    0xEC, 0x78, 0x01, 0x00, 0x00, 0x48, 0x89, 0x74, 0x24, 0x28, 0x48, 0x8B, 0x54, 0x24, 0x30, 0x48,
    0x33, 0x94, 0xEC, 0x80, 0x01, 0x00, 0x00, 0x48, 0x89, 0x54, 0x24, 0x30, 0x48, 0x8B, 0x4C, 0x24,
    0x38, 0x48, 0x33, 0x8C, 0xEC, 0x88, 0x01, 0x00, 0x00] ++ bytes_l109037_1

theorem code_l109037 : ∀ x ∈ codeRange 0x109037 bytes_l109037, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x9037 121 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l109037_1

@[cfg_block] def b_l1090d1 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1090d1 (movR32Imm32Effect 0x1090d1 5 6 0x8) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 54) (.exec 0x1090d1 (fun s => s.RIP = 0x1090d1) (movR32Imm32Effect 0x1090d1 5 6 0x8) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x1090d6 (leaR64Effect 0x1090d6 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 56) (.exec 0x1090d6 (fun s => s.RIP = 0x1090d6) (leaR64Effect 0x1090d6 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1090db (callEffect (fun _ => 0x100e90) 0x1090e0) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x1090db (PushPre 0x1090db 5) (callEffect (fun _ => 0x100e90) 0x1090e0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x1090e0⟩) #v[]
    (.terminate (.call ⟨.l100e90, RegMap.args [(3, 3), (4, 57), (5, 5), (6, 53), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ { target := .l1090e0, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l1090d1 : List UInt8 :=
  [0xBE, 0x08, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x7C, 0x24, 0x08, 0xE8, 0xB0, 0x7D, 0xFF, 0xFF]

theorem code_l1090d1 : ∀ x ∈ codeRange 0x1090d1 bytes_l1090d1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x90d1 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1090e0_6 : Block Op Label signature Reg.count 283 :=
  .letOp (n := 283) (.out 0x1092d8 (movR64M64Effect 0x1092d8 2 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 284) (.exec 0x1092d8 (LoadPre 0x1092d8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1092d8 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1092d8 2 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 285) (.out 0x1092e0 (xorR64R64Effect 0x1092e0 2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 13] []) (.reg (.gpr 2))) #v[283, 167]
    (.letOp (n := 286) (.exec 0x1092e0 (fun s => s.RIP = 0x1092e0) (xorR64R64Effect 0x1092e0 2 13) (Reg.operands [.gpr 2, .gpr 13] [])) #v[283, 167]
    (.letOp (n := 287) (.out 0x1092e3 (xorR64R64Effect 0x1092e3 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 13] []) (.reg (.gpr 6))) #v[272, 167]
    (.letOp (n := 288) (.exec 0x1092e3 (fun s => s.RIP = 0x1092e3) (xorR64R64Effect 0x1092e3 6 13) (Reg.operands [.gpr 6, .gpr 13] [])) #v[272, 167]
    (.letOp (n := 289) (.out 0x1092e6 (movR64R64Effect 0x1092e6 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[285]
    (.letOp (n := 290) (.exec 0x1092e6 (fun s => s.RIP = 0x1092e6) (movR64R64Effect 0x1092e6 0 2) (Reg.operands [.gpr 2] [])) #v[285]
    (.letOp (n := 291) (.out 0x1092e9 (rolR64Effect 0x1092e9 4 0 32) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[289]
    (.letOp (n := 292) (.exec 0x1092e9 (fun s => s.RIP = 0x1092e9) (rolR64Effect 0x1092e9 4 0 32) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[289]
    (.letOp (n := 293) (.out 0x1092ed (xorR64M64Effect 0x1092ed 0 (.sib 4 (some 5) 3 (.d32 0x1c8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4, .gpr 5] []) (.reg (.gpr 0))) #v[291, 4, 5]
    (.letOp (n := 294) (.exec 0x1092ed (LoadPre 0x1092ed (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x1c8)) s (0x1092ed + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x1092ed 0 (.sib 4 (some 5) 3 (.d32 0x1c8))) (Reg.operands [.gpr 0, .gpr 4, .gpr 5] [])) #v[291, 4, 5]
    (.letOp (n := 295) (.out 0x1092f5 (xorR64R64Effect 0x1092f5 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[287, 293]
    (.letOp (n := 296) (.exec 0x1092f5 (fun s => s.RIP = 0x1092f5) (xorR64R64Effect 0x1092f5 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[287, 293]
    (.letOp (n := 297) (.exec 0x1092f8 (StorePre 0x1092f8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1092f8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1092f8 6 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[295, 4]
    (.letOp (n := 298) (.out 0x1092fd (xorR64R64Effect 0x1092fd 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[285, 187]
    (.letOp (n := 299) (.exec 0x1092fd (fun s => s.RIP = 0x1092fd) (xorR64R64Effect 0x1092fd 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[285, 187]
    (.letOp (n := 300) (.out 0x109300 (rolR64Effect 0x109300 4 14 32) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[191]
    (.letOp (n := 301) (.exec 0x109300 (fun s => s.RIP = 0x109300) (rolR64Effect 0x109300 4 14 32) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[191]
    (.letOp (n := 302) (.out 0x109304 (xorR64M64Effect 0x109304 14 (.sib 4 (some 5) 3 (.d32 0x1d0))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 4, .gpr 5] []) (.reg (.gpr 14))) #v[300, 4, 5]
    (.letOp (n := 303) (.exec 0x109304 (LoadPre 0x109304 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x1d0)) s (0x109304 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x109304 14 (.sib 4 (some 5) 3 (.d32 0x1d0))) (Reg.operands [.gpr 14, .gpr 4, .gpr 5] [])) #v[300, 4, 5]
    (.letOp (n := 304) (.out 0x10930c (xorR64R64Effect 0x10930c 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 14] []) (.reg (.gpr 2))) #v[298, 302]
    (.letOp (n := 305) (.exec 0x10930c (fun s => s.RIP = 0x10930c) (xorR64R64Effect 0x10930c 2 14) (Reg.operands [.gpr 2, .gpr 14] [])) #v[298, 302]
    (.letOp (n := 306) (.exec 0x10930f (StorePre 0x10930f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10930f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10930f 2 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[304, 4]
    (.letOp (n := 307) (.out 0x109314 (movR32Imm32Effect 0x109314 5 6 0x8) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 308) (.exec 0x109314 (fun s => s.RIP = 0x109314) (movR32Imm32Effect 0x109314 5 6 0x8) (Reg.operands [] [])) #v[]
    (.letOp (n := 309) (.out 0x109319 (leaR64Effect 0x109319 3 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 310) (.exec 0x109319 (fun s => s.RIP = 0x109319) (leaR64Effect 0x109319 3 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 311) (.out 0x10931e (movR64R64Effect 0x10931e 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[309]
    (.letOp (n := 312) (.exec 0x10931e (fun s => s.RIP = 0x10931e) (movR64R64Effect 0x10931e 7 3) (Reg.operands [.gpr 3] [])) #v[309]
    (.letOp (n := 313) (.out 0x109321 (callEffect (fun _ => 0x100e90) 0x109326) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 314) (.exec 0x109321 (PushPre 0x109321 5) (callEffect (fun _ => 0x100e90) 0x109326) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 315) (.const ⟨64, 0x109326⟩) #v[]
    (.terminate (.call ⟨.l100e90, RegMap.args [(0, 293), (1, 187), (2, 304), (3, 309), (4, 313), (5, 5), (6, 307), (7, 311), (8, 280), (9, 201), (10, 197), (11, 229), (12, 183), (13, 167), (14, 302), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)] 316⟩ { target := .l109326, kept := #v[], arity := rfl, guard := some (Fin.last 315) }))))))))))))))))))))))))))))))))))

def bytes_l1090e0_6 : List UInt8 :=
  [0x48, 0x8B, 0x94, 0x24, 0x80, 0x00, 0x00, 0x00, 0x4C, 0x31, 0xEA, 0x4C, 0x31, 0xEE, 0x48, 0x89,
    0xD0, 0x48, 0xC1, 0xC0, 0x20, 0x48, 0x33, 0x84, 0xEC, 0xC8, 0x01, 0x00, 0x00, 0x48, 0x31, 0xC6,
    0x48, 0x89, 0x74, 0x24, 0x38, 0x48, 0x31, 0xCA, 0x49, 0xC1, 0xC6, 0x20, 0x4C, 0x33, 0xB4, 0xEC,
    0xD0, 0x01, 0x00, 0x00, 0x4C, 0x31, 0xF2, 0x48, 0x89, 0x54, 0x24, 0x40, 0xBE, 0x08, 0x00, 0x00,
    0x00, 0x48, 0x8D, 0x5C, 0x24, 0x08, 0x48, 0x89, 0xDF, 0xE8, 0x6A, 0x7B, 0xFF, 0xFF]

theorem code_l1090e0_6 : ∀ x ∈ codeRange 0x1092d8 bytes_l1090e0_6, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x92d8 78 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1090e0_5 : Block Op Label signature Reg.count 246 :=
  .letOp (n := 246) (.out 0x10927e (movR64M64Effect 0x10927e 8 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 247) (.exec 0x10927e (LoadPre 0x10927e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10927e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10927e 8 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 248) (.out 0x109286 (xorR64R64Effect 0x109286 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2] []) (.reg (.gpr 8))) #v[246, 138]
    (.letOp (n := 249) (.exec 0x109286 (fun s => s.RIP = 0x109286) (xorR64R64Effect 0x109286 8 2) (Reg.operands [.gpr 8, .gpr 2] [])) #v[246, 138]
    (.letOp (n := 250) (.exec 0x109289 (StorePre 0x109289 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x109289 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109289 7 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[244, 4]
    (.letOp (n := 251) (.out 0x10928e (movR64R64Effect 0x10928e 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[248]
    (.letOp (n := 252) (.exec 0x10928e (fun s => s.RIP = 0x10928e) (movR64R64Effect 0x10928e 0 8) (Reg.operands [.gpr 8] [])) #v[248]
    (.letOp (n := 253) (.out 0x109291 (rolR64Effect 0x109291 4 0 32) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[251]
    (.letOp (n := 254) (.exec 0x109291 (fun s => s.RIP = 0x109291) (rolR64Effect 0x109291 4 0 32) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[251]
    (.letOp (n := 255) (.out 0x109295 (xorR64R64Effect 0x109295 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[231, 138]
    (.letOp (n := 256) (.exec 0x109295 (fun s => s.RIP = 0x109295) (xorR64R64Effect 0x109295 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[231, 138]
    (.letOp (n := 257) (.out 0x109298 (xorR64M64Effect 0x109298 0 (.sib 4 (some 5) 3 (.d32 0x1b8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4, .gpr 5] []) (.reg (.gpr 0))) #v[253, 4, 5]
    (.letOp (n := 258) (.exec 0x109298 (LoadPre 0x109298 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x1b8)) s (0x109298 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x109298 0 (.sib 4 (some 5) 3 (.d32 0x1b8))) (Reg.operands [.gpr 0, .gpr 4, .gpr 5] [])) #v[253, 4, 5]
    (.letOp (n := 259) (.out 0x1092a0 (xorR64R64Effect 0x1092a0 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 14] []) (.reg (.gpr 6))) #v[255, 191]
    (.letOp (n := 260) (.exec 0x1092a0 (fun s => s.RIP = 0x1092a0) (xorR64R64Effect 0x1092a0 6 14) (Reg.operands [.gpr 6, .gpr 14] [])) #v[255, 191]
    (.letOp (n := 261) (.out 0x1092a3 (xorR64R64Effect 0x1092a3 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[259, 257]
    (.letOp (n := 262) (.exec 0x1092a3 (fun s => s.RIP = 0x1092a3) (xorR64R64Effect 0x1092a3 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[259, 257]
    (.letOp (n := 263) (.out 0x1092a6 (movR64M64Effect 0x1092a6 2 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 264) (.exec 0x1092a6 (LoadPre 0x1092a6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1092a6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1092a6 2 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 265) (.out 0x1092ab (movR64M64Effect 0x1092ab 7 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 266) (.exec 0x1092ab (LoadPre 0x1092ab (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x1092ab + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1092ab 7 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 267) (.out 0x1092b3 (xorR64R64Effect 0x1092b3 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 7] []) (.reg (.gpr 2))) #v[263, 265]
    (.letOp (n := 268) (.exec 0x1092b3 (fun s => s.RIP = 0x1092b3) (xorR64R64Effect 0x1092b3 2 7) (Reg.operands [.gpr 2, .gpr 7] [])) #v[263, 265]
    (.letOp (n := 269) (.exec 0x1092b6 (StorePre 0x1092b6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1092b6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1092b6 6 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[261, 4]
    (.letOp (n := 270) (.out 0x1092bb (movR64R64Effect 0x1092bb 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[267]
    (.letOp (n := 271) (.exec 0x1092bb (fun s => s.RIP = 0x1092bb) (movR64R64Effect 0x1092bb 0 2) (Reg.operands [.gpr 2] [])) #v[267]
    (.letOp (n := 272) (.out 0x1092be (movR64R64Effect 0x1092be 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[267]
    (.letOp (n := 273) (.exec 0x1092be (fun s => s.RIP = 0x1092be) (movR64R64Effect 0x1092be 6 2) (Reg.operands [.gpr 2] [])) #v[267]
    (.letOp (n := 274) (.out 0x1092c1 (rolR64Effect 0x1092c1 4 0 32) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[270]
    (.letOp (n := 275) (.exec 0x1092c1 (fun s => s.RIP = 0x1092c1) (rolR64Effect 0x1092c1 4 0 32) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[270]
    (.letOp (n := 276) (.out 0x1092c5 (xorR64M64Effect 0x1092c5 0 (.sib 4 (some 5) 3 (.d32 0x1c0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4, .gpr 5] []) (.reg (.gpr 0))) #v[274, 4, 5]
    (.letOp (n := 277) (.exec 0x1092c5 (LoadPre 0x1092c5 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x1c0)) s (0x1092c5 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x1092c5 0 (.sib 4 (some 5) 3 (.d32 0x1c0))) (Reg.operands [.gpr 0, .gpr 4, .gpr 5] [])) #v[274, 4, 5]
    (.letOp (n := 278) (.out 0x1092cd (xorR64R64Effect 0x1092cd 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 7] []) (.reg (.gpr 8))) #v[248, 265]
    (.letOp (n := 279) (.exec 0x1092cd (fun s => s.RIP = 0x1092cd) (xorR64R64Effect 0x1092cd 8 7) (Reg.operands [.gpr 8, .gpr 7] [])) #v[248, 265]
    (.letOp (n := 280) (.out 0x1092d0 (xorR64R64Effect 0x1092d0 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[278, 276]
    (.letOp (n := 281) (.exec 0x1092d0 (fun s => s.RIP = 0x1092d0) (xorR64R64Effect 0x1092d0 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[278, 276]
    (.letOp (n := 282) (.exec 0x1092d3 (StorePre 0x1092d3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1092d3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1092d3 8 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[280, 4]
    (b_l1090e0_6)))))))))))))))))))))))))))))))))))))

def bytes_l1090e0_5 : List UInt8 :=
  [0x4C, 0x8B, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, 0x49, 0x31, 0xD0, 0x48, 0x89, 0x7C, 0x24, 0x20,
    0x4C, 0x89, 0xC0, 0x48, 0xC1, 0xC0, 0x20, 0x48, 0x31, 0xD6, 0x48, 0x33, 0x84, 0xEC, 0xB8, 0x01,
    0x00, 0x00, 0x4C, 0x31, 0xF6, 0x48, 0x31, 0xC6, 0x48, 0x8B, 0x54, 0x24, 0x78, 0x48, 0x8B, 0xBC,
    0x24, 0x90, 0x00, 0x00, 0x00, 0x48, 0x31, 0xFA, 0x48, 0x89, 0x74, 0x24, 0x28, 0x48, 0x89, 0xD0,
    0x48, 0x89, 0xD6, 0x48, 0xC1, 0xC0, 0x20, 0x48, 0x33, 0x84, 0xEC, 0xC0, 0x01, 0x00, 0x00, 0x49,
    0x31, 0xF8, 0x49, 0x31, 0xC0, 0x4C, 0x89, 0x44, 0x24, 0x30] ++ bytes_l1090e0_6

theorem code_l1090e0_5 : ∀ x ∈ codeRange 0x10927e bytes_l1090e0_5, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x927e 90 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1090e0_6

@[cfg_block] def b_l1090e0_4 : Block Op Label signature Reg.count 208 :=
  .letOp (n := 208) (.out 0x10922c (movR64R64Effect 0x10922c 8 11) (EffectPart.reads (.reg (.gpr 8)) [.gpr 11] []) (.reg (.gpr 8))) #v[204]
    (.letOp (n := 209) (.exec 0x10922c (fun s => s.RIP = 0x10922c) (movR64R64Effect 0x10922c 8 11) (Reg.operands [.gpr 11] [])) #v[204]
    (.letOp (n := 210) (.out 0x10922f (rolR64Effect 0x10922f 4 8 32) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[208]
    (.letOp (n := 211) (.exec 0x10922f (fun s => s.RIP = 0x10922f) (rolR64Effect 0x10922f 4 8 32) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[208]
    (.letOp (n := 212) (.out 0x109233 (xorR64M64Effect 0x109233 8 (.sib 4 (some 5) 3 (.d32 0x1a0))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 4, .gpr 5] []) (.reg (.gpr 8))) #v[210, 4, 5]
    (.letOp (n := 213) (.exec 0x109233 (LoadPre 0x109233 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x1a0)) s (0x109233 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x109233 8 (.sib 4 (some 5) 3 (.d32 0x1a0))) (Reg.operands [.gpr 8, .gpr 4, .gpr 5] [])) #v[210, 4, 5]
    (.letOp (n := 214) (.out 0x10923b (xorR64R64Effect 0x10923b 3 14) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 14] []) (.reg (.gpr 3))) #v[206, 191]
    (.letOp (n := 215) (.exec 0x10923b (fun s => s.RIP = 0x10923b) (xorR64R64Effect 0x10923b 3 14) (Reg.operands [.gpr 3, .gpr 14] [])) #v[206, 191]
    (.letOp (n := 216) (.out 0x10923e (xorR64R64Effect 0x10923e 3 8) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 8] []) (.reg (.gpr 3))) #v[214, 212]
    (.letOp (n := 217) (.exec 0x10923e (fun s => s.RIP = 0x10923e) (xorR64R64Effect 0x10923e 3 8) (Reg.operands [.gpr 3, .gpr 8] [])) #v[214, 212]
    (.letOp (n := 218) (.exec 0x109241 (StorePre 0x109241 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x109241 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109241 3 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[216, 4]
    (.letOp (n := 219) (.out 0x109246 (xorR64R64Effect 0x109246 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[57, 111]
    (.letOp (n := 220) (.exec 0x109246 (fun s => s.RIP = 0x109246) (xorR64R64Effect 0x109246 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[57, 111]
    (.letOp (n := 221) (.out 0x109249 (xorR64R64Effect 0x109249 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0] []) (.reg (.gpr 11))) #v[204, 111]
    (.letOp (n := 222) (.exec 0x109249 (fun s => s.RIP = 0x109249) (xorR64R64Effect 0x109249 11 0) (Reg.operands [.gpr 11, .gpr 0] [])) #v[204, 111]
    (.letOp (n := 223) (.out 0x10924c (movR64R64Effect 0x10924c 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[219]
    (.letOp (n := 224) (.exec 0x10924c (fun s => s.RIP = 0x10924c) (movR64R64Effect 0x10924c 0 7) (Reg.operands [.gpr 7] [])) #v[219]
    (.letOp (n := 225) (.out 0x10924f (rolR64Effect 0x10924f 4 0 32) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[223]
    (.letOp (n := 226) (.exec 0x10924f (fun s => s.RIP = 0x10924f) (rolR64Effect 0x10924f 4 0 32) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[223]
    (.letOp (n := 227) (.out 0x109253 (xorR64M64Effect 0x109253 0 (.sib 4 (some 5) 3 (.d32 0x1a8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4, .gpr 5] []) (.reg (.gpr 0))) #v[225, 4, 5]
    (.letOp (n := 228) (.exec 0x109253 (LoadPre 0x109253 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x1a8)) s (0x109253 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x109253 0 (.sib 4 (some 5) 3 (.d32 0x1a8))) (Reg.operands [.gpr 0, .gpr 4, .gpr 5] [])) #v[225, 4, 5]
    (.letOp (n := 229) (.out 0x10925b (xorR64R64Effect 0x10925b 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0] []) (.reg (.gpr 11))) #v[221, 227]
    (.letOp (n := 230) (.exec 0x10925b (fun s => s.RIP = 0x10925b) (xorR64R64Effect 0x10925b 11 0) (Reg.operands [.gpr 11, .gpr 0] [])) #v[221, 227]
    (.letOp (n := 231) (.out 0x10925e (xorR64R64Effect 0x10925e 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 15] []) (.reg (.gpr 6))) #v[59, 125]
    (.letOp (n := 232) (.exec 0x10925e (fun s => s.RIP = 0x10925e) (xorR64R64Effect 0x10925e 6 15) (Reg.operands [.gpr 6, .gpr 15] [])) #v[59, 125]
    (.letOp (n := 233) (.exec 0x109261 (StorePre 0x109261 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x109261 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109261 11 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[229, 4]
    (.letOp (n := 234) (.out 0x109266 (movR64R64Effect 0x109266 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[231]
    (.letOp (n := 235) (.exec 0x109266 (fun s => s.RIP = 0x109266) (movR64R64Effect 0x109266 0 6) (Reg.operands [.gpr 6] [])) #v[231]
    (.letOp (n := 236) (.out 0x109269 (rolR64Effect 0x109269 4 0 32) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[234]
    (.letOp (n := 237) (.exec 0x109269 (fun s => s.RIP = 0x109269) (rolR64Effect 0x109269 4 0 32) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[234]
    (.letOp (n := 238) (.out 0x10926d (xorR64M64Effect 0x10926d 0 (.sib 4 (some 5) 3 (.d32 0x1b0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4, .gpr 5] []) (.reg (.gpr 0))) #v[236, 4, 5]
    (.letOp (n := 239) (.exec 0x10926d (LoadPre 0x10926d (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x1b0)) s (0x10926d + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x10926d 0 (.sib 4 (some 5) 3 (.d32 0x1b0))) (Reg.operands [.gpr 0, .gpr 4, .gpr 5] [])) #v[236, 4, 5]
    (.letOp (n := 240) (.out 0x109275 (xorR64R64Effect 0x109275 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 15] []) (.reg (.gpr 7))) #v[219, 125]
    (.letOp (n := 241) (.exec 0x109275 (fun s => s.RIP = 0x109275) (xorR64R64Effect 0x109275 7 15) (Reg.operands [.gpr 7, .gpr 15] [])) #v[219, 125]
    (.letOp (n := 242) (.out 0x109278 (xorR64R64Effect 0x109278 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 14] []) (.reg (.gpr 7))) #v[240, 191]
    (.letOp (n := 243) (.exec 0x109278 (fun s => s.RIP = 0x109278) (xorR64R64Effect 0x109278 7 14) (Reg.operands [.gpr 7, .gpr 14] [])) #v[240, 191]
    (.letOp (n := 244) (.out 0x10927b (xorR64R64Effect 0x10927b 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[242, 238]
    (.letOp (n := 245) (.exec 0x10927b (fun s => s.RIP = 0x10927b) (xorR64R64Effect 0x10927b 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[242, 238]
    (b_l1090e0_5))))))))))))))))))))))))))))))))))))))

def bytes_l1090e0_4 : List UInt8 :=
  [0x4D, 0x89, 0xD8, 0x49, 0xC1, 0xC0, 0x20, 0x4C, 0x33, 0x84, 0xEC, 0xA0, 0x01, 0x00, 0x00, 0x4C,
    0x31, 0xF3, 0x4C, 0x31, 0xC3, 0x48, 0x89, 0x5C, 0x24, 0x10, 0x48, 0x31, 0xC7, 0x49, 0x31, 0xC3,
    0x48, 0x89, 0xF8, 0x48, 0xC1, 0xC0, 0x20, 0x48, 0x33, 0x84, 0xEC, 0xA8, 0x01, 0x00, 0x00, 0x49,
    0x31, 0xC3, 0x4C, 0x31, 0xFE, 0x4C, 0x89, 0x5C, 0x24, 0x18, 0x48, 0x89, 0xF0, 0x48, 0xC1, 0xC0,
    0x20, 0x48, 0x33, 0x84, 0xEC, 0xB0, 0x01, 0x00, 0x00, 0x4C, 0x31, 0xFF, 0x4C, 0x31, 0xF7, 0x48,
    0x31, 0xC7] ++ bytes_l1090e0_5

theorem code_l1090e0_4 : ∀ x ∈ codeRange 0x10922c bytes_l1090e0_4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x922c 82 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1090e0_5

@[cfg_block] def b_l1090e0_3 : Block Op Label signature Reg.count 169 :=
  .letOp (n := 169) (.out 0x1091d6 (movR64M64Effect 0x1091d6 14 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 170) (.exec 0x1091d6 (LoadPre 0x1091d6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1091d6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1091d6 14 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 171) (.out 0x1091db (movR64R64Effect 0x1091db 10 14) (EffectPart.reads (.reg (.gpr 10)) [.gpr 14] []) (.reg (.gpr 10))) #v[169]
    (.letOp (n := 172) (.exec 0x1091db (fun s => s.RIP = 0x1091db) (movR64R64Effect 0x1091db 10 14) (Reg.operands [.gpr 14] [])) #v[169]
    (.letOp (n := 173) (.out 0x1091de (rolR64Effect 0x1091de 4 10 40) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[171]
    (.letOp (n := 174) (.exec 0x1091de (fun s => s.RIP = 0x1091de) (rolR64Effect 0x1091de 4 10 40) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[171]
    (.letOp (n := 175) (.out 0x1091e2 (movR64Imm64Effect 0x1091e2 1 0xff00ff00ff00ff) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 176) (.exec 0x1091e2 (fun s => s.RIP = 0x1091e2) (movR64Imm64Effect 0x1091e2 1 0xff00ff00ff00ff) (Reg.operands [] [])) #v[]
    (.letOp (n := 177) (.out 0x1091ec (andR64R64Effect 0x1091ec 10 1) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 1] []) (.reg (.gpr 10))) #v[173, 175]
    (.letOp (n := 178) (.exec 0x1091ec (fun s => s.RIP = 0x1091ec) (andR64R64Effect 0x1091ec 10 1) (Reg.operands [.gpr 10, .gpr 1] [])) #v[173, 175]
    (.letOp (n := 179) (.out 0x1091ef (movR64R64Effect 0x1091ef 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[169]
    (.letOp (n := 180) (.exec 0x1091ef (fun s => s.RIP = 0x1091ef) (movR64R64Effect 0x1091ef 1 14) (Reg.operands [.gpr 14] [])) #v[169]
    (.letOp (n := 181) (.out 0x1091f2 (rolR64Effect 0x1091f2 4 1 56) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[179]
    (.letOp (n := 182) (.exec 0x1091f2 (fun s => s.RIP = 0x1091f2) (rolR64Effect 0x1091f2 4 1 56) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[179]
    (.letOp (n := 183) (.out 0x1091f6 (movR64Imm64Effect 0x1091f6 12 0xff00ff00ff00ff00) (EffectPart.reads (.reg (.gpr 12)) [] []) (.reg (.gpr 12))) #v[]
    (.letOp (n := 184) (.exec 0x1091f6 (fun s => s.RIP = 0x1091f6) (movR64Imm64Effect 0x1091f6 12 0xff00ff00ff00ff00) (Reg.operands [] [])) #v[]
    (.letOp (n := 185) (.out 0x109200 (andR64R64Effect 0x109200 1 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 12] []) (.reg (.gpr 1))) #v[181, 183]
    (.letOp (n := 186) (.exec 0x109200 (fun s => s.RIP = 0x109200) (andR64R64Effect 0x109200 1 12) (Reg.operands [.gpr 1, .gpr 12] [])) #v[181, 183]
    (.letOp (n := 187) (.out 0x109203 (orR64R64Effect 0x109203 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10] []) (.reg (.gpr 1))) #v[185, 177]
    (.letOp (n := 188) (.exec 0x109203 (fun s => s.RIP = 0x109203) (orR64R64Effect 0x109203 1 10) (Reg.operands [.gpr 1, .gpr 10] [])) #v[185, 177]
    (.letOp (n := 189) (.out 0x109206 (xorR64R64Effect 0x109206 3 9) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 9] []) (.reg (.gpr 3))) #v[53, 83]
    (.letOp (n := 190) (.exec 0x109206 (fun s => s.RIP = 0x109206) (xorR64R64Effect 0x109206 3 9) (Reg.operands [.gpr 3, .gpr 9] [])) #v[53, 83]
    (.letOp (n := 191) (.out 0x109209 (xorR64R64Effect 0x109209 14 1) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 1] []) (.reg (.gpr 14))) #v[169, 187]
    (.letOp (n := 192) (.exec 0x109209 (fun s => s.RIP = 0x109209) (xorR64R64Effect 0x109209 14 1) (Reg.operands [.gpr 14, .gpr 1] [])) #v[169, 187]
    (.letOp (n := 193) (.out 0x10920c (movR64R64Effect 0x10920c 10 3) (EffectPart.reads (.reg (.gpr 10)) [.gpr 3] []) (.reg (.gpr 10))) #v[189]
    (.letOp (n := 194) (.exec 0x10920c (fun s => s.RIP = 0x10920c) (movR64R64Effect 0x10920c 10 3) (Reg.operands [.gpr 3] [])) #v[189]
    (.letOp (n := 195) (.out 0x10920f (rolR64Effect 0x10920f 4 10 32) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[193]
    (.letOp (n := 196) (.exec 0x10920f (fun s => s.RIP = 0x10920f) (rolR64Effect 0x10920f 4 10 32) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[193]
    (.letOp (n := 197) (.out 0x109213 (xorR64M64Effect 0x109213 10 (.sib 4 (some 5) 3 (.d32 0x198))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 4, .gpr 5] []) (.reg (.gpr 10))) #v[195, 4, 5]
    (.letOp (n := 198) (.exec 0x109213 (LoadPre 0x109213 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x198)) s (0x109213 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x109213 10 (.sib 4 (some 5) 3 (.d32 0x198))) (Reg.operands [.gpr 10, .gpr 4, .gpr 5] [])) #v[195, 4, 5]
    (.letOp (n := 199) (.out 0x10921b (xorR64R64Effect 0x10921b 9 14) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 14] []) (.reg (.gpr 9))) #v[83, 191]
    (.letOp (n := 200) (.exec 0x10921b (fun s => s.RIP = 0x10921b) (xorR64R64Effect 0x10921b 9 14) (Reg.operands [.gpr 9, .gpr 14] [])) #v[83, 191]
    (.letOp (n := 201) (.out 0x10921e (xorR64R64Effect 0x10921e 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[199, 197]
    (.letOp (n := 202) (.exec 0x10921e (fun s => s.RIP = 0x10921e) (xorR64R64Effect 0x10921e 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[199, 197]
    (.letOp (n := 203) (.exec 0x109221 (StorePre 0x109221 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109221 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109221 9 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[201, 4]
    (.letOp (n := 204) (.out 0x109226 (xorR64R64Effect 0x109226 11 8) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 8] []) (.reg (.gpr 11))) #v[55, 101]
    (.letOp (n := 205) (.exec 0x109226 (fun s => s.RIP = 0x109226) (xorR64R64Effect 0x109226 11 8) (Reg.operands [.gpr 11, .gpr 8] [])) #v[55, 101]
    (.letOp (n := 206) (.out 0x109229 (xorR64R64Effect 0x109229 3 8) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 8] []) (.reg (.gpr 3))) #v[189, 101]
    (.letOp (n := 207) (.exec 0x109229 (fun s => s.RIP = 0x109229) (xorR64R64Effect 0x109229 3 8) (Reg.operands [.gpr 3, .gpr 8] [])) #v[189, 101]
    (b_l1090e0_4)))))))))))))))))))))))))))))))))))))))

def bytes_l1090e0_3 : List UInt8 :=
  [0x4C, 0x8B, 0x74, 0x24, 0x40, 0x4D, 0x89, 0xF2, 0x49, 0xC1, 0xC2, 0x28, 0x48, 0xB9, 0xFF, 0x00,
    0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0x49, 0x21, 0xCA, 0x4C, 0x89, 0xF1, 0x48, 0xC1, 0xC1, 0x38,
    0x49, 0xBC, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x4C, 0x21, 0xE1, 0x4C, 0x09, 0xD1,
    0x4C, 0x31, 0xCB, 0x49, 0x31, 0xCE, 0x49, 0x89, 0xDA, 0x49, 0xC1, 0xC2, 0x20, 0x4C, 0x33, 0x94,
    0xEC, 0x98, 0x01, 0x00, 0x00, 0x4D, 0x31, 0xF1, 0x4D, 0x31, 0xD1, 0x4C, 0x89, 0x4C, 0x24, 0x08,
    0x4D, 0x31, 0xC3, 0x4C, 0x31, 0xC3] ++ bytes_l1090e0_4

theorem code_l1090e0_3 : ∀ x ∈ codeRange 0x1091d6 bytes_l1090e0_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x91d6 86 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1090e0_4

@[cfg_block] def b_l1090e0_2 : Block Op Label signature Reg.count 132 :=
  .letOp (n := 132) (.out 0x109182 (andR64R64Effect 0x109182 10 13) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 13] []) (.reg (.gpr 10))) #v[130, 71]
    (.letOp (n := 133) (.exec 0x109182 (fun s => s.RIP = 0x109182) (andR64R64Effect 0x109182 10 13) (Reg.operands [.gpr 10, .gpr 13] [])) #v[130, 71]
    (.letOp (n := 134) (.out 0x109185 (rolR64Effect 0x109185 4 2 56) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[127]
    (.letOp (n := 135) (.exec 0x109185 (fun s => s.RIP = 0x109185) (rolR64Effect 0x109185 4 2 56) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[127]
    (.letOp (n := 136) (.out 0x109189 (andR64R64Effect 0x109189 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[134, 79]
    (.letOp (n := 137) (.exec 0x109189 (fun s => s.RIP = 0x109189) (andR64R64Effect 0x109189 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[134, 79]
    (.letOp (n := 138) (.out 0x10918c (orR64R64Effect 0x10918c 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 10] []) (.reg (.gpr 2))) #v[136, 132]
    (.letOp (n := 139) (.exec 0x10918c (fun s => s.RIP = 0x10918c) (orR64R64Effect 0x10918c 2 10) (Reg.operands [.gpr 2, .gpr 10] [])) #v[136, 132]
    (.letOp (n := 140) (.exec 0x10918f (StorePre 0x10918f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10918f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10918f 12 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[63, 4]
    (.letOp (n := 141) (.out 0x109194 (movR64R64Effect 0x109194 10 12) (EffectPart.reads (.reg (.gpr 10)) [.gpr 12] []) (.reg (.gpr 10))) #v[63]
    (.letOp (n := 142) (.exec 0x109194 (fun s => s.RIP = 0x109194) (movR64R64Effect 0x109194 10 12) (Reg.operands [.gpr 12] [])) #v[63]
    (.letOp (n := 143) (.out 0x109197 (rolR64Effect 0x109197 4 10 40) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[141]
    (.letOp (n := 144) (.exec 0x109197 (fun s => s.RIP = 0x109197) (rolR64Effect 0x109197 4 10 40) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[141]
    (.letOp (n := 145) (.out 0x10919b (andR64R64Effect 0x10919b 10 13) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 13] []) (.reg (.gpr 10))) #v[143, 71]
    (.letOp (n := 146) (.exec 0x10919b (fun s => s.RIP = 0x10919b) (andR64R64Effect 0x10919b 10 13) (Reg.operands [.gpr 10, .gpr 13] [])) #v[143, 71]
    (.letOp (n := 147) (.out 0x10919e (rolR64Effect 0x10919e 4 12 56) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[63]
    (.letOp (n := 148) (.exec 0x10919e (fun s => s.RIP = 0x10919e) (rolR64Effect 0x10919e 4 12 56) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[63]
    (.letOp (n := 149) (.out 0x1091a2 (andR64R64Effect 0x1091a2 12 1) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 1] []) (.reg (.gpr 12))) #v[147, 79]
    (.letOp (n := 150) (.exec 0x1091a2 (fun s => s.RIP = 0x1091a2) (andR64R64Effect 0x1091a2 12 1) (Reg.operands [.gpr 12, .gpr 1] [])) #v[147, 79]
    (.letOp (n := 151) (.out 0x1091a5 (movR64R64Effect 0x1091a5 13 14) (EffectPart.reads (.reg (.gpr 13)) [.gpr 14] []) (.reg (.gpr 13))) #v[65]
    (.letOp (n := 152) (.exec 0x1091a5 (fun s => s.RIP = 0x1091a5) (movR64R64Effect 0x1091a5 13 14) (Reg.operands [.gpr 14] [])) #v[65]
    (.letOp (n := 153) (.exec 0x1091a8 (StorePre 0x1091a8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1091a8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1091a8 14 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 154) (.out 0x1091b0 (rolR64Effect 0x1091b0 4 14 40) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[65]
    (.letOp (n := 155) (.exec 0x1091b0 (fun s => s.RIP = 0x1091b0) (rolR64Effect 0x1091b0 4 14 40) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[65]
    (.letOp (n := 156) (.out 0x1091b4 (orR64R64Effect 0x1091b4 12 10) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 10] []) (.reg (.gpr 12))) #v[149, 145]
    (.letOp (n := 157) (.exec 0x1091b4 (fun s => s.RIP = 0x1091b4) (orR64R64Effect 0x1091b4 12 10) (Reg.operands [.gpr 12, .gpr 10] [])) #v[149, 145]
    (.letOp (n := 158) (.exec 0x1091b7 (StorePre 0x1091b7 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x1091b7 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1091b7 12 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[156, 4]
    (.letOp (n := 159) (.out 0x1091bf (rolR64Effect 0x1091bf 4 13 56) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[151]
    (.letOp (n := 160) (.exec 0x1091bf (fun s => s.RIP = 0x1091bf) (rolR64Effect 0x1091bf 4 13 56) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[151]
    (.letOp (n := 161) (.out 0x1091c3 (movR64Imm64Effect 0x1091c3 10 0xff00ff00ff00ff) (EffectPart.reads (.reg (.gpr 10)) [] []) (.reg (.gpr 10))) #v[]
    (.letOp (n := 162) (.exec 0x1091c3 (fun s => s.RIP = 0x1091c3) (movR64Imm64Effect 0x1091c3 10 0xff00ff00ff00ff) (Reg.operands [] [])) #v[]
    (.letOp (n := 163) (.out 0x1091cd (andR64R64Effect 0x1091cd 14 10) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 10] []) (.reg (.gpr 14))) #v[154, 161]
    (.letOp (n := 164) (.exec 0x1091cd (fun s => s.RIP = 0x1091cd) (andR64R64Effect 0x1091cd 14 10) (Reg.operands [.gpr 14, .gpr 10] [])) #v[154, 161]
    (.letOp (n := 165) (.out 0x1091d0 (andR64R64Effect 0x1091d0 13 1) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 1] []) (.reg (.gpr 13))) #v[159, 79]
    (.letOp (n := 166) (.exec 0x1091d0 (fun s => s.RIP = 0x1091d0) (andR64R64Effect 0x1091d0 13 1) (Reg.operands [.gpr 13, .gpr 1] [])) #v[159, 79]
    (.letOp (n := 167) (.out 0x1091d3 (orR64R64Effect 0x1091d3 13 14) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 14] []) (.reg (.gpr 13))) #v[165, 163]
    (.letOp (n := 168) (.exec 0x1091d3 (fun s => s.RIP = 0x1091d3) (orR64R64Effect 0x1091d3 13 14) (Reg.operands [.gpr 13, .gpr 14] [])) #v[165, 163]
    (b_l1090e0_3)))))))))))))))))))))))))))))))))))))

def bytes_l1090e0_2 : List UInt8 :=
  [0x4D, 0x21, 0xEA, 0x48, 0xC1, 0xC2, 0x38, 0x48, 0x21, 0xCA, 0x4C, 0x09, 0xD2, 0x4C, 0x89, 0x64,
    0x24, 0x78, 0x4D, 0x89, 0xE2, 0x49, 0xC1, 0xC2, 0x28, 0x4D, 0x21, 0xEA, 0x49, 0xC1, 0xC4, 0x38,
    0x49, 0x21, 0xCC, 0x4D, 0x89, 0xF5, 0x4C, 0x89, 0xB4, 0x24, 0x80, 0x00, 0x00, 0x00, 0x49, 0xC1,
    0xC6, 0x28, 0x4D, 0x09, 0xD4, 0x4C, 0x89, 0xA4, 0x24, 0x90, 0x00, 0x00, 0x00, 0x49, 0xC1, 0xC5,
    0x38, 0x49, 0xBA, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0x4D, 0x21, 0xD6, 0x49, 0x21,
    0xCD, 0x4D, 0x09, 0xF5] ++ bytes_l1090e0_3

theorem code_l1090e0_2 : ∀ x ∈ codeRange 0x109182 bytes_l1090e0_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x9182 84 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1090e0_3

@[cfg_block] def b_l1090e0_1 : Block Op Label signature Reg.count 93 :=
  .letOp (n := 93) (.out 0x10913b (rolR64Effect 0x10913b 4 8 56) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[91]
    (.letOp (n := 94) (.exec 0x10913b (fun s => s.RIP = 0x10913b) (rolR64Effect 0x10913b 4 8 56) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[91]
    (.letOp (n := 95) (.out 0x10913f (andR64R64Effect 0x10913f 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[93, 79]
    (.letOp (n := 96) (.exec 0x10913f (fun s => s.RIP = 0x10913f) (andR64R64Effect 0x10913f 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[93, 79]
    (.letOp (n := 97) (.out 0x109142 (movR64R64Effect 0x109142 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7] []) (.reg (.gpr 2))) #v[57]
    (.letOp (n := 98) (.exec 0x109142 (fun s => s.RIP = 0x109142) (movR64R64Effect 0x109142 2 7) (Reg.operands [.gpr 7] [])) #v[57]
    (.letOp (n := 99) (.out 0x109145 (rolR64Effect 0x109145 4 2 40) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[97]
    (.letOp (n := 100) (.exec 0x109145 (fun s => s.RIP = 0x109145) (rolR64Effect 0x109145 4 2 40) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[97]
    (.letOp (n := 101) (.out 0x109149 (orR64R64Effect 0x109149 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[95, 89]
    (.letOp (n := 102) (.exec 0x109149 (fun s => s.RIP = 0x109149) (orR64R64Effect 0x109149 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[95, 89]
    (.letOp (n := 103) (.out 0x10914c (movR64R64Effect 0x10914c 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[57]
    (.letOp (n := 104) (.exec 0x10914c (fun s => s.RIP = 0x10914c) (movR64R64Effect 0x10914c 0 7) (Reg.operands [.gpr 7] [])) #v[57]
    (.letOp (n := 105) (.out 0x10914f (rolR64Effect 0x10914f 4 0 56) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[103]
    (.letOp (n := 106) (.exec 0x10914f (fun s => s.RIP = 0x10914f) (rolR64Effect 0x10914f 4 0 56) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[103]
    (.letOp (n := 107) (.out 0x109153 (andR64R64Effect 0x109153 2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 13] []) (.reg (.gpr 2))) #v[99, 71]
    (.letOp (n := 108) (.exec 0x109153 (fun s => s.RIP = 0x109153) (andR64R64Effect 0x109153 2 13) (Reg.operands [.gpr 2, .gpr 13] [])) #v[99, 71]
    (.letOp (n := 109) (.out 0x109156 (andR64R64Effect 0x109156 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[105, 79]
    (.letOp (n := 110) (.exec 0x109156 (fun s => s.RIP = 0x109156) (andR64R64Effect 0x109156 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[105, 79]
    (.letOp (n := 111) (.out 0x109159 (orR64R64Effect 0x109159 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[109, 107]
    (.letOp (n := 112) (.exec 0x109159 (fun s => s.RIP = 0x109159) (orR64R64Effect 0x109159 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[109, 107]
    (.letOp (n := 113) (.out 0x10915c (movR64R64Effect 0x10915c 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6] []) (.reg (.gpr 2))) #v[59]
    (.letOp (n := 114) (.exec 0x10915c (fun s => s.RIP = 0x10915c) (movR64R64Effect 0x10915c 2 6) (Reg.operands [.gpr 6] [])) #v[59]
    (.letOp (n := 115) (.out 0x10915f (rolR64Effect 0x10915f 4 2 40) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[113]
    (.letOp (n := 116) (.exec 0x10915f (fun s => s.RIP = 0x10915f) (rolR64Effect 0x10915f 4 2 40) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[113]
    (.letOp (n := 117) (.out 0x109163 (andR64R64Effect 0x109163 2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 13] []) (.reg (.gpr 2))) #v[115, 71]
    (.letOp (n := 118) (.exec 0x109163 (fun s => s.RIP = 0x109163) (andR64R64Effect 0x109163 2 13) (Reg.operands [.gpr 2, .gpr 13] [])) #v[115, 71]
    (.letOp (n := 119) (.out 0x109166 (movR64R64Effect 0x109166 15 6) (EffectPart.reads (.reg (.gpr 15)) [.gpr 6] []) (.reg (.gpr 15))) #v[59]
    (.letOp (n := 120) (.exec 0x109166 (fun s => s.RIP = 0x109166) (movR64R64Effect 0x109166 15 6) (Reg.operands [.gpr 6] [])) #v[59]
    (.letOp (n := 121) (.out 0x109169 (rolR64Effect 0x109169 4 15 56) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[119]
    (.letOp (n := 122) (.exec 0x109169 (fun s => s.RIP = 0x109169) (rolR64Effect 0x109169 4 15 56) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[119]
    (.letOp (n := 123) (.out 0x10916d (andR64R64Effect 0x10916d 15 1) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 1] []) (.reg (.gpr 15))) #v[121, 79]
    (.letOp (n := 124) (.exec 0x10916d (fun s => s.RIP = 0x10916d) (andR64R64Effect 0x10916d 15 1) (Reg.operands [.gpr 15, .gpr 1] [])) #v[121, 79]
    (.letOp (n := 125) (.out 0x109170 (orR64R64Effect 0x109170 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 2] []) (.reg (.gpr 15))) #v[123, 117]
    (.letOp (n := 126) (.exec 0x109170 (fun s => s.RIP = 0x109170) (orR64R64Effect 0x109170 15 2) (Reg.operands [.gpr 15, .gpr 2] [])) #v[123, 117]
    (.letOp (n := 127) (.out 0x109173 (movR64R64Effect 0x109173 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10] []) (.reg (.gpr 2))) #v[61]
    (.letOp (n := 128) (.exec 0x109173 (fun s => s.RIP = 0x109173) (movR64R64Effect 0x109173 2 10) (Reg.operands [.gpr 10] [])) #v[61]
    (.letOp (n := 129) (.exec 0x109176 (StorePre 0x109176 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x109176 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x109176 10 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 130) (.out 0x10917e (rolR64Effect 0x10917e 4 10 40) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[61]
    (.letOp (n := 131) (.exec 0x10917e (fun s => s.RIP = 0x10917e) (rolR64Effect 0x10917e 4 10 40) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[61]
    (b_l1090e0_2)))))))))))))))))))))))))))))))))))))))

def bytes_l1090e0_1 : List UInt8 :=
  [0x49, 0xC1, 0xC0, 0x38, 0x49, 0x21, 0xC8, 0x48, 0x89, 0xFA, 0x48, 0xC1, 0xC2, 0x28, 0x49, 0x09,
    0xC0, 0x48, 0x89, 0xF8, 0x48, 0xC1, 0xC0, 0x38, 0x4C, 0x21, 0xEA, 0x48, 0x21, 0xC8, 0x48, 0x09,
    0xD0, 0x48, 0x89, 0xF2, 0x48, 0xC1, 0xC2, 0x28, 0x4C, 0x21, 0xEA, 0x49, 0x89, 0xF7, 0x49, 0xC1,
    0xC7, 0x38, 0x49, 0x21, 0xCF, 0x49, 0x09, 0xD7, 0x4C, 0x89, 0xD2, 0x4C, 0x89, 0x94, 0x24, 0x88,
    0x00, 0x00, 0x00, 0x49, 0xC1, 0xC2, 0x28] ++ bytes_l1090e0_2

theorem code_l1090e0_1 : ∀ x ∈ codeRange 0x10913b bytes_l1090e0_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x913b 71 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1090e0_2

@[cfg_block] def b_l1090e0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1090e0 (movR64M64Effect 0x1090e0 3 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 54) (.exec 0x1090e0 (LoadPre 0x1090e0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1090e0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1090e0 3 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1090e5 (movR64M64Effect 0x1090e5 11 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 56) (.exec 0x1090e5 (LoadPre 0x1090e5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1090e5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1090e5 11 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1090ea (movR64M64Effect 0x1090ea 7 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 58) (.exec 0x1090ea (LoadPre 0x1090ea (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1090ea + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1090ea 7 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x1090ef (movR64M64Effect 0x1090ef 6 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 60) (.exec 0x1090ef (LoadPre 0x1090ef (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1090ef + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1090ef 6 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x1090f4 (movR64M64Effect 0x1090f4 10 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 62) (.exec 0x1090f4 (LoadPre 0x1090f4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1090f4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1090f4 10 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x1090f9 (movR64M64Effect 0x1090f9 12 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 64) (.exec 0x1090f9 (LoadPre 0x1090f9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1090f9 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1090f9 12 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x1090fe (movR64M64Effect 0x1090fe 14 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 66) (.exec 0x1090fe (LoadPre 0x1090fe (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1090fe + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1090fe 14 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x109103 (movR64R64Effect 0x109103 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 68) (.exec 0x109103 (fun s => s.RIP = 0x109103) (movR64R64Effect 0x109103 0 3) (Reg.operands [.gpr 3] [])) #v[53]
    (.letOp (n := 69) (.out 0x109106 (rolR64Effect 0x109106 4 0 40) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[67]
    (.letOp (n := 70) (.exec 0x109106 (fun s => s.RIP = 0x109106) (rolR64Effect 0x109106 4 0 40) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[67]
    (.letOp (n := 71) (.out 0x10910a (movR64Imm64Effect 0x10910a 13 0xff00ff00ff00ff) (EffectPart.reads (.reg (.gpr 13)) [] []) (.reg (.gpr 13))) #v[]
    (.letOp (n := 72) (.exec 0x10910a (fun s => s.RIP = 0x10910a) (movR64Imm64Effect 0x10910a 13 0xff00ff00ff00ff) (Reg.operands [] [])) #v[]
    (.letOp (n := 73) (.out 0x109114 (andR64R64Effect 0x109114 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 13] []) (.reg (.gpr 0))) #v[69, 71]
    (.letOp (n := 74) (.exec 0x109114 (fun s => s.RIP = 0x109114) (andR64R64Effect 0x109114 0 13) (Reg.operands [.gpr 0, .gpr 13] [])) #v[69, 71]
    (.letOp (n := 75) (.out 0x109117 (movR64R64Effect 0x109117 9 3) (EffectPart.reads (.reg (.gpr 9)) [.gpr 3] []) (.reg (.gpr 9))) #v[53]
    (.letOp (n := 76) (.exec 0x109117 (fun s => s.RIP = 0x109117) (movR64R64Effect 0x109117 9 3) (Reg.operands [.gpr 3] [])) #v[53]
    (.letOp (n := 77) (.out 0x10911a (rolR64Effect 0x10911a 4 9 56) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[75]
    (.letOp (n := 78) (.exec 0x10911a (fun s => s.RIP = 0x10911a) (rolR64Effect 0x10911a 4 9 56) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[75]
    (.letOp (n := 79) (.out 0x10911e (movR64Imm64Effect 0x10911e 1 0xff00ff00ff00ff00) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 80) (.exec 0x10911e (fun s => s.RIP = 0x10911e) (movR64Imm64Effect 0x10911e 1 0xff00ff00ff00ff00) (Reg.operands [] [])) #v[]
    (.letOp (n := 81) (.out 0x109128 (andR64R64Effect 0x109128 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1] []) (.reg (.gpr 9))) #v[77, 79]
    (.letOp (n := 82) (.exec 0x109128 (fun s => s.RIP = 0x109128) (andR64R64Effect 0x109128 9 1) (Reg.operands [.gpr 9, .gpr 1] [])) #v[77, 79]
    (.letOp (n := 83) (.out 0x10912b (orR64R64Effect 0x10912b 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0] []) (.reg (.gpr 9))) #v[81, 73]
    (.letOp (n := 84) (.exec 0x10912b (fun s => s.RIP = 0x10912b) (orR64R64Effect 0x10912b 9 0) (Reg.operands [.gpr 9, .gpr 0] [])) #v[81, 73]
    (.letOp (n := 85) (.out 0x10912e (movR64R64Effect 0x10912e 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[55]
    (.letOp (n := 86) (.exec 0x10912e (fun s => s.RIP = 0x10912e) (movR64R64Effect 0x10912e 0 11) (Reg.operands [.gpr 11] [])) #v[55]
    (.letOp (n := 87) (.out 0x109131 (rolR64Effect 0x109131 4 0 40) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[85]
    (.letOp (n := 88) (.exec 0x109131 (fun s => s.RIP = 0x109131) (rolR64Effect 0x109131 4 0 40) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[85]
    (.letOp (n := 89) (.out 0x109135 (andR64R64Effect 0x109135 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 13] []) (.reg (.gpr 0))) #v[87, 71]
    (.letOp (n := 90) (.exec 0x109135 (fun s => s.RIP = 0x109135) (andR64R64Effect 0x109135 0 13) (Reg.operands [.gpr 0, .gpr 13] [])) #v[87, 71]
    (.letOp (n := 91) (.out 0x109138 (movR64R64Effect 0x109138 8 11) (EffectPart.reads (.reg (.gpr 8)) [.gpr 11] []) (.reg (.gpr 8))) #v[55]
    (.letOp (n := 92) (.exec 0x109138 (fun s => s.RIP = 0x109138) (movR64R64Effect 0x109138 8 11) (Reg.operands [.gpr 11] [])) #v[55]
    (b_l1090e0_1))))))))))))))))))))))))))))))))))))))))

def bytes_l1090e0 : List UInt8 :=
  [0x48, 0x8B, 0x5C, 0x24, 0x08, 0x4C, 0x8B, 0x5C, 0x24, 0x10, 0x48, 0x8B, 0x7C, 0x24, 0x18, 0x48,
    0x8B, 0x74, 0x24, 0x20, 0x4C, 0x8B, 0x54, 0x24, 0x28, 0x4C, 0x8B, 0x64, 0x24, 0x30, 0x4C, 0x8B,
    0x74, 0x24, 0x38, 0x48, 0x89, 0xD8, 0x48, 0xC1, 0xC0, 0x28, 0x49, 0xBD, 0xFF, 0x00, 0xFF, 0x00,
    0xFF, 0x00, 0xFF, 0x00, 0x4C, 0x21, 0xE8, 0x49, 0x89, 0xD9, 0x49, 0xC1, 0xC1, 0x38, 0x48, 0xB9,
    0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x49, 0x21, 0xC9, 0x49, 0x09, 0xC1, 0x4C, 0x89,
    0xD8, 0x48, 0xC1, 0xC0, 0x28, 0x4C, 0x21, 0xE8, 0x4D, 0x89, 0xD8] ++ bytes_l1090e0_1

theorem code_l1090e0 : ∀ x ∈ codeRange 0x1090e0 bytes_l1090e0, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x90e0 91 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1090e0_1

@[cfg_block] def b_l109326 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x109326 (movR64R64Effect 0x109326 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 54) (.exec 0x109326 (fun s => s.RIP = 0x109326) (movR64R64Effect 0x109326 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x109329 (callEffect (fun _ => 0x100830) 0x10932e) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 56) (.exec 0x109329 (PushPre 0x109329 5) (callEffect (fun _ => 0x100830) 0x10932e) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.const ⟨64, 0x10932e⟩) #v[]
    (.terminate (.call ⟨.l100830, RegMap.args [(3, 3), (4, 55), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ { target := .l10932e, kept := #v[], arity := rfl, guard := some (Fin.last 57) }))))))

def bytes_l109326 : List UInt8 :=
  [0x48, 0x89, 0xDF, 0xE8, 0x02, 0x75, 0xFF, 0xFF]

theorem code_l109326 : ∀ x ∈ codeRange 0x109326 bytes_l109326, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9326 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10932e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10932e (movR64M64Effect 0x10932e 0 (.sib 4 (some 5) 3 (.d32 0x1d8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4, .gpr 5] []) (.reg (.gpr 0))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x10932e (LoadPre 0x10932e (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x1d8)) s (0x10932e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10932e 0 (.sib 4 (some 5) 3 (.d32 0x1d8))) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.exec 0x109336 (StorePre 0x109336 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109336 + BitVec.ofNat 64 5)) 8) (xorMREffect 0x109336 5 64 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x10933b (movR64M64Effect 0x10933b 0 (.sib 4 (some 5) 3 (.d32 0x1e0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4, .gpr 5] []) (.reg (.gpr 0))) #v[4, 5]
    (.letOp (n := 57) (.exec 0x10933b (LoadPre 0x10933b (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x1e0)) s (0x10933b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10933b 0 (.sib 4 (some 5) 3 (.d32 0x1e0))) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 58) (.exec 0x109343 (StorePre 0x109343 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x109343 + BitVec.ofNat 64 5)) 8) (xorMREffect 0x109343 5 64 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x109348 (movR64M64Effect 0x109348 0 (.sib 4 (some 5) 3 (.d32 0x1e8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4, .gpr 5] []) (.reg (.gpr 0))) #v[4, 5]
    (.letOp (n := 60) (.exec 0x109348 (LoadPre 0x109348 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x1e8)) s (0x109348 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x109348 0 (.sib 4 (some 5) 3 (.d32 0x1e8))) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 61) (.exec 0x109350 (StorePre 0x109350 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x109350 + BitVec.ofNat 64 5)) 8) (xorMREffect 0x109350 5 64 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x109355 (movR64M64Effect 0x109355 0 (.sib 4 (some 5) 3 (.d32 0x1f0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4, .gpr 5] []) (.reg (.gpr 0))) #v[4, 5]
    (.letOp (n := 63) (.exec 0x109355 (LoadPre 0x109355 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x1f0)) s (0x109355 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x109355 0 (.sib 4 (some 5) 3 (.d32 0x1f0))) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 64) (.exec 0x10935d (StorePre 0x10935d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10935d + BitVec.ofNat 64 5)) 8) (xorMREffect 0x10935d 5 64 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x109362 (movR64M64Effect 0x109362 0 (.sib 4 (some 5) 3 (.d32 0x1f8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4, .gpr 5] []) (.reg (.gpr 0))) #v[4, 5]
    (.letOp (n := 66) (.exec 0x109362 (LoadPre 0x109362 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x1f8)) s (0x109362 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x109362 0 (.sib 4 (some 5) 3 (.d32 0x1f8))) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 67) (.exec 0x10936a (StorePre 0x10936a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10936a + BitVec.ofNat 64 5)) 8) (xorMREffect 0x10936a 5 64 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x10936f (movR64M64Effect 0x10936f 0 (.sib 4 (some 5) 3 (.d32 0x200))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4, .gpr 5] []) (.reg (.gpr 0))) #v[4, 5]
    (.letOp (n := 69) (.exec 0x10936f (LoadPre 0x10936f (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x200)) s (0x10936f + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10936f 0 (.sib 4 (some 5) 3 (.d32 0x200))) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 70) (.exec 0x109377 (StorePre 0x109377 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x109377 + BitVec.ofNat 64 5)) 8) (xorMREffect 0x109377 5 64 0 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[68, 4]
    (.letOp (n := 71) (.out 0x10937c (movR64M64Effect 0x10937c 0 (.sib 4 (some 5) 3 (.d32 0x208))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4, .gpr 5] []) (.reg (.gpr 0))) #v[4, 5]
    (.letOp (n := 72) (.exec 0x10937c (LoadPre 0x10937c (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x208)) s (0x10937c + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10937c 0 (.sib 4 (some 5) 3 (.d32 0x208))) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 73) (.exec 0x109384 (StorePre 0x109384 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x109384 + BitVec.ofNat 64 5)) 8) (xorMREffect 0x109384 5 64 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[71, 4]
    (.letOp (n := 74) (.out 0x109389 (movR64M64Effect 0x109389 0 (.sib 4 (some 5) 3 (.d32 0x210))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4, .gpr 5] []) (.reg (.gpr 0))) #v[4, 5]
    (.letOp (n := 75) (.exec 0x109389 (LoadPre 0x109389 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x210)) s (0x109389 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x109389 0 (.sib 4 (some 5) 3 (.d32 0x210))) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 76) (.exec 0x109391 (StorePre 0x109391 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x109391 + BitVec.ofNat 64 5)) 8) (xorMREffect 0x109391 5 64 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[74, 4]
    (.letOp (n := 77) (.out 0x109396 (movR32Imm32Effect 0x109396 5 6 0x8) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 78) (.exec 0x109396 (fun s => s.RIP = 0x109396) (movR32Imm32Effect 0x109396 5 6 0x8) (Reg.operands [] [])) #v[]
    (.letOp (n := 79) (.out 0x10939b (movR64R64Effect 0x10939b 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 80) (.exec 0x10939b (fun s => s.RIP = 0x10939b) (movR64R64Effect 0x10939b 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 81) (.out 0x10939e (callEffect (fun _ => 0x100e90) 0x1093a3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 82) (.exec 0x10939e (PushPre 0x10939e 5) (callEffect (fun _ => 0x100e90) 0x1093a3) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 83) (.const ⟨64, 0x1093a3⟩) #v[]
    (.terminate (.call ⟨.l100e90, RegMap.args [(0, 74), (3, 3), (4, 81), (5, 5), (6, 77), (7, 79), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 84⟩ { target := .l1093a3, kept := #v[], arity := rfl, guard := some (Fin.last 83) }))))))))))))))))))))))))))))))))

def bytes_l10932e : List UInt8 :=
  [0x48, 0x8B, 0x84, 0xEC, 0xD8, 0x01, 0x00, 0x00, 0x48, 0x31, 0x44, 0x24, 0x08, 0x48, 0x8B, 0x84,
    0xEC, 0xE0, 0x01, 0x00, 0x00, 0x48, 0x31, 0x44, 0x24, 0x10, 0x48, 0x8B, 0x84, 0xEC, 0xE8, 0x01,
    0x00, 0x00, 0x48, 0x31, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x84, 0xEC, 0xF0, 0x01, 0x00, 0x00, 0x48,
    0x31, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x84, 0xEC, 0xF8, 0x01, 0x00, 0x00, 0x48, 0x31, 0x44, 0x24,
    0x28, 0x48, 0x8B, 0x84, 0xEC, 0x00, 0x02, 0x00, 0x00, 0x48, 0x31, 0x44, 0x24, 0x30, 0x48, 0x8B,
    0x84, 0xEC, 0x08, 0x02, 0x00, 0x00, 0x48, 0x31, 0x44, 0x24, 0x38, 0x48, 0x8B, 0x84, 0xEC, 0x10,
    0x02, 0x00, 0x00, 0x48, 0x31, 0x44, 0x24, 0x40, 0xBE, 0x08, 0x00, 0x00, 0x00, 0x48, 0x89, 0xDF,
    0xE8, 0xED, 0x7A, 0xFF, 0xFF]

theorem code_l10932e : ∀ x ∈ codeRange 0x10932e bytes_l10932e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x932e 117 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1093a3_4 : Block Op Label signature Reg.count 204 :=
  .letOp (n := 204) (.out 0x1094ec (rolR64Effect 0x1094ec 4 7 32) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[123]
    (.letOp (n := 205) (.exec 0x1094ec (fun s => s.RIP = 0x1094ec) (rolR64Effect 0x1094ec 4 7 32) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[123]
    (.letOp (n := 206) (.out 0x1094f0 (xorR64M64Effect 0x1094f0 7 (.sib 4 (some 5) 3 (.d32 0x248))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 4, .gpr 5] []) (.reg (.gpr 7))) #v[204, 4, 5]
    (.letOp (n := 207) (.exec 0x1094f0 (LoadPre 0x1094f0 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x248)) s (0x1094f0 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x1094f0 7 (.sib 4 (some 5) 3 (.d32 0x248))) (Reg.operands [.gpr 7, .gpr 4, .gpr 5] [])) #v[204, 4, 5]
    (.letOp (n := 208) (.out 0x1094f8 (xorR64R64Effect 0x1094f8 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 7] []) (.reg (.gpr 3))) #v[202, 206]
    (.letOp (n := 209) (.exec 0x1094f8 (fun s => s.RIP = 0x1094f8) (xorR64R64Effect 0x1094f8 3 7) (Reg.operands [.gpr 3, .gpr 7] [])) #v[202, 206]
    (.letOp (n := 210) (.exec 0x1094fb (StorePre 0x1094fb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1094fb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1094fb 3 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[208, 4]
    (.letOp (n := 211) (.out 0x109500 (addR64Imm8Effect 0x109500 5 0x20) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5] []) (.reg (.gpr 5))) #v[5]
    (.letOp (n := 212) (.exec 0x109500 (fun s => s.RIP = 0x109500) (addR64Imm8Effect 0x109500 5 0x20) (Reg.operands [.gpr 5] [])) #v[5]
    (.terminate (.br ⟨.l109010, RegMap.args [(0, 195), (1, 199), (2, 184), (3, 208), (4, 4), (5, 211), (6, 177), (7, 206), (8, 166), (9, 157), (10, 149), (11, 121), (12, 147), (13, 164), (14, 154), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)] 213⟩))))))))))

def bytes_l1093a3_4 : List UInt8 :=
  [0x48, 0xC1, 0xC7, 0x20, 0x48, 0x33, 0xBC, 0xEC, 0x48, 0x02, 0x00, 0x00, 0x48, 0x31, 0xFB, 0x48,
    0x89, 0x5C, 0x24, 0x38, 0x48, 0x83, 0xC5, 0x20, 0xE9, 0x07, 0xFB, 0xFF, 0xFF]

theorem code_l1093a3_4 : ∀ x ∈ codeRange 0x1094ec bytes_l1093a3_4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x94ec 29 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1093a3_3 : Block Op Label signature Reg.count 168 :=
  .letOp (n := 168) (.exec 0x109495 (StorePre 0x109495 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x109495 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109495 8 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[166, 4]
    (.letOp (n := 169) (.out 0x10949a (rolR64Effect 0x10949a 4 6 32) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[117]
    (.letOp (n := 170) (.exec 0x10949a (fun s => s.RIP = 0x10949a) (rolR64Effect 0x10949a 4 6 32) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[117]
    (.letOp (n := 171) (.out 0x10949e (xorR64M64Effect 0x10949e 6 (.sib 4 (some 5) 3 (.d32 0x230))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 4, .gpr 5] []) (.reg (.gpr 6))) #v[169, 4, 5]
    (.letOp (n := 172) (.exec 0x10949e (LoadPre 0x10949e (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x230)) s (0x10949e + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x10949e 6 (.sib 4 (some 5) 3 (.d32 0x230))) (Reg.operands [.gpr 6, .gpr 4, .gpr 5] [])) #v[169, 4, 5]
    (.letOp (n := 173) (.out 0x1094a6 (xorR64R64Effect 0x1094a6 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[137, 171]
    (.letOp (n := 174) (.exec 0x1094a6 (fun s => s.RIP = 0x1094a6) (xorR64R64Effect 0x1094a6 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[137, 171]
    (.letOp (n := 175) (.out 0x1094a9 (movR64R64Effect 0x1094a9 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[151]
    (.letOp (n := 176) (.exec 0x1094a9 (fun s => s.RIP = 0x1094a9) (movR64R64Effect 0x1094a9 6 3) (Reg.operands [.gpr 3] [])) #v[151]
    (.letOp (n := 177) (.out 0x1094ac (rolR64Effect 0x1094ac 4 6 48) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[175]
    (.letOp (n := 178) (.exec 0x1094ac (fun s => s.RIP = 0x1094ac) (rolR64Effect 0x1094ac 4 6 48) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[175]
    (.letOp (n := 179) (.exec 0x1094b0 (StorePre 0x1094b0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1094b0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1094b0 2 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[173, 4]
    (.letOp (n := 180) (.out 0x1094b5 (movR64R64Effect 0x1094b5 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[115]
    (.letOp (n := 181) (.exec 0x1094b5 (fun s => s.RIP = 0x1094b5) (movR64R64Effect 0x1094b5 2 1) (Reg.operands [.gpr 1] [])) #v[115]
    (.letOp (n := 182) (.out 0x1094b8 (rolR64Effect 0x1094b8 4 2 32) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[180]
    (.letOp (n := 183) (.exec 0x1094b8 (fun s => s.RIP = 0x1094b8) (rolR64Effect 0x1094b8 4 2 32) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[180]
    (.letOp (n := 184) (.out 0x1094bc (xorR64M64Effect 0x1094bc 2 (.sib 4 (some 5) 3 (.d32 0x238))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 4, .gpr 5] []) (.reg (.gpr 2))) #v[182, 4, 5]
    (.letOp (n := 185) (.exec 0x1094bc (LoadPre 0x1094bc (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x238)) s (0x1094bc + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x1094bc 2 (.sib 4 (some 5) 3 (.d32 0x238))) (Reg.operands [.gpr 2, .gpr 4, .gpr 5] [])) #v[182, 4, 5]
    (.letOp (n := 186) (.out 0x1094c4 (xorR64R64Effect 0x1094c4 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[139, 184]
    (.letOp (n := 187) (.exec 0x1094c4 (fun s => s.RIP = 0x1094c4) (xorR64R64Effect 0x1094c4 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[139, 184]
    (.letOp (n := 188) (.out 0x1094c7 (xorR64R64Effect 0x1094c7 3 6) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 6] []) (.reg (.gpr 3))) #v[151, 177]
    (.letOp (n := 189) (.exec 0x1094c7 (fun s => s.RIP = 0x1094c7) (xorR64R64Effect 0x1094c7 3 6) (Reg.operands [.gpr 3, .gpr 6] [])) #v[151, 177]
    (.letOp (n := 190) (.exec 0x1094ca (StorePre 0x1094ca 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1094ca + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1094ca 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[186, 4]
    (.letOp (n := 191) (.out 0x1094cf (movR64R64Effect 0x1094cf 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[188]
    (.letOp (n := 192) (.exec 0x1094cf (fun s => s.RIP = 0x1094cf) (movR64R64Effect 0x1094cf 0 3) (Reg.operands [.gpr 3] [])) #v[188]
    (.letOp (n := 193) (.out 0x1094d2 (rolR64Effect 0x1094d2 4 0 32) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[191]
    (.letOp (n := 194) (.exec 0x1094d2 (fun s => s.RIP = 0x1094d2) (rolR64Effect 0x1094d2 4 0 32) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[191]
    (.letOp (n := 195) (.out 0x1094d6 (xorR64M64Effect 0x1094d6 0 (.sib 4 (some 5) 3 (.d32 0x240))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4, .gpr 5] []) (.reg (.gpr 0))) #v[193, 4, 5]
    (.letOp (n := 196) (.exec 0x1094d6 (LoadPre 0x1094d6 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x240)) s (0x1094d6 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x1094d6 0 (.sib 4 (some 5) 3 (.d32 0x240))) (Reg.operands [.gpr 0, .gpr 4, .gpr 5] [])) #v[193, 4, 5]
    (.letOp (n := 197) (.out 0x1094de (xorR64R64Effect 0x1094de 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[115, 177]
    (.letOp (n := 198) (.exec 0x1094de (fun s => s.RIP = 0x1094de) (xorR64R64Effect 0x1094de 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[115, 177]
    (.letOp (n := 199) (.out 0x1094e1 (xorR64R64Effect 0x1094e1 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[197, 195]
    (.letOp (n := 200) (.exec 0x1094e1 (fun s => s.RIP = 0x1094e1) (xorR64R64Effect 0x1094e1 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[197, 195]
    (.letOp (n := 201) (.exec 0x1094e4 (StorePre 0x1094e4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1094e4 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1094e4 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[199, 4]
    (.letOp (n := 202) (.out 0x1094e9 (xorR64R64Effect 0x1094e9 3 11) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 11] []) (.reg (.gpr 3))) #v[188, 121]
    (.letOp (n := 203) (.exec 0x1094e9 (fun s => s.RIP = 0x1094e9) (xorR64R64Effect 0x1094e9 3 11) (Reg.operands [.gpr 3, .gpr 11] [])) #v[188, 121]
    (b_l1093a3_4))))))))))))))))))))))))))))))))))))

def bytes_l1093a3_3 : List UInt8 :=
  [0x4C, 0x89, 0x44, 0x24, 0x18, 0x48, 0xC1, 0xC6, 0x20, 0x48, 0x33, 0xB4, 0xEC, 0x30, 0x02, 0x00,
    0x00, 0x48, 0x31, 0xF2, 0x48, 0x89, 0xDE, 0x48, 0xC1, 0xC6, 0x30, 0x48, 0x89, 0x54, 0x24, 0x20,
    0x48, 0x89, 0xCA, 0x48, 0xC1, 0xC2, 0x20, 0x48, 0x33, 0x94, 0xEC, 0x38, 0x02, 0x00, 0x00, 0x48,
    0x31, 0xD0, 0x48, 0x31, 0xF3, 0x48, 0x89, 0x44, 0x24, 0x28, 0x48, 0x89, 0xD8, 0x48, 0xC1, 0xC0,
    0x20, 0x48, 0x33, 0x84, 0xEC, 0x40, 0x02, 0x00, 0x00, 0x48, 0x31, 0xF1, 0x48, 0x31, 0xC1, 0x48,
    0x89, 0x4C, 0x24, 0x30, 0x4C, 0x31, 0xDB] ++ bytes_l1093a3_4

theorem code_l1093a3_3 : ∀ x ∈ codeRange 0x109495 bytes_l1093a3_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x9495 87 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1093a3_4

@[cfg_block] def b_l1093a3_2 : Block Op Label signature Reg.count 131 :=
  .letOp (n := 131) (.out 0x10943a (rolR64Effect 0x10943a 4 14 32) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[129]
    (.letOp (n := 132) (.exec 0x10943a (fun s => s.RIP = 0x10943a) (rolR64Effect 0x10943a 4 14 32) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[129]
    (.letOp (n := 133) (.out 0x10943e (xorR64R64Effect 0x10943e 10 3) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 3] []) (.reg (.gpr 10))) #v[61, 127]
    (.letOp (n := 134) (.exec 0x10943e (fun s => s.RIP = 0x10943e) (xorR64R64Effect 0x10943e 10 3) (Reg.operands [.gpr 10, .gpr 3] [])) #v[61, 127]
    (.letOp (n := 135) (.out 0x109441 (xorR64R64Effect 0x109441 9 3) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 3] []) (.reg (.gpr 9))) #v[105, 127]
    (.letOp (n := 136) (.exec 0x109441 (fun s => s.RIP = 0x109441) (xorR64R64Effect 0x109441 9 3) (Reg.operands [.gpr 9, .gpr 3] [])) #v[105, 127]
    (.letOp (n := 137) (.out 0x109444 (xorR64R64Effect 0x109444 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 3] []) (.reg (.gpr 2))) #v[109, 127]
    (.letOp (n := 138) (.exec 0x109444 (fun s => s.RIP = 0x109444) (xorR64R64Effect 0x109444 2 3) (Reg.operands [.gpr 2, .gpr 3] [])) #v[109, 127]
    (.letOp (n := 139) (.out 0x109447 (xorR64R64Effect 0x109447 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[119, 127]
    (.letOp (n := 140) (.exec 0x109447 (fun s => s.RIP = 0x109447) (xorR64R64Effect 0x109447 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[119, 127]
    (.letOp (n := 141) (.out 0x10944a (rolR64Effect 0x10944a 4 3 32) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[127]
    (.letOp (n := 142) (.exec 0x10944a (fun s => s.RIP = 0x10944a) (rolR64Effect 0x10944a 4 3 32) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[127]
    (.letOp (n := 143) (.out 0x10944e (xorR64R64Effect 0x10944e 15 7) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 7] []) (.reg (.gpr 15))) #v[113, 123]
    (.letOp (n := 144) (.exec 0x10944e (fun s => s.RIP = 0x10944e) (xorR64R64Effect 0x10944e 15 7) (Reg.operands [.gpr 15, .gpr 7] [])) #v[113, 123]
    (.letOp (n := 145) (.out 0x109451 (xorR64R64Effect 0x109451 15 3) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 3] []) (.reg (.gpr 15))) #v[143, 141]
    (.letOp (n := 146) (.exec 0x109451 (fun s => s.RIP = 0x109451) (xorR64R64Effect 0x109451 15 3) (Reg.operands [.gpr 15, .gpr 3] [])) #v[143, 141]
    (.letOp (n := 147) (.out 0x109454 (xorR64M64Effect 0x109454 12 (.sib 4 (some 5) 3 (.d32 0x218))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 4, .gpr 5] []) (.reg (.gpr 12))) #v[125, 4, 5]
    (.letOp (n := 148) (.exec 0x109454 (LoadPre 0x109454 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x218)) s (0x109454 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x109454 12 (.sib 4 (some 5) 3 (.d32 0x218))) (Reg.operands [.gpr 12, .gpr 4, .gpr 5] [])) #v[125, 4, 5]
    (.letOp (n := 149) (.out 0x10945c (xorR64R64Effect 0x10945c 10 12) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 12] []) (.reg (.gpr 10))) #v[133, 147]
    (.letOp (n := 150) (.exec 0x10945c (fun s => s.RIP = 0x10945c) (xorR64R64Effect 0x10945c 10 12) (Reg.operands [.gpr 10, .gpr 12] [])) #v[133, 147]
    (.letOp (n := 151) (.out 0x10945f (movR64M64Effect 0x10945f 3 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 152) (.exec 0x10945f (LoadPre 0x10945f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10945f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10945f 3 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 153) (.exec 0x109464 (StorePre 0x109464 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x109464 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109464 15 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[145, 4]
    (.letOp (n := 154) (.out 0x109469 (xorR64M64Effect 0x109469 14 (.sib 4 (some 5) 3 (.d32 0x220))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 4, .gpr 5] []) (.reg (.gpr 14))) #v[131, 4, 5]
    (.letOp (n := 155) (.exec 0x109469 (LoadPre 0x109469 (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x220)) s (0x109469 + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x109469 14 (.sib 4 (some 5) 3 (.d32 0x220))) (Reg.operands [.gpr 14, .gpr 4, .gpr 5] [])) #v[131, 4, 5]
    (.letOp (n := 156) (.exec 0x109471 (StorePre 0x109471 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109471 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109471 10 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[149, 4]
    (.letOp (n := 157) (.out 0x109476 (xorR64R64Effect 0x109476 9 14) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 14] []) (.reg (.gpr 9))) #v[135, 154]
    (.letOp (n := 158) (.exec 0x109476 (fun s => s.RIP = 0x109476) (xorR64R64Effect 0x109476 9 14) (Reg.operands [.gpr 9, .gpr 14] [])) #v[135, 154]
    (.letOp (n := 159) (.exec 0x109479 (StorePre 0x109479 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x109479 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109479 9 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[157, 4]
    (.letOp (n := 160) (.out 0x10947e (xorR64M64Effect 0x10947e 8 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 4] []) (.reg (.gpr 8))) #v[97, 4]
    (.letOp (n := 161) (.exec 0x10947e (LoadPre 0x10947e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10947e + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x10947e 8 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[97, 4]
    (.letOp (n := 162) (.out 0x109486 (rolR64Effect 0x109486 4 13 32) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[107]
    (.letOp (n := 163) (.exec 0x109486 (fun s => s.RIP = 0x109486) (rolR64Effect 0x109486 4 13 32) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[107]
    (.letOp (n := 164) (.out 0x10948a (xorR64M64Effect 0x10948a 13 (.sib 4 (some 5) 3 (.d32 0x228))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 4, .gpr 5] []) (.reg (.gpr 13))) #v[162, 4, 5]
    (.letOp (n := 165) (.exec 0x10948a (LoadPre 0x10948a (fun s => AddrMode.addr (.sib 4 (some 5) 3 (.d32 0x228)) s (0x10948a + BitVec.ofNat 64 8)) 8) (xorR64M64Effect 0x10948a 13 (.sib 4 (some 5) 3 (.d32 0x228))) (Reg.operands [.gpr 13, .gpr 4, .gpr 5] [])) #v[162, 4, 5]
    (.letOp (n := 166) (.out 0x109492 (xorR64R64Effect 0x109492 8 13) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 13] []) (.reg (.gpr 8))) #v[160, 164]
    (.letOp (n := 167) (.exec 0x109492 (fun s => s.RIP = 0x109492) (xorR64R64Effect 0x109492 8 13) (Reg.operands [.gpr 8, .gpr 13] [])) #v[160, 164]
    (b_l1093a3_3)))))))))))))))))))))))))))))))))))))

def bytes_l1093a3_2 : List UInt8 :=
  [0x49, 0xC1, 0xC6, 0x20, 0x49, 0x31, 0xDA, 0x49, 0x31, 0xD9, 0x48, 0x31, 0xDA, 0x48, 0x31, 0xD8,
    0x48, 0xC1, 0xC3, 0x20, 0x49, 0x31, 0xFF, 0x49, 0x31, 0xDF, 0x4C, 0x33, 0xA4, 0xEC, 0x18, 0x02,
    0x00, 0x00, 0x4D, 0x31, 0xE2, 0x48, 0x8B, 0x5C, 0x24, 0x30, 0x4C, 0x89, 0x7C, 0x24, 0x40, 0x4C,
    0x33, 0xB4, 0xEC, 0x20, 0x02, 0x00, 0x00, 0x4C, 0x89, 0x54, 0x24, 0x08, 0x4D, 0x31, 0xF1, 0x4C,
    0x89, 0x4C, 0x24, 0x10, 0x4C, 0x33, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x49, 0xC1, 0xC5, 0x20,
    0x4C, 0x33, 0xAC, 0xEC, 0x28, 0x02, 0x00, 0x00, 0x4D, 0x31, 0xE8] ++ bytes_l1093a3_3

theorem code_l1093a3_2 : ∀ x ∈ codeRange 0x10943a bytes_l1093a3_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x943a 91 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1093a3_3

@[cfg_block] def b_l1093a3_1 : Block Op Label signature Reg.count 92 :=
  .letOp (n := 92) (.out 0x1093f7 (rolR64Effect 0x1093f7 4 6 48) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[90]
    (.letOp (n := 93) (.exec 0x1093f7 (fun s => s.RIP = 0x1093f7) (rolR64Effect 0x1093f7 4 6 48) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[90]
    (.letOp (n := 94) (.exec 0x1093fb (StorePre 0x1093fb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1093fb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1093fb 6 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[92, 4]
    (.letOp (n := 95) (.out 0x109400 (xorR64R64Effect 0x109400 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[53, 61]
    (.letOp (n := 96) (.exec 0x109400 (fun s => s.RIP = 0x109400) (xorR64R64Effect 0x109400 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[53, 61]
    (.letOp (n := 97) (.out 0x109403 (xorR64R64Effect 0x109403 8 13) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 13] []) (.reg (.gpr 8))) #v[55, 67]
    (.letOp (n := 98) (.exec 0x109403 (fun s => s.RIP = 0x109403) (xorR64R64Effect 0x109403 8 13) (Reg.operands [.gpr 8, .gpr 13] [])) #v[55, 67]
    (.letOp (n := 99) (.out 0x109406 (xorR64R64Effect 0x109406 2 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 11] []) (.reg (.gpr 2))) #v[57, 75]
    (.letOp (n := 100) (.exec 0x109406 (fun s => s.RIP = 0x109406) (xorR64R64Effect 0x109406 2 11) (Reg.operands [.gpr 2, .gpr 11] [])) #v[57, 75]
    (.letOp (n := 101) (.out 0x109409 (xorR64R64Effect 0x109409 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 15] []) (.reg (.gpr 0))) #v[63, 82]
    (.letOp (n := 102) (.exec 0x109409 (fun s => s.RIP = 0x109409) (xorR64R64Effect 0x109409 0 15) (Reg.operands [.gpr 0, .gpr 15] [])) #v[63, 82]
    (.letOp (n := 103) (.out 0x10940c (movR64R64Effect 0x10940c 12 9) (EffectPart.reads (.reg (.gpr 12)) [.gpr 9] []) (.reg (.gpr 12))) #v[95]
    (.letOp (n := 104) (.exec 0x10940c (fun s => s.RIP = 0x10940c) (movR64R64Effect 0x10940c 12 9) (Reg.operands [.gpr 9] [])) #v[95]
    (.letOp (n := 105) (.out 0x10940f (xorR64R64Effect 0x10940f 9 13) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 13] []) (.reg (.gpr 9))) #v[95, 67]
    (.letOp (n := 106) (.exec 0x10940f (fun s => s.RIP = 0x10940f) (xorR64R64Effect 0x10940f 9 13) (Reg.operands [.gpr 9, .gpr 13] [])) #v[95, 67]
    (.letOp (n := 107) (.out 0x109412 (movR64R64Effect 0x109412 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[99]
    (.letOp (n := 108) (.exec 0x109412 (fun s => s.RIP = 0x109412) (movR64R64Effect 0x109412 13 2) (Reg.operands [.gpr 2] [])) #v[99]
    (.letOp (n := 109) (.out 0x109415 (xorR64R64Effect 0x109415 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 15] []) (.reg (.gpr 2))) #v[99, 82]
    (.letOp (n := 110) (.exec 0x109415 (fun s => s.RIP = 0x109415) (xorR64R64Effect 0x109415 2 15) (Reg.operands [.gpr 2, .gpr 15] [])) #v[99, 82]
    (.letOp (n := 111) (.out 0x109418 (movR64R64Effect 0x109418 15 3) (EffectPart.reads (.reg (.gpr 15)) [.gpr 3] []) (.reg (.gpr 15))) #v[84]
    (.letOp (n := 112) (.exec 0x109418 (fun s => s.RIP = 0x109418) (movR64R64Effect 0x109418 15 3) (Reg.operands [.gpr 3] [])) #v[84]
    (.letOp (n := 113) (.out 0x10941b (rolR64Effect 0x10941b 4 15 48) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[111]
    (.letOp (n := 114) (.exec 0x10941b (fun s => s.RIP = 0x10941b) (rolR64Effect 0x10941b 4 15 48) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[111]
    (.letOp (n := 115) (.out 0x10941f (xorR64R64Effect 0x10941f 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 14] []) (.reg (.gpr 1))) #v[69, 88]
    (.letOp (n := 116) (.exec 0x10941f (fun s => s.RIP = 0x10941f) (xorR64R64Effect 0x10941f 1 14) (Reg.operands [.gpr 1, .gpr 14] [])) #v[69, 88]
    (.letOp (n := 117) (.out 0x109422 (movR64R64Effect 0x109422 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[101]
    (.letOp (n := 118) (.exec 0x109422 (fun s => s.RIP = 0x109422) (movR64R64Effect 0x109422 6 0) (Reg.operands [.gpr 0] [])) #v[101]
    (.letOp (n := 119) (.out 0x109425 (xorR64R64Effect 0x109425 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[101, 88]
    (.letOp (n := 120) (.exec 0x109425 (fun s => s.RIP = 0x109425) (xorR64R64Effect 0x109425 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[101, 88]
    (.letOp (n := 121) (.out 0x109428 (movR64M64Effect 0x109428 11 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 122) (.exec 0x109428 (LoadPre 0x109428 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x109428 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109428 11 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 123) (.out 0x10942d (xorR64R64Effect 0x10942d 7 11) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 11] []) (.reg (.gpr 7))) #v[78, 121]
    (.letOp (n := 124) (.exec 0x10942d (fun s => s.RIP = 0x10942d) (xorR64R64Effect 0x10942d 7 11) (Reg.operands [.gpr 7, .gpr 11] [])) #v[78, 121]
    (.letOp (n := 125) (.out 0x109430 (rolR64Effect 0x109430 4 12 32) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[103]
    (.letOp (n := 126) (.exec 0x109430 (fun s => s.RIP = 0x109430) (rolR64Effect 0x109430 4 12 32) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[103]
    (.letOp (n := 127) (.out 0x109434 (xorR64R64Effect 0x109434 3 15) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 15] []) (.reg (.gpr 3))) #v[84, 113]
    (.letOp (n := 128) (.exec 0x109434 (fun s => s.RIP = 0x109434) (xorR64R64Effect 0x109434 3 15) (Reg.operands [.gpr 3, .gpr 15] [])) #v[84, 113]
    (.letOp (n := 129) (.out 0x109437 (movR64R64Effect 0x109437 14 8) (EffectPart.reads (.reg (.gpr 14)) [.gpr 8] []) (.reg (.gpr 14))) #v[97]
    (.letOp (n := 130) (.exec 0x109437 (fun s => s.RIP = 0x109437) (movR64R64Effect 0x109437 14 8) (Reg.operands [.gpr 8] [])) #v[97]
    (b_l1093a3_2)))))))))))))))))))))))))))))))))))))))

def bytes_l1093a3_1 : List UInt8 :=
  [0x48, 0xC1, 0xC6, 0x30, 0x48, 0x89, 0x74, 0x24, 0x78, 0x4D, 0x31, 0xD1, 0x4D, 0x31, 0xE8, 0x4C,
    0x31, 0xDA, 0x4C, 0x31, 0xF8, 0x4D, 0x89, 0xCC, 0x4D, 0x31, 0xE9, 0x49, 0x89, 0xD5, 0x4C, 0x31,
    0xFA, 0x49, 0x89, 0xDF, 0x49, 0xC1, 0xC7, 0x30, 0x4C, 0x31, 0xF1, 0x48, 0x89, 0xC6, 0x4C, 0x31,
    0xF0, 0x4C, 0x8B, 0x5C, 0x24, 0x78, 0x4C, 0x31, 0xDF, 0x49, 0xC1, 0xC4, 0x20, 0x4C, 0x31, 0xFB,
    0x4D, 0x89, 0xC6] ++ bytes_l1093a3_2

theorem code_l1093a3_1 : ∀ x ∈ codeRange 0x1093f7 bytes_l1093a3_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x93f7 67 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1093a3_2

@[cfg_block] def b_l1093a3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1093a3 (movR64M64Effect 0x1093a3 9 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 54) (.exec 0x1093a3 (LoadPre 0x1093a3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1093a3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1093a3 9 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1093a8 (movR64M64Effect 0x1093a8 8 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 56) (.exec 0x1093a8 (LoadPre 0x1093a8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1093a8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1093a8 8 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1093ad (movR64M64Effect 0x1093ad 2 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 58) (.exec 0x1093ad (LoadPre 0x1093ad (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1093ad + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1093ad 2 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x1093b2 (movR64R64Effect 0x1093b2 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 9] []) (.reg (.gpr 10))) #v[53]
    (.letOp (n := 60) (.exec 0x1093b2 (fun s => s.RIP = 0x1093b2) (movR64R64Effect 0x1093b2 10 9) (Reg.operands [.gpr 9] [])) #v[53]
    (.letOp (n := 61) (.out 0x1093b5 (rolR64Effect 0x1093b5 4 10 48) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[59]
    (.letOp (n := 62) (.exec 0x1093b5 (fun s => s.RIP = 0x1093b5) (rolR64Effect 0x1093b5 4 10 48) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[59]
    (.letOp (n := 63) (.out 0x1093b9 (movR64M64Effect 0x1093b9 0 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 64) (.exec 0x1093b9 (LoadPre 0x1093b9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1093b9 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1093b9 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x1093be (movR64R64Effect 0x1093be 13 8) (EffectPart.reads (.reg (.gpr 13)) [.gpr 8] []) (.reg (.gpr 13))) #v[55]
    (.letOp (n := 66) (.exec 0x1093be (fun s => s.RIP = 0x1093be) (movR64R64Effect 0x1093be 13 8) (Reg.operands [.gpr 8] [])) #v[55]
    (.letOp (n := 67) (.out 0x1093c1 (rolR64Effect 0x1093c1 4 13 48) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[65]
    (.letOp (n := 68) (.exec 0x1093c1 (fun s => s.RIP = 0x1093c1) (rolR64Effect 0x1093c1 4 13 48) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[65]
    (.letOp (n := 69) (.out 0x1093c5 (movR64M64Effect 0x1093c5 1 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 70) (.exec 0x1093c5 (LoadPre 0x1093c5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1093c5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1093c5 1 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.out 0x1093ca (movR64R64Effect 0x1093ca 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[57]
    (.letOp (n := 72) (.exec 0x1093ca (fun s => s.RIP = 0x1093ca) (movR64R64Effect 0x1093ca 6 2) (Reg.operands [.gpr 2] [])) #v[57]
    (.letOp (n := 73) (.out 0x1093cd (rolR64Effect 0x1093cd 4 6 48) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[71]
    (.letOp (n := 74) (.exec 0x1093cd (fun s => s.RIP = 0x1093cd) (rolR64Effect 0x1093cd 4 6 48) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[71]
    (.letOp (n := 75) (.out 0x1093d1 (movR64R64Effect 0x1093d1 11 6) (EffectPart.reads (.reg (.gpr 11)) [.gpr 6] []) (.reg (.gpr 11))) #v[73]
    (.letOp (n := 76) (.exec 0x1093d1 (fun s => s.RIP = 0x1093d1) (movR64R64Effect 0x1093d1 11 6) (Reg.operands [.gpr 6] [])) #v[73]
    (.letOp (n := 77) (.exec 0x1093d4 (StorePre 0x1093d4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1093d4 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1093d4 6 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[73, 4]
    (.letOp (n := 78) (.out 0x1093dc (movR64M64Effect 0x1093dc 7 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 79) (.exec 0x1093dc (LoadPre 0x1093dc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1093dc + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1093dc 7 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 80) (.out 0x1093e1 (movR64R64Effect 0x1093e1 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[63]
    (.letOp (n := 81) (.exec 0x1093e1 (fun s => s.RIP = 0x1093e1) (movR64R64Effect 0x1093e1 15 0) (Reg.operands [.gpr 0] [])) #v[63]
    (.letOp (n := 82) (.out 0x1093e4 (rolR64Effect 0x1093e4 4 15 48) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[80]
    (.letOp (n := 83) (.exec 0x1093e4 (fun s => s.RIP = 0x1093e4) (rolR64Effect 0x1093e4 4 15 48) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[80]
    (.letOp (n := 84) (.out 0x1093e8 (movR64M64Effect 0x1093e8 3 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 85) (.exec 0x1093e8 (LoadPre 0x1093e8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1093e8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1093e8 3 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 86) (.out 0x1093ed (movR64R64Effect 0x1093ed 14 1) (EffectPart.reads (.reg (.gpr 14)) [.gpr 1] []) (.reg (.gpr 14))) #v[69]
    (.letOp (n := 87) (.exec 0x1093ed (fun s => s.RIP = 0x1093ed) (movR64R64Effect 0x1093ed 14 1) (Reg.operands [.gpr 1] [])) #v[69]
    (.letOp (n := 88) (.out 0x1093f0 (rolR64Effect 0x1093f0 4 14 48) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[86]
    (.letOp (n := 89) (.exec 0x1093f0 (fun s => s.RIP = 0x1093f0) (rolR64Effect 0x1093f0 4 14 48) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[86]
    (.letOp (n := 90) (.out 0x1093f4 (movR64R64Effect 0x1093f4 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 7] []) (.reg (.gpr 6))) #v[78]
    (.letOp (n := 91) (.exec 0x1093f4 (fun s => s.RIP = 0x1093f4) (movR64R64Effect 0x1093f4 6 7) (Reg.operands [.gpr 7] [])) #v[78]
    (b_l1093a3_1)))))))))))))))))))))))))))))))))))))))

def bytes_l1093a3 : List UInt8 :=
  [0x4C, 0x8B, 0x4C, 0x24, 0x08, 0x4C, 0x8B, 0x44, 0x24, 0x10, 0x48, 0x8B, 0x54, 0x24, 0x18, 0x4D,
    0x89, 0xCA, 0x49, 0xC1, 0xC2, 0x30, 0x48, 0x8B, 0x44, 0x24, 0x20, 0x4D, 0x89, 0xC5, 0x49, 0xC1,
    0xC5, 0x30, 0x48, 0x8B, 0x4C, 0x24, 0x28, 0x48, 0x89, 0xD6, 0x48, 0xC1, 0xC6, 0x30, 0x49, 0x89,
    0xF3, 0x48, 0x89, 0xB4, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x7C, 0x24, 0x38, 0x49, 0x89,
    0xC7, 0x49, 0xC1, 0xC7, 0x30, 0x48, 0x8B, 0x5C, 0x24, 0x40, 0x49, 0x89, 0xCE, 0x49, 0xC1, 0xC6,
    0x30, 0x48, 0x89, 0xFE] ++ bytes_l1093a3_1

theorem code_l1093a3 : ∀ x ∈ codeRange 0x1093a3 bytes_l1093a3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x93a3 84 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1093a3_1

@[cfg_block] def b_l109509 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x109509 (StorePre 0x109509 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x109509 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x109509 (.sib 4 none 0 (.d8 0x40)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.exec 0x109512 (StorePre 0x109512 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x109512 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x109512 (.sib 4 none 0 (.d8 0x38)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x10951b (StorePre 0x10951b 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10951b + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10951b (.sib 4 none 0 (.d8 0x30)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.exec 0x109524 (StorePre 0x109524 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x109524 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x109524 (.sib 4 none 0 (.d8 0x28)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x10952d (StorePre 0x10952d 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10952d + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10952d (.sib 4 none 0 (.d8 0x20)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x109536 (StorePre 0x109536 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x109536 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x109536 (.sib 4 none 0 (.d8 0x18)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.exec 0x10953f (StorePre 0x10953f 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10953f + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10953f (.sib 4 none 0 (.d8 0x10)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.exec 0x109548 (StorePre 0x109548 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109548 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x109548 (.sib 4 none 0 (.d8 0x8)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x109551 (movR64M64Effect 0x109551 12 (.sib 4 none 0 (.d32 0xe8))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 62) (.exec 0x109551 (LoadPre 0x109551 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x109551 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x109551 12 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x109559 (testR64R64Effect 0x109559 12 12) (EffectPart.reads (.flag .ZF) [.gpr 12, .gpr 12] []) (.flag .ZF)) #v[61, 61]
    (.letOp (n := 64) (.exec 0x109559 (fun s => s.RIP = 0x109559) (testR64R64Effect 0x109559 12 12) (Reg.operands [.gpr 12, .gpr 12] [])) #v[61, 61]
    (.letOp (n := 65) (.out 0x10955c (movR64M64Effect 0x10955c 5 (.sib 4 none 0 (.d32 0xf0))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 66) (.exec 0x10955c (LoadPre 0x10955c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x10955c + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10955c 5 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.pure (condOp 4)) #v[63]
    (.terminate (.condBr (Fin.last 67) ⟨.l109961, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 65), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 61), (13, 13), (19, 63), (22, 22), (39, 39), (50, 50), (51, 51)] 68⟩ ⟨.l10956a, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 65), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 61), (13, 13), (19, 63), (22, 22), (39, 39), (50, 50), (51, 51)] 68⟩))))))))))))))))

def bytes_l109509 : List UInt8 :=
  [0x48, 0xC7, 0x44, 0x24, 0x40, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x38, 0x00, 0x00,
    0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x30, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x28,
    0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x20, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44,
    0x24, 0x18, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x10, 0x00, 0x00, 0x00, 0x00, 0x48,
    0xC7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00, 0x4C, 0x8B, 0xA4, 0x24, 0xE8, 0x00, 0x00, 0x00,
    0x4D, 0x85, 0xE4, 0x48, 0x8B, 0xAC, 0x24, 0xF0, 0x00, 0x00, 0x00, 0x0F, 0x84, 0xF7, 0x03, 0x00,
    0x00]

theorem code_l109509 : ∀ x ∈ codeRange 0x109509 bytes_l109509, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9509 97 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10956a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10956a (movR64Imm64Effect 0x10956a 0 0xffffffffffffffc) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 54) (.exec 0x10956a (fun s => s.RIP = 0x10956a) (movR64Imm64Effect 0x10956a 0 0xffffffffffffffc) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x109574 (movR64M64Effect 0x109574 1 (.sib 4 none 0 (.d32 0x140))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x109574 (LoadPre 0x109574 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x109574 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x109574 1 (.sib 4 none 0 (.d32 0x140))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x10957c (andR64R64Effect 0x10957c 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[55, 53]
    (.letOp (n := 58) (.exec 0x10957c (fun s => s.RIP = 0x10957c) (andR64R64Effect 0x10957c 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[55, 53]
    (.letOp (n := 59) (.out 0x10957f (shlR64Effect 0x10957f 4 1 4) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[57]
    (.letOp (n := 60) (.exec 0x10957f (fun s => s.RIP = 0x10957f) (shlR64Effect 0x10957f 4 1 4) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[57]
    (.letOp (n := 61) (.out 0x109583 (addR64R64Effect 0x109583 5 1) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 1] []) (.reg (.gpr 5))) #v[5, 59]
    (.letOp (n := 62) (.exec 0x109583 (fun s => s.RIP = 0x109583) (addR64R64Effect 0x109583 5 1) (Reg.operands [.gpr 5, .gpr 1] [])) #v[5, 59]
    (.letOp (n := 63) (.out 0x109586 (addR64R64Effect 0x109586 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[2, 59]
    (.letOp (n := 64) (.exec 0x109586 (fun s => s.RIP = 0x109586) (addR64R64Effect 0x109586 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[2, 59]
    (.letOp (n := 65) (.exec 0x109589 (StorePre 0x109589 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x109589 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x109589 2 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[63, 4]
    (.letOp (n := 66) (.out 0x109591 (shlR32Effect 0x109591 4 12 4) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[12]
    (.letOp (n := 67) (.exec 0x109591 (fun s => s.RIP = 0x109591) (shlR32Effect 0x109591 4 12 4) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[12]
    (.letOp (n := 68) (.out 0x109595 (movR64M64Effect 0x109595 3 (.sib 4 none 0 (.d32 0x150))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 69) (.exec 0x109595 (LoadPre 0x109595 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x150)) s (0x109595 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x109595 3 (.sib 4 none 0 (.d32 0x150))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.out 0x10959d (xorR32R32Effect 0x10959d 3 13 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 13] []) (.reg (.gpr 13))) #v[13, 13]
    (.letOp (n := 71) (.exec 0x10959d (fun s => s.RIP = 0x10959d) (xorR32R32Effect 0x10959d 3 13 13) (Reg.operands [.gpr 13, .gpr 13] [])) #v[13, 13]
    (.letOp (n := 72) (.out 0x1095a0 (leaR64Effect 0x1095a0 14 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 73) (.exec 0x1095a0 (fun s => s.RIP = 0x1095a0) (leaR64Effect 0x1095a0 14 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.out 0x1095a8 (leaR64Effect 0x1095a8 15 (.sib 4 none 0 (.d32 0x100))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 75) (.exec 0x1095a8 (fun s => s.RIP = 0x1095a8) (leaR64Effect 0x1095a8 15 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.br ⟨.l1095b0, RegMap.args [(0, 53), (1, 59), (2, 63), (3, 68), (4, 4), (5, 61), (9, 9), (12, 66), (13, 70), (14, 72), (15, 74), (22, 22), (39, 39), (50, 50), (51, 51)] 76⟩))))))))))))))))))))))))

def bytes_l10956a : List UInt8 :=
  [0x48, 0xB8, 0xFC, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x48, 0x8B, 0x8C, 0x24, 0x40, 0x01,
    0x00, 0x00, 0x48, 0x21, 0xC1, 0x48, 0xC1, 0xE1, 0x04, 0x48, 0x01, 0xCD, 0x48, 0x01, 0xCA, 0x48,
    0x89, 0x94, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x41, 0xC1, 0xE4, 0x04, 0x48, 0x8B, 0x9C, 0x24, 0x50,
    0x01, 0x00, 0x00, 0x45, 0x31, 0xED, 0x4C, 0x8D, 0xB4, 0x24, 0x98, 0x00, 0x00, 0x00, 0x4C, 0x8D,
    0xBC, 0x24, 0x00, 0x01, 0x00, 0x00]

theorem code_l10956a : ∀ x ∈ codeRange 0x10956a bytes_l10956a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x956a 70 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1095b0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1095b0 (movR32M32Effect 0x1095b0 0 (.base 9 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[9]
    (.letOp (n := 54) (.exec 0x1095b0 (LoadPre 0x1095b0 (fun s => AddrMode.addr (.base 9 (.d8 0x10)) s (0x1095b0 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x1095b0 0 (.base 9 (.d8 0x10))) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 55) (.out 0x1095b4 (movR64M64Effect 0x1095b4 1 (.base 9 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 9] []) (.reg (.gpr 1))) #v[9]
    (.letOp (n := 56) (.exec 0x1095b4 (LoadPre 0x1095b4 (fun s => AddrMode.addr (.base 9 .none) s (0x1095b4 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1095b4 1 (.base 9 .none)) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 57) (.out 0x1095b7 (movR32M32Effect 0x1095b7 2 (.base 9 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9] []) (.reg (.gpr 2))) #v[9]
    (.letOp (n := 58) (.exec 0x1095b7 (LoadPre 0x1095b7 (fun s => AddrMode.addr (.base 9 (.d8 0x8)) s (0x1095b7 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x1095b7 2 (.base 9 (.d8 0x8))) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 59) (.out 0x1095bb (movR32M32Effect 0x1095bb 6 (.base 9 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 9] []) (.reg (.gpr 6))) #v[9]
    (.letOp (n := 60) (.exec 0x1095bb (LoadPre 0x1095bb (fun s => AddrMode.addr (.base 9 (.d8 0xc)) s (0x1095bb + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x1095bb 6 (.base 9 (.d8 0xc))) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 61) (.out 0x1095bf (addR32R32Effect 0x1095bf 2 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[59, 53]
    (.letOp (n := 62) (.exec 0x1095bf (fun s => s.RIP = 0x1095bf) (addR32R32Effect 0x1095bf 2 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[59, 53]
    (.letOp (n := 63) (.out 0x1095c1 (bswapR32Effect 0x1095c1 2 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[61]
    (.letOp (n := 64) (.exec 0x1095c1 (fun s => s.RIP = 0x1095c1) (bswapR32Effect 0x1095c1 2 6) (Reg.operands [.gpr 6] [])) #v[61]
    (.letOp (n := 65) (.out 0x1095c3 (incR32Effect 0x1095c3 2 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 66) (.exec 0x1095c3 (fun s => s.RIP = 0x1095c3) (incR32Effect 0x1095c3 2 0) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 67) (.exec 0x1095c5 (StorePre 0x1095c5 4 (fun s => AddrMode.addr (.base 9 (.d8 0x10)) s (0x1095c5 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x1095c5 0 (.base 9 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 9] [])) #v[65, 9]
    (.letOp (n := 68) (.exec 0x1095c9 (StorePre 0x1095c9 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x1095c9 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1095c9 1 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 69) (.exec 0x1095d1 (StorePre 0x1095d1 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x1095d1 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x1095d1 2 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 70) (.exec 0x1095d8 (StorePre 0x1095d8 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x10c)) s (0x1095d8 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x1095d8 6 (.sib 4 none 0 (.d32 0x10c))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[63, 4]
    (.letOp (n := 71) (.out 0x1095df (movR64R64Effect 0x1095df 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 72) (.exec 0x1095df (fun s => s.RIP = 0x1095df) (movR64R64Effect 0x1095df 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 73) (.out 0x1095e2 (movR64R64Effect 0x1095e2 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[3]
    (.letOp (n := 74) (.exec 0x1095e2 (fun s => s.RIP = 0x1095e2) (movR64R64Effect 0x1095e2 6 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 75) (.out 0x1095e5 (movR64R64Effect 0x1095e5 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15] []) (.reg (.gpr 2))) #v[15]
    (.letOp (n := 76) (.exec 0x1095e5 (fun s => s.RIP = 0x1095e5) (movR64R64Effect 0x1095e5 2 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 77) (.out 0x1095e8 (callEffect (fun _ => 0x106960) 0x1095ed) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 78) (.exec 0x1095e8 (PushPre 0x1095e8 5) (callEffect (fun _ => 0x106960) 0x1095ed) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.const ⟨64, 0x1095ed⟩) #v[]
    (.terminate (.call ⟨.l106960, RegMap.args [(0, 65), (1, 55), (2, 75), (3, 3), (4, 77), (5, 5), (6, 73), (7, 71), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 80⟩ { target := .l1095ed, kept := #v[], arity := rfl, guard := some (Fin.last 79) }))))))))))))))))))))))))))))

def bytes_l1095b0 : List UInt8 :=
  [0x41, 0x8B, 0x41, 0x10, 0x49, 0x8B, 0x09, 0x41, 0x8B, 0x51, 0x08, 0x41, 0x8B, 0x71, 0x0C, 0x01,
    0xC6, 0x0F, 0xCE, 0xFF, 0xC0, 0x41, 0x89, 0x41, 0x10, 0x48, 0x89, 0x8C, 0x24, 0x00, 0x01, 0x00,
    0x00, 0x89, 0x94, 0x24, 0x08, 0x01, 0x00, 0x00, 0x89, 0xB4, 0x24, 0x0C, 0x01, 0x00, 0x00, 0x4C,
    0x89, 0xF7, 0x48, 0x89, 0xDE, 0x4C, 0x89, 0xFA, 0xE8, 0x73, 0xD3, 0xFF, 0xFF]

theorem code_l1095b0 : ∀ x ∈ codeRange 0x1095b0 bytes_l1095b0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x95b0 61 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1095ed : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1095ed (movR64M64Effect 0x1095ed 9 (.sib 4 none 0 (.d32 0xf8))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 54) (.exec 0x1095ed (LoadPre 0x1095ed (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x1095ed + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1095ed 9 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1095f5 (movR64M64Effect 0x1095f5 0 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 56) (.exec 0x1095f5 (LoadPre 0x1095f5 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x1095f5 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1095f5 0 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1095fd (movR64M64Effect 0x1095fd 1 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 58) (.exec 0x1095fd (LoadPre 0x1095fd (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x1095fd + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1095fd 1 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.exec 0x109605 (StorePre 0x109605 5 (fun s => AddrMode.addr (.sib 4 (some 13) 0 (.d8 0x10)) s (0x109605 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109605 1 (.sib 4 (some 13) 0 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 4, .gpr 13] [])) #v[57, 4, 13]
    (.letOp (n := 60) (.exec 0x10960a (StorePre 0x10960a 5 (fun s => AddrMode.addr (.sib 4 (some 13) 0 (.d8 0x8)) s (0x10960a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10960a 0 (.sib 4 (some 13) 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4, .gpr 13] [])) #v[55, 4, 13]
    (.letOp (n := 61) (.out 0x10960f (addR64Imm8Effect 0x10960f 13 0x10) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[13]
    (.letOp (n := 62) (.exec 0x10960f (fun s => s.RIP = 0x10960f) (addR64Imm8Effect 0x10960f 13 0x10) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 63) (.out 0x109613 (cmpR64R64Effect 0x109613 12 13) (EffectPart.reads (.flag .ZF) [.gpr 12, .gpr 13] []) (.flag .ZF)) #v[12, 61]
    (.letOp (n := 64) (.exec 0x109613 (fun s => s.RIP = 0x109613) (cmpR64R64Effect 0x109613 12 13) (Reg.operands [.gpr 12, .gpr 13] [])) #v[12, 61]
    (.letOp (n := 65) (.pure (condOp 5)) #v[63]
    (.terminate (.condBr (Fin.last 65) ⟨.l1095b0, RegMap.args [(0, 55), (1, 57), (3, 3), (4, 4), (5, 5), (9, 53), (12, 12), (13, 61), (14, 14), (15, 15), (19, 63), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩ ⟨.l109618, RegMap.args [(0, 55), (1, 57), (3, 3), (4, 4), (5, 5), (9, 53), (12, 12), (13, 61), (14, 14), (15, 15), (19, 63), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩))))))))))))))

def bytes_l1095ed : List UInt8 :=
  [0x4C, 0x8B, 0x8C, 0x24, 0xF8, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00,
    0x48, 0x8B, 0x8C, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x4A, 0x89, 0x4C, 0x2C, 0x10, 0x4A, 0x89, 0x44,
    0x2C, 0x08, 0x49, 0x83, 0xC5, 0x10, 0x4D, 0x39, 0xEC, 0x75, 0x98]

theorem code_l1095ed : ∀ x ∈ codeRange 0x1095ed bytes_l1095ed, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x95ed 43 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109618_3 : Block Op Label signature Reg.count 153 :=
  .letOp (n := 153) (.pure (condOp 4)) #v[151]
    (.terminate (.condBr (Fin.last 153) ⟨.l109961, RegMap.args [(0, 149), (1, 121), (2, 97), (3, 95), (4, 4), (5, 101), (6, 134), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 113), (13, 117), (14, 105), (15, 109), (19, 151), (22, 22), (39, 39), (50, 50), (51, 51)] 154⟩ ⟨.l109739, RegMap.args [(0, 149), (1, 121), (2, 97), (3, 95), (4, 4), (5, 101), (6, 134), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 113), (13, 117), (14, 105), (15, 109), (19, 151), (22, 22), (39, 39), (50, 50), (51, 51)] 154⟩))

def bytes_l109618_3 : List UInt8 :=
  [0x0F, 0x84, 0x28, 0x02, 0x00, 0x00]

theorem code_l109618_3 : ∀ x ∈ codeRange 0x109733 bytes_l109618_3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9733 6 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109618_2 : Block Op Label signature Reg.count 128 :=
  .letOp (n := 128) (.out 0x1096d9 (movzxR32M8Effect 0x1096d9 5 6 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 129) (.exec 0x1096d9 (LoadPre 0x1096d9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1096d9 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1096d9 5 6 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 130) (.exec 0x1096de (StorePre 0x1096de 4 (fun s => AddrMode.addr (.base 0 (.d8 0x1)) s (0x1096de + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1096de 4 6 (.base 0 (.d8 0x1))) (Reg.operands [.gpr 6, .gpr 0] [])) #v[128, 123]
    (.letOp (n := 131) (.out 0x1096e2 (movzxR32M8Effect 0x1096e2 8 6 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 132) (.exec 0x1096e2 (LoadPre 0x1096e2 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1096e2 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1096e2 8 6 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 133) (.exec 0x1096ea (StorePre 0x1096ea 4 (fun s => AddrMode.addr (.base 0 (.d8 0x2)) s (0x1096ea + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1096ea 4 6 (.base 0 (.d8 0x2))) (Reg.operands [.gpr 6, .gpr 0] [])) #v[131, 123]
    (.letOp (n := 134) (.out 0x1096ee (movzxR32M8Effect 0x1096ee 8 6 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 135) (.exec 0x1096ee (LoadPre 0x1096ee (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x1096ee + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1096ee 8 6 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 136) (.exec 0x1096f6 (StorePre 0x1096f6 4 (fun s => AddrMode.addr (.base 0 (.d8 0x3)) s (0x1096f6 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1096f6 4 6 (.base 0 (.d8 0x3))) (Reg.operands [.gpr 6, .gpr 0] [])) #v[134, 123]
    (.letOp (n := 137) (.exec 0x1096fa (StorePre 0x1096fa 4 (fun s => AddrMode.addr (.base 0 (.d8 0x4)) s (0x1096fa + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1096fa 4 7 (.base 0 (.d8 0x4))) (Reg.operands [.gpr 7, .gpr 0] [])) #v[75, 123]
    (.letOp (n := 138) (.exec 0x1096fe (StorePre 0x1096fe 4 (fun s => AddrMode.addr (.base 0 (.d8 0x5)) s (0x1096fe + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1096fe 4 8 (.base 0 (.d8 0x5))) (Reg.operands [.gpr 8, .gpr 0] [])) #v[79, 123]
    (.letOp (n := 139) (.exec 0x109702 (StorePre 0x109702 4 (fun s => AddrMode.addr (.base 0 (.d8 0x6)) s (0x109702 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109702 4 9 (.base 0 (.d8 0x6))) (Reg.operands [.gpr 9, .gpr 0] [])) #v[83, 123]
    (.letOp (n := 140) (.exec 0x109706 (StorePre 0x109706 4 (fun s => AddrMode.addr (.base 0 (.d8 0x7)) s (0x109706 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109706 4 10 (.base 0 (.d8 0x7))) (Reg.operands [.gpr 10, .gpr 0] [])) #v[87, 123]
    (.letOp (n := 141) (.exec 0x10970a (StorePre 0x10970a 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x10970a + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10970a 4 11 (.base 0 (.d8 0x8))) (Reg.operands [.gpr 11, .gpr 0] [])) #v[91, 123]
    (.letOp (n := 142) (.exec 0x10970e (StorePre 0x10970e 3 (fun s => AddrMode.addr (.base 0 (.d8 0x9)) s (0x10970e + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10970e 3 3 (.base 0 (.d8 0x9))) (Reg.operands [.gpr 3, .gpr 0] [])) #v[95, 123]
    (.letOp (n := 143) (.exec 0x109711 (StorePre 0x109711 4 (fun s => AddrMode.addr (.base 0 (.d8 0xa)) s (0x109711 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109711 4 5 (.base 0 (.d8 0xa))) (Reg.operands [.gpr 5, .gpr 0] [])) #v[101, 123]
    (.letOp (n := 144) (.exec 0x109715 (StorePre 0x109715 4 (fun s => AddrMode.addr (.base 0 (.d8 0xb)) s (0x109715 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109715 4 14 (.base 0 (.d8 0xb))) (Reg.operands [.gpr 14, .gpr 0] [])) #v[105, 123]
    (.letOp (n := 145) (.exec 0x109719 (StorePre 0x109719 4 (fun s => AddrMode.addr (.base 0 (.d8 0xc)) s (0x109719 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109719 4 15 (.base 0 (.d8 0xc))) (Reg.operands [.gpr 15, .gpr 0] [])) #v[109, 123]
    (.letOp (n := 146) (.exec 0x10971d (StorePre 0x10971d 4 (fun s => AddrMode.addr (.base 0 (.d8 0xd)) s (0x10971d + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10971d 4 12 (.base 0 (.d8 0xd))) (Reg.operands [.gpr 12, .gpr 0] [])) #v[113, 123]
    (.letOp (n := 147) (.exec 0x109721 (StorePre 0x109721 4 (fun s => AddrMode.addr (.base 0 (.d8 0xe)) s (0x109721 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109721 4 13 (.base 0 (.d8 0xe))) (Reg.operands [.gpr 13, .gpr 0] [])) #v[117, 123]
    (.letOp (n := 148) (.exec 0x109725 (StorePre 0x109725 3 (fun s => AddrMode.addr (.base 0 (.d8 0xf)) s (0x109725 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x109725 3 1 (.base 0 (.d8 0xf))) (Reg.operands [.gpr 1, .gpr 0] [])) #v[121, 123]
    (.letOp (n := 149) (.out 0x109728 (movR64M64Effect 0x109728 0 (.sib 4 none 0 (.d32 0xe8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 150) (.exec 0x109728 (LoadPre 0x109728 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x109728 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x109728 0 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 151) (.out 0x109730 (cmpR32Imm8Effect 0x109730 3 0 0x1) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[149]
    (.letOp (n := 152) (.exec 0x109730 (fun s => s.RIP = 0x109730) (cmpR32Imm8Effect 0x109730 3 0 0x1) (Reg.operands [.gpr 0] [])) #v[149]
    (b_l109618_3)))))))))))))))))))))))))

def bytes_l109618_2 : List UInt8 :=
  [0x0F, 0xB6, 0x74, 0x24, 0x78, 0x40, 0x88, 0x70, 0x01, 0x0F, 0xB6, 0xB4, 0x24, 0x88, 0x00, 0x00,
    0x00, 0x40, 0x88, 0x70, 0x02, 0x0F, 0xB6, 0xB4, 0x24, 0x90, 0x00, 0x00, 0x00, 0x40, 0x88, 0x70,
    0x03, 0x40, 0x88, 0x78, 0x04, 0x44, 0x88, 0x40, 0x05, 0x44, 0x88, 0x48, 0x06, 0x44, 0x88, 0x50,
    0x07, 0x44, 0x88, 0x58, 0x08, 0x88, 0x58, 0x09, 0x40, 0x88, 0x68, 0x0A, 0x44, 0x88, 0x70, 0x0B,
    0x44, 0x88, 0x78, 0x0C, 0x44, 0x88, 0x60, 0x0D, 0x44, 0x88, 0x68, 0x0E, 0x88, 0x48, 0x0F, 0x48,
    0x8B, 0x84, 0x24, 0xE8, 0x00, 0x00, 0x00, 0x83, 0xF8, 0x01] ++ bytes_l109618_3

theorem code_l109618_2 : ∀ x ∈ codeRange 0x1096d9 bytes_l109618_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x96d9 90 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l109618_3

@[cfg_block] def b_l109618_1 : Block Op Label signature Reg.count 89 :=
  .letOp (n := 89) (.out 0x109678 (movzxR32M8Effect 0x109678 6 11 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 90) (.exec 0x109678 (LoadPre 0x109678 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x109678 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x109678 6 11 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 91) (.out 0x10967e (xorR8M8Effect 0x10967e 4 11 (.base 5 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 5] []) (.reg (.gpr 11))) #v[89, 5]
    (.letOp (n := 92) (.exec 0x10967e (LoadPre 0x10967e (fun s => AddrMode.addr (.base 5 (.d8 0x8)) s (0x10967e + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10967e 4 11 (.base 5 (.d8 0x8))) (Reg.operands [.gpr 11, .gpr 5] [])) #v[89, 5]
    (.letOp (n := 93) (.out 0x109682 (movzxR32M8Effect 0x109682 5 3 (.sib 4 none 0 (.d8 0x11))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 94) (.exec 0x109682 (LoadPre 0x109682 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x11)) s (0x109682 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109682 5 3 (.sib 4 none 0 (.d8 0x11))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 95) (.out 0x109687 (xorR8M8Effect 0x109687 3 3 (.base 5 (.d8 0x9))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 5] []) (.reg (.gpr 3))) #v[93, 5]
    (.letOp (n := 96) (.exec 0x109687 (LoadPre 0x109687 (fun s => AddrMode.addr (.base 5 (.d8 0x9)) s (0x109687 + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x109687 3 3 (.base 5 (.d8 0x9))) (Reg.operands [.gpr 3, .gpr 5] [])) #v[93, 5]
    (.letOp (n := 97) (.out 0x10968a (movR64R64Effect 0x10968a 2 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5] []) (.reg (.gpr 2))) #v[5]
    (.letOp (n := 98) (.exec 0x10968a (fun s => s.RIP = 0x10968a) (movR64R64Effect 0x10968a 2 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 99) (.out 0x10968d (movzxR32M8Effect 0x10968d 5 5 (.sib 4 none 0 (.d8 0x12))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 100) (.exec 0x10968d (LoadPre 0x10968d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x12)) s (0x10968d + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10968d 5 5 (.sib 4 none 0 (.d8 0x12))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 101) (.out 0x109692 (xorR8M8Effect 0x109692 4 5 (.base 2 (.d8 0xa))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 2] []) (.reg (.gpr 5))) #v[99, 97]
    (.letOp (n := 102) (.exec 0x109692 (LoadPre 0x109692 (fun s => AddrMode.addr (.base 2 (.d8 0xa)) s (0x109692 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x109692 4 5 (.base 2 (.d8 0xa))) (Reg.operands [.gpr 5, .gpr 2] [])) #v[99, 97]
    (.letOp (n := 103) (.out 0x109696 (movzxR32M8Effect 0x109696 6 14 (.sib 4 none 0 (.d8 0x13))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 104) (.exec 0x109696 (LoadPre 0x109696 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x13)) s (0x109696 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x109696 6 14 (.sib 4 none 0 (.d8 0x13))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 105) (.out 0x10969c (xorR8M8Effect 0x10969c 4 14 (.base 2 (.d8 0xb))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 2] []) (.reg (.gpr 14))) #v[103, 97]
    (.letOp (n := 106) (.exec 0x10969c (LoadPre 0x10969c (fun s => AddrMode.addr (.base 2 (.d8 0xb)) s (0x10969c + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10969c 4 14 (.base 2 (.d8 0xb))) (Reg.operands [.gpr 14, .gpr 2] [])) #v[103, 97]
    (.letOp (n := 107) (.out 0x1096a0 (movzxR32M8Effect 0x1096a0 6 15 (.sib 4 none 0 (.d8 0x14))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 108) (.exec 0x1096a0 (LoadPre 0x1096a0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x1096a0 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1096a0 6 15 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 109) (.out 0x1096a6 (xorR8M8Effect 0x1096a6 4 15 (.base 2 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 2] []) (.reg (.gpr 15))) #v[107, 97]
    (.letOp (n := 110) (.exec 0x1096a6 (LoadPre 0x1096a6 (fun s => AddrMode.addr (.base 2 (.d8 0xc)) s (0x1096a6 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1096a6 4 15 (.base 2 (.d8 0xc))) (Reg.operands [.gpr 15, .gpr 2] [])) #v[107, 97]
    (.letOp (n := 111) (.out 0x1096aa (movzxR32M8Effect 0x1096aa 6 12 (.sib 4 none 0 (.d8 0x15))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 112) (.exec 0x1096aa (LoadPre 0x1096aa (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x15)) s (0x1096aa + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1096aa 6 12 (.sib 4 none 0 (.d8 0x15))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 113) (.out 0x1096b0 (xorR8M8Effect 0x1096b0 4 12 (.base 2 (.d8 0xd))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 2] []) (.reg (.gpr 12))) #v[111, 97]
    (.letOp (n := 114) (.exec 0x1096b0 (LoadPre 0x1096b0 (fun s => AddrMode.addr (.base 2 (.d8 0xd)) s (0x1096b0 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1096b0 4 12 (.base 2 (.d8 0xd))) (Reg.operands [.gpr 12, .gpr 2] [])) #v[111, 97]
    (.letOp (n := 115) (.out 0x1096b4 (movzxR32M8Effect 0x1096b4 6 13 (.sib 4 none 0 (.d8 0x16))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 116) (.exec 0x1096b4 (LoadPre 0x1096b4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x16)) s (0x1096b4 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1096b4 6 13 (.sib 4 none 0 (.d8 0x16))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 117) (.out 0x1096ba (xorR8M8Effect 0x1096ba 4 13 (.base 2 (.d8 0xe))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 2] []) (.reg (.gpr 13))) #v[115, 97]
    (.letOp (n := 118) (.exec 0x1096ba (LoadPre 0x1096ba (fun s => AddrMode.addr (.base 2 (.d8 0xe)) s (0x1096ba + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1096ba 4 13 (.base 2 (.d8 0xe))) (Reg.operands [.gpr 13, .gpr 2] [])) #v[115, 97]
    (.letOp (n := 119) (.out 0x1096be (movzxR32M8Effect 0x1096be 5 1 (.sib 4 none 0 (.d8 0x17))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 120) (.exec 0x1096be (LoadPre 0x1096be (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x17)) s (0x1096be + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1096be 5 1 (.sib 4 none 0 (.d8 0x17))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 121) (.out 0x1096c3 (xorR8M8Effect 0x1096c3 3 1 (.base 2 (.d8 0xf))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[119, 97]
    (.letOp (n := 122) (.exec 0x1096c3 (LoadPre 0x1096c3 (fun s => AddrMode.addr (.base 2 (.d8 0xf)) s (0x1096c3 + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x1096c3 3 1 (.base 2 (.d8 0xf))) (Reg.operands [.gpr 1, .gpr 2] [])) #v[119, 97]
    (.letOp (n := 123) (.out 0x1096c6 (movR64M64Effect 0x1096c6 0 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 124) (.exec 0x1096c6 (LoadPre 0x1096c6 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x1096c6 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1096c6 0 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 125) (.out 0x1096ce (movzxR32M8Effect 0x1096ce 8 6 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 126) (.exec 0x1096ce (LoadPre 0x1096ce (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1096ce + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1096ce 8 6 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 127) (.exec 0x1096d6 (StorePre 0x1096d6 3 (fun s => AddrMode.addr (.base 0 .none) s (0x1096d6 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x1096d6 3 6 (.base 0 .none)) (Reg.operands [.gpr 6, .gpr 0] [])) #v[125, 123]
    (b_l109618_2)))))))))))))))))))))))))))))))))))))))

def bytes_l109618_1 : List UInt8 :=
  [0x44, 0x0F, 0xB6, 0x5C, 0x24, 0x10, 0x44, 0x32, 0x5D, 0x08, 0x0F, 0xB6, 0x5C, 0x24, 0x11, 0x32,
    0x5D, 0x09, 0x48, 0x89, 0xEA, 0x0F, 0xB6, 0x6C, 0x24, 0x12, 0x40, 0x32, 0x6A, 0x0A, 0x44, 0x0F,
    0xB6, 0x74, 0x24, 0x13, 0x44, 0x32, 0x72, 0x0B, 0x44, 0x0F, 0xB6, 0x7C, 0x24, 0x14, 0x44, 0x32,
    0x7A, 0x0C, 0x44, 0x0F, 0xB6, 0x64, 0x24, 0x15, 0x44, 0x32, 0x62, 0x0D, 0x44, 0x0F, 0xB6, 0x6C,
    0x24, 0x16, 0x44, 0x32, 0x6A, 0x0E, 0x0F, 0xB6, 0x4C, 0x24, 0x17, 0x32, 0x4A, 0x0F, 0x48, 0x8B,
    0x84, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x0F, 0xB6, 0xB4, 0x24, 0x80, 0x00, 0x00, 0x00, 0x40, 0x88,
    0x30] ++ bytes_l109618_2

theorem code_l109618_1 : ∀ x ∈ codeRange 0x109678 bytes_l109618_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x9678 97 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l109618_2

@[cfg_block] def b_l109618 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x109618 (movzxR32M8Effect 0x109618 5 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x109618 (LoadPre 0x109618 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109618 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109618 5 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10961d (movzxR32M8Effect 0x10961d 5 1 (.sib 4 none 0 (.d8 0x9))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x10961d (LoadPre 0x10961d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x9)) s (0x10961d + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10961d 5 1 (.sib 4 none 0 (.d8 0x9))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x109622 (xorR8M8Effect 0x109622 3 0 (.base 5 (.d8 0x0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[53, 5]
    (.letOp (n := 58) (.exec 0x109622 (LoadPre 0x109622 (fun s => AddrMode.addr (.base 5 (.d8 0x0)) s (0x109622 + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x109622 3 0 (.base 5 (.d8 0x0))) (Reg.operands [.gpr 0, .gpr 5] [])) #v[53, 5]
    (.letOp (n := 59) (.exec 0x109625 (StorePre 0x109625 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x109625 + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x109625 7 0 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 60) (.out 0x10962c (xorR8M8Effect 0x10962c 3 1 (.base 5 (.d8 0x1))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 5] []) (.reg (.gpr 1))) #v[55, 5]
    (.letOp (n := 61) (.exec 0x10962c (LoadPre 0x10962c (fun s => AddrMode.addr (.base 5 (.d8 0x1)) s (0x10962c + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x10962c 3 1 (.base 5 (.d8 0x1))) (Reg.operands [.gpr 1, .gpr 5] [])) #v[55, 5]
    (.letOp (n := 62) (.exec 0x10962f (StorePre 0x10962f 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10962f + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10962f 4 1 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[60, 4]
    (.letOp (n := 63) (.out 0x109633 (movzxR32M8Effect 0x109633 5 0 (.sib 4 none 0 (.d8 0xa))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 64) (.exec 0x109633 (LoadPre 0x109633 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xa)) s (0x109633 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109633 5 0 (.sib 4 none 0 (.d8 0xa))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x109638 (xorR8M8Effect 0x109638 3 0 (.base 5 (.d8 0x2))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[63, 5]
    (.letOp (n := 66) (.exec 0x109638 (LoadPre 0x109638 (fun s => AddrMode.addr (.base 5 (.d8 0x2)) s (0x109638 + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x109638 3 0 (.base 5 (.d8 0x2))) (Reg.operands [.gpr 0, .gpr 5] [])) #v[63, 5]
    (.letOp (n := 67) (.exec 0x10963b (StorePre 0x10963b 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10963b + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x10963b 7 0 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x109642 (movzxR32M8Effect 0x109642 5 0 (.sib 4 none 0 (.d8 0xb))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 69) (.exec 0x109642 (LoadPre 0x109642 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xb)) s (0x109642 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109642 5 0 (.sib 4 none 0 (.d8 0xb))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.out 0x109647 (xorR8M8Effect 0x109647 3 0 (.base 5 (.d8 0x3))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[68, 5]
    (.letOp (n := 71) (.exec 0x109647 (LoadPre 0x109647 (fun s => AddrMode.addr (.base 5 (.d8 0x3)) s (0x109647 + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x109647 3 0 (.base 5 (.d8 0x3))) (Reg.operands [.gpr 0, .gpr 5] [])) #v[68, 5]
    (.letOp (n := 72) (.exec 0x10964a (StorePre 0x10964a 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x10964a + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x10964a 7 0 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[70, 4]
    (.letOp (n := 73) (.out 0x109651 (movzxR32M8Effect 0x109651 5 7 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 74) (.exec 0x109651 (LoadPre 0x109651 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x109651 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109651 5 7 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.out 0x109656 (xorR8M8Effect 0x109656 4 7 (.base 5 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 5] []) (.reg (.gpr 7))) #v[73, 5]
    (.letOp (n := 76) (.exec 0x109656 (LoadPre 0x109656 (fun s => AddrMode.addr (.base 5 (.d8 0x4)) s (0x109656 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x109656 4 7 (.base 5 (.d8 0x4))) (Reg.operands [.gpr 7, .gpr 5] [])) #v[73, 5]
    (.letOp (n := 77) (.out 0x10965a (movzxR32M8Effect 0x10965a 6 8 (.sib 4 none 0 (.d8 0xd))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 78) (.exec 0x10965a (LoadPre 0x10965a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xd)) s (0x10965a + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x10965a 6 8 (.sib 4 none 0 (.d8 0xd))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.out 0x109660 (xorR8M8Effect 0x109660 4 8 (.base 5 (.d8 0x5))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 5] []) (.reg (.gpr 8))) #v[77, 5]
    (.letOp (n := 80) (.exec 0x109660 (LoadPre 0x109660 (fun s => AddrMode.addr (.base 5 (.d8 0x5)) s (0x109660 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x109660 4 8 (.base 5 (.d8 0x5))) (Reg.operands [.gpr 8, .gpr 5] [])) #v[77, 5]
    (.letOp (n := 81) (.out 0x109664 (movzxR32M8Effect 0x109664 6 9 (.sib 4 none 0 (.d8 0xe))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 82) (.exec 0x109664 (LoadPre 0x109664 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x109664 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x109664 6 9 (.sib 4 none 0 (.d8 0xe))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 83) (.out 0x10966a (xorR8M8Effect 0x10966a 4 9 (.base 5 (.d8 0x6))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 5] []) (.reg (.gpr 9))) #v[81, 5]
    (.letOp (n := 84) (.exec 0x10966a (LoadPre 0x10966a (fun s => AddrMode.addr (.base 5 (.d8 0x6)) s (0x10966a + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10966a 4 9 (.base 5 (.d8 0x6))) (Reg.operands [.gpr 9, .gpr 5] [])) #v[81, 5]
    (.letOp (n := 85) (.out 0x10966e (movzxR32M8Effect 0x10966e 6 10 (.sib 4 none 0 (.d8 0xf))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 86) (.exec 0x10966e (LoadPre 0x10966e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x10966e + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x10966e 6 10 (.sib 4 none 0 (.d8 0xf))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 87) (.out 0x109674 (xorR8M8Effect 0x109674 4 10 (.base 5 (.d8 0x7))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 5] []) (.reg (.gpr 10))) #v[85, 5]
    (.letOp (n := 88) (.exec 0x109674 (LoadPre 0x109674 (fun s => AddrMode.addr (.base 5 (.d8 0x7)) s (0x109674 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x109674 4 10 (.base 5 (.d8 0x7))) (Reg.operands [.gpr 10, .gpr 5] [])) #v[85, 5]
    (b_l109618_1))))))))))))))))))))))))))))))))))))

def bytes_l109618 : List UInt8 :=
  [0x0F, 0xB6, 0x44, 0x24, 0x08, 0x0F, 0xB6, 0x4C, 0x24, 0x09, 0x32, 0x45, 0x00, 0x88, 0x84, 0x24,
    0x80, 0x00, 0x00, 0x00, 0x32, 0x4D, 0x01, 0x88, 0x4C, 0x24, 0x78, 0x0F, 0xB6, 0x44, 0x24, 0x0A,
    0x32, 0x45, 0x02, 0x88, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, 0x0F, 0xB6, 0x44, 0x24, 0x0B, 0x32,
    0x45, 0x03, 0x88, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00, 0x0F, 0xB6, 0x7C, 0x24, 0x0C, 0x40, 0x32,
    0x7D, 0x04, 0x44, 0x0F, 0xB6, 0x44, 0x24, 0x0D, 0x44, 0x32, 0x45, 0x05, 0x44, 0x0F, 0xB6, 0x4C,
    0x24, 0x0E, 0x44, 0x32, 0x4D, 0x06, 0x44, 0x0F, 0xB6, 0x54, 0x24, 0x0F, 0x44, 0x32, 0x55, 0x07] ++ bytes_l109618_1

theorem code_l109618 : ∀ x ∈ codeRange 0x109618 bytes_l109618, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x9618 96 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l109618_1

@[cfg_block] def b_l109739_3 : Block Op Label signature Reg.count 153 :=
  .letOp (n := 153) (.pure (condOp 4)) #v[151]
    (.terminate (.condBr (Fin.last 153) ⟨.l109961, RegMap.args [(0, 119), (1, 131), (2, 2), (3, 95), (4, 4), (5, 99), (6, 136), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (13, 115), (14, 103), (15, 107), (19, 151), (22, 22), (39, 39), (50, 50), (51, 51)] 154⟩ ⟨.l109867, RegMap.args [(0, 119), (1, 131), (2, 2), (3, 95), (4, 4), (5, 99), (6, 136), (7, 75), (8, 79), (9, 83), (10, 87), (11, 91), (12, 111), (13, 115), (14, 103), (15, 107), (19, 151), (22, 22), (39, 39), (50, 50), (51, 51)] 154⟩))

def bytes_l109739_3 : List UInt8 :=
  [0x0F, 0x84, 0xFA, 0x00, 0x00, 0x00]

theorem code_l109739_3 : ∀ x ∈ codeRange 0x109861 bytes_l109739_3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9861 6 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109739_2 : Block Op Label signature Reg.count 128 :=
  .letOp (n := 128) (.out 0x109802 (movzxR32M8Effect 0x109802 5 6 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 129) (.exec 0x109802 (LoadPre 0x109802 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x109802 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109802 5 6 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 130) (.exec 0x109807 (StorePre 0x109807 4 (fun s => AddrMode.addr (.base 1 (.d8 0x11)) s (0x109807 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109807 4 6 (.base 1 (.d8 0x11))) (Reg.operands [.gpr 6, .gpr 1] [])) #v[128, 126]
    (.letOp (n := 131) (.out 0x10980b (movR64M64Effect 0x10980b 1 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 132) (.exec 0x10980b (LoadPre 0x10980b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x10980b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10980b 1 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 133) (.out 0x109813 (movzxR32M8Effect 0x109813 8 6 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 134) (.exec 0x109813 (LoadPre 0x109813 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x109813 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x109813 8 6 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 135) (.exec 0x10981b (StorePre 0x10981b 4 (fun s => AddrMode.addr (.base 1 (.d8 0x12)) s (0x10981b + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10981b 4 6 (.base 1 (.d8 0x12))) (Reg.operands [.gpr 6, .gpr 1] [])) #v[133, 131]
    (.letOp (n := 136) (.out 0x10981f (movzxR32M8Effect 0x10981f 8 6 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 137) (.exec 0x10981f (LoadPre 0x10981f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x10981f + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x10981f 8 6 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 138) (.exec 0x109827 (StorePre 0x109827 4 (fun s => AddrMode.addr (.base 1 (.d8 0x13)) s (0x109827 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109827 4 6 (.base 1 (.d8 0x13))) (Reg.operands [.gpr 6, .gpr 1] [])) #v[136, 131]
    (.letOp (n := 139) (.exec 0x10982b (StorePre 0x10982b 4 (fun s => AddrMode.addr (.base 1 (.d8 0x14)) s (0x10982b + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10982b 4 7 (.base 1 (.d8 0x14))) (Reg.operands [.gpr 7, .gpr 1] [])) #v[75, 131]
    (.letOp (n := 140) (.exec 0x10982f (StorePre 0x10982f 4 (fun s => AddrMode.addr (.base 1 (.d8 0x15)) s (0x10982f + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10982f 4 8 (.base 1 (.d8 0x15))) (Reg.operands [.gpr 8, .gpr 1] [])) #v[79, 131]
    (.letOp (n := 141) (.exec 0x109833 (StorePre 0x109833 4 (fun s => AddrMode.addr (.base 1 (.d8 0x16)) s (0x109833 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109833 4 9 (.base 1 (.d8 0x16))) (Reg.operands [.gpr 9, .gpr 1] [])) #v[83, 131]
    (.letOp (n := 142) (.exec 0x109837 (StorePre 0x109837 4 (fun s => AddrMode.addr (.base 1 (.d8 0x17)) s (0x109837 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109837 4 10 (.base 1 (.d8 0x17))) (Reg.operands [.gpr 10, .gpr 1] [])) #v[87, 131]
    (.letOp (n := 143) (.exec 0x10983b (StorePre 0x10983b 4 (fun s => AddrMode.addr (.base 1 (.d8 0x18)) s (0x10983b + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10983b 4 11 (.base 1 (.d8 0x18))) (Reg.operands [.gpr 11, .gpr 1] [])) #v[91, 131]
    (.letOp (n := 144) (.exec 0x10983f (StorePre 0x10983f 3 (fun s => AddrMode.addr (.base 1 (.d8 0x19)) s (0x10983f + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10983f 3 3 (.base 1 (.d8 0x19))) (Reg.operands [.gpr 3, .gpr 1] [])) #v[95, 131]
    (.letOp (n := 145) (.exec 0x109842 (StorePre 0x109842 4 (fun s => AddrMode.addr (.base 1 (.d8 0x1a)) s (0x109842 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109842 4 5 (.base 1 (.d8 0x1a))) (Reg.operands [.gpr 5, .gpr 1] [])) #v[99, 131]
    (.letOp (n := 146) (.exec 0x109846 (StorePre 0x109846 4 (fun s => AddrMode.addr (.base 1 (.d8 0x1b)) s (0x109846 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109846 4 14 (.base 1 (.d8 0x1b))) (Reg.operands [.gpr 14, .gpr 1] [])) #v[103, 131]
    (.letOp (n := 147) (.exec 0x10984a (StorePre 0x10984a 4 (fun s => AddrMode.addr (.base 1 (.d8 0x1c)) s (0x10984a + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10984a 4 15 (.base 1 (.d8 0x1c))) (Reg.operands [.gpr 15, .gpr 1] [])) #v[107, 131]
    (.letOp (n := 148) (.exec 0x10984e (StorePre 0x10984e 4 (fun s => AddrMode.addr (.base 1 (.d8 0x1d)) s (0x10984e + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10984e 4 12 (.base 1 (.d8 0x1d))) (Reg.operands [.gpr 12, .gpr 1] [])) #v[111, 131]
    (.letOp (n := 149) (.exec 0x109852 (StorePre 0x109852 4 (fun s => AddrMode.addr (.base 1 (.d8 0x1e)) s (0x109852 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109852 4 13 (.base 1 (.d8 0x1e))) (Reg.operands [.gpr 13, .gpr 1] [])) #v[115, 131]
    (.letOp (n := 150) (.exec 0x109856 (StorePre 0x109856 3 (fun s => AddrMode.addr (.base 1 (.d8 0x1f)) s (0x109856 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x109856 3 0 (.base 1 (.d8 0x1f))) (Reg.operands [.gpr 0, .gpr 1] [])) #v[119, 131]
    (.letOp (n := 151) (.out 0x109859 (cmpMImm8Effect 0x109859 8 32 (.sib 4 none 0 (.d32 0xe8)) 0x2) (EffectPart.reads (.flag .ZF) [.gpr 4] []) (.flag .ZF)) #v[4]
    (.letOp (n := 152) (.exec 0x109859 (LoadPre 0x109859 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x109859 + BitVec.ofNat 64 8)) 4) (cmpMImm8Effect 0x109859 8 32 (.sib 4 none 0 (.d32 0xe8)) 0x2) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l109739_3)))))))))))))))))))))))))

def bytes_l109739_2 : List UInt8 :=
  [0x0F, 0xB6, 0x74, 0x24, 0x78, 0x40, 0x88, 0x71, 0x11, 0x48, 0x8B, 0x8C, 0x24, 0xD8, 0x00, 0x00,
    0x00, 0x0F, 0xB6, 0xB4, 0x24, 0x88, 0x00, 0x00, 0x00, 0x40, 0x88, 0x71, 0x12, 0x0F, 0xB6, 0xB4,
    0x24, 0x90, 0x00, 0x00, 0x00, 0x40, 0x88, 0x71, 0x13, 0x40, 0x88, 0x79, 0x14, 0x44, 0x88, 0x41,
    0x15, 0x44, 0x88, 0x49, 0x16, 0x44, 0x88, 0x51, 0x17, 0x44, 0x88, 0x59, 0x18, 0x88, 0x59, 0x19,
    0x40, 0x88, 0x69, 0x1A, 0x44, 0x88, 0x71, 0x1B, 0x44, 0x88, 0x79, 0x1C, 0x44, 0x88, 0x61, 0x1D,
    0x44, 0x88, 0x69, 0x1E, 0x88, 0x41, 0x1F, 0x83, 0xBC, 0x24, 0xE8, 0x00, 0x00, 0x00, 0x02] ++ bytes_l109739_3

theorem code_l109739_2 : ∀ x ∈ codeRange 0x109802 bytes_l109739_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x9802 95 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l109739_3

@[cfg_block] def b_l109739_1 : Block Op Label signature Reg.count 89 :=
  .letOp (n := 89) (.out 0x10979b (movzxR32M8Effect 0x10979b 6 11 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 90) (.exec 0x10979b (LoadPre 0x10979b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10979b + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x10979b 6 11 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 91) (.out 0x1097a1 (xorR8M8Effect 0x1097a1 4 11 (.base 2 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 2] []) (.reg (.gpr 11))) #v[89, 2]
    (.letOp (n := 92) (.exec 0x1097a1 (LoadPre 0x1097a1 (fun s => AddrMode.addr (.base 2 (.d8 0x18)) s (0x1097a1 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1097a1 4 11 (.base 2 (.d8 0x18))) (Reg.operands [.gpr 11, .gpr 2] [])) #v[89, 2]
    (.letOp (n := 93) (.out 0x1097a5 (movzxR32M8Effect 0x1097a5 5 3 (.sib 4 none 0 (.d8 0x21))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 94) (.exec 0x1097a5 (LoadPre 0x1097a5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x21)) s (0x1097a5 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1097a5 5 3 (.sib 4 none 0 (.d8 0x21))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 95) (.out 0x1097aa (xorR8M8Effect 0x1097aa 3 3 (.base 2 (.d8 0x19))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 2] []) (.reg (.gpr 3))) #v[93, 2]
    (.letOp (n := 96) (.exec 0x1097aa (LoadPre 0x1097aa (fun s => AddrMode.addr (.base 2 (.d8 0x19)) s (0x1097aa + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x1097aa 3 3 (.base 2 (.d8 0x19))) (Reg.operands [.gpr 3, .gpr 2] [])) #v[93, 2]
    (.letOp (n := 97) (.out 0x1097ad (movzxR32M8Effect 0x1097ad 5 5 (.sib 4 none 0 (.d8 0x22))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 98) (.exec 0x1097ad (LoadPre 0x1097ad (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x22)) s (0x1097ad + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1097ad 5 5 (.sib 4 none 0 (.d8 0x22))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 99) (.out 0x1097b2 (xorR8M8Effect 0x1097b2 4 5 (.base 2 (.d8 0x1a))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 2] []) (.reg (.gpr 5))) #v[97, 2]
    (.letOp (n := 100) (.exec 0x1097b2 (LoadPre 0x1097b2 (fun s => AddrMode.addr (.base 2 (.d8 0x1a)) s (0x1097b2 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1097b2 4 5 (.base 2 (.d8 0x1a))) (Reg.operands [.gpr 5, .gpr 2] [])) #v[97, 2]
    (.letOp (n := 101) (.out 0x1097b6 (movzxR32M8Effect 0x1097b6 6 14 (.sib 4 none 0 (.d8 0x23))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 102) (.exec 0x1097b6 (LoadPre 0x1097b6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x23)) s (0x1097b6 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1097b6 6 14 (.sib 4 none 0 (.d8 0x23))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 103) (.out 0x1097bc (xorR8M8Effect 0x1097bc 4 14 (.base 2 (.d8 0x1b))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 2] []) (.reg (.gpr 14))) #v[101, 2]
    (.letOp (n := 104) (.exec 0x1097bc (LoadPre 0x1097bc (fun s => AddrMode.addr (.base 2 (.d8 0x1b)) s (0x1097bc + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1097bc 4 14 (.base 2 (.d8 0x1b))) (Reg.operands [.gpr 14, .gpr 2] [])) #v[101, 2]
    (.letOp (n := 105) (.out 0x1097c0 (movzxR32M8Effect 0x1097c0 6 15 (.sib 4 none 0 (.d8 0x24))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 106) (.exec 0x1097c0 (LoadPre 0x1097c0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x1097c0 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1097c0 6 15 (.sib 4 none 0 (.d8 0x24))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 107) (.out 0x1097c6 (xorR8M8Effect 0x1097c6 4 15 (.base 2 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 2] []) (.reg (.gpr 15))) #v[105, 2]
    (.letOp (n := 108) (.exec 0x1097c6 (LoadPre 0x1097c6 (fun s => AddrMode.addr (.base 2 (.d8 0x1c)) s (0x1097c6 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1097c6 4 15 (.base 2 (.d8 0x1c))) (Reg.operands [.gpr 15, .gpr 2] [])) #v[105, 2]
    (.letOp (n := 109) (.out 0x1097ca (movzxR32M8Effect 0x1097ca 6 12 (.sib 4 none 0 (.d8 0x25))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 110) (.exec 0x1097ca (LoadPre 0x1097ca (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x25)) s (0x1097ca + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1097ca 6 12 (.sib 4 none 0 (.d8 0x25))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 111) (.out 0x1097d0 (xorR8M8Effect 0x1097d0 4 12 (.base 2 (.d8 0x1d))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 2] []) (.reg (.gpr 12))) #v[109, 2]
    (.letOp (n := 112) (.exec 0x1097d0 (LoadPre 0x1097d0 (fun s => AddrMode.addr (.base 2 (.d8 0x1d)) s (0x1097d0 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1097d0 4 12 (.base 2 (.d8 0x1d))) (Reg.operands [.gpr 12, .gpr 2] [])) #v[109, 2]
    (.letOp (n := 113) (.out 0x1097d4 (movzxR32M8Effect 0x1097d4 6 13 (.sib 4 none 0 (.d8 0x26))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 114) (.exec 0x1097d4 (LoadPre 0x1097d4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x26)) s (0x1097d4 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1097d4 6 13 (.sib 4 none 0 (.d8 0x26))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 115) (.out 0x1097da (xorR8M8Effect 0x1097da 4 13 (.base 2 (.d8 0x1e))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 2] []) (.reg (.gpr 13))) #v[113, 2]
    (.letOp (n := 116) (.exec 0x1097da (LoadPre 0x1097da (fun s => AddrMode.addr (.base 2 (.d8 0x1e)) s (0x1097da + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1097da 4 13 (.base 2 (.d8 0x1e))) (Reg.operands [.gpr 13, .gpr 2] [])) #v[113, 2]
    (.letOp (n := 117) (.out 0x1097de (movzxR32M8Effect 0x1097de 5 0 (.sib 4 none 0 (.d8 0x27))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 118) (.exec 0x1097de (LoadPre 0x1097de (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x27)) s (0x1097de + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1097de 5 0 (.sib 4 none 0 (.d8 0x27))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 119) (.out 0x1097e3 (xorR8M8Effect 0x1097e3 3 0 (.base 2 (.d8 0x1f))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[117, 2]
    (.letOp (n := 120) (.exec 0x1097e3 (LoadPre 0x1097e3 (fun s => AddrMode.addr (.base 2 (.d8 0x1f)) s (0x1097e3 + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x1097e3 3 0 (.base 2 (.d8 0x1f))) (Reg.operands [.gpr 0, .gpr 2] [])) #v[117, 2]
    (.letOp (n := 121) (.out 0x1097e6 (movR64M64Effect 0x1097e6 1 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 122) (.exec 0x1097e6 (LoadPre 0x1097e6 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x1097e6 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1097e6 1 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 123) (.out 0x1097ee (movzxR32M8Effect 0x1097ee 8 6 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 124) (.exec 0x1097ee (LoadPre 0x1097ee (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1097ee + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x1097ee 8 6 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 125) (.exec 0x1097f6 (StorePre 0x1097f6 4 (fun s => AddrMode.addr (.base 1 (.d8 0x10)) s (0x1097f6 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1097f6 4 6 (.base 1 (.d8 0x10))) (Reg.operands [.gpr 6, .gpr 1] [])) #v[123, 121]
    (.letOp (n := 126) (.out 0x1097fa (movR64M64Effect 0x1097fa 1 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 127) (.exec 0x1097fa (LoadPre 0x1097fa (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x1097fa + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1097fa 1 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l109739_2)))))))))))))))))))))))))))))))))))))))

def bytes_l109739_1 : List UInt8 :=
  [0x44, 0x0F, 0xB6, 0x5C, 0x24, 0x20, 0x44, 0x32, 0x5A, 0x18, 0x0F, 0xB6, 0x5C, 0x24, 0x21, 0x32,
    0x5A, 0x19, 0x0F, 0xB6, 0x6C, 0x24, 0x22, 0x40, 0x32, 0x6A, 0x1A, 0x44, 0x0F, 0xB6, 0x74, 0x24,
    0x23, 0x44, 0x32, 0x72, 0x1B, 0x44, 0x0F, 0xB6, 0x7C, 0x24, 0x24, 0x44, 0x32, 0x7A, 0x1C, 0x44,
    0x0F, 0xB6, 0x64, 0x24, 0x25, 0x44, 0x32, 0x62, 0x1D, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x26, 0x44,
    0x32, 0x6A, 0x1E, 0x0F, 0xB6, 0x44, 0x24, 0x27, 0x32, 0x42, 0x1F, 0x48, 0x8B, 0x8C, 0x24, 0xD8,
    0x00, 0x00, 0x00, 0x0F, 0xB6, 0xB4, 0x24, 0x80, 0x00, 0x00, 0x00, 0x40, 0x88, 0x71, 0x10, 0x48,
    0x8B, 0x8C, 0x24, 0xD8, 0x00, 0x00, 0x00] ++ bytes_l109739_2

theorem code_l109739_1 : ∀ x ∈ codeRange 0x10979b bytes_l109739_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x979b 103 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l109739_2

@[cfg_block] def b_l109739 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x109739 (movzxR32M8Effect 0x109739 5 1 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x109739 (LoadPre 0x109739 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x109739 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109739 5 1 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10973e (movzxR32M8Effect 0x10973e 5 6 (.sib 4 none 0 (.d8 0x19))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 56) (.exec 0x10973e (LoadPre 0x10973e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x19)) s (0x10973e + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10973e 5 6 (.sib 4 none 0 (.d8 0x19))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x109743 (xorR8M8Effect 0x109743 3 1 (.base 2 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[53, 2]
    (.letOp (n := 58) (.exec 0x109743 (LoadPre 0x109743 (fun s => AddrMode.addr (.base 2 (.d8 0x10)) s (0x109743 + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x109743 3 1 (.base 2 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 2] [])) #v[53, 2]
    (.letOp (n := 59) (.exec 0x109746 (StorePre 0x109746 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x109746 + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x109746 7 1 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 60) (.out 0x10974d (xorR8M8Effect 0x10974d 4 6 (.base 2 (.d8 0x11))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[55, 2]
    (.letOp (n := 61) (.exec 0x10974d (LoadPre 0x10974d (fun s => AddrMode.addr (.base 2 (.d8 0x11)) s (0x10974d + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10974d 4 6 (.base 2 (.d8 0x11))) (Reg.operands [.gpr 6, .gpr 2] [])) #v[55, 2]
    (.letOp (n := 62) (.exec 0x109751 (StorePre 0x109751 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x109751 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x109751 5 6 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[60, 4]
    (.letOp (n := 63) (.out 0x109756 (movzxR32M8Effect 0x109756 5 1 (.sib 4 none 0 (.d8 0x1a))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 64) (.exec 0x109756 (LoadPre 0x109756 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1a)) s (0x109756 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109756 5 1 (.sib 4 none 0 (.d8 0x1a))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x10975b (xorR8M8Effect 0x10975b 3 1 (.base 2 (.d8 0x12))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[63, 2]
    (.letOp (n := 66) (.exec 0x10975b (LoadPre 0x10975b (fun s => AddrMode.addr (.base 2 (.d8 0x12)) s (0x10975b + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x10975b 3 1 (.base 2 (.d8 0x12))) (Reg.operands [.gpr 1, .gpr 2] [])) #v[63, 2]
    (.letOp (n := 67) (.exec 0x10975e (StorePre 0x10975e 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10975e + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x10975e 7 1 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x109765 (movzxR32M8Effect 0x109765 5 1 (.sib 4 none 0 (.d8 0x1b))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 69) (.exec 0x109765 (LoadPre 0x109765 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1b)) s (0x109765 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109765 5 1 (.sib 4 none 0 (.d8 0x1b))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.out 0x10976a (xorR8M8Effect 0x10976a 3 1 (.base 2 (.d8 0x13))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[68, 2]
    (.letOp (n := 71) (.exec 0x10976a (LoadPre 0x10976a (fun s => AddrMode.addr (.base 2 (.d8 0x13)) s (0x10976a + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x10976a 3 1 (.base 2 (.d8 0x13))) (Reg.operands [.gpr 1, .gpr 2] [])) #v[68, 2]
    (.letOp (n := 72) (.exec 0x10976d (StorePre 0x10976d 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x10976d + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x10976d 7 1 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[70, 4]
    (.letOp (n := 73) (.out 0x109774 (movzxR32M8Effect 0x109774 5 7 (.sib 4 none 0 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 74) (.exec 0x109774 (LoadPre 0x109774 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x109774 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109774 5 7 (.sib 4 none 0 (.d8 0x1c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.out 0x109779 (xorR8M8Effect 0x109779 4 7 (.base 2 (.d8 0x14))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2] []) (.reg (.gpr 7))) #v[73, 2]
    (.letOp (n := 76) (.exec 0x109779 (LoadPre 0x109779 (fun s => AddrMode.addr (.base 2 (.d8 0x14)) s (0x109779 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x109779 4 7 (.base 2 (.d8 0x14))) (Reg.operands [.gpr 7, .gpr 2] [])) #v[73, 2]
    (.letOp (n := 77) (.out 0x10977d (movzxR32M8Effect 0x10977d 6 8 (.sib 4 none 0 (.d8 0x1d))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 78) (.exec 0x10977d (LoadPre 0x10977d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1d)) s (0x10977d + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x10977d 6 8 (.sib 4 none 0 (.d8 0x1d))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.out 0x109783 (xorR8M8Effect 0x109783 4 8 (.base 2 (.d8 0x15))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2] []) (.reg (.gpr 8))) #v[77, 2]
    (.letOp (n := 80) (.exec 0x109783 (LoadPre 0x109783 (fun s => AddrMode.addr (.base 2 (.d8 0x15)) s (0x109783 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x109783 4 8 (.base 2 (.d8 0x15))) (Reg.operands [.gpr 8, .gpr 2] [])) #v[77, 2]
    (.letOp (n := 81) (.out 0x109787 (movzxR32M8Effect 0x109787 6 9 (.sib 4 none 0 (.d8 0x1e))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 82) (.exec 0x109787 (LoadPre 0x109787 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1e)) s (0x109787 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x109787 6 9 (.sib 4 none 0 (.d8 0x1e))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 83) (.out 0x10978d (xorR8M8Effect 0x10978d 4 9 (.base 2 (.d8 0x16))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2] []) (.reg (.gpr 9))) #v[81, 2]
    (.letOp (n := 84) (.exec 0x10978d (LoadPre 0x10978d (fun s => AddrMode.addr (.base 2 (.d8 0x16)) s (0x10978d + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10978d 4 9 (.base 2 (.d8 0x16))) (Reg.operands [.gpr 9, .gpr 2] [])) #v[81, 2]
    (.letOp (n := 85) (.out 0x109791 (movzxR32M8Effect 0x109791 6 10 (.sib 4 none 0 (.d8 0x1f))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 86) (.exec 0x109791 (LoadPre 0x109791 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1f)) s (0x109791 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x109791 6 10 (.sib 4 none 0 (.d8 0x1f))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 87) (.out 0x109797 (xorR8M8Effect 0x109797 4 10 (.base 2 (.d8 0x17))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2] []) (.reg (.gpr 10))) #v[85, 2]
    (.letOp (n := 88) (.exec 0x109797 (LoadPre 0x109797 (fun s => AddrMode.addr (.base 2 (.d8 0x17)) s (0x109797 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x109797 4 10 (.base 2 (.d8 0x17))) (Reg.operands [.gpr 10, .gpr 2] [])) #v[85, 2]
    (b_l109739_1))))))))))))))))))))))))))))))))))))

def bytes_l109739 : List UInt8 :=
  [0x0F, 0xB6, 0x4C, 0x24, 0x18, 0x0F, 0xB6, 0x74, 0x24, 0x19, 0x32, 0x4A, 0x10, 0x88, 0x8C, 0x24,
    0x80, 0x00, 0x00, 0x00, 0x40, 0x32, 0x72, 0x11, 0x40, 0x88, 0x74, 0x24, 0x78, 0x0F, 0xB6, 0x4C,
    0x24, 0x1A, 0x32, 0x4A, 0x12, 0x88, 0x8C, 0x24, 0x88, 0x00, 0x00, 0x00, 0x0F, 0xB6, 0x4C, 0x24,
    0x1B, 0x32, 0x4A, 0x13, 0x88, 0x8C, 0x24, 0x90, 0x00, 0x00, 0x00, 0x0F, 0xB6, 0x7C, 0x24, 0x1C,
    0x40, 0x32, 0x7A, 0x14, 0x44, 0x0F, 0xB6, 0x44, 0x24, 0x1D, 0x44, 0x32, 0x42, 0x15, 0x44, 0x0F,
    0xB6, 0x4C, 0x24, 0x1E, 0x44, 0x32, 0x4A, 0x16, 0x44, 0x0F, 0xB6, 0x54, 0x24, 0x1F, 0x44, 0x32,
    0x52, 0x17] ++ bytes_l109739_1

theorem code_l109739 : ∀ x ∈ codeRange 0x109739 bytes_l109739, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x9739 98 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l109739_1

@[cfg_block] def b_l109867_2 : Block Op Label signature Reg.count 128 :=
  .letOp (n := 128) (.out 0x109924 (movzxR32M8Effect 0x109924 8 2 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 129) (.exec 0x109924 (LoadPre 0x109924 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x109924 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x109924 8 2 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 130) (.exec 0x10992c (StorePre 0x10992c 3 (fun s => AddrMode.addr (.base 0 (.d8 0x22)) s (0x10992c + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10992c 3 2 (.base 0 (.d8 0x22))) (Reg.operands [.gpr 2, .gpr 0] [])) #v[128, 55]
    (.letOp (n := 131) (.exec 0x10992f (StorePre 0x10992f 4 (fun s => AddrMode.addr (.base 0 (.d8 0x23)) s (0x10992f + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10992f 4 6 (.base 0 (.d8 0x23))) (Reg.operands [.gpr 6, .gpr 0] [])) #v[72, 55]
    (.letOp (n := 132) (.exec 0x109933 (StorePre 0x109933 4 (fun s => AddrMode.addr (.base 0 (.d8 0x24)) s (0x109933 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109933 4 7 (.base 0 (.d8 0x24))) (Reg.operands [.gpr 7, .gpr 0] [])) #v[76, 55]
    (.letOp (n := 133) (.exec 0x109937 (StorePre 0x109937 4 (fun s => AddrMode.addr (.base 0 (.d8 0x25)) s (0x109937 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109937 4 8 (.base 0 (.d8 0x25))) (Reg.operands [.gpr 8, .gpr 0] [])) #v[80, 55]
    (.letOp (n := 134) (.exec 0x10993b (StorePre 0x10993b 4 (fun s => AddrMode.addr (.base 0 (.d8 0x26)) s (0x10993b + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10993b 4 9 (.base 0 (.d8 0x26))) (Reg.operands [.gpr 9, .gpr 0] [])) #v[84, 55]
    (.letOp (n := 135) (.exec 0x10993f (StorePre 0x10993f 4 (fun s => AddrMode.addr (.base 0 (.d8 0x27)) s (0x10993f + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10993f 4 10 (.base 0 (.d8 0x27))) (Reg.operands [.gpr 10, .gpr 0] [])) #v[88, 55]
    (.letOp (n := 136) (.exec 0x109943 (StorePre 0x109943 4 (fun s => AddrMode.addr (.base 0 (.d8 0x28)) s (0x109943 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109943 4 11 (.base 0 (.d8 0x28))) (Reg.operands [.gpr 11, .gpr 0] [])) #v[92, 55]
    (.letOp (n := 137) (.exec 0x109947 (StorePre 0x109947 3 (fun s => AddrMode.addr (.base 0 (.d8 0x29)) s (0x109947 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x109947 3 3 (.base 0 (.d8 0x29))) (Reg.operands [.gpr 3, .gpr 0] [])) #v[96, 55]
    (.letOp (n := 138) (.exec 0x10994a (StorePre 0x10994a 4 (fun s => AddrMode.addr (.base 0 (.d8 0x2a)) s (0x10994a + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10994a 4 5 (.base 0 (.d8 0x2a))) (Reg.operands [.gpr 5, .gpr 0] [])) #v[100, 55]
    (.letOp (n := 139) (.exec 0x10994e (StorePre 0x10994e 4 (fun s => AddrMode.addr (.base 0 (.d8 0x2b)) s (0x10994e + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10994e 4 14 (.base 0 (.d8 0x2b))) (Reg.operands [.gpr 14, .gpr 0] [])) #v[104, 55]
    (.letOp (n := 140) (.exec 0x109952 (StorePre 0x109952 4 (fun s => AddrMode.addr (.base 0 (.d8 0x2c)) s (0x109952 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109952 4 15 (.base 0 (.d8 0x2c))) (Reg.operands [.gpr 15, .gpr 0] [])) #v[108, 55]
    (.letOp (n := 141) (.exec 0x109956 (StorePre 0x109956 4 (fun s => AddrMode.addr (.base 0 (.d8 0x2d)) s (0x109956 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109956 4 12 (.base 0 (.d8 0x2d))) (Reg.operands [.gpr 12, .gpr 0] [])) #v[112, 55]
    (.letOp (n := 142) (.exec 0x10995a (StorePre 0x10995a 4 (fun s => AddrMode.addr (.base 0 (.d8 0x2e)) s (0x10995a + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10995a 4 13 (.base 0 (.d8 0x2e))) (Reg.operands [.gpr 13, .gpr 0] [])) #v[116, 55]
    (.letOp (n := 143) (.exec 0x10995e (StorePre 0x10995e 3 (fun s => AddrMode.addr (.base 0 (.d8 0x2f)) s (0x10995e + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10995e 3 1 (.base 0 (.d8 0x2f))) (Reg.operands [.gpr 1, .gpr 0] [])) #v[120, 55]
    (.terminate (.br ⟨.l109961, RegMap.args [(0, 55), (1, 120), (2, 128), (3, 96), (4, 4), (5, 100), (6, 72), (7, 76), (8, 80), (9, 84), (10, 88), (11, 92), (12, 112), (13, 116), (14, 104), (15, 108), (22, 22), (39, 39), (50, 50), (51, 51)] 144⟩)))))))))))))))))

def bytes_l109867_2 : List UInt8 :=
  [0x0F, 0xB6, 0x94, 0x24, 0x88, 0x00, 0x00, 0x00, 0x88, 0x50, 0x22, 0x40, 0x88, 0x70, 0x23, 0x40,
    0x88, 0x78, 0x24, 0x44, 0x88, 0x40, 0x25, 0x44, 0x88, 0x48, 0x26, 0x44, 0x88, 0x50, 0x27, 0x44,
    0x88, 0x58, 0x28, 0x88, 0x58, 0x29, 0x40, 0x88, 0x68, 0x2A, 0x44, 0x88, 0x70, 0x2B, 0x44, 0x88,
    0x78, 0x2C, 0x44, 0x88, 0x60, 0x2D, 0x44, 0x88, 0x68, 0x2E, 0x88, 0x48, 0x2F]

theorem code_l109867_2 : ∀ x ∈ codeRange 0x109924 bytes_l109867_2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9924 61 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109867_1 : Block Op Label signature Reg.count 90 :=
  .letOp (n := 90) (.out 0x1098c6 (movzxR32M8Effect 0x1098c6 6 11 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 91) (.exec 0x1098c6 (LoadPre 0x1098c6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1098c6 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1098c6 6 11 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 92) (.out 0x1098cc (xorR8M8Effect 0x1098cc 4 11 (.base 2 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 2] []) (.reg (.gpr 11))) #v[90, 2]
    (.letOp (n := 93) (.exec 0x1098cc (LoadPre 0x1098cc (fun s => AddrMode.addr (.base 2 (.d8 0x28)) s (0x1098cc + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1098cc 4 11 (.base 2 (.d8 0x28))) (Reg.operands [.gpr 11, .gpr 2] [])) #v[90, 2]
    (.letOp (n := 94) (.out 0x1098d0 (movzxR32M8Effect 0x1098d0 5 3 (.sib 4 none 0 (.d8 0x31))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 95) (.exec 0x1098d0 (LoadPre 0x1098d0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x31)) s (0x1098d0 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1098d0 5 3 (.sib 4 none 0 (.d8 0x31))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 96) (.out 0x1098d5 (xorR8M8Effect 0x1098d5 3 3 (.base 2 (.d8 0x29))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 2] []) (.reg (.gpr 3))) #v[94, 2]
    (.letOp (n := 97) (.exec 0x1098d5 (LoadPre 0x1098d5 (fun s => AddrMode.addr (.base 2 (.d8 0x29)) s (0x1098d5 + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x1098d5 3 3 (.base 2 (.d8 0x29))) (Reg.operands [.gpr 3, .gpr 2] [])) #v[94, 2]
    (.letOp (n := 98) (.out 0x1098d8 (movzxR32M8Effect 0x1098d8 5 5 (.sib 4 none 0 (.d8 0x32))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 99) (.exec 0x1098d8 (LoadPre 0x1098d8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x32)) s (0x1098d8 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1098d8 5 5 (.sib 4 none 0 (.d8 0x32))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 100) (.out 0x1098dd (xorR8M8Effect 0x1098dd 4 5 (.base 2 (.d8 0x2a))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 2] []) (.reg (.gpr 5))) #v[98, 2]
    (.letOp (n := 101) (.exec 0x1098dd (LoadPre 0x1098dd (fun s => AddrMode.addr (.base 2 (.d8 0x2a)) s (0x1098dd + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1098dd 4 5 (.base 2 (.d8 0x2a))) (Reg.operands [.gpr 5, .gpr 2] [])) #v[98, 2]
    (.letOp (n := 102) (.out 0x1098e1 (movzxR32M8Effect 0x1098e1 6 14 (.sib 4 none 0 (.d8 0x33))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 103) (.exec 0x1098e1 (LoadPre 0x1098e1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x33)) s (0x1098e1 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1098e1 6 14 (.sib 4 none 0 (.d8 0x33))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 104) (.out 0x1098e7 (xorR8M8Effect 0x1098e7 4 14 (.base 2 (.d8 0x2b))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 2] []) (.reg (.gpr 14))) #v[102, 2]
    (.letOp (n := 105) (.exec 0x1098e7 (LoadPre 0x1098e7 (fun s => AddrMode.addr (.base 2 (.d8 0x2b)) s (0x1098e7 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1098e7 4 14 (.base 2 (.d8 0x2b))) (Reg.operands [.gpr 14, .gpr 2] [])) #v[102, 2]
    (.letOp (n := 106) (.out 0x1098eb (movzxR32M8Effect 0x1098eb 6 15 (.sib 4 none 0 (.d8 0x34))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 107) (.exec 0x1098eb (LoadPre 0x1098eb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x1098eb + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1098eb 6 15 (.sib 4 none 0 (.d8 0x34))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 108) (.out 0x1098f1 (xorR8M8Effect 0x1098f1 4 15 (.base 2 (.d8 0x2c))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 2] []) (.reg (.gpr 15))) #v[106, 2]
    (.letOp (n := 109) (.exec 0x1098f1 (LoadPre 0x1098f1 (fun s => AddrMode.addr (.base 2 (.d8 0x2c)) s (0x1098f1 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1098f1 4 15 (.base 2 (.d8 0x2c))) (Reg.operands [.gpr 15, .gpr 2] [])) #v[106, 2]
    (.letOp (n := 110) (.out 0x1098f5 (movzxR32M8Effect 0x1098f5 6 12 (.sib 4 none 0 (.d8 0x35))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 111) (.exec 0x1098f5 (LoadPre 0x1098f5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x35)) s (0x1098f5 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1098f5 6 12 (.sib 4 none 0 (.d8 0x35))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 112) (.out 0x1098fb (xorR8M8Effect 0x1098fb 4 12 (.base 2 (.d8 0x2d))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 2] []) (.reg (.gpr 12))) #v[110, 2]
    (.letOp (n := 113) (.exec 0x1098fb (LoadPre 0x1098fb (fun s => AddrMode.addr (.base 2 (.d8 0x2d)) s (0x1098fb + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1098fb 4 12 (.base 2 (.d8 0x2d))) (Reg.operands [.gpr 12, .gpr 2] [])) #v[110, 2]
    (.letOp (n := 114) (.out 0x1098ff (movzxR32M8Effect 0x1098ff 6 13 (.sib 4 none 0 (.d8 0x36))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 115) (.exec 0x1098ff (LoadPre 0x1098ff (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x36)) s (0x1098ff + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1098ff 6 13 (.sib 4 none 0 (.d8 0x36))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 116) (.out 0x109905 (xorR8M8Effect 0x109905 4 13 (.base 2 (.d8 0x2e))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 2] []) (.reg (.gpr 13))) #v[114, 2]
    (.letOp (n := 117) (.exec 0x109905 (LoadPre 0x109905 (fun s => AddrMode.addr (.base 2 (.d8 0x2e)) s (0x109905 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x109905 4 13 (.base 2 (.d8 0x2e))) (Reg.operands [.gpr 13, .gpr 2] [])) #v[114, 2]
    (.letOp (n := 118) (.out 0x109909 (movzxR32M8Effect 0x109909 5 1 (.sib 4 none 0 (.d8 0x37))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 119) (.exec 0x109909 (LoadPre 0x109909 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x37)) s (0x109909 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109909 5 1 (.sib 4 none 0 (.d8 0x37))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 120) (.out 0x10990e (xorR8M8Effect 0x10990e 3 1 (.base 2 (.d8 0x2f))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[118, 2]
    (.letOp (n := 121) (.exec 0x10990e (LoadPre 0x10990e (fun s => AddrMode.addr (.base 2 (.d8 0x2f)) s (0x10990e + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x10990e 3 1 (.base 2 (.d8 0x2f))) (Reg.operands [.gpr 1, .gpr 2] [])) #v[118, 2]
    (.letOp (n := 122) (.out 0x109911 (movzxR32M8Effect 0x109911 8 2 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 123) (.exec 0x109911 (LoadPre 0x109911 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x109911 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x109911 8 2 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 124) (.exec 0x109919 (StorePre 0x109919 3 (fun s => AddrMode.addr (.base 0 (.d8 0x20)) s (0x109919 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x109919 3 2 (.base 0 (.d8 0x20))) (Reg.operands [.gpr 2, .gpr 0] [])) #v[122, 55]
    (.letOp (n := 125) (.out 0x10991c (movzxR32M8Effect 0x10991c 5 2 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 126) (.exec 0x10991c (LoadPre 0x10991c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10991c + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10991c 5 2 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 127) (.exec 0x109921 (StorePre 0x109921 3 (fun s => AddrMode.addr (.base 0 (.d8 0x21)) s (0x109921 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x109921 3 2 (.base 0 (.d8 0x21))) (Reg.operands [.gpr 2, .gpr 0] [])) #v[125, 55]
    (b_l109867_2))))))))))))))))))))))))))))))))))))))

def bytes_l109867_1 : List UInt8 :=
  [0x44, 0x0F, 0xB6, 0x5C, 0x24, 0x30, 0x44, 0x32, 0x5A, 0x28, 0x0F, 0xB6, 0x5C, 0x24, 0x31, 0x32,
    0x5A, 0x29, 0x0F, 0xB6, 0x6C, 0x24, 0x32, 0x40, 0x32, 0x6A, 0x2A, 0x44, 0x0F, 0xB6, 0x74, 0x24,
    0x33, 0x44, 0x32, 0x72, 0x2B, 0x44, 0x0F, 0xB6, 0x7C, 0x24, 0x34, 0x44, 0x32, 0x7A, 0x2C, 0x44,
    0x0F, 0xB6, 0x64, 0x24, 0x35, 0x44, 0x32, 0x62, 0x2D, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x36, 0x44,
    0x32, 0x6A, 0x2E, 0x0F, 0xB6, 0x4C, 0x24, 0x37, 0x32, 0x4A, 0x2F, 0x0F, 0xB6, 0x94, 0x24, 0x80,
    0x00, 0x00, 0x00, 0x88, 0x50, 0x20, 0x0F, 0xB6, 0x54, 0x24, 0x78, 0x88, 0x50, 0x21] ++ bytes_l109867_2

theorem code_l109867_1 : ∀ x ∈ codeRange 0x1098c6 bytes_l109867_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x98c6 94 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l109867_2

@[cfg_block] def b_l109867 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x109867 (movzxR32M8Effect 0x109867 5 6 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 54) (.exec 0x109867 (LoadPre 0x109867 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x109867 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109867 5 6 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10986c (movR64R64Effect 0x10986c 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[1]
    (.letOp (n := 56) (.exec 0x10986c (fun s => s.RIP = 0x10986c) (movR64R64Effect 0x10986c 0 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 57) (.out 0x10986f (movzxR32M8Effect 0x10986f 5 1 (.sib 4 none 0 (.d8 0x29))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 58) (.exec 0x10986f (LoadPre 0x10986f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x29)) s (0x10986f + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10986f 5 1 (.sib 4 none 0 (.d8 0x29))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x109874 (xorR8M8Effect 0x109874 4 6 (.base 2 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[53, 2]
    (.letOp (n := 60) (.exec 0x109874 (LoadPre 0x109874 (fun s => AddrMode.addr (.base 2 (.d8 0x20)) s (0x109874 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x109874 4 6 (.base 2 (.d8 0x20))) (Reg.operands [.gpr 6, .gpr 2] [])) #v[53, 2]
    (.letOp (n := 61) (.exec 0x109878 (StorePre 0x109878 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x109878 + BitVec.ofNat 64 8)) 1) (movM8R8Effect 0x109878 8 6 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x109880 (xorR8M8Effect 0x109880 3 1 (.base 2 (.d8 0x21))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[57, 2]
    (.letOp (n := 63) (.exec 0x109880 (LoadPre 0x109880 (fun s => AddrMode.addr (.base 2 (.d8 0x21)) s (0x109880 + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x109880 3 1 (.base 2 (.d8 0x21))) (Reg.operands [.gpr 1, .gpr 2] [])) #v[57, 2]
    (.letOp (n := 64) (.exec 0x109883 (StorePre 0x109883 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x109883 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109883 4 1 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x109887 (movzxR32M8Effect 0x109887 5 1 (.sib 4 none 0 (.d8 0x2a))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 66) (.exec 0x109887 (LoadPre 0x109887 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2a)) s (0x109887 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109887 5 1 (.sib 4 none 0 (.d8 0x2a))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x10988c (xorR8M8Effect 0x10988c 3 1 (.base 2 (.d8 0x22))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[65, 2]
    (.letOp (n := 68) (.exec 0x10988c (LoadPre 0x10988c (fun s => AddrMode.addr (.base 2 (.d8 0x22)) s (0x10988c + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x10988c 3 1 (.base 2 (.d8 0x22))) (Reg.operands [.gpr 1, .gpr 2] [])) #v[65, 2]
    (.letOp (n := 69) (.exec 0x10988f (StorePre 0x10988f 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10988f + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x10988f 7 1 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[67, 4]
    (.letOp (n := 70) (.out 0x109896 (movzxR32M8Effect 0x109896 5 6 (.sib 4 none 0 (.d8 0x2b))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 71) (.exec 0x109896 (LoadPre 0x109896 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2b)) s (0x109896 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109896 5 6 (.sib 4 none 0 (.d8 0x2b))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.out 0x10989b (xorR8M8Effect 0x10989b 4 6 (.base 2 (.d8 0x23))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[70, 2]
    (.letOp (n := 73) (.exec 0x10989b (LoadPre 0x10989b (fun s => AddrMode.addr (.base 2 (.d8 0x23)) s (0x10989b + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x10989b 4 6 (.base 2 (.d8 0x23))) (Reg.operands [.gpr 6, .gpr 2] [])) #v[70, 2]
    (.letOp (n := 74) (.out 0x10989f (movzxR32M8Effect 0x10989f 5 7 (.sib 4 none 0 (.d8 0x2c))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 75) (.exec 0x10989f (LoadPre 0x10989f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x10989f + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10989f 5 7 (.sib 4 none 0 (.d8 0x2c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 76) (.out 0x1098a4 (xorR8M8Effect 0x1098a4 4 7 (.base 2 (.d8 0x24))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2] []) (.reg (.gpr 7))) #v[74, 2]
    (.letOp (n := 77) (.exec 0x1098a4 (LoadPre 0x1098a4 (fun s => AddrMode.addr (.base 2 (.d8 0x24)) s (0x1098a4 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1098a4 4 7 (.base 2 (.d8 0x24))) (Reg.operands [.gpr 7, .gpr 2] [])) #v[74, 2]
    (.letOp (n := 78) (.out 0x1098a8 (movzxR32M8Effect 0x1098a8 6 8 (.sib 4 none 0 (.d8 0x2d))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 79) (.exec 0x1098a8 (LoadPre 0x1098a8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2d)) s (0x1098a8 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1098a8 6 8 (.sib 4 none 0 (.d8 0x2d))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 80) (.out 0x1098ae (xorR8M8Effect 0x1098ae 4 8 (.base 2 (.d8 0x25))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2] []) (.reg (.gpr 8))) #v[78, 2]
    (.letOp (n := 81) (.exec 0x1098ae (LoadPre 0x1098ae (fun s => AddrMode.addr (.base 2 (.d8 0x25)) s (0x1098ae + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1098ae 4 8 (.base 2 (.d8 0x25))) (Reg.operands [.gpr 8, .gpr 2] [])) #v[78, 2]
    (.letOp (n := 82) (.out 0x1098b2 (movzxR32M8Effect 0x1098b2 6 9 (.sib 4 none 0 (.d8 0x2e))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 83) (.exec 0x1098b2 (LoadPre 0x1098b2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2e)) s (0x1098b2 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1098b2 6 9 (.sib 4 none 0 (.d8 0x2e))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 84) (.out 0x1098b8 (xorR8M8Effect 0x1098b8 4 9 (.base 2 (.d8 0x26))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2] []) (.reg (.gpr 9))) #v[82, 2]
    (.letOp (n := 85) (.exec 0x1098b8 (LoadPre 0x1098b8 (fun s => AddrMode.addr (.base 2 (.d8 0x26)) s (0x1098b8 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1098b8 4 9 (.base 2 (.d8 0x26))) (Reg.operands [.gpr 9, .gpr 2] [])) #v[82, 2]
    (.letOp (n := 86) (.out 0x1098bc (movzxR32M8Effect 0x1098bc 6 10 (.sib 4 none 0 (.d8 0x2f))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 87) (.exec 0x1098bc (LoadPre 0x1098bc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2f)) s (0x1098bc + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1098bc 6 10 (.sib 4 none 0 (.d8 0x2f))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 88) (.out 0x1098c2 (xorR8M8Effect 0x1098c2 4 10 (.base 2 (.d8 0x27))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2] []) (.reg (.gpr 10))) #v[86, 2]
    (.letOp (n := 89) (.exec 0x1098c2 (LoadPre 0x1098c2 (fun s => AddrMode.addr (.base 2 (.d8 0x27)) s (0x1098c2 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1098c2 4 10 (.base 2 (.d8 0x27))) (Reg.operands [.gpr 10, .gpr 2] [])) #v[86, 2]
    (b_l109867_1)))))))))))))))))))))))))))))))))))))

def bytes_l109867 : List UInt8 :=
  [0x0F, 0xB6, 0x74, 0x24, 0x28, 0x48, 0x89, 0xC8, 0x0F, 0xB6, 0x4C, 0x24, 0x29, 0x40, 0x32, 0x72,
    0x20, 0x40, 0x88, 0xB4, 0x24, 0x80, 0x00, 0x00, 0x00, 0x32, 0x4A, 0x21, 0x88, 0x4C, 0x24, 0x78,
    0x0F, 0xB6, 0x4C, 0x24, 0x2A, 0x32, 0x4A, 0x22, 0x88, 0x8C, 0x24, 0x88, 0x00, 0x00, 0x00, 0x0F,
    0xB6, 0x74, 0x24, 0x2B, 0x40, 0x32, 0x72, 0x23, 0x0F, 0xB6, 0x7C, 0x24, 0x2C, 0x40, 0x32, 0x7A,
    0x24, 0x44, 0x0F, 0xB6, 0x44, 0x24, 0x2D, 0x44, 0x32, 0x42, 0x25, 0x44, 0x0F, 0xB6, 0x4C, 0x24,
    0x2E, 0x44, 0x32, 0x4A, 0x26, 0x44, 0x0F, 0xB6, 0x54, 0x24, 0x2F, 0x44, 0x32, 0x52, 0x27] ++ bytes_l109867_1

theorem code_l109867 : ∀ x ∈ codeRange 0x109867 bytes_l109867, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x9867 95 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l109867_1

@[cfg_block] def b_l109961 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x109961 (addR64Imm32Effect 0x109961 4 0x8d8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 54) (.exec 0x109961 (fun s => s.RIP = 0x109961) (addR64Imm32Effect 0x109961 4 0x8d8) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x109968 (popR64Effect 0x109968 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[53]
    (.letOp (n := 56) (.out 0x109968 (popR64Effect 0x109968 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[53]
    (.letOp (n := 57) (.exec 0x109968 (PopPre 0x109968) (popR64Effect 0x109968 1 3) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 58) (.out 0x109969 (popR64Effect 0x109969 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[56]
    (.letOp (n := 59) (.out 0x109969 (popR64Effect 0x109969 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[56]
    (.letOp (n := 60) (.exec 0x109969 (PopPre 0x109969) (popR64Effect 0x109969 2 12) (Reg.operands [.gpr 4] [])) #v[56]
    (.letOp (n := 61) (.out 0x10996b (popR64Effect 0x10996b 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[59]
    (.letOp (n := 62) (.out 0x10996b (popR64Effect 0x10996b 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 63) (.exec 0x10996b (PopPre 0x10996b) (popR64Effect 0x10996b 2 13) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 64) (.out 0x10996d (popR64Effect 0x10996d 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[62]
    (.letOp (n := 65) (.out 0x10996d (popR64Effect 0x10996d 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[62]
    (.letOp (n := 66) (.exec 0x10996d (PopPre 0x10996d) (popR64Effect 0x10996d 2 14) (Reg.operands [.gpr 4] [])) #v[62]
    (.letOp (n := 67) (.out 0x10996f (popR64Effect 0x10996f 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[65]
    (.letOp (n := 68) (.out 0x10996f (popR64Effect 0x10996f 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 69) (.exec 0x10996f (PopPre 0x10996f) (popR64Effect 0x10996f 2 15) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 70) (.out 0x109971 (popR64Effect 0x109971 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[68]
    (.letOp (n := 71) (.out 0x109971 (popR64Effect 0x109971 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[68]
    (.letOp (n := 72) (.exec 0x109971 (PopPre 0x109971) (popR64Effect 0x109971 1 5) (Reg.operands [.gpr 4] [])) #v[68]
    (.letOp (n := 73) (.out 0x109972 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[71]
    (.letOp (n := 74) (.out 0x109972 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[71]
    (.letOp (n := 75) (.exec 0x109972 (RetPre 0x109972) (retEffect) (Reg.operands [.gpr 4] [])) #v[71]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 2), (3, 55), (4, 74), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 76) (some ⟨73, by decide⟩)))))))))))))))))))))))))

def bytes_l109961 : List UInt8 :=
  [0x48, 0x81, 0xC4, 0xD8, 0x08, 0x00, 0x00, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F,
    0x5D, 0xC3]

theorem code_l109961 : ∀ x ∈ codeRange 0x109961 bytes_l109961, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9961 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109980 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x109980 (pushR64Effect 0x109980 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x109980 (PushPre 0x109980 1) (pushR64Effect 0x109980 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x109981 (pushR64Effect 0x109981 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x109981 (PushPre 0x109981 2) (pushR64Effect 0x109981 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x109983 (pushR64Effect 0x109983 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x109983 (PushPre 0x109983 2) (pushR64Effect 0x109983 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x109985 (pushR64Effect 0x109985 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x109985 (PushPre 0x109985 2) (pushR64Effect 0x109985 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x109987 (pushR64Effect 0x109987 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x109987 (PushPre 0x109987 2) (pushR64Effect 0x109987 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x109989 (pushR64Effect 0x109989 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x109989 (PushPre 0x109989 1) (pushR64Effect 0x109989 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x10998a (subR64Imm8Effect 0x10998a 4 0x28) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x10998a (fun s => s.RIP = 0x10998a) (subR64Imm8Effect 0x10998a 4 0x28) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x10998e (movR64R64Effect 0x10998e 3 6) (EffectPart.reads (.reg (.gpr 3)) [.gpr 6] []) (.reg (.gpr 3))) #v[6]
    (.letOp (n := 68) (.exec 0x10998e (fun s => s.RIP = 0x10998e) (movR64R64Effect 0x10998e 3 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 69) (.out 0x109991 (movR64R64Effect 0x109991 14 7) (EffectPart.reads (.reg (.gpr 14)) [.gpr 7] []) (.reg (.gpr 14))) #v[7]
    (.letOp (n := 70) (.exec 0x109991 (fun s => s.RIP = 0x109991) (movR64R64Effect 0x109991 14 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 71) (.exec 0x109994 (StorePre 0x109994 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x109994 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109994 7 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[7, 65]
    (.letOp (n := 72) (.exec 0x109999 (StorePre 0x109999 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x109999 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109999 2 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2, 65]
    (.letOp (n := 73) (.out 0x10999e (movR64R64Effect 0x10999e 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[2]
    (.letOp (n := 74) (.exec 0x10999e (fun s => s.RIP = 0x10999e) (movR64R64Effect 0x10999e 13 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 75) (.out 0x1099a1 (shlR64Effect 0x1099a1 4 13 4) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[73]
    (.letOp (n := 76) (.exec 0x1099a1 (fun s => s.RIP = 0x1099a1) (shlR64Effect 0x1099a1 4 13 4) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[73]
    (.letOp (n := 77) (.out 0x1099a5 (movR64Imm64Effect 0x1099a5 5 0x7fffffffffffffc0) (EffectPart.reads (.reg (.gpr 5)) [] []) (.reg (.gpr 5))) #v[]
    (.letOp (n := 78) (.exec 0x1099a5 (fun s => s.RIP = 0x1099a5) (movR64Imm64Effect 0x1099a5 5 0x7fffffffffffffc0) (Reg.operands [] [])) #v[]
    (.letOp (n := 79) (.out 0x1099af (andR64R64Effect 0x1099af 5 13) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 13] []) (.reg (.gpr 5))) #v[77, 75]
    (.letOp (n := 80) (.out 0x1099af (andR64R64Effect 0x1099af 5 13) (EffectPart.reads (.flag .ZF) [.gpr 5, .gpr 13] []) (.flag .ZF)) #v[77, 75]
    (.letOp (n := 81) (.exec 0x1099af (fun s => s.RIP = 0x1099af) (andR64R64Effect 0x1099af 5 13) (Reg.operands [.gpr 5, .gpr 13] [])) #v[77, 75]
    (.letOp (n := 82) (.pure (condOp 4)) #v[80]
    (.terminate (.condBr (Fin.last 82) ⟨.l1099d5, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 67), (4, 65), (5, 79), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 75), (14, 69), (15, 15), (19, 80), (22, 22), (39, 39), (50, 50), (51, 51)] 83⟩ ⟨.l1099b4, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 67), (4, 65), (5, 79), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 75), (14, 69), (15, 15), (19, 80), (22, 22), (39, 39), (50, 50), (51, 51)] 83⟩)))))))))))))))))))))))))))))))

def bytes_l109980 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x83, 0xEC, 0x28, 0x48, 0x89,
    0xF3, 0x49, 0x89, 0xFE, 0x48, 0x89, 0x7C, 0x24, 0x20, 0x48, 0x89, 0x54, 0x24, 0x18, 0x49, 0x89,
    0xD5, 0x49, 0xC1, 0xE5, 0x04, 0x48, 0xBD, 0xC0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F, 0x4C,
    0x21, 0xED, 0x74, 0x21]

theorem code_l109980 : ∀ x ∈ codeRange 0x109980 bytes_l109980, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9980 52 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1099b4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1099b4 (leaR64Effect 0x1099b4 12 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 54) (.exec 0x1099b4 (fun s => s.RIP = 0x1099b4) (leaR64Effect 0x1099b4 12 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1099b9 (movR64R64Effect 0x1099b9 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[3]
    (.letOp (n := 56) (.exec 0x1099b9 (fun s => s.RIP = 0x1099b9) (movR64R64Effect 0x1099b9 6 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 57) (.exec 0x1099bc (fun s => s.RIP = 0x1099bc) (fun _ => nopEffect 0x1099bc 4) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l1099c0, RegMap.args [(3, 3), (4, 4), (5, 5), (6, 55), (12, 53), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l1099b4 : List UInt8 :=
  [0x4C, 0x8D, 0x64, 0x24, 0x20, 0x48, 0x89, 0xDE, 0x0F, 0x1F, 0x40, 0x00]

theorem code_l1099b4 : ∀ x ∈ codeRange 0x1099b4 bytes_l1099b4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x99b4 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1099c0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1099c0 (leaR64Effect 0x1099c0 15 (.base 6 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 6] []) (.reg (.gpr 15))) #v[6]
    (.letOp (n := 54) (.exec 0x1099c0 (fun s => s.RIP = 0x1099c0) (leaR64Effect 0x1099c0 15 (.base 6 (.d8 0x40))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 55) (.out 0x1099c4 (movR64R64Effect 0x1099c4 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[12]
    (.letOp (n := 56) (.exec 0x1099c4 (fun s => s.RIP = 0x1099c4) (movR64R64Effect 0x1099c4 7 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 57) (.out 0x1099c7 (callEffect (fun _ => 0x109ac0) 0x1099cc) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x1099c7 (PushPre 0x1099c7 5) (callEffect (fun _ => 0x109ac0) 0x1099cc) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x1099cc⟩) #v[]
    (.terminate (.call ⟨.l109ac0, RegMap.args [(3, 3), (4, 57), (5, 5), (6, 6), (7, 55), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ { target := .l1099cc, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l1099c0 : List UInt8 :=
  [0x4C, 0x8D, 0x7E, 0x40, 0x4C, 0x89, 0xE7, 0xE8, 0xF4, 0x00, 0x00, 0x00]

theorem code_l1099c0 : ∀ x ∈ codeRange 0x1099c0 bytes_l1099c0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x99c0 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

end AesGcm.Proofs.Machine.LIR
