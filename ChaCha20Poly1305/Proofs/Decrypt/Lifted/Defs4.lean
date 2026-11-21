import ChaCha20Poly1305.Proofs.Decrypt.Movsd
import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Labels
import ChaCha20Poly1305.Proofs.Common.CFG.EvalAttr
import ChaCha20Poly1305.Proofs.Common.Lift.Generated.Footprints

namespace ChaCha20Poly1305.Proofs.Decrypt.Lifted

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift

@[cfg_block] def b_l10153a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10153a (movR64M64Effect 0x10153a 5 (.rip 0x1feabf)) (EffectPart.reads (.reg (.gpr 5)) [] []) (.reg (.gpr 5))) #v[]
    (.letOp (n := 54) (.exec 0x10153a (LoadPre 0x10153a (fun s => AddrMode.addr (.rip 0x1feabf) s (0x10153a + BitVec.ofNat 64 7)) 8) (movR64M64Effect 0x10153a 5 (.rip 0x1feabf)) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x101541 (movR64R64Effect 0x101541 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x101541 (fun s => s.RIP = 0x101541) (movR64R64Effect 0x101541 0 5) (Reg.operands [.gpr 5] [])) #v[53]
    (.letOp (n := 57) (.exec 0x101544 (fun s => s.RIP = 0x101544) (movR32Imm32Effect 0x101544 5 7 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 58) (.out 0x101549 (addR64R64Effect 0x101549 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[55, 14]
    (.letOp (n := 59) (.out 0x101549 (addR64R64Effect 0x101549 0 14) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 14] []) (.flag .CF)) #v[55, 14]
    (.letOp (n := 60) (.exec 0x101549 (fun s => s.RIP = 0x101549) (addR64R64Effect 0x101549 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 61) (.pure (condOp 2)) #v[59]
    (.terminate (.condBr (Fin.last 61) ⟨.l10163b, RegMap.args [(0, 58), (3, 3), (4, 4), (5, 53), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (16, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ ⟨.l101552, RegMap.args [(0, 58), (3, 3), (4, 4), (5, 53), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (16, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩))))))))))

def bytes_l10153a : List UInt8 :=
  [0x48, 0x8B, 0x2D, 0xBF, 0xEA, 0x1F, 0x00, 0x48, 0x89, 0xE8, 0xBF, 0x01, 0x00, 0x00, 0x00, 0x4C,
    0x01, 0xF0, 0x0F, 0x82, 0xE9, 0x00, 0x00, 0x00]

theorem code_l10153a : ∀ x ∈ codeRange 0x10153a bytes_l10153a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x153a 24 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101552 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101552 (movR64M64Effect 0x101552 1 (.rip 0x1feaaf)) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 54) (.exec 0x101552 (LoadPre 0x101552 (fun s => AddrMode.addr (.rip 0x1feaaf) s (0x101552 + BitVec.ofNat 64 7)) 8) (movR64M64Effect 0x101552 1 (.rip 0x1feaaf)) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x101559 (cmpR64R64Effect 0x101559 0 1) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 1] []) (.flag .CF)) #v[0, 53]
    (.letOp (n := 56) (.out 0x101559 (cmpR64R64Effect 0x101559 0 1) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 1] []) (.flag .ZF)) #v[0, 53]
    (.letOp (n := 57) (.exec 0x101559 (fun s => s.RIP = 0x101559) (cmpR64R64Effect 0x101559 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[0, 53]
    (.letOp (n := 58) (.pure (condOp 7)) #v[55, 56]
    (.terminate (.condBr (Fin.last 58) ⟨.l10163b, RegMap.args [(0, 0), (1, 53), (3, 3), (4, 4), (5, 5), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩ ⟨.l101562, RegMap.args [(0, 0), (1, 53), (3, 3), (4, 4), (5, 5), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l101552 : List UInt8 :=
  [0x48, 0x8B, 0x0D, 0xAF, 0xEA, 0x1F, 0x00, 0x48, 0x39, 0xC8, 0x0F, 0x87, 0xD9, 0x00, 0x00, 0x00]

theorem code_l101552 : ∀ x ∈ codeRange 0x101552 bytes_l101552, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1552 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101562 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x101562 (StorePre 0x101562 7 (fun s => AddrMode.addr (.rip 0x1fea97) s (0x101562 + BitVec.ofNat 64 7)) 8) (movM64R64Effect 0x101562 0 (.rip 0x1fea97)) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 54) (.out 0x101569 (testR64R64Effect 0x101569 5 5) (EffectPart.reads (.flag .ZF) [.gpr 5, .gpr 5] []) (.flag .ZF)) #v[5, 5]
    (.letOp (n := 55) (.exec 0x101569 (fun s => s.RIP = 0x101569) (testR64R64Effect 0x101569 5 5) (Reg.operands [.gpr 5, .gpr 5] [])) #v[5, 5]
    (.letOp (n := 56) (.pure (condOp 4)) #v[54]
    (.terminate (.condBr (Fin.last 56) ⟨.l10163b, RegMap.args [(0, 0), (3, 3), (4, 4), (5, 5), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩ ⟨.l101572, RegMap.args [(0, 0), (3, 3), (4, 4), (5, 5), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l101562 : List UInt8 :=
  [0x48, 0x89, 0x05, 0x97, 0xEA, 0x1F, 0x00, 0x48, 0x85, 0xED, 0x0F, 0x84, 0xC9, 0x00, 0x00, 0x00]

theorem code_l101562 : ∀ x ∈ codeRange 0x101562 bytes_l101562, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1562 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101572 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x101572 (StorePre 0x101572 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x101572 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101572 14 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[14, 4]
    (.letOp (n := 54) (.exec 0x101577 (StorePre 0x101577 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x101577 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101577 5 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[5, 4]
    (.letOp (n := 55) (.out 0x10157c (movR64R64Effect 0x10157c 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[5]
    (.letOp (n := 56) (.exec 0x10157c (fun s => s.RIP = 0x10157c) (movR64R64Effect 0x10157c 7 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 57) (.out 0x10157f (movR64R64Effect 0x10157f 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 13] []) (.reg (.gpr 6))) #v[13]
    (.letOp (n := 58) (.exec 0x10157f (fun s => s.RIP = 0x10157f) (movR64R64Effect 0x10157f 6 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 59) (.out 0x101582 (movR64R64Effect 0x101582 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14] []) (.reg (.gpr 2))) #v[14]
    (.letOp (n := 60) (.exec 0x101582 (fun s => s.RIP = 0x101582) (movR64R64Effect 0x101582 2 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 61) (.out 0x101585 (callEffect (callMemPtr 0x101585 (.rip 0xffe1d)) (0x101585 + BitVec.ofNat 64 (callMemLen (.rip 0xffe1d)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 62) (.exec 0x101585 (GoesTo (CallMemPre 0x101585 (.rip 0xffe1d)) (callEffect (callMemPtr 0x101585 (.rip 0xffe1d)) (0x101585 + BitVec.ofNat 64 (callMemLen (.rip 0xffe1d)))) 0x102dc0) (callEffect (callMemPtr 0x101585 (.rip 0xffe1d)) (0x101585 + BitVec.ofNat 64 (callMemLen (.rip 0xffe1d)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.const ⟨64, 0x10158b⟩) #v[]
    (.terminate (.call ⟨.l102dc0, RegMap.args [(2, 59), (3, 3), (4, 61), (5, 5), (6, 57), (7, 55), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ { target := .l10158b, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l101572 : List UInt8 :=
  [0x4C, 0x89, 0x74, 0x24, 0x08, 0x48, 0x89, 0x6C, 0x24, 0x10, 0x48, 0x89, 0xEF, 0x4C, 0x89, 0xEE,
    0x4C, 0x89, 0xF2, 0xFF, 0x15, 0x1D, 0xFE, 0x0F, 0x00]

theorem code_l101572 : ∀ x ∈ codeRange 0x101572 bytes_l101572, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1572 25 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10158b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x10158b (StorePre 0x10158b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10158b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10158b 14 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[14, 4]
    (.letOp (n := 54) (.out 0x101590 (cmpR64Imm8Effect 0x101590 14 0x10) (EffectPart.reads (.flag .CF) [.gpr 14] []) (.flag .CF)) #v[14]
    (.letOp (n := 55) (.exec 0x101590 (fun s => s.RIP = 0x101590) (cmpR64Imm8Effect 0x101590 14 0x10) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 56) (.pure (condOp 2)) #v[54]
    (.terminate (.condBr (Fin.last 56) ⟨.l101611, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (12, 12), (14, 14), (15, 15), (16, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩ ⟨.l101596, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (12, 12), (14, 14), (15, 15), (16, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l10158b : List UInt8 :=
  [0x4C, 0x89, 0x74, 0x24, 0x18, 0x49, 0x83, 0xFE, 0x10, 0x72, 0x7B]

theorem code_l10158b : ∀ x ∈ codeRange 0x10158b bytes_l10158b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x158b 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101596 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101596 (movR64M64Effect 0x101596 1 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x101596 (LoadPre 0x101596 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x101596 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x101596 1 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10159e (leaR64Effect 0x10159e 13 (.base 14 (.d8 0xf0))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 14] []) (.reg (.gpr 13))) #v[14]
    (.letOp (n := 56) (.exec 0x10159e (fun s => s.RIP = 0x10159e) (leaR64Effect 0x10159e 13 (.base 14 (.d8 0xf0))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x1015a2 (movR64M64Effect 0x1015a2 9 (.sib 5 (some 14) 0 (.d8 0xf0))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 5, .gpr 14] []) (.reg (.gpr 9))) #v[5, 14]
    (.letOp (n := 58) (.exec 0x1015a2 (LoadPre 0x1015a2 (fun s => AddrMode.addr (.sib 5 (some 14) 0 (.d8 0xf0)) s (0x1015a2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1015a2 9 (.sib 5 (some 14) 0 (.d8 0xf0))) (Reg.operands [.gpr 5, .gpr 14] [])) #v[5, 14]
    (.letOp (n := 59) (.out 0x1015a7 (movR64M64Effect 0x1015a7 0 (.sib 5 (some 14) 0 (.d8 0xf8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 14] []) (.reg (.gpr 0))) #v[5, 14]
    (.letOp (n := 60) (.exec 0x1015a7 (LoadPre 0x1015a7 (fun s => AddrMode.addr (.sib 5 (some 14) 0 (.d8 0xf8)) s (0x1015a7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1015a7 0 (.sib 5 (some 14) 0 (.d8 0xf8))) (Reg.operands [.gpr 5, .gpr 14] [])) #v[5, 14]
    (.letOp (n := 61) (.exec 0x1015ac (StorePre 0x1015ac 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1015ac + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1015ac 5 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[5, 4]
    (.letOp (n := 62) (.exec 0x1015b1 (StorePre 0x1015b1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1015b1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1015b1 5 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[5, 4]
    (.letOp (n := 63) (.exec 0x1015b6 (StorePre 0x1015b6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1015b6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1015b6 13 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 64) (.exec 0x1015bb (StorePre 0x1015bb 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1015bb + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1015bb 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 65) (.out 0x1015bf (leaR64Effect 0x1015bf 7 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 66) (.exec 0x1015bf (fun s => s.RIP = 0x1015bf) (leaR64Effect 0x1015bf 7 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x1015c4 (leaR64Effect 0x1015c4 8 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 68) (.exec 0x1015c4 (fun s => s.RIP = 0x1015c4) (leaR64Effect 0x1015c4 8 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.out 0x1015c9 (movR64R64Effect 0x1015c9 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 12] []) (.reg (.gpr 6))) #v[12]
    (.letOp (n := 70) (.exec 0x1015c9 (fun s => s.RIP = 0x1015c9) (movR64R64Effect 0x1015c9 6 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 71) (.out 0x1015cc (movR64R64Effect 0x1015cc 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15] []) (.reg (.gpr 2))) #v[15]
    (.letOp (n := 72) (.exec 0x1015cc (fun s => s.RIP = 0x1015cc) (movR64R64Effect 0x1015cc 2 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 73) (.out 0x1015cf (callEffect (fun _ => 0x1001f0) 0x1015d4) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 74) (.exec 0x1015cf (PushPre 0x1015cf 5) (callEffect (fun _ => 0x1001f0) 0x1015d4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.const ⟨64, 0x1015d4⟩) #v[]
    (.terminate (.call ⟨.l1001f0, RegMap.args [(0, 59), (1, 53), (2, 71), (3, 3), (4, 73), (5, 5), (6, 69), (7, 65), (8, 67), (9, 57), (12, 12), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 76⟩ { target := .l1015d4, kept := #v[], arity := rfl, guard := some (Fin.last 75) }))))))))))))))))))))))))

def bytes_l101596 : List UInt8 :=
  [0x48, 0x8B, 0x8C, 0x24, 0x90, 0x00, 0x00, 0x00, 0x4D, 0x8D, 0x6E, 0xF0, 0x4E, 0x8B, 0x4C, 0x35,
    0xF0, 0x4A, 0x8B, 0x44, 0x35, 0xF8, 0x48, 0x89, 0x6C, 0x24, 0x20, 0x48, 0x89, 0x6C, 0x24, 0x28,
    0x4C, 0x89, 0x6C, 0x24, 0x30, 0x48, 0x89, 0x04, 0x24, 0x48, 0x8D, 0x7C, 0x24, 0x38, 0x4C, 0x8D,
    0x44, 0x24, 0x20, 0x4C, 0x89, 0xE6, 0x4C, 0x89, 0xFA, 0xE8, 0x1C, 0xEC, 0xFF, 0xFF]

theorem code_l101596 : ∀ x ∈ codeRange 0x101596 bytes_l101596, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1596 62 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1015d4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1015d4 (testR8R8Effect 0x1015d4 2 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[0, 0]
    (.letOp (n := 54) (.exec 0x1015d4 (fun s => s.RIP = 0x1015d4) (testR8R8Effect 0x1015d4 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l101611, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l1015d8, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l1015d4 : List UInt8 :=
  [0x84, 0xC0, 0x75, 0x39]

theorem code_l1015d4 : ∀ x ∈ codeRange 0x1015d4 bytes_l1015d4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x15d4 4 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1015d8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1015d8 (leaR64Effect 0x1015d8 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x1015d8 (fun s => s.RIP = 0x1015d8) (leaR64Effect 0x1015d8 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1015dd (movR64R64Effect 0x1015dd 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 13] []) (.reg (.gpr 6))) #v[13]
    (.letOp (n := 56) (.exec 0x1015dd (fun s => s.RIP = 0x1015dd) (movR64R64Effect 0x1015dd 6 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 57) (.out 0x1015e0 (callEffect (fun _ => 0x102020) 0x1015e5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x1015e0 (PushPre 0x1015e0 5) (callEffect (fun _ => 0x102020) 0x1015e5) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x1015e5⟩) #v[]
    (.terminate (.call ⟨.l102020, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ { target := .l1015e5, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l1015d8 : List UInt8 :=
  [0x48, 0x8D, 0x7C, 0x24, 0x08, 0x4C, 0x89, 0xEE, 0xE8, 0x3B, 0x0A, 0x00, 0x00]

theorem code_l1015d8 : ∀ x ∈ codeRange 0x1015d8 bytes_l1015d8, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x15d8 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1015e5 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1015e5 (cmpMImm8Effect 0x1015e5 6 64 (.sib 4 none 0 (.d8 0x8)) 0xff) (EffectPart.reads (.flag .ZF) [.gpr 4] []) (.flag .ZF)) #v[4]
    (.letOp (n := 54) (.exec 0x1015e5 (LoadPre 0x1015e5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1015e5 + BitVec.ofNat 64 6)) 8) (cmpMImm8Effect 0x1015e5 6 64 (.sib 4 none 0 (.d8 0x8)) 0xff) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l101611, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l1015ed, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l1015e5 : List UInt8 :=
  [0x48, 0x83, 0x7C, 0x24, 0x08, 0xFF, 0x74, 0x24]

theorem code_l1015e5 : ∀ x ∈ codeRange 0x1015e5 bytes_l1015e5, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x15e5 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1015ed : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1015ed (movR64M64Effect 0x1015ed 0 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1015ed (LoadPre 0x1015ed (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x1015ed + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1015ed 0 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1015f5 (movR64M64Effect 0x1015f5 2 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 56) (.exec 0x1015f5 (LoadPre 0x1015f5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1015f5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1015f5 2 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1015fa (cmpR64R64Effect 0x1015fa 2 0) (EffectPart.reads (.flag .CF) [.gpr 2, .gpr 0] []) (.flag .CF)) #v[55, 53]
    (.letOp (n := 58) (.out 0x1015fa (cmpR64R64Effect 0x1015fa 2 0) (EffectPart.reads (.flag .ZF) [.gpr 2, .gpr 0] []) (.flag .ZF)) #v[55, 53]
    (.letOp (n := 59) (.exec 0x1015fa (fun s => s.RIP = 0x1015fa) (cmpR64R64Effect 0x1015fa 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[55, 53]
    (.letOp (n := 60) (.pure (condOp 7)) #v[57, 58]
    (.terminate (.condBr (Fin.last 60) ⟨.l101625, RegMap.args [(0, 53), (2, 55), (3, 3), (4, 4), (5, 5), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩ ⟨.l1015ff, RegMap.args [(0, 53), (2, 55), (3, 3), (4, 4), (5, 5), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩)))))))))

def bytes_l1015ed : List UInt8 :=
  [0x48, 0x8B, 0x84, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x54, 0x24, 0x18, 0x48, 0x39, 0xC2,
    0x77, 0x26]

theorem code_l1015ed : ∀ x ∈ codeRange 0x1015ed bytes_l1015ed, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x15ed 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1015ff : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1015ff (movR64M64Effect 0x1015ff 6 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 54) (.exec 0x1015ff (LoadPre 0x1015ff (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1015ff + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1015ff 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x101604 (movR64R64Effect 0x101604 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 56) (.exec 0x101604 (fun s => s.RIP = 0x101604) (movR64R64Effect 0x101604 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 57) (.out 0x101607 (callEffect (callMemPtr 0x101607 (.rip 0xffd9b)) (0x101607 + BitVec.ofNat 64 (callMemLen (.rip 0xffd9b)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x101607 (GoesTo (CallMemPre 0x101607 (.rip 0xffd9b)) (callEffect (callMemPtr 0x101607 (.rip 0xffd9b)) (0x101607 + BitVec.ofNat 64 (callMemLen (.rip 0xffd9b)))) 0x102dc0) (callEffect (callMemPtr 0x101607 (.rip 0xffd9b)) (0x101607 + BitVec.ofNat 64 (callMemLen (.rip 0xffd9b)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x10160d⟩) #v[]
    (.terminate (.call ⟨.l102dc0, RegMap.args [(2, 2), (3, 3), (4, 57), (5, 5), (6, 53), (7, 55), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ { target := .l10160d, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l1015ff : List UInt8 :=
  [0x48, 0x8B, 0x74, 0x24, 0x10, 0x48, 0x89, 0xDF, 0xFF, 0x15, 0x9B, 0xFD, 0x0F, 0x00]

theorem code_l1015ff : ∀ x ∈ codeRange 0x1015ff bytes_l1015ff, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x15ff 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10160d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10160d (xorR32R32Effect 0x10160d 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[0, 0]
    (.letOp (n := 54) (.exec 0x10160d (fun s => s.RIP = 0x10160d) (xorR32R32Effect 0x10160d 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.terminate (.br ⟨.l101616, RegMap.args [(0, 53), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (9, 9), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l10160d : List UInt8 :=
  [0x31, 0xC0, 0xEB, 0x05]

theorem code_l10160d : ∀ x ∈ codeRange 0x10160d bytes_l10160d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x160d 4 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101611 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101611 (movR32Imm32Effect 0x101611 5 0 0x1) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 54) (.exec 0x101611 (fun s => s.RIP = 0x101611) (movR32Imm32Effect 0x101611 5 0 0x1) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l101616, RegMap.args [(0, 53), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (9, 9), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l101611 : List UInt8 :=
  [0xB8, 0x01, 0x00, 0x00, 0x00]

theorem code_l101611 : ∀ x ∈ codeRange 0x101611 bytes_l101611, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1611 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101616 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101616 (addR64Imm8Effect 0x101616 4 0x58) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 54) (.exec 0x101616 (fun s => s.RIP = 0x101616) (addR64Imm8Effect 0x101616 4 0x58) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10161a (popR64Effect 0x10161a 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[53]
    (.letOp (n := 56) (.out 0x10161a (popR64Effect 0x10161a 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[53]
    (.letOp (n := 57) (.exec 0x10161a (PopPre 0x10161a) (popR64Effect 0x10161a 1 3) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 58) (.out 0x10161b (popR64Effect 0x10161b 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[56]
    (.letOp (n := 59) (.out 0x10161b (popR64Effect 0x10161b 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[56]
    (.letOp (n := 60) (.exec 0x10161b (PopPre 0x10161b) (popR64Effect 0x10161b 2 12) (Reg.operands [.gpr 4] [])) #v[56]
    (.letOp (n := 61) (.out 0x10161d (popR64Effect 0x10161d 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[59]
    (.letOp (n := 62) (.out 0x10161d (popR64Effect 0x10161d 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 63) (.exec 0x10161d (PopPre 0x10161d) (popR64Effect 0x10161d 2 13) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 64) (.out 0x10161f (popR64Effect 0x10161f 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[62]
    (.letOp (n := 65) (.out 0x10161f (popR64Effect 0x10161f 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[62]
    (.letOp (n := 66) (.exec 0x10161f (PopPre 0x10161f) (popR64Effect 0x10161f 2 14) (Reg.operands [.gpr 4] [])) #v[62]
    (.letOp (n := 67) (.out 0x101621 (popR64Effect 0x101621 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[65]
    (.letOp (n := 68) (.out 0x101621 (popR64Effect 0x101621 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 69) (.exec 0x101621 (PopPre 0x101621) (popR64Effect 0x101621 2 15) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 70) (.out 0x101623 (popR64Effect 0x101623 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[68]
    (.letOp (n := 71) (.out 0x101623 (popR64Effect 0x101623 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[68]
    (.letOp (n := 72) (.exec 0x101623 (PopPre 0x101623) (popR64Effect 0x101623 1 5) (Reg.operands [.gpr 4] [])) #v[68]
    (.letOp (n := 73) (.out 0x101624 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[71]
    (.letOp (n := 74) (.out 0x101624 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[71]
    (.letOp (n := 75) (.exec 0x101624 (RetPre 0x101624) (retEffect) (Reg.operands [.gpr 4] [])) #v[71]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 2), (3, 55), (4, 74), (5, 70), (6, 6), (7, 7), (9, 9), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 76) (some ⟨73, by decide⟩)))))))))))))))))))))))))

def bytes_l101616 : List UInt8 :=
  [0x48, 0x83, 0xC4, 0x58, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l101616 : ∀ x ∈ codeRange 0x101616 bytes_l101616, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1616 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101625 : Block Op Label signature Reg.count 53 :=
  cutBlock 0x101625

def bytes_l101625 : List UInt8 :=
  [0x31]

theorem code_l101625 : ∀ x ∈ codeRange 0x101625 bytes_l101625, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1625 1 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101639 : Block Op Label signature Reg.count 53 :=
  cutBlock 0x101639

def bytes_l101639 : List UInt8 :=
  [0x31]

theorem code_l101639 : ∀ x ∈ codeRange 0x101639 bytes_l101639, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1639 1 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10163b : Block Op Label signature Reg.count 53 :=
  cutBlock 0x10163b

def bytes_l10163b : List UInt8 :=
  [0x4C]

theorem code_l10163b : ∀ x ∈ codeRange 0x10163b bytes_l10163b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x163b 1 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101aa0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101aa0 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[4]
    (.letOp (n := 54) (.out 0x101aa0 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 55) (.exec 0x101aa0 (RetPre 0x101aa0) (retEffect) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 54), (5, 5), (6, 6), (7, 7), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 56) (some ⟨53, by decide⟩)))))

def bytes_l101aa0 : List UInt8 :=
  [0xC3]

theorem code_l101aa0 : ∀ x ∈ codeRange 0x101aa0 bytes_l101aa0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1aa0 1 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101ab0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101ab0 (pushR64Effect 0x101ab0 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x101ab0 (PushPre 0x101ab0 1) (pushR64Effect 0x101ab0 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x101ab1 (pushR64Effect 0x101ab1 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x101ab1 (PushPre 0x101ab1 2) (pushR64Effect 0x101ab1 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x101ab3 (pushR64Effect 0x101ab3 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x101ab3 (PushPre 0x101ab3 2) (pushR64Effect 0x101ab3 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x101ab5 (pushR64Effect 0x101ab5 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x101ab5 (PushPre 0x101ab5 2) (pushR64Effect 0x101ab5 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x101ab7 (pushR64Effect 0x101ab7 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x101ab7 (PushPre 0x101ab7 2) (pushR64Effect 0x101ab7 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x101ab9 (pushR64Effect 0x101ab9 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x101ab9 (PushPre 0x101ab9 1) (pushR64Effect 0x101ab9 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x101aba (subR64Imm8Effect 0x101aba 4 0x28) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x101aba (fun s => s.RIP = 0x101aba) (subR64Imm8Effect 0x101aba 4 0x28) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x101abe (movR64R64Effect 0x101abe 10 7) (EffectPart.reads (.reg (.gpr 10)) [.gpr 7] []) (.reg (.gpr 10))) #v[7]
    (.letOp (n := 68) (.exec 0x101abe (fun s => s.RIP = 0x101abe) (movR64R64Effect 0x101abe 10 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 69) (.out 0x101ac1 (xorR8Imm8Effect 0x101ac1 3 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[2]
    (.letOp (n := 70) (.exec 0x101ac1 (fun s => s.RIP = 0x101ac1) (xorR8Imm8Effect 0x101ac1 3 2 0x1) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 71) (.out 0x101ac4 (movzxR32R8Effect 0x101ac4 3 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[69]
    (.letOp (n := 72) (.exec 0x101ac4 (fun s => s.RIP = 0x101ac4) (movzxR32R8Effect 0x101ac4 3 7 2) (Reg.operands [.gpr 2] [])) #v[69]
    (.letOp (n := 73) (.out 0x101ac7 (shlR32Effect 0x101ac7 3 7 24) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[71]
    (.letOp (n := 74) (.exec 0x101ac7 (fun s => s.RIP = 0x101ac7) (shlR32Effect 0x101ac7 3 7 24) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[71]
    (.letOp (n := 75) (.out 0x101aca (movR32M32Effect 0x101aca 8 (.base 10 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 10] []) (.reg (.gpr 8))) #v[67]
    (.letOp (n := 76) (.exec 0x101aca (LoadPre 0x101aca (fun s => AddrMode.addr (.base 10 (.d8 0x10)) s (0x101aca + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x101aca 8 (.base 10 (.d8 0x10))) (Reg.operands [.gpr 10] [])) #v[67]
    (.letOp (n := 77) (.out 0x101ace (movR32M32Effect 0x101ace 0 (.base 10 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[67]
    (.letOp (n := 78) (.exec 0x101ace (LoadPre 0x101ace (fun s => AddrMode.addr (.base 10 (.d8 0x18)) s (0x101ace + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x101ace 0 (.base 10 (.d8 0x18))) (Reg.operands [.gpr 10] [])) #v[67]
    (.letOp (n := 79) (.exec 0x101ad2 (StorePre 0x101ad2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x101ad2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101ad2 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[77, 65]
    (.letOp (n := 80) (.out 0x101ad7 (movR32M32Effect 0x101ad7 1 (.base 10 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 10] []) (.reg (.gpr 1))) #v[67]
    (.letOp (n := 81) (.exec 0x101ad7 (LoadPre 0x101ad7 (fun s => AddrMode.addr (.base 10 (.d8 0x1c)) s (0x101ad7 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x101ad7 1 (.base 10 (.d8 0x1c))) (Reg.operands [.gpr 10] [])) #v[67]
    (.letOp (n := 82) (.exec 0x101adb (StorePre 0x101adb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x101adb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101adb 1 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[80, 65]
    (.letOp (n := 83) (.out 0x101ae0 (movR32M32Effect 0x101ae0 2 (.base 10 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10] []) (.reg (.gpr 2))) #v[67]
    (.letOp (n := 84) (.exec 0x101ae0 (LoadPre 0x101ae0 (fun s => AddrMode.addr (.base 10 (.d8 0x20)) s (0x101ae0 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x101ae0 2 (.base 10 (.d8 0x20))) (Reg.operands [.gpr 10] [])) #v[67]
    (.letOp (n := 85) (.exec 0x101ae4 (StorePre 0x101ae4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x101ae4 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101ae4 2 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[83, 65]
    (.letOp (n := 86) (.out 0x101ae9 (leaR32Effect 0x101ae9 3 0 (.sib 0 (some 0) 2 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[77, 77]
    (.letOp (n := 87) (.exec 0x101ae9 (fun s => s.RIP = 0x101ae9) (leaR32Effect 0x101ae9 3 0 (.sib 0 (some 0) 2 .none)) (Reg.operands [.gpr 0, .gpr 0] [])) #v[77, 77]
    (.letOp (n := 88) (.exec 0x101aec (StorePre 0x101aec 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x101aec + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101aec 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[86, 65]
    (.terminate (.br ⟨.l101af1, RegMap.args [(0, 86), (1, 80), (2, 83), (3, 3), (4, 65), (5, 5), (6, 6), (7, 73), (8, 75), (10, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 89⟩)))))))))))))))))))))))))))))))))))))

def bytes_l101ab0 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x83, 0xEC, 0x28, 0x49, 0x89,
    0xFA, 0x80, 0xF2, 0x01, 0x0F, 0xB6, 0xFA, 0xC1, 0xE7, 0x18, 0x45, 0x8B, 0x42, 0x10, 0x41, 0x8B,
    0x42, 0x18, 0x48, 0x89, 0x44, 0x24, 0x10, 0x41, 0x8B, 0x4A, 0x1C, 0x48, 0x89, 0x4C, 0x24, 0x18,
    0x41, 0x8B, 0x52, 0x20, 0x48, 0x89, 0x54, 0x24, 0x20, 0x8D, 0x04, 0x80, 0x48, 0x89, 0x44, 0x24,
    0x08]

theorem code_l101ab0 : ∀ x ∈ codeRange 0x101ab0 bytes_l101ab0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1ab0 65 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101af1 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101af1 (leaR32Effect 0x101af1 4 9 (.sib 1 (some 1) 2 .none)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 1, .gpr 1] []) (.reg (.gpr 9))) #v[1, 1]
    (.letOp (n := 54) (.exec 0x101af1 (fun s => s.RIP = 0x101af1) (leaR32Effect 0x101af1 4 9 (.sib 1 (some 1) 2 .none)) (Reg.operands [.gpr 1, .gpr 1] [])) #v[1, 1]
    (.letOp (n := 55) (.exec 0x101af5 (StorePre 0x101af5 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x101af5 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x101af5 9 (.sib 4 none 0 .none)) (Reg.operands [.gpr 9, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x101af9 (leaR32Effect 0x101af9 3 3 (.sib 2 (some 2) 2 .none)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2, .gpr 2] []) (.reg (.gpr 3))) #v[2, 2]
    (.letOp (n := 57) (.exec 0x101af9 (fun s => s.RIP = 0x101af9) (leaR32Effect 0x101af9 3 3 (.sib 2 (some 2) 2 .none)) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 58) (.out 0x101afc (movR32Imm32Effect 0x101afc 6 15 0x3ffffff) (EffectPart.reads (.reg (.gpr 15)) [] []) (.reg (.gpr 15))) #v[]
    (.letOp (n := 59) (.exec 0x101afc (fun s => s.RIP = 0x101afc) (movR32Imm32Effect 0x101afc 6 15 0x3ffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 60) (.out 0x101b02 (andR32M32Effect 0x101b02 3 15 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 6] []) (.reg (.gpr 15))) #v[58, 6]
    (.letOp (n := 61) (.exec 0x101b02 (LoadPre 0x101b02 (fun s => AddrMode.addr (.base 6 .none) s (0x101b02 + BitVec.ofNat 64 3)) 4) (andR32M32Effect 0x101b02 3 15 (.base 6 .none)) (Reg.operands [.gpr 15, .gpr 6] [])) #v[58, 6]
    (.letOp (n := 62) (.out 0x101b05 (addR32M32Effect 0x101b05 4 15 (.base 10 (.d8 0x24))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 10] []) (.reg (.gpr 15))) #v[60, 10]
    (.letOp (n := 63) (.exec 0x101b05 (LoadPre 0x101b05 (fun s => AddrMode.addr (.base 10 (.d8 0x24)) s (0x101b05 + BitVec.ofNat 64 4)) 4) (addR32M32Effect 0x101b05 4 15 (.base 10 (.d8 0x24))) (Reg.operands [.gpr 15, .gpr 10] [])) #v[60, 10]
    (.letOp (n := 64) (.out 0x101b09 (movR32M32LowEffect 0x101b09 2 (.base 6 (.d8 0x3))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6] []) (.reg (.gpr 2))) #v[6]
    (.letOp (n := 65) (.exec 0x101b09 (LoadPre 0x101b09 (fun s => AddrMode.addr (.base 6 (.d8 0x3)) s (0x101b09 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x101b09 2 (.base 6 (.d8 0x3))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 66) (.out 0x101b0c (movR32M32Effect 0x101b0c 12 (.base 6 (.d8 0x6))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 6] []) (.reg (.gpr 12))) #v[6]
    (.letOp (n := 67) (.exec 0x101b0c (LoadPre 0x101b0c (fun s => AddrMode.addr (.base 6 (.d8 0x6)) s (0x101b0c + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x101b0c 12 (.base 6 (.d8 0x6))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 68) (.out 0x101b10 (shrR32Effect 0x101b10 3 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[64]
    (.letOp (n := 69) (.exec 0x101b10 (fun s => s.RIP = 0x101b10) (shrR32Effect 0x101b10 3 2 2) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[64]
    (.letOp (n := 70) (.out 0x101b13 (andR32Imm32Effect 0x101b13 6 2 0x3ffffff) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[68]
    (.letOp (n := 71) (.exec 0x101b13 (fun s => s.RIP = 0x101b13) (andR32Imm32Effect 0x101b13 6 2 0x3ffffff) (Reg.operands [.gpr 2] [])) #v[68]
    (.letOp (n := 72) (.out 0x101b19 (addR32M32Effect 0x101b19 4 2 (.base 10 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 10] []) (.reg (.gpr 2))) #v[70, 10]
    (.letOp (n := 73) (.exec 0x101b19 (LoadPre 0x101b19 (fun s => AddrMode.addr (.base 10 (.d8 0x28)) s (0x101b19 + BitVec.ofNat 64 4)) 4) (addR32M32Effect 0x101b19 4 2 (.base 10 (.d8 0x28))) (Reg.operands [.gpr 2, .gpr 10] [])) #v[70, 10]
    (.letOp (n := 74) (.out 0x101b1d (shrR32Effect 0x101b1d 4 12 4) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[66]
    (.letOp (n := 75) (.exec 0x101b1d (fun s => s.RIP = 0x101b1d) (shrR32Effect 0x101b1d 4 12 4) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[66]
    (.letOp (n := 76) (.out 0x101b21 (andR32Imm32Effect 0x101b21 7 12 0x3ffffff) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[74]
    (.letOp (n := 77) (.exec 0x101b21 (fun s => s.RIP = 0x101b21) (andR32Imm32Effect 0x101b21 7 12 0x3ffffff) (Reg.operands [.gpr 12] [])) #v[74]
    (.letOp (n := 78) (.out 0x101b28 (addR32M32Effect 0x101b28 4 12 (.base 10 (.d8 0x2c))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 10] []) (.reg (.gpr 12))) #v[76, 10]
    (.letOp (n := 79) (.exec 0x101b28 (LoadPre 0x101b28 (fun s => AddrMode.addr (.base 10 (.d8 0x2c)) s (0x101b28 + BitVec.ofNat 64 4)) 4) (addR32M32Effect 0x101b28 4 12 (.base 10 (.d8 0x2c))) (Reg.operands [.gpr 12, .gpr 10] [])) #v[76, 10]
    (.letOp (n := 80) (.out 0x101b2c (movR32M32LowEffect 0x101b2c 1 (.base 6 (.d8 0x9))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[6]
    (.letOp (n := 81) (.exec 0x101b2c (LoadPre 0x101b2c (fun s => AddrMode.addr (.base 6 (.d8 0x9)) s (0x101b2c + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x101b2c 1 (.base 6 (.d8 0x9))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 82) (.out 0x101b2f (shrR32Effect 0x101b2f 3 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[80]
    (.letOp (n := 83) (.exec 0x101b2f (fun s => s.RIP = 0x101b2f) (shrR32Effect 0x101b2f 3 1 6) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[80]
    (.letOp (n := 84) (.out 0x101b32 (addR32M32Effect 0x101b32 4 1 (.base 10 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10] []) (.reg (.gpr 1))) #v[82, 10]
    (.letOp (n := 85) (.exec 0x101b32 (LoadPre 0x101b32 (fun s => AddrMode.addr (.base 10 (.d8 0x30)) s (0x101b32 + BitVec.ofNat 64 4)) 4) (addR32M32Effect 0x101b32 4 1 (.base 10 (.d8 0x30))) (Reg.operands [.gpr 1, .gpr 10] [])) #v[82, 10]
    (.letOp (n := 86) (.out 0x101b36 (movR32M32LowEffect 0x101b36 6 (.base 6 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[6]
    (.letOp (n := 87) (.exec 0x101b36 (LoadPre 0x101b36 (fun s => AddrMode.addr (.base 6 (.d8 0xc)) s (0x101b36 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x101b36 6 (.base 6 (.d8 0xc))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 88) (.out 0x101b39 (shrR32Effect 0x101b39 3 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[86]
    (.letOp (n := 89) (.exec 0x101b39 (fun s => s.RIP = 0x101b39) (shrR32Effect 0x101b39 3 6 8) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[86]
    (.letOp (n := 90) (.out 0x101b3c (addR32M32Effect 0x101b3c 4 7 (.base 10 (.d8 0x34))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 10] []) (.reg (.gpr 7))) #v[7, 10]
    (.letOp (n := 91) (.exec 0x101b3c (LoadPre 0x101b3c (fun s => AddrMode.addr (.base 10 (.d8 0x34)) s (0x101b3c + BitVec.ofNat 64 4)) 4) (addR32M32Effect 0x101b3c 4 7 (.base 10 (.d8 0x34))) (Reg.operands [.gpr 7, .gpr 10] [])) #v[7, 10]
    (.terminate (.br ⟨.l101b40, RegMap.args [(0, 0), (1, 84), (2, 72), (3, 56), (4, 4), (6, 88), (7, 90), (8, 8), (9, 53), (10, 10), (12, 78), (15, 62), (22, 22), (39, 39), (50, 50), (51, 51)] 92⟩))))))))))))))))))))))))))))))))))))))))

def bytes_l101af1 : List UInt8 :=
  [0x44, 0x8D, 0x0C, 0x89, 0x4C, 0x89, 0x0C, 0x24, 0x8D, 0x1C, 0x92, 0x41, 0xBF, 0xFF, 0xFF, 0xFF,
    0x03, 0x44, 0x23, 0x3E, 0x45, 0x03, 0x7A, 0x24, 0x8B, 0x56, 0x03, 0x44, 0x8B, 0x66, 0x06, 0xC1,
    0xEA, 0x02, 0x81, 0xE2, 0xFF, 0xFF, 0xFF, 0x03, 0x41, 0x03, 0x52, 0x28, 0x41, 0xC1, 0xEC, 0x04,
    0x41, 0x81, 0xE4, 0xFF, 0xFF, 0xFF, 0x03, 0x45, 0x03, 0x62, 0x2C, 0x8B, 0x4E, 0x09, 0xC1, 0xE9,
    0x06, 0x41, 0x03, 0x4A, 0x30, 0x8B, 0x76, 0x0C, 0xC1, 0xEE, 0x08, 0x41, 0x03, 0x7A, 0x34]

theorem code_l101af1 : ∀ x ∈ codeRange 0x101af1 bytes_l101af1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1af1 79 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101b40 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101b40 (addR32R32Effect 0x101b40 2 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[7, 6]
    (.letOp (n := 54) (.exec 0x101b40 (fun s => s.RIP = 0x101b40) (addR32R32Effect 0x101b40 2 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[7, 6]
    (.letOp (n := 55) (.out 0x101b42 (movR64R64Effect 0x101b42 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 56) (.exec 0x101b42 (fun s => s.RIP = 0x101b42) (movR64R64Effect 0x101b42 6 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 57) (.out 0x101b45 (imulR64R64Effect 0x101b45 4 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 8] []) (.reg (.gpr 6))) #v[55, 8]
    (.letOp (n := 58) (.exec 0x101b45 (fun s => s.RIP = 0x101b45) (imulR64R64Effect 0x101b45 4 6 8) (Reg.operands [.gpr 6, .gpr 8] [])) #v[55, 8]
    (.letOp (n := 59) (.out 0x101b49 (movR64R64Effect 0x101b49 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[2]
    (.letOp (n := 60) (.exec 0x101b49 (fun s => s.RIP = 0x101b49) (movR64R64Effect 0x101b49 5 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 61) (.out 0x101b4c (imulR64R64Effect 0x101b4c 4 5 3) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 3] []) (.reg (.gpr 5))) #v[59, 3]
    (.letOp (n := 62) (.exec 0x101b4c (fun s => s.RIP = 0x101b4c) (imulR64R64Effect 0x101b4c 4 5 3) (Reg.operands [.gpr 5, .gpr 3] [])) #v[59, 3]
    (.letOp (n := 63) (.out 0x101b50 (addR64R64Effect 0x101b50 5 6) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 6] []) (.reg (.gpr 5))) #v[61, 57]
    (.letOp (n := 64) (.exec 0x101b50 (fun s => s.RIP = 0x101b50) (addR64R64Effect 0x101b50 5 6) (Reg.operands [.gpr 5, .gpr 6] [])) #v[61, 57]
    (.letOp (n := 65) (.out 0x101b53 (movR64R64Effect 0x101b53 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 12] []) (.reg (.gpr 6))) #v[12]
    (.letOp (n := 66) (.exec 0x101b53 (fun s => s.RIP = 0x101b53) (movR64R64Effect 0x101b53 6 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 67) (.out 0x101b56 (imulR64R64Effect 0x101b56 4 6 9) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 9] []) (.reg (.gpr 6))) #v[65, 9]
    (.letOp (n := 68) (.exec 0x101b56 (fun s => s.RIP = 0x101b56) (imulR64R64Effect 0x101b56 4 6 9) (Reg.operands [.gpr 6, .gpr 9] [])) #v[65, 9]
    (.letOp (n := 69) (.out 0x101b5a (movR64R64Effect 0x101b5a 13 1) (EffectPart.reads (.reg (.gpr 13)) [.gpr 1] []) (.reg (.gpr 13))) #v[1]
    (.letOp (n := 70) (.exec 0x101b5a (fun s => s.RIP = 0x101b5a) (movR64R64Effect 0x101b5a 13 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 71) (.out 0x101b5d (imulR64R64Effect 0x101b5d 4 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 0] []) (.reg (.gpr 13))) #v[69, 0]
    (.letOp (n := 72) (.exec 0x101b5d (fun s => s.RIP = 0x101b5d) (imulR64R64Effect 0x101b5d 4 13 0) (Reg.operands [.gpr 13, .gpr 0] [])) #v[69, 0]
    (.letOp (n := 73) (.out 0x101b61 (addR64R64Effect 0x101b61 13 6) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 6] []) (.reg (.gpr 13))) #v[71, 67]
    (.letOp (n := 74) (.exec 0x101b61 (fun s => s.RIP = 0x101b61) (addR64R64Effect 0x101b61 13 6) (Reg.operands [.gpr 13, .gpr 6] [])) #v[71, 67]
    (.letOp (n := 75) (.out 0x101b64 (addR64R64Effect 0x101b64 13 5) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 5] []) (.reg (.gpr 13))) #v[73, 63]
    (.letOp (n := 76) (.exec 0x101b64 (fun s => s.RIP = 0x101b64) (addR64R64Effect 0x101b64 13 5) (Reg.operands [.gpr 13, .gpr 5] [])) #v[73, 63]
    (.letOp (n := 77) (.out 0x101b67 (movR32M32Effect 0x101b67 5 (.base 10 (.d8 0x14))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 10] []) (.reg (.gpr 5))) #v[10]
    (.letOp (n := 78) (.exec 0x101b67 (LoadPre 0x101b67 (fun s => AddrMode.addr (.base 10 (.d8 0x14)) s (0x101b67 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x101b67 5 (.base 10 (.d8 0x14))) (Reg.operands [.gpr 10] [])) #v[10]
    (.letOp (n := 79) (.out 0x101b6b (leaR32Effect 0x101b6b 5 11 (.sib 5 (some 5) 2 (.d8 0x0))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 5, .gpr 5] []) (.reg (.gpr 11))) #v[77, 77]
    (.letOp (n := 80) (.exec 0x101b6b (fun s => s.RIP = 0x101b6b) (leaR32Effect 0x101b6b 5 11 (.sib 5 (some 5) 2 (.d8 0x0))) (Reg.operands [.gpr 5, .gpr 5] [])) #v[77, 77]
    (.letOp (n := 81) (.out 0x101b70 (imulR64R64Effect 0x101b70 4 11 7) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 7] []) (.reg (.gpr 11))) #v[79, 53]
    (.letOp (n := 82) (.exec 0x101b70 (fun s => s.RIP = 0x101b70) (imulR64R64Effect 0x101b70 4 11 7) (Reg.operands [.gpr 11, .gpr 7] [])) #v[79, 53]
    (.letOp (n := 83) (.out 0x101b74 (addR64R64Effect 0x101b74 11 13) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 13] []) (.reg (.gpr 11))) #v[81, 75]
    (.letOp (n := 84) (.exec 0x101b74 (fun s => s.RIP = 0x101b74) (addR64R64Effect 0x101b74 11 13) (Reg.operands [.gpr 11, .gpr 13] [])) #v[81, 75]
    (.letOp (n := 85) (.out 0x101b77 (movR64R64Effect 0x101b77 13 15) (EffectPart.reads (.reg (.gpr 13)) [.gpr 15] []) (.reg (.gpr 13))) #v[15]
    (.letOp (n := 86) (.exec 0x101b77 (fun s => s.RIP = 0x101b77) (movR64R64Effect 0x101b77 13 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 87) (.out 0x101b7a (imulR64R64Effect 0x101b7a 4 13 5) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 5] []) (.reg (.gpr 13))) #v[85, 77]
    (.letOp (n := 88) (.exec 0x101b7a (fun s => s.RIP = 0x101b7a) (imulR64R64Effect 0x101b7a 4 13 5) (Reg.operands [.gpr 13, .gpr 5] [])) #v[85, 77]
    (.letOp (n := 89) (.out 0x101b7e (movR64R64Effect 0x101b7e 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[2]
    (.letOp (n := 90) (.exec 0x101b7e (fun s => s.RIP = 0x101b7e) (movR64R64Effect 0x101b7e 14 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 91) (.out 0x101b81 (imulR64R64Effect 0x101b81 4 14 8) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 8] []) (.reg (.gpr 14))) #v[89, 8]
    (.letOp (n := 92) (.exec 0x101b81 (fun s => s.RIP = 0x101b81) (imulR64R64Effect 0x101b81 4 14 8) (Reg.operands [.gpr 14, .gpr 8] [])) #v[89, 8]
    (.terminate (.br ⟨.l101b85, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 77), (6, 67), (7, 53), (8, 8), (9, 9), (10, 10), (11, 83), (12, 12), (13, 87), (14, 91), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 93⟩)))))))))))))))))))))))))))))))))))))))))

def bytes_l101b40 : List UInt8 :=
  [0x01, 0xF7, 0x4C, 0x89, 0xFE, 0x49, 0x0F, 0xAF, 0xF0, 0x48, 0x89, 0xD5, 0x48, 0x0F, 0xAF, 0xEB,
    0x48, 0x01, 0xF5, 0x4C, 0x89, 0xE6, 0x49, 0x0F, 0xAF, 0xF1, 0x49, 0x89, 0xCD, 0x4C, 0x0F, 0xAF,
    0xE8, 0x49, 0x01, 0xF5, 0x49, 0x01, 0xED, 0x41, 0x8B, 0x6A, 0x14, 0x44, 0x8D, 0x5C, 0xAD, 0x00,
    0x4C, 0x0F, 0xAF, 0xDF, 0x4D, 0x01, 0xEB, 0x4D, 0x89, 0xFD, 0x4C, 0x0F, 0xAF, 0xED, 0x49, 0x89,
    0xD6, 0x4D, 0x0F, 0xAF, 0xF0]

theorem code_l101b40 : ∀ x ∈ codeRange 0x101b40 bytes_l101b40, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1b40 69 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101b85 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101b85 (movR64R64Effect 0x101b85 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 8] []) (.reg (.gpr 9))) #v[8]
    (.letOp (n := 54) (.exec 0x101b85 (fun s => s.RIP = 0x101b85) (movR64R64Effect 0x101b85 9 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 55) (.out 0x101b88 (addR64R64Effect 0x101b88 14 13) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 13] []) (.reg (.gpr 14))) #v[14, 13]
    (.letOp (n := 56) (.exec 0x101b88 (fun s => s.RIP = 0x101b88) (addR64R64Effect 0x101b88 14 13) (Reg.operands [.gpr 14, .gpr 13] [])) #v[14, 13]
    (.letOp (n := 57) (.out 0x101b8b (movR64R64Effect 0x101b8b 13 12) (EffectPart.reads (.reg (.gpr 13)) [.gpr 12] []) (.reg (.gpr 13))) #v[12]
    (.letOp (n := 58) (.exec 0x101b8b (fun s => s.RIP = 0x101b8b) (movR64R64Effect 0x101b8b 13 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 59) (.out 0x101b8e (imulR64R64Effect 0x101b8e 4 13 3) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 3] []) (.reg (.gpr 13))) #v[57, 3]
    (.letOp (n := 60) (.exec 0x101b8e (fun s => s.RIP = 0x101b8e) (imulR64R64Effect 0x101b8e 4 13 3) (Reg.operands [.gpr 13, .gpr 3] [])) #v[57, 3]
    (.letOp (n := 61) (.out 0x101b92 (movR64R64Effect 0x101b92 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[1]
    (.letOp (n := 62) (.exec 0x101b92 (fun s => s.RIP = 0x101b92) (movR64R64Effect 0x101b92 0 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 63) (.out 0x101b95 (movR64M64Effect 0x101b95 8 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 64) (.exec 0x101b95 (LoadPre 0x101b95 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x101b95 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x101b95 8 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x101b99 (imulR64R64Effect 0x101b99 4 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 8] []) (.reg (.gpr 0))) #v[61, 63]
    (.letOp (n := 66) (.exec 0x101b99 (fun s => s.RIP = 0x101b99) (imulR64R64Effect 0x101b99 4 0 8) (Reg.operands [.gpr 0, .gpr 8] [])) #v[61, 63]
    (.letOp (n := 67) (.out 0x101b9d (addR64R64Effect 0x101b9d 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 13] []) (.reg (.gpr 0))) #v[65, 59]
    (.letOp (n := 68) (.exec 0x101b9d (fun s => s.RIP = 0x101b9d) (addR64R64Effect 0x101b9d 0 13) (Reg.operands [.gpr 0, .gpr 13] [])) #v[65, 59]
    (.letOp (n := 69) (.out 0x101ba0 (addR64R64Effect 0x101ba0 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[67, 55]
    (.letOp (n := 70) (.exec 0x101ba0 (fun s => s.RIP = 0x101ba0) (addR64R64Effect 0x101ba0 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[67, 55]
    (.letOp (n := 71) (.out 0x101ba3 (movR64M64Effect 0x101ba3 6 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 72) (.exec 0x101ba3 (LoadPre 0x101ba3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x101ba3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101ba3 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.out 0x101ba8 (imulR64R64Effect 0x101ba8 4 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7] []) (.reg (.gpr 6))) #v[71, 7]
    (.letOp (n := 74) (.exec 0x101ba8 (fun s => s.RIP = 0x101ba8) (imulR64R64Effect 0x101ba8 4 6 7) (Reg.operands [.gpr 6, .gpr 7] [])) #v[71, 7]
    (.letOp (n := 75) (.out 0x101bac (addR64R64Effect 0x101bac 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[73, 69]
    (.letOp (n := 76) (.exec 0x101bac (fun s => s.RIP = 0x101bac) (addR64R64Effect 0x101bac 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[73, 69]
    (.letOp (n := 77) (.exec 0x101baf (StorePre 0x101baf 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x101baf + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101baf 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[75, 4]
    (.letOp (n := 78) (.out 0x101bb4 (movR64R64Effect 0x101bb4 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[15]
    (.letOp (n := 79) (.exec 0x101bb4 (fun s => s.RIP = 0x101bb4) (movR64R64Effect 0x101bb4 0 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 80) (.out 0x101bb7 (movR64M64Effect 0x101bb7 6 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 81) (.exec 0x101bb7 (LoadPre 0x101bb7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x101bb7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101bb7 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 82) (.out 0x101bbc (imulR64R64Effect 0x101bbc 4 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[78, 80]
    (.letOp (n := 83) (.exec 0x101bbc (fun s => s.RIP = 0x101bbc) (imulR64R64Effect 0x101bbc 4 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[78, 80]
    (.letOp (n := 84) (.out 0x101bc0 (movR64R64Effect 0x101bc0 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[2]
    (.letOp (n := 85) (.exec 0x101bc0 (fun s => s.RIP = 0x101bc0) (movR64R64Effect 0x101bc0 14 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 86) (.out 0x101bc3 (imulR64R64Effect 0x101bc3 4 14 5) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 5] []) (.reg (.gpr 14))) #v[84, 5]
    (.letOp (n := 87) (.exec 0x101bc3 (fun s => s.RIP = 0x101bc3) (imulR64R64Effect 0x101bc3 4 14 5) (Reg.operands [.gpr 14, .gpr 5] [])) #v[84, 5]
    (.letOp (n := 88) (.out 0x101bc7 (addR64R64Effect 0x101bc7 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 0] []) (.reg (.gpr 14))) #v[86, 82]
    (.letOp (n := 89) (.exec 0x101bc7 (fun s => s.RIP = 0x101bc7) (addR64R64Effect 0x101bc7 14 0) (Reg.operands [.gpr 14, .gpr 0] [])) #v[86, 82]
    (.letOp (n := 90) (.out 0x101bca (movR64R64Effect 0x101bca 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[12]
    (.letOp (n := 91) (.exec 0x101bca (fun s => s.RIP = 0x101bca) (movR64R64Effect 0x101bca 0 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.terminate (.br ⟨.l101bcd, RegMap.args [(0, 90), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 80), (7, 7), (8, 63), (9, 53), (10, 10), (11, 11), (12, 12), (13, 59), (14, 88), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 92⟩))))))))))))))))))))))))))))))))))))))))

def bytes_l101b85 : List UInt8 :=
  [0x4D, 0x89, 0xC1, 0x4D, 0x01, 0xEE, 0x4D, 0x89, 0xE5, 0x4C, 0x0F, 0xAF, 0xEB, 0x48, 0x89, 0xC8,
    0x4C, 0x8B, 0x04, 0x24, 0x49, 0x0F, 0xAF, 0xC0, 0x4C, 0x01, 0xE8, 0x4C, 0x01, 0xF0, 0x48, 0x8B,
    0x74, 0x24, 0x08, 0x48, 0x0F, 0xAF, 0xF7, 0x48, 0x01, 0xC6, 0x48, 0x89, 0x74, 0x24, 0x08, 0x4C,
    0x89, 0xF8, 0x48, 0x8B, 0x74, 0x24, 0x10, 0x48, 0x0F, 0xAF, 0xC6, 0x49, 0x89, 0xD6, 0x4C, 0x0F,
    0xAF, 0xF5, 0x49, 0x01, 0xC6, 0x4C, 0x89, 0xE0]

theorem code_l101b85 : ∀ x ∈ codeRange 0x101b85 bytes_l101b85, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1b85 72 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101bcd : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101bcd (imulR64R64Effect 0x101bcd 4 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[0, 9]
    (.letOp (n := 54) (.exec 0x101bcd (fun s => s.RIP = 0x101bcd) (imulR64R64Effect 0x101bcd 4 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[0, 9]
    (.letOp (n := 55) (.out 0x101bd1 (movR64R64Effect 0x101bd1 13 1) (EffectPart.reads (.reg (.gpr 13)) [.gpr 1] []) (.reg (.gpr 13))) #v[1]
    (.letOp (n := 56) (.exec 0x101bd1 (fun s => s.RIP = 0x101bd1) (movR64R64Effect 0x101bd1 13 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 57) (.out 0x101bd4 (imulR64R64Effect 0x101bd4 4 13 3) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 3] []) (.reg (.gpr 13))) #v[55, 3]
    (.letOp (n := 58) (.exec 0x101bd4 (fun s => s.RIP = 0x101bd4) (imulR64R64Effect 0x101bd4 4 13 3) (Reg.operands [.gpr 13, .gpr 3] [])) #v[55, 3]
    (.letOp (n := 59) (.out 0x101bd8 (addR64R64Effect 0x101bd8 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 0] []) (.reg (.gpr 13))) #v[57, 53]
    (.letOp (n := 60) (.exec 0x101bd8 (fun s => s.RIP = 0x101bd8) (addR64R64Effect 0x101bd8 13 0) (Reg.operands [.gpr 13, .gpr 0] [])) #v[57, 53]
    (.letOp (n := 61) (.out 0x101bdb (addR64R64Effect 0x101bdb 13 14) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 14] []) (.reg (.gpr 13))) #v[59, 14]
    (.letOp (n := 62) (.exec 0x101bdb (fun s => s.RIP = 0x101bdb) (addR64R64Effect 0x101bdb 13 14) (Reg.operands [.gpr 13, .gpr 14] [])) #v[59, 14]
    (.letOp (n := 63) (.out 0x101bde (movR64R64Effect 0x101bde 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[8]
    (.letOp (n := 64) (.exec 0x101bde (fun s => s.RIP = 0x101bde) (movR64R64Effect 0x101bde 0 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 65) (.out 0x101be1 (imulR64R64Effect 0x101be1 4 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[63, 7]
    (.letOp (n := 66) (.exec 0x101be1 (fun s => s.RIP = 0x101be1) (imulR64R64Effect 0x101be1 4 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[63, 7]
    (.letOp (n := 67) (.out 0x101be5 (addR64R64Effect 0x101be5 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 13] []) (.reg (.gpr 0))) #v[65, 61]
    (.letOp (n := 68) (.exec 0x101be5 (fun s => s.RIP = 0x101be5) (addR64R64Effect 0x101be5 0 13) (Reg.operands [.gpr 0, .gpr 13] [])) #v[65, 61]
    (.letOp (n := 69) (.exec 0x101be8 (StorePre 0x101be8 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x101be8 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x101be8 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[67, 4]
    (.letOp (n := 70) (.out 0x101bec (movR64R64Effect 0x101bec 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[15]
    (.letOp (n := 71) (.exec 0x101bec (fun s => s.RIP = 0x101bec) (movR64R64Effect 0x101bec 0 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 72) (.out 0x101bef (movR64M64Effect 0x101bef 8 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 73) (.exec 0x101bef (LoadPre 0x101bef (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x101bef + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101bef 8 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.out 0x101bf4 (imulR64R64Effect 0x101bf4 4 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 8] []) (.reg (.gpr 0))) #v[70, 72]
    (.letOp (n := 75) (.exec 0x101bf4 (fun s => s.RIP = 0x101bf4) (imulR64R64Effect 0x101bf4 4 0 8) (Reg.operands [.gpr 0, .gpr 8] [])) #v[70, 72]
    (.letOp (n := 76) (.out 0x101bf8 (movR64R64Effect 0x101bf8 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[2]
    (.letOp (n := 77) (.exec 0x101bf8 (fun s => s.RIP = 0x101bf8) (movR64R64Effect 0x101bf8 14 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 78) (.out 0x101bfb (imulR64R64Effect 0x101bfb 4 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 6] []) (.reg (.gpr 14))) #v[76, 6]
    (.letOp (n := 79) (.exec 0x101bfb (fun s => s.RIP = 0x101bfb) (imulR64R64Effect 0x101bfb 4 14 6) (Reg.operands [.gpr 14, .gpr 6] [])) #v[76, 6]
    (.letOp (n := 80) (.out 0x101bff (addR64R64Effect 0x101bff 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 0] []) (.reg (.gpr 14))) #v[78, 74]
    (.letOp (n := 81) (.exec 0x101bff (fun s => s.RIP = 0x101bff) (addR64R64Effect 0x101bff 14 0) (Reg.operands [.gpr 14, .gpr 0] [])) #v[78, 74]
    (.letOp (n := 82) (.out 0x101c02 (movR64R64Effect 0x101c02 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[12]
    (.letOp (n := 83) (.exec 0x101c02 (fun s => s.RIP = 0x101c02) (movR64R64Effect 0x101c02 0 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 84) (.out 0x101c05 (imulR64R64Effect 0x101c05 4 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[82, 5]
    (.letOp (n := 85) (.exec 0x101c05 (fun s => s.RIP = 0x101c05) (imulR64R64Effect 0x101c05 4 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[82, 5]
    (.letOp (n := 86) (.out 0x101c09 (movR64R64Effect 0x101c09 13 1) (EffectPart.reads (.reg (.gpr 13)) [.gpr 1] []) (.reg (.gpr 13))) #v[1]
    (.letOp (n := 87) (.exec 0x101c09 (fun s => s.RIP = 0x101c09) (movR64R64Effect 0x101c09 13 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 88) (.out 0x101c0c (imulR64R64Effect 0x101c0c 4 13 9) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 9] []) (.reg (.gpr 13))) #v[86, 9]
    (.letOp (n := 89) (.exec 0x101c0c (fun s => s.RIP = 0x101c0c) (imulR64R64Effect 0x101c0c 4 13 9) (Reg.operands [.gpr 13, .gpr 9] [])) #v[86, 9]
    (.letOp (n := 90) (.out 0x101c10 (addR64R64Effect 0x101c10 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 0] []) (.reg (.gpr 13))) #v[88, 84]
    (.letOp (n := 91) (.exec 0x101c10 (fun s => s.RIP = 0x101c10) (addR64R64Effect 0x101c10 13 0) (Reg.operands [.gpr 13, .gpr 0] [])) #v[88, 84]
    (.terminate (.br ⟨.l101c13, RegMap.args [(0, 84), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 72), (9, 9), (10, 10), (11, 11), (12, 12), (13, 90), (14, 80), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 92⟩))))))))))))))))))))))))))))))))))))))))

def bytes_l101bcd : List UInt8 :=
  [0x49, 0x0F, 0xAF, 0xC1, 0x49, 0x89, 0xCD, 0x4C, 0x0F, 0xAF, 0xEB, 0x49, 0x01, 0xC5, 0x4D, 0x01,
    0xF5, 0x4C, 0x89, 0xC0, 0x48, 0x0F, 0xAF, 0xC7, 0x4C, 0x01, 0xE8, 0x48, 0x89, 0x04, 0x24, 0x4C,
    0x89, 0xF8, 0x4C, 0x8B, 0x44, 0x24, 0x18, 0x49, 0x0F, 0xAF, 0xC0, 0x49, 0x89, 0xD6, 0x4C, 0x0F,
    0xAF, 0xF6, 0x49, 0x01, 0xC6, 0x4C, 0x89, 0xE0, 0x48, 0x0F, 0xAF, 0xC5, 0x49, 0x89, 0xCD, 0x4D,
    0x0F, 0xAF, 0xE9, 0x49, 0x01, 0xC5]

theorem code_l101bcd : ∀ x ∈ codeRange 0x101bcd bytes_l101bcd, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1bcd 70 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101c13 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101c13 (addR64R64Effect 0x101c13 13 14) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 14] []) (.reg (.gpr 13))) #v[13, 14]
    (.letOp (n := 54) (.exec 0x101c13 (fun s => s.RIP = 0x101c13) (addR64R64Effect 0x101c13 13 14) (Reg.operands [.gpr 13, .gpr 14] [])) #v[13, 14]
    (.letOp (n := 55) (.out 0x101c16 (imulR64R64Effect 0x101c16 4 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 7] []) (.reg (.gpr 3))) #v[3, 7]
    (.letOp (n := 56) (.exec 0x101c16 (fun s => s.RIP = 0x101c16) (imulR64R64Effect 0x101c16 4 3 7) (Reg.operands [.gpr 3, .gpr 7] [])) #v[3, 7]
    (.letOp (n := 57) (.out 0x101c1a (addR64R64Effect 0x101c1a 3 13) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 13] []) (.reg (.gpr 3))) #v[55, 53]
    (.letOp (n := 58) (.exec 0x101c1a (fun s => s.RIP = 0x101c1a) (addR64R64Effect 0x101c1a 3 13) (Reg.operands [.gpr 3, .gpr 13] [])) #v[55, 53]
    (.letOp (n := 59) (.out 0x101c1d (imulR64M64Effect 0x101c1d 6 15 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 4] []) (.reg (.gpr 15))) #v[15, 4]
    (.letOp (n := 60) (.exec 0x101c1d (LoadPre 0x101c1d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x101c1d + BitVec.ofNat 64 6)) 8) (imulR64M64Effect 0x101c1d 6 15 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[15, 4]
    (.letOp (n := 61) (.out 0x101c23 (imulR64R64Effect 0x101c23 4 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 8] []) (.reg (.gpr 2))) #v[2, 8]
    (.letOp (n := 62) (.exec 0x101c23 (fun s => s.RIP = 0x101c23) (imulR64R64Effect 0x101c23 4 2 8) (Reg.operands [.gpr 2, .gpr 8] [])) #v[2, 8]
    (.letOp (n := 63) (.out 0x101c27 (addR64R64Effect 0x101c27 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 15] []) (.reg (.gpr 2))) #v[61, 59]
    (.letOp (n := 64) (.exec 0x101c27 (fun s => s.RIP = 0x101c27) (addR64R64Effect 0x101c27 2 15) (Reg.operands [.gpr 2, .gpr 15] [])) #v[61, 59]
    (.letOp (n := 65) (.out 0x101c2a (imulR64R64Effect 0x101c2a 4 12 6) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 6] []) (.reg (.gpr 12))) #v[12, 6]
    (.letOp (n := 66) (.exec 0x101c2a (fun s => s.RIP = 0x101c2a) (imulR64R64Effect 0x101c2a 4 12 6) (Reg.operands [.gpr 12, .gpr 6] [])) #v[12, 6]
    (.letOp (n := 67) (.out 0x101c2e (imulR64R64Effect 0x101c2e 4 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 5] []) (.reg (.gpr 1))) #v[1, 5]
    (.letOp (n := 68) (.exec 0x101c2e (fun s => s.RIP = 0x101c2e) (imulR64R64Effect 0x101c2e 4 1 5) (Reg.operands [.gpr 1, .gpr 5] [])) #v[1, 5]
    (.letOp (n := 69) (.out 0x101c32 (addR64R64Effect 0x101c32 1 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 12] []) (.reg (.gpr 1))) #v[67, 65]
    (.letOp (n := 70) (.exec 0x101c32 (fun s => s.RIP = 0x101c32) (addR64R64Effect 0x101c32 1 12) (Reg.operands [.gpr 1, .gpr 12] [])) #v[67, 65]
    (.letOp (n := 71) (.out 0x101c35 (addR64R64Effect 0x101c35 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[69, 63]
    (.letOp (n := 72) (.exec 0x101c35 (fun s => s.RIP = 0x101c35) (addR64R64Effect 0x101c35 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[69, 63]
    (.letOp (n := 73) (.out 0x101c38 (imulR64R64Effect 0x101c38 4 7 9) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 9] []) (.reg (.gpr 7))) #v[7, 9]
    (.letOp (n := 74) (.exec 0x101c38 (fun s => s.RIP = 0x101c38) (imulR64R64Effect 0x101c38 4 7 9) (Reg.operands [.gpr 7, .gpr 9] [])) #v[7, 9]
    (.letOp (n := 75) (.out 0x101c3c (addR64R64Effect 0x101c3c 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1] []) (.reg (.gpr 7))) #v[73, 71]
    (.letOp (n := 76) (.exec 0x101c3c (fun s => s.RIP = 0x101c3c) (addR64R64Effect 0x101c3c 7 1) (Reg.operands [.gpr 7, .gpr 1] [])) #v[73, 71]
    (.letOp (n := 77) (.out 0x101c3f (movR64R64Effect 0x101c3f 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[11]
    (.letOp (n := 78) (.exec 0x101c3f (fun s => s.RIP = 0x101c3f) (movR64R64Effect 0x101c3f 0 11) (Reg.operands [.gpr 11] [])) #v[11]
    (.letOp (n := 79) (.out 0x101c42 (shrR64Effect 0x101c42 4 0 26) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[77]
    (.letOp (n := 80) (.exec 0x101c42 (fun s => s.RIP = 0x101c42) (shrR64Effect 0x101c42 4 0 26) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[77]
    (.letOp (n := 81) (.out 0x101c46 (andR32Imm32Effect 0x101c46 7 11 0x3ffffff) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11] []) (.reg (.gpr 11))) #v[11]
    (.letOp (n := 82) (.exec 0x101c46 (fun s => s.RIP = 0x101c46) (andR32Imm32Effect 0x101c46 7 11 0x3ffffff) (Reg.operands [.gpr 11] [])) #v[11]
    (.letOp (n := 83) (.out 0x101c4d (movR32R32Effect 0x101c4d 3 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[79]
    (.letOp (n := 84) (.exec 0x101c4d (fun s => s.RIP = 0x101c4d) (movR32R32Effect 0x101c4d 3 8 0) (Reg.operands [.gpr 0] [])) #v[79]
    (.letOp (n := 85) (.out 0x101c50 (addR64M64Effect 0x101c50 8 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 4] []) (.reg (.gpr 8))) #v[83, 4]
    (.letOp (n := 86) (.exec 0x101c50 (LoadPre 0x101c50 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x101c50 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x101c50 8 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[83, 4]
    (.letOp (n := 87) (.out 0x101c55 (movR64R64Effect 0x101c55 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[85]
    (.letOp (n := 88) (.exec 0x101c55 (fun s => s.RIP = 0x101c55) (movR64R64Effect 0x101c55 0 8) (Reg.operands [.gpr 8] [])) #v[85]
    (.letOp (n := 89) (.out 0x101c58 (shrR64Effect 0x101c58 4 0 26) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[87]
    (.letOp (n := 90) (.exec 0x101c58 (fun s => s.RIP = 0x101c58) (shrR64Effect 0x101c58 4 0 26) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[87]
    (.letOp (n := 91) (.out 0x101c5c (andR32Imm32Effect 0x101c5c 7 8 0x3ffffff) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[85]
    (.letOp (n := 92) (.exec 0x101c5c (fun s => s.RIP = 0x101c5c) (andR32Imm32Effect 0x101c5c 7 8 0x3ffffff) (Reg.operands [.gpr 8] [])) #v[85]
    (.terminate (.br ⟨.l101c63, RegMap.args [(0, 89), (1, 71), (2, 63), (3, 57), (4, 4), (5, 5), (6, 6), (7, 75), (8, 91), (9, 9), (10, 10), (11, 81), (12, 65), (13, 53), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 93⟩)))))))))))))))))))))))))))))))))))))))))

def bytes_l101c13 : List UInt8 :=
  [0x4D, 0x01, 0xF5, 0x48, 0x0F, 0xAF, 0xDF, 0x4C, 0x01, 0xEB, 0x4C, 0x0F, 0xAF, 0x7C, 0x24, 0x20,
    0x49, 0x0F, 0xAF, 0xD0, 0x4C, 0x01, 0xFA, 0x4C, 0x0F, 0xAF, 0xE6, 0x48, 0x0F, 0xAF, 0xCD, 0x4C,
    0x01, 0xE1, 0x48, 0x01, 0xD1, 0x49, 0x0F, 0xAF, 0xF9, 0x48, 0x01, 0xCF, 0x4C, 0x89, 0xD8, 0x48,
    0xC1, 0xE8, 0x1A, 0x41, 0x81, 0xE3, 0xFF, 0xFF, 0xFF, 0x03, 0x41, 0x89, 0xC0, 0x4C, 0x03, 0x44,
    0x24, 0x08, 0x4C, 0x89, 0xC0, 0x48, 0xC1, 0xE8, 0x1A, 0x41, 0x81, 0xE0, 0xFF, 0xFF, 0xFF, 0x03]

theorem code_l101c13 : ∀ x ∈ codeRange 0x101c13 bytes_l101c13, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c13 80 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101c63 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101c63 (movR32R32Effect 0x101c63 3 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[0]
    (.letOp (n := 54) (.exec 0x101c63 (fun s => s.RIP = 0x101c63) (movR32R32Effect 0x101c63 3 9 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x101c66 (addR64M64Effect 0x101c66 9 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 4] []) (.reg (.gpr 9))) #v[53, 4]
    (.letOp (n := 56) (.exec 0x101c66 (LoadPre 0x101c66 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x101c66 + BitVec.ofNat 64 4)) 8) (addR64M64Effect 0x101c66 9 (.sib 4 none 0 .none)) (Reg.operands [.gpr 9, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 57) (.out 0x101c6a (movR64R64Effect 0x101c6a 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[55]
    (.letOp (n := 58) (.exec 0x101c6a (fun s => s.RIP = 0x101c6a) (movR64R64Effect 0x101c6a 0 9) (Reg.operands [.gpr 9] [])) #v[55]
    (.letOp (n := 59) (.out 0x101c6d (shrR64Effect 0x101c6d 4 0 26) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[57]
    (.letOp (n := 60) (.exec 0x101c6d (fun s => s.RIP = 0x101c6d) (shrR64Effect 0x101c6d 4 0 26) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[57]
    (.letOp (n := 61) (.out 0x101c71 (movR32R32Effect 0x101c71 2 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0] []) (.reg (.gpr 2))) #v[59]
    (.letOp (n := 62) (.exec 0x101c71 (fun s => s.RIP = 0x101c71) (movR32R32Effect 0x101c71 2 2 0) (Reg.operands [.gpr 0] [])) #v[59]
    (.letOp (n := 63) (.out 0x101c73 (addR64R64Effect 0x101c73 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 3] []) (.reg (.gpr 2))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x101c73 (fun s => s.RIP = 0x101c73) (addR64R64Effect 0x101c73 2 3) (Reg.operands [.gpr 2, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x101c76 (movR64R64Effect 0x101c76 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[63]
    (.letOp (n := 66) (.exec 0x101c76 (fun s => s.RIP = 0x101c76) (movR64R64Effect 0x101c76 0 2) (Reg.operands [.gpr 2] [])) #v[63]
    (.letOp (n := 67) (.out 0x101c79 (shrR64Effect 0x101c79 4 0 26) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 68) (.exec 0x101c79 (fun s => s.RIP = 0x101c79) (shrR64Effect 0x101c79 4 0 26) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[65]
    (.letOp (n := 69) (.out 0x101c7d (movR32R32Effect 0x101c7d 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[67]
    (.letOp (n := 70) (.exec 0x101c7d (fun s => s.RIP = 0x101c7d) (movR32R32Effect 0x101c7d 2 0 0) (Reg.operands [.gpr 0] [])) #v[67]
    (.letOp (n := 71) (.out 0x101c7f (addR64R64Effect 0x101c7f 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[69, 7]
    (.letOp (n := 72) (.exec 0x101c7f (fun s => s.RIP = 0x101c7f) (addR64R64Effect 0x101c7f 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[69, 7]
    (.letOp (n := 73) (.out 0x101c82 (movR64R64Effect 0x101c82 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[71]
    (.letOp (n := 74) (.exec 0x101c82 (fun s => s.RIP = 0x101c82) (movR64R64Effect 0x101c82 1 0) (Reg.operands [.gpr 0] [])) #v[71]
    (.letOp (n := 75) (.out 0x101c85 (shrR64Effect 0x101c85 4 1 26) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[73]
    (.letOp (n := 76) (.exec 0x101c85 (fun s => s.RIP = 0x101c85) (shrR64Effect 0x101c85 4 1 26) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[73]
    (.letOp (n := 77) (.out 0x101c89 (leaR32Effect 0x101c89 3 1 (.sib 1 (some 1) 2 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[75, 75]
    (.letOp (n := 78) (.exec 0x101c89 (fun s => s.RIP = 0x101c89) (leaR32Effect 0x101c89 3 1 (.sib 1 (some 1) 2 .none)) (Reg.operands [.gpr 1, .gpr 1] [])) #v[75, 75]
    (.letOp (n := 79) (.out 0x101c8c (addR32R32Effect 0x101c8c 3 1 11) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 11] []) (.reg (.gpr 1))) #v[77, 11]
    (.letOp (n := 80) (.exec 0x101c8c (fun s => s.RIP = 0x101c8c) (addR32R32Effect 0x101c8c 3 1 11) (Reg.operands [.gpr 1, .gpr 11] [])) #v[77, 11]
    (.letOp (n := 81) (.out 0x101c8f (movR32R32Effect 0x101c8f 2 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 1] []) (.reg (.gpr 6))) #v[79]
    (.letOp (n := 82) (.exec 0x101c8f (fun s => s.RIP = 0x101c8f) (movR32R32Effect 0x101c8f 2 6 1) (Reg.operands [.gpr 1] [])) #v[79]
    (.letOp (n := 83) (.out 0x101c91 (shrR32Effect 0x101c91 3 6 26) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[81]
    (.letOp (n := 84) (.exec 0x101c91 (fun s => s.RIP = 0x101c91) (shrR32Effect 0x101c91 3 6 26) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[81]
    (.letOp (n := 85) (.out 0x101c94 (addR32R32Effect 0x101c94 3 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 8] []) (.reg (.gpr 6))) #v[83, 8]
    (.letOp (n := 86) (.exec 0x101c94 (fun s => s.RIP = 0x101c94) (addR32R32Effect 0x101c94 3 6 8) (Reg.operands [.gpr 6, .gpr 8] [])) #v[83, 8]
    (.letOp (n := 87) (.out 0x101c97 (andR32Imm32Effect 0x101c97 6 1 0x3ffffff) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[79]
    (.letOp (n := 88) (.exec 0x101c97 (fun s => s.RIP = 0x101c97) (andR32Imm32Effect 0x101c97 6 1 0x3ffffff) (Reg.operands [.gpr 1] [])) #v[79]
    (.letOp (n := 89) (.exec 0x101c9d (StorePre 0x101c9d 4 (fun s => AddrMode.addr (.base 10 (.d8 0x24)) s (0x101c9d + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x101c9d 1 (.base 10 (.d8 0x24))) (Reg.operands [.gpr 1, .gpr 10] [])) #v[87, 10]
    (.letOp (n := 90) (.exec 0x101ca1 (StorePre 0x101ca1 4 (fun s => AddrMode.addr (.base 10 (.d8 0x28)) s (0x101ca1 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x101ca1 6 (.base 10 (.d8 0x28))) (Reg.operands [.gpr 6, .gpr 10] [])) #v[85, 10]
    (.terminate (.br ⟨.l101ca5, RegMap.args [(0, 71), (1, 87), (2, 63), (3, 3), (4, 4), (6, 85), (7, 7), (8, 8), (9, 55), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 91⟩)))))))))))))))))))))))))))))))))))))))

def bytes_l101c63 : List UInt8 :=
  [0x41, 0x89, 0xC1, 0x4C, 0x03, 0x0C, 0x24, 0x4C, 0x89, 0xC8, 0x48, 0xC1, 0xE8, 0x1A, 0x89, 0xC2,
    0x48, 0x01, 0xDA, 0x48, 0x89, 0xD0, 0x48, 0xC1, 0xE8, 0x1A, 0x89, 0xC0, 0x48, 0x01, 0xF8, 0x48,
    0x89, 0xC1, 0x48, 0xC1, 0xE9, 0x1A, 0x8D, 0x0C, 0x89, 0x44, 0x01, 0xD9, 0x89, 0xCE, 0xC1, 0xEE,
    0x1A, 0x44, 0x01, 0xC6, 0x81, 0xE1, 0xFF, 0xFF, 0xFF, 0x03, 0x41, 0x89, 0x4A, 0x24, 0x41, 0x89,
    0x72, 0x28]

theorem code_l101c63 : ∀ x ∈ codeRange 0x101c63 bytes_l101c63, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c63 66 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101ca5 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101ca5 (andR32Imm32Effect 0x101ca5 7 9 0x3ffffff) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[9]
    (.letOp (n := 54) (.exec 0x101ca5 (fun s => s.RIP = 0x101ca5) (andR32Imm32Effect 0x101ca5 7 9 0x3ffffff) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 55) (.exec 0x101cac (StorePre 0x101cac 4 (fun s => AddrMode.addr (.base 10 (.d8 0x2c)) s (0x101cac + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x101cac 9 (.base 10 (.d8 0x2c))) (Reg.operands [.gpr 9, .gpr 10] [])) #v[53, 10]
    (.letOp (n := 56) (.out 0x101cb0 (andR32Imm32Effect 0x101cb0 6 2 0x3ffffff) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[2]
    (.letOp (n := 57) (.exec 0x101cb0 (fun s => s.RIP = 0x101cb0) (andR32Imm32Effect 0x101cb0 6 2 0x3ffffff) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 58) (.exec 0x101cb6 (StorePre 0x101cb6 4 (fun s => AddrMode.addr (.base 10 (.d8 0x30)) s (0x101cb6 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x101cb6 2 (.base 10 (.d8 0x30))) (Reg.operands [.gpr 2, .gpr 10] [])) #v[56, 10]
    (.letOp (n := 59) (.out 0x101cba (andEaxImm32Effect 0x101cba 0x3ffffff) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 60) (.exec 0x101cba (fun s => s.RIP = 0x101cba) (andEaxImm32Effect 0x101cba 0x3ffffff) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 61) (.exec 0x101cbf (StorePre 0x101cbf 4 (fun s => AddrMode.addr (.base 10 (.d8 0x34)) s (0x101cbf + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x101cbf 0 (.base 10 (.d8 0x34))) (Reg.operands [.gpr 0, .gpr 10] [])) #v[59, 10]
    (.letOp (n := 62) (.out 0x101cc3 (addR64Imm8Effect 0x101cc3 4 0x28) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 63) (.exec 0x101cc3 (fun s => s.RIP = 0x101cc3) (addR64Imm8Effect 0x101cc3 4 0x28) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x101cc7 (popR64Effect 0x101cc7 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[62]
    (.letOp (n := 65) (.out 0x101cc7 (popR64Effect 0x101cc7 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[62]
    (.letOp (n := 66) (.exec 0x101cc7 (PopPre 0x101cc7) (popR64Effect 0x101cc7 1 3) (Reg.operands [.gpr 4] [])) #v[62]
    (.letOp (n := 67) (.out 0x101cc8 (popR64Effect 0x101cc8 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[65]
    (.letOp (n := 68) (.out 0x101cc8 (popR64Effect 0x101cc8 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 69) (.exec 0x101cc8 (PopPre 0x101cc8) (popR64Effect 0x101cc8 2 12) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 70) (.out 0x101cca (popR64Effect 0x101cca 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[68]
    (.letOp (n := 71) (.out 0x101cca (popR64Effect 0x101cca 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[68]
    (.letOp (n := 72) (.exec 0x101cca (PopPre 0x101cca) (popR64Effect 0x101cca 2 13) (Reg.operands [.gpr 4] [])) #v[68]
    (.letOp (n := 73) (.out 0x101ccc (popR64Effect 0x101ccc 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[71]
    (.letOp (n := 74) (.out 0x101ccc (popR64Effect 0x101ccc 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[71]
    (.letOp (n := 75) (.exec 0x101ccc (PopPre 0x101ccc) (popR64Effect 0x101ccc 2 14) (Reg.operands [.gpr 4] [])) #v[71]
    (.letOp (n := 76) (.out 0x101cce (popR64Effect 0x101cce 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[74]
    (.letOp (n := 77) (.out 0x101cce (popR64Effect 0x101cce 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[74]
    (.letOp (n := 78) (.exec 0x101cce (PopPre 0x101cce) (popR64Effect 0x101cce 2 15) (Reg.operands [.gpr 4] [])) #v[74]
    (.letOp (n := 79) (.out 0x101cd0 (popR64Effect 0x101cd0 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[77]
    (.letOp (n := 80) (.out 0x101cd0 (popR64Effect 0x101cd0 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[77]
    (.letOp (n := 81) (.exec 0x101cd0 (PopPre 0x101cd0) (popR64Effect 0x101cd0 1 5) (Reg.operands [.gpr 4] [])) #v[77]
    (.letOp (n := 82) (.out 0x101cd1 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[80]
    (.letOp (n := 83) (.out 0x101cd1 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[80]
    (.letOp (n := 84) (.exec 0x101cd1 (RetPre 0x101cd1) (retEffect) (Reg.operands [.gpr 4] [])) #v[80]
    (.terminate (.ret (RegMap.args [(0, 59), (1, 1), (2, 56), (3, 64), (4, 83), (5, 79), (6, 6), (7, 7), (9, 53), (10, 10), (12, 67), (13, 70), (14, 73), (15, 76), (22, 22), (39, 39), (50, 50), (51, 51)] 85) (some ⟨82, by decide⟩))))))))))))))))))))))))))))))))))

def bytes_l101ca5 : List UInt8 :=
  [0x41, 0x81, 0xE1, 0xFF, 0xFF, 0xFF, 0x03, 0x45, 0x89, 0x4A, 0x2C, 0x81, 0xE2, 0xFF, 0xFF, 0xFF,
    0x03, 0x41, 0x89, 0x52, 0x30, 0x25, 0xFF, 0xFF, 0xFF, 0x03, 0x41, 0x89, 0x42, 0x34, 0x48, 0x83,
    0xC4, 0x28, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l101ca5 : ∀ x ∈ codeRange 0x101ca5 bytes_l101ca5, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1ca5 45 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101ce0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101ce0 (pushR64Effect 0x101ce0 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x101ce0 (PushPre 0x101ce0 1) (pushR64Effect 0x101ce0 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x101ce1 (pushR64Effect 0x101ce1 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x101ce1 (PushPre 0x101ce1 2) (pushR64Effect 0x101ce1 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x101ce3 (pushR64Effect 0x101ce3 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x101ce3 (PushPre 0x101ce3 2) (pushR64Effect 0x101ce3 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x101ce5 (pushR64Effect 0x101ce5 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x101ce5 (PushPre 0x101ce5 2) (pushR64Effect 0x101ce5 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x101ce7 (pushR64Effect 0x101ce7 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x101ce7 (PushPre 0x101ce7 2) (pushR64Effect 0x101ce7 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x101ce9 (pushR64Effect 0x101ce9 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x101ce9 (PushPre 0x101ce9 1) (pushR64Effect 0x101ce9 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x101cea (movR64R64Effect 0x101cea 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 66) (.exec 0x101cea (fun s => s.RIP = 0x101cea) (movR64R64Effect 0x101cea 0 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 67) (.out 0x101ced (movR32M32Effect 0x101ced 11 (.base 6 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 6] []) (.reg (.gpr 11))) #v[6]
    (.letOp (n := 68) (.exec 0x101ced (LoadPre 0x101ced (fun s => AddrMode.addr (.base 6 (.d8 0x28)) s (0x101ced + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x101ced 11 (.base 6 (.d8 0x28))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 69) (.out 0x101cf1 (movR32R32Effect 0x101cf1 3 1 11) (EffectPart.reads (.reg (.gpr 1)) [.gpr 11] []) (.reg (.gpr 1))) #v[67]
    (.letOp (n := 70) (.exec 0x101cf1 (fun s => s.RIP = 0x101cf1) (movR32R32Effect 0x101cf1 3 1 11) (Reg.operands [.gpr 11] [])) #v[67]
    (.letOp (n := 71) (.out 0x101cf4 (shrR32Effect 0x101cf4 3 1 26) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[69]
    (.letOp (n := 72) (.exec 0x101cf4 (fun s => s.RIP = 0x101cf4) (shrR32Effect 0x101cf4 3 1 26) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[69]
    (.letOp (n := 73) (.out 0x101cf7 (addR32M32Effect 0x101cf7 3 1 (.base 6 (.d8 0x2c))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[71, 6]
    (.letOp (n := 74) (.exec 0x101cf7 (LoadPre 0x101cf7 (fun s => AddrMode.addr (.base 6 (.d8 0x2c)) s (0x101cf7 + BitVec.ofNat 64 3)) 4) (addR32M32Effect 0x101cf7 3 1 (.base 6 (.d8 0x2c))) (Reg.operands [.gpr 1, .gpr 6] [])) #v[71, 6]
    (.letOp (n := 75) (.out 0x101cfa (andR32Imm32Effect 0x101cfa 7 11 0x3ffffff) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11] []) (.reg (.gpr 11))) #v[67]
    (.letOp (n := 76) (.exec 0x101cfa (fun s => s.RIP = 0x101cfa) (andR32Imm32Effect 0x101cfa 7 11 0x3ffffff) (Reg.operands [.gpr 11] [])) #v[67]
    (.letOp (n := 77) (.out 0x101d01 (movR32R32Effect 0x101d01 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[73]
    (.letOp (n := 78) (.exec 0x101d01 (fun s => s.RIP = 0x101d01) (movR32R32Effect 0x101d01 2 2 1) (Reg.operands [.gpr 1] [])) #v[73]
    (.letOp (n := 79) (.out 0x101d03 (shrR32Effect 0x101d03 3 2 26) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[77]
    (.letOp (n := 80) (.exec 0x101d03 (fun s => s.RIP = 0x101d03) (shrR32Effect 0x101d03 3 2 26) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[77]
    (.letOp (n := 81) (.out 0x101d06 (andR32Imm32Effect 0x101d06 6 1 0x3ffffff) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[73]
    (.letOp (n := 82) (.exec 0x101d06 (fun s => s.RIP = 0x101d06) (andR32Imm32Effect 0x101d06 6 1 0x3ffffff) (Reg.operands [.gpr 1] [])) #v[73]
    (.letOp (n := 83) (.out 0x101d0c (addR32M32Effect 0x101d0c 3 2 (.base 6 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[79, 6]
    (.letOp (n := 84) (.exec 0x101d0c (LoadPre 0x101d0c (fun s => AddrMode.addr (.base 6 (.d8 0x30)) s (0x101d0c + BitVec.ofNat 64 3)) 4) (addR32M32Effect 0x101d0c 3 2 (.base 6 (.d8 0x30))) (Reg.operands [.gpr 2, .gpr 6] [])) #v[79, 6]
    (.letOp (n := 85) (.out 0x101d0f (movR32R32Effect 0x101d0f 3 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[83]
    (.letOp (n := 86) (.exec 0x101d0f (fun s => s.RIP = 0x101d0f) (movR32R32Effect 0x101d0f 3 8 2) (Reg.operands [.gpr 2] [])) #v[83]
    (.letOp (n := 87) (.out 0x101d12 (shrR32Effect 0x101d12 4 8 26) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[85]
    (.letOp (n := 88) (.exec 0x101d12 (fun s => s.RIP = 0x101d12) (shrR32Effect 0x101d12 4 8 26) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[85]
    (.letOp (n := 89) (.out 0x101d16 (andR32Imm32Effect 0x101d16 6 2 0x3ffffff) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[83]
    (.letOp (n := 90) (.exec 0x101d16 (fun s => s.RIP = 0x101d16) (andR32Imm32Effect 0x101d16 6 2 0x3ffffff) (Reg.operands [.gpr 2] [])) #v[83]
    (.letOp (n := 91) (.out 0x101d1c (addR32M32Effect 0x101d1c 4 8 (.base 6 (.d8 0x34))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6] []) (.reg (.gpr 8))) #v[87, 6]
    (.letOp (n := 92) (.exec 0x101d1c (LoadPre 0x101d1c (fun s => AddrMode.addr (.base 6 (.d8 0x34)) s (0x101d1c + BitVec.ofNat 64 4)) 4) (addR32M32Effect 0x101d1c 4 8 (.base 6 (.d8 0x34))) (Reg.operands [.gpr 8, .gpr 6] [])) #v[87, 6]
    (.terminate (.br ⟨.l101d20, RegMap.args [(0, 65), (1, 81), (2, 89), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 91), (11, 75), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 93⟩)))))))))))))))))))))))))))))))))))))))))

def bytes_l101ce0 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x89, 0xF8, 0x44, 0x8B, 0x5E,
    0x28, 0x44, 0x89, 0xD9, 0xC1, 0xE9, 0x1A, 0x03, 0x4E, 0x2C, 0x41, 0x81, 0xE3, 0xFF, 0xFF, 0xFF,
    0x03, 0x89, 0xCA, 0xC1, 0xEA, 0x1A, 0x81, 0xE1, 0xFF, 0xFF, 0xFF, 0x03, 0x03, 0x56, 0x30, 0x41,
    0x89, 0xD0, 0x41, 0xC1, 0xE8, 0x1A, 0x81, 0xE2, 0xFF, 0xFF, 0xFF, 0x03, 0x44, 0x03, 0x46, 0x34]

theorem code_l101ce0 : ∀ x ∈ codeRange 0x101ce0 bytes_l101ce0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1ce0 64 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101d20 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101d20 (movR32R32Effect 0x101d20 3 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 8] []) (.reg (.gpr 9))) #v[8]
    (.letOp (n := 54) (.exec 0x101d20 (fun s => s.RIP = 0x101d20) (movR32R32Effect 0x101d20 3 9 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 55) (.out 0x101d23 (shrR32Effect 0x101d23 4 9 26) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[53]
    (.letOp (n := 56) (.exec 0x101d23 (fun s => s.RIP = 0x101d23) (shrR32Effect 0x101d23 4 9 26) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 57) (.out 0x101d27 (movR32R32Effect 0x101d27 3 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 8] []) (.reg (.gpr 7))) #v[8]
    (.letOp (n := 58) (.exec 0x101d27 (fun s => s.RIP = 0x101d27) (movR32R32Effect 0x101d27 3 7 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 59) (.out 0x101d2a (andR32Imm32Effect 0x101d2a 6 7 0x3ffffff) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[57]
    (.letOp (n := 60) (.exec 0x101d2a (fun s => s.RIP = 0x101d2a) (andR32Imm32Effect 0x101d2a 6 7 0x3ffffff) (Reg.operands [.gpr 7] [])) #v[57]
    (.letOp (n := 61) (.out 0x101d30 (leaR32Effect 0x101d30 4 10 (.sib 9 (some 9) 2 .none)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 9, .gpr 9] []) (.reg (.gpr 10))) #v[55, 55]
    (.letOp (n := 62) (.exec 0x101d30 (fun s => s.RIP = 0x101d30) (leaR32Effect 0x101d30 4 10 (.sib 9 (some 9) 2 .none)) (Reg.operands [.gpr 9, .gpr 9] [])) #v[55, 55]
    (.letOp (n := 63) (.out 0x101d34 (addR32M32Effect 0x101d34 4 10 (.base 6 (.d8 0x24))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 6] []) (.reg (.gpr 10))) #v[61, 6]
    (.letOp (n := 64) (.exec 0x101d34 (LoadPre 0x101d34 (fun s => AddrMode.addr (.base 6 (.d8 0x24)) s (0x101d34 + BitVec.ofNat 64 4)) 4) (addR32M32Effect 0x101d34 4 10 (.base 6 (.d8 0x24))) (Reg.operands [.gpr 10, .gpr 6] [])) #v[61, 6]
    (.letOp (n := 65) (.out 0x101d38 (movR32R32Effect 0x101d38 3 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 10] []) (.reg (.gpr 9))) #v[63]
    (.letOp (n := 66) (.exec 0x101d38 (fun s => s.RIP = 0x101d38) (movR32R32Effect 0x101d38 3 9 10) (Reg.operands [.gpr 10] [])) #v[63]
    (.letOp (n := 67) (.out 0x101d3b (shrR32Effect 0x101d3b 4 9 26) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[65]
    (.letOp (n := 68) (.exec 0x101d3b (fun s => s.RIP = 0x101d3b) (shrR32Effect 0x101d3b 4 9 26) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[65]
    (.letOp (n := 69) (.out 0x101d3f (addR32R32Effect 0x101d3f 3 9 11) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 11] []) (.reg (.gpr 9))) #v[67, 11]
    (.letOp (n := 70) (.exec 0x101d3f (fun s => s.RIP = 0x101d3f) (addR32R32Effect 0x101d3f 3 9 11) (Reg.operands [.gpr 9, .gpr 11] [])) #v[67, 11]
    (.letOp (n := 71) (.out 0x101d42 (andR32Imm32Effect 0x101d42 7 10 0x3ffffff) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[63]
    (.letOp (n := 72) (.exec 0x101d42 (fun s => s.RIP = 0x101d42) (andR32Imm32Effect 0x101d42 7 10 0x3ffffff) (Reg.operands [.gpr 10] [])) #v[63]
    (.letOp (n := 73) (.out 0x101d49 (leaR32Effect 0x101d49 4 5 (.base 10 (.d8 0x5))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 10] []) (.reg (.gpr 5))) #v[71]
    (.letOp (n := 74) (.exec 0x101d49 (fun s => s.RIP = 0x101d49) (leaR32Effect 0x101d49 4 5 (.base 10 (.d8 0x5))) (Reg.operands [.gpr 10] [])) #v[71]
    (.letOp (n := 75) (.out 0x101d4d (movR32R32Effect 0x101d4d 3 11 5) (EffectPart.reads (.reg (.gpr 11)) [.gpr 5] []) (.reg (.gpr 11))) #v[73]
    (.letOp (n := 76) (.exec 0x101d4d (fun s => s.RIP = 0x101d4d) (movR32R32Effect 0x101d4d 3 11 5) (Reg.operands [.gpr 5] [])) #v[73]
    (.letOp (n := 77) (.out 0x101d50 (shrR32Effect 0x101d50 4 11 26) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[75]
    (.letOp (n := 78) (.exec 0x101d50 (fun s => s.RIP = 0x101d50) (shrR32Effect 0x101d50 4 11 26) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[75]
    (.letOp (n := 79) (.out 0x101d54 (addR32R32Effect 0x101d54 3 11 9) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 9] []) (.reg (.gpr 11))) #v[77, 69]
    (.letOp (n := 80) (.exec 0x101d54 (fun s => s.RIP = 0x101d54) (addR32R32Effect 0x101d54 3 11 9) (Reg.operands [.gpr 11, .gpr 9] [])) #v[77, 69]
    (.letOp (n := 81) (.out 0x101d57 (movR32R32Effect 0x101d57 3 3 11) (EffectPart.reads (.reg (.gpr 3)) [.gpr 11] []) (.reg (.gpr 3))) #v[79]
    (.letOp (n := 82) (.exec 0x101d57 (fun s => s.RIP = 0x101d57) (movR32R32Effect 0x101d57 3 3 11) (Reg.operands [.gpr 11] [])) #v[79]
    (.letOp (n := 83) (.out 0x101d5a (shrR32Effect 0x101d5a 3 3 26) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[81]
    (.letOp (n := 84) (.exec 0x101d5a (fun s => s.RIP = 0x101d5a) (shrR32Effect 0x101d5a 3 3 26) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[81]
    (.letOp (n := 85) (.out 0x101d5d (addR32R32Effect 0x101d5d 2 3 1) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 1] []) (.reg (.gpr 3))) #v[83, 1]
    (.letOp (n := 86) (.exec 0x101d5d (fun s => s.RIP = 0x101d5d) (addR32R32Effect 0x101d5d 2 3 1) (Reg.operands [.gpr 3, .gpr 1] [])) #v[83, 1]
    (.letOp (n := 87) (.out 0x101d5f (movR32R32Effect 0x101d5f 3 15 3) (EffectPart.reads (.reg (.gpr 15)) [.gpr 3] []) (.reg (.gpr 15))) #v[85]
    (.letOp (n := 88) (.exec 0x101d5f (fun s => s.RIP = 0x101d5f) (movR32R32Effect 0x101d5f 3 15 3) (Reg.operands [.gpr 3] [])) #v[85]
    (.letOp (n := 89) (.out 0x101d62 (shrR32Effect 0x101d62 4 15 26) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[87]
    (.letOp (n := 90) (.exec 0x101d62 (fun s => s.RIP = 0x101d62) (shrR32Effect 0x101d62 4 15 26) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[87]
    (.letOp (n := 91) (.out 0x101d66 (addR32R32Effect 0x101d66 3 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 2] []) (.reg (.gpr 15))) #v[89, 2]
    (.letOp (n := 92) (.exec 0x101d66 (fun s => s.RIP = 0x101d66) (addR32R32Effect 0x101d66 3 15 2) (Reg.operands [.gpr 15, .gpr 2] [])) #v[89, 2]
    (.terminate (.br ⟨.l101d69, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 85), (4, 4), (5, 73), (6, 6), (7, 59), (8, 8), (9, 69), (10, 71), (11, 79), (15, 91), (22, 22), (39, 39), (50, 50), (51, 51)] 93⟩)))))))))))))))))))))))))))))))))))))))))

def bytes_l101d20 : List UInt8 :=
  [0x45, 0x89, 0xC1, 0x41, 0xC1, 0xE9, 0x1A, 0x44, 0x89, 0xC7, 0x81, 0xE7, 0xFF, 0xFF, 0xFF, 0x03,
    0x47, 0x8D, 0x14, 0x89, 0x44, 0x03, 0x56, 0x24, 0x45, 0x89, 0xD1, 0x41, 0xC1, 0xE9, 0x1A, 0x45,
    0x01, 0xD9, 0x41, 0x81, 0xE2, 0xFF, 0xFF, 0xFF, 0x03, 0x41, 0x8D, 0x6A, 0x05, 0x41, 0x89, 0xEB,
    0x41, 0xC1, 0xEB, 0x1A, 0x45, 0x01, 0xCB, 0x44, 0x89, 0xDB, 0xC1, 0xEB, 0x1A, 0x01, 0xCB, 0x41,
    0x89, 0xDF, 0x41, 0xC1, 0xEF, 0x1A, 0x41, 0x01, 0xD7]

theorem code_l101d20 : ∀ x ∈ codeRange 0x101d20 bytes_l101d20, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1d20 73 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101d69 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101d69 (movR32R32Effect 0x101d69 3 12 15) (EffectPart.reads (.reg (.gpr 12)) [.gpr 15] []) (.reg (.gpr 12))) #v[15]
    (.letOp (n := 54) (.exec 0x101d69 (fun s => s.RIP = 0x101d69) (movR32R32Effect 0x101d69 3 12 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.out 0x101d6c (shrR32Effect 0x101d6c 4 12 26) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[53]
    (.letOp (n := 56) (.exec 0x101d6c (fun s => s.RIP = 0x101d6c) (shrR32Effect 0x101d6c 4 12 26) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 57) (.out 0x101d70 (leaR32Effect 0x101d70 4 14 (.sib 12 (some 7) 0 .none)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 12, .gpr 7] []) (.reg (.gpr 14))) #v[55, 7]
    (.letOp (n := 58) (.exec 0x101d70 (fun s => s.RIP = 0x101d70) (leaR32Effect 0x101d70 4 14 (.sib 12 (some 7) 0 .none)) (Reg.operands [.gpr 12, .gpr 7] [])) #v[55, 7]
    (.letOp (n := 59) (.out 0x101d74 (addR32Imm32Effect 0x101d74 7 14 0xfc000000) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14] []) (.reg (.gpr 14))) #v[57]
    (.letOp (n := 60) (.exec 0x101d74 (fun s => s.RIP = 0x101d74) (addR32Imm32Effect 0x101d74 7 14 0xfc000000) (Reg.operands [.gpr 14] [])) #v[57]
    (.letOp (n := 61) (.out 0x101d7b (addR32R32Effect 0x101d7b 3 12 7) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 7] []) (.reg (.gpr 12))) #v[55, 7]
    (.letOp (n := 62) (.exec 0x101d7b (fun s => s.RIP = 0x101d7b) (addR32R32Effect 0x101d7b 3 12 7) (Reg.operands [.gpr 12, .gpr 7] [])) #v[55, 7]
    (.letOp (n := 63) (.out 0x101d7e (movR32R32Effect 0x101d7e 3 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[59]
    (.letOp (n := 64) (.exec 0x101d7e (fun s => s.RIP = 0x101d7e) (movR32R32Effect 0x101d7e 3 7 14) (Reg.operands [.gpr 14] [])) #v[59]
    (.letOp (n := 65) (.out 0x101d81 (sarR32Effect 0x101d81 3 7 31) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[63]
    (.letOp (n := 66) (.exec 0x101d81 (fun s => s.RIP = 0x101d81) (sarR32Effect 0x101d81 3 7 31) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[63]
    (.letOp (n := 67) (.out 0x101d84 (shrR32Effect 0x101d84 4 14 31) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[59]
    (.letOp (n := 68) (.exec 0x101d84 (fun s => s.RIP = 0x101d84) (shrR32Effect 0x101d84 4 14 31) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[59]
    (.letOp (n := 69) (.out 0x101d88 (decR32Effect 0x101d88 3 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[67]
    (.letOp (n := 70) (.exec 0x101d88 (fun s => s.RIP = 0x101d88) (decR32Effect 0x101d88 3 14) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[67]
    (.letOp (n := 71) (.out 0x101d8b (movR32R32Effect 0x101d8b 3 13 14) (EffectPart.reads (.reg (.gpr 13)) [.gpr 14] []) (.reg (.gpr 13))) #v[69]
    (.letOp (n := 72) (.exec 0x101d8b (fun s => s.RIP = 0x101d8b) (movR32R32Effect 0x101d8b 3 13 14) (Reg.operands [.gpr 14] [])) #v[69]
    (.letOp (n := 73) (.out 0x101d8e (andR32Imm32Effect 0x101d8e 7 13 0x3ffffff) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[71]
    (.letOp (n := 74) (.exec 0x101d8e (fun s => s.RIP = 0x101d8e) (andR32Imm32Effect 0x101d8e 7 13 0x3ffffff) (Reg.operands [.gpr 13] [])) #v[71]
    (.letOp (n := 75) (.out 0x101d95 (andR32R32Effect 0x101d95 3 5 13) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 13] []) (.reg (.gpr 5))) #v[5, 73]
    (.letOp (n := 76) (.exec 0x101d95 (fun s => s.RIP = 0x101d95) (andR32R32Effect 0x101d95 3 5 13) (Reg.operands [.gpr 5, .gpr 13] [])) #v[5, 73]
    (.letOp (n := 77) (.out 0x101d98 (andR32R32Effect 0x101d98 3 11 13) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 13] []) (.reg (.gpr 11))) #v[11, 73]
    (.letOp (n := 78) (.exec 0x101d98 (fun s => s.RIP = 0x101d98) (andR32R32Effect 0x101d98 3 11 13) (Reg.operands [.gpr 11, .gpr 13] [])) #v[11, 73]
    (.letOp (n := 79) (.out 0x101d9b (andR32R32Effect 0x101d9b 3 3 13) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 13] []) (.reg (.gpr 3))) #v[3, 73]
    (.letOp (n := 80) (.exec 0x101d9b (fun s => s.RIP = 0x101d9b) (andR32R32Effect 0x101d9b 3 3 13) (Reg.operands [.gpr 3, .gpr 13] [])) #v[3, 73]
    (.letOp (n := 81) (.out 0x101d9e (andR32R32Effect 0x101d9e 3 13 15) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 15] []) (.reg (.gpr 13))) #v[73, 15]
    (.letOp (n := 82) (.exec 0x101d9e (fun s => s.RIP = 0x101d9e) (andR32R32Effect 0x101d9e 3 13 15) (Reg.operands [.gpr 13, .gpr 15] [])) #v[73, 15]
    (.letOp (n := 83) (.out 0x101da1 (andR32R32Effect 0x101da1 3 14 12) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 12] []) (.reg (.gpr 14))) #v[69, 61]
    (.letOp (n := 84) (.exec 0x101da1 (fun s => s.RIP = 0x101da1) (andR32R32Effect 0x101da1 3 14 12) (Reg.operands [.gpr 14, .gpr 12] [])) #v[69, 61]
    (.letOp (n := 85) (.out 0x101da4 (andR32R32Effect 0x101da4 3 10 7) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 7] []) (.reg (.gpr 10))) #v[10, 65]
    (.letOp (n := 86) (.exec 0x101da4 (fun s => s.RIP = 0x101da4) (andR32R32Effect 0x101da4 3 10 7) (Reg.operands [.gpr 10, .gpr 7] [])) #v[10, 65]
    (.letOp (n := 87) (.out 0x101da7 (orR32R32Effect 0x101da7 3 10 5) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 5] []) (.reg (.gpr 10))) #v[85, 75]
    (.letOp (n := 88) (.exec 0x101da7 (fun s => s.RIP = 0x101da7) (orR32R32Effect 0x101da7 3 10 5) (Reg.operands [.gpr 10, .gpr 5] [])) #v[85, 75]
    (.letOp (n := 89) (.out 0x101daa (andR32R32Effect 0x101daa 3 9 7) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 7] []) (.reg (.gpr 9))) #v[9, 65]
    (.letOp (n := 90) (.exec 0x101daa (fun s => s.RIP = 0x101daa) (andR32R32Effect 0x101daa 3 9 7) (Reg.operands [.gpr 9, .gpr 7] [])) #v[9, 65]
    (.letOp (n := 91) (.out 0x101dad (orR32R32Effect 0x101dad 3 9 11) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 11] []) (.reg (.gpr 9))) #v[89, 77]
    (.letOp (n := 92) (.exec 0x101dad (fun s => s.RIP = 0x101dad) (orR32R32Effect 0x101dad 3 9 11) (Reg.operands [.gpr 9, .gpr 11] [])) #v[89, 77]
    (.terminate (.br ⟨.l101db0, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 79), (4, 4), (5, 75), (6, 6), (7, 65), (8, 8), (9, 91), (10, 87), (11, 77), (12, 61), (13, 81), (14, 83), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 93⟩)))))))))))))))))))))))))))))))))))))))))

def bytes_l101d69 : List UInt8 :=
  [0x45, 0x89, 0xFC, 0x41, 0xC1, 0xEC, 0x1A, 0x45, 0x8D, 0x34, 0x3C, 0x41, 0x81, 0xC6, 0x00, 0x00,
    0x00, 0xFC, 0x41, 0x01, 0xFC, 0x44, 0x89, 0xF7, 0xC1, 0xFF, 0x1F, 0x41, 0xC1, 0xEE, 0x1F, 0x41,
    0xFF, 0xCE, 0x45, 0x89, 0xF5, 0x41, 0x81, 0xE5, 0xFF, 0xFF, 0xFF, 0x03, 0x44, 0x21, 0xED, 0x45,
    0x21, 0xEB, 0x44, 0x21, 0xEB, 0x45, 0x21, 0xFD, 0x45, 0x21, 0xE6, 0x41, 0x21, 0xFA, 0x41, 0x09,
    0xEA, 0x41, 0x21, 0xF9, 0x45, 0x09, 0xD9]

theorem code_l101d69 : ∀ x ∈ codeRange 0x101d69 bytes_l101d69, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1d69 71 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

end ChaCha20Poly1305.Proofs.Decrypt.Lifted
