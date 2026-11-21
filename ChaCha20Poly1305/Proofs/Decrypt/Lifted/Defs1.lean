import ChaCha20Poly1305.Proofs.Decrypt.Movsd
import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Labels
import ChaCha20Poly1305.Proofs.Common.CFG.EvalAttr
import ChaCha20Poly1305.Proofs.Common.Lift.Generated.Footprints

namespace ChaCha20Poly1305.Proofs.Decrypt.Lifted

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift

@[cfg_block] def b_l1001f0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1001f0 (pushR64Effect 0x1001f0 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x1001f0 (PushPre 0x1001f0 1) (pushR64Effect 0x1001f0 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x1001f1 (pushR64Effect 0x1001f1 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x1001f1 (PushPre 0x1001f1 2) (pushR64Effect 0x1001f1 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x1001f3 (pushR64Effect 0x1001f3 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x1001f3 (PushPre 0x1001f3 2) (pushR64Effect 0x1001f3 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x1001f5 (pushR64Effect 0x1001f5 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x1001f5 (PushPre 0x1001f5 2) (pushR64Effect 0x1001f5 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x1001f7 (pushR64Effect 0x1001f7 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x1001f7 (PushPre 0x1001f7 2) (pushR64Effect 0x1001f7 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x1001f9 (pushR64Effect 0x1001f9 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x1001f9 (PushPre 0x1001f9 1) (pushR64Effect 0x1001f9 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x1001fa (subR64Imm32Effect 0x1001fa 4 0x188) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x1001fa (fun s => s.RIP = 0x1001fa) (subR64Imm32Effect 0x1001fa 4 0x188) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x100201 (movR64R64Effect 0x100201 14 9) (EffectPart.reads (.reg (.gpr 14)) [.gpr 9] []) (.reg (.gpr 14))) #v[9]
    (.letOp (n := 68) (.exec 0x100201 (fun s => s.RIP = 0x100201) (movR64R64Effect 0x100201 14 9) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 69) (.out 0x100204 (movR64R64Effect 0x100204 3 8) (EffectPart.reads (.reg (.gpr 3)) [.gpr 8] []) (.reg (.gpr 3))) #v[8]
    (.letOp (n := 70) (.exec 0x100204 (fun s => s.RIP = 0x100204) (movR64R64Effect 0x100204 3 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 71) (.out 0x100207 (movR64R64Effect 0x100207 5 1) (EffectPart.reads (.reg (.gpr 5)) [.gpr 1] []) (.reg (.gpr 5))) #v[1]
    (.letOp (n := 72) (.exec 0x100207 (fun s => s.RIP = 0x100207) (movR64R64Effect 0x100207 5 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 73) (.out 0x10020a (movR64R64Effect 0x10020a 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[2]
    (.letOp (n := 74) (.exec 0x10020a (fun s => s.RIP = 0x10020a) (movR64R64Effect 0x10020a 13 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 75) (.out 0x10020d (movR64Imm64Effect 0x10020d 0 0x6b20657479622d32) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 76) (.exec 0x10020d (fun s => s.RIP = 0x10020d) (movR64Imm64Effect 0x10020d 0 0x6b20657479622d32) (Reg.operands [] [])) #v[]
    (.letOp (n := 77) (.exec 0x100217 (StorePre 0x100217 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x100217 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100217 0 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[75, 65]
    (.letOp (n := 78) (.out 0x10021f (movR64Imm64Effect 0x10021f 0 0x3320646e61707865) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 79) (.exec 0x10021f (fun s => s.RIP = 0x10021f) (movR64Imm64Effect 0x10021f 0 0x3320646e61707865) (Reg.operands [] [])) #v[]
    (.letOp (n := 80) (.exec 0x100229 (StorePre 0x100229 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x100229 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100229 0 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[78, 65]
    (.letOp (n := 81) (.out 0x100231 (movR64M64Effect 0x100231 0 (.base 7 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 82) (.exec 0x100231 (LoadPre 0x100231 (fun s => AddrMode.addr (.base 7 .none) s (0x100231 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x100231 0 (.base 7 .none)) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 83) (.out 0x100234 (movR64M64Effect 0x100234 1 (.base 7 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 7] []) (.reg (.gpr 1))) #v[7]
    (.letOp (n := 84) (.exec 0x100234 (LoadPre 0x100234 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x100234 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x100234 1 (.base 7 (.d8 0x8))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 85) (.exec 0x100238 (StorePre 0x100238 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x100238 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100238 0 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[81, 65]
    (.letOp (n := 86) (.exec 0x100240 (StorePre 0x100240 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x100240 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100240 1 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[83, 65]
    (.letOp (n := 87) (.out 0x100248 (movR64M64Effect 0x100248 0 (.base 7 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 88) (.exec 0x100248 (LoadPre 0x100248 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x100248 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x100248 0 (.base 7 (.d8 0x10))) (Reg.operands [.gpr 7] [])) #v[7]
    (.terminate (.br ⟨.l10024c, RegMap.args [(0, 87), (1, 83), (2, 2), (3, 69), (4, 65), (5, 71), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 73), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 89⟩)))))))))))))))))))))))))))))))))))))

def bytes_l1001f0 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0x88, 0x01, 0x00,
    0x00, 0x4D, 0x89, 0xCE, 0x4C, 0x89, 0xC3, 0x48, 0x89, 0xCD, 0x49, 0x89, 0xD5, 0x48, 0xB8, 0x32,
    0x2D, 0x62, 0x79, 0x74, 0x65, 0x20, 0x6B, 0x48, 0x89, 0x84, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x48,
    0xB8, 0x65, 0x78, 0x70, 0x61, 0x6E, 0x64, 0x20, 0x33, 0x48, 0x89, 0x84, 0x24, 0xD0, 0x00, 0x00,
    0x00, 0x48, 0x8B, 0x07, 0x48, 0x8B, 0x4F, 0x08, 0x48, 0x89, 0x84, 0x24, 0xE0, 0x00, 0x00, 0x00,
    0x48, 0x89, 0x8C, 0x24, 0xE8, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x47, 0x10]

theorem code_l1001f0 : ∀ x ∈ codeRange 0x1001f0 bytes_l1001f0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1f0 92 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10024c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x10024c (StorePre 0x10024c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x10024c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10024c 0 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[0, 4]
    (.letOp (n := 54) (.out 0x100254 (movR64M64Effect 0x100254 0 (.base 7 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 55) (.exec 0x100254 (LoadPre 0x100254 (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x100254 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x100254 0 (.base 7 (.d8 0x18))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 56) (.exec 0x100258 (StorePre 0x100258 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x100258 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100258 0 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[54, 4]
    (.letOp (n := 57) (.out 0x100260 (movR64M64Effect 0x100260 0 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 58) (.exec 0x100260 (LoadPre 0x100260 (fun s => AddrMode.addr (.base 6 .none) s (0x100260 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x100260 0 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 59) (.exec 0x100263 (StorePre 0x100263 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x54)) s (0x100263 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100263 0 (.sib 4 none 0 (.d8 0x54))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 60) (.out 0x100268 (movR32M32LowEffect 0x100268 0 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 61) (.exec 0x100268 (LoadPre 0x100268 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x100268 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x100268 0 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 62) (.exec 0x10026b (StorePre 0x10026b 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5c)) s (0x10026b + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x10026b 0 (.sib 4 none 0 (.d8 0x5c))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[60, 4]
    (.letOp (n := 63) (.exec 0x10026f (StorePre 0x10026f 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x61)) s (0x10026f + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10026f (.sib 4 none 0 (.d8 0x61)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x100278 (StorePre 0x100278 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x69)) s (0x100278 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x100278 (.sib 4 none 0 (.d8 0x69)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.exec 0x100281 (StorePre 0x100281 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x71)) s (0x100281 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x100281 (.sib 4 none 0 (.d8 0x71)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x10028a (StorePre 0x10028a 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x79)) s (0x10028a + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10028a (.sib 4 none 0 (.d8 0x79)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x100293 (StorePre 0x100293 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x81)) s (0x100293 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x100293 (.sib 4 none 0 (.d32 0x81)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.exec 0x10029f (StorePre 0x10029f 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x89)) s (0x10029f + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x10029f (.sib 4 none 0 (.d32 0x89)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.exec 0x1002ab (StorePre 0x1002ab 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x91)) s (0x1002ab + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1002ab (.sib 4 none 0 (.d32 0x91)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.exec 0x1002b7 (StorePre 0x1002b7 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x1002b7 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1002b7 (.sib 4 none 0 (.d32 0x98)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.out 0x1002c3 (movR64M64Effect 0x1002c3 0 (.sib 4 none 0 (.d32 0xf8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 72) (.exec 0x1002c3 (LoadPre 0x1002c3 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x1002c3 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1002c3 0 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.exec 0x1002cb (StorePre 0x1002cb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1002cb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1002cb 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[71, 4]
    (.letOp (n := 74) (.out 0x1002d0 (movR64M64Effect 0x1002d0 0 (.sib 4 none 0 (.d32 0xf0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 75) (.exec 0x1002d0 (LoadPre 0x1002d0 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x1002d0 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1002d0 0 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 76) (.exec 0x1002d8 (StorePre 0x1002d8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1002d8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1002d8 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[74, 4]
    (.letOp (n := 77) (.out 0x1002dd (movR64M64Effect 0x1002dd 0 (.sib 4 none 0 (.d32 0xe8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 78) (.exec 0x1002dd (LoadPre 0x1002dd (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x1002dd + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1002dd 0 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.br ⟨.l1002e5, RegMap.args [(0, 77), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 79⟩)))))))))))))))))))))))))))

def bytes_l10024c : List UInt8 :=
  [0x48, 0x89, 0x84, 0x24, 0xF0, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x47, 0x18, 0x48, 0x89, 0x84, 0x24,
    0xF8, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x06, 0x48, 0x89, 0x44, 0x24, 0x54, 0x8B, 0x46, 0x08, 0x89,
    0x44, 0x24, 0x5C, 0x48, 0xC7, 0x44, 0x24, 0x61, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24,
    0x69, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x71, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7,
    0x44, 0x24, 0x79, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0x81, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0x89, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48,
    0xC7, 0x84, 0x24, 0x91, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0x98,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x84, 0x24, 0xF8, 0x00, 0x00, 0x00, 0x48,
    0x89, 0x44, 0x24, 0x48, 0x48, 0x8B, 0x84, 0x24, 0xF0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24,
    0x40, 0x48, 0x8B, 0x84, 0x24, 0xE8, 0x00, 0x00, 0x00]

theorem code_l10024c : ∀ x ∈ codeRange 0x10024c bytes_l10024c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24c 153 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1002e5 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1002e5 (StorePre 0x1002e5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1002e5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1002e5 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[0, 4]
    (.letOp (n := 54) (.out 0x1002ea (movR64M64Effect 0x1002ea 0 (.sib 4 none 0 (.d32 0xe0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 55) (.exec 0x1002ea (LoadPre 0x1002ea (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x1002ea + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1002ea 0 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.exec 0x1002f2 (StorePre 0x1002f2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1002f2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1002f2 0 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[54, 4]
    (.letOp (n := 57) (.out 0x1002f7 (movR64M64Effect 0x1002f7 0 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 58) (.exec 0x1002f7 (LoadPre 0x1002f7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x1002f7 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1002f7 0 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x1002ff (movR64M64Effect 0x1002ff 1 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 60) (.exec 0x1002ff (LoadPre 0x1002ff (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x1002ff + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1002ff 1 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x100307 (StorePre 0x100307 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x100307 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100307 1 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.exec 0x10030c (StorePre 0x10030c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10030c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10030c 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 63) (.exec 0x100311 (StorePre 0x100311 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x100311 + BitVec.ofNat 64 8)) 4) (movM32Imm32Effect 0x100311 8 (.sib 4 none 0 (.d8 0x50)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x100319 (StorePre 0x100319 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x100319 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x100319 (.sib 4 none 0 (.d8 0x60)) 0x40) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.exec 0x10031e (StorePre 0x10031e 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x10031e + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x10031e (.sib 4 none 0 (.d32 0xb8)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x10032a (StorePre 0x10032a 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x10032a + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x10032a (.sib 4 none 0 (.d32 0xb0)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x100336 (StorePre 0x100336 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x100336 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x100336 (.sib 4 none 0 (.d32 0xa8)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.exec 0x100342 (StorePre 0x100342 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x100342 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x100342 (.sib 4 none 0 (.d32 0xa0)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.out 0x10034e (leaR64Effect 0x10034e 0 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 70) (.exec 0x10034e (fun s => s.RIP = 0x10034e) (leaR64Effect 0x10034e 0 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.exec 0x100356 (StorePre 0x100356 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x100356 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100356 0 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[69, 4]
    (.letOp (n := 72) (.exec 0x10035e (StorePre 0x10035e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x10035e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10035e 0 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[69, 4]
    (.letOp (n := 73) (.exec 0x100366 (StorePre 0x100366 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x100366 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x100366 (.sib 4 none 0 (.d32 0xe0)) 0x20) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.out 0x100372 (leaR64Effect 0x100372 7 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 75) (.exec 0x100372 (fun s => s.RIP = 0x100372) (leaR64Effect 0x100372 7 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 76) (.out 0x100377 (leaR64Effect 0x100377 6 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 77) (.exec 0x100377 (fun s => s.RIP = 0x100377) (leaR64Effect 0x100377 6 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 78) (.out 0x10037f (callEffect (fun _ => 0x100a80) 0x100384) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 79) (.exec 0x10037f (PushPre 0x10037f 5) (callEffect (fun _ => 0x100a80) 0x100384) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 80) (.const ⟨64, 0x100384⟩) #v[]
    (.terminate (.call ⟨.l100a80, RegMap.args [(0, 69), (1, 59), (2, 2), (3, 3), (4, 78), (5, 5), (6, 76), (7, 74), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 81⟩ { target := .l100384, kept := #v[], arity := rfl, guard := some (Fin.last 80) })))))))))))))))))))))))))))))

def bytes_l1002e5 : List UInt8 :=
  [0x48, 0x89, 0x44, 0x24, 0x38, 0x48, 0x8B, 0x84, 0x24, 0xE0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44,
    0x24, 0x30, 0x48, 0x8B, 0x84, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x8C, 0x24, 0xD8, 0x00,
    0x00, 0x00, 0x48, 0x89, 0x4C, 0x24, 0x28, 0x48, 0x89, 0x44, 0x24, 0x20, 0xC7, 0x44, 0x24, 0x50,
    0x00, 0x00, 0x00, 0x00, 0xC6, 0x44, 0x24, 0x60, 0x40, 0x48, 0xC7, 0x84, 0x24, 0xB8, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x48, 0xC7, 0x84, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84,
    0x24, 0xA0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x84, 0x24, 0xA0, 0x00, 0x00,
    0x00, 0x48, 0x89, 0x84, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0xD8, 0x00, 0x00,
    0x00, 0x48, 0xC7, 0x84, 0x24, 0xE0, 0x00, 0x00, 0x00, 0x20, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x7C,
    0x24, 0x20, 0x48, 0x8D, 0xB4, 0x24, 0xD0, 0x00, 0x00, 0x00, 0xE8, 0xFC, 0x06, 0x00, 0x00]

theorem code_l1002e5 : ∀ x ∈ codeRange 0x1002e5 bytes_l1002e5, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2e5 159 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100384 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100384 (testR8R8Effect 0x100384 2 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[0, 0]
    (.letOp (n := 54) (.exec 0x100384 (fun s => s.RIP = 0x100384) (testR8R8Effect 0x100384 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l1005fc, RegMap.args [(0, 0), (3, 3), (4, 4), (5, 5), (13, 13), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l10038c, RegMap.args [(0, 0), (3, 3), (4, 4), (5, 5), (13, 13), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l100384 : List UInt8 :=
  [0x84, 0xC0, 0x0F, 0x85, 0x70, 0x02, 0x00, 0x00]

theorem code_l100384 : ∀ x ∈ codeRange 0x100384 bytes_l100384, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x384 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10038c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10038c (movR64Imm64Effect 0x10038c 15 0x3fffffffbf) (EffectPart.reads (.reg (.gpr 15)) [] []) (.reg (.gpr 15))) #v[]
    (.letOp (n := 54) (.exec 0x10038c (fun s => s.RIP = 0x10038c) (movR64Imm64Effect 0x10038c 15 0x3fffffffbf) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x100396 (leaR64Effect 0x100396 12 (.sib 4 none 0 (.d32 0x150))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 56) (.exec 0x100396 (fun s => s.RIP = 0x100396) (leaR64Effect 0x100396 12 (.sib 4 none 0 (.d32 0x150))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x10039e (leaR64Effect 0x10039e 6 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 58) (.exec 0x10039e (fun s => s.RIP = 0x10039e) (leaR64Effect 0x10039e 6 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x1003a6 (movR64R64Effect 0x1003a6 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[55]
    (.letOp (n := 60) (.exec 0x1003a6 (fun s => s.RIP = 0x1003a6) (movR64R64Effect 0x1003a6 7 12) (Reg.operands [.gpr 12] [])) #v[55]
    (.letOp (n := 61) (.out 0x1003a9 (callEffect (fun _ => 0x101e40) 0x1003ae) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 62) (.exec 0x1003a9 (PushPre 0x1003a9 5) (callEffect (fun _ => 0x101e40) 0x1003ae) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.const ⟨64, 0x1003ae⟩) #v[]
    (.terminate (.call ⟨.l101e40, RegMap.args [(3, 3), (4, 61), (5, 5), (6, 57), (7, 59), (12, 55), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ { target := .l1003ae, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l10038c : List UInt8 :=
  [0x49, 0xBF, 0xBF, 0xFF, 0xFF, 0xFF, 0x3F, 0x00, 0x00, 0x00, 0x4C, 0x8D, 0xA4, 0x24, 0x50, 0x01,
    0x00, 0x00, 0x48, 0x8D, 0xB4, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xE7, 0xE8, 0x92, 0x1A,
    0x00, 0x00]

theorem code_l10038c : ∀ x ∈ codeRange 0x10038c bytes_l10038c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x38c 34 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1003ae : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1003ae (StorePre 0x1003ae 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1003ae + BitVec.ofNat 64 8)) 4) (movM32Imm32Effect 0x1003ae 8 (.sib 4 none 0 (.d8 0x50)) 0x1) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.exec 0x1003b6 (StorePre 0x1003b6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1003b6 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x1003b6 (.sib 4 none 0 (.d8 0x60)) 0x40) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1003bb (leaR64Effect 0x1003bb 7 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 56) (.exec 0x1003bb (fun s => s.RIP = 0x1003bb) (leaR64Effect 0x1003bb 7 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1003c3 (leaR64Effect 0x1003c3 6 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 58) (.exec 0x1003c3 (fun s => s.RIP = 0x1003c3) (leaR64Effect 0x1003c3 6 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x1003c8 (movR32Imm32Effect 0x1003c8 5 1 0x20) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 60) (.exec 0x1003c8 (fun s => s.RIP = 0x1003c8) (movR32Imm32Effect 0x1003c8 5 1 0x20) (Reg.operands [] [])) #v[]
    (.letOp (n := 61) (.out 0x1003cd (repMovsdEffect 0x1003cd) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 6))) #v[57, 55, 59, 22]
    (.letOp (n := 62) (.out 0x1003cd (repMovsdEffect 0x1003cd) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 7))) #v[57, 55, 59, 22]
    (.letOp (n := 63) (.exec 0x1003cd (RepPre 0x1003cd (RepMovsdPre 0x1003cd)) (repMovsdEffect 0x1003cd) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[57, 55, 59, 22]
    (.letOp (n := 64) (.out 0x1003cf (movR64M64Effect 0x1003cf 1 (.base 3 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 3] []) (.reg (.gpr 1))) #v[3]
    (.letOp (n := 65) (.exec 0x1003cf (LoadPre 0x1003cf (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x1003cf + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1003cf 1 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 66) (.out 0x1003d3 (movR8Imm8Effect 0x1003d3 2 0 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 67) (.exec 0x1003d3 (fun s => s.RIP = 0x1003d3) (movR8Imm8Effect 0x1003d3 2 0 0x1) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 68) (.exec 0x1003d5 (StorePre 0x1003d5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1003d5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1003d5 1 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 69) (.out 0x1003da (cmpR64R64Effect 0x1003da 1 15) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 15] []) (.flag .CF)) #v[64, 15]
    (.letOp (n := 70) (.out 0x1003da (cmpR64R64Effect 0x1003da 1 15) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 15] []) (.flag .ZF)) #v[64, 15]
    (.letOp (n := 71) (.exec 0x1003da (fun s => s.RIP = 0x1003da) (cmpR64R64Effect 0x1003da 1 15) (Reg.operands [.gpr 1, .gpr 15] [])) #v[64, 15]
    (.letOp (n := 72) (.pure (condOp 7)) #v[69, 70]
    (.terminate (.condBr (Fin.last 72) ⟨.l1005ea, RegMap.args [(0, 66), (1, 64), (2, 2), (3, 3), (4, 4), (5, 5), (6, 61), (7, 62), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (16, 69), (19, 70), (22, 22), (39, 39), (50, 50), (51, 51)] 73⟩ ⟨.l1003e3, RegMap.args [(0, 66), (1, 64), (2, 2), (3, 3), (4, 4), (5, 5), (6, 61), (7, 62), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (16, 69), (19, 70), (22, 22), (39, 39), (50, 50), (51, 51)] 73⟩)))))))))))))))))))))

def bytes_l1003ae : List UInt8 :=
  [0xC7, 0x44, 0x24, 0x50, 0x01, 0x00, 0x00, 0x00, 0xC6, 0x44, 0x24, 0x60, 0x40, 0x48, 0x8D, 0xBC,
    0x24, 0xD0, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x74, 0x24, 0x20, 0xB9, 0x20, 0x00, 0x00, 0x00, 0xF3,
    0xA5, 0x48, 0x8B, 0x4B, 0x10, 0xB0, 0x01, 0x48, 0x89, 0x4C, 0x24, 0x18, 0x4C, 0x39, 0xF9, 0x0F,
    0x87, 0x07, 0x02, 0x00, 0x00]

theorem code_l1003ae : ∀ x ∈ codeRange 0x1003ae bytes_l1003ae, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3ae 53 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1003e3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1003e3 (StorePre 0x1003e3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1003e3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1003e3 13 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[13, 4]
    (.letOp (n := 54) (.exec 0x1003e8 (StorePre 0x1003e8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x1003e8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1003e8 14 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[14, 4]
    (.letOp (n := 55) (.exec 0x1003f0 (StorePre 0x1003f0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1003f0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1003f0 3 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[3, 4]
    (.letOp (n := 56) (.out 0x1003f5 (movR64Imm64Effect 0x1003f5 13 0x7ffffffffffffff0) (EffectPart.reads (.reg (.gpr 13)) [] []) (.reg (.gpr 13))) #v[]
    (.letOp (n := 57) (.exec 0x1003f5 (fun s => s.RIP = 0x1003f5) (movR64Imm64Effect 0x1003f5 13 0x7ffffffffffffff0) (Reg.operands [] [])) #v[]
    (.letOp (n := 58) (.out 0x1003ff (andR64R64Effect 0x1003ff 13 5) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 5] []) (.reg (.gpr 13))) #v[56, 5]
    (.letOp (n := 59) (.exec 0x1003ff (fun s => s.RIP = 0x1003ff) (andR64R64Effect 0x1003ff 13 5) (Reg.operands [.gpr 13, .gpr 5] [])) #v[56, 5]
    (.letOp (n := 60) (.out 0x100402 (movR32R32Effect 0x100402 3 14 5) (EffectPart.reads (.reg (.gpr 14)) [.gpr 5] []) (.reg (.gpr 14))) #v[5]
    (.letOp (n := 61) (.exec 0x100402 (fun s => s.RIP = 0x100402) (movR32R32Effect 0x100402 3 14 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 62) (.out 0x100405 (andR32Imm8Effect 0x100405 4 14 0xf) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14] []) (.reg (.gpr 14))) #v[60]
    (.letOp (n := 63) (.exec 0x100405 (fun s => s.RIP = 0x100405) (andR32Imm8Effect 0x100405 4 14 0xf) (Reg.operands [.gpr 14] [])) #v[60]
    (.letOp (n := 64) (.exec 0x100409 (StorePre 0x100409 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x100409 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100409 5 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[5, 4]
    (.letOp (n := 65) (.out 0x100411 (cmpR64Imm8Effect 0x100411 5 0x10) (EffectPart.reads (.flag .CF) [.gpr 5] []) (.flag .CF)) #v[5]
    (.letOp (n := 66) (.exec 0x100411 (fun s => s.RIP = 0x100411) (cmpR64Imm8Effect 0x100411 5 0x10) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 67) (.pure (condOp 2)) #v[65]
    (.terminate (.condBr (Fin.last 67) ⟨.l100435, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (12, 12), (13, 58), (14, 62), (15, 15), (16, 65), (22, 22), (39, 39), (50, 50), (51, 51)] 68⟩ ⟨.l100417, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (12, 12), (13, 58), (14, 62), (15, 15), (16, 65), (22, 22), (39, 39), (50, 50), (51, 51)] 68⟩))))))))))))))))

def bytes_l1003e3 : List UInt8 :=
  [0x4C, 0x89, 0x6C, 0x24, 0x08, 0x4C, 0x89, 0xB4, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x5C,
    0x24, 0x10, 0x49, 0xBD, 0xF0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F, 0x49, 0x21, 0xED, 0x41,
    0x89, 0xEE, 0x41, 0x83, 0xE6, 0x0F, 0x48, 0x89, 0xAC, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x48, 0x83,
    0xFD, 0x10, 0x72, 0x1E]

theorem code_l1003e3 : ∀ x ∈ codeRange 0x1003e3 bytes_l1003e3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3e3 52 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100417 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100417 (movR64R64Effect 0x100417 3 13) (EffectPart.reads (.reg (.gpr 3)) [.gpr 13] []) (.reg (.gpr 3))) #v[13]
    (.letOp (n := 54) (.exec 0x100417 (fun s => s.RIP = 0x100417) (movR64R64Effect 0x100417 3 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 55) (.out 0x10041a (movR64M64Effect 0x10041a 6 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 56) (.exec 0x10041a (LoadPre 0x10041a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10041a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10041a 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x10041f (fun s => s.RIP = 0x10041f) (fun _ => nopEffect 0x10041f 1) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l100420, RegMap.args [(2, 2), (3, 53), (4, 4), (6, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l100417 : List UInt8 :=
  [0x4C, 0x89, 0xEB, 0x48, 0x8B, 0x74, 0x24, 0x08, 0x90]

theorem code_l100417 : ∀ x ∈ codeRange 0x100417 bytes_l100417, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x417 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100420 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100420 (leaR64Effect 0x100420 5 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 6] []) (.reg (.gpr 5))) #v[6]
    (.letOp (n := 54) (.exec 0x100420 (fun s => s.RIP = 0x100420) (leaR64Effect 0x100420 5 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 55) (.out 0x100424 (movR64R64Effect 0x100424 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[12]
    (.letOp (n := 56) (.exec 0x100424 (fun s => s.RIP = 0x100424) (movR64R64Effect 0x100424 7 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 57) (.out 0x100427 (callEffect (fun _ => 0x101e30) 0x10042c) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x100427 (PushPre 0x100427 5) (callEffect (fun _ => 0x101e30) 0x10042c) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x10042c⟩) #v[]
    (.terminate (.call ⟨.l101e30, RegMap.args [(2, 2), (3, 3), (4, 57), (5, 53), (6, 6), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ { target := .l10042c, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l100420 : List UInt8 :=
  [0x48, 0x8D, 0x6E, 0x10, 0x4C, 0x89, 0xE7, 0xE8, 0x04, 0x1A, 0x00, 0x00]

theorem code_l100420 : ∀ x ∈ codeRange 0x100420 bytes_l100420, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x420 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10042c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10042c (movR64R64Effect 0x10042c 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[5]
    (.letOp (n := 54) (.exec 0x10042c (fun s => s.RIP = 0x10042c) (movR64R64Effect 0x10042c 6 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 55) (.out 0x10042f (addR64Imm8Effect 0x10042f 3 0xf0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[3]
    (.letOp (n := 56) (.out 0x10042f (addR64Imm8Effect 0x10042f 3 0xf0) (EffectPart.reads (.flag .ZF) [.gpr 3] []) (.flag .ZF)) #v[3]
    (.letOp (n := 57) (.exec 0x10042f (fun s => s.RIP = 0x10042f) (addR64Imm8Effect 0x10042f 3 0xf0) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 58) (.pure (condOp 5)) #v[56]
    (.terminate (.condBr (Fin.last 58) ⟨.l100420, RegMap.args [(2, 2), (3, 55), (4, 4), (5, 5), (6, 53), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩ ⟨.l100435, RegMap.args [(2, 2), (3, 55), (4, 4), (5, 5), (6, 53), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l10042c : List UInt8 :=
  [0x48, 0x89, 0xEE, 0x48, 0x83, 0xC3, 0xF0, 0x75, 0xEB]

theorem code_l10042c : ∀ x ∈ codeRange 0x10042c bytes_l10042c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x42c 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100435 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100435 (testR64R64Effect 0x100435 14 14) (EffectPart.reads (.flag .ZF) [.gpr 14, .gpr 14] []) (.flag .ZF)) #v[14, 14]
    (.letOp (n := 54) (.exec 0x100435 (fun s => s.RIP = 0x100435) (testR64R64Effect 0x100435 14 14) (Reg.operands [.gpr 14, .gpr 14] [])) #v[14, 14]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l100479, RegMap.args [(2, 2), (3, 3), (4, 4), (6, 6), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l10043a, RegMap.args [(2, 2), (3, 3), (4, 4), (6, 6), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l100435 : List UInt8 :=
  [0x4D, 0x85, 0xF6, 0x74, 0x3F]

theorem code_l100435 : ∀ x ∈ codeRange 0x100435 bytes_l100435, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x435 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10043a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10043a (movR64M64Effect 0x10043a 5 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 54) (.exec 0x10043a (LoadPre 0x10043a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10043a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10043a 5 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10043f (addR64R64Effect 0x10043f 5 13) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 13] []) (.reg (.gpr 5))) #v[53, 13]
    (.letOp (n := 56) (.exec 0x10043f (fun s => s.RIP = 0x10043f) (addR64R64Effect 0x10043f 5 13) (Reg.operands [.gpr 5, .gpr 13] [])) #v[53, 13]
    (.letOp (n := 57) (.out 0x100442 (movR32Imm32Effect 0x100442 5 2 0x10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x100442 (fun s => s.RIP = 0x100442) (movR32Imm32Effect 0x100442 5 2 0x10) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x100447 (subR64R64Effect 0x100447 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 14] []) (.reg (.gpr 2))) #v[57, 14]
    (.letOp (n := 60) (.exec 0x100447 (fun s => s.RIP = 0x100447) (subR64R64Effect 0x100447 2 14) (Reg.operands [.gpr 2, .gpr 14] [])) #v[57, 14]
    (.letOp (n := 61) (.out 0x10044a (leaR64Effect 0x10044a 7 (.sib 4 (some 14) 0 .none)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4, .gpr 14] []) (.reg (.gpr 7))) #v[4, 14]
    (.letOp (n := 62) (.exec 0x10044a (fun s => s.RIP = 0x10044a) (leaR64Effect 0x10044a 7 (.sib 4 (some 14) 0 .none)) (Reg.operands [.gpr 4, .gpr 14] [])) #v[4, 14]
    (.letOp (n := 63) (.out 0x10044e (addR64Imm8Effect 0x10044e 7 0x20) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[61]
    (.letOp (n := 64) (.exec 0x10044e (fun s => s.RIP = 0x10044e) (addR64Imm8Effect 0x10044e 7 0x20) (Reg.operands [.gpr 7] [])) #v[61]
    (.letOp (n := 65) (.out 0x100452 (xorR32R32Effect 0x100452 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[6, 6]
    (.letOp (n := 66) (.exec 0x100452 (fun s => s.RIP = 0x100452) (xorR32R32Effect 0x100452 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 67) (.out 0x100454 (callEffect (callMemPtr 0x100454 (.rip 0x100f86)) (0x100454 + BitVec.ofNat 64 (callMemLen (.rip 0x100f86)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 68) (.exec 0x100454 (GoesTo (CallMemPre 0x100454 (.rip 0x100f86)) (callEffect (callMemPtr 0x100454 (.rip 0x100f86)) (0x100454 + BitVec.ofNat 64 (callMemLen (.rip 0x100f86)))) 0x102d70) (callEffect (callMemPtr 0x100454 (.rip 0x100f86)) (0x100454 + BitVec.ofNat 64 (callMemLen (.rip 0x100f86)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.const ⟨64, 0x10045a⟩) #v[]
    (.terminate (.call ⟨.l102d70, RegMap.args [(2, 59), (3, 3), (4, 67), (5, 55), (6, 65), (7, 63), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 70⟩ { target := .l10045a, kept := #v[], arity := rfl, guard := some (Fin.last 69) }))))))))))))))))))

def bytes_l10043a : List UInt8 :=
  [0x48, 0x8B, 0x6C, 0x24, 0x08, 0x4C, 0x01, 0xED, 0xBA, 0x10, 0x00, 0x00, 0x00, 0x4C, 0x29, 0xF2,
    0x4A, 0x8D, 0x3C, 0x34, 0x48, 0x83, 0xC7, 0x20, 0x31, 0xF6, 0xFF, 0x15, 0x86, 0x0F, 0x10, 0x00]

theorem code_l10043a : ∀ x ∈ codeRange 0x10043a bytes_l10043a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x43a 32 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10045a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10045a (leaR64Effect 0x10045a 3 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 54) (.exec 0x10045a (fun s => s.RIP = 0x10045a) (leaR64Effect 0x10045a 3 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10045f (movR64R64Effect 0x10045f 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 56) (.exec 0x10045f (fun s => s.RIP = 0x10045f) (movR64R64Effect 0x10045f 7 3) (Reg.operands [.gpr 3] [])) #v[53]
    (.letOp (n := 57) (.out 0x100462 (movR64R64Effect 0x100462 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[5]
    (.letOp (n := 58) (.exec 0x100462 (fun s => s.RIP = 0x100462) (movR64R64Effect 0x100462 6 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 59) (.out 0x100465 (movR64R64Effect 0x100465 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14] []) (.reg (.gpr 2))) #v[14]
    (.letOp (n := 60) (.exec 0x100465 (fun s => s.RIP = 0x100465) (movR64R64Effect 0x100465 2 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 61) (.out 0x100468 (callEffect (callMemPtr 0x100468 (.rip 0x100f3a)) (0x100468 + BitVec.ofNat 64 (callMemLen (.rip 0x100f3a)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 62) (.exec 0x100468 (GoesTo (CallMemPre 0x100468 (.rip 0x100f3a)) (callEffect (callMemPtr 0x100468 (.rip 0x100f3a)) (0x100468 + BitVec.ofNat 64 (callMemLen (.rip 0x100f3a)))) 0x102dc0) (callEffect (callMemPtr 0x100468 (.rip 0x100f3a)) (0x100468 + BitVec.ofNat 64 (callMemLen (.rip 0x100f3a)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.const ⟨64, 0x10046e⟩) #v[]
    (.terminate (.call ⟨.l102dc0, RegMap.args [(2, 59), (3, 53), (4, 61), (5, 5), (6, 57), (7, 55), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ { target := .l10046e, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l10045a : List UInt8 :=
  [0x48, 0x8D, 0x5C, 0x24, 0x20, 0x48, 0x89, 0xDF, 0x48, 0x89, 0xEE, 0x4C, 0x89, 0xF2, 0xFF, 0x15,
    0x3A, 0x0F, 0x10, 0x00]

theorem code_l10045a : ∀ x ∈ codeRange 0x10045a bytes_l10045a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x45a 20 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10046e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10046e (movR64R64Effect 0x10046e 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[12]
    (.letOp (n := 54) (.exec 0x10046e (fun s => s.RIP = 0x10046e) (movR64R64Effect 0x10046e 7 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 55) (.out 0x100471 (movR64R64Effect 0x100471 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[3]
    (.letOp (n := 56) (.exec 0x100471 (fun s => s.RIP = 0x100471) (movR64R64Effect 0x100471 6 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 57) (.out 0x100474 (callEffect (fun _ => 0x101e30) 0x100479) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x100474 (PushPre 0x100474 5) (callEffect (fun _ => 0x101e30) 0x100479) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x100479⟩) #v[]
    (.terminate (.call ⟨.l101e30, RegMap.args [(2, 2), (3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ { target := .l100479, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l10046e : List UInt8 :=
  [0x4C, 0x89, 0xE7, 0x48, 0x89, 0xDE, 0xE8, 0xB7, 0x19, 0x00, 0x00]

theorem code_l10046e : ∀ x ∈ codeRange 0x10046e bytes_l10046e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x46e 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100479 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100479 (movR64M64Effect 0x100479 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x100479 (LoadPre 0x100479 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x100479 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100479 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10047e (movR64M64Effect 0x10047e 13 (.base 0 .none)) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[53]
    (.letOp (n := 56) (.exec 0x10047e (LoadPre 0x10047e (fun s => AddrMode.addr (.base 0 .none) s (0x10047e + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x10047e 13 (.base 0 .none)) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x100481 (addR64Imm8Effect 0x100481 15 0x31) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15] []) (.reg (.gpr 15))) #v[15]
    (.letOp (n := 58) (.exec 0x100481 (fun s => s.RIP = 0x100481) (addR64Imm8Effect 0x100481 15 0x31) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 59) (.out 0x100485 (movR64M64Effect 0x100485 0 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x100485 (LoadPre 0x100485 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x100485 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100485 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x10048a (andR64R64Effect 0x10048a 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 0] []) (.reg (.gpr 15))) #v[57, 59]
    (.letOp (n := 62) (.exec 0x10048a (fun s => s.RIP = 0x10048a) (andR64R64Effect 0x10048a 15 0) (Reg.operands [.gpr 15, .gpr 0] [])) #v[57, 59]
    (.letOp (n := 63) (.out 0x10048d (movR32R32Effect 0x10048d 3 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[59]
    (.letOp (n := 64) (.exec 0x10048d (fun s => s.RIP = 0x10048d) (movR32R32Effect 0x10048d 3 14 0) (Reg.operands [.gpr 0] [])) #v[59]
    (.letOp (n := 65) (.out 0x100490 (andR32Imm8Effect 0x100490 4 14 0xf) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14] []) (.reg (.gpr 14))) #v[63]
    (.letOp (n := 66) (.exec 0x100490 (fun s => s.RIP = 0x100490) (andR32Imm8Effect 0x100490 4 14 0xf) (Reg.operands [.gpr 14] [])) #v[63]
    (.letOp (n := 67) (.out 0x100494 (cmpR64Imm8Effect 0x100494 0 0x10) (EffectPart.reads (.flag .CF) [.gpr 0] []) (.flag .CF)) #v[59]
    (.letOp (n := 68) (.exec 0x100494 (fun s => s.RIP = 0x100494) (cmpR64Imm8Effect 0x100494 0 0x10) (Reg.operands [.gpr 0] [])) #v[59]
    (.letOp (n := 69) (.pure (condOp 2)) #v[67]
    (.terminate (.condBr (Fin.last 69) ⟨.l1004b5, RegMap.args [(0, 59), (2, 2), (3, 3), (4, 4), (6, 6), (9, 9), (12, 12), (13, 55), (14, 65), (15, 61), (16, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 70⟩ ⟨.l10049a, RegMap.args [(0, 59), (2, 2), (3, 3), (4, 4), (6, 6), (9, 9), (12, 12), (13, 55), (14, 65), (15, 61), (16, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 70⟩))))))))))))))))))

def bytes_l100479 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x10, 0x4C, 0x8B, 0x28, 0x49, 0x83, 0xC7, 0x31, 0x48, 0x8B, 0x44, 0x24,
    0x18, 0x49, 0x21, 0xC7, 0x41, 0x89, 0xC6, 0x41, 0x83, 0xE6, 0x0F, 0x48, 0x83, 0xF8, 0x10, 0x72,
    0x1B]

theorem code_l100479 : ∀ x ∈ codeRange 0x100479 bytes_l100479, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x479 33 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10049a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10049a (movR64R64Effect 0x10049a 3 15) (EffectPart.reads (.reg (.gpr 3)) [.gpr 15] []) (.reg (.gpr 3))) #v[15]
    (.letOp (n := 54) (.exec 0x10049a (fun s => s.RIP = 0x10049a) (movR64R64Effect 0x10049a 3 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.out 0x10049d (movR64R64Effect 0x10049d 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 13] []) (.reg (.gpr 6))) #v[13]
    (.letOp (n := 56) (.exec 0x10049d (fun s => s.RIP = 0x10049d) (movR64R64Effect 0x10049d 6 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.terminate (.br ⟨.l1004a0, RegMap.args [(2, 2), (3, 53), (4, 4), (6, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l10049a : List UInt8 :=
  [0x4C, 0x89, 0xFB, 0x4C, 0x89, 0xEE]

theorem code_l10049a : ∀ x ∈ codeRange 0x10049a bytes_l10049a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x49a 6 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1004a0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1004a0 (leaR64Effect 0x1004a0 5 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 6] []) (.reg (.gpr 5))) #v[6]
    (.letOp (n := 54) (.exec 0x1004a0 (fun s => s.RIP = 0x1004a0) (leaR64Effect 0x1004a0 5 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 55) (.out 0x1004a4 (movR64R64Effect 0x1004a4 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[12]
    (.letOp (n := 56) (.exec 0x1004a4 (fun s => s.RIP = 0x1004a4) (movR64R64Effect 0x1004a4 7 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 57) (.out 0x1004a7 (callEffect (fun _ => 0x101e30) 0x1004ac) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x1004a7 (PushPre 0x1004a7 5) (callEffect (fun _ => 0x101e30) 0x1004ac) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x1004ac⟩) #v[]
    (.terminate (.call ⟨.l101e30, RegMap.args [(2, 2), (3, 3), (4, 57), (5, 53), (6, 6), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ { target := .l1004ac, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l1004a0 : List UInt8 :=
  [0x48, 0x8D, 0x6E, 0x10, 0x4C, 0x89, 0xE7, 0xE8, 0x84, 0x19, 0x00, 0x00]

theorem code_l1004a0 : ∀ x ∈ codeRange 0x1004a0 bytes_l1004a0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4a0 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1004ac : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1004ac (movR64R64Effect 0x1004ac 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[5]
    (.letOp (n := 54) (.exec 0x1004ac (fun s => s.RIP = 0x1004ac) (movR64R64Effect 0x1004ac 6 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 55) (.out 0x1004af (addR64Imm8Effect 0x1004af 3 0xf0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[3]
    (.letOp (n := 56) (.out 0x1004af (addR64Imm8Effect 0x1004af 3 0xf0) (EffectPart.reads (.flag .ZF) [.gpr 3] []) (.flag .ZF)) #v[3]
    (.letOp (n := 57) (.exec 0x1004af (fun s => s.RIP = 0x1004af) (addR64Imm8Effect 0x1004af 3 0xf0) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 58) (.pure (condOp 5)) #v[56]
    (.terminate (.condBr (Fin.last 58) ⟨.l1004a0, RegMap.args [(2, 2), (3, 55), (4, 4), (5, 5), (6, 53), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩ ⟨.l1004b5, RegMap.args [(2, 2), (3, 55), (4, 4), (5, 5), (6, 53), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l1004ac : List UInt8 :=
  [0x48, 0x89, 0xEE, 0x48, 0x83, 0xC3, 0xF0, 0x75, 0xEB]

theorem code_l1004ac : ∀ x ∈ codeRange 0x1004ac bytes_l1004ac, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4ac 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1004b5 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1004b5 (movR64M64Effect 0x1004b5 5 (.sib 4 none 0 (.d32 0x1c0))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 54) (.exec 0x1004b5 (LoadPre 0x1004b5 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1c0)) s (0x1004b5 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1004b5 5 (.sib 4 none 0 (.d32 0x1c0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1004bd (testR64R64Effect 0x1004bd 14 14) (EffectPart.reads (.flag .ZF) [.gpr 14, .gpr 14] []) (.flag .ZF)) #v[14, 14]
    (.letOp (n := 56) (.exec 0x1004bd (fun s => s.RIP = 0x1004bd) (testR64R64Effect 0x1004bd 14 14) (Reg.operands [.gpr 14, .gpr 14] [])) #v[14, 14]
    (.letOp (n := 57) (.pure (condOp 4)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l1004fc, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l1004c2, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l1004b5 : List UInt8 :=
  [0x48, 0x8B, 0xAC, 0x24, 0xC0, 0x01, 0x00, 0x00, 0x4D, 0x85, 0xF6, 0x74, 0x3A]

theorem code_l1004b5 : ∀ x ∈ codeRange 0x1004b5 bytes_l1004b5, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4b5 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1004c2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1004c2 (addR64R64Effect 0x1004c2 13 15) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 15] []) (.reg (.gpr 13))) #v[13, 15]
    (.letOp (n := 54) (.exec 0x1004c2 (fun s => s.RIP = 0x1004c2) (addR64R64Effect 0x1004c2 13 15) (Reg.operands [.gpr 13, .gpr 15] [])) #v[13, 15]
    (.letOp (n := 55) (.out 0x1004c5 (movR32Imm32Effect 0x1004c5 5 2 0x10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 56) (.exec 0x1004c5 (fun s => s.RIP = 0x1004c5) (movR32Imm32Effect 0x1004c5 5 2 0x10) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x1004ca (subR64R64Effect 0x1004ca 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 14] []) (.reg (.gpr 2))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x1004ca (fun s => s.RIP = 0x1004ca) (subR64R64Effect 0x1004ca 2 14) (Reg.operands [.gpr 2, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x1004cd (leaR64Effect 0x1004cd 7 (.sib 4 (some 14) 0 .none)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4, .gpr 14] []) (.reg (.gpr 7))) #v[4, 14]
    (.letOp (n := 60) (.exec 0x1004cd (fun s => s.RIP = 0x1004cd) (leaR64Effect 0x1004cd 7 (.sib 4 (some 14) 0 .none)) (Reg.operands [.gpr 4, .gpr 14] [])) #v[4, 14]
    (.letOp (n := 61) (.out 0x1004d1 (addR64Imm8Effect 0x1004d1 7 0x20) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[59]
    (.letOp (n := 62) (.exec 0x1004d1 (fun s => s.RIP = 0x1004d1) (addR64Imm8Effect 0x1004d1 7 0x20) (Reg.operands [.gpr 7] [])) #v[59]
    (.letOp (n := 63) (.out 0x1004d5 (xorR32R32Effect 0x1004d5 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[6, 6]
    (.letOp (n := 64) (.exec 0x1004d5 (fun s => s.RIP = 0x1004d5) (xorR32R32Effect 0x1004d5 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 65) (.out 0x1004d7 (callEffect (callMemPtr 0x1004d7 (.rip 0x100f03)) (0x1004d7 + BitVec.ofNat 64 (callMemLen (.rip 0x100f03)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 66) (.exec 0x1004d7 (GoesTo (CallMemPre 0x1004d7 (.rip 0x100f03)) (callEffect (callMemPtr 0x1004d7 (.rip 0x100f03)) (0x1004d7 + BitVec.ofNat 64 (callMemLen (.rip 0x100f03)))) 0x102d70) (callEffect (callMemPtr 0x1004d7 (.rip 0x100f03)) (0x1004d7 + BitVec.ofNat 64 (callMemLen (.rip 0x100f03)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.const ⟨64, 0x1004dd⟩) #v[]
    (.terminate (.call ⟨.l102d70, RegMap.args [(2, 57), (3, 3), (4, 65), (5, 5), (6, 63), (7, 61), (9, 9), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 68⟩ { target := .l1004dd, kept := #v[], arity := rfl, guard := some (Fin.last 67) }))))))))))))))))

def bytes_l1004c2 : List UInt8 :=
  [0x4D, 0x01, 0xFD, 0xBA, 0x10, 0x00, 0x00, 0x00, 0x4C, 0x29, 0xF2, 0x4A, 0x8D, 0x3C, 0x34, 0x48,
    0x83, 0xC7, 0x20, 0x31, 0xF6, 0xFF, 0x15, 0x03, 0x0F, 0x10, 0x00]

theorem code_l1004c2 : ∀ x ∈ codeRange 0x1004c2 bytes_l1004c2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4c2 27 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1004dd : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1004dd (leaR64Effect 0x1004dd 3 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 54) (.exec 0x1004dd (fun s => s.RIP = 0x1004dd) (leaR64Effect 0x1004dd 3 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1004e2 (movR64R64Effect 0x1004e2 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 56) (.exec 0x1004e2 (fun s => s.RIP = 0x1004e2) (movR64R64Effect 0x1004e2 7 3) (Reg.operands [.gpr 3] [])) #v[53]
    (.letOp (n := 57) (.out 0x1004e5 (movR64R64Effect 0x1004e5 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 13] []) (.reg (.gpr 6))) #v[13]
    (.letOp (n := 58) (.exec 0x1004e5 (fun s => s.RIP = 0x1004e5) (movR64R64Effect 0x1004e5 6 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 59) (.out 0x1004e8 (movR64R64Effect 0x1004e8 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14] []) (.reg (.gpr 2))) #v[14]
    (.letOp (n := 60) (.exec 0x1004e8 (fun s => s.RIP = 0x1004e8) (movR64R64Effect 0x1004e8 2 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 61) (.out 0x1004eb (callEffect (callMemPtr 0x1004eb (.rip 0x100eb7)) (0x1004eb + BitVec.ofNat 64 (callMemLen (.rip 0x100eb7)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 62) (.exec 0x1004eb (GoesTo (CallMemPre 0x1004eb (.rip 0x100eb7)) (callEffect (callMemPtr 0x1004eb (.rip 0x100eb7)) (0x1004eb + BitVec.ofNat 64 (callMemLen (.rip 0x100eb7)))) 0x102dc0) (callEffect (callMemPtr 0x1004eb (.rip 0x100eb7)) (0x1004eb + BitVec.ofNat 64 (callMemLen (.rip 0x100eb7)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.const ⟨64, 0x1004f1⟩) #v[]
    (.terminate (.call ⟨.l102dc0, RegMap.args [(2, 59), (3, 53), (4, 61), (5, 5), (6, 57), (7, 55), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ { target := .l1004f1, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l1004dd : List UInt8 :=
  [0x48, 0x8D, 0x5C, 0x24, 0x20, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xEE, 0x4C, 0x89, 0xF2, 0xFF, 0x15,
    0xB7, 0x0E, 0x10, 0x00]

theorem code_l1004dd : ∀ x ∈ codeRange 0x1004dd bytes_l1004dd, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4dd 20 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1004f1 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1004f1 (movR64R64Effect 0x1004f1 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[12]
    (.letOp (n := 54) (.exec 0x1004f1 (fun s => s.RIP = 0x1004f1) (movR64R64Effect 0x1004f1 7 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 55) (.out 0x1004f4 (movR64R64Effect 0x1004f4 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[3]
    (.letOp (n := 56) (.exec 0x1004f4 (fun s => s.RIP = 0x1004f4) (movR64R64Effect 0x1004f4 6 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 57) (.out 0x1004f7 (callEffect (fun _ => 0x101e30) 0x1004fc) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x1004f7 (PushPre 0x1004f7 5) (callEffect (fun _ => 0x101e30) 0x1004fc) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x1004fc⟩) #v[]
    (.terminate (.call ⟨.l101e30, RegMap.args [(2, 2), (3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ { target := .l1004fc, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l1004f1 : List UInt8 :=
  [0x4C, 0x89, 0xE7, 0x48, 0x89, 0xDE, 0xE8, 0x34, 0x19, 0x00, 0x00]

theorem code_l1004f1 : ∀ x ∈ codeRange 0x1004f1 bytes_l1004f1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4f1 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1004fc : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1004fc (movR64M64Effect 0x1004fc 0 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1004fc (LoadPre 0x1004fc (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x1004fc + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1004fc 0 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x100504 (StorePre 0x100504 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x100504 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100504 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x100509 (movR64M64Effect 0x100509 0 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x100509 (LoadPre 0x100509 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x100509 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100509 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x10050e (StorePre 0x10050e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10050e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10050e 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x100513 (leaR64Effect 0x100513 6 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 60) (.exec 0x100513 (fun s => s.RIP = 0x100513) (leaR64Effect 0x100513 6 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x100518 (movR64R64Effect 0x100518 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[12]
    (.letOp (n := 62) (.exec 0x100518 (fun s => s.RIP = 0x100518) (movR64R64Effect 0x100518 7 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 63) (.out 0x10051b (callEffect (fun _ => 0x101e30) 0x100520) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 64) (.exec 0x10051b (PushPre 0x10051b 5) (callEffect (fun _ => 0x101e30) 0x100520) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.const ⟨64, 0x100520⟩) #v[]
    (.terminate (.call ⟨.l101e30, RegMap.args [(0, 56), (2, 2), (3, 3), (4, 63), (5, 5), (6, 59), (7, 61), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩ { target := .l100520, kept := #v[], arity := rfl, guard := some (Fin.last 65) }))))))))))))))

def bytes_l1004fc : List UInt8 :=
  [0x48, 0x8B, 0x84, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44,
    0x24, 0x18, 0x48, 0x89, 0x44, 0x24, 0x28, 0x48, 0x8D, 0x74, 0x24, 0x20, 0x4C, 0x89, 0xE7, 0xE8,
    0x10, 0x19, 0x00, 0x00]

theorem code_l1004fc : ∀ x ∈ codeRange 0x1004fc bytes_l1004fc, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4fc 36 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100520 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100520 (movR64M64Effect 0x100520 0 (.sib 12 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[12]
    (.letOp (n := 54) (.exec 0x100520 (LoadPre 0x100520 (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x30)) s (0x100520 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100520 0 (.sib 12 none 0 (.d8 0x30))) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 55) (.exec 0x100525 (StorePre 0x100525 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x100525 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100525 0 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x10052a (movR64M64Effect 0x10052a 0 (.sib 12 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[12]
    (.letOp (n := 57) (.exec 0x10052a (LoadPre 0x10052a (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x28)) s (0x10052a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10052a 0 (.sib 12 none 0 (.d8 0x28))) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 58) (.exec 0x10052f (StorePre 0x10052f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10052f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10052f 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x100534 (movR64M64Effect 0x100534 0 (.sib 12 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[12]
    (.letOp (n := 60) (.exec 0x100534 (LoadPre 0x100534 (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x20)) s (0x100534 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100534 0 (.sib 12 none 0 (.d8 0x20))) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 61) (.exec 0x100539 (StorePre 0x100539 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x100539 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100539 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x10053e (movR64M64Effect 0x10053e 0 (.sib 12 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[12]
    (.letOp (n := 63) (.exec 0x10053e (LoadPre 0x10053e (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x18)) s (0x10053e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10053e 0 (.sib 12 none 0 (.d8 0x18))) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 64) (.exec 0x100543 (StorePre 0x100543 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x100543 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100543 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x100548 (movR64M64Effect 0x100548 0 (.sib 12 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[12]
    (.letOp (n := 66) (.exec 0x100548 (LoadPre 0x100548 (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x10)) s (0x100548 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100548 0 (.sib 12 none 0 (.d8 0x10))) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 67) (.exec 0x10054d (StorePre 0x10054d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10054d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10054d 0 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x100552 (movR64M64Effect 0x100552 0 (.sib 12 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[12]
    (.letOp (n := 69) (.exec 0x100552 (LoadPre 0x100552 (fun s => AddrMode.addr (.sib 12 none 0 .none) s (0x100552 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x100552 0 (.sib 12 none 0 .none)) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 70) (.out 0x100556 (movR64M64Effect 0x100556 1 (.sib 12 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 12] []) (.reg (.gpr 1))) #v[12]
    (.letOp (n := 71) (.exec 0x100556 (LoadPre 0x100556 (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x8)) s (0x100556 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100556 1 (.sib 12 none 0 (.d8 0x8))) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 72) (.exec 0x10055b (StorePre 0x10055b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10055b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10055b 1 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[70, 4]
    (.letOp (n := 73) (.exec 0x100560 (StorePre 0x100560 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x100560 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100560 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[68, 4]
    (.letOp (n := 74) (.out 0x100565 (leaR64Effect 0x100565 7 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 75) (.exec 0x100565 (fun s => s.RIP = 0x100565) (leaR64Effect 0x100565 7 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 76) (.out 0x10056d (leaR64Effect 0x10056d 6 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 77) (.exec 0x10056d (fun s => s.RIP = 0x10056d) (leaR64Effect 0x10056d 6 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 78) (.out 0x100572 (callEffect (fun _ => 0x101ce0) 0x100577) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 79) (.exec 0x100572 (PushPre 0x100572 5) (callEffect (fun _ => 0x101ce0) 0x100577) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 80) (.const ⟨64, 0x100577⟩) #v[]
    (.terminate (.call ⟨.l101ce0, RegMap.args [(0, 68), (1, 70), (3, 3), (4, 78), (5, 5), (6, 76), (7, 74), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 81⟩ { target := .l100577, kept := #v[], arity := rfl, guard := some (Fin.last 80) })))))))))))))))))))))))))))))

def bytes_l100520 : List UInt8 :=
  [0x49, 0x8B, 0x44, 0x24, 0x30, 0x48, 0x89, 0x44, 0x24, 0x50, 0x49, 0x8B, 0x44, 0x24, 0x28, 0x48,
    0x89, 0x44, 0x24, 0x48, 0x49, 0x8B, 0x44, 0x24, 0x20, 0x48, 0x89, 0x44, 0x24, 0x40, 0x49, 0x8B,
    0x44, 0x24, 0x18, 0x48, 0x89, 0x44, 0x24, 0x38, 0x49, 0x8B, 0x44, 0x24, 0x10, 0x48, 0x89, 0x44,
    0x24, 0x30, 0x49, 0x8B, 0x04, 0x24, 0x49, 0x8B, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x4C, 0x24, 0x28,
    0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8D, 0xBC, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x74,
    0x24, 0x20, 0xE8, 0x69, 0x17, 0x00, 0x00]

theorem code_l100520 : ∀ x ∈ codeRange 0x100520 bytes_l100520, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x520 87 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100577_1 : Block Op Label signature Reg.count 95 :=
  .letOp (n := 95) (.out 0x1005c9 (cmpM8Imm8Effect 0x1005c9 5 (.sib 4 none 0 (.d8 0x6)) 0x0) (EffectPart.reads (.flag .ZF) [.gpr 4] []) (.flag .ZF)) #v[4]
    (.letOp (n := 96) (.exec 0x1005c9 (LoadPre 0x1005c9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6)) s (0x1005c9 + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x1005c9 5 (.sib 4 none 0 (.d8 0x6)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 97) (.out 0x1005ce (movR8Imm8Effect 0x1005ce 2 0 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[93]
    (.letOp (n := 98) (.exec 0x1005ce (fun s => s.RIP = 0x1005ce) (movR8Imm8Effect 0x1005ce 2 0 0x1) (Reg.operands [.gpr 0] [])) #v[93]
    (.letOp (n := 99) (.pure (condOp 4)) #v[95]
    (.terminate (.condBr (Fin.last 99) ⟨.l1005ea, RegMap.args [(0, 97), (1, 59), (2, 87), (3, 3), (4, 4), (5, 5), (6, 80), (7, 67), (8, 63), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (19, 95), (22, 22), (39, 39), (50, 50), (51, 51)] 100⟩ ⟨.l1005d2, RegMap.args [(0, 97), (1, 59), (2, 87), (3, 3), (4, 4), (5, 5), (6, 80), (7, 67), (8, 63), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (19, 95), (22, 22), (39, 39), (50, 50), (51, 51)] 100⟩))))))

def bytes_l100577_1 : List UInt8 :=
  [0x80, 0x7C, 0x24, 0x06, 0x00, 0xB0, 0x01, 0x74, 0x18]

theorem code_l100577_1 : ∀ x ∈ codeRange 0x1005c9 bytes_l100577_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5c9 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100577 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100577 (movR64M64Effect 0x100577 2 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 54) (.exec 0x100577 (LoadPre 0x100577 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x100577 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x100577 2 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10057f (movR64M64Effect 0x10057f 6 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 56) (.exec 0x10057f (LoadPre 0x10057f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x10057f + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10057f 6 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x100587 (xorR32R32Effect 0x100587 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[0, 0]
    (.letOp (n := 58) (.exec 0x100587 (fun s => s.RIP = 0x100587) (xorR32R32Effect 0x100587 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.letOp (n := 59) (.out 0x100589 (movR16Imm16Effect 0x100589 4 1 0x1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1]
    (.letOp (n := 60) (.exec 0x100589 (fun s => s.RIP = 0x100589) (movR16Imm16Effect 0x100589 4 1 0x1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 61) (.out 0x10058d (movR16Imm16Effect 0x10058d 4 7 0x1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[7]
    (.letOp (n := 62) (.exec 0x10058d (fun s => s.RIP = 0x10058d) (movR16Imm16Effect 0x10058d 4 7 0x1) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 63) (.out 0x100591 (movR64M64Effect 0x100591 8 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 64) (.exec 0x100591 (LoadPre 0x100591 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x100591 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x100591 8 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x100599 (xorR64R64Effect 0x100599 2 8) (EffectPart.reads (.flag .ZF) [.gpr 2, .gpr 8] []) (.flag .ZF)) #v[53, 63]
    (.letOp (n := 66) (.exec 0x100599 (fun s => s.RIP = 0x100599) (xorR64R64Effect 0x100599 2 8) (Reg.operands [.gpr 2, .gpr 8] [])) #v[53, 63]
    (.letOp (n := 67) (.out 0x10059c (atFlags (condHolds 5) (cmovR64R64Effect 0x10059c 4 7 0)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 7))) #v[61, 57, 65]
    (.letOp (n := 68) (.exec 0x10059c (fun s => s.RIP = 0x10059c) (atFlags (condHolds 5) (cmovR64R64Effect 0x10059c 4 7 0)) (Reg.operands [.gpr 7, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[61, 57, 65]
    (.letOp (n := 69) (.out 0x1005a0 (movzxR32R8Effect 0x1005a0 4 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7] []) (.reg (.gpr 2))) #v[67]
    (.letOp (n := 70) (.exec 0x1005a0 (fun s => s.RIP = 0x1005a0) (movzxR32R8Effect 0x1005a0 4 2 7) (Reg.operands [.gpr 7] [])) #v[67]
    (.letOp (n := 71) (.out 0x1005a4 (xorR64R64Effect 0x1005a4 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 5] []) (.reg (.gpr 6))) #v[55, 5]
    (.letOp (n := 72) (.out 0x1005a4 (xorR64R64Effect 0x1005a4 6 5) (EffectPart.reads (.flag .ZF) [.gpr 6, .gpr 5] []) (.flag .ZF)) #v[55, 5]
    (.letOp (n := 73) (.exec 0x1005a4 (fun s => s.RIP = 0x1005a4) (xorR64R64Effect 0x1005a4 6 5) (Reg.operands [.gpr 6, .gpr 5] [])) #v[55, 5]
    (.letOp (n := 74) (.out 0x1005a7 (atFlags (condHolds 5) (cmovR64R64Effect 0x1005a7 4 2 0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 2))) #v[69, 57, 72]
    (.letOp (n := 75) (.exec 0x1005a7 (fun s => s.RIP = 0x1005a7) (atFlags (condHolds 5) (cmovR64R64Effect 0x1005a7 4 2 0)) (Reg.operands [.gpr 2, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[69, 57, 72]
    (.letOp (n := 76) (.out 0x1005ab (movzxR32R8Effect 0x1005ab 3 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[74]
    (.letOp (n := 77) (.exec 0x1005ab (fun s => s.RIP = 0x1005ab) (movzxR32R8Effect 0x1005ab 3 2 2) (Reg.operands [.gpr 2] [])) #v[74]
    (.letOp (n := 78) (.out 0x1005ae (xorR32R32Effect 0x1005ae 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[71, 71]
    (.letOp (n := 79) (.exec 0x1005ae (fun s => s.RIP = 0x1005ae) (xorR32R32Effect 0x1005ae 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[71, 71]
    (.letOp (n := 80) (.out 0x1005b0 (xorR64R64Effect 0x1005b0 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[78, 57]
    (.letOp (n := 81) (.out 0x1005b0 (xorR64R64Effect 0x1005b0 6 0) (EffectPart.reads (.flag .ZF) [.gpr 6, .gpr 0] []) (.flag .ZF)) #v[78, 57]
    (.letOp (n := 82) (.exec 0x1005b0 (fun s => s.RIP = 0x1005b0) (xorR64R64Effect 0x1005b0 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[78, 57]
    (.letOp (n := 83) (.out 0x1005b3 (atFlags (condHolds 5) (cmovR64R64Effect 0x1005b3 4 2 0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 2))) #v[76, 57, 81]
    (.letOp (n := 84) (.exec 0x1005b3 (fun s => s.RIP = 0x1005b3) (atFlags (condHolds 5) (cmovR64R64Effect 0x1005b3 4 2 0)) (Reg.operands [.gpr 2, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[76, 57, 81]
    (.letOp (n := 85) (.out 0x1005b7 (movzxR32R8Effect 0x1005b7 3 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[83]
    (.letOp (n := 86) (.exec 0x1005b7 (fun s => s.RIP = 0x1005b7) (movzxR32R8Effect 0x1005b7 3 2 2) (Reg.operands [.gpr 2] [])) #v[83]
    (.letOp (n := 87) (.out 0x1005ba (xorR16R16Effect 0x1005ba 3 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[85, 59]
    (.letOp (n := 88) (.out 0x1005ba (xorR16R16Effect 0x1005ba 3 2 1) (EffectPart.reads (.flag .ZF) [.gpr 2, .gpr 1] []) (.flag .ZF)) #v[85, 59]
    (.letOp (n := 89) (.exec 0x1005ba (fun s => s.RIP = 0x1005ba) (xorR16R16Effect 0x1005ba 3 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[85, 59]
    (.letOp (n := 90) (.out 0x1005bd (atFlags (condHolds 4) (cmovR32R32Effect 0x1005bd 3 0 1)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 0))) #v[57, 59, 88]
    (.letOp (n := 91) (.exec 0x1005bd (fun s => s.RIP = 0x1005bd) (atFlags (condHolds 4) (cmovR32R32Effect 0x1005bd 3 0 1)) (Reg.operands [.gpr 0, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[57, 59, 88]
    (.letOp (n := 92) (.exec 0x1005c0 (StorePre 0x1005c0 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6)) s (0x1005c0 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1005c0 4 0 (.sib 4 none 0 (.d8 0x6))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[90, 4]
    (.letOp (n := 93) (.out 0x1005c4 (leaR64Effect 0x1005c4 0 (.sib 4 none 0 (.d8 0x6))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 94) (.exec 0x1005c4 (fun s => s.RIP = 0x1005c4) (leaR64Effect 0x1005c4 0 (.sib 4 none 0 (.d8 0x6))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l100577_1))))))))))))))))))))))))))))))))))))))))))

def bytes_l100577 : List UInt8 :=
  [0x48, 0x8B, 0x94, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x48, 0x8B, 0xB4, 0x24, 0xA8, 0x00, 0x00, 0x00,
    0x31, 0xC0, 0x66, 0xB9, 0x01, 0x00, 0x66, 0xBF, 0x01, 0x00, 0x4C, 0x8B, 0x84, 0x24, 0xC8, 0x00,
    0x00, 0x00, 0x4C, 0x31, 0xC2, 0x48, 0x0F, 0x45, 0xF8, 0x40, 0x0F, 0xB6, 0xD7, 0x48, 0x31, 0xEE,
    0x48, 0x0F, 0x45, 0xD0, 0x0F, 0xB6, 0xD2, 0x31, 0xF6, 0x48, 0x31, 0xC6, 0x48, 0x0F, 0x45, 0xD0,
    0x0F, 0xB6, 0xD2, 0x66, 0x31, 0xCA, 0x0F, 0x44, 0xC1, 0x88, 0x44, 0x24, 0x06, 0x48, 0x8D, 0x44,
    0x24, 0x06] ++ bytes_l100577_1

theorem code_l100577 : ∀ x ∈ codeRange 0x100577 bytes_l100577, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x577 82 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l100577_1

@[cfg_block] def b_l1005d2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1005d2 (leaR64Effect 0x1005d2 7 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x1005d2 (fun s => s.RIP = 0x1005d2) (leaR64Effect 0x1005d2 7 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1005da (movR64M64Effect 0x1005da 6 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 56) (.exec 0x1005da (LoadPre 0x1005da (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1005da + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1005da 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1005df (callEffect (fun _ => 0x100a80) 0x1005e4) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x1005df (PushPre 0x1005df 5) (callEffect (fun _ => 0x100a80) 0x1005e4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x1005e4⟩) #v[]
    (.terminate (.call ⟨.l100a80, RegMap.args [(2, 2), (3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ { target := .l1005e4, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l1005d2 : List UInt8 :=
  [0x48, 0x8D, 0xBC, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x74, 0x24, 0x10, 0xE8, 0x9C, 0x04,
    0x00, 0x00]

theorem code_l1005d2 : ∀ x ∈ codeRange 0x1005d2 bytes_l1005d2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5d2 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1005e4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1005e4 (testR8R8Effect 0x1005e4 2 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[0, 0]
    (.letOp (n := 54) (.exec 0x1005e4 (fun s => s.RIP = 0x1005e4) (testR8R8Effect 0x1005e4 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l100620, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (9, 9), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l1005e8, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (9, 9), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l1005e4 : List UInt8 :=
  [0x84, 0xC0, 0x75, 0x38]

theorem code_l1005e4 : ∀ x ∈ codeRange 0x1005e4 bytes_l1005e4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5e4 4 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1005e8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1005e8 (xorR32R32Effect 0x1005e8 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[0, 0]
    (.letOp (n := 54) (.exec 0x1005e8 (fun s => s.RIP = 0x1005e8) (xorR32R32Effect 0x1005e8 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.terminate (.br ⟨.l1005ea, RegMap.args [(0, 53), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (9, 9), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l1005e8 : List UInt8 :=
  [0x31, 0xC0]

theorem code_l1005e8 : ∀ x ∈ codeRange 0x1005e8 bytes_l1005e8, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5e8 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1005ea : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1005ea (addR64Imm32Effect 0x1005ea 4 0x188) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 54) (.exec 0x1005ea (fun s => s.RIP = 0x1005ea) (addR64Imm32Effect 0x1005ea 4 0x188) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1005f1 (popR64Effect 0x1005f1 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[53]
    (.letOp (n := 56) (.out 0x1005f1 (popR64Effect 0x1005f1 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[53]
    (.letOp (n := 57) (.exec 0x1005f1 (PopPre 0x1005f1) (popR64Effect 0x1005f1 1 3) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 58) (.out 0x1005f2 (popR64Effect 0x1005f2 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[56]
    (.letOp (n := 59) (.out 0x1005f2 (popR64Effect 0x1005f2 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[56]
    (.letOp (n := 60) (.exec 0x1005f2 (PopPre 0x1005f2) (popR64Effect 0x1005f2 2 12) (Reg.operands [.gpr 4] [])) #v[56]
    (.letOp (n := 61) (.out 0x1005f4 (popR64Effect 0x1005f4 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[59]
    (.letOp (n := 62) (.out 0x1005f4 (popR64Effect 0x1005f4 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 63) (.exec 0x1005f4 (PopPre 0x1005f4) (popR64Effect 0x1005f4 2 13) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 64) (.out 0x1005f6 (popR64Effect 0x1005f6 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[62]
    (.letOp (n := 65) (.out 0x1005f6 (popR64Effect 0x1005f6 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[62]
    (.letOp (n := 66) (.exec 0x1005f6 (PopPre 0x1005f6) (popR64Effect 0x1005f6 2 14) (Reg.operands [.gpr 4] [])) #v[62]
    (.letOp (n := 67) (.out 0x1005f8 (popR64Effect 0x1005f8 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[65]
    (.letOp (n := 68) (.out 0x1005f8 (popR64Effect 0x1005f8 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 69) (.exec 0x1005f8 (PopPre 0x1005f8) (popR64Effect 0x1005f8 2 15) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 70) (.out 0x1005fa (popR64Effect 0x1005fa 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[68]
    (.letOp (n := 71) (.out 0x1005fa (popR64Effect 0x1005fa 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[68]
    (.letOp (n := 72) (.exec 0x1005fa (PopPre 0x1005fa) (popR64Effect 0x1005fa 1 5) (Reg.operands [.gpr 4] [])) #v[68]
    (.letOp (n := 73) (.out 0x1005fb (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[71]
    (.letOp (n := 74) (.out 0x1005fb (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[71]
    (.letOp (n := 75) (.exec 0x1005fb (RetPre 0x1005fb) (retEffect) (Reg.operands [.gpr 4] [])) #v[71]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 2), (3, 55), (4, 74), (5, 70), (6, 6), (7, 7), (9, 9), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 76) (some ⟨73, by decide⟩)))))))))))))))))))))))))

def bytes_l1005ea : List UInt8 :=
  [0x48, 0x81, 0xC4, 0x88, 0x01, 0x00, 0x00, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F,
    0x5D, 0xC3]

theorem code_l1005ea : ∀ x ∈ codeRange 0x1005ea bytes_l1005ea, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5ea 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1005fc : Block Op Label signature Reg.count 53 :=
  cutBlock 0x1005fc

def bytes_l1005fc : List UInt8 :=
  [0x48]

theorem code_l1005fc : ∀ x ∈ codeRange 0x1005fc bytes_l1005fc, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5fc 1 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100620 : Block Op Label signature Reg.count 53 :=
  cutBlock 0x100620

def bytes_l100620 : List UInt8 :=
  [0x48]

theorem code_l100620 : ∀ x ∈ codeRange 0x100620 bytes_l100620, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x620 1 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100a80 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100a80 (pushR64Effect 0x100a80 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x100a80 (PushPre 0x100a80 1) (pushR64Effect 0x100a80 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x100a81 (pushR64Effect 0x100a81 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x100a81 (PushPre 0x100a81 2) (pushR64Effect 0x100a81 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x100a83 (pushR64Effect 0x100a83 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x100a83 (PushPre 0x100a83 2) (pushR64Effect 0x100a83 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x100a85 (pushR64Effect 0x100a85 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x100a85 (PushPre 0x100a85 2) (pushR64Effect 0x100a85 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x100a87 (pushR64Effect 0x100a87 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x100a87 (PushPre 0x100a87 2) (pushR64Effect 0x100a87 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x100a89 (pushR64Effect 0x100a89 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x100a89 (PushPre 0x100a89 1) (pushR64Effect 0x100a89 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x100a8a (subR64Imm32Effect 0x100a8a 4 0x170) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x100a8a (fun s => s.RIP = 0x100a8a) (subR64Imm32Effect 0x100a8a 4 0x170) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x100a91 (movR64M64Effect 0x100a91 11 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 6] []) (.reg (.gpr 11))) #v[6]
    (.letOp (n := 68) (.exec 0x100a91 (LoadPre 0x100a91 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x100a91 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x100a91 11 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 69) (.out 0x100a95 (movR32M32Effect 0x100a95 12 (.base 7 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 7] []) (.reg (.gpr 12))) #v[7]
    (.letOp (n := 70) (.exec 0x100a95 (LoadPre 0x100a95 (fun s => AddrMode.addr (.base 7 (.d8 0x30)) s (0x100a95 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x100a95 12 (.base 7 (.d8 0x30))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 71) (.out 0x100a99 (movzxR32M8Effect 0x100a99 4 1 (.base 7 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 7] []) (.reg (.gpr 1))) #v[7]
    (.letOp (n := 72) (.exec 0x100a99 (LoadPre 0x100a99 (fun s => AddrMode.addr (.base 7 (.d8 0x40)) s (0x100a99 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x100a99 4 1 (.base 7 (.d8 0x40))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 73) (.out 0x100a9d (movR32Imm32Effect 0x100a9d 6 10 0x40) (EffectPart.reads (.reg (.gpr 10)) [] []) (.reg (.gpr 10))) #v[]
    (.letOp (n := 74) (.exec 0x100a9d (fun s => s.RIP = 0x100a9d) (movR32Imm32Effect 0x100a9d 6 10 0x40) (Reg.operands [] [])) #v[]
    (.letOp (n := 75) (.out 0x100aa3 (subR64R64Effect 0x100aa3 10 1) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 1] []) (.reg (.gpr 10))) #v[73, 71]
    (.letOp (n := 76) (.exec 0x100aa3 (fun s => s.RIP = 0x100aa3) (subR64R64Effect 0x100aa3 10 1) (Reg.operands [.gpr 10, .gpr 1] [])) #v[73, 71]
    (.letOp (n := 77) (.out 0x100aa6 (movR64R64Effect 0x100aa6 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[67]
    (.letOp (n := 78) (.exec 0x100aa6 (fun s => s.RIP = 0x100aa6) (movR64R64Effect 0x100aa6 0 11) (Reg.operands [.gpr 11] [])) #v[67]
    (.letOp (n := 79) (.out 0x100aa9 (subR64R64Effect 0x100aa9 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[77, 75]
    (.letOp (n := 80) (.out 0x100aa9 (subR64R64Effect 0x100aa9 0 10) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 10] []) (.flag .CF)) #v[77, 75]
    (.letOp (n := 81) (.exec 0x100aa9 (fun s => s.RIP = 0x100aa9) (subR64R64Effect 0x100aa9 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[77, 75]
    (.letOp (n := 82) (.pure (condOp 2)) #v[80]
    (.terminate (.condBr (Fin.last 82) ⟨.l100ad0, RegMap.args [(0, 79), (1, 71), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (9, 9), (10, 75), (11, 67), (12, 69), (13, 13), (14, 14), (15, 15), (16, 80), (22, 22), (39, 39), (50, 50), (51, 51)] 83⟩ ⟨.l100aae, RegMap.args [(0, 79), (1, 71), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (9, 9), (10, 75), (11, 67), (12, 69), (13, 13), (14, 14), (15, 15), (16, 80), (22, 22), (39, 39), (50, 50), (51, 51)] 83⟩)))))))))))))))))))))))))))))))

def bytes_l100a80 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0x70, 0x01, 0x00,
    0x00, 0x4C, 0x8B, 0x5E, 0x10, 0x44, 0x8B, 0x67, 0x30, 0x0F, 0xB6, 0x4F, 0x40, 0x41, 0xBA, 0x40,
    0x00, 0x00, 0x00, 0x49, 0x29, 0xCA, 0x4C, 0x89, 0xD8, 0x4C, 0x29, 0xD0, 0x72, 0x22]

theorem code_l100a80 : ∀ x ∈ codeRange 0x100a80 bytes_l100a80, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xa80 46 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100aae : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100aae (movR32R32Effect 0x100aae 3 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12] []) (.reg (.gpr 2))) #v[12]
    (.letOp (n := 54) (.exec 0x100aae (fun s => s.RIP = 0x100aae) (movR32R32Effect 0x100aae 3 2 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 55) (.out 0x100ab1 (notR32Effect 0x100ab1 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[53]
    (.letOp (n := 56) (.exec 0x100ab1 (fun s => s.RIP = 0x100ab1) (notR32Effect 0x100ab1 2 2) (Reg.operands [.gpr 2] [])) #v[53]
    (.letOp (n := 57) (.out 0x100ab3 (movR64R64Effect 0x100ab3 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[0]
    (.letOp (n := 58) (.exec 0x100ab3 (fun s => s.RIP = 0x100ab3) (movR64R64Effect 0x100ab3 8 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 59) (.out 0x100ab6 (shrR64Effect 0x100ab6 4 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[57]
    (.letOp (n := 60) (.exec 0x100ab6 (fun s => s.RIP = 0x100ab6) (shrR64Effect 0x100ab6 4 8 6) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[57]
    (.letOp (n := 61) (.out 0x100aba (andR32Imm8Effect 0x100aba 3 0 0x3f) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 62) (.exec 0x100aba (fun s => s.RIP = 0x100aba) (andR32Imm8Effect 0x100aba 3 0 0x3f) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 63) (.out 0x100abd (cmpR64Imm8Effect 0x100abd 0 0x1) (EffectPart.reads (.flag .CF) [.gpr 0] []) (.flag .CF)) #v[61]
    (.letOp (n := 64) (.exec 0x100abd (fun s => s.RIP = 0x100abd) (cmpR64Imm8Effect 0x100abd 0 0x1) (Reg.operands [.gpr 0] [])) #v[61]
    (.letOp (n := 65) (.out 0x100ac1 (atFlags StatusFlags.CF (sbbR64Imm8Effect 0x100ac1 8 0xff)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[59, 63]
    (.letOp (n := 66) (.exec 0x100ac1 (fun s => s.RIP = 0x100ac1) (atFlags StatusFlags.CF (sbbR64Imm8Effect 0x100ac1 8 0xff)) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[59, 63]
    (.letOp (n := 67) (.out 0x100ac5 (movR8Imm8Effect 0x100ac5 2 0 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[61]
    (.letOp (n := 68) (.exec 0x100ac5 (fun s => s.RIP = 0x100ac5) (movR8Imm8Effect 0x100ac5 2 0 0x1) (Reg.operands [.gpr 0] [])) #v[61]
    (.letOp (n := 69) (.out 0x100ac7 (cmpR64R64Effect 0x100ac7 8 2) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 2] []) (.flag .CF)) #v[65, 55]
    (.letOp (n := 70) (.out 0x100ac7 (cmpR64R64Effect 0x100ac7 8 2) (EffectPart.reads (.flag .ZF) [.gpr 8, .gpr 2] []) (.flag .ZF)) #v[65, 55]
    (.letOp (n := 71) (.exec 0x100ac7 (fun s => s.RIP = 0x100ac7) (cmpR64R64Effect 0x100ac7 8 2) (Reg.operands [.gpr 8, .gpr 2] [])) #v[65, 55]
    (.letOp (n := 72) (.pure (condOp 7)) #v[69, 70]
    (.terminate (.condBr (Fin.last 72) ⟨.l1014aa, RegMap.args [(0, 67), (1, 1), (2, 55), (4, 4), (6, 6), (7, 7), (8, 65), (9, 9), (10, 10), (11, 11), (12, 12), (16, 69), (19, 70), (22, 22), (39, 39), (50, 50), (51, 51)] 73⟩ ⟨.l100ad0, RegMap.args [(0, 67), (1, 1), (2, 55), (4, 4), (6, 6), (7, 7), (8, 65), (9, 9), (10, 10), (11, 11), (12, 12), (16, 69), (19, 70), (22, 22), (39, 39), (50, 50), (51, 51)] 73⟩)))))))))))))))))))))

def bytes_l100aae : List UInt8 :=
  [0x44, 0x89, 0xE2, 0xF7, 0xD2, 0x49, 0x89, 0xC0, 0x49, 0xC1, 0xE8, 0x06, 0x83, 0xE0, 0x3F, 0x48,
    0x83, 0xF8, 0x01, 0x49, 0x83, 0xD8, 0xFF, 0xB0, 0x01, 0x49, 0x39, 0xD0, 0x0F, 0x87, 0xDA, 0x09,
    0x00, 0x00]

theorem code_l100aae : ∀ x ∈ codeRange 0x100aae bytes_l100aae, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xaae 34 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100ad0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100ad0 (cmpR64R64Effect 0x100ad0 11 10) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 10] []) (.flag .CF)) #v[11, 10]
    (.letOp (n := 54) (.exec 0x100ad0 (fun s => s.RIP = 0x100ad0) (cmpR64R64Effect 0x100ad0 11 10) (Reg.operands [.gpr 11, .gpr 10] [])) #v[11, 10]
    (.letOp (n := 55) (.out 0x100ad3 (atFlags (condHolds 2) (cmovR64R64Effect 0x100ad3 4 10 11)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[10, 11, 53]
    (.letOp (n := 56) (.exec 0x100ad3 (fun s => s.RIP = 0x100ad3) (atFlags (condHolds 2) (cmovR64R64Effect 0x100ad3 4 10 11)) (Reg.operands [.gpr 10, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[10, 11, 53]
    (.letOp (n := 57) (.out 0x100ad7 (leaR32Effect 0x100ad7 4 0 (.sib 10 (some 1) 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 1] []) (.reg (.gpr 0))) #v[55, 1]
    (.letOp (n := 58) (.exec 0x100ad7 (fun s => s.RIP = 0x100ad7) (leaR32Effect 0x100ad7 4 0 (.sib 10 (some 1) 0 .none)) (Reg.operands [.gpr 10, .gpr 1] [])) #v[55, 1]
    (.letOp (n := 59) (.exec 0x100adb (StorePre 0x100adb 3 (fun s => AddrMode.addr (.base 7 (.d8 0x40)) s (0x100adb + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x100adb 3 0 (.base 7 (.d8 0x40))) (Reg.operands [.gpr 0, .gpr 7] [])) #v[57, 7]
    (.letOp (n := 60) (.out 0x100ade (movR64M64Effect 0x100ade 3 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 6] []) (.reg (.gpr 3))) #v[6]
    (.letOp (n := 61) (.exec 0x100ade (LoadPre 0x100ade (fun s => AddrMode.addr (.base 6 .none) s (0x100ade + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x100ade 3 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 62) (.out 0x100ae1 (movR64M64Effect 0x100ae1 14 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 6] []) (.reg (.gpr 14))) #v[6]
    (.letOp (n := 63) (.exec 0x100ae1 (LoadPre 0x100ae1 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x100ae1 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x100ae1 14 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 64) (.out 0x100ae5 (subR64R64Effect 0x100ae5 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 10] []) (.reg (.gpr 11))) #v[11, 55]
    (.letOp (n := 65) (.exec 0x100ae5 (fun s => s.RIP = 0x100ae5) (subR64R64Effect 0x100ae5 11 10) (Reg.operands [.gpr 11, .gpr 10] [])) #v[11, 55]
    (.letOp (n := 66) (.out 0x100ae8 (movR64R64Effect 0x100ae8 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[64]
    (.letOp (n := 67) (.exec 0x100ae8 (fun s => s.RIP = 0x100ae8) (movR64R64Effect 0x100ae8 0 11) (Reg.operands [.gpr 11] [])) #v[64]
    (.letOp (n := 68) (.out 0x100aeb (shrR64Effect 0x100aeb 4 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[66]
    (.letOp (n := 69) (.exec 0x100aeb (fun s => s.RIP = 0x100aeb) (shrR64Effect 0x100aeb 4 0 6) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[66]
    (.letOp (n := 70) (.exec 0x100aef (StorePre 0x100aef 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x100aef + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100aef 0 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[68, 4]
    (.letOp (n := 71) (.out 0x100af4 (movR32R32Effect 0x100af4 3 15 11) (EffectPart.reads (.reg (.gpr 15)) [.gpr 11] []) (.reg (.gpr 15))) #v[64]
    (.letOp (n := 72) (.exec 0x100af4 (fun s => s.RIP = 0x100af4) (movR32R32Effect 0x100af4 3 15 11) (Reg.operands [.gpr 11] [])) #v[64]
    (.letOp (n := 73) (.out 0x100af7 (andR32Imm8Effect 0x100af7 4 15 0x3f) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15] []) (.reg (.gpr 15))) #v[71]
    (.letOp (n := 74) (.exec 0x100af7 (fun s => s.RIP = 0x100af7) (andR32Imm8Effect 0x100af7 4 15 0x3f) (Reg.operands [.gpr 15] [])) #v[71]
    (.letOp (n := 75) (.out 0x100afb (testR64R64Effect 0x100afb 10 10) (EffectPart.reads (.flag .ZF) [.gpr 10, .gpr 10] []) (.flag .ZF)) #v[55, 55]
    (.letOp (n := 76) (.exec 0x100afb (fun s => s.RIP = 0x100afb) (testR64R64Effect 0x100afb 10 10) (Reg.operands [.gpr 10, .gpr 10] [])) #v[55, 55]
    (.letOp (n := 77) (.pure (condOp 4)) #v[75]
    (.terminate (.condBr (Fin.last 77) ⟨.l100ba5, RegMap.args [(0, 68), (1, 1), (2, 2), (3, 60), (4, 4), (6, 6), (7, 7), (9, 9), (10, 55), (11, 64), (12, 12), (14, 62), (15, 73), (19, 75), (22, 22), (39, 39), (50, 50), (51, 51)] 78⟩ ⟨.l100b04, RegMap.args [(0, 68), (1, 1), (2, 2), (3, 60), (4, 4), (6, 6), (7, 7), (9, 9), (10, 55), (11, 64), (12, 12), (14, 62), (15, 73), (19, 75), (22, 22), (39, 39), (50, 50), (51, 51)] 78⟩))))))))))))))))))))))))))

def bytes_l100ad0 : List UInt8 :=
  [0x4D, 0x39, 0xD3, 0x4D, 0x0F, 0x42, 0xD3, 0x41, 0x8D, 0x04, 0x0A, 0x88, 0x47, 0x40, 0x48, 0x8B,
    0x1E, 0x4C, 0x8B, 0x76, 0x08, 0x4D, 0x29, 0xD3, 0x4C, 0x89, 0xD8, 0x48, 0xC1, 0xE8, 0x06, 0x48,
    0x89, 0x44, 0x24, 0x50, 0x45, 0x89, 0xDF, 0x41, 0x83, 0xE7, 0x3F, 0x4D, 0x85, 0xD2, 0x0F, 0x84,
    0xA1, 0x00, 0x00, 0x00]

theorem code_l100ad0 : ∀ x ∈ codeRange 0x100ad0 bytes_l100ad0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xad0 52 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100b04 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100b04 (movR32R32Effect 0x100b04 3 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[10]
    (.letOp (n := 54) (.exec 0x100b04 (fun s => s.RIP = 0x100b04) (movR32R32Effect 0x100b04 3 0 10) (Reg.operands [.gpr 10] [])) #v[10]
    (.letOp (n := 55) (.out 0x100b07 (andR32Imm8Effect 0x100b07 3 0 0x3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x100b07 (fun s => s.RIP = 0x100b07) (andR32Imm8Effect 0x100b07 3 0 0x3) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x100b0a (cmpR64Imm8Effect 0x100b0a 10 0x4) (EffectPart.reads (.flag .CF) [.gpr 10] []) (.flag .CF)) #v[10]
    (.letOp (n := 58) (.exec 0x100b0a (fun s => s.RIP = 0x100b0a) (cmpR64Imm8Effect 0x100b0a 10 0x4) (Reg.operands [.gpr 10] [])) #v[10]
    (.letOp (n := 59) (.pure (condOp 3)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l100b14, RegMap.args [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (16, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l100b10, RegMap.args [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (16, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l100b04 : List UInt8 :=
  [0x44, 0x89, 0xD0, 0x83, 0xE0, 0x03, 0x49, 0x83, 0xFA, 0x04, 0x73, 0x04]

theorem code_l100b04 : ∀ x ∈ codeRange 0x100b04 bytes_l100b04, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xb04 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100b10 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100b10 (xorR32R32Effect 0x100b10 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[2, 2]
    (.letOp (n := 54) (.exec 0x100b10 (fun s => s.RIP = 0x100b10) (xorR32R32Effect 0x100b10 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.terminate (.br ⟨.l100b7b, RegMap.args [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l100b10 : List UInt8 :=
  [0x31, 0xD2, 0xEB, 0x67]

theorem code_l100b10 : ∀ x ∈ codeRange 0x100b10 bytes_l100b10, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xb10 4 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100b14 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100b14 (movR32R32Effect 0x100b14 3 6 10) (EffectPart.reads (.reg (.gpr 6)) [.gpr 10] []) (.reg (.gpr 6))) #v[10]
    (.letOp (n := 54) (.exec 0x100b14 (fun s => s.RIP = 0x100b14) (movR32R32Effect 0x100b14 3 6 10) (Reg.operands [.gpr 10] [])) #v[10]
    (.letOp (n := 55) (.out 0x100b17 (andR32Imm8Effect 0x100b17 3 6 0x7c) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[53]
    (.letOp (n := 56) (.exec 0x100b17 (fun s => s.RIP = 0x100b17) (andR32Imm8Effect 0x100b17 3 6 0x7c) (Reg.operands [.gpr 6] [])) #v[53]
    (.letOp (n := 57) (.out 0x100b1a (leaR64Effect 0x100b1a 9 (.sib 1 (some 7) 0 .none)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 1, .gpr 7] []) (.reg (.gpr 9))) #v[1, 7]
    (.letOp (n := 58) (.exec 0x100b1a (fun s => s.RIP = 0x100b1a) (leaR64Effect 0x100b1a 9 (.sib 1 (some 7) 0 .none)) (Reg.operands [.gpr 1, .gpr 7] [])) #v[1, 7]
    (.letOp (n := 59) (.out 0x100b1e (addR64Imm8Effect 0x100b1e 9 0x43) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[57]
    (.letOp (n := 60) (.exec 0x100b1e (fun s => s.RIP = 0x100b1e) (addR64Imm8Effect 0x100b1e 9 0x43) (Reg.operands [.gpr 9] [])) #v[57]
    (.letOp (n := 61) (.out 0x100b22 (xorR32R32Effect 0x100b22 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[2, 2]
    (.letOp (n := 62) (.exec 0x100b22 (fun s => s.RIP = 0x100b22) (xorR32R32Effect 0x100b22 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 63) (.exec 0x100b24 (fun s => s.RIP = 0x100b24) (fun _ => nopEffect 0x100b24 12) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l100b30, RegMap.args [(0, 0), (1, 1), (2, 61), (3, 3), (4, 4), (6, 55), (7, 7), (9, 59), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩))))))))))))

def bytes_l100b14 : List UInt8 :=
  [0x44, 0x89, 0xD6, 0x83, 0xE6, 0x7C, 0x4C, 0x8D, 0x0C, 0x39, 0x49, 0x83, 0xC1, 0x43, 0x31, 0xD2,
    0x66, 0x66, 0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem code_l100b14 : ∀ x ∈ codeRange 0x100b14 bytes_l100b14, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xb14 28 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100b30 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100b30 (movzxR32M8Effect 0x100b30 6 8 (.sib 9 (some 2) 0 (.d8 0xfd))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 9, .gpr 2] []) (.reg (.gpr 8))) #v[9, 2]
    (.letOp (n := 54) (.exec 0x100b30 (LoadPre 0x100b30 (fun s => AddrMode.addr (.sib 9 (some 2) 0 (.d8 0xfd)) s (0x100b30 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x100b30 6 8 (.sib 9 (some 2) 0 (.d8 0xfd))) (Reg.operands [.gpr 9, .gpr 2] [])) #v[9, 2]
    (.letOp (n := 55) (.out 0x100b36 (xorR8M8Effect 0x100b36 4 8 (.sib 3 (some 2) 0 .none)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 3, .gpr 2] []) (.reg (.gpr 8))) #v[53, 3, 2]
    (.letOp (n := 56) (.exec 0x100b36 (LoadPre 0x100b36 (fun s => AddrMode.addr (.sib 3 (some 2) 0 .none) s (0x100b36 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x100b36 4 8 (.sib 3 (some 2) 0 .none)) (Reg.operands [.gpr 8, .gpr 3, .gpr 2] [])) #v[53, 3, 2]
    (.letOp (n := 57) (.exec 0x100b3a (StorePre 0x100b3a 4 (fun s => AddrMode.addr (.sib 14 (some 2) 0 .none) s (0x100b3a + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x100b3a 4 8 (.sib 14 (some 2) 0 .none)) (Reg.operands [.gpr 8, .gpr 14, .gpr 2] [])) #v[55, 14, 2]
    (.letOp (n := 58) (.out 0x100b3e (movzxR32M8Effect 0x100b3e 6 8 (.sib 9 (some 2) 0 (.d8 0xfe))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 9, .gpr 2] []) (.reg (.gpr 8))) #v[9, 2]
    (.letOp (n := 59) (.exec 0x100b3e (LoadPre 0x100b3e (fun s => AddrMode.addr (.sib 9 (some 2) 0 (.d8 0xfe)) s (0x100b3e + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x100b3e 6 8 (.sib 9 (some 2) 0 (.d8 0xfe))) (Reg.operands [.gpr 9, .gpr 2] [])) #v[9, 2]
    (.letOp (n := 60) (.out 0x100b44 (xorR8M8Effect 0x100b44 5 8 (.sib 3 (some 2) 0 (.d8 0x1))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 3, .gpr 2] []) (.reg (.gpr 8))) #v[58, 3, 2]
    (.letOp (n := 61) (.exec 0x100b44 (LoadPre 0x100b44 (fun s => AddrMode.addr (.sib 3 (some 2) 0 (.d8 0x1)) s (0x100b44 + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x100b44 5 8 (.sib 3 (some 2) 0 (.d8 0x1))) (Reg.operands [.gpr 8, .gpr 3, .gpr 2] [])) #v[58, 3, 2]
    (.letOp (n := 62) (.exec 0x100b49 (StorePre 0x100b49 5 (fun s => AddrMode.addr (.sib 14 (some 2) 0 (.d8 0x1)) s (0x100b49 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x100b49 5 8 (.sib 14 (some 2) 0 (.d8 0x1))) (Reg.operands [.gpr 8, .gpr 14, .gpr 2] [])) #v[60, 14, 2]
    (.letOp (n := 63) (.out 0x100b4e (movzxR32M8Effect 0x100b4e 6 8 (.sib 9 (some 2) 0 (.d8 0xff))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 9, .gpr 2] []) (.reg (.gpr 8))) #v[9, 2]
    (.letOp (n := 64) (.exec 0x100b4e (LoadPre 0x100b4e (fun s => AddrMode.addr (.sib 9 (some 2) 0 (.d8 0xff)) s (0x100b4e + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x100b4e 6 8 (.sib 9 (some 2) 0 (.d8 0xff))) (Reg.operands [.gpr 9, .gpr 2] [])) #v[9, 2]
    (.letOp (n := 65) (.out 0x100b54 (xorR8M8Effect 0x100b54 5 8 (.sib 3 (some 2) 0 (.d8 0x2))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 3, .gpr 2] []) (.reg (.gpr 8))) #v[63, 3, 2]
    (.letOp (n := 66) (.exec 0x100b54 (LoadPre 0x100b54 (fun s => AddrMode.addr (.sib 3 (some 2) 0 (.d8 0x2)) s (0x100b54 + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x100b54 5 8 (.sib 3 (some 2) 0 (.d8 0x2))) (Reg.operands [.gpr 8, .gpr 3, .gpr 2] [])) #v[63, 3, 2]
    (.letOp (n := 67) (.exec 0x100b59 (StorePre 0x100b59 5 (fun s => AddrMode.addr (.sib 14 (some 2) 0 (.d8 0x2)) s (0x100b59 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x100b59 5 8 (.sib 14 (some 2) 0 (.d8 0x2))) (Reg.operands [.gpr 8, .gpr 14, .gpr 2] [])) #v[65, 14, 2]
    (.letOp (n := 68) (.out 0x100b5e (movzxR32M8Effect 0x100b5e 5 8 (.sib 9 (some 2) 0 .none)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 9, .gpr 2] []) (.reg (.gpr 8))) #v[9, 2]
    (.letOp (n := 69) (.exec 0x100b5e (LoadPre 0x100b5e (fun s => AddrMode.addr (.sib 9 (some 2) 0 .none) s (0x100b5e + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x100b5e 5 8 (.sib 9 (some 2) 0 .none)) (Reg.operands [.gpr 9, .gpr 2] [])) #v[9, 2]
    (.letOp (n := 70) (.out 0x100b63 (xorR8M8Effect 0x100b63 5 8 (.sib 3 (some 2) 0 (.d8 0x3))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 3, .gpr 2] []) (.reg (.gpr 8))) #v[68, 3, 2]
    (.letOp (n := 71) (.exec 0x100b63 (LoadPre 0x100b63 (fun s => AddrMode.addr (.sib 3 (some 2) 0 (.d8 0x3)) s (0x100b63 + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x100b63 5 8 (.sib 3 (some 2) 0 (.d8 0x3))) (Reg.operands [.gpr 8, .gpr 3, .gpr 2] [])) #v[68, 3, 2]
    (.letOp (n := 72) (.exec 0x100b68 (StorePre 0x100b68 5 (fun s => AddrMode.addr (.sib 14 (some 2) 0 (.d8 0x3)) s (0x100b68 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x100b68 5 8 (.sib 14 (some 2) 0 (.d8 0x3))) (Reg.operands [.gpr 8, .gpr 14, .gpr 2] [])) #v[70, 14, 2]
    (.letOp (n := 73) (.out 0x100b6d (addR64Imm8Effect 0x100b6d 2 0x4) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[2]
    (.letOp (n := 74) (.exec 0x100b6d (fun s => s.RIP = 0x100b6d) (addR64Imm8Effect 0x100b6d 2 0x4) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 75) (.out 0x100b71 (cmpR64R64Effect 0x100b71 6 2) (EffectPart.reads (.flag .ZF) [.gpr 6, .gpr 2] []) (.flag .ZF)) #v[6, 73]
    (.letOp (n := 76) (.exec 0x100b71 (fun s => s.RIP = 0x100b71) (cmpR64R64Effect 0x100b71 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[6, 73]
    (.letOp (n := 77) (.pure (condOp 5)) #v[75]
    (.terminate (.condBr (Fin.last 77) ⟨.l100b30, RegMap.args [(0, 0), (1, 1), (2, 73), (3, 3), (4, 4), (6, 6), (7, 7), (8, 70), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 75), (22, 22), (39, 39), (50, 50), (51, 51)] 78⟩ ⟨.l100b76, RegMap.args [(0, 0), (1, 1), (2, 73), (3, 3), (4, 4), (6, 6), (7, 7), (8, 70), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 75), (22, 22), (39, 39), (50, 50), (51, 51)] 78⟩))))))))))))))))))))))))))

def bytes_l100b30 : List UInt8 :=
  [0x45, 0x0F, 0xB6, 0x44, 0x11, 0xFD, 0x44, 0x32, 0x04, 0x13, 0x45, 0x88, 0x04, 0x16, 0x45, 0x0F,
    0xB6, 0x44, 0x11, 0xFE, 0x44, 0x32, 0x44, 0x13, 0x01, 0x45, 0x88, 0x44, 0x16, 0x01, 0x45, 0x0F,
    0xB6, 0x44, 0x11, 0xFF, 0x44, 0x32, 0x44, 0x13, 0x02, 0x45, 0x88, 0x44, 0x16, 0x02, 0x45, 0x0F,
    0xB6, 0x04, 0x11, 0x44, 0x32, 0x44, 0x13, 0x03, 0x45, 0x88, 0x44, 0x16, 0x03, 0x48, 0x83, 0xC2,
    0x04, 0x48, 0x39, 0xD6, 0x75, 0xBA]

theorem code_l100b30 : ∀ x ∈ codeRange 0x100b30 bytes_l100b30, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xb30 70 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100b76 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100b76 (testR64R64Effect 0x100b76 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[0, 0]
    (.letOp (n := 54) (.exec 0x100b76 (fun s => s.RIP = 0x100b76) (testR64R64Effect 0x100b76 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l100ba5, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l100b7b, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l100b76 : List UInt8 :=
  [0x48, 0x85, 0xC0, 0x74, 0x2A]

theorem code_l100b76 : ∀ x ∈ codeRange 0x100b76 bytes_l100b76, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xb76 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

end ChaCha20Poly1305.Proofs.Decrypt.Lifted
