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

@[cfg_block] def b_l1249f2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1249f2 (movR64M64Effect 0x1249f2 7 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x1249f2 (LoadPre 0x1249f2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1249f2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1249f2 7 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x1249f7 (StorePre 0x1249f7 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x1249f7 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1249f7 7 (.base 3 (.d8 0x30))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[53, 3]
    (.letOp (n := 56) (.out 0x1249fb (movR64M64Effect 0x1249fb 7 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 57) (.exec 0x1249fb (LoadPre 0x1249fb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1249fb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1249fb 7 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x124a00 (StorePre 0x124a00 4 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x124a00 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124a00 7 (.base 3 (.d8 0x28))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[56, 3]
    (.letOp (n := 59) (.out 0x124a04 (movR64M64Effect 0x124a04 7 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 60) (.exec 0x124a04 (LoadPre 0x124a04 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x124a04 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124a04 7 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x124a09 (movR64M64Effect 0x124a09 8 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 62) (.exec 0x124a09 (LoadPre 0x124a09 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x124a09 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124a09 8 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x124a0e (StorePre 0x124a0e 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x124a0e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124a0e 8 (.base 3 (.d8 0x20))) (Reg.operands [.gpr 8, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 64) (.exec 0x124a12 (StorePre 0x124a12 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x124a12 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124a12 7 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[59, 3]
    (.letOp (n := 65) (.exec 0x124a16 (StorePre 0x124a16 2 (fun s => AddrMode.addr (.base 3 .none) s (0x124a16 + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x124a16 1 (.base 3 .none)) (Reg.operands [.gpr 1, .gpr 3] [])) #v[1, 3]
    (.letOp (n := 66) (.exec 0x124a18 (StorePre 0x124a18 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x124a18 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x124a18 0 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (.letOp (n := 67) (.exec 0x124a1b (StorePre 0x124a1b 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x124a1b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124a1b 2 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[2, 3]
    (.letOp (n := 68) (.exec 0x124a1f (StorePre 0x124a1f 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x124a1f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124a1f 6 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[6, 3]
    (.terminate (.br ⟨.l124a23, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 59), (8, 61), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)] 69⟩)))))))))))))))))

def bytes_l1249f2 : List UInt8 :=
  [0x48, 0x8B, 0x7C, 0x24, 0x58, 0x48, 0x89, 0x7B, 0x30, 0x48, 0x8B, 0x7C, 0x24, 0x50, 0x48, 0x89,
    0x7B, 0x28, 0x48, 0x8B, 0x7C, 0x24, 0x40, 0x4C, 0x8B, 0x44, 0x24, 0x48, 0x4C, 0x89, 0x43, 0x20,
    0x48, 0x89, 0x7B, 0x18, 0x89, 0x0B, 0x89, 0x43, 0x04, 0x48, 0x89, 0x53, 0x08, 0x48, 0x89, 0x73,
    0x10]

theorem code_l1249f2 : ∀ x ∈ codeRange 0x1249f2 bytes_l1249f2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x249f2 49 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124a23 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124a23 (movR64R64Effect 0x124a23 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 54) (.exec 0x124a23 (fun s => s.RIP = 0x124a23) (movR64R64Effect 0x124a23 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x124a26 (addR64Imm32Effect 0x124a26 4 0x98) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 56) (.exec 0x124a26 (fun s => s.RIP = 0x124a26) (addR64Imm32Effect 0x124a26 4 0x98) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x124a2d (popR64Effect 0x124a2d 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[55]
    (.letOp (n := 58) (.out 0x124a2d (popR64Effect 0x124a2d 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[55]
    (.letOp (n := 59) (.exec 0x124a2d (PopPre 0x124a2d) (popR64Effect 0x124a2d 1 3) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 60) (.out 0x124a2e (popR64Effect 0x124a2e 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[58]
    (.letOp (n := 61) (.out 0x124a2e (popR64Effect 0x124a2e 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[58]
    (.letOp (n := 62) (.exec 0x124a2e (PopPre 0x124a2e) (popR64Effect 0x124a2e 2 12) (Reg.operands [.gpr 4] [])) #v[58]
    (.letOp (n := 63) (.out 0x124a30 (popR64Effect 0x124a30 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[61]
    (.letOp (n := 64) (.out 0x124a30 (popR64Effect 0x124a30 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 65) (.exec 0x124a30 (PopPre 0x124a30) (popR64Effect 0x124a30 2 14) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 66) (.out 0x124a32 (popR64Effect 0x124a32 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[64]
    (.letOp (n := 67) (.out 0x124a32 (popR64Effect 0x124a32 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[64]
    (.letOp (n := 68) (.exec 0x124a32 (PopPre 0x124a32) (popR64Effect 0x124a32 2 15) (Reg.operands [.gpr 4] [])) #v[64]
    (.letOp (n := 69) (.out 0x124a34 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[67]
    (.letOp (n := 70) (.out 0x124a34 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[67]
    (.letOp (n := 71) (.exec 0x124a34 (RetPre 0x124a34) (retEffect) (Reg.operands [.gpr 4] [])) #v[67]
    (.terminate (.ret (RegMap.args [(0, 53), (1, 1), (2, 2), (3, 57), (4, 70), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 13), (14, 63), (15, 66), (22, 22), (39, 39), (50, 50), (51, 51)] 72) (some ⟨69, by decide⟩)))))))))))))))))))))

def bytes_l124a23 : List UInt8 :=
  [0x48, 0x89, 0xD8, 0x48, 0x81, 0xC4, 0x98, 0x00, 0x00, 0x00, 0x5B, 0x41, 0x5C, 0x41, 0x5E, 0x41,
    0x5F, 0xC3]

theorem code_l124a23 : ∀ x ∈ codeRange 0x124a23 bytes_l124a23, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24a23 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124a35 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x124a35 (StorePre 0x124a35 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x27)) s (0x124a35 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x124a35 (.sib 4 none 0 (.d8 0x27)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.exec 0x124a3e (StorePre 0x124a3e 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x124a3e + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x124a3e (.sib 4 none 0 (.d8 0x20)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x124a47 (StorePre 0x124a47 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x124a47 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x124a47 (.sib 4 none 0 (.d8 0x18)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.exec 0x124a50 (StorePre 0x124a50 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x124a50 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x124a50 (.sib 4 none 0 (.d8 0x10)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x124a59 (StorePre 0x124a59 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x124a59 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x124a59 (.sib 4 none 0 (.d8 0x8)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.out 0x124a62 (leaR64Effect 0x124a62 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 59) (.exec 0x124a62 (fun s => s.RIP = 0x124a62) (leaR64Effect 0x124a62 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.out 0x124a67 (movR64R64Effect 0x124a67 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14] []) (.reg (.gpr 2))) #v[14]
    (.letOp (n := 61) (.exec 0x124a67 (fun s => s.RIP = 0x124a67) (movR64R64Effect 0x124a67 2 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 62) (.out 0x124a6a (callEffect (callMemPtr 0x124a6a (.rip 0xdf360)) (0x124a6a + BitVec.ofNat 64 (callMemLen (.rip 0xdf360)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 63) (.exec 0x124a6a (GoesTo (CallMemPre 0x124a6a (.rip 0xdf360)) (callEffect (callMemPtr 0x124a6a (.rip 0xdf360)) (0x124a6a + BitVec.ofNat 64 (callMemLen (.rip 0xdf360)))) 0x12a820) (callEffect (callMemPtr 0x124a6a (.rip 0xdf360)) (0x124a6a + BitVec.ofNat 64 (callMemLen (.rip 0xdf360)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.const ⟨64, 0x124a70⟩) #v[]
    (.terminate (.call ⟨.l12a820, RegMap.args [(2, 60), (3, 3), (4, 62), (5, 5), (6, 6), (7, 58), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 65⟩ { target := .l124a70, kept := #v[], arity := rfl, guard := some (Fin.last 64) })))))))))))))

def bytes_l124a35 : List UInt8 :=
  [0x48, 0xC7, 0x44, 0x24, 0x27, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x20, 0x00, 0x00,
    0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x18, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x10,
    0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x7C,
    0x24, 0x08, 0x4C, 0x89, 0xF2, 0xFF, 0x15, 0x60, 0xF3, 0x0D, 0x00]

theorem code_l124a35 : ∀ x ∈ codeRange 0x124a35 bytes_l124a35, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24a35 59 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124a70_1 : Block Op Label signature Reg.count 84 :=
  .letOp (n := 84) (.exec 0x124ac4 (StorePre 0x124ac4 6 (fun s => AddrMode.addr (.base 3 .none) s (0x124ac4 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x124ac4 6 (.base 3 .none) 0x2) (Reg.operands [.gpr 3] [])) #v[3]
    (.terminate (.br ⟨.l124a23, RegMap.args [(0, 76), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 59), (7, 62), (8, 65), (9, 70), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)] 85⟩))

def bytes_l124a70_1 : List UInt8 :=
  [0xC7, 0x03, 0x02, 0x00, 0x00, 0x00, 0xE9, 0x54, 0xFF, 0xFF, 0xFF]

theorem code_l124a70_1 : ∀ x ∈ codeRange 0x124ac4 bytes_l124a70_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24ac4 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124a70 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124a70 (movzxR32M16Effect 0x124a70 5 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x124a70 (LoadPre 0x124a70 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x124a70 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x124a70 5 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x124a75 (movR64M64Effect 0x124a75 1 (.sib 4 none 0 (.d8 0xb))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x124a75 (LoadPre 0x124a75 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xb)) s (0x124a75 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124a75 1 (.sib 4 none 0 (.d8 0xb))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x124a7a (movR64M64Effect 0x124a7a 2 (.sib 4 none 0 (.d8 0x13))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 58) (.exec 0x124a7a (LoadPre 0x124a7a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x13)) s (0x124a7a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124a7a 2 (.sib 4 none 0 (.d8 0x13))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x124a7f (movR32M32LowEffect 0x124a7f 6 (.sib 4 none 0 (.d8 0x2b))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 60) (.exec 0x124a7f (LoadPre 0x124a7f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2b)) s (0x124a7f + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x124a7f 6 (.sib 4 none 0 (.d8 0x2b))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x124a83 (StorePre 0x124a83 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x124a83 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x124a83 6 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x124a87 (movR64M64Effect 0x124a87 7 (.sib 4 none 0 (.d8 0x23))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 63) (.exec 0x124a87 (LoadPre 0x124a87 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x23)) s (0x124a87 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124a87 7 (.sib 4 none 0 (.d8 0x23))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x124a8c (StorePre 0x124a8c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x124a8c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x124a8c 7 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x124a91 (movR64M64Effect 0x124a91 8 (.sib 4 none 0 (.d8 0x1b))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 66) (.exec 0x124a91 (LoadPre 0x124a91 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1b)) s (0x124a91 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124a91 8 (.sib 4 none 0 (.d8 0x1b))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x124a96 (StorePre 0x124a96 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x124a96 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x124a96 8 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x124a9b (movzxR32M8Effect 0x124a9b 6 9 (.sib 4 none 0 (.d8 0xa))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 69) (.exec 0x124a9b (LoadPre 0x124a9b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xa)) s (0x124a9b + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x124a9b 6 9 (.sib 4 none 0 (.d8 0xa))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.out 0x124aa1 (shlR32Effect 0x124aa1 4 9 24) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[68]
    (.letOp (n := 71) (.exec 0x124aa1 (fun s => s.RIP = 0x124aa1) (shlR32Effect 0x124aa1 4 9 24) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[68]
    (.letOp (n := 72) (.out 0x124aa5 (shlR32Effect 0x124aa5 3 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 73) (.exec 0x124aa5 (fun s => s.RIP = 0x124aa5) (shlR32Effect 0x124aa5 3 0 8) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 74) (.out 0x124aa8 (orR32R32Effect 0x124aa8 3 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[72, 14]
    (.letOp (n := 75) (.exec 0x124aa8 (fun s => s.RIP = 0x124aa8) (orR32R32Effect 0x124aa8 3 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[72, 14]
    (.letOp (n := 76) (.out 0x124aab (orR32R32Effect 0x124aab 3 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[74, 70]
    (.letOp (n := 77) (.exec 0x124aab (fun s => s.RIP = 0x124aab) (orR32R32Effect 0x124aab 3 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[74, 70]
    (.letOp (n := 78) (.exec 0x124aae (StorePre 0x124aae 3 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x124aae + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x124aae 6 (.base 3 (.d8 0x28))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[59, 3]
    (.letOp (n := 79) (.exec 0x124ab1 (StorePre 0x124ab1 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x124ab1 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124ab1 7 (.base 3 (.d8 0x20))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[62, 3]
    (.letOp (n := 80) (.exec 0x124ab5 (StorePre 0x124ab5 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x124ab5 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124ab5 8 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 8, .gpr 3] [])) #v[65, 3]
    (.letOp (n := 81) (.exec 0x124ab9 (StorePre 0x124ab9 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x124ab9 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x124ab9 0 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[76, 3]
    (.letOp (n := 82) (.exec 0x124abc (StorePre 0x124abc 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x124abc + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124abc 1 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[55, 3]
    (.letOp (n := 83) (.exec 0x124ac0 (StorePre 0x124ac0 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x124ac0 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124ac0 2 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[57, 3]
    (b_l124a70_1)))))))))))))))))))))))))))))))

def bytes_l124a70 : List UInt8 :=
  [0x0F, 0xB7, 0x44, 0x24, 0x08, 0x48, 0x8B, 0x4C, 0x24, 0x0B, 0x48, 0x8B, 0x54, 0x24, 0x13, 0x8B,
    0x74, 0x24, 0x2B, 0x89, 0x74, 0x24, 0x50, 0x48, 0x8B, 0x7C, 0x24, 0x23, 0x48, 0x89, 0x7C, 0x24,
    0x48, 0x4C, 0x8B, 0x44, 0x24, 0x1B, 0x4C, 0x89, 0x44, 0x24, 0x40, 0x44, 0x0F, 0xB6, 0x4C, 0x24,
    0x0A, 0x41, 0xC1, 0xE1, 0x18, 0xC1, 0xE0, 0x08, 0x44, 0x09, 0xF0, 0x44, 0x09, 0xC8, 0x89, 0x73,
    0x28, 0x48, 0x89, 0x7B, 0x20, 0x4C, 0x89, 0x43, 0x18, 0x89, 0x43, 0x04, 0x48, 0x89, 0x4B, 0x08,
    0x48, 0x89, 0x53, 0x10] ++ bytes_l124a70_1

theorem code_l124a70 : ∀ x ∈ codeRange 0x124a70 bytes_l124a70, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x24a70 84 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l124a70_1

@[cfg_block] def b_l124acf : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124acf (movR64R64Effect 0x124acf 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 54) (.exec 0x124acf (fun s => s.RIP = 0x124acf) (movR64R64Effect 0x124acf 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 55) (.out 0x124ad2 (movR64Imm32Effect 0x124ad2 2 0x2036e0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 56) (.exec 0x124ad2 (fun s => s.RIP = 0x124ad2) (movR64Imm32Effect 0x124ad2 2 0x2036e0) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x124ad9 (callEffect (fun _ => 0x129c90) 0x124ade) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x124ad9 (PushPre 0x124ad9 5) (callEffect (fun _ => 0x129c90) 0x124ade) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x124ade⟩) #v[]
    (.terminate (.call ⟨.l129c90, RegMap.args [(2, 55), (4, 57), (5, 5), (6, 6), (7, 53), (14, 14)] 60⟩ { target := .l124ade, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l124acf : List UInt8 :=
  [0x4C, 0x89, 0xF7, 0x48, 0xC7, 0xC2, 0xE0, 0x36, 0x20, 0x00, 0xE8, 0xB2, 0x51, 0x00, 0x00]

theorem code_l124acf : ∀ x ∈ codeRange 0x124acf bytes_l124acf, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24acf 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124ade : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x124ade (fun s => s.RIP = 0x124ade) (fun _ => nopEffect 0x124ade 2) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l124ae0, RegMap.args [(3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 54⟩))

def bytes_l124ade : List UInt8 :=
  [0x66, 0x90]

theorem code_l124ade : ∀ x ∈ codeRange 0x124ade bytes_l124ade, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24ade 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124ae0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124ae0 (pushR64Effect 0x124ae0 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[4, 14]
    (.letOp (n := 54) (.exec 0x124ae0 (PushPre 0x124ae0 2) (pushR64Effect 0x124ae0 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[4, 14]
    (.letOp (n := 55) (.out 0x124ae2 (pushR64Effect 0x124ae2 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[53, 3]
    (.letOp (n := 56) (.exec 0x124ae2 (PushPre 0x124ae2 1) (pushR64Effect 0x124ae2 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[53, 3]
    (.letOp (n := 57) (.out 0x124ae3 (subR64Imm8Effect 0x124ae3 4 0x58) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[55]
    (.letOp (n := 58) (.exec 0x124ae3 (fun s => s.RIP = 0x124ae3) (subR64Imm8Effect 0x124ae3 4 0x58) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 59) (.out 0x124ae7 (movR64R64Effect 0x124ae7 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 6] []) (.reg (.gpr 14))) #v[6]
    (.letOp (n := 60) (.exec 0x124ae7 (fun s => s.RIP = 0x124ae7) (movR64R64Effect 0x124ae7 14 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 61) (.out 0x124aea (movR64R64Effect 0x124aea 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 62) (.exec 0x124aea (fun s => s.RIP = 0x124aea) (movR64R64Effect 0x124aea 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 63) (.out 0x124aed (leaR64Effect 0x124aed 7 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[57]
    (.letOp (n := 64) (.exec 0x124aed (fun s => s.RIP = 0x124aed) (leaR64Effect 0x124aed 7 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[57]
    (.letOp (n := 65) (.out 0x124af2 (callEffect (fun _ => 0x125450) 0x124af7) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[57]
    (.letOp (n := 66) (.exec 0x124af2 (PushPre 0x124af2 5) (callEffect (fun _ => 0x125450) 0x124af7) (Reg.operands [.gpr 4] [])) #v[57]
    (.letOp (n := 67) (.const ⟨64, 0x124af7⟩) #v[]
    (.terminate (.call ⟨.l125450, RegMap.args [(3, 61), (4, 65), (5, 5), (6, 6), (7, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 59), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 68⟩ { target := .l124af7, kept := #v[], arity := rfl, guard := some (Fin.last 67) }))))))))))))))))

def bytes_l124ae0 : List UInt8 :=
  [0x41, 0x56, 0x53, 0x48, 0x83, 0xEC, 0x58, 0x49, 0x89, 0xF6, 0x48, 0x89, 0xFB, 0x48, 0x8D, 0x7C,
    0x24, 0x10, 0xE8, 0x59, 0x09, 0x00, 0x00]

theorem code_l124ae0 : ∀ x ∈ codeRange 0x124ae0 bytes_l124ae0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24ae0 23 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124af7 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124af7 (movR32M32LowEffect 0x124af7 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x124af7 (LoadPre 0x124af7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x124af7 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x124af7 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x124afb (movR64M64Effect 0x124afb 1 (.sib 4 none 0 (.d8 0x14))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x124afb (LoadPre 0x124afb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x124afb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124afb 1 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x124b00 (StorePre 0x124b00 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x124b00 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124b00 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 1, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 58) (.out 0x124b04 (movR64M64Effect 0x124b04 1 (.sib 4 none 0 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 59) (.exec 0x124b04 (LoadPre 0x124b04 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x124b04 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124b04 1 (.sib 4 none 0 (.d8 0x1c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.exec 0x124b09 (StorePre 0x124b09 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x124b09 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x124b09 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[58, 4]
    (.letOp (n := 61) (.out 0x124b0e (cmpR32Imm8Effect 0x124b0e 3 0 0x2) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[53]
    (.letOp (n := 62) (.exec 0x124b0e (fun s => s.RIP = 0x124b0e) (cmpR32Imm8Effect 0x124b0e 3 0 0x2) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 63) (.pure (condOp 5)) #v[61]
    (.terminate (.condBr (Fin.last 63) ⟨.l124b50, RegMap.args [(0, 53), (1, 58), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 61), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ ⟨.l124b13, RegMap.args [(0, 53), (1, 58), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 61), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩))))))))))))

def bytes_l124af7 : List UInt8 :=
  [0x8B, 0x44, 0x24, 0x10, 0x48, 0x8B, 0x4C, 0x24, 0x14, 0x48, 0x89, 0x0C, 0x24, 0x48, 0x8B, 0x4C,
    0x24, 0x1C, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x83, 0xF8, 0x02, 0x75, 0x3D]

theorem code_l124af7 : ∀ x ∈ codeRange 0x124af7 bytes_l124af7, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24af7 28 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124b13 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124b13 (movR64M64Effect 0x124b13 6 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 54) (.exec 0x124b13 (LoadPre 0x124b13 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x124b13 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x124b13 6 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x124b17 (movR64M64Effect 0x124b17 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 56) (.exec 0x124b17 (LoadPre 0x124b17 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x124b17 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124b17 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x124b1c (StorePre 0x124b1c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x124b1c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x124b1c 6 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 58) (.exec 0x124b21 (StorePre 0x124b21 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x124b21 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x124b21 0 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 59) (.out 0x124b26 (leaR64Effect 0x124b26 7 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 60) (.exec 0x124b26 (fun s => s.RIP = 0x124b26) (leaR64Effect 0x124b26 7 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x124b2b (movR32Imm32Effect 0x124b2b 5 2 0x5) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 62) (.exec 0x124b2b (fun s => s.RIP = 0x124b2b) (movR32Imm32Effect 0x124b2b 5 2 0x5) (Reg.operands [] [])) #v[]
    (.letOp (n := 63) (.out 0x124b30 (callEffect (fun _ => 0x1276d0) 0x124b35) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 64) (.exec 0x124b30 (PushPre 0x124b30 5) (callEffect (fun _ => 0x1276d0) 0x124b35) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.const ⟨64, 0x124b35⟩) #v[]
    (.terminate (.call ⟨.l1276d0, RegMap.args [(0, 55), (1, 1), (2, 61), (3, 3), (4, 63), (5, 5), (6, 53), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩ { target := .l124b35, kept := #v[], arity := rfl, guard := some (Fin.last 65) }))))))))))))))

def bytes_l124b13 : List UInt8 :=
  [0x48, 0x8B, 0x34, 0x24, 0x48, 0x8B, 0x44, 0x24, 0x08, 0x48, 0x89, 0x74, 0x24, 0x48, 0x48, 0x89,
    0x44, 0x24, 0x50, 0x48, 0x8D, 0x7C, 0x24, 0x10, 0xBA, 0x05, 0x00, 0x00, 0x00, 0xE8, 0x9B, 0x2B,
    0x00, 0x00]

theorem code_l124b13 : ∀ x ∈ codeRange 0x124b13 bytes_l124b13, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24b13 34 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124b35 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124b35 (movR32M32LowEffect 0x124b35 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x124b35 (LoadPre 0x124b35 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x124b35 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x124b35 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x124b39 (cmpR32Imm8Effect 0x124b39 3 0 0x2) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x124b39 (fun s => s.RIP = 0x124b39) (cmpR32Imm8Effect 0x124b39 3 0 0x2) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l124b90, RegMap.args [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l124b3e, RegMap.args [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l124b35 : List UInt8 :=
  [0x8B, 0x44, 0x24, 0x10, 0x83, 0xF8, 0x02, 0x75, 0x52]

theorem code_l124b35 : ∀ x ∈ codeRange 0x124b35 bytes_l124b35, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24b35 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124b3e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124b3e (leaR64Effect 0x124b3e 2 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 54) (.exec 0x124b3e (fun s => s.RIP = 0x124b3e) (leaR64Effect 0x124b3e 2 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x124b43 (movR64R64Effect 0x124b43 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 56) (.exec 0x124b43 (fun s => s.RIP = 0x124b43) (movR64R64Effect 0x124b43 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 57) (.out 0x124b46 (movR64R64Effect 0x124b46 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 58) (.exec 0x124b46 (fun s => s.RIP = 0x124b46) (movR64R64Effect 0x124b46 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 59) (.out 0x124b49 (callEffect (fun _ => 0x1267c0) 0x124b4e) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x124b49 (PushPre 0x124b49 5) (callEffect (fun _ => 0x1267c0) 0x124b4e) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x124b4e⟩) #v[]
    (.terminate (.call ⟨.l1267c0, RegMap.args [(1, 1), (2, 53), (3, 3), (4, 59), (5, 5), (6, 57), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l124b4e, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l124b3e : List UInt8 :=
  [0x48, 0x8D, 0x54, 0x24, 0x48, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x72, 0x1C, 0x00, 0x00]

theorem code_l124b3e : ∀ x ∈ codeRange 0x124b3e bytes_l124b3e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24b3e 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124b4e : Block Op Label signature Reg.count 53 :=
  .terminate (.br ⟨.l124bcf, RegMap.args (entryMap (live .l124b4e)) 53⟩)

def bytes_l124b4e : List UInt8 :=
  [0xEB, 0x7F]

theorem code_l124b4e : ∀ x ∈ codeRange 0x124b4e bytes_l124b4e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24b4e 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124b50 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124b50 (movR32M32LowEffect 0x124b50 1 (.sib 4 none 0 (.d8 0x44))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x124b50 (LoadPre 0x124b50 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x124b50 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x124b50 1 (.sib 4 none 0 (.d8 0x44))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x124b54 (StorePre 0x124b54 3 (fun s => AddrMode.addr (.base 3 (.d8 0x34)) s (0x124b54 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x124b54 1 (.base 3 (.d8 0x34))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[53, 3]
    (.letOp (n := 56) (.out 0x124b57 (movR64M64Effect 0x124b57 1 (.sib 4 none 0 (.d8 0x3c))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 57) (.exec 0x124b57 (LoadPre 0x124b57 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x124b57 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124b57 1 (.sib 4 none 0 (.d8 0x3c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x124b5c (StorePre 0x124b5c 4 (fun s => AddrMode.addr (.base 3 (.d8 0x2c)) s (0x124b5c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124b5c 1 (.base 3 (.d8 0x2c))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[56, 3]
    (.letOp (n := 59) (.out 0x124b60 (movR64M64Effect 0x124b60 1 (.sib 4 none 0 (.d8 0x34))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 60) (.exec 0x124b60 (LoadPre 0x124b60 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x124b60 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124b60 1 (.sib 4 none 0 (.d8 0x34))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x124b65 (StorePre 0x124b65 4 (fun s => AddrMode.addr (.base 3 (.d8 0x24)) s (0x124b65 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124b65 1 (.base 3 (.d8 0x24))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[59, 3]
    (.letOp (n := 62) (.out 0x124b69 (movR64M64Effect 0x124b69 1 (.sib 4 none 0 (.d8 0x24))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 63) (.exec 0x124b69 (LoadPre 0x124b69 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x124b69 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124b69 1 (.sib 4 none 0 (.d8 0x24))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x124b6e (movR64M64Effect 0x124b6e 2 (.sib 4 none 0 (.d8 0x2c))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 65) (.exec 0x124b6e (LoadPre 0x124b6e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x124b6e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124b6e 2 (.sib 4 none 0 (.d8 0x2c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x124b73 (StorePre 0x124b73 4 (fun s => AddrMode.addr (.base 3 (.d8 0x1c)) s (0x124b73 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124b73 2 (.base 3 (.d8 0x1c))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[64, 3]
    (.letOp (n := 67) (.exec 0x124b77 (StorePre 0x124b77 4 (fun s => AddrMode.addr (.base 3 (.d8 0x14)) s (0x124b77 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124b77 1 (.base 3 (.d8 0x14))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[62, 3]
    (.letOp (n := 68) (.out 0x124b7b (movR64M64Effect 0x124b7b 1 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 69) (.exec 0x124b7b (LoadPre 0x124b7b (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x124b7b + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x124b7b 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.out 0x124b7f (movR64M64Effect 0x124b7f 2 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 71) (.exec 0x124b7f (LoadPre 0x124b7f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x124b7f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124b7f 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.exec 0x124b84 (StorePre 0x124b84 4 (fun s => AddrMode.addr (.base 3 (.d8 0xc)) s (0x124b84 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124b84 2 (.base 3 (.d8 0xc))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[70, 3]
    (.letOp (n := 73) (.exec 0x124b88 (StorePre 0x124b88 4 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x124b88 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124b88 1 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[68, 3]
    (.letOp (n := 74) (.exec 0x124b8c (StorePre 0x124b8c 2 (fun s => AddrMode.addr (.base 3 .none) s (0x124b8c + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x124b8c 0 (.base 3 .none)) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (.terminate (.br ⟨.l124bcf, RegMap.args [(0, 0), (1, 68), (2, 70), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩)))))))))))))))))))))))

def bytes_l124b50 : List UInt8 :=
  [0x8B, 0x4C, 0x24, 0x44, 0x89, 0x4B, 0x34, 0x48, 0x8B, 0x4C, 0x24, 0x3C, 0x48, 0x89, 0x4B, 0x2C,
    0x48, 0x8B, 0x4C, 0x24, 0x34, 0x48, 0x89, 0x4B, 0x24, 0x48, 0x8B, 0x4C, 0x24, 0x24, 0x48, 0x8B,
    0x54, 0x24, 0x2C, 0x48, 0x89, 0x53, 0x1C, 0x48, 0x89, 0x4B, 0x14, 0x48, 0x8B, 0x0C, 0x24, 0x48,
    0x8B, 0x54, 0x24, 0x08, 0x48, 0x89, 0x53, 0x0C, 0x48, 0x89, 0x4B, 0x04, 0x89, 0x03, 0xEB, 0x3F]

theorem code_l124b50 : ∀ x ∈ codeRange 0x124b50 bytes_l124b50, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24b50 64 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124b90 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124b90 (movR64M64Effect 0x124b90 1 (.sib 4 none 0 (.d8 0x14))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x124b90 (LoadPre 0x124b90 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x124b90 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124b90 1 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x124b95 (movR64M64Effect 0x124b95 2 (.sib 4 none 0 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 56) (.exec 0x124b95 (LoadPre 0x124b95 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x124b95 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124b95 2 (.sib 4 none 0 (.d8 0x1c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x124b9a (movR32M32LowEffect 0x124b9a 6 (.sib 4 none 0 (.d8 0x44))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 58) (.exec 0x124b9a (LoadPre 0x124b9a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x124b9a + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x124b9a 6 (.sib 4 none 0 (.d8 0x44))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.exec 0x124b9e (StorePre 0x124b9e 3 (fun s => AddrMode.addr (.base 3 (.d8 0x34)) s (0x124b9e + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x124b9e 6 (.base 3 (.d8 0x34))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[57, 3]
    (.letOp (n := 60) (.out 0x124ba1 (movR64M64Effect 0x124ba1 6 (.sib 4 none 0 (.d8 0x3c))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 61) (.exec 0x124ba1 (LoadPre 0x124ba1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x124ba1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124ba1 6 (.sib 4 none 0 (.d8 0x3c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.exec 0x124ba6 (StorePre 0x124ba6 4 (fun s => AddrMode.addr (.base 3 (.d8 0x2c)) s (0x124ba6 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124ba6 6 (.base 3 (.d8 0x2c))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[60, 3]
    (.letOp (n := 63) (.out 0x124baa (movR64M64Effect 0x124baa 6 (.sib 4 none 0 (.d8 0x34))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 64) (.exec 0x124baa (LoadPre 0x124baa (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x124baa + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124baa 6 (.sib 4 none 0 (.d8 0x34))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.exec 0x124baf (StorePre 0x124baf 4 (fun s => AddrMode.addr (.base 3 (.d8 0x24)) s (0x124baf + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124baf 6 (.base 3 (.d8 0x24))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[63, 3]
    (.letOp (n := 66) (.out 0x124bb3 (movR64M64Effect 0x124bb3 6 (.sib 4 none 0 (.d8 0x2c))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 67) (.exec 0x124bb3 (LoadPre 0x124bb3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x124bb3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124bb3 6 (.sib 4 none 0 (.d8 0x2c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.exec 0x124bb8 (StorePre 0x124bb8 4 (fun s => AddrMode.addr (.base 3 (.d8 0x1c)) s (0x124bb8 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124bb8 6 (.base 3 (.d8 0x1c))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[66, 3]
    (.letOp (n := 69) (.out 0x124bbc (movR64M64Effect 0x124bbc 6 (.sib 4 none 0 (.d8 0x24))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 70) (.exec 0x124bbc (LoadPre 0x124bbc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x124bbc + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124bbc 6 (.sib 4 none 0 (.d8 0x24))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.exec 0x124bc1 (StorePre 0x124bc1 4 (fun s => AddrMode.addr (.base 3 (.d8 0x14)) s (0x124bc1 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124bc1 6 (.base 3 (.d8 0x14))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[69, 3]
    (.letOp (n := 72) (.exec 0x124bc5 (StorePre 0x124bc5 4 (fun s => AddrMode.addr (.base 3 (.d8 0xc)) s (0x124bc5 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124bc5 2 (.base 3 (.d8 0xc))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[55, 3]
    (.letOp (n := 73) (.exec 0x124bc9 (StorePre 0x124bc9 2 (fun s => AddrMode.addr (.base 3 .none) s (0x124bc9 + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x124bc9 0 (.base 3 .none)) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (.letOp (n := 74) (.exec 0x124bcb (StorePre 0x124bcb 4 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x124bcb + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124bcb 1 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[53, 3]
    (.terminate (.br ⟨.l124bcf, RegMap.args [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 69), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩)))))))))))))))))))))))

def bytes_l124b90 : List UInt8 :=
  [0x48, 0x8B, 0x4C, 0x24, 0x14, 0x48, 0x8B, 0x54, 0x24, 0x1C, 0x8B, 0x74, 0x24, 0x44, 0x89, 0x73,
    0x34, 0x48, 0x8B, 0x74, 0x24, 0x3C, 0x48, 0x89, 0x73, 0x2C, 0x48, 0x8B, 0x74, 0x24, 0x34, 0x48,
    0x89, 0x73, 0x24, 0x48, 0x8B, 0x74, 0x24, 0x2C, 0x48, 0x89, 0x73, 0x1C, 0x48, 0x8B, 0x74, 0x24,
    0x24, 0x48, 0x89, 0x73, 0x14, 0x48, 0x89, 0x53, 0x0C, 0x89, 0x03, 0x48, 0x89, 0x4B, 0x04]

theorem code_l124b90 : ∀ x ∈ codeRange 0x124b90 bytes_l124b90, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24b90 63 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124bcf : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124bcf (movR64R64Effect 0x124bcf 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 54) (.exec 0x124bcf (fun s => s.RIP = 0x124bcf) (movR64R64Effect 0x124bcf 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x124bd2 (addR64Imm8Effect 0x124bd2 4 0x58) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 56) (.exec 0x124bd2 (fun s => s.RIP = 0x124bd2) (addR64Imm8Effect 0x124bd2 4 0x58) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x124bd6 (popR64Effect 0x124bd6 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[55]
    (.letOp (n := 58) (.out 0x124bd6 (popR64Effect 0x124bd6 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[55]
    (.letOp (n := 59) (.exec 0x124bd6 (PopPre 0x124bd6) (popR64Effect 0x124bd6 1 3) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 60) (.out 0x124bd7 (popR64Effect 0x124bd7 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[58]
    (.letOp (n := 61) (.out 0x124bd7 (popR64Effect 0x124bd7 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[58]
    (.letOp (n := 62) (.exec 0x124bd7 (PopPre 0x124bd7) (popR64Effect 0x124bd7 2 14) (Reg.operands [.gpr 4] [])) #v[58]
    (.letOp (n := 63) (.out 0x124bd9 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[61]
    (.letOp (n := 64) (.out 0x124bd9 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 65) (.exec 0x124bd9 (RetPre 0x124bd9) (retEffect) (Reg.operands [.gpr 4] [])) #v[61]
    (.terminate (.ret (RegMap.args [(0, 53), (1, 1), (2, 2), (3, 57), (4, 64), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 66) (some ⟨63, by decide⟩)))))))))))))))

def bytes_l124bcf : List UInt8 :=
  [0x48, 0x89, 0xD8, 0x48, 0x83, 0xC4, 0x58, 0x5B, 0x41, 0x5E, 0xC3]

theorem code_l124bcf : ∀ x ∈ codeRange 0x124bcf bytes_l124bcf, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24bcf 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124be0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124be0 (pushR64Effect 0x124be0 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x124be0 (PushPre 0x124be0 1) (pushR64Effect 0x124be0 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x124be1 (pushR64Effect 0x124be1 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x124be1 (PushPre 0x124be1 2) (pushR64Effect 0x124be1 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x124be3 (pushR64Effect 0x124be3 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x124be3 (PushPre 0x124be3 2) (pushR64Effect 0x124be3 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x124be5 (pushR64Effect 0x124be5 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[57, 3]
    (.letOp (n := 60) (.exec 0x124be5 (PushPre 0x124be5 1) (pushR64Effect 0x124be5 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[57, 3]
    (.letOp (n := 61) (.out 0x124be6 (subR64Imm8Effect 0x124be6 4 0x48) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 62) (.exec 0x124be6 (fun s => s.RIP = 0x124be6) (subR64Imm8Effect 0x124be6 4 0x48) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 63) (.exec 0x124bea (StorePre 0x124bea 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x124bea + BitVec.ofNat 64 7)) 2) (movM16Imm16Effect 0x124bea (.sib 4 none 0 (.d8 0xc)) 0x0) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 64) (.out 0x124bf1 (movR32M32LowEffect 0x124bf1 3 (.base 2 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[2]
    (.letOp (n := 65) (.exec 0x124bf1 (LoadPre 0x124bf1 (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x124bf1 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x124bf1 3 (.base 2 (.d8 0x8))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 66) (.out 0x124bf4 (testR64R64Effect 0x124bf4 3 3) (EffectPart.reads (.flag .ZF) [.gpr 3, .gpr 3] []) (.flag .ZF)) #v[64, 64]
    (.letOp (n := 67) (.exec 0x124bf4 (fun s => s.RIP = 0x124bf4) (testR64R64Effect 0x124bf4 3 3) (Reg.operands [.gpr 3, .gpr 3] [])) #v[64, 64]
    (.letOp (n := 68) (.pure (condOp 4)) #v[66]
    (.terminate (.condBr (Fin.last 68) ⟨.l124c1f, RegMap.args [(1, 1), (2, 2), (3, 64), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 66), (22, 22), (39, 39), (50, 50), (51, 51)] 69⟩ ⟨.l124bf9, RegMap.args [(1, 1), (2, 2), (3, 64), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 66), (22, 22), (39, 39), (50, 50), (51, 51)] 69⟩)))))))))))))))))

def bytes_l124be0 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x53, 0x48, 0x83, 0xEC, 0x48, 0x66, 0xC7, 0x44, 0x24, 0x0C, 0x00,
    0x00, 0x8B, 0x5A, 0x08, 0x48, 0x85, 0xDB, 0x74, 0x26]

theorem code_l124be0 : ∀ x ∈ codeRange 0x124be0 bytes_l124be0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24be0 25 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124bf9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124bf9 (cmpR32Imm8Effect 0x124bf9 3 3 0x2) (EffectPart.reads (.flag .CF) [.gpr 3] []) (.flag .CF)) #v[3]
    (.letOp (n := 54) (.out 0x124bf9 (cmpR32Imm8Effect 0x124bf9 3 3 0x2) (EffectPart.reads (.flag .ZF) [.gpr 3] []) (.flag .ZF)) #v[3]
    (.letOp (n := 55) (.exec 0x124bf9 (fun s => s.RIP = 0x124bf9) (cmpR32Imm8Effect 0x124bf9 3 3 0x2) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 56) (.pure (condOp 6)) #v[53, 54]
    (.terminate (.condBr (Fin.last 56) ⟨.l124c3c, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩ ⟨.l124bfe, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l124bf9 : List UInt8 :=
  [0x83, 0xFB, 0x02, 0x76, 0x3E]

theorem code_l124bf9 : ∀ x ∈ codeRange 0x124bf9 bytes_l124bf9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24bf9 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124bfe : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x124bfe (StorePre 0x124bfe 4 (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x124bfe + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x124bfe (.base 6 (.d8 0x20)) 0x1) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 54) (.out 0x124c02 (movR32M32LowEffect 0x124c02 0 (.base 6 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 55) (.exec 0x124c02 (LoadPre 0x124c02 (fun s => AddrMode.addr (.base 6 (.d8 0x1c)) s (0x124c02 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x124c02 0 (.base 6 (.d8 0x1c))) (Reg.operands [.gpr 6] [])) #v[6]
    (.terminate (.br ⟨.l124c05, RegMap.args [(0, 54), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l124bfe : List UInt8 :=
  [0xC6, 0x46, 0x20, 0x01, 0x8B, 0x46, 0x1C]

theorem code_l124bfe : ∀ x ∈ codeRange 0x124bfe bytes_l124bfe, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24bfe 7 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124c05 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x124c05 (StorePre 0x124c05 6 (fun s => AddrMode.addr (.base 7 .none) s (0x124c05 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x124c05 6 (.base 7 .none) 0x1) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 54) (.exec 0x124c0b (StorePre 0x124c0b 3 (fun s => AddrMode.addr (.base 7 (.d8 0x4)) s (0x124c0b + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x124c0b 0 (.base 7 (.d8 0x4))) (Reg.operands [.gpr 0, .gpr 7] [])) #v[0, 7]
    (.letOp (n := 55) (.exec 0x124c0e (StorePre 0x124c0e 4 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x124c0e + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x124c0e (.base 7 (.d8 0x8)) 0x7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 56) (.exec 0x124c12 (StorePre 0x124c12 8 (fun s => AddrMode.addr (.base 7 (.d8 0xc)) s (0x124c12 + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x124c12 (.base 7 (.d8 0xc)) 0x1) (Reg.operands [.gpr 7] [])) #v[7]
    (.terminate (.br ⟨.l124db3, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l124c05 : List UInt8 :=
  [0xC7, 0x07, 0x01, 0x00, 0x00, 0x00, 0x89, 0x47, 0x04, 0xC6, 0x47, 0x08, 0x07, 0x48, 0xC7, 0x47,
    0x0C, 0x01, 0x00, 0x00, 0x00, 0xE9, 0x94, 0x01, 0x00, 0x00]

theorem code_l124c05 : ∀ x ∈ codeRange 0x124c05 bytes_l124c05, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24c05 26 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124c1f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x124c1f (StorePre 0x124c1f 4 (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x124c1f + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x124c1f (.base 6 (.d8 0x20)) 0x1) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 54) (.out 0x124c23 (movR32M32LowEffect 0x124c23 0 (.base 6 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 55) (.exec 0x124c23 (LoadPre 0x124c23 (fun s => AddrMode.addr (.base 6 (.d8 0x1c)) s (0x124c23 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x124c23 0 (.base 6 (.d8 0x1c))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 56) (.exec 0x124c26 (StorePre 0x124c26 6 (fun s => AddrMode.addr (.base 7 .none) s (0x124c26 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x124c26 6 (.base 7 .none) 0x1) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 57) (.exec 0x124c2c (StorePre 0x124c2c 3 (fun s => AddrMode.addr (.base 7 (.d8 0x4)) s (0x124c2c + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x124c2c 0 (.base 7 (.d8 0x4))) (Reg.operands [.gpr 0, .gpr 7] [])) #v[54, 7]
    (.letOp (n := 58) (.exec 0x124c2f (StorePre 0x124c2f 4 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x124c2f + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x124c2f (.base 7 (.d8 0x8)) 0x5) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 59) (.exec 0x124c33 (StorePre 0x124c33 4 (fun s => AddrMode.addr (.base 7 (.d8 0xc)) s (0x124c33 + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x124c33 (.base 7 (.d8 0xc)) 0x1) (Reg.operands [.gpr 7] [])) #v[7]
    (.terminate (.br ⟨.l124db3, RegMap.args [(0, 54), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l124c1f : List UInt8 :=
  [0xC6, 0x46, 0x20, 0x01, 0x8B, 0x46, 0x1C, 0xC7, 0x07, 0x01, 0x00, 0x00, 0x00, 0x89, 0x47, 0x04,
    0xC6, 0x47, 0x08, 0x05, 0xC6, 0x47, 0x0C, 0x01, 0xE9, 0x77, 0x01, 0x00, 0x00]

theorem code_l124c1f : ∀ x ∈ codeRange 0x124c1f bytes_l124c1f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24c1f 29 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124c3c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124c3c (movR64R64Effect 0x124c3c 14 7) (EffectPart.reads (.reg (.gpr 14)) [.gpr 7] []) (.reg (.gpr 14))) #v[7]
    (.letOp (n := 54) (.exec 0x124c3c (fun s => s.RIP = 0x124c3c) (movR64R64Effect 0x124c3c 14 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 55) (.out 0x124c3f (leaR64Effect 0x124c3f 7 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 56) (.exec 0x124c3f (fun s => s.RIP = 0x124c3f) (leaR64Effect 0x124c3f 7 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x124c44 (movR64R64Effect 0x124c44 15 6) (EffectPart.reads (.reg (.gpr 15)) [.gpr 6] []) (.reg (.gpr 15))) #v[6]
    (.letOp (n := 58) (.exec 0x124c44 (fun s => s.RIP = 0x124c44) (movR64R64Effect 0x124c44 15 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 59) (.out 0x124c47 (movR32R32Effect 0x124c47 2 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3] []) (.reg (.gpr 2))) #v[3]
    (.letOp (n := 60) (.exec 0x124c47 (fun s => s.RIP = 0x124c47) (movR32R32Effect 0x124c47 2 2 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 61) (.out 0x124c49 (callEffect (fun _ => 0x127b80) 0x124c4e) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 62) (.exec 0x124c49 (PushPre 0x124c49 5) (callEffect (fun _ => 0x127b80) 0x124c4e) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.const ⟨64, 0x124c4e⟩) #v[]
    (.terminate (.call ⟨.l127b80, RegMap.args [(2, 59), (3, 3), (4, 61), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ { target := .l124c4e, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l124c3c : List UInt8 :=
  [0x49, 0x89, 0xFE, 0x48, 0x8D, 0x7C, 0x24, 0x10, 0x49, 0x89, 0xF7, 0x89, 0xDA, 0xE8, 0x32, 0x2F,
    0x00, 0x00]

theorem code_l124c3c : ∀ x ∈ codeRange 0x124c3c bytes_l124c3c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24c3c 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124c4e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124c4e (movR32M32LowEffect 0x124c4e 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x124c4e (LoadPre 0x124c4e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x124c4e + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x124c4e 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x124c52 (cmpR32Imm8Effect 0x124c52 3 0 0x2) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x124c52 (fun s => s.RIP = 0x124c52) (cmpR32Imm8Effect 0x124c52 3 0 0x2) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l124ca1, RegMap.args [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l124c57, RegMap.args [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l124c4e : List UInt8 :=
  [0x8B, 0x44, 0x24, 0x10, 0x83, 0xF8, 0x02, 0x75, 0x4A]

theorem code_l124c4e : ∀ x ∈ codeRange 0x124c4e bytes_l124c4e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24c4e 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124c57 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124c57 (movR64M64Effect 0x124c57 6 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 54) (.exec 0x124c57 (LoadPre 0x124c57 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x124c57 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124c57 6 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x124c5c (cmpR64R64Effect 0x124c5c 6 3) (EffectPart.reads (.flag .ZF) [.gpr 6, .gpr 3] []) (.flag .ZF)) #v[53, 3]
    (.letOp (n := 56) (.exec 0x124c5c (fun s => s.RIP = 0x124c5c) (cmpR64R64Effect 0x124c5c 6 3) (Reg.operands [.gpr 6, .gpr 3] [])) #v[53, 3]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l124dcf, RegMap.args [(3, 3), (4, 4), (5, 5), (6, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l124c65, RegMap.args [(3, 3), (4, 4), (5, 5), (6, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l124c57 : List UInt8 :=
  [0x48, 0x8B, 0x74, 0x24, 0x20, 0x48, 0x39, 0xDE, 0x0F, 0x85, 0x6A, 0x01, 0x00, 0x00]

theorem code_l124c57 : ∀ x ∈ codeRange 0x124c57 bytes_l124c57, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24c57 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124c65 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124c65 (movR64M64Effect 0x124c65 6 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 54) (.exec 0x124c65 (LoadPre 0x124c65 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x124c65 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124c65 6 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x124c6a (leaR64Effect 0x124c6a 7 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 56) (.exec 0x124c6a (fun s => s.RIP = 0x124c6a) (leaR64Effect 0x124c6a 7 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x124c6f (movR64R64Effect 0x124c6f 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3] []) (.reg (.gpr 2))) #v[3]
    (.letOp (n := 58) (.exec 0x124c6f (fun s => s.RIP = 0x124c6f) (movR64R64Effect 0x124c6f 2 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 59) (.out 0x124c72 (callEffect (callMemPtr 0x124c72 (.rip 0xdf158)) (0x124c72 + BitVec.ofNat 64 (callMemLen (.rip 0xdf158)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x124c72 (GoesTo (CallMemPre 0x124c72 (.rip 0xdf158)) (callEffect (callMemPtr 0x124c72 (.rip 0xdf158)) (0x124c72 + BitVec.ofNat 64 (callMemLen (.rip 0xdf158)))) 0x12a820) (callEffect (callMemPtr 0x124c72 (.rip 0xdf158)) (0x124c72 + BitVec.ofNat 64 (callMemLen (.rip 0xdf158)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x124c78⟩) #v[]
    (.terminate (.call ⟨.l12a820, RegMap.args [(2, 57), (3, 3), (4, 59), (5, 5), (6, 53), (7, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l124c78, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l124c65 : List UInt8 :=
  [0x48, 0x8B, 0x74, 0x24, 0x18, 0x48, 0x8D, 0x7C, 0x24, 0x0C, 0x48, 0x89, 0xDA, 0xFF, 0x15, 0x58,
    0xF1, 0x0D, 0x00]

theorem code_l124c65 : ∀ x ∈ codeRange 0x124c65 bytes_l124c65, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24c65 19 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124c78 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124c78 (movzxR32M8Effect 0x124c78 5 5 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 54) (.exec 0x124c78 (LoadPre 0x124c78 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x124c78 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x124c78 5 5 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x124c7d (cmpR64Imm8Effect 0x124c7d 3 0x1) (EffectPart.reads (.flag .ZF) [.gpr 3] []) (.flag .ZF)) #v[3]
    (.letOp (n := 56) (.exec 0x124c7d (fun s => s.RIP = 0x124c7d) (cmpR64Imm8Effect 0x124c7d 3 0x1) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l124cea, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l124c83, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l124c78 : List UInt8 :=
  [0x0F, 0xB6, 0x6C, 0x24, 0x0C, 0x48, 0x83, 0xFB, 0x01, 0x75, 0x67]

theorem code_l124c78 : ∀ x ∈ codeRange 0x124c78 bytes_l124c78, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24c78 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124c83 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124c83 (testR8R8Effect 0x124c83 3 5 5) (EffectPart.reads (.flag .ZF) [.gpr 5, .gpr 5] []) (.flag .ZF)) #v[5, 5]
    (.letOp (n := 54) (.out 0x124c83 (testR8R8Effect 0x124c83 3 5 5) (EffectPart.reads (.flag .SF) [.gpr 5, .gpr 5] []) (.flag .SF)) #v[5, 5]
    (.letOp (n := 55) (.exec 0x124c83 (fun s => s.RIP = 0x124c83) (testR8R8Effect 0x124c83 3 5 5) (Reg.operands [.gpr 5, .gpr 5] [])) #v[5, 5]
    (.letOp (n := 56) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 56) ⟨.l124d0c, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (20, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩ ⟨.l124c8c, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (20, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l124c83 : List UInt8 :=
  [0x40, 0x84, 0xED, 0x0F, 0x84, 0x80, 0x00, 0x00, 0x00]

theorem code_l124c83 : ∀ x ∈ codeRange 0x124c83 bytes_l124c83, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24c83 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124c8c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.pure (condOp 9)) #v[20]
    (.terminate (.condBr (Fin.last 53) ⟨.l124d3f, RegMap.args (entryMap (live .l124c8c)) 54⟩ ⟨.l124c92, RegMap.args (entryMap (live .l124c8c)) 54⟩))

def bytes_l124c8c : List UInt8 :=
  [0x0F, 0x89, 0xAD, 0x00, 0x00, 0x00]

theorem code_l124c8c : ∀ x ∈ codeRange 0x124c8c bytes_l124c8c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24c8c 6 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124c92 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124c92 (movR64R64Effect 0x124c92 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[15]
    (.letOp (n := 54) (.exec 0x124c92 (fun s => s.RIP = 0x124c92) (movR64R64Effect 0x124c92 0 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.out 0x124c95 (movR64Imm64Effect 0x124c95 1 0x100000015) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 56) (.exec 0x124c95 (fun s => s.RIP = 0x124c95) (movR64Imm64Effect 0x124c95 1 0x100000015) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l124d1e, RegMap.args [(0, 53), (1, 55), (2, 2), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l124c92 : List UInt8 :=
  [0x4C, 0x89, 0xF8, 0x48, 0xB9, 0x15, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0xEB, 0x7D]

theorem code_l124c92 : ∀ x ∈ codeRange 0x124c92 bytes_l124c92, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24c92 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124ca1 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124ca1 (movR32M32LowEffect 0x124ca1 1 (.sib 4 none 0 (.d8 0x14))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x124ca1 (LoadPre 0x124ca1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x124ca1 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x124ca1 1 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x124ca5 (movR64M64Effect 0x124ca5 2 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 56) (.exec 0x124ca5 (LoadPre 0x124ca5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x124ca5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124ca5 2 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x124caa (movR64M64Effect 0x124caa 6 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 58) (.exec 0x124caa (LoadPre 0x124caa (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x124caa + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124caa 6 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x124caf (movR64M64Effect 0x124caf 8 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 60) (.exec 0x124caf (LoadPre 0x124caf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x124caf + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124caf 8 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x124cb4 (movR64R64Effect 0x124cb4 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 62) (.exec 0x124cb4 (fun s => s.RIP = 0x124cb4) (movR64R64Effect 0x124cb4 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 63) (.exec 0x124cb7 (StorePre 0x124cb7 4 (fun s => AddrMode.addr (.base 14 (.d8 0x30)) s (0x124cb7 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124cb7 8 (.base 14 (.d8 0x30))) (Reg.operands [.gpr 8, .gpr 14] [])) #v[59, 14]
    (.letOp (n := 64) (.out 0x124cbb (movR64M64Effect 0x124cbb 8 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 65) (.exec 0x124cbb (LoadPre 0x124cbb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x124cbb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124cbb 8 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x124cc0 (StorePre 0x124cc0 4 (fun s => AddrMode.addr (.base 14 (.d8 0x28)) s (0x124cc0 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124cc0 8 (.base 14 (.d8 0x28))) (Reg.operands [.gpr 8, .gpr 14] [])) #v[64, 14]
    (.letOp (n := 67) (.out 0x124cc4 (movR64M64Effect 0x124cc4 8 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 68) (.exec 0x124cc4 (LoadPre 0x124cc4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x124cc4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124cc4 8 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.exec 0x124cc9 (StorePre 0x124cc9 4 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x124cc9 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124cc9 8 (.base 14 (.d8 0x20))) (Reg.operands [.gpr 8, .gpr 14] [])) #v[67, 14]
    (.letOp (n := 70) (.out 0x124ccd (movR64M64Effect 0x124ccd 8 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 71) (.exec 0x124ccd (LoadPre 0x124ccd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x124ccd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124ccd 8 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.exec 0x124cd2 (StorePre 0x124cd2 4 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x124cd2 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124cd2 8 (.base 14 (.d8 0x18))) (Reg.operands [.gpr 8, .gpr 14] [])) #v[70, 14]
    (.letOp (n := 73) (.exec 0x124cd6 (StorePre 0x124cd6 3 (fun s => AddrMode.addr (.base 14 .none) s (0x124cd6 + BitVec.ofNat 64 3)) 4) (movM32R32Effect 0x124cd6 0 (.base 14 .none)) (Reg.operands [.gpr 0, .gpr 14] [])) #v[0, 14]
    (.letOp (n := 74) (.exec 0x124cd9 (StorePre 0x124cd9 4 (fun s => AddrMode.addr (.base 14 (.d8 0x4)) s (0x124cd9 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x124cd9 1 (.base 14 (.d8 0x4))) (Reg.operands [.gpr 1, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 75) (.exec 0x124cdd (StorePre 0x124cdd 4 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x124cdd + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124cdd 2 (.base 14 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 76) (.exec 0x124ce1 (StorePre 0x124ce1 4 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x124ce1 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124ce1 6 (.base 14 (.d8 0x10))) (Reg.operands [.gpr 6, .gpr 14] [])) #v[57, 14]
    (.terminate (.br ⟨.l124db3, RegMap.args [(0, 0), (1, 53), (2, 55), (4, 4), (6, 57), (7, 61), (8, 70), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)] 77⟩)))))))))))))))))))))))))

def bytes_l124ca1 : List UInt8 :=
  [0x8B, 0x4C, 0x24, 0x14, 0x48, 0x8B, 0x54, 0x24, 0x18, 0x48, 0x8B, 0x74, 0x24, 0x20, 0x4C, 0x8B,
    0x44, 0x24, 0x40, 0x4C, 0x89, 0xF7, 0x4D, 0x89, 0x46, 0x30, 0x4C, 0x8B, 0x44, 0x24, 0x38, 0x4D,
    0x89, 0x46, 0x28, 0x4C, 0x8B, 0x44, 0x24, 0x30, 0x4D, 0x89, 0x46, 0x20, 0x4C, 0x8B, 0x44, 0x24,
    0x28, 0x4D, 0x89, 0x46, 0x18, 0x41, 0x89, 0x06, 0x41, 0x89, 0x4E, 0x04, 0x49, 0x89, 0x56, 0x08,
    0x49, 0x89, 0x76, 0x10, 0xE9, 0xC9, 0x00, 0x00, 0x00]

theorem code_l124ca1 : ∀ x ∈ codeRange 0x124ca1 bytes_l124ca1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24ca1 73 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124cea : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124cea (movR64Imm64Effect 0x124cea 1 0x100000015) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 54) (.exec 0x124cea (fun s => s.RIP = 0x124cea) (movR64Imm64Effect 0x124cea 1 0x100000015) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x124cf4 (testR8R8Effect 0x124cf4 3 5 5) (EffectPart.reads (.flag .ZF) [.gpr 5, .gpr 5] []) (.flag .ZF)) #v[5, 5]
    (.letOp (n := 56) (.exec 0x124cf4 (fun s => s.RIP = 0x124cf4) (testR8R8Effect 0x124cf4 3 5 5) (Reg.operands [.gpr 5, .gpr 5] [])) #v[5, 5]
    (.letOp (n := 57) (.out 0x124cf7 (movR64R64Effect 0x124cf7 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[15]
    (.letOp (n := 58) (.exec 0x124cf7 (fun s => s.RIP = 0x124cf7) (movR64R64Effect 0x124cf7 0 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 59) (.pure (condOp 4)) #v[55]
    (.terminate (.condBr (Fin.last 59) ⟨.l124d10, RegMap.args [(0, 57), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l124cfc, RegMap.args [(0, 57), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l124cea : List UInt8 :=
  [0x48, 0xB9, 0x15, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x40, 0x84, 0xED, 0x4C, 0x89, 0xF8,
    0x74, 0x14]

theorem code_l124cea : ∀ x ∈ codeRange 0x124cea bytes_l124cea, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24cea 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124cfc : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124cfc (movR64R64Effect 0x124cfc 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 54) (.exec 0x124cfc (fun s => s.RIP = 0x124cfc) (movR64R64Effect 0x124cfc 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 55) (.out 0x124cff (leaR64Effect 0x124cff 2 (.base 1 (.d8 0xf0))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[1]
    (.letOp (n := 56) (.exec 0x124cff (fun s => s.RIP = 0x124cff) (leaR64Effect 0x124cff 2 (.base 1 (.d8 0xf0))) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 57) (.out 0x124d03 (testR8R8Effect 0x124d03 3 5 5) (EffectPart.reads (.flag .SF) [.gpr 5, .gpr 5] []) (.flag .SF)) #v[5, 5]
    (.letOp (n := 58) (.exec 0x124d03 (fun s => s.RIP = 0x124d03) (testR8R8Effect 0x124d03 3 5 5) (Reg.operands [.gpr 5, .gpr 5] [])) #v[5, 5]
    (.letOp (n := 59) (.out 0x124d06 (atFlags (condHolds 9) (cmovR64R64Effect 0x124d06 4 1 2)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF]) (.reg (.gpr 1))) #v[1, 55, 57]
    (.letOp (n := 60) (.exec 0x124d06 (fun s => s.RIP = 0x124d06) (atFlags (condHolds 9) (cmovR64R64Effect 0x124d06 4 1 2)) (Reg.operands [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF])) #v[1, 55, 57]
    (.terminate (.br ⟨.l124d21, RegMap.args [(0, 0), (1, 59), (2, 55), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (20, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩)))))))))

def bytes_l124cfc : List UInt8 :=
  [0x4C, 0x89, 0xF7, 0x48, 0x8D, 0x51, 0xF0, 0x40, 0x84, 0xED, 0x48, 0x0F, 0x49, 0xCA, 0xEB, 0x15]

theorem code_l124cfc : ∀ x ∈ codeRange 0x124cfc bytes_l124cfc, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24cfc 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124d0c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124d0c (xorR32R32Effect 0x124d0c 2 5 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 5] []) (.reg (.gpr 5))) #v[5, 5]
    (.letOp (n := 54) (.exec 0x124d0c (fun s => s.RIP = 0x124d0c) (xorR32R32Effect 0x124d0c 2 5 5) (Reg.operands [.gpr 5, .gpr 5] [])) #v[5, 5]
    (.terminate (.br ⟨.l124d3f, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l124d0c : List UInt8 :=
  [0x31, 0xED, 0xEB, 0x2F]

theorem code_l124d0c : ∀ x ∈ codeRange 0x124d0c bytes_l124d0c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24d0c 4 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124d10 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124d10 (movzxR32M8Effect 0x124d10 5 5 (.sib 4 none 0 (.d8 0xd))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 54) (.exec 0x124d10 (LoadPre 0x124d10 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xd)) s (0x124d10 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x124d10 5 5 (.sib 4 none 0 (.d8 0xd))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x124d15 (testR8R8Effect 0x124d15 3 5 5) (EffectPart.reads (.flag .SF) [.gpr 5, .gpr 5] []) (.flag .SF)) #v[53, 53]
    (.letOp (n := 56) (.exec 0x124d15 (fun s => s.RIP = 0x124d15) (testR8R8Effect 0x124d15 3 5 5) (Reg.operands [.gpr 5, .gpr 5] [])) #v[53, 53]
    (.letOp (n := 57) (.pure (condOp 8)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l124d3f, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (20, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l124d1a, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (20, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l124d10 : List UInt8 :=
  [0x0F, 0xB6, 0x6C, 0x24, 0x0D, 0x40, 0x84, 0xED, 0x78, 0x25]

theorem code_l124d10 : ∀ x ∈ codeRange 0x124d10 bytes_l124d10, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24d10 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124d1a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124d1a (addR64Imm8Effect 0x124d1a 1 0xf2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1]
    (.letOp (n := 54) (.exec 0x124d1a (fun s => s.RIP = 0x124d1a) (addR64Imm8Effect 0x124d1a 1 0xf2) (Reg.operands [.gpr 1] [])) #v[1]
    (.terminate (.br ⟨.l124d1e, RegMap.args [(0, 0), (1, 53), (2, 2), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l124d1a : List UInt8 :=
  [0x48, 0x83, 0xC1, 0xF2]

theorem code_l124d1a : ∀ x ∈ codeRange 0x124d1a bytes_l124d1a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24d1a 4 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124d1e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124d1e (movR64R64Effect 0x124d1e 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 54) (.exec 0x124d1e (fun s => s.RIP = 0x124d1e) (movR64R64Effect 0x124d1e 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.terminate (.br ⟨.l124d21, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l124d1e : List UInt8 :=
  [0x4C, 0x89, 0xF7]

theorem code_l124d1e : ∀ x ∈ codeRange 0x124d1e bytes_l124d1e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24d1e 3 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124d21 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x124d21 (StorePre 0x124d21 4 (fun s => AddrMode.addr (.base 0 (.d8 0x20)) s (0x124d21 + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x124d21 (.base 0 (.d8 0x20)) 0x1) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 54) (.out 0x124d25 (movR32M32LowEffect 0x124d25 0 (.base 0 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 55) (.exec 0x124d25 (LoadPre 0x124d25 (fun s => AddrMode.addr (.base 0 (.d8 0x1c)) s (0x124d25 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x124d25 0 (.base 0 (.d8 0x1c))) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 56) (.exec 0x124d28 (StorePre 0x124d28 6 (fun s => AddrMode.addr (.base 7 .none) s (0x124d28 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x124d28 6 (.base 7 .none) 0x1) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 57) (.exec 0x124d2e (StorePre 0x124d2e 3 (fun s => AddrMode.addr (.base 7 (.d8 0x4)) s (0x124d2e + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x124d2e 0 (.base 7 (.d8 0x4))) (Reg.operands [.gpr 0, .gpr 7] [])) #v[54, 7]
    (.letOp (n := 58) (.exec 0x124d31 (StorePre 0x124d31 4 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x124d31 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124d31 1 (.base 7 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 7] [])) #v[1, 7]
    (.letOp (n := 59) (.exec 0x124d35 (StorePre 0x124d35 8 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x124d35 + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x124d35 (.base 7 (.d8 0x10)) 0x0) (Reg.operands [.gpr 7] [])) #v[7]
    (.terminate (.br ⟨.l124db3, RegMap.args [(0, 54), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l124d21 : List UInt8 :=
  [0xC6, 0x40, 0x20, 0x01, 0x8B, 0x40, 0x1C, 0xC7, 0x07, 0x01, 0x00, 0x00, 0x00, 0x89, 0x47, 0x04,
    0x48, 0x89, 0x4F, 0x08, 0x48, 0xC7, 0x47, 0x10, 0x00, 0x00, 0x00, 0x00, 0xEB, 0x74]

theorem code_l124d21 : ∀ x ∈ codeRange 0x124d21 bytes_l124d21, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24d21 30 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124d3f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x124d3f (StorePre 0x124d3f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x124d3f + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x124d3f 5 5 (.sib 4 none 0 (.d8 0xf))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[5, 4]
    (.letOp (n := 54) (.out 0x124d44 (leaR64Effect 0x124d44 7 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 55) (.exec 0x124d44 (fun s => s.RIP = 0x124d44) (leaR64Effect 0x124d44 7 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x124d49 (leaR64Effect 0x124d49 6 (.sib 4 none 0 (.d8 0xf))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 57) (.exec 0x124d49 (fun s => s.RIP = 0x124d49) (leaR64Effect 0x124d49 6 (.sib 4 none 0 (.d8 0xf))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.out 0x124d4e (callEffect (fun _ => 0x127670) 0x124d53) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 59) (.exec 0x124d4e (PushPre 0x124d4e 5) (callEffect (fun _ => 0x127670) 0x124d53) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.const ⟨64, 0x124d53⟩) #v[]
    (.terminate (.call ⟨.l127670, RegMap.args [(2, 2), (3, 3), (4, 58), (5, 5), (6, 56), (7, 54), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩ { target := .l124d53, kept := #v[], arity := rfl, guard := some (Fin.last 60) })))))))))

def bytes_l124d3f : List UInt8 :=
  [0x40, 0x88, 0x6C, 0x24, 0x0F, 0x48, 0x8D, 0x7C, 0x24, 0x10, 0x48, 0x8D, 0x74, 0x24, 0x0F, 0xE8,
    0x1D, 0x29, 0x00, 0x00]

theorem code_l124d3f : ∀ x ∈ codeRange 0x124d3f bytes_l124d3f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24d3f 20 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124d53 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124d53 (movR32M32LowEffect 0x124d53 1 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x124d53 (LoadPre 0x124d53 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x124d53 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x124d53 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x124d57 (movR32M32LowEffect 0x124d57 0 (.sib 4 none 0 (.d8 0x14))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 56) (.exec 0x124d57 (LoadPre 0x124d57 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x124d57 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x124d57 0 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x124d5b (cmpR32Imm8Effect 0x124d5b 3 1 0x2) (EffectPart.reads (.flag .ZF) [.gpr 1] []) (.flag .ZF)) #v[53]
    (.letOp (n := 58) (.exec 0x124d5b (fun s => s.RIP = 0x124d5b) (cmpR32Imm8Effect 0x124d5b 3 1 0x2) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 59) (.pure (condOp 5)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l124d73, RegMap.args [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l124d60, RegMap.args [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l124d53 : List UInt8 :=
  [0x8B, 0x4C, 0x24, 0x10, 0x8B, 0x44, 0x24, 0x14, 0x83, 0xF9, 0x02, 0x75, 0x13]

theorem code_l124d53 : ∀ x ∈ codeRange 0x124d53 bytes_l124d53, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24d53 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124d60 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124d60 (cmpR32R32Effect 0x124d60 2 3 0) (EffectPart.reads (.flag .ZF) [.gpr 3, .gpr 0] []) (.flag .ZF)) #v[3, 0]
    (.letOp (n := 54) (.exec 0x124d60 (fun s => s.RIP = 0x124d60) (cmpR32R32Effect 0x124d60 2 3 0) (Reg.operands [.gpr 3, .gpr 0] [])) #v[3, 0]
    (.letOp (n := 55) (.out 0x124d62 (movR64R64Effect 0x124d62 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 56) (.exec 0x124d62 (fun s => s.RIP = 0x124d62) (movR64R64Effect 0x124d62 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 57) ⟨.l124dc1, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l124d67, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l124d60 : List UInt8 :=
  [0x39, 0xC3, 0x4C, 0x89, 0xF7, 0x75, 0x5A]

theorem code_l124d60 : ∀ x ∈ codeRange 0x124d60 bytes_l124d60, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24d60 7 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124d67 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x124d67 (StorePre 0x124d67 4 (fun s => AddrMode.addr (.base 7 (.d8 0x4)) s (0x124d67 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x124d67 4 5 (.base 7 (.d8 0x4))) (Reg.operands [.gpr 5, .gpr 7] [])) #v[5, 7]
    (.letOp (n := 54) (.exec 0x124d6b (StorePre 0x124d6b 6 (fun s => AddrMode.addr (.base 7 .none) s (0x124d6b + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x124d6b 6 (.base 7 .none) 0x2) (Reg.operands [.gpr 7] [])) #v[7]
    (.terminate (.br ⟨.l124db3, RegMap.args [(1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l124d67 : List UInt8 :=
  [0x40, 0x88, 0x6F, 0x04, 0xC7, 0x07, 0x02, 0x00, 0x00, 0x00, 0xEB, 0x40]

theorem code_l124d67 : ∀ x ∈ codeRange 0x124d67 bytes_l124d67, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24d67 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124d73 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124d73 (movR64M64Effect 0x124d73 2 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 54) (.exec 0x124d73 (LoadPre 0x124d73 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x124d73 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124d73 2 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x124d78 (movR64R64Effect 0x124d78 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 56) (.exec 0x124d78 (fun s => s.RIP = 0x124d78) (movR64R64Effect 0x124d78 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.exec 0x124d7b (StorePre 0x124d7b 4 (fun s => AddrMode.addr (.base 14 (.d8 0x30)) s (0x124d7b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124d7b 2 (.base 14 (.d8 0x30))) (Reg.operands [.gpr 2, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 58) (.out 0x124d7f (movR64M64Effect 0x124d7f 2 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 59) (.exec 0x124d7f (LoadPre 0x124d7f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x124d7f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124d7f 2 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.exec 0x124d84 (StorePre 0x124d84 4 (fun s => AddrMode.addr (.base 14 (.d8 0x28)) s (0x124d84 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124d84 2 (.base 14 (.d8 0x28))) (Reg.operands [.gpr 2, .gpr 14] [])) #v[58, 14]
    (.letOp (n := 61) (.out 0x124d88 (movR64M64Effect 0x124d88 2 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 62) (.exec 0x124d88 (LoadPre 0x124d88 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x124d88 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124d88 2 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x124d8d (StorePre 0x124d8d 4 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x124d8d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124d8d 2 (.base 14 (.d8 0x20))) (Reg.operands [.gpr 2, .gpr 14] [])) #v[61, 14]
    (.letOp (n := 64) (.out 0x124d91 (movR64M64Effect 0x124d91 2 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 65) (.exec 0x124d91 (LoadPre 0x124d91 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x124d91 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124d91 2 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x124d96 (StorePre 0x124d96 4 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x124d96 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124d96 2 (.base 14 (.d8 0x18))) (Reg.operands [.gpr 2, .gpr 14] [])) #v[64, 14]
    (.letOp (n := 67) (.out 0x124d9a (movR64M64Effect 0x124d9a 2 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 68) (.exec 0x124d9a (LoadPre 0x124d9a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x124d9a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124d9a 2 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.out 0x124d9f (movR64M64Effect 0x124d9f 6 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 70) (.exec 0x124d9f (LoadPre 0x124d9f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x124d9f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124d9f 6 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.exec 0x124da4 (StorePre 0x124da4 4 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x124da4 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124da4 6 (.base 14 (.d8 0x10))) (Reg.operands [.gpr 6, .gpr 14] [])) #v[69, 14]
    (.letOp (n := 72) (.exec 0x124da8 (StorePre 0x124da8 4 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x124da8 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124da8 2 (.base 14 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 14] [])) #v[67, 14]
    (.letOp (n := 73) (.exec 0x124dac (StorePre 0x124dac 3 (fun s => AddrMode.addr (.base 14 .none) s (0x124dac + BitVec.ofNat 64 3)) 4) (movM32R32Effect 0x124dac 1 (.base 14 .none)) (Reg.operands [.gpr 1, .gpr 14] [])) #v[1, 14]
    (.letOp (n := 74) (.exec 0x124daf (StorePre 0x124daf 4 (fun s => AddrMode.addr (.base 14 (.d8 0x4)) s (0x124daf + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x124daf 0 (.base 14 (.d8 0x4))) (Reg.operands [.gpr 0, .gpr 14] [])) #v[0, 14]
    (.terminate (.br ⟨.l124db3, RegMap.args [(0, 0), (1, 1), (2, 67), (4, 4), (6, 69), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩)))))))))))))))))))))))

def bytes_l124d73 : List UInt8 :=
  [0x48, 0x8B, 0x54, 0x24, 0x40, 0x4C, 0x89, 0xF7, 0x49, 0x89, 0x56, 0x30, 0x48, 0x8B, 0x54, 0x24,
    0x38, 0x49, 0x89, 0x56, 0x28, 0x48, 0x8B, 0x54, 0x24, 0x30, 0x49, 0x89, 0x56, 0x20, 0x48, 0x8B,
    0x54, 0x24, 0x28, 0x49, 0x89, 0x56, 0x18, 0x48, 0x8B, 0x54, 0x24, 0x18, 0x48, 0x8B, 0x74, 0x24,
    0x20, 0x49, 0x89, 0x76, 0x10, 0x49, 0x89, 0x56, 0x08, 0x41, 0x89, 0x0E, 0x41, 0x89, 0x46, 0x04]

theorem code_l124d73 : ∀ x ∈ codeRange 0x124d73 bytes_l124d73, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24d73 64 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124db3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124db3 (movR64R64Effect 0x124db3 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 54) (.exec 0x124db3 (fun s => s.RIP = 0x124db3) (movR64R64Effect 0x124db3 0 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 55) (.out 0x124db6 (addR64Imm8Effect 0x124db6 4 0x48) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 56) (.exec 0x124db6 (fun s => s.RIP = 0x124db6) (addR64Imm8Effect 0x124db6 4 0x48) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x124dba (popR64Effect 0x124dba 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[55]
    (.letOp (n := 58) (.out 0x124dba (popR64Effect 0x124dba 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[55]
    (.letOp (n := 59) (.exec 0x124dba (PopPre 0x124dba) (popR64Effect 0x124dba 1 3) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 60) (.out 0x124dbb (popR64Effect 0x124dbb 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[58]
    (.letOp (n := 61) (.out 0x124dbb (popR64Effect 0x124dbb 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[58]
    (.letOp (n := 62) (.exec 0x124dbb (PopPre 0x124dbb) (popR64Effect 0x124dbb 2 14) (Reg.operands [.gpr 4] [])) #v[58]
    (.letOp (n := 63) (.out 0x124dbd (popR64Effect 0x124dbd 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[61]
    (.letOp (n := 64) (.out 0x124dbd (popR64Effect 0x124dbd 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 65) (.exec 0x124dbd (PopPre 0x124dbd) (popR64Effect 0x124dbd 2 15) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 66) (.out 0x124dbf (popR64Effect 0x124dbf 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[64]
    (.letOp (n := 67) (.out 0x124dbf (popR64Effect 0x124dbf 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[64]
    (.letOp (n := 68) (.exec 0x124dbf (PopPre 0x124dbf) (popR64Effect 0x124dbf 1 5) (Reg.operands [.gpr 4] [])) #v[64]
    (.letOp (n := 69) (.out 0x124dc0 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[67]
    (.letOp (n := 70) (.out 0x124dc0 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[67]
    (.letOp (n := 71) (.exec 0x124dc0 (RetPre 0x124dc0) (retEffect) (Reg.operands [.gpr 4] [])) #v[67]
    (.terminate (.ret (RegMap.args [(0, 53), (1, 1), (2, 2), (3, 57), (4, 70), (5, 66), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 60), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)] 72) (some ⟨69, by decide⟩)))))))))))))))))))))

def bytes_l124db3 : List UInt8 :=
  [0x48, 0x89, 0xF8, 0x48, 0x83, 0xC4, 0x48, 0x5B, 0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l124db3 : ∀ x ∈ codeRange 0x124db3 bytes_l124db3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24db3 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124dc1 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x124dc1 (StorePre 0x124dc1 5 (fun s => AddrMode.addr (.base 15 (.d8 0x20)) s (0x124dc1 + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x124dc1 (.base 15 (.d8 0x20)) 0x1) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 54) (.out 0x124dc6 (movR32M32Effect 0x124dc6 0 (.base 15 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[15]
    (.letOp (n := 55) (.exec 0x124dc6 (LoadPre 0x124dc6 (fun s => AddrMode.addr (.base 15 (.d8 0x1c)) s (0x124dc6 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x124dc6 0 (.base 15 (.d8 0x1c))) (Reg.operands [.gpr 15] [])) #v[15]
    (.terminate (.br ⟨.l124c05, RegMap.args [(0, 54), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l124dc1 : List UInt8 :=
  [0x41, 0xC6, 0x47, 0x20, 0x01, 0x41, 0x8B, 0x47, 0x1C, 0xE9, 0x36, 0xFE, 0xFF, 0xFF]

theorem code_l124dc1 : ∀ x ∈ codeRange 0x124dc1 bytes_l124dc1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24dc1 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124dcf : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124dcf (movR64R64Effect 0x124dcf 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 54) (.exec 0x124dcf (fun s => s.RIP = 0x124dcf) (movR64R64Effect 0x124dcf 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x124dd2 (movR64Imm32Effect 0x124dd2 2 0x2036e0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 56) (.exec 0x124dd2 (fun s => s.RIP = 0x124dd2) (movR64Imm32Effect 0x124dd2 2 0x2036e0) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x124dd9 (callEffect (fun _ => 0x129c90) 0x124dde) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x124dd9 (PushPre 0x124dd9 5) (callEffect (fun _ => 0x129c90) 0x124dde) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x124dde⟩) #v[]
    (.terminate (.call ⟨.l129c90, RegMap.args [(2, 55), (3, 3), (4, 57), (5, 5), (6, 6), (7, 53)] 60⟩ { target := .l124dde, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l124dcf : List UInt8 :=
  [0x48, 0x89, 0xDF, 0x48, 0xC7, 0xC2, 0xE0, 0x36, 0x20, 0x00, 0xE8, 0xB2, 0x4E, 0x00, 0x00]

theorem code_l124dcf : ∀ x ∈ codeRange 0x124dcf bytes_l124dcf, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24dcf 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124dde : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x124dde (fun s => s.RIP = 0x124dde) (fun _ => nopEffect 0x124dde 2) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l124de0, RegMap.args [(3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 54⟩))

def bytes_l124dde : List UInt8 :=
  [0x66, 0x90]

theorem code_l124dde : ∀ x ∈ codeRange 0x124dde bytes_l124dde, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24dde 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124de0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124de0 (pushR64Effect 0x124de0 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x124de0 (PushPre 0x124de0 1) (pushR64Effect 0x124de0 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x124de1 (pushR64Effect 0x124de1 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x124de1 (PushPre 0x124de1 2) (pushR64Effect 0x124de1 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x124de3 (pushR64Effect 0x124de3 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x124de3 (PushPre 0x124de3 2) (pushR64Effect 0x124de3 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x124de5 (pushR64Effect 0x124de5 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[57, 12]
    (.letOp (n := 60) (.exec 0x124de5 (PushPre 0x124de5 2) (pushR64Effect 0x124de5 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[57, 12]
    (.letOp (n := 61) (.out 0x124de7 (pushR64Effect 0x124de7 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[59, 3]
    (.letOp (n := 62) (.exec 0x124de7 (PushPre 0x124de7 1) (pushR64Effect 0x124de7 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[59, 3]
    (.letOp (n := 63) (.out 0x124de8 (subR64Imm32Effect 0x124de8 4 0xd0) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 64) (.exec 0x124de8 (fun s => s.RIP = 0x124de8) (subR64Imm32Effect 0x124de8 4 0xd0) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 65) (.out 0x124def (movR64R64Effect 0x124def 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 6] []) (.reg (.gpr 14))) #v[6]
    (.letOp (n := 66) (.exec 0x124def (fun s => s.RIP = 0x124def) (movR64R64Effect 0x124def 14 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 67) (.out 0x124df2 (movR64R64Effect 0x124df2 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 68) (.exec 0x124df2 (fun s => s.RIP = 0x124df2) (movR64R64Effect 0x124df2 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 69) (.out 0x124df5 (movR64R64Effect 0x124df5 7 4) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[63]
    (.letOp (n := 70) (.exec 0x124df5 (fun s => s.RIP = 0x124df5) (movR64R64Effect 0x124df5 7 4) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 71) (.out 0x124df8 (callEffect (fun _ => 0x125450) 0x124dfd) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 72) (.exec 0x124df8 (PushPre 0x124df8 5) (callEffect (fun _ => 0x125450) 0x124dfd) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 73) (.const ⟨64, 0x124dfd⟩) #v[]
    (.terminate (.call ⟨.l125450, RegMap.args [(3, 67), (4, 71), (5, 5), (6, 6), (7, 69), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 74⟩ { target := .l124dfd, kept := #v[], arity := rfl, guard := some (Fin.last 73) }))))))))))))))))))))))

def bytes_l124de0 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0xD0, 0x00, 0x00, 0x00, 0x49,
    0x89, 0xF6, 0x48, 0x89, 0xFB, 0x48, 0x89, 0xE7, 0xE8, 0x53, 0x06, 0x00, 0x00]

theorem code_l124de0 : ∀ x ∈ codeRange 0x124de0 bytes_l124de0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24de0 29 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124dfd : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124dfd (movR32M32LowEffect 0x124dfd 0 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x124dfd (LoadPre 0x124dfd (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x124dfd + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x124dfd 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x124e00 (movR64M64Effect 0x124e00 1 (.sib 4 none 0 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x124e00 (LoadPre 0x124e00 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x124e00 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124e00 1 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x124e05 (StorePre 0x124e05 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x124e05 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x124e05 1 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 58) (.out 0x124e0a (movR64M64Effect 0x124e0a 1 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 59) (.exec 0x124e0a (LoadPre 0x124e0a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x124e0a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124e0a 1 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.exec 0x124e0f (StorePre 0x124e0f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x124e0f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x124e0f 1 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[58, 4]
    (.letOp (n := 61) (.out 0x124e14 (cmpR32Imm8Effect 0x124e14 3 0 0x2) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[53]
    (.letOp (n := 62) (.exec 0x124e14 (fun s => s.RIP = 0x124e14) (cmpR32Imm8Effect 0x124e14 3 0 0x2) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 63) (.pure (condOp 5)) #v[61]
    (.terminate (.condBr (Fin.last 63) ⟨.l124fbb, RegMap.args [(0, 53), (1, 58), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 61), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ ⟨.l124e1d, RegMap.args [(0, 53), (1, 58), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 61), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩))))))))))))

def bytes_l124dfd : List UInt8 :=
  [0x8B, 0x04, 0x24, 0x48, 0x8B, 0x4C, 0x24, 0x04, 0x48, 0x89, 0x4C, 0x24, 0x38, 0x48, 0x8B, 0x4C,
    0x24, 0x0C, 0x48, 0x89, 0x4C, 0x24, 0x40, 0x83, 0xF8, 0x02, 0x0F, 0x85, 0x9E, 0x01, 0x00, 0x00]

theorem code_l124dfd : ∀ x ∈ codeRange 0x124dfd bytes_l124dfd, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24dfd 32 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124e1d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124e1d (movR64M64Effect 0x124e1d 6 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 54) (.exec 0x124e1d (LoadPre 0x124e1d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x124e1d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124e1d 6 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x124e22 (movR64M64Effect 0x124e22 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 56) (.exec 0x124e22 (LoadPre 0x124e22 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x124e22 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124e22 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x124e27 (StorePre 0x124e27 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x124e27 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x124e27 6 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 58) (.exec 0x124e2f (StorePre 0x124e2f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x124e2f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x124e2f 0 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 59) (.out 0x124e37 (movR64R64Effect 0x124e37 7 4) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 60) (.exec 0x124e37 (fun s => s.RIP = 0x124e37) (movR64R64Effect 0x124e37 7 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x124e3a (movR32Imm32Effect 0x124e3a 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 62) (.exec 0x124e3a (fun s => s.RIP = 0x124e3a) (movR32Imm32Effect 0x124e3a 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 63) (.out 0x124e3f (callEffect (fun _ => 0x1276d0) 0x124e44) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 64) (.exec 0x124e3f (PushPre 0x124e3f 5) (callEffect (fun _ => 0x1276d0) 0x124e44) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.const ⟨64, 0x124e44⟩) #v[]
    (.terminate (.call ⟨.l1276d0, RegMap.args [(0, 55), (1, 1), (2, 61), (3, 3), (4, 63), (5, 5), (6, 53), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩ { target := .l124e44, kept := #v[], arity := rfl, guard := some (Fin.last 65) }))))))))))))))

def bytes_l124e1d : List UInt8 :=
  [0x48, 0x8B, 0x74, 0x24, 0x38, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48, 0x89, 0xB4, 0x24, 0x80, 0x00,
    0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x89, 0xE7, 0xBA, 0x01, 0x00,
    0x00, 0x00, 0xE8, 0x8C, 0x28, 0x00, 0x00]

theorem code_l124e1d : ∀ x ∈ codeRange 0x124e1d bytes_l124e1d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24e1d 39 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124e44 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124e44 (movR32M32LowEffect 0x124e44 0 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x124e44 (LoadPre 0x124e44 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x124e44 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x124e44 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x124e47 (cmpR32Imm8Effect 0x124e47 3 0 0x2) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x124e47 (fun s => s.RIP = 0x124e47) (cmpR32Imm8Effect 0x124e47 3 0 0x2) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l125001, RegMap.args [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l124e50, RegMap.args [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l124e44 : List UInt8 :=
  [0x8B, 0x04, 0x24, 0x83, 0xF8, 0x02, 0x0F, 0x85, 0xB1, 0x01, 0x00, 0x00]

theorem code_l124e44 : ∀ x ∈ codeRange 0x124e44 bytes_l124e44, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24e44 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124e50 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124e50 (leaR64Effect 0x124e50 7 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x124e50 (fun s => s.RIP = 0x124e50) (leaR64Effect 0x124e50 7 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x124e55 (leaR64Effect 0x124e55 2 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 56) (.exec 0x124e55 (fun s => s.RIP = 0x124e55) (leaR64Effect 0x124e55 2 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x124e5d (movR64R64Effect 0x124e5d 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 58) (.exec 0x124e5d (fun s => s.RIP = 0x124e5d) (movR64R64Effect 0x124e5d 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 59) (.out 0x124e60 (callEffect (fun _ => 0x1273c0) 0x124e65) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x124e60 (PushPre 0x124e60 5) (callEffect (fun _ => 0x1273c0) 0x124e65) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x124e65⟩) #v[]
    (.terminate (.call ⟨.l1273c0, RegMap.args [(1, 1), (2, 55), (3, 3), (4, 59), (5, 5), (6, 57), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l124e65, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l124e50 : List UInt8 :=
  [0x48, 0x8D, 0x7C, 0x24, 0x48, 0x48, 0x8D, 0x94, 0x24, 0x80, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF6,
    0xE8, 0x5B, 0x25, 0x00, 0x00]

theorem code_l124e50 : ∀ x ∈ codeRange 0x124e50 bytes_l124e50, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24e50 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124e65 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124e65 (movR32M32LowEffect 0x124e65 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x124e65 (LoadPre 0x124e65 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x124e65 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x124e65 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x124e69 (cmpR32Imm8Effect 0x124e69 3 0 0x2) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x124e69 (fun s => s.RIP = 0x124e69) (cmpR32Imm8Effect 0x124e69 3 0 0x2) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l125045, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l124e72, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l124e65 : List UInt8 :=
  [0x8B, 0x44, 0x24, 0x48, 0x83, 0xF8, 0x02, 0x0F, 0x85, 0xD3, 0x01, 0x00, 0x00]

theorem code_l124e65 : ∀ x ∈ codeRange 0x124e65 bytes_l124e65, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24e65 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124e72 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124e72 (cmpM8Imm8Effect 0x124e72 5 (.sib 4 none 0 (.d8 0x4c)) 0x1) (EffectPart.reads (.flag .ZF) [.gpr 4] []) (.flag .ZF)) #v[4]
    (.letOp (n := 54) (.exec 0x124e72 (LoadPre 0x124e72 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4c)) s (0x124e72 + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x124e72 5 (.sib 4 none 0 (.d8 0x4c)) 0x1) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l1250a8, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l124e7d, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l124e72 : List UInt8 :=
  [0x80, 0x7C, 0x24, 0x4C, 0x01, 0x0F, 0x85, 0x2B, 0x02, 0x00, 0x00]

theorem code_l124e72 : ∀ x ∈ codeRange 0x124e72 bytes_l124e72, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24e72 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124e7d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124e7d (movR64R64Effect 0x124e7d 7 4) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x124e7d (fun s => s.RIP = 0x124e7d) (movR64R64Effect 0x124e7d 7 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x124e80 (movR64R64Effect 0x124e80 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 56) (.exec 0x124e80 (fun s => s.RIP = 0x124e80) (movR64R64Effect 0x124e80 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x124e83 (callEffect (fun _ => 0x125450) 0x124e88) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x124e83 (PushPre 0x124e83 5) (callEffect (fun _ => 0x125450) 0x124e88) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x124e88⟩) #v[]
    (.terminate (.call ⟨.l125450, RegMap.args [(3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ { target := .l124e88, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l124e7d : List UInt8 :=
  [0x48, 0x89, 0xE7, 0x4C, 0x89, 0xF6, 0xE8, 0xC8, 0x05, 0x00, 0x00]

theorem code_l124e7d : ∀ x ∈ codeRange 0x124e7d bytes_l124e7d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24e7d 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124e88 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124e88 (movR32M32LowEffect 0x124e88 0 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x124e88 (LoadPre 0x124e88 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x124e88 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x124e88 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x124e8b (movR64M64Effect 0x124e8b 1 (.sib 4 none 0 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x124e8b (LoadPre 0x124e8b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x124e8b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124e8b 1 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x124e90 (StorePre 0x124e90 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x124e90 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x124e90 1 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 58) (.out 0x124e95 (movR64M64Effect 0x124e95 1 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 59) (.exec 0x124e95 (LoadPre 0x124e95 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x124e95 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124e95 1 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.exec 0x124e9a (StorePre 0x124e9a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x124e9a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x124e9a 1 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[58, 4]
    (.letOp (n := 61) (.out 0x124e9f (cmpR32Imm8Effect 0x124e9f 3 0 0x2) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[53]
    (.letOp (n := 62) (.exec 0x124e9f (fun s => s.RIP = 0x124e9f) (cmpR32Imm8Effect 0x124e9f 3 0 0x2) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 63) (.pure (condOp 5)) #v[61]
    (.terminate (.condBr (Fin.last 63) ⟨.l1250c5, RegMap.args [(0, 53), (1, 58), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 61), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ ⟨.l124ea8, RegMap.args [(0, 53), (1, 58), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 61), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩))))))))))))

def bytes_l124e88 : List UInt8 :=
  [0x8B, 0x04, 0x24, 0x48, 0x8B, 0x4C, 0x24, 0x04, 0x48, 0x89, 0x4C, 0x24, 0x38, 0x48, 0x8B, 0x4C,
    0x24, 0x0C, 0x48, 0x89, 0x4C, 0x24, 0x40, 0x83, 0xF8, 0x02, 0x0F, 0x85, 0x1D, 0x02, 0x00, 0x00]

theorem code_l124e88 : ∀ x ∈ codeRange 0x124e88 bytes_l124e88, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24e88 32 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124ea8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124ea8 (movR64M64Effect 0x124ea8 6 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 54) (.exec 0x124ea8 (LoadPre 0x124ea8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x124ea8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124ea8 6 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x124ead (movR64M64Effect 0x124ead 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 56) (.exec 0x124ead (LoadPre 0x124ead (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x124ead + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124ead 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x124eb2 (StorePre 0x124eb2 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x124eb2 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x124eb2 6 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 58) (.exec 0x124eba (StorePre 0x124eba 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x124eba + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x124eba 0 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 59) (.out 0x124ec2 (movR64R64Effect 0x124ec2 7 4) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 60) (.exec 0x124ec2 (fun s => s.RIP = 0x124ec2) (movR64R64Effect 0x124ec2 7 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x124ec5 (movR32Imm32Effect 0x124ec5 5 2 0x3) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 62) (.exec 0x124ec5 (fun s => s.RIP = 0x124ec5) (movR32Imm32Effect 0x124ec5 5 2 0x3) (Reg.operands [] [])) #v[]
    (.letOp (n := 63) (.out 0x124eca (callEffect (fun _ => 0x1276d0) 0x124ecf) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 64) (.exec 0x124eca (PushPre 0x124eca 5) (callEffect (fun _ => 0x1276d0) 0x124ecf) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.const ⟨64, 0x124ecf⟩) #v[]
    (.terminate (.call ⟨.l1276d0, RegMap.args [(0, 55), (1, 1), (2, 61), (3, 3), (4, 63), (5, 5), (6, 53), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩ { target := .l124ecf, kept := #v[], arity := rfl, guard := some (Fin.last 65) }))))))))))))))

def bytes_l124ea8 : List UInt8 :=
  [0x48, 0x8B, 0x74, 0x24, 0x38, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48, 0x89, 0xB4, 0x24, 0x80, 0x00,
    0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x89, 0xE7, 0xBA, 0x03, 0x00,
    0x00, 0x00, 0xE8, 0x01, 0x28, 0x00, 0x00]

theorem code_l124ea8 : ∀ x ∈ codeRange 0x124ea8 bytes_l124ea8, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24ea8 39 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124ecf : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124ecf (movR32M32LowEffect 0x124ecf 0 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x124ecf (LoadPre 0x124ecf (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x124ecf + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x124ecf 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x124ed2 (cmpR32Imm8Effect 0x124ed2 3 0 0x2) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x124ed2 (fun s => s.RIP = 0x124ed2) (cmpR32Imm8Effect 0x124ed2 3 0 0x2) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l12510b, RegMap.args [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l124edb, RegMap.args [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l124ecf : List UInt8 :=
  [0x8B, 0x04, 0x24, 0x83, 0xF8, 0x02, 0x0F, 0x85, 0x30, 0x02, 0x00, 0x00]

theorem code_l124ecf : ∀ x ∈ codeRange 0x124ecf bytes_l124ecf, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24ecf 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124edb : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124edb (leaR64Effect 0x124edb 7 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x124edb (fun s => s.RIP = 0x124edb) (leaR64Effect 0x124edb 7 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x124ee0 (leaR64Effect 0x124ee0 2 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 56) (.exec 0x124ee0 (fun s => s.RIP = 0x124ee0) (leaR64Effect 0x124ee0 2 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x124ee8 (movR64R64Effect 0x124ee8 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 58) (.exec 0x124ee8 (fun s => s.RIP = 0x124ee8) (movR64R64Effect 0x124ee8 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 59) (.out 0x124eeb (callEffect (fun _ => 0x127150) 0x124ef0) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x124eeb (PushPre 0x124eeb 5) (callEffect (fun _ => 0x127150) 0x124ef0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x124ef0⟩) #v[]
    (.terminate (.call ⟨.l127150, RegMap.args [(1, 1), (2, 55), (3, 3), (4, 59), (5, 5), (6, 57), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l124ef0, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l124edb : List UInt8 :=
  [0x48, 0x8D, 0x7C, 0x24, 0x48, 0x48, 0x8D, 0x94, 0x24, 0x80, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF6,
    0xE8, 0x60, 0x22, 0x00, 0x00]

theorem code_l124edb : ∀ x ∈ codeRange 0x124edb bytes_l124edb, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24edb 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124ef0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124ef0 (movR32M32LowEffect 0x124ef0 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x124ef0 (LoadPre 0x124ef0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x124ef0 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x124ef0 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x124ef4 (cmpR32Imm8Effect 0x124ef4 3 0 0x2) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x124ef4 (fun s => s.RIP = 0x124ef4) (cmpR32Imm8Effect 0x124ef4 3 0 0x2) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l12514f, RegMap.args [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l124efd, RegMap.args [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l124ef0 : List UInt8 :=
  [0x8B, 0x44, 0x24, 0x48, 0x83, 0xF8, 0x02, 0x0F, 0x85, 0x52, 0x02, 0x00, 0x00]

theorem code_l124ef0 : ∀ x ∈ codeRange 0x124ef0 bytes_l124ef0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24ef0 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124efd : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124efd (movR64M64Effect 0x124efd 15 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 54) (.exec 0x124efd (LoadPre 0x124efd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x124efd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124efd 15 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x124f02 (movR64M64Effect 0x124f02 12 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 56) (.exec 0x124f02 (LoadPre 0x124f02 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x124f02 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124f02 12 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x124f07 (movR64R64Effect 0x124f07 7 4) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 58) (.exec 0x124f07 (fun s => s.RIP = 0x124f07) (movR64R64Effect 0x124f07 7 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x124f0a (movR64R64Effect 0x124f0a 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 60) (.exec 0x124f0a (fun s => s.RIP = 0x124f0a) (movR64R64Effect 0x124f0a 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 61) (.out 0x124f0d (xorR32R32Effect 0x124f0d 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[2, 2]
    (.letOp (n := 62) (.exec 0x124f0d (fun s => s.RIP = 0x124f0d) (xorR32R32Effect 0x124f0d 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 63) (.out 0x124f0f (callEffect (fun _ => 0x1262e0) 0x124f14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 64) (.exec 0x124f0f (PushPre 0x124f0f 5) (callEffect (fun _ => 0x1262e0) 0x124f14) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.const ⟨64, 0x124f14⟩) #v[]
    (.terminate (.call ⟨.l1262e0, RegMap.args [(2, 61), (3, 3), (4, 63), (5, 5), (6, 59), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩ { target := .l124f14, kept := #v[], arity := rfl, guard := some (Fin.last 65) }))))))))))))))

def bytes_l124efd : List UInt8 :=
  [0x4C, 0x8B, 0x7C, 0x24, 0x50, 0x4C, 0x8B, 0x64, 0x24, 0x58, 0x48, 0x89, 0xE7, 0x4C, 0x89, 0xF6,
    0x31, 0xD2, 0xE8, 0xCC, 0x13, 0x00, 0x00]

theorem code_l124efd : ∀ x ∈ codeRange 0x124efd bytes_l124efd, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24efd 23 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124f14 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124f14 (movR32M32LowEffect 0x124f14 0 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x124f14 (LoadPre 0x124f14 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x124f14 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x124f14 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x124f17 (cmpR32Imm8Effect 0x124f17 3 0 0x2) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x124f17 (fun s => s.RIP = 0x124f17) (cmpR32Imm8Effect 0x124f17 3 0 0x2) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l125194, RegMap.args [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l124f20, RegMap.args [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l124f14 : List UInt8 :=
  [0x8B, 0x04, 0x24, 0x83, 0xF8, 0x02, 0x0F, 0x85, 0x74, 0x02, 0x00, 0x00]

theorem code_l124f14 : ∀ x ∈ codeRange 0x124f14 bytes_l124f14, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24f14 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124f20_1 : Block Op Label signature Reg.count 81 :=
  .letOp (n := 81) (.out 0x124f97 (movzxR32M8Effect 0x124f97 5 0 (.sib 4 none 0 (.d8 0x3a))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 82) (.exec 0x124f97 (LoadPre 0x124f97 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3a)) s (0x124f97 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x124f97 5 0 (.sib 4 none 0 (.d8 0x3a))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 83) (.exec 0x124f9c (StorePre 0x124f9c 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x72)) s (0x124f9c + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x124f9c 4 0 (.sib 4 none 0 (.d8 0x72))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[81, 4]
    (.letOp (n := 84) (.out 0x124fa0 (movzxR32M16Effect 0x124fa0 5 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 85) (.exec 0x124fa0 (LoadPre 0x124fa0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x124fa0 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x124fa0 5 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 86) (.exec 0x124fa5 (StorePre 0x124fa5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x124fa5 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x124fa5 5 0 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[84, 4]
    (.letOp (n := 87) (.out 0x124faa (cmpR8Imm8Effect 0x124faa 4 8 0x2) (EffectPart.reads (.flag .ZF) [.gpr 8] []) (.flag .ZF)) #v[74]
    (.letOp (n := 88) (.exec 0x124faa (fun s => s.RIP = 0x124faa) (cmpR8Imm8Effect 0x124faa 4 8 0x2) (Reg.operands [.gpr 8] [])) #v[74]
    (.letOp (n := 89) (.pure (condOp 5)) #v[87]
    (.terminate (.condBr (Fin.last 89) ⟨.l1252b7, RegMap.args [(0, 84), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 62), (7, 64), (8, 74), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 87), (22, 22), (39, 39), (50, 50), (51, 51)] 90⟩ ⟨.l124fb4, RegMap.args [(0, 84), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 62), (7, 64), (8, 74), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 87), (22, 22), (39, 39), (50, 50), (51, 51)] 90⟩))))))))))

def bytes_l124f20_1 : List UInt8 :=
  [0x0F, 0xB6, 0x44, 0x24, 0x3A, 0x88, 0x44, 0x24, 0x72, 0x0F, 0xB7, 0x44, 0x24, 0x38, 0x66, 0x89,
    0x44, 0x24, 0x70, 0x41, 0x80, 0xF8, 0x02, 0x0F, 0x85, 0x03, 0x03, 0x00, 0x00]

theorem code_l124f20_1 : ∀ x ∈ codeRange 0x124f97 bytes_l124f20_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24f97 29 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124f20 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124f20 (movR64M64Effect 0x124f20 0 (.sib 4 none 0 (.d8 0x25))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x124f20 (LoadPre 0x124f20 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x25)) s (0x124f20 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124f20 0 (.sib 4 none 0 (.d8 0x25))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x124f25 (StorePre 0x124f25 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x124f25 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x124f25 0 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x124f2d (movR64M64Effect 0x124f2d 1 (.sib 4 none 0 (.d8 0x1d))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 57) (.exec 0x124f2d (LoadPre 0x124f2d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1d)) s (0x124f2d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124f2d 1 (.sib 4 none 0 (.d8 0x1d))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x124f32 (StorePre 0x124f32 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x124f32 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x124f32 1 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x124f3a (movR64M64Effect 0x124f3a 2 (.sib 4 none 0 (.d8 0x15))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 60) (.exec 0x124f3a (LoadPre 0x124f3a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x15)) s (0x124f3a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124f3a 2 (.sib 4 none 0 (.d8 0x15))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x124f3f (StorePre 0x124f3f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x124f3f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x124f3f 2 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x124f47 (movR64M64Effect 0x124f47 6 (.sib 4 none 0 (.d8 0x5))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 63) (.exec 0x124f47 (LoadPre 0x124f47 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5)) s (0x124f47 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124f47 6 (.sib 4 none 0 (.d8 0x5))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x124f4c (movR64M64Effect 0x124f4c 7 (.sib 4 none 0 (.d8 0xd))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 65) (.exec 0x124f4c (LoadPre 0x124f4c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xd)) s (0x124f4c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124f4c 7 (.sib 4 none 0 (.d8 0xd))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x124f51 (StorePre 0x124f51 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x124f51 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x124f51 7 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x124f59 (StorePre 0x124f59 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x124f59 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x124f59 6 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x124f61 (movzxR32M16Effect 0x124f61 6 8 (.sib 4 none 0 (.d8 0x2d))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 69) (.exec 0x124f61 (LoadPre 0x124f61 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2d)) s (0x124f61 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x124f61 6 8 (.sib 4 none 0 (.d8 0x2d))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.exec 0x124f67 (StorePre 0x124f67 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x124f67 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x124f67 6 8 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[68, 4]
    (.letOp (n := 71) (.out 0x124f6d (movzxR32M8Effect 0x124f6d 6 8 (.sib 4 none 0 (.d8 0x2f))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 72) (.exec 0x124f6d (LoadPre 0x124f6d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2f)) s (0x124f6d + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x124f6d 6 8 (.sib 4 none 0 (.d8 0x2f))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.exec 0x124f73 (StorePre 0x124f73 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3a)) s (0x124f73 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x124f73 5 8 (.sib 4 none 0 (.d8 0x3a))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[71, 4]
    (.letOp (n := 74) (.out 0x124f78 (movzxR32M8Effect 0x124f78 6 8 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 75) (.exec 0x124f78 (LoadPre 0x124f78 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x124f78 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x124f78 6 8 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 76) (.exec 0x124f7e (StorePre 0x124f7e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x124f7e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x124f7e 6 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 77) (.exec 0x124f83 (StorePre 0x124f83 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x124f83 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x124f83 7 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 78) (.exec 0x124f88 (StorePre 0x124f88 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x124f88 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x124f88 2 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 79) (.exec 0x124f8d (StorePre 0x124f8d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x124f8d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x124f8d 1 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 80) (.exec 0x124f92 (StorePre 0x124f92 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x124f92 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x124f92 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (b_l124f20_1))))))))))))))))))))))))))))

def bytes_l124f20 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x25, 0x48, 0x89, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x4C,
    0x24, 0x1D, 0x48, 0x89, 0x8C, 0x24, 0x98, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x54, 0x24, 0x15, 0x48,
    0x89, 0x94, 0x24, 0x90, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x74, 0x24, 0x05, 0x48, 0x8B, 0x7C, 0x24,
    0x0D, 0x48, 0x89, 0xBC, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x89, 0xB4, 0x24, 0x80, 0x00, 0x00,
    0x00, 0x44, 0x0F, 0xB7, 0x44, 0x24, 0x2D, 0x66, 0x44, 0x89, 0x44, 0x24, 0x38, 0x44, 0x0F, 0xB6,
    0x44, 0x24, 0x2F, 0x44, 0x88, 0x44, 0x24, 0x3A, 0x44, 0x0F, 0xB6, 0x44, 0x24, 0x30, 0x48, 0x89,
    0x74, 0x24, 0x48, 0x48, 0x89, 0x7C, 0x24, 0x50, 0x48, 0x89, 0x54, 0x24, 0x58, 0x48, 0x89, 0x4C,
    0x24, 0x60, 0x48, 0x89, 0x44, 0x24, 0x68] ++ bytes_l124f20_1

theorem code_l124f20 : ∀ x ∈ codeRange 0x124f20 bytes_l124f20, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x24f20 119 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l124f20_1

@[cfg_block] def b_l124fb4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124fb4 (xorR32R32Effect 0x124fb4 2 5 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 5] []) (.reg (.gpr 5))) #v[5, 5]
    (.letOp (n := 54) (.exec 0x124fb4 (fun s => s.RIP = 0x124fb4) (xorR32R32Effect 0x124fb4 2 5 5) (Reg.operands [.gpr 5, .gpr 5] [])) #v[5, 5]
    (.terminate (.br ⟨.l1252fb, RegMap.args [(3, 3), (4, 4), (5, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l124fb4 : List UInt8 :=
  [0x31, 0xED, 0xE9, 0x40, 0x03, 0x00, 0x00]

theorem code_l124fb4 : ∀ x ∈ codeRange 0x124fb4 bytes_l124fb4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24fb4 7 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l124fbb : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x124fbb (movR32M32LowEffect 0x124fbb 1 (.sib 4 none 0 (.d8 0x34))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x124fbb (LoadPre 0x124fbb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x124fbb + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x124fbb 1 (.sib 4 none 0 (.d8 0x34))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x124fbf (StorePre 0x124fbf 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7c)) s (0x124fbf + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x124fbf 1 (.sib 4 none 0 (.d8 0x7c))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x124fc3 (movR64M64Effect 0x124fc3 1 (.sib 4 none 0 (.d8 0x2c))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 57) (.exec 0x124fc3 (LoadPre 0x124fc3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x124fc3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124fc3 1 (.sib 4 none 0 (.d8 0x2c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x124fc8 (StorePre 0x124fc8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x74)) s (0x124fc8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x124fc8 1 (.sib 4 none 0 (.d8 0x74))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x124fcd (movR64M64Effect 0x124fcd 1 (.sib 4 none 0 (.d8 0x24))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 60) (.exec 0x124fcd (LoadPre 0x124fcd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x124fcd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124fcd 1 (.sib 4 none 0 (.d8 0x24))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x124fd2 (StorePre 0x124fd2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6c)) s (0x124fd2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x124fd2 1 (.sib 4 none 0 (.d8 0x6c))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x124fd7 (movR64M64Effect 0x124fd7 1 (.sib 4 none 0 (.d8 0x14))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 63) (.exec 0x124fd7 (LoadPre 0x124fd7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x124fd7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124fd7 1 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x124fdc (movR64M64Effect 0x124fdc 2 (.sib 4 none 0 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 65) (.exec 0x124fdc (LoadPre 0x124fdc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x124fdc + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124fdc 2 (.sib 4 none 0 (.d8 0x1c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x124fe1 (StorePre 0x124fe1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x64)) s (0x124fe1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x124fe1 2 (.sib 4 none 0 (.d8 0x64))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x124fe6 (StorePre 0x124fe6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5c)) s (0x124fe6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x124fe6 1 (.sib 4 none 0 (.d8 0x5c))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x124feb (movR64M64Effect 0x124feb 1 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 69) (.exec 0x124feb (LoadPre 0x124feb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x124feb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124feb 1 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.out 0x124ff0 (movR64M64Effect 0x124ff0 2 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 71) (.exec 0x124ff0 (LoadPre 0x124ff0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x124ff0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124ff0 2 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.exec 0x124ff5 (StorePre 0x124ff5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4c)) s (0x124ff5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x124ff5 1 (.sib 4 none 0 (.d8 0x4c))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[68, 4]
    (.letOp (n := 73) (.exec 0x124ffa (StorePre 0x124ffa 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x54)) s (0x124ffa + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x124ffa 2 (.sib 4 none 0 (.d8 0x54))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[70, 4]
    (.terminate (.br ⟨.l125045, RegMap.args [(0, 0), (1, 68), (2, 70), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)] 74⟩))))))))))))))))))))))

def bytes_l124fbb : List UInt8 :=
  [0x8B, 0x4C, 0x24, 0x34, 0x89, 0x4C, 0x24, 0x7C, 0x48, 0x8B, 0x4C, 0x24, 0x2C, 0x48, 0x89, 0x4C,
    0x24, 0x74, 0x48, 0x8B, 0x4C, 0x24, 0x24, 0x48, 0x89, 0x4C, 0x24, 0x6C, 0x48, 0x8B, 0x4C, 0x24,
    0x14, 0x48, 0x8B, 0x54, 0x24, 0x1C, 0x48, 0x89, 0x54, 0x24, 0x64, 0x48, 0x89, 0x4C, 0x24, 0x5C,
    0x48, 0x8B, 0x4C, 0x24, 0x38, 0x48, 0x8B, 0x54, 0x24, 0x40, 0x48, 0x89, 0x4C, 0x24, 0x4C, 0x48,
    0x89, 0x54, 0x24, 0x54, 0xEB, 0x44]

theorem code_l124fbb : ∀ x ∈ codeRange 0x124fbb bytes_l124fbb, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24fbb 70 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l125001 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x125001 (movR64M64Effect 0x125001 1 (.sib 4 none 0 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x125001 (LoadPre 0x125001 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x125001 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125001 1 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x125006 (movR64M64Effect 0x125006 2 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 56) (.exec 0x125006 (LoadPre 0x125006 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x125006 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125006 2 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x12500b (StorePre 0x12500b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x54)) s (0x12500b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12500b 2 (.sib 4 none 0 (.d8 0x54))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 58) (.out 0x125010 (movR64M64Effect 0x125010 2 (.sib 4 none 0 (.d8 0x14))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 59) (.exec 0x125010 (LoadPre 0x125010 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x125010 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125010 2 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.exec 0x125015 (StorePre 0x125015 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5c)) s (0x125015 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125015 2 (.sib 4 none 0 (.d8 0x5c))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[58, 4]
    (.letOp (n := 61) (.out 0x12501a (movR64M64Effect 0x12501a 2 (.sib 4 none 0 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 62) (.exec 0x12501a (LoadPre 0x12501a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x12501a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12501a 2 (.sib 4 none 0 (.d8 0x1c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x12501f (StorePre 0x12501f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x64)) s (0x12501f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12501f 2 (.sib 4 none 0 (.d8 0x64))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.out 0x125024 (movR64M64Effect 0x125024 2 (.sib 4 none 0 (.d8 0x24))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 65) (.exec 0x125024 (LoadPre 0x125024 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x125024 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125024 2 (.sib 4 none 0 (.d8 0x24))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x125029 (StorePre 0x125029 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6c)) s (0x125029 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125029 2 (.sib 4 none 0 (.d8 0x6c))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.out 0x12502e (movR64M64Effect 0x12502e 2 (.sib 4 none 0 (.d8 0x2c))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 68) (.exec 0x12502e (LoadPre 0x12502e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x12502e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12502e 2 (.sib 4 none 0 (.d8 0x2c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.exec 0x125033 (StorePre 0x125033 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x74)) s (0x125033 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125033 2 (.sib 4 none 0 (.d8 0x74))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[67, 4]
    (.letOp (n := 70) (.out 0x125038 (movR32M32LowEffect 0x125038 2 (.sib 4 none 0 (.d8 0x34))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 71) (.exec 0x125038 (LoadPre 0x125038 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x125038 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x125038 2 (.sib 4 none 0 (.d8 0x34))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.exec 0x12503c (StorePre 0x12503c 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7c)) s (0x12503c + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x12503c 2 (.sib 4 none 0 (.d8 0x7c))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[70, 4]
    (.letOp (n := 73) (.exec 0x125040 (StorePre 0x125040 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4c)) s (0x125040 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125040 1 (.sib 4 none 0 (.d8 0x4c))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[53, 4]
    (.terminate (.br ⟨.l125045, RegMap.args [(0, 0), (1, 53), (2, 70), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)] 74⟩))))))))))))))))))))))

def bytes_l125001 : List UInt8 :=
  [0x48, 0x8B, 0x4C, 0x24, 0x04, 0x48, 0x8B, 0x54, 0x24, 0x0C, 0x48, 0x89, 0x54, 0x24, 0x54, 0x48,
    0x8B, 0x54, 0x24, 0x14, 0x48, 0x89, 0x54, 0x24, 0x5C, 0x48, 0x8B, 0x54, 0x24, 0x1C, 0x48, 0x89,
    0x54, 0x24, 0x64, 0x48, 0x8B, 0x54, 0x24, 0x24, 0x48, 0x89, 0x54, 0x24, 0x6C, 0x48, 0x8B, 0x54,
    0x24, 0x2C, 0x48, 0x89, 0x54, 0x24, 0x74, 0x8B, 0x54, 0x24, 0x34, 0x89, 0x54, 0x24, 0x7C, 0x48,
    0x89, 0x4C, 0x24, 0x4C]

theorem code_l125001 : ∀ x ∈ codeRange 0x125001 bytes_l125001, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x25001 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l125045 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x125045 (movzxR32M8Effect 0x125045 5 1 (.sib 4 none 0 (.d8 0x4c))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x125045 (LoadPre 0x125045 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4c)) s (0x125045 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x125045 5 1 (.sib 4 none 0 (.d8 0x4c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x12504a (movR32M32LowEffect 0x12504a 2 (.sib 4 none 0 (.d8 0x7c))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 56) (.exec 0x12504a (LoadPre 0x12504a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7c)) s (0x12504a + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x12504a 2 (.sib 4 none 0 (.d8 0x7c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x12504e (StorePre 0x12504e 3 (fun s => AddrMode.addr (.base 3 (.d8 0x3c)) s (0x12504e + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x12504e 2 (.base 3 (.d8 0x3c))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[55, 3]
    (.letOp (n := 58) (.out 0x125051 (movR64M64Effect 0x125051 2 (.sib 4 none 0 (.d8 0x75))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 59) (.exec 0x125051 (LoadPre 0x125051 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x75)) s (0x125051 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125051 2 (.sib 4 none 0 (.d8 0x75))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.exec 0x125056 (StorePre 0x125056 4 (fun s => AddrMode.addr (.base 3 (.d8 0x35)) s (0x125056 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125056 2 (.base 3 (.d8 0x35))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[58, 3]
    (.letOp (n := 61) (.out 0x12505a (movR64M64Effect 0x12505a 2 (.sib 4 none 0 (.d8 0x6d))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 62) (.exec 0x12505a (LoadPre 0x12505a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6d)) s (0x12505a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12505a 2 (.sib 4 none 0 (.d8 0x6d))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x12505f (StorePre 0x12505f 4 (fun s => AddrMode.addr (.base 3 (.d8 0x2d)) s (0x12505f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12505f 2 (.base 3 (.d8 0x2d))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 64) (.out 0x125063 (movR64M64Effect 0x125063 2 (.sib 4 none 0 (.d8 0x65))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 65) (.exec 0x125063 (LoadPre 0x125063 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x65)) s (0x125063 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125063 2 (.sib 4 none 0 (.d8 0x65))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x125068 (StorePre 0x125068 4 (fun s => AddrMode.addr (.base 3 (.d8 0x25)) s (0x125068 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125068 2 (.base 3 (.d8 0x25))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[64, 3]
    (.letOp (n := 67) (.out 0x12506c (movR64M64Effect 0x12506c 2 (.sib 4 none 0 (.d8 0x5d))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 68) (.exec 0x12506c (LoadPre 0x12506c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5d)) s (0x12506c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12506c 2 (.sib 4 none 0 (.d8 0x5d))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.exec 0x125071 (StorePre 0x125071 4 (fun s => AddrMode.addr (.base 3 (.d8 0x1d)) s (0x125071 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125071 2 (.base 3 (.d8 0x1d))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[67, 3]
    (.letOp (n := 70) (.out 0x125075 (movR64M64Effect 0x125075 2 (.sib 4 none 0 (.d8 0x55))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 71) (.exec 0x125075 (LoadPre 0x125075 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x55)) s (0x125075 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125075 2 (.sib 4 none 0 (.d8 0x55))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.exec 0x12507a (StorePre 0x12507a 4 (fun s => AddrMode.addr (.base 3 (.d8 0x15)) s (0x12507a + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12507a 2 (.base 3 (.d8 0x15))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[70, 3]
    (.letOp (n := 73) (.out 0x12507e (movR64M64Effect 0x12507e 2 (.sib 4 none 0 (.d8 0x4d))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 74) (.exec 0x12507e (LoadPre 0x12507e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4d)) s (0x12507e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12507e 2 (.sib 4 none 0 (.d8 0x4d))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.exec 0x125083 (StorePre 0x125083 4 (fun s => AddrMode.addr (.base 3 (.d8 0xd)) s (0x125083 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125083 2 (.base 3 (.d8 0xd))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[73, 3]
    (.letOp (n := 76) (.exec 0x125087 (StorePre 0x125087 3 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x125087 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x125087 0 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (.letOp (n := 77) (.exec 0x12508a (StorePre 0x12508a 3 (fun s => AddrMode.addr (.base 3 (.d8 0xc)) s (0x12508a + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x12508a 3 1 (.base 3 (.d8 0xc))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[53, 3]
    (.terminate (.br ⟨.l12508d, RegMap.args [(0, 0), (1, 53), (2, 73), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)] 78⟩))))))))))))))))))))))))))

def bytes_l125045 : List UInt8 :=
  [0x0F, 0xB6, 0x4C, 0x24, 0x4C, 0x8B, 0x54, 0x24, 0x7C, 0x89, 0x53, 0x3C, 0x48, 0x8B, 0x54, 0x24,
    0x75, 0x48, 0x89, 0x53, 0x35, 0x48, 0x8B, 0x54, 0x24, 0x6D, 0x48, 0x89, 0x53, 0x2D, 0x48, 0x8B,
    0x54, 0x24, 0x65, 0x48, 0x89, 0x53, 0x25, 0x48, 0x8B, 0x54, 0x24, 0x5D, 0x48, 0x89, 0x53, 0x1D,
    0x48, 0x8B, 0x54, 0x24, 0x55, 0x48, 0x89, 0x53, 0x15, 0x48, 0x8B, 0x54, 0x24, 0x4D, 0x48, 0x89,
    0x53, 0x0D, 0x89, 0x43, 0x08, 0x88, 0x4B, 0x0C]

theorem code_l125045 : ∀ x ∈ codeRange 0x125045 bytes_l125045, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x25045 72 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12508d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12508d (movR32Imm32Effect 0x12508d 5 0 0x1) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 54) (.exec 0x12508d (fun s => s.RIP = 0x12508d) (movR32Imm32Effect 0x12508d 5 0 0x1) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l125092, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l12508d : List UInt8 :=
  [0xB8, 0x01, 0x00, 0x00, 0x00]

theorem code_l12508d : ∀ x ∈ codeRange 0x12508d bytes_l12508d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2508d 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l125092 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x125092 (StorePre 0x125092 3 (fun s => AddrMode.addr (.base 3 .none) s (0x125092 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x125092 0 (.base 3 .none)) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (.letOp (n := 54) (.out 0x125095 (movR64R64Effect 0x125095 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 55) (.exec 0x125095 (fun s => s.RIP = 0x125095) (movR64R64Effect 0x125095 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 56) (.out 0x125098 (addR64Imm32Effect 0x125098 4 0xd0) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 57) (.exec 0x125098 (fun s => s.RIP = 0x125098) (addR64Imm32Effect 0x125098 4 0xd0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.out 0x12509f (popR64Effect 0x12509f 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[56]
    (.letOp (n := 59) (.out 0x12509f (popR64Effect 0x12509f 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[56]
    (.letOp (n := 60) (.exec 0x12509f (PopPre 0x12509f) (popR64Effect 0x12509f 1 3) (Reg.operands [.gpr 4] [])) #v[56]
    (.letOp (n := 61) (.out 0x1250a0 (popR64Effect 0x1250a0 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[59]
    (.letOp (n := 62) (.out 0x1250a0 (popR64Effect 0x1250a0 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 63) (.exec 0x1250a0 (PopPre 0x1250a0) (popR64Effect 0x1250a0 2 12) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 64) (.out 0x1250a2 (popR64Effect 0x1250a2 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[62]
    (.letOp (n := 65) (.out 0x1250a2 (popR64Effect 0x1250a2 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[62]
    (.letOp (n := 66) (.exec 0x1250a2 (PopPre 0x1250a2) (popR64Effect 0x1250a2 2 14) (Reg.operands [.gpr 4] [])) #v[62]
    (.letOp (n := 67) (.out 0x1250a4 (popR64Effect 0x1250a4 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[65]
    (.letOp (n := 68) (.out 0x1250a4 (popR64Effect 0x1250a4 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 69) (.exec 0x1250a4 (PopPre 0x1250a4) (popR64Effect 0x1250a4 2 15) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 70) (.out 0x1250a6 (popR64Effect 0x1250a6 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[68]
    (.letOp (n := 71) (.out 0x1250a6 (popR64Effect 0x1250a6 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[68]
    (.letOp (n := 72) (.exec 0x1250a6 (PopPre 0x1250a6) (popR64Effect 0x1250a6 1 5) (Reg.operands [.gpr 4] [])) #v[68]
    (.letOp (n := 73) (.out 0x1250a7 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[71]
    (.letOp (n := 74) (.out 0x1250a7 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[71]
    (.letOp (n := 75) (.exec 0x1250a7 (RetPre 0x1250a7) (retEffect) (Reg.operands [.gpr 4] [])) #v[71]
    (.terminate (.ret (RegMap.args [(0, 54), (1, 1), (2, 2), (3, 58), (4, 74), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 13), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 76) (some ⟨73, by decide⟩)))))))))))))))))))))))))

def bytes_l125092 : List UInt8 :=
  [0x48, 0x89, 0x03, 0x48, 0x89, 0xD8, 0x48, 0x81, 0xC4, 0xD0, 0x00, 0x00, 0x00, 0x5B, 0x41, 0x5C,
    0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l125092 : ∀ x ∈ codeRange 0x125092 bytes_l125092, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x25092 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1250a8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1250a8 (StorePre 0x1250a8 5 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x1250a8 + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x1250a8 (.base 14 (.d8 0x20)) 0x1) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 54) (.out 0x1250ad (movR32M32Effect 0x1250ad 0 (.base 14 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[14]
    (.letOp (n := 55) (.exec 0x1250ad (LoadPre 0x1250ad (fun s => AddrMode.addr (.base 14 (.d8 0x1c)) s (0x1250ad + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x1250ad 0 (.base 14 (.d8 0x1c))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 56) (.exec 0x1250b1 (StorePre 0x1250b1 7 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x1250b1 + BitVec.ofNat 64 7)) 4) (movM32Imm32Effect 0x1250b1 7 (.base 3 (.d8 0x8)) 0x1) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 57) (.exec 0x1250b8 (StorePre 0x1250b8 3 (fun s => AddrMode.addr (.base 3 (.d8 0xc)) s (0x1250b8 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x1250b8 0 (.base 3 (.d8 0xc))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[54, 3]
    (.letOp (n := 58) (.exec 0x1250bb (StorePre 0x1250bb 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x1250bb + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x1250bb (.base 3 (.d8 0x10)) 0x15) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 59) (.exec 0x1250bf (StorePre 0x1250bf 4 (fun s => AddrMode.addr (.base 3 (.d8 0x14)) s (0x1250bf + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x1250bf (.base 3 (.d8 0x14)) 0x1) (Reg.operands [.gpr 3] [])) #v[3]
    (.terminate (.br ⟨.l12508d, RegMap.args [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l1250a8 : List UInt8 :=
  [0x41, 0xC6, 0x46, 0x20, 0x01, 0x41, 0x8B, 0x46, 0x1C, 0xC7, 0x43, 0x08, 0x01, 0x00, 0x00, 0x00,
    0x89, 0x43, 0x0C, 0xC6, 0x43, 0x10, 0x15, 0xC6, 0x43, 0x14, 0x01, 0xEB, 0xC8]

theorem code_l1250a8 : ∀ x ∈ codeRange 0x1250a8 bytes_l1250a8, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x250a8 29 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1250c5 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1250c5 (movR32M32LowEffect 0x1250c5 1 (.sib 4 none 0 (.d8 0x34))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x1250c5 (LoadPre 0x1250c5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x1250c5 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1250c5 1 (.sib 4 none 0 (.d8 0x34))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x1250c9 (StorePre 0x1250c9 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7c)) s (0x1250c9 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x1250c9 1 (.sib 4 none 0 (.d8 0x7c))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x1250cd (movR64M64Effect 0x1250cd 1 (.sib 4 none 0 (.d8 0x2c))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 57) (.exec 0x1250cd (LoadPre 0x1250cd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x1250cd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1250cd 1 (.sib 4 none 0 (.d8 0x2c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x1250d2 (StorePre 0x1250d2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x74)) s (0x1250d2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1250d2 1 (.sib 4 none 0 (.d8 0x74))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x1250d7 (movR64M64Effect 0x1250d7 1 (.sib 4 none 0 (.d8 0x24))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 60) (.exec 0x1250d7 (LoadPre 0x1250d7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x1250d7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1250d7 1 (.sib 4 none 0 (.d8 0x24))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x1250dc (StorePre 0x1250dc 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6c)) s (0x1250dc + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1250dc 1 (.sib 4 none 0 (.d8 0x6c))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x1250e1 (movR64M64Effect 0x1250e1 1 (.sib 4 none 0 (.d8 0x14))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 63) (.exec 0x1250e1 (LoadPre 0x1250e1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x1250e1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1250e1 1 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x1250e6 (movR64M64Effect 0x1250e6 2 (.sib 4 none 0 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 65) (.exec 0x1250e6 (LoadPre 0x1250e6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x1250e6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1250e6 2 (.sib 4 none 0 (.d8 0x1c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x1250eb (StorePre 0x1250eb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x64)) s (0x1250eb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1250eb 2 (.sib 4 none 0 (.d8 0x64))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x1250f0 (StorePre 0x1250f0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5c)) s (0x1250f0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1250f0 1 (.sib 4 none 0 (.d8 0x5c))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x1250f5 (movR64M64Effect 0x1250f5 1 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 69) (.exec 0x1250f5 (LoadPre 0x1250f5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1250f5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1250f5 1 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.out 0x1250fa (movR64M64Effect 0x1250fa 2 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 71) (.exec 0x1250fa (LoadPre 0x1250fa (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1250fa + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1250fa 2 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.exec 0x1250ff (StorePre 0x1250ff 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4c)) s (0x1250ff + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1250ff 1 (.sib 4 none 0 (.d8 0x4c))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[68, 4]
    (.letOp (n := 73) (.exec 0x125104 (StorePre 0x125104 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x54)) s (0x125104 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125104 2 (.sib 4 none 0 (.d8 0x54))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[70, 4]
    (.terminate (.br ⟨.l12514f, RegMap.args [(0, 0), (1, 68), (2, 70), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)] 74⟩))))))))))))))))))))))

def bytes_l1250c5 : List UInt8 :=
  [0x8B, 0x4C, 0x24, 0x34, 0x89, 0x4C, 0x24, 0x7C, 0x48, 0x8B, 0x4C, 0x24, 0x2C, 0x48, 0x89, 0x4C,
    0x24, 0x74, 0x48, 0x8B, 0x4C, 0x24, 0x24, 0x48, 0x89, 0x4C, 0x24, 0x6C, 0x48, 0x8B, 0x4C, 0x24,
    0x14, 0x48, 0x8B, 0x54, 0x24, 0x1C, 0x48, 0x89, 0x54, 0x24, 0x64, 0x48, 0x89, 0x4C, 0x24, 0x5C,
    0x48, 0x8B, 0x4C, 0x24, 0x38, 0x48, 0x8B, 0x54, 0x24, 0x40, 0x48, 0x89, 0x4C, 0x24, 0x4C, 0x48,
    0x89, 0x54, 0x24, 0x54, 0xEB, 0x44]

theorem code_l1250c5 : ∀ x ∈ codeRange 0x1250c5 bytes_l1250c5, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x250c5 70 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12510b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12510b (movR64M64Effect 0x12510b 1 (.sib 4 none 0 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x12510b (LoadPre 0x12510b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x12510b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12510b 1 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x125110 (movR64M64Effect 0x125110 2 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 56) (.exec 0x125110 (LoadPre 0x125110 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x125110 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125110 2 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x125115 (StorePre 0x125115 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x54)) s (0x125115 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125115 2 (.sib 4 none 0 (.d8 0x54))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 58) (.out 0x12511a (movR64M64Effect 0x12511a 2 (.sib 4 none 0 (.d8 0x14))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 59) (.exec 0x12511a (LoadPre 0x12511a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x12511a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12511a 2 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.exec 0x12511f (StorePre 0x12511f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5c)) s (0x12511f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12511f 2 (.sib 4 none 0 (.d8 0x5c))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[58, 4]
    (.letOp (n := 61) (.out 0x125124 (movR64M64Effect 0x125124 2 (.sib 4 none 0 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 62) (.exec 0x125124 (LoadPre 0x125124 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x125124 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125124 2 (.sib 4 none 0 (.d8 0x1c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x125129 (StorePre 0x125129 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x64)) s (0x125129 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125129 2 (.sib 4 none 0 (.d8 0x64))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.out 0x12512e (movR64M64Effect 0x12512e 2 (.sib 4 none 0 (.d8 0x24))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 65) (.exec 0x12512e (LoadPre 0x12512e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x12512e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12512e 2 (.sib 4 none 0 (.d8 0x24))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x125133 (StorePre 0x125133 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6c)) s (0x125133 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125133 2 (.sib 4 none 0 (.d8 0x6c))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.out 0x125138 (movR64M64Effect 0x125138 2 (.sib 4 none 0 (.d8 0x2c))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 68) (.exec 0x125138 (LoadPre 0x125138 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x125138 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125138 2 (.sib 4 none 0 (.d8 0x2c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.exec 0x12513d (StorePre 0x12513d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x74)) s (0x12513d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12513d 2 (.sib 4 none 0 (.d8 0x74))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[67, 4]
    (.letOp (n := 70) (.out 0x125142 (movR32M32LowEffect 0x125142 2 (.sib 4 none 0 (.d8 0x34))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 71) (.exec 0x125142 (LoadPre 0x125142 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x125142 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x125142 2 (.sib 4 none 0 (.d8 0x34))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.exec 0x125146 (StorePre 0x125146 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7c)) s (0x125146 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x125146 2 (.sib 4 none 0 (.d8 0x7c))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[70, 4]
    (.letOp (n := 73) (.exec 0x12514a (StorePre 0x12514a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4c)) s (0x12514a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12514a 1 (.sib 4 none 0 (.d8 0x4c))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[53, 4]
    (.terminate (.br ⟨.l12514f, RegMap.args [(0, 0), (1, 53), (2, 70), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)] 74⟩))))))))))))))))))))))

def bytes_l12510b : List UInt8 :=
  [0x48, 0x8B, 0x4C, 0x24, 0x04, 0x48, 0x8B, 0x54, 0x24, 0x0C, 0x48, 0x89, 0x54, 0x24, 0x54, 0x48,
    0x8B, 0x54, 0x24, 0x14, 0x48, 0x89, 0x54, 0x24, 0x5C, 0x48, 0x8B, 0x54, 0x24, 0x1C, 0x48, 0x89,
    0x54, 0x24, 0x64, 0x48, 0x8B, 0x54, 0x24, 0x24, 0x48, 0x89, 0x54, 0x24, 0x6C, 0x48, 0x8B, 0x54,
    0x24, 0x2C, 0x48, 0x89, 0x54, 0x24, 0x74, 0x8B, 0x54, 0x24, 0x34, 0x89, 0x54, 0x24, 0x7C, 0x48,
    0x89, 0x4C, 0x24, 0x4C]

theorem code_l12510b : ∀ x ∈ codeRange 0x12510b bytes_l12510b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2510b 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12514f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12514f (movR32M32LowEffect 0x12514f 1 (.sib 4 none 0 (.d8 0x4c))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x12514f (LoadPre 0x12514f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4c)) s (0x12514f + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x12514f 1 (.sib 4 none 0 (.d8 0x4c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x125153 (movR64M64Effect 0x125153 2 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 56) (.exec 0x125153 (LoadPre 0x125153 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x125153 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125153 2 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x125158 (movR64M64Effect 0x125158 6 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 58) (.exec 0x125158 (LoadPre 0x125158 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x125158 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125158 6 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x12515d (movR64M64Effect 0x12515d 7 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 60) (.exec 0x12515d (LoadPre 0x12515d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x12515d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12515d 7 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x125162 (StorePre 0x125162 4 (fun s => AddrMode.addr (.base 3 (.d8 0x38)) s (0x125162 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125162 7 (.base 3 (.d8 0x38))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[59, 3]
    (.letOp (n := 62) (.out 0x125166 (movR64M64Effect 0x125166 7 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 63) (.exec 0x125166 (LoadPre 0x125166 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x125166 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125166 7 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x12516b (StorePre 0x12516b 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x12516b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12516b 7 (.base 3 (.d8 0x30))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[62, 3]
    (.letOp (n := 65) (.out 0x12516f (movR64M64Effect 0x12516f 7 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 66) (.exec 0x12516f (LoadPre 0x12516f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x12516f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12516f 7 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x125174 (StorePre 0x125174 4 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x125174 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125174 7 (.base 3 (.d8 0x28))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[65, 3]
    (.letOp (n := 68) (.out 0x125178 (movR64M64Effect 0x125178 7 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 69) (.exec 0x125178 (LoadPre 0x125178 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x125178 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125178 7 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.exec 0x12517d (StorePre 0x12517d 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x12517d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12517d 7 (.base 3 (.d8 0x20))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[68, 3]
    (.letOp (n := 71) (.exec 0x125181 (StorePre 0x125181 3 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x125181 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x125181 0 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (.letOp (n := 72) (.exec 0x125184 (StorePre 0x125184 3 (fun s => AddrMode.addr (.base 3 (.d8 0xc)) s (0x125184 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x125184 1 (.base 3 (.d8 0xc))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[53, 3]
    (.letOp (n := 73) (.exec 0x125187 (StorePre 0x125187 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x125187 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125187 2 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[55, 3]
    (.letOp (n := 74) (.exec 0x12518b (StorePre 0x12518b 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x12518b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12518b 6 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[57, 3]
    (.terminate (.br ⟨.l12508d, RegMap.args [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩)))))))))))))))))))))))

def bytes_l12514f : List UInt8 :=
  [0x8B, 0x4C, 0x24, 0x4C, 0x48, 0x8B, 0x54, 0x24, 0x50, 0x48, 0x8B, 0x74, 0x24, 0x58, 0x48, 0x8B,
    0x7C, 0x24, 0x78, 0x48, 0x89, 0x7B, 0x38, 0x48, 0x8B, 0x7C, 0x24, 0x70, 0x48, 0x89, 0x7B, 0x30,
    0x48, 0x8B, 0x7C, 0x24, 0x68, 0x48, 0x89, 0x7B, 0x28, 0x48, 0x8B, 0x7C, 0x24, 0x60, 0x48, 0x89,
    0x7B, 0x20, 0x89, 0x43, 0x08, 0x89, 0x4B, 0x0C, 0x48, 0x89, 0x53, 0x10, 0x48, 0x89, 0x73, 0x18,
    0xE9, 0xF9, 0xFE, 0xFF, 0xFF]

theorem code_l12514f : ∀ x ∈ codeRange 0x12514f bytes_l12514f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2514f 69 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l125194_2 : Block Op Label signature Reg.count 115 :=
  .letOp (n := 115) (.exec 0x12528a (StorePre 0x12528a 4 (fun s => AddrMode.addr (.base 3 (.d8 0x1d)) s (0x12528a + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12528a 7 (.base 3 (.d8 0x1d))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[113, 3]
    (.letOp (n := 116) (.out 0x12528e (movR64M64Effect 0x12528e 7 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 117) (.exec 0x12528e (LoadPre 0x12528e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x12528e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x12528e 7 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 118) (.out 0x125296 (movR64M64Effect 0x125296 8 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 119) (.exec 0x125296 (LoadPre 0x125296 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x125296 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125296 8 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 120) (.exec 0x12529e (StorePre 0x12529e 4 (fun s => AddrMode.addr (.base 3 (.d8 0x15)) s (0x12529e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12529e 8 (.base 3 (.d8 0x15))) (Reg.operands [.gpr 8, .gpr 3] [])) #v[118, 3]
    (.letOp (n := 121) (.exec 0x1252a2 (StorePre 0x1252a2 4 (fun s => AddrMode.addr (.base 3 (.d8 0xd)) s (0x1252a2 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1252a2 7 (.base 3 (.d8 0xd))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[116, 3]
    (.letOp (n := 122) (.exec 0x1252a6 (StorePre 0x1252a6 3 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x1252a6 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x1252a6 0 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (.letOp (n := 123) (.exec 0x1252a9 (StorePre 0x1252a9 3 (fun s => AddrMode.addr (.base 3 (.d8 0xc)) s (0x1252a9 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x1252a9 3 1 (.base 3 (.d8 0xc))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[53, 3]
    (.letOp (n := 124) (.exec 0x1252ac (StorePre 0x1252ac 3 (fun s => AddrMode.addr (.base 3 (.d8 0x38)) s (0x1252ac + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x1252ac 3 2 (.base 3 (.d8 0x38))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[76, 3]
    (.letOp (n := 125) (.exec 0x1252af (StorePre 0x1252af 3 (fun s => AddrMode.addr (.base 3 (.d8 0x3c)) s (0x1252af + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x1252af 6 (.base 3 (.d8 0x3c))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[84, 3]
    (.terminate (.br ⟨.l12508d, RegMap.args [(0, 0), (1, 53), (2, 76), (3, 3), (4, 4), (6, 84), (7, 116), (8, 118), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)] 126⟩))))))))))))

def bytes_l125194_2 : List UInt8 :=
  [0x48, 0x89, 0x7B, 0x1D, 0x48, 0x8B, 0xBC, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x4C, 0x8B, 0x84, 0x24,
    0xB0, 0x00, 0x00, 0x00, 0x4C, 0x89, 0x43, 0x15, 0x48, 0x89, 0x7B, 0x0D, 0x89, 0x43, 0x08, 0x88,
    0x4B, 0x0C, 0x88, 0x53, 0x38, 0x89, 0x73, 0x3C, 0xE9, 0xD6, 0xFD, 0xFF, 0xFF]

theorem code_l125194_2 : ∀ x ∈ codeRange 0x12528a bytes_l125194_2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2528a 45 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l125194_1 : Block Op Label signature Reg.count 84 :=
  .letOp (n := 84) (.out 0x125204 (movR32M32LowEffect 0x125204 6 (.sib 4 none 0 (.d8 0x34))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 85) (.exec 0x125204 (LoadPre 0x125204 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x125204 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x125204 6 (.sib 4 none 0 (.d8 0x34))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 86) (.out 0x125208 (movR64M64Effect 0x125208 7 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 87) (.exec 0x125208 (LoadPre 0x125208 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x125208 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125208 7 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 88) (.exec 0x125210 (StorePre 0x125210 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x125210 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x125210 7 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[86, 4]
    (.letOp (n := 89) (.out 0x125218 (movR64M64Effect 0x125218 7 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 90) (.exec 0x125218 (LoadPre 0x125218 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x125218 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125218 7 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 91) (.exec 0x125220 (StorePre 0x125220 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x125220 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x125220 7 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[89, 4]
    (.letOp (n := 92) (.out 0x125228 (movR64M64Effect 0x125228 7 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 93) (.exec 0x125228 (LoadPre 0x125228 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x125228 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125228 7 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 94) (.exec 0x125230 (StorePre 0x125230 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x125230 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x125230 7 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[92, 4]
    (.letOp (n := 95) (.out 0x125238 (movR64M64Effect 0x125238 7 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 96) (.exec 0x125238 (LoadPre 0x125238 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x125238 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125238 7 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 97) (.out 0x125240 (movR64M64Effect 0x125240 8 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 98) (.exec 0x125240 (LoadPre 0x125240 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x125240 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125240 8 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 99) (.exec 0x125248 (StorePre 0x125248 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x125248 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x125248 8 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[97, 4]
    (.letOp (n := 100) (.exec 0x125250 (StorePre 0x125250 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x125250 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x125250 7 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[95, 4]
    (.letOp (n := 101) (.out 0x125258 (movzxR32M8Effect 0x125258 5 7 (.sib 4 none 0 (.d8 0x3a))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 102) (.exec 0x125258 (LoadPre 0x125258 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3a)) s (0x125258 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x125258 5 7 (.sib 4 none 0 (.d8 0x3a))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 103) (.exec 0x12525d (StorePre 0x12525d 4 (fun s => AddrMode.addr (.base 3 (.d8 0x37)) s (0x12525d + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x12525d 4 7 (.base 3 (.d8 0x37))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[101, 3]
    (.letOp (n := 104) (.out 0x125261 (movzxR32M16Effect 0x125261 5 7 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 105) (.exec 0x125261 (LoadPre 0x125261 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x125261 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x125261 5 7 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 106) (.exec 0x125266 (StorePre 0x125266 4 (fun s => AddrMode.addr (.base 3 (.d8 0x35)) s (0x125266 + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x125266 4 7 (.base 3 (.d8 0x35))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[104, 3]
    (.letOp (n := 107) (.out 0x12526a (movR64M64Effect 0x12526a 7 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 108) (.exec 0x12526a (LoadPre 0x12526a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x12526a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x12526a 7 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 109) (.exec 0x125272 (StorePre 0x125272 4 (fun s => AddrMode.addr (.base 3 (.d8 0x2d)) s (0x125272 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125272 7 (.base 3 (.d8 0x2d))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[107, 3]
    (.letOp (n := 110) (.out 0x125276 (movR64M64Effect 0x125276 7 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 111) (.exec 0x125276 (LoadPre 0x125276 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x125276 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125276 7 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 112) (.exec 0x12527e (StorePre 0x12527e 4 (fun s => AddrMode.addr (.base 3 (.d8 0x25)) s (0x12527e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12527e 7 (.base 3 (.d8 0x25))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[110, 3]
    (.letOp (n := 113) (.out 0x125282 (movR64M64Effect 0x125282 7 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 114) (.exec 0x125282 (LoadPre 0x125282 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x125282 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125282 7 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l125194_2)))))))))))))))))))))))))))))))

def bytes_l125194_1 : List UInt8 :=
  [0x8B, 0x74, 0x24, 0x34, 0x48, 0x8B, 0xBC, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x48, 0x89, 0xBC, 0x24,
    0xC8, 0x00, 0x00, 0x00, 0x48, 0x8B, 0xBC, 0x24, 0x98, 0x00, 0x00, 0x00, 0x48, 0x89, 0xBC, 0x24,
    0xC0, 0x00, 0x00, 0x00, 0x48, 0x8B, 0xBC, 0x24, 0x90, 0x00, 0x00, 0x00, 0x48, 0x89, 0xBC, 0x24,
    0xB8, 0x00, 0x00, 0x00, 0x48, 0x8B, 0xBC, 0x24, 0x80, 0x00, 0x00, 0x00, 0x4C, 0x8B, 0x84, 0x24,
    0x88, 0x00, 0x00, 0x00, 0x4C, 0x89, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x48, 0x89, 0xBC, 0x24,
    0xA8, 0x00, 0x00, 0x00, 0x0F, 0xB6, 0x7C, 0x24, 0x3A, 0x40, 0x88, 0x7B, 0x37, 0x0F, 0xB7, 0x7C,
    0x24, 0x38, 0x66, 0x89, 0x7B, 0x35, 0x48, 0x8B, 0xBC, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x48, 0x89,
    0x7B, 0x2D, 0x48, 0x8B, 0xBC, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x7B, 0x25, 0x48, 0x8B,
    0xBC, 0x24, 0xB8, 0x00, 0x00, 0x00] ++ bytes_l125194_2

theorem code_l125194_1 : ∀ x ∈ codeRange 0x125204 bytes_l125194_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x25204 134 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l125194_2

@[cfg_block] def b_l125194 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x125194 (movzxR32M8Effect 0x125194 5 1 (.sib 4 none 0 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x125194 (LoadPre 0x125194 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x125194 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x125194 5 1 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x125199 (movR64M64Effect 0x125199 2 (.sib 4 none 0 (.d8 0x5))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 56) (.exec 0x125199 (LoadPre 0x125199 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5)) s (0x125199 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125199 2 (.sib 4 none 0 (.d8 0x5))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x12519e (StorePre 0x12519e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x12519e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x12519e 2 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 58) (.out 0x1251a6 (movR64M64Effect 0x1251a6 2 (.sib 4 none 0 (.d8 0xd))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 59) (.exec 0x1251a6 (LoadPre 0x1251a6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xd)) s (0x1251a6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1251a6 2 (.sib 4 none 0 (.d8 0xd))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.exec 0x1251ab (StorePre 0x1251ab 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1251ab + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1251ab 2 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[58, 4]
    (.letOp (n := 61) (.out 0x1251b3 (movR64M64Effect 0x1251b3 2 (.sib 4 none 0 (.d8 0x15))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 62) (.exec 0x1251b3 (LoadPre 0x1251b3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x15)) s (0x1251b3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1251b3 2 (.sib 4 none 0 (.d8 0x15))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x1251b8 (StorePre 0x1251b8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x1251b8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1251b8 2 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.out 0x1251c0 (movR64M64Effect 0x1251c0 2 (.sib 4 none 0 (.d8 0x1d))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 65) (.exec 0x1251c0 (LoadPre 0x1251c0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1d)) s (0x1251c0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1251c0 2 (.sib 4 none 0 (.d8 0x1d))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x1251c5 (StorePre 0x1251c5 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x1251c5 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1251c5 2 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.out 0x1251cd (movR64M64Effect 0x1251cd 2 (.sib 4 none 0 (.d8 0x25))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 68) (.exec 0x1251cd (LoadPre 0x1251cd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x25)) s (0x1251cd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1251cd 2 (.sib 4 none 0 (.d8 0x25))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.exec 0x1251d2 (StorePre 0x1251d2 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x1251d2 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1251d2 2 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[67, 4]
    (.letOp (n := 70) (.out 0x1251da (movzxR32M16Effect 0x1251da 5 2 (.sib 4 none 0 (.d8 0x2d))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 71) (.exec 0x1251da (LoadPre 0x1251da (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2d)) s (0x1251da + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x1251da 5 2 (.sib 4 none 0 (.d8 0x2d))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.exec 0x1251df (StorePre 0x1251df 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1251df + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1251df 5 2 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[70, 4]
    (.letOp (n := 73) (.out 0x1251e4 (movzxR32M8Effect 0x1251e4 5 2 (.sib 4 none 0 (.d8 0x2f))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 74) (.exec 0x1251e4 (LoadPre 0x1251e4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2f)) s (0x1251e4 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1251e4 5 2 (.sib 4 none 0 (.d8 0x2f))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.exec 0x1251e9 (StorePre 0x1251e9 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3a)) s (0x1251e9 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1251e9 4 2 (.sib 4 none 0 (.d8 0x3a))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[73, 4]
    (.letOp (n := 76) (.out 0x1251ed (movzxR32M8Effect 0x1251ed 5 2 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 77) (.exec 0x1251ed (LoadPre 0x1251ed (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1251ed + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1251ed 5 2 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 78) (.out 0x1251f2 (movzxR32M8Effect 0x1251f2 5 6 (.sib 4 none 0 (.d8 0x33))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 79) (.exec 0x1251f2 (LoadPre 0x1251f2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x33)) s (0x1251f2 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1251f2 5 6 (.sib 4 none 0 (.d8 0x33))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 80) (.exec 0x1251f7 (StorePre 0x1251f7 4 (fun s => AddrMode.addr (.base 3 (.d8 0x3b)) s (0x1251f7 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1251f7 4 6 (.base 3 (.d8 0x3b))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[78, 3]
    (.letOp (n := 81) (.out 0x1251fb (movzxR32M16Effect 0x1251fb 5 6 (.sib 4 none 0 (.d8 0x31))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 82) (.exec 0x1251fb (LoadPre 0x1251fb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x31)) s (0x1251fb + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x1251fb 5 6 (.sib 4 none 0 (.d8 0x31))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 83) (.exec 0x125200 (StorePre 0x125200 4 (fun s => AddrMode.addr (.base 3 (.d8 0x39)) s (0x125200 + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x125200 4 6 (.base 3 (.d8 0x39))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[81, 3]
    (b_l125194_1)))))))))))))))))))))))))))))))

def bytes_l125194 : List UInt8 :=
  [0x0F, 0xB6, 0x4C, 0x24, 0x04, 0x48, 0x8B, 0x54, 0x24, 0x05, 0x48, 0x89, 0x94, 0x24, 0x80, 0x00,
    0x00, 0x00, 0x48, 0x8B, 0x54, 0x24, 0x0D, 0x48, 0x89, 0x94, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48,
    0x8B, 0x54, 0x24, 0x15, 0x48, 0x89, 0x94, 0x24, 0x90, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x54, 0x24,
    0x1D, 0x48, 0x89, 0x94, 0x24, 0x98, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x54, 0x24, 0x25, 0x48, 0x89,
    0x94, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x0F, 0xB7, 0x54, 0x24, 0x2D, 0x66, 0x89, 0x54, 0x24, 0x38,
    0x0F, 0xB6, 0x54, 0x24, 0x2F, 0x88, 0x54, 0x24, 0x3A, 0x0F, 0xB6, 0x54, 0x24, 0x30, 0x0F, 0xB6,
    0x74, 0x24, 0x33, 0x40, 0x88, 0x73, 0x3B, 0x0F, 0xB7, 0x74, 0x24, 0x31, 0x66, 0x89, 0x73, 0x39] ++ bytes_l125194_1

theorem code_l125194 : ∀ x ∈ codeRange 0x125194 bytes_l125194, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x25194 112 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l125194_1

@[cfg_block] def b_l1252b7 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1252b7 (movR64M64Effect 0x1252b7 0 (.sib 4 none 0 (.d8 0x6b))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1252b7 (LoadPre 0x1252b7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6b)) s (0x1252b7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1252b7 0 (.sib 4 none 0 (.d8 0x6b))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x1252bc (StorePre 0x1252bc 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x1252bc + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1252bc 0 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x1252c4 (movR64M64Effect 0x1252c4 0 (.sib 4 none 0 (.d8 0x63))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x1252c4 (LoadPre 0x1252c4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x63)) s (0x1252c4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1252c4 0 (.sib 4 none 0 (.d8 0x63))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x1252c9 (StorePre 0x1252c9 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x1252c9 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1252c9 0 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x1252d1 (movR64M64Effect 0x1252d1 0 (.sib 4 none 0 (.d8 0x5b))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x1252d1 (LoadPre 0x1252d1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5b)) s (0x1252d1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1252d1 0 (.sib 4 none 0 (.d8 0x5b))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x1252d6 (StorePre 0x1252d6 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x1252d6 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1252d6 0 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x1252de (movR64M64Effect 0x1252de 0 (.sib 4 none 0 (.d8 0x4b))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x1252de (LoadPre 0x1252de (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4b)) s (0x1252de + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1252de 0 (.sib 4 none 0 (.d8 0x4b))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x1252e3 (movR64M64Effect 0x1252e3 1 (.sib 4 none 0 (.d8 0x53))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x1252e3 (LoadPre 0x1252e3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x53)) s (0x1252e3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1252e3 1 (.sib 4 none 0 (.d8 0x53))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x1252e8 (StorePre 0x1252e8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x1252e8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1252e8 1 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x1252f0 (StorePre 0x1252f0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x1252f0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1252f0 0 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x1252f8 (movR8Imm8Effect 0x1252f8 3 5 0x1) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5] []) (.reg (.gpr 5))) #v[5]
    (.letOp (n := 69) (.exec 0x1252f8 (fun s => s.RIP = 0x1252f8) (movR8Imm8Effect 0x1252f8 3 5 0x1) (Reg.operands [.gpr 5] [])) #v[5]
    (.terminate (.br ⟨.l1252fb, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 4), (5, 68), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 70⟩))))))))))))))))))

def bytes_l1252b7 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x6B, 0x48, 0x89, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x44,
    0x24, 0x63, 0x48, 0x89, 0x84, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x5B, 0x48,
    0x89, 0x84, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x4B, 0x48, 0x8B, 0x4C, 0x24,
    0x53, 0x48, 0x89, 0x8C, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0xA8, 0x00, 0x00,
    0x00, 0x40, 0xB5, 0x01]

theorem code_l1252b7 : ∀ x ∈ codeRange 0x1252b7 bytes_l1252b7, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x252b7 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1252fb : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1252fb (movR64R64Effect 0x1252fb 7 4) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x1252fb (fun s => s.RIP = 0x1252fb) (movR64R64Effect 0x1252fb 7 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1252fe (movR64R64Effect 0x1252fe 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 56) (.exec 0x1252fe (fun s => s.RIP = 0x1252fe) (movR64R64Effect 0x1252fe 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x125301 (movR32Imm32Effect 0x125301 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x125301 (fun s => s.RIP = 0x125301) (movR32Imm32Effect 0x125301 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x125306 (callEffect (fun _ => 0x125d50) 0x12530b) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x125306 (PushPre 0x125306 5) (callEffect (fun _ => 0x125d50) 0x12530b) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x12530b⟩) #v[]
    (.terminate (.call ⟨.l125d50, RegMap.args [(2, 57), (3, 3), (4, 59), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l12530b, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l1252fb : List UInt8 :=
  [0x48, 0x89, 0xE7, 0x4C, 0x89, 0xF6, 0xBA, 0x01, 0x00, 0x00, 0x00, 0xE8, 0x45, 0x0A, 0x00, 0x00]

theorem code_l1252fb : ∀ x ∈ codeRange 0x1252fb bytes_l1252fb, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x252fb 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12530b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12530b (movR32M32LowEffect 0x12530b 0 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x12530b (LoadPre 0x12530b (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x12530b + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x12530b 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x12530e (cmpR32Imm8Effect 0x12530e 3 0 0x2) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x12530e (fun s => s.RIP = 0x12530e) (cmpR32Imm8Effect 0x12530e 3 0 0x2) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l12532d, RegMap.args [(0, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l125313, RegMap.args [(0, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l12530b : List UInt8 :=
  [0x8B, 0x04, 0x24, 0x83, 0xF8, 0x02, 0x75, 0x1A]

theorem code_l12530b : ∀ x ∈ codeRange 0x12530b bytes_l12530b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2530b 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l125313 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x125313 (movzxR32M8Effect 0x125313 5 2 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 54) (.exec 0x125313 (LoadPre 0x125313 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x125313 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x125313 5 2 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x125318 (cmpM8Imm8Effect 0x125318 5 (.sib 4 none 0 (.d8 0x24)) 0x2) (EffectPart.reads (.flag .ZF) [.gpr 4] []) (.flag .ZF)) #v[4]
    (.letOp (n := 56) (.exec 0x125318 (LoadPre 0x125318 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x125318 + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x125318 5 (.sib 4 none 0 (.d8 0x24)) 0x2) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.pure (condOp 4)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l1253b7, RegMap.args [(0, 0), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l125323, RegMap.args [(0, 0), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l125313 : List UInt8 :=
  [0x0F, 0xB6, 0x54, 0x24, 0x18, 0x80, 0x7C, 0x24, 0x24, 0x02, 0x0F, 0x84, 0x94, 0x00, 0x00, 0x00]

theorem code_l125313 : ∀ x ∈ codeRange 0x125313 bytes_l125313, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x25313 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l125323 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x125323 (movR64M64Effect 0x125323 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x125323 (LoadPre 0x125323 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x125323 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125323 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.br ⟨.l1253b9, RegMap.args [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l125323 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x08, 0xE9, 0x8C, 0x00, 0x00, 0x00]

theorem code_l125323 : ∀ x ∈ codeRange 0x125323 bytes_l125323, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x25323 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12532d_1 : Block Op Label signature Reg.count 87 :=
  .letOp (n := 87) (.exec 0x125390 (StorePre 0x125390 4 (fun s => AddrMode.addr (.base 3 (.d8 0x24)) s (0x125390 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x125390 11 (.base 3 (.d8 0x24))) (Reg.operands [.gpr 11, .gpr 3] [])) #v[85, 3]
    (.letOp (n := 88) (.exec 0x125394 (StorePre 0x125394 4 (fun s => AddrMode.addr (.base 3 (.d8 0x21)) s (0x125394 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x125394 10 (.base 3 (.d8 0x21))) (Reg.operands [.gpr 10, .gpr 3] [])) #v[83, 3]
    (.letOp (n := 89) (.exec 0x125398 (StorePre 0x125398 3 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x125398 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x125398 0 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (.letOp (n := 90) (.exec 0x12539b (StorePre 0x12539b 3 (fun s => AddrMode.addr (.base 3 (.d8 0xc)) s (0x12539b + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x12539b 1 (.base 3 (.d8 0xc))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[53, 3]
    (.letOp (n := 91) (.exec 0x12539e (StorePre 0x12539e 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x12539e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12539e 2 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[55, 3]
    (.letOp (n := 92) (.exec 0x1253a2 (StorePre 0x1253a2 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x1253a2 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1253a2 6 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[57, 3]
    (.letOp (n := 93) (.exec 0x1253a6 (StorePre 0x1253a6 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x1253a6 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1253a6 4 7 (.base 3 (.d8 0x20))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[59, 3]
    (.letOp (n := 94) (.exec 0x1253aa (StorePre 0x1253aa 4 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x1253aa + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x1253aa 8 (.base 3 (.d8 0x28))) (Reg.operands [.gpr 8, .gpr 3] [])) #v[67, 3]
    (.letOp (n := 95) (.exec 0x1253ae (StorePre 0x1253ae 4 (fun s => AddrMode.addr (.base 3 (.d8 0x2c)) s (0x1253ae + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1253ae 4 9 (.base 3 (.d8 0x2c))) (Reg.operands [.gpr 9, .gpr 3] [])) #v[69, 3]
    (.terminate (.br ⟨.l12508d, RegMap.args [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 59), (8, 67), (9, 69), (10, 83), (11, 85), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)] 96⟩))))))))))

def bytes_l12532d_1 : List UInt8 :=
  [0x44, 0x89, 0x5B, 0x24, 0x44, 0x89, 0x53, 0x21, 0x89, 0x43, 0x08, 0x89, 0x4B, 0x0C, 0x48, 0x89,
    0x53, 0x10, 0x48, 0x89, 0x73, 0x18, 0x40, 0x88, 0x7B, 0x20, 0x44, 0x89, 0x43, 0x28, 0x44, 0x88,
    0x4B, 0x2C, 0xE9, 0xD6, 0xFC, 0xFF, 0xFF]

theorem code_l12532d_1 : ∀ x ∈ codeRange 0x125390 bytes_l12532d_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x25390 39 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12532d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12532d (movR32M32LowEffect 0x12532d 1 (.sib 4 none 0 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x12532d (LoadPre 0x12532d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x12532d + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x12532d 1 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x125331 (movR64M64Effect 0x125331 2 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 56) (.exec 0x125331 (LoadPre 0x125331 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x125331 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125331 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x125336 (movR64M64Effect 0x125336 6 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 58) (.exec 0x125336 (LoadPre 0x125336 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x125336 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125336 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x12533b (movzxR32M8Effect 0x12533b 5 7 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 60) (.exec 0x12533b (LoadPre 0x12533b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x12533b + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x12533b 5 7 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x125340 (movR32M32Effect 0x125340 8 (.sib 4 none 0 (.d8 0x19))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 62) (.exec 0x125340 (LoadPre 0x125340 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x19)) s (0x125340 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x125340 8 (.sib 4 none 0 (.d8 0x19))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x125345 (StorePre 0x125345 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x125345 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x125345 8 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.out 0x12534a (movR32M32Effect 0x12534a 8 (.sib 4 none 0 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 65) (.exec 0x12534a (LoadPre 0x12534a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x12534a + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x12534a 8 (.sib 4 none 0 (.d8 0x1c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x12534f (StorePre 0x12534f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4b)) s (0x12534f + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x12534f 8 (.sib 4 none 0 (.d8 0x4b))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.out 0x125354 (movR32M32Effect 0x125354 8 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 68) (.exec 0x125354 (LoadPre 0x125354 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x125354 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x125354 8 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.out 0x125359 (movzxR32M8Effect 0x125359 6 9 (.sib 4 none 0 (.d8 0x24))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 70) (.exec 0x125359 (LoadPre 0x125359 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x125359 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x125359 6 9 (.sib 4 none 0 (.d8 0x24))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.out 0x12535f (movzxR32M8Effect 0x12535f 6 10 (.sib 4 none 0 (.d8 0x27))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 72) (.exec 0x12535f (LoadPre 0x12535f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x27)) s (0x12535f + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x12535f 6 10 (.sib 4 none 0 (.d8 0x27))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.exec 0x125365 (StorePre 0x125365 4 (fun s => AddrMode.addr (.base 3 (.d8 0x2f)) s (0x125365 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x125365 4 10 (.base 3 (.d8 0x2f))) (Reg.operands [.gpr 10, .gpr 3] [])) #v[71, 3]
    (.letOp (n := 74) (.out 0x125369 (movzxR32M16Effect 0x125369 6 10 (.sib 4 none 0 (.d8 0x25))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 75) (.exec 0x125369 (LoadPre 0x125369 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x25)) s (0x125369 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x125369 6 10 (.sib 4 none 0 (.d8 0x25))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 76) (.exec 0x12536f (StorePre 0x12536f 5 (fun s => AddrMode.addr (.base 3 (.d8 0x2d)) s (0x12536f + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x12536f 5 10 (.base 3 (.d8 0x2d))) (Reg.operands [.gpr 10, .gpr 3] [])) #v[74, 3]
    (.letOp (n := 77) (.out 0x125374 (movR64M64Effect 0x125374 10 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 78) (.exec 0x125374 (LoadPre 0x125374 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x125374 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125374 10 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.out 0x125379 (movR64M64Effect 0x125379 11 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 80) (.exec 0x125379 (LoadPre 0x125379 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x125379 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125379 11 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 81) (.exec 0x12537e (StorePre 0x12537e 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x12537e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12537e 10 (.base 3 (.d8 0x30))) (Reg.operands [.gpr 10, .gpr 3] [])) #v[77, 3]
    (.letOp (n := 82) (.exec 0x125382 (StorePre 0x125382 4 (fun s => AddrMode.addr (.base 3 (.d8 0x38)) s (0x125382 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125382 11 (.base 3 (.d8 0x38))) (Reg.operands [.gpr 11, .gpr 3] [])) #v[79, 3]
    (.letOp (n := 83) (.out 0x125386 (movR32M32Effect 0x125386 10 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 84) (.exec 0x125386 (LoadPre 0x125386 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x125386 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x125386 10 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 85) (.out 0x12538b (movR32M32Effect 0x12538b 11 (.sib 4 none 0 (.d8 0x4b))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 86) (.exec 0x12538b (LoadPre 0x12538b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4b)) s (0x12538b + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x12538b 11 (.sib 4 none 0 (.d8 0x4b))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l12532d_1))))))))))))))))))))))))))))))))))

def bytes_l12532d : List UInt8 :=
  [0x8B, 0x4C, 0x24, 0x04, 0x48, 0x8B, 0x54, 0x24, 0x08, 0x48, 0x8B, 0x74, 0x24, 0x10, 0x0F, 0xB6,
    0x7C, 0x24, 0x18, 0x44, 0x8B, 0x44, 0x24, 0x19, 0x44, 0x89, 0x44, 0x24, 0x48, 0x44, 0x8B, 0x44,
    0x24, 0x1C, 0x44, 0x89, 0x44, 0x24, 0x4B, 0x44, 0x8B, 0x44, 0x24, 0x20, 0x44, 0x0F, 0xB6, 0x4C,
    0x24, 0x24, 0x44, 0x0F, 0xB6, 0x54, 0x24, 0x27, 0x44, 0x88, 0x53, 0x2F, 0x44, 0x0F, 0xB7, 0x54,
    0x24, 0x25, 0x66, 0x44, 0x89, 0x53, 0x2D, 0x4C, 0x8B, 0x54, 0x24, 0x28, 0x4C, 0x8B, 0x5C, 0x24,
    0x30, 0x4C, 0x89, 0x53, 0x30, 0x4C, 0x89, 0x5B, 0x38, 0x44, 0x8B, 0x54, 0x24, 0x48, 0x44, 0x8B,
    0x5C, 0x24, 0x4B] ++ bytes_l12532d_1

theorem code_l12532d : ∀ x ∈ codeRange 0x12532d bytes_l12532d, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x2532d 99 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l12532d_1

@[cfg_block] def b_l1253b7 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1253b7 (xorR32R32Effect 0x1253b7 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[0, 0]
    (.letOp (n := 54) (.exec 0x1253b7 (fun s => s.RIP = 0x1253b7) (xorR32R32Effect 0x1253b7 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.terminate (.br ⟨.l1253b9, RegMap.args [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l1253b7 : List UInt8 :=
  [0x31, 0xC0]

theorem code_l1253b7 : ∀ x ∈ codeRange 0x1253b7 bytes_l1253b7, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x253b7 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1253b9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1253b9 (movR64M64Effect 0x1253b9 1 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x1253b9 (LoadPre 0x1253b9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1253b9 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1253b9 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1253be (testR8R8Effect 0x1253be 2 2 2) (EffectPart.reads (.flag .ZF) [.gpr 2, .gpr 2] []) (.flag .ZF)) #v[2, 2]
    (.letOp (n := 56) (.exec 0x1253be (fun s => s.RIP = 0x1253be) (testR8R8Effect 0x1253be 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 57) (.out 0x1253c0 (atFlags (condHolds 4) (setccR8Effect 0x1253c0 3 2)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 2))) #v[2, 55]
    (.letOp (n := 58) (.exec 0x1253c0 (fun s => s.RIP = 0x1253c0) (atFlags (condHolds 4) (setccR8Effect 0x1253c0 3 2)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[2, 55]
    (.letOp (n := 59) (.out 0x1253c3 (testR64R64Effect 0x1253c3 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[0, 0]
    (.letOp (n := 60) (.exec 0x1253c3 (fun s => s.RIP = 0x1253c3) (testR64R64Effect 0x1253c3 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.letOp (n := 61) (.pure (condOp 4)) #v[59]
    (.terminate (.condBr (Fin.last 61) ⟨.l1253f5, RegMap.args [(0, 0), (1, 53), (2, 57), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ ⟨.l1253c8, RegMap.args [(0, 0), (1, 53), (2, 57), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩))))))))))

def bytes_l1253b9 : List UInt8 :=
  [0x48, 0x8B, 0x4C, 0x24, 0x10, 0x84, 0xD2, 0x0F, 0x94, 0xC2, 0x48, 0x85, 0xC0, 0x74, 0x2D]

theorem code_l1253b9 : ∀ x ∈ codeRange 0x1253b9 bytes_l1253b9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x253b9 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1253c8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1253c8 (testR8R8Effect 0x1253c8 2 2 2) (EffectPart.reads (.flag .ZF) [.gpr 2, .gpr 2] []) (.flag .ZF)) #v[2, 2]
    (.letOp (n := 54) (.exec 0x1253c8 (fun s => s.RIP = 0x1253c8) (testR8R8Effect 0x1253c8 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l1253f5, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l1253cc, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l1253c8 : List UInt8 :=
  [0x84, 0xD2, 0x75, 0x29]

theorem code_l1253c8 : ∀ x ∈ codeRange 0x1253c8 bytes_l1253c8, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x253c8 4 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1253cc : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1253cc (StorePre 0x1253cc 7 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x1253cc + BitVec.ofNat 64 7)) 4) (movM32Imm32Effect 0x1253cc 7 (.base 3 (.d8 0x8)) 0x0) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 54) (.exec 0x1253d3 (StorePre 0x1253d3 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x1253d3 + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x1253d3 (.base 3 (.d8 0x10)) 0x15) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.exec 0x1253d7 (StorePre 0x1253d7 4 (fun s => AddrMode.addr (.base 3 (.d8 0x17)) s (0x1253d7 + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x1253d7 (.base 3 (.d8 0x17)) 0x0) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 56) (.exec 0x1253db (StorePre 0x1253db 6 (fun s => AddrMode.addr (.base 3 (.d8 0x15)) s (0x1253db + BitVec.ofNat 64 6)) 2) (movM16Imm16Effect 0x1253db (.base 3 (.d8 0x15)) 0x0) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 57) (.exec 0x1253e1 (StorePre 0x1253e1 7 (fun s => AddrMode.addr (.base 3 (.d8 0x11)) s (0x1253e1 + BitVec.ofNat 64 7)) 4) (movM32Imm32Effect 0x1253e1 7 (.base 3 (.d8 0x11)) 0x2000000) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 58) (.exec 0x1253e8 (StorePre 0x1253e8 8 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x1253e8 + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x1253e8 (.base 3 (.d8 0x18)) 0x0) (Reg.operands [.gpr 3] [])) #v[3]
    (.terminate (.br ⟨.l12508d, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l1253cc : List UInt8 :=
  [0xC7, 0x43, 0x08, 0x00, 0x00, 0x00, 0x00, 0xC6, 0x43, 0x10, 0x15, 0xC6, 0x43, 0x17, 0x00, 0x66,
    0xC7, 0x43, 0x15, 0x00, 0x00, 0xC7, 0x43, 0x11, 0x00, 0x00, 0x00, 0x02, 0x48, 0xC7, 0x43, 0x18,
    0x00, 0x00, 0x00, 0x00, 0xE9, 0x98, 0xFC, 0xFF, 0xFF]

theorem code_l1253cc : ∀ x ∈ codeRange 0x1253cc bytes_l1253cc, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x253cc 41 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1253f5 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1253f5 (movR64M64Effect 0x1253f5 2 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 54) (.exec 0x1253f5 (LoadPre 0x1253f5 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x1253f5 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1253f5 2 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x1253fd (StorePre 0x1253fd 4 (fun s => AddrMode.addr (.base 3 (.d8 0x49)) s (0x1253fd + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1253fd 2 (.base 3 (.d8 0x49))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[53, 3]
    (.letOp (n := 56) (.out 0x125401 (movR64M64Effect 0x125401 2 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 57) (.exec 0x125401 (LoadPre 0x125401 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x125401 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125401 2 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x125409 (StorePre 0x125409 4 (fun s => AddrMode.addr (.base 3 (.d8 0x41)) s (0x125409 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125409 2 (.base 3 (.d8 0x41))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[56, 3]
    (.letOp (n := 59) (.out 0x12540d (movR64M64Effect 0x12540d 2 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 60) (.exec 0x12540d (LoadPre 0x12540d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x12540d + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x12540d 2 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x125415 (StorePre 0x125415 4 (fun s => AddrMode.addr (.base 3 (.d8 0x39)) s (0x125415 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125415 2 (.base 3 (.d8 0x39))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[59, 3]
    (.letOp (n := 62) (.out 0x125419 (movR64M64Effect 0x125419 2 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 63) (.exec 0x125419 (LoadPre 0x125419 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x125419 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125419 2 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x125421 (movR64M64Effect 0x125421 6 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 65) (.exec 0x125421 (LoadPre 0x125421 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x125421 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125421 6 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x125429 (StorePre 0x125429 4 (fun s => AddrMode.addr (.base 3 (.d8 0x31)) s (0x125429 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125429 6 (.base 3 (.d8 0x31))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[64, 3]
    (.letOp (n := 67) (.exec 0x12542d (StorePre 0x12542d 4 (fun s => AddrMode.addr (.base 3 (.d8 0x29)) s (0x12542d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12542d 2 (.base 3 (.d8 0x29))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[62, 3]
    (.letOp (n := 68) (.exec 0x125431 (StorePre 0x125431 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x125431 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125431 15 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 15, .gpr 3] [])) #v[15, 3]
    (.letOp (n := 69) (.exec 0x125435 (StorePre 0x125435 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x125435 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125435 12 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 12, .gpr 3] [])) #v[12, 3]
    (.letOp (n := 70) (.exec 0x125439 (StorePre 0x125439 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x125439 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125439 0 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (.letOp (n := 71) (.exec 0x12543d (StorePre 0x12543d 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x12543d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12543d 1 (.base 3 (.d8 0x20))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[1, 3]
    (.letOp (n := 72) (.exec 0x125441 (StorePre 0x125441 4 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x125441 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x125441 4 5 (.base 3 (.d8 0x28))) (Reg.operands [.gpr 5, .gpr 3] [])) #v[5, 3]
    (.letOp (n := 73) (.out 0x125445 (xorR32R32Effect 0x125445 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[0, 0]
    (.letOp (n := 74) (.exec 0x125445 (fun s => s.RIP = 0x125445) (xorR32R32Effect 0x125445 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.terminate (.br ⟨.l125092, RegMap.args [(0, 73), (1, 1), (2, 62), (3, 3), (4, 4), (5, 5), (6, 64), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩)))))))))))))))))))))))

def bytes_l1253f5 : List UInt8 :=
  [0x48, 0x8B, 0x94, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x53, 0x49, 0x48, 0x8B, 0x94, 0x24,
    0xC0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x53, 0x41, 0x48, 0x8B, 0x94, 0x24, 0xB8, 0x00, 0x00, 0x00,
    0x48, 0x89, 0x53, 0x39, 0x48, 0x8B, 0x94, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x48, 0x8B, 0xB4, 0x24,
    0xB0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x73, 0x31, 0x48, 0x89, 0x53, 0x29, 0x4C, 0x89, 0x7B, 0x08,
    0x4C, 0x89, 0x63, 0x10, 0x48, 0x89, 0x43, 0x18, 0x48, 0x89, 0x4B, 0x20, 0x40, 0x88, 0x6B, 0x28,
    0x31, 0xC0, 0xE9, 0x46, 0xFC, 0xFF, 0xFF]

theorem code_l1253f5 : ∀ x ∈ codeRange 0x1253f5 bytes_l1253f5, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x253f5 87 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l125450 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x125450 (pushR64Effect 0x125450 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x125450 (PushPre 0x125450 1) (pushR64Effect 0x125450 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x125451 (pushR64Effect 0x125451 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x125451 (PushPre 0x125451 2) (pushR64Effect 0x125451 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x125453 (pushR64Effect 0x125453 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x125453 (PushPre 0x125453 2) (pushR64Effect 0x125453 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x125455 (pushR64Effect 0x125455 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x125455 (PushPre 0x125455 2) (pushR64Effect 0x125455 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x125457 (pushR64Effect 0x125457 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x125457 (PushPre 0x125457 2) (pushR64Effect 0x125457 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x125459 (pushR64Effect 0x125459 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x125459 (PushPre 0x125459 1) (pushR64Effect 0x125459 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x12545a (subR64Imm8Effect 0x12545a 4 0x78) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x12545a (fun s => s.RIP = 0x12545a) (subR64Imm8Effect 0x12545a 4 0x78) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x12545e (movR64R64Effect 0x12545e 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 6] []) (.reg (.gpr 14))) #v[6]
    (.letOp (n := 68) (.exec 0x12545e (fun s => s.RIP = 0x12545e) (movR64R64Effect 0x12545e 14 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 69) (.out 0x125461 (movR64R64Effect 0x125461 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 70) (.exec 0x125461 (fun s => s.RIP = 0x125461) (movR64R64Effect 0x125461 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 71) (.out 0x125464 (leaR64Effect 0x125464 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[65]
    (.letOp (n := 72) (.exec 0x125464 (fun s => s.RIP = 0x125464) (leaR64Effect 0x125464 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 73) (.out 0x125469 (callEffect (fun _ => 0x124430) 0x12546e) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 74) (.exec 0x125469 (PushPre 0x125469 5) (callEffect (fun _ => 0x124430) 0x12546e) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 75) (.const ⟨64, 0x12546e⟩) #v[]
    (.terminate (.call ⟨.l124430, RegMap.args [(3, 69), (4, 73), (5, 5), (6, 6), (7, 71), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 76⟩ { target := .l12546e, kept := #v[], arity := rfl, guard := some (Fin.last 75) }))))))))))))))))))))))))

def bytes_l125450 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x83, 0xEC, 0x78, 0x49, 0x89,
    0xF6, 0x48, 0x89, 0xFB, 0x48, 0x8D, 0x7C, 0x24, 0x08, 0xE8, 0xC2, 0xEF, 0xFF, 0xFF]

theorem code_l125450 : ∀ x ∈ codeRange 0x125450 bytes_l125450, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x25450 30 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12546e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12546e (movR32M32LowEffect 0x12546e 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x12546e (LoadPre 0x12546e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x12546e + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x12546e 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x125472 (cmpR32Imm8Effect 0x125472 3 0 0x2) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x125472 (fun s => s.RIP = 0x125472) (cmpR32Imm8Effect 0x125472 3 0 0x2) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l1254f3, RegMap.args [(0, 53), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l125477, RegMap.args [(0, 53), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l12546e : List UInt8 :=
  [0x8B, 0x44, 0x24, 0x08, 0x83, 0xF8, 0x02, 0x75, 0x7C]

theorem code_l12546e : ∀ x ∈ codeRange 0x12546e bytes_l12546e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2546e 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l125477 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x125477 (movR32M32Effect 0x125477 12 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 54) (.exec 0x125477 (LoadPre 0x125477 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x125477 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x125477 12 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x12547c (movR32M32Effect 0x12547c 13 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 56) (.exec 0x12547c (LoadPre 0x12547c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x12547c + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x12547c 13 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x125481 (movR64M64Effect 0x125481 15 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 58) (.exec 0x125481 (LoadPre 0x125481 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x125481 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125481 15 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x125486 (movzxR32M8Effect 0x125486 5 5 (.sib 4 none 0 (.d8 0x14))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 60) (.exec 0x125486 (LoadPre 0x125486 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x125486 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x125486 5 5 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x12548b (leaR64Effect 0x12548b 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 62) (.exec 0x12548b (fun s => s.RIP = 0x12548b) (leaR64Effect 0x12548b 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x125490 (movR64R64Effect 0x125490 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 64) (.exec 0x125490 (fun s => s.RIP = 0x125490) (movR64R64Effect 0x125490 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 65) (.out 0x125493 (movR32Imm32Effect 0x125493 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 66) (.exec 0x125493 (fun s => s.RIP = 0x125493) (movR32Imm32Effect 0x125493 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 67) (.out 0x125498 (callEffect (fun _ => 0x127b80) 0x12549d) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 68) (.exec 0x125498 (PushPre 0x125498 5) (callEffect (fun _ => 0x127b80) 0x12549d) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.const ⟨64, 0x12549d⟩) #v[]
    (.terminate (.call ⟨.l127b80, RegMap.args [(2, 65), (3, 3), (4, 67), (5, 59), (6, 63), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 55), (14, 14), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 70⟩ { target := .l12549d, kept := #v[], arity := rfl, guard := some (Fin.last 69) }))))))))))))))))))

def bytes_l125477 : List UInt8 :=
  [0x44, 0x8B, 0x64, 0x24, 0x0C, 0x44, 0x8B, 0x6C, 0x24, 0x10, 0x4C, 0x8B, 0x7C, 0x24, 0x0C, 0x0F,
    0xB6, 0x6C, 0x24, 0x14, 0x48, 0x8D, 0x7C, 0x24, 0x08, 0x4C, 0x89, 0xF6, 0xBA, 0x01, 0x00, 0x00,
    0x00, 0xE8, 0xE3, 0x26, 0x00, 0x00]

theorem code_l125477 : ∀ x ∈ codeRange 0x125477 bytes_l125477, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x25477 38 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12549d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12549d (movR32M32LowEffect 0x12549d 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x12549d (LoadPre 0x12549d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x12549d + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x12549d 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1254a1 (cmpR32Imm8Effect 0x1254a1 3 0 0x2) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x1254a1 (fun s => s.RIP = 0x1254a1) (cmpR32Imm8Effect 0x1254a1 3 0 0x2) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l12553f, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l1254aa, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l12549d : List UInt8 :=
  [0x8B, 0x44, 0x24, 0x08, 0x83, 0xF8, 0x02, 0x0F, 0x85, 0x95, 0x00, 0x00, 0x00]

theorem code_l12549d : ∀ x ∈ codeRange 0x12549d bytes_l12549d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2549d 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1254aa : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1254aa (movR64M64Effect 0x1254aa 6 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 54) (.exec 0x1254aa (LoadPre 0x1254aa (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1254aa + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1254aa 6 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1254af (cmpR64Imm8Effect 0x1254af 6 0x1) (EffectPart.reads (.flag .ZF) [.gpr 6] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x1254af (fun s => s.RIP = 0x1254af) (cmpR64Imm8Effect 0x1254af 6 0x1) (Reg.operands [.gpr 6] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l125741, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l1254b9, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l1254aa : List UInt8 :=
  [0x48, 0x8B, 0x74, 0x24, 0x18, 0x48, 0x83, 0xFE, 0x01, 0x0F, 0x85, 0x88, 0x02, 0x00, 0x00]

theorem code_l1254aa : ∀ x ∈ codeRange 0x1254aa bytes_l1254aa, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x254aa 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1254b9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1254b9 (StorePre 0x1254b9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x1254b9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1254b9 15 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[15, 4]
    (.letOp (n := 54) (.out 0x1254be (movR64M64Effect 0x1254be 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 55) (.exec 0x1254be (LoadPre 0x1254be (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1254be + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1254be 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x1254c3 (movsxR32M8Effect 0x1254c3 4 15 (.base 0 .none)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[54]
    (.letOp (n := 57) (.exec 0x1254c3 (LoadPre 0x1254c3 (fun s => AddrMode.addr (.base 0 .none) s (0x1254c3 + BitVec.ofNat 64 4)) 1) (movsxR32M8Effect 0x1254c3 4 15 (.base 0 .none)) (Reg.operands [.gpr 0] [])) #v[54]
    (.letOp (n := 58) (.out 0x1254c7 (testR32R32Effect 0x1254c7 3 15 15) (EffectPart.reads (.flag .SF) [.gpr 15, .gpr 15] []) (.flag .SF)) #v[56, 56]
    (.letOp (n := 59) (.exec 0x1254c7 (fun s => s.RIP = 0x1254c7) (testR32R32Effect 0x1254c7 3 15 15) (Reg.operands [.gpr 15, .gpr 15] [])) #v[56, 56]
    (.letOp (n := 60) (.pure (condOp 8)) #v[58]
    (.terminate (.condBr (Fin.last 60) ⟨.l1255d9, RegMap.args [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 56), (20, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩ ⟨.l1254d0, RegMap.args [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 56), (20, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩)))))))))

def bytes_l1254b9 : List UInt8 :=
  [0x4C, 0x89, 0x7C, 0x24, 0x70, 0x48, 0x8B, 0x44, 0x24, 0x10, 0x44, 0x0F, 0xBE, 0x38, 0x45, 0x85,
    0xFF, 0x0F, 0x88, 0x09, 0x01, 0x00, 0x00]

theorem code_l1254b9 : ∀ x ∈ codeRange 0x1254b9 bytes_l1254b9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x254b9 23 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1254d0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1254d0 (movR32R32Effect 0x1254d0 3 13 15) (EffectPart.reads (.reg (.gpr 13)) [.gpr 15] []) (.reg (.gpr 13))) #v[15]
    (.letOp (n := 54) (.exec 0x1254d0 (fun s => s.RIP = 0x1254d0) (movR32R32Effect 0x1254d0 3 13 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.terminate (.br ⟨.l1254d3, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l1254d0 : List UInt8 :=
  [0x45, 0x89, 0xFD]

theorem code_l1254d0 : ∀ x ∈ codeRange 0x1254d0 bytes_l1254d0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x254d0 3 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1254d3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1254d3 (andR8Imm8Effect 0x1254d3 4 5 0x1) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5] []) (.reg (.gpr 5))) #v[5]
    (.letOp (n := 54) (.exec 0x1254d3 (fun s => s.RIP = 0x1254d3) (andR8Imm8Effect 0x1254d3 4 5 0x1) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 55) (.out 0x1254d7 (movR64M64Effect 0x1254d7 0 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 56) (.exec 0x1254d7 (LoadPre 0x1254d7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x1254d7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1254d7 0 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x1254dc (StorePre 0x1254dc 4 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x1254dc + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1254dc 0 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[55, 3]
    (.letOp (n := 58) (.exec 0x1254e0 (StorePre 0x1254e0 4 (fun s => AddrMode.addr (.base 3 (.d8 0xc)) s (0x1254e0 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x1254e0 13 (.base 3 (.d8 0xc))) (Reg.operands [.gpr 13, .gpr 3] [])) #v[13, 3]
    (.letOp (n := 59) (.exec 0x1254e4 (StorePre 0x1254e4 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x1254e4 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1254e4 4 5 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 5, .gpr 3] [])) #v[53, 3]
    (.letOp (n := 60) (.exec 0x1254e8 (StorePre 0x1254e8 6 (fun s => AddrMode.addr (.base 3 .none) s (0x1254e8 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x1254e8 6 (.base 3 .none) 0x2) (Reg.operands [.gpr 3] [])) #v[3]
    (.terminate (.br ⟨.l1255c7, RegMap.args [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩)))))))))

def bytes_l1254d3 : List UInt8 :=
  [0x40, 0x80, 0xE5, 0x01, 0x48, 0x8B, 0x44, 0x24, 0x70, 0x48, 0x89, 0x43, 0x04, 0x44, 0x89, 0x6B,
    0x0C, 0x40, 0x88, 0x6B, 0x10, 0xC7, 0x03, 0x02, 0x00, 0x00, 0x00, 0xE9, 0xD4, 0x00, 0x00, 0x00]

theorem code_l1254d3 : ∀ x ∈ codeRange 0x1254d3 bytes_l1254d3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x254d3 32 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1254f3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1254f3 (movR64M64Effect 0x1254f3 1 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x1254f3 (LoadPre 0x1254f3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x1254f3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1254f3 1 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1254f8 (movzxR32M8Effect 0x1254f8 5 2 (.sib 4 none 0 (.d8 0x14))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 56) (.exec 0x1254f8 (LoadPre 0x1254f8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x1254f8 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1254f8 5 2 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1254fd (movR32M32LowEffect 0x1254fd 6 (.sib 4 none 0 (.d8 0x3c))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 58) (.exec 0x1254fd (LoadPre 0x1254fd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x1254fd + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1254fd 6 (.sib 4 none 0 (.d8 0x3c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.exec 0x125501 (StorePre 0x125501 3 (fun s => AddrMode.addr (.base 3 (.d8 0x34)) s (0x125501 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x125501 6 (.base 3 (.d8 0x34))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[57, 3]
    (.letOp (n := 60) (.out 0x125504 (movR64M64Effect 0x125504 6 (.sib 4 none 0 (.d8 0x35))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 61) (.exec 0x125504 (LoadPre 0x125504 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x35)) s (0x125504 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125504 6 (.sib 4 none 0 (.d8 0x35))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.exec 0x125509 (StorePre 0x125509 4 (fun s => AddrMode.addr (.base 3 (.d8 0x2d)) s (0x125509 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125509 6 (.base 3 (.d8 0x2d))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[60, 3]
    (.letOp (n := 63) (.out 0x12550d (movR64M64Effect 0x12550d 6 (.sib 4 none 0 (.d8 0x2d))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 64) (.exec 0x12550d (LoadPre 0x12550d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2d)) s (0x12550d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12550d 6 (.sib 4 none 0 (.d8 0x2d))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.exec 0x125512 (StorePre 0x125512 4 (fun s => AddrMode.addr (.base 3 (.d8 0x25)) s (0x125512 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125512 6 (.base 3 (.d8 0x25))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[63, 3]
    (.letOp (n := 66) (.out 0x125516 (movR64M64Effect 0x125516 6 (.sib 4 none 0 (.d8 0x25))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 67) (.exec 0x125516 (LoadPre 0x125516 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x25)) s (0x125516 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125516 6 (.sib 4 none 0 (.d8 0x25))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.exec 0x12551b (StorePre 0x12551b 4 (fun s => AddrMode.addr (.base 3 (.d8 0x1d)) s (0x12551b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12551b 6 (.base 3 (.d8 0x1d))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[66, 3]
    (.letOp (n := 69) (.out 0x12551f (movR64M64Effect 0x12551f 6 (.sib 4 none 0 (.d8 0x1d))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 70) (.exec 0x12551f (LoadPre 0x12551f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1d)) s (0x12551f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12551f 6 (.sib 4 none 0 (.d8 0x1d))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.exec 0x125524 (StorePre 0x125524 4 (fun s => AddrMode.addr (.base 3 (.d8 0x15)) s (0x125524 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125524 6 (.base 3 (.d8 0x15))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[69, 3]
    (.letOp (n := 72) (.out 0x125528 (movR64M64Effect 0x125528 6 (.sib 4 none 0 (.d8 0x15))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 73) (.exec 0x125528 (LoadPre 0x125528 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x15)) s (0x125528 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125528 6 (.sib 4 none 0 (.d8 0x15))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.exec 0x12552d (StorePre 0x12552d 4 (fun s => AddrMode.addr (.base 3 (.d8 0xd)) s (0x12552d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12552d 6 (.base 3 (.d8 0xd))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[72, 3]
    (.letOp (n := 75) (.exec 0x125531 (StorePre 0x125531 2 (fun s => AddrMode.addr (.base 3 .none) s (0x125531 + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x125531 0 (.base 3 .none)) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (.letOp (n := 76) (.exec 0x125533 (StorePre 0x125533 4 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x125533 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125533 1 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[53, 3]
    (.letOp (n := 77) (.exec 0x125537 (StorePre 0x125537 3 (fun s => AddrMode.addr (.base 3 (.d8 0xc)) s (0x125537 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x125537 3 2 (.base 3 (.d8 0xc))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[55, 3]
    (.terminate (.br ⟨.l1255c7, RegMap.args [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 72), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 78⟩))))))))))))))))))))))))))

def bytes_l1254f3 : List UInt8 :=
  [0x48, 0x8B, 0x4C, 0x24, 0x0C, 0x0F, 0xB6, 0x54, 0x24, 0x14, 0x8B, 0x74, 0x24, 0x3C, 0x89, 0x73,
    0x34, 0x48, 0x8B, 0x74, 0x24, 0x35, 0x48, 0x89, 0x73, 0x2D, 0x48, 0x8B, 0x74, 0x24, 0x2D, 0x48,
    0x89, 0x73, 0x25, 0x48, 0x8B, 0x74, 0x24, 0x25, 0x48, 0x89, 0x73, 0x1D, 0x48, 0x8B, 0x74, 0x24,
    0x1D, 0x48, 0x89, 0x73, 0x15, 0x48, 0x8B, 0x74, 0x24, 0x15, 0x48, 0x89, 0x73, 0x0D, 0x89, 0x03,
    0x48, 0x89, 0x4B, 0x04, 0x88, 0x53, 0x0C, 0xE9, 0x88, 0x00, 0x00, 0x00]

theorem code_l1254f3 : ∀ x ∈ codeRange 0x1254f3 bytes_l1254f3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x254f3 76 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12553f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12553f (movR32M32LowEffect 0x12553f 1 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x12553f (LoadPre 0x12553f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x12553f + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x12553f 1 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x125543 (movR64M64Effect 0x125543 2 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 56) (.exec 0x125543 (LoadPre 0x125543 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x125543 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125543 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x125548 (movR64M64Effect 0x125548 6 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 58) (.exec 0x125548 (LoadPre 0x125548 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x125548 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125548 6 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x12554d (movR64M64Effect 0x12554d 7 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 60) (.exec 0x12554d (LoadPre 0x12554d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x12554d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12554d 7 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x125552 (StorePre 0x125552 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x125552 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125552 7 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x125557 (movR64M64Effect 0x125557 7 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 63) (.exec 0x125557 (LoadPre 0x125557 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x125557 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125557 7 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x12555c (StorePre 0x12555c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x12555c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12555c 7 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x125561 (movR64M64Effect 0x125561 7 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 66) (.exec 0x125561 (LoadPre 0x125561 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x125561 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125561 7 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x125566 (StorePre 0x125566 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x125566 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125566 7 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x12556b (movR64M64Effect 0x12556b 7 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 69) (.exec 0x12556b (LoadPre 0x12556b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x12556b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12556b 7 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.exec 0x125570 (StorePre 0x125570 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x125570 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125570 7 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[68, 4]
    (.terminate (.br ⟨.l125575, RegMap.args [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)] 71⟩)))))))))))))))))))

def bytes_l12553f : List UInt8 :=
  [0x8B, 0x4C, 0x24, 0x0C, 0x48, 0x8B, 0x54, 0x24, 0x10, 0x48, 0x8B, 0x74, 0x24, 0x18, 0x48, 0x8B,
    0x7C, 0x24, 0x20, 0x48, 0x89, 0x7C, 0x24, 0x50, 0x48, 0x8B, 0x7C, 0x24, 0x28, 0x48, 0x89, 0x7C,
    0x24, 0x58, 0x48, 0x8B, 0x7C, 0x24, 0x30, 0x48, 0x89, 0x7C, 0x24, 0x60, 0x48, 0x8B, 0x7C, 0x24,
    0x38, 0x48, 0x89, 0x7C, 0x24, 0x68]

theorem code_l12553f : ∀ x ∈ codeRange 0x12553f bytes_l12553f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2553f 54 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l125575 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x125575 (cmpR8Imm8Effect 0x125575 3 2 0xd) (EffectPart.reads (.flag .ZF) [.gpr 2] []) (.flag .ZF)) #v[2]
    (.letOp (n := 54) (.exec 0x125575 (fun s => s.RIP = 0x125575) (cmpR8Imm8Effect 0x125575 3 2 0xd) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l125596, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l12557a, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l125575 : List UInt8 :=
  [0x80, 0xFA, 0x0D, 0x75, 0x1C]

theorem code_l125575 : ∀ x ∈ codeRange 0x125575 bytes_l125575, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x25575 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12557a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12557a (shlR64Effect 0x12557a 4 12 32) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[12]
    (.letOp (n := 54) (.exec 0x12557a (fun s => s.RIP = 0x12557a) (shlR64Effect 0x12557a 4 12 32) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[12]
    (.letOp (n := 55) (.out 0x12557e (orR64Imm8Effect 0x12557e 12 0x5) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[53]
    (.letOp (n := 56) (.exec 0x12557e (fun s => s.RIP = 0x12557e) (orR64Imm8Effect 0x12557e 12 0x5) (Reg.operands [.gpr 12] [])) #v[53]
    (.letOp (n := 57) (.exec 0x125582 (StorePre 0x125582 5 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x125582 + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x125582 (.base 14 (.d8 0x20)) 0x1) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 58) (.out 0x125587 (movR32M32Effect 0x125587 1 (.base 14 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[14]
    (.letOp (n := 59) (.exec 0x125587 (LoadPre 0x125587 (fun s => AddrMode.addr (.base 14 (.d8 0x1c)) s (0x125587 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x125587 1 (.base 14 (.d8 0x1c))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 60) (.out 0x12558b (movR32Imm32Effect 0x12558b 5 0 0x1) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 61) (.exec 0x12558b (fun s => s.RIP = 0x12558b) (movR32Imm32Effect 0x12558b 5 0 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 62) (.out 0x125590 (movR64R64Effect 0x125590 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 13] []) (.reg (.gpr 6))) #v[13]
    (.letOp (n := 63) (.exec 0x125590 (fun s => s.RIP = 0x125590) (movR64R64Effect 0x125590 6 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 64) (.out 0x125593 (movR64R64Effect 0x125593 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12] []) (.reg (.gpr 2))) #v[55]
    (.letOp (n := 65) (.exec 0x125593 (fun s => s.RIP = 0x125593) (movR64R64Effect 0x125593 2 12) (Reg.operands [.gpr 12] [])) #v[55]
    (.terminate (.br ⟨.l125596, RegMap.args [(0, 60), (1, 58), (2, 64), (3, 3), (4, 4), (6, 62), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩))))))))))))))

def bytes_l12557a : List UInt8 :=
  [0x49, 0xC1, 0xE4, 0x20, 0x49, 0x83, 0xCC, 0x05, 0x41, 0xC6, 0x46, 0x20, 0x01, 0x41, 0x8B, 0x4E,
    0x1C, 0xB8, 0x01, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xEE, 0x4C, 0x89, 0xE2]

theorem code_l12557a : ∀ x ∈ codeRange 0x12557a bytes_l12557a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2557a 28 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l125596 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x125596 (StorePre 0x125596 2 (fun s => AddrMode.addr (.base 3 .none) s (0x125596 + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x125596 0 (.base 3 .none)) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (.letOp (n := 54) (.exec 0x125598 (StorePre 0x125598 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x125598 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x125598 1 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[1, 3]
    (.letOp (n := 55) (.exec 0x12559b (StorePre 0x12559b 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x12559b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12559b 2 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[2, 3]
    (.letOp (n := 56) (.exec 0x12559f (StorePre 0x12559f 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x12559f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12559f 6 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[6, 3]
    (.letOp (n := 57) (.out 0x1255a3 (movR64M64Effect 0x1255a3 0 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 58) (.exec 0x1255a3 (LoadPre 0x1255a3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1255a3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1255a3 0 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x1255a8 (movR64M64Effect 0x1255a8 1 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 60) (.exec 0x1255a8 (LoadPre 0x1255a8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1255a8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1255a8 1 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x1255ad (StorePre 0x1255ad 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x1255ad + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1255ad 0 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[57, 3]
    (.letOp (n := 62) (.exec 0x1255b1 (StorePre 0x1255b1 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x1255b1 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1255b1 1 (.base 3 (.d8 0x20))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[59, 3]
    (.letOp (n := 63) (.out 0x1255b5 (movR64M64Effect 0x1255b5 0 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 64) (.exec 0x1255b5 (LoadPre 0x1255b5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1255b5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1255b5 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.exec 0x1255ba (StorePre 0x1255ba 4 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x1255ba + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1255ba 0 (.base 3 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[63, 3]
    (.letOp (n := 66) (.out 0x1255be (movR64M64Effect 0x1255be 0 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 67) (.exec 0x1255be (LoadPre 0x1255be (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x1255be + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1255be 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.exec 0x1255c3 (StorePre 0x1255c3 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x1255c3 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1255c3 0 (.base 3 (.d8 0x30))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[66, 3]
    (.terminate (.br ⟨.l1255c7, RegMap.args [(0, 66), (1, 59), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 69⟩)))))))))))))))))

def bytes_l125596 : List UInt8 :=
  [0x89, 0x03, 0x89, 0x4B, 0x04, 0x48, 0x89, 0x53, 0x08, 0x48, 0x89, 0x73, 0x10, 0x48, 0x8B, 0x44,
    0x24, 0x50, 0x48, 0x8B, 0x4C, 0x24, 0x58, 0x48, 0x89, 0x43, 0x18, 0x48, 0x89, 0x4B, 0x20, 0x48,
    0x8B, 0x44, 0x24, 0x60, 0x48, 0x89, 0x43, 0x28, 0x48, 0x8B, 0x44, 0x24, 0x68, 0x48, 0x89, 0x43,
    0x30]

theorem code_l125596 : ∀ x ∈ codeRange 0x125596 bytes_l125596, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x25596 49 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1255c7 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1255c7 (movR64R64Effect 0x1255c7 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 54) (.exec 0x1255c7 (fun s => s.RIP = 0x1255c7) (movR64R64Effect 0x1255c7 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x1255ca (addR64Imm8Effect 0x1255ca 4 0x78) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 56) (.exec 0x1255ca (fun s => s.RIP = 0x1255ca) (addR64Imm8Effect 0x1255ca 4 0x78) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1255ce (popR64Effect 0x1255ce 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[55]
    (.letOp (n := 58) (.out 0x1255ce (popR64Effect 0x1255ce 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[55]
    (.letOp (n := 59) (.exec 0x1255ce (PopPre 0x1255ce) (popR64Effect 0x1255ce 1 3) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 60) (.out 0x1255cf (popR64Effect 0x1255cf 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[58]
    (.letOp (n := 61) (.out 0x1255cf (popR64Effect 0x1255cf 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[58]
    (.letOp (n := 62) (.exec 0x1255cf (PopPre 0x1255cf) (popR64Effect 0x1255cf 2 12) (Reg.operands [.gpr 4] [])) #v[58]
    (.letOp (n := 63) (.out 0x1255d1 (popR64Effect 0x1255d1 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[61]
    (.letOp (n := 64) (.out 0x1255d1 (popR64Effect 0x1255d1 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 65) (.exec 0x1255d1 (PopPre 0x1255d1) (popR64Effect 0x1255d1 2 13) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 66) (.out 0x1255d3 (popR64Effect 0x1255d3 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[64]
    (.letOp (n := 67) (.out 0x1255d3 (popR64Effect 0x1255d3 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[64]
    (.letOp (n := 68) (.exec 0x1255d3 (PopPre 0x1255d3) (popR64Effect 0x1255d3 2 14) (Reg.operands [.gpr 4] [])) #v[64]
    (.letOp (n := 69) (.out 0x1255d5 (popR64Effect 0x1255d5 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[67]
    (.letOp (n := 70) (.out 0x1255d5 (popR64Effect 0x1255d5 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[67]
    (.letOp (n := 71) (.exec 0x1255d5 (PopPre 0x1255d5) (popR64Effect 0x1255d5 2 15) (Reg.operands [.gpr 4] [])) #v[67]
    (.letOp (n := 72) (.out 0x1255d7 (popR64Effect 0x1255d7 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[70]
    (.letOp (n := 73) (.out 0x1255d7 (popR64Effect 0x1255d7 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[70]
    (.letOp (n := 74) (.exec 0x1255d7 (PopPre 0x1255d7) (popR64Effect 0x1255d7 1 5) (Reg.operands [.gpr 4] [])) #v[70]
    (.letOp (n := 75) (.out 0x1255d8 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[73]
    (.letOp (n := 76) (.out 0x1255d8 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[73]
    (.letOp (n := 77) (.exec 0x1255d8 (RetPre 0x1255d8) (retEffect) (Reg.operands [.gpr 4] [])) #v[73]
    (.terminate (.ret (RegMap.args [(0, 53), (1, 1), (2, 2), (3, 57), (4, 76), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 78) (some ⟨75, by decide⟩)))))))))))))))))))))))))))

def bytes_l1255c7 : List UInt8 :=
  [0x48, 0x89, 0xD8, 0x48, 0x83, 0xC4, 0x78, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F,
    0x5D, 0xC3]

theorem code_l1255c7 : ∀ x ∈ codeRange 0x1255c7 bytes_l1255c7, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x255c7 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1255d9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1255d9 (movR32R32Effect 0x1255d9 3 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[15]
    (.letOp (n := 54) (.exec 0x1255d9 (fun s => s.RIP = 0x1255d9) (movR32R32Effect 0x1255d9 3 0 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.out 0x1255dc (negR8Effect 0x1255dc 2 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.out 0x1255dc (negR8Effect 0x1255dc 2 0) (EffectPart.reads (.flag .OF) [.gpr 0] []) (.flag .OF)) #v[53]
    (.letOp (n := 57) (.exec 0x1255dc (fun s => s.RIP = 0x1255dc) (negR8Effect 0x1255dc 2 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 58) (.pure (condOp 1)) #v[56]
    (.terminate (.condBr (Fin.last 58) ⟨.l1255f5, RegMap.args [(0, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (21, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩ ⟨.l1255e0, RegMap.args [(0, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (21, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l1255d9 : List UInt8 :=
  [0x44, 0x89, 0xF8, 0xF6, 0xD8, 0x71, 0x15]

theorem code_l1255d9 : ∀ x ∈ codeRange 0x1255d9 bytes_l1255d9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x255d9 7 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1255e0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1255e0 (StorePre 0x1255e0 5 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x1255e0 + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x1255e0 (.base 14 (.d8 0x20)) 0x1) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 54) (.out 0x1255e5 (movR32M32Effect 0x1255e5 1 (.base 14 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[14]
    (.letOp (n := 55) (.exec 0x1255e5 (LoadPre 0x1255e5 (fun s => AddrMode.addr (.base 14 (.d8 0x1c)) s (0x1255e5 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x1255e5 1 (.base 14 (.d8 0x1c))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 56) (.out 0x1255e9 (movR32Imm32Effect 0x1255e9 5 0 0x1) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 57) (.exec 0x1255e9 (fun s => s.RIP = 0x1255e9) (movR32Imm32Effect 0x1255e9 5 0 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 58) (.out 0x1255ee (movR32Imm32Effect 0x1255ee 5 2 0x4) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 59) (.exec 0x1255ee (fun s => s.RIP = 0x1255ee) (movR32Imm32Effect 0x1255ee 5 2 0x4) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l125575, RegMap.args [(0, 56), (1, 54), (2, 58), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l1255e0 : List UInt8 :=
  [0x41, 0xC6, 0x46, 0x20, 0x01, 0x41, 0x8B, 0x4E, 0x1C, 0xB8, 0x01, 0x00, 0x00, 0x00, 0xBA, 0x04,
    0x00, 0x00, 0x00, 0xEB, 0x80]

theorem code_l1255e0 : ∀ x ∈ codeRange 0x1255e0 bytes_l1255e0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x255e0 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1255f5 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1255f5 (cmpR8Imm8Effect 0x1255f5 4 15 0x85) (EffectPart.reads (.flag .CF) [.gpr 15] []) (.flag .CF)) #v[15]
    (.letOp (n := 54) (.exec 0x1255f5 (fun s => s.RIP = 0x1255f5) (cmpR8Imm8Effect 0x1255f5 4 15 0x85) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.pure (condOp 3)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l125682, RegMap.args [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l1255ff, RegMap.args [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l1255f5 : List UInt8 :=
  [0x41, 0x80, 0xFF, 0x85, 0x0F, 0x83, 0x83, 0x00, 0x00, 0x00]

theorem code_l1255f5 : ∀ x ∈ codeRange 0x1255f5 bytes_l1255f5, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x255f5 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1255ff : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1255ff (StorePre 0x1255ff 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1255ff + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1255ff 13 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[13, 4]
    (.letOp (n := 54) (.out 0x125604 (testR8Imm8Effect 0x125604 15 0x7f) (EffectPart.reads (.flag .ZF) [.gpr 15] []) (.flag .ZF)) #v[15]
    (.letOp (n := 55) (.exec 0x125604 (fun s => s.RIP = 0x125604) (testR8Imm8Effect 0x125604 15 0x7f) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 56) (.pure (condOp 4)) #v[54]
    (.terminate (.condBr (Fin.last 56) ⟨.l12569a, RegMap.args [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩ ⟨.l12560e, RegMap.args [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l1255ff : List UInt8 :=
  [0x4C, 0x89, 0x6C, 0x24, 0x48, 0x41, 0xF6, 0xC7, 0x7F, 0x0F, 0x84, 0x8C, 0x00, 0x00, 0x00]

theorem code_l1255ff : ∀ x ∈ codeRange 0x1255ff bytes_l1255ff, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x255ff 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12560e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x12560e (StorePre 0x12560e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x12560e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12560e 12 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[12, 4]
    (.letOp (n := 54) (.out 0x125613 (movR32R32Effect 0x125613 3 12 15) (EffectPart.reads (.reg (.gpr 12)) [.gpr 15] []) (.reg (.gpr 12))) #v[15]
    (.letOp (n := 55) (.exec 0x125613 (fun s => s.RIP = 0x125613) (movR32R32Effect 0x125613 3 12 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 56) (.out 0x125616 (andR32Imm8Effect 0x125616 4 12 0x7f) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[54]
    (.letOp (n := 57) (.exec 0x125616 (fun s => s.RIP = 0x125616) (andR32Imm8Effect 0x125616 4 12 0x7f) (Reg.operands [.gpr 12] [])) #v[54]
    (.letOp (n := 58) (.out 0x12561a (xorR32R32Effect 0x12561a 3 13 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 13] []) (.reg (.gpr 13))) #v[13, 13]
    (.letOp (n := 59) (.exec 0x12561a (fun s => s.RIP = 0x12561a) (xorR32R32Effect 0x12561a 3 13 13) (Reg.operands [.gpr 13, .gpr 13] [])) #v[13, 13]
    (.letOp (n := 60) (.exec 0x12561d (fun s => s.RIP = 0x12561d) (fun _ => nopEffect 0x12561d 3) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l125620, RegMap.args [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 56), (13, 58), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩)))))))))

def bytes_l12560e : List UInt8 :=
  [0x4C, 0x89, 0x64, 0x24, 0x40, 0x45, 0x89, 0xFC, 0x41, 0x83, 0xE4, 0x7F, 0x45, 0x31, 0xED, 0x0F,
    0x1F, 0x00]

theorem code_l12560e : ∀ x ∈ codeRange 0x12560e bytes_l12560e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2560e 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l125620 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x125620 (leaR64Effect 0x125620 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x125620 (fun s => s.RIP = 0x125620) (leaR64Effect 0x125620 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x125625 (movR64R64Effect 0x125625 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 56) (.exec 0x125625 (fun s => s.RIP = 0x125625) (movR64R64Effect 0x125625 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x125628 (movR32Imm32Effect 0x125628 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x125628 (fun s => s.RIP = 0x125628) (movR32Imm32Effect 0x125628 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x12562d (callEffect (fun _ => 0x127b80) 0x125632) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x12562d (PushPre 0x12562d 5) (callEffect (fun _ => 0x127b80) 0x125632) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x125632⟩) #v[]
    (.terminate (.call ⟨.l127b80, RegMap.args [(2, 57), (3, 3), (4, 59), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l125632, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l125620 : List UInt8 :=
  [0x48, 0x8D, 0x7C, 0x24, 0x08, 0x4C, 0x89, 0xF6, 0xBA, 0x01, 0x00, 0x00, 0x00, 0xE8, 0x4E, 0x25,
    0x00, 0x00]

theorem code_l125620 : ∀ x ∈ codeRange 0x125620 bytes_l125620, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x25620 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l125632 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x125632 (movR32M32LowEffect 0x125632 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x125632 (LoadPre 0x125632 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x125632 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x125632 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x125636 (cmpR32Imm8Effect 0x125636 3 0 0x2) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x125636 (fun s => s.RIP = 0x125636) (cmpR32Imm8Effect 0x125636 3 0 0x2) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l1256de, RegMap.args [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l12563f, RegMap.args [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l125632 : List UInt8 :=
  [0x8B, 0x44, 0x24, 0x08, 0x83, 0xF8, 0x02, 0x0F, 0x85, 0x9F, 0x00, 0x00, 0x00]

theorem code_l125632 : ∀ x ∈ codeRange 0x125632 bytes_l125632, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x25632 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12563f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12563f (movR64M64Effect 0x12563f 6 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 54) (.exec 0x12563f (LoadPre 0x12563f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x12563f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12563f 6 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x125644 (cmpR64Imm8Effect 0x125644 6 0x1) (EffectPart.reads (.flag .ZF) [.gpr 6] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x125644 (fun s => s.RIP = 0x125644) (cmpR64Imm8Effect 0x125644 6 0x1) (Reg.operands [.gpr 6] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l125741, RegMap.args [(1, 1), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l12564e, RegMap.args [(1, 1), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l12563f : List UInt8 :=
  [0x48, 0x8B, 0x74, 0x24, 0x18, 0x48, 0x83, 0xFE, 0x01, 0x0F, 0x85, 0xF3, 0x00, 0x00, 0x00]

theorem code_l12563f : ∀ x ∈ codeRange 0x12563f bytes_l12563f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2563f 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12564e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12564e (movR64M64Effect 0x12564e 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x12564e (LoadPre 0x12564e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x12564e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12564e 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x125653 (movR32R32Effect 0x125653 3 2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13] []) (.reg (.gpr 2))) #v[13]
    (.letOp (n := 56) (.exec 0x125653 (fun s => s.RIP = 0x125653) (movR32R32Effect 0x125653 3 2 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 57) (.out 0x125656 (movzxR32M8Effect 0x125656 4 13 (.base 0 .none)) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[53]
    (.letOp (n := 58) (.exec 0x125656 (LoadPre 0x125656 (fun s => AddrMode.addr (.base 0 .none) s (0x125656 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x125656 4 13 (.base 0 .none)) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 59) (.out 0x12565a (shlR32Effect 0x12565a 3 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[55]
    (.letOp (n := 60) (.exec 0x12565a (fun s => s.RIP = 0x12565a) (shlR32Effect 0x12565a 3 2 8) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[55]
    (.letOp (n := 61) (.out 0x12565d (orR32R32Effect 0x12565d 3 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 2] []) (.reg (.gpr 13))) #v[57, 59]
    (.letOp (n := 62) (.exec 0x12565d (fun s => s.RIP = 0x12565d) (orR32R32Effect 0x12565d 3 13 2) (Reg.operands [.gpr 13, .gpr 2] [])) #v[57, 59]
    (.letOp (n := 63) (.out 0x125660 (decR64Effect 0x125660 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[12]
    (.letOp (n := 64) (.out 0x125660 (decR64Effect 0x125660 12) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.flag .ZF)) #v[12]
    (.letOp (n := 65) (.exec 0x125660 (fun s => s.RIP = 0x125660) (decR64Effect 0x125660 12) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[12]
    (.letOp (n := 66) (.pure (condOp 5)) #v[64]
    (.terminate (.condBr (Fin.last 66) ⟨.l125620, RegMap.args [(0, 53), (1, 1), (2, 59), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 63), (13, 61), (14, 14), (15, 15), (19, 64), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩ ⟨.l125665, RegMap.args [(0, 53), (1, 1), (2, 59), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 63), (13, 61), (14, 14), (15, 15), (19, 64), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩)))))))))))))))

def bytes_l12564e : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x10, 0x44, 0x89, 0xEA, 0x44, 0x0F, 0xB6, 0x28, 0xC1, 0xE2, 0x08, 0x41,
    0x09, 0xD5, 0x49, 0xFF, 0xCC, 0x75, 0xBB]

theorem code_l12564e : ∀ x ∈ codeRange 0x12564e bytes_l12564e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2564e 23 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l125665 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x125665 (movR32R32Effect 0x125665 3 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 13] []) (.reg (.gpr 6))) #v[13]
    (.letOp (n := 54) (.exec 0x125665 (fun s => s.RIP = 0x125665) (movR32R32Effect 0x125665 3 6 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 55) (.out 0x125668 (andR32Imm8Effect 0x125668 3 6 0x80) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[53]
    (.letOp (n := 56) (.exec 0x125668 (fun s => s.RIP = 0x125668) (andR32Imm8Effect 0x125668 3 6 0x80) (Reg.operands [.gpr 6] [])) #v[53]
    (.letOp (n := 57) (.out 0x12566b (movR8Imm8Effect 0x12566b 2 0 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 58) (.exec 0x12566b (fun s => s.RIP = 0x12566b) (movR8Imm8Effect 0x12566b 2 0 0x1) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 59) (.out 0x12566d (movR8Imm8Effect 0x12566d 2 1 0x81) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1]
    (.letOp (n := 60) (.exec 0x12566d (fun s => s.RIP = 0x12566d) (movR8Imm8Effect 0x12566d 2 1 0x81) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 61) (.out 0x12566f (cmpR32Imm32Effect 0x12566f 6 6 0x80) (EffectPart.reads (.flag .ZF) [.gpr 6] []) (.flag .ZF)) #v[55]
    (.letOp (n := 62) (.exec 0x12566f (fun s => s.RIP = 0x12566f) (cmpR32Imm32Effect 0x12566f 6 6 0x80) (Reg.operands [.gpr 6] [])) #v[55]
    (.letOp (n := 63) (.pure (condOp 5)) #v[61]
    (.terminate (.condBr (Fin.last 63) ⟨.l125723, RegMap.args [(0, 57), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 55), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 61), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ ⟨.l12567b, RegMap.args [(0, 57), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 55), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 61), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩))))))))))))

def bytes_l125665 : List UInt8 :=
  [0x44, 0x89, 0xEE, 0x83, 0xE6, 0x80, 0xB0, 0x01, 0xB1, 0x81, 0x81, 0xFE, 0x80, 0x00, 0x00, 0x00,
    0x0F, 0x85, 0xA8, 0x00, 0x00, 0x00]

theorem code_l125665 : ∀ x ∈ codeRange 0x125665 bytes_l125665, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x25665 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12567b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12567b (movR64M64Effect 0x12567b 12 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 54) (.exec 0x12567b (LoadPre 0x12567b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x12567b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12567b 12 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.br ⟨.l1256b4, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l12567b : List UInt8 :=
  [0x4C, 0x8B, 0x64, 0x24, 0x40, 0xEB, 0x32]

theorem code_l12567b : ∀ x ∈ codeRange 0x12567b bytes_l12567b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2567b 7 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l125682 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x125682 (StorePre 0x125682 5 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x125682 + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x125682 (.base 14 (.d8 0x20)) 0x1) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 54) (.out 0x125687 (movR32M32Effect 0x125687 1 (.base 14 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[14]
    (.letOp (n := 55) (.exec 0x125687 (LoadPre 0x125687 (fun s => AddrMode.addr (.base 14 (.d8 0x1c)) s (0x125687 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x125687 1 (.base 14 (.d8 0x1c))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 56) (.out 0x12568b (movR32Imm32Effect 0x12568b 5 0 0x1) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 57) (.exec 0x12568b (fun s => s.RIP = 0x12568b) (movR32Imm32Effect 0x12568b 5 0 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 58) (.out 0x125690 (movR32Imm32Effect 0x125690 5 2 0xd) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 59) (.exec 0x125690 (fun s => s.RIP = 0x125690) (movR32Imm32Effect 0x125690 5 2 0xd) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l125575, RegMap.args [(0, 56), (1, 54), (2, 58), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l125682 : List UInt8 :=
  [0x41, 0xC6, 0x46, 0x20, 0x01, 0x41, 0x8B, 0x4E, 0x1C, 0xB8, 0x01, 0x00, 0x00, 0x00, 0xBA, 0x0D,
    0x00, 0x00, 0x00, 0xE9, 0xDB, 0xFE, 0xFF, 0xFF]

theorem code_l125682 : ∀ x ∈ codeRange 0x125682 bytes_l125682, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x25682 24 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12569a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12569a (xorR32R32Effect 0x12569a 3 13 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 13] []) (.reg (.gpr 13))) #v[13, 13]
    (.letOp (n := 54) (.exec 0x12569a (fun s => s.RIP = 0x12569a) (xorR32R32Effect 0x12569a 3 13 13) (Reg.operands [.gpr 13, .gpr 13] [])) #v[13, 13]
    (.terminate (.br ⟨.l12569d, RegMap.args [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l12569a : List UInt8 :=
  [0x45, 0x31, 0xED]

theorem code_l12569a : ∀ x ∈ codeRange 0x12569a bytes_l12569a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2569a 3 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12569d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12569d (movR32R32Effect 0x12569d 3 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 13] []) (.reg (.gpr 1))) #v[13]
    (.letOp (n := 54) (.exec 0x12569d (fun s => s.RIP = 0x12569d) (movR32R32Effect 0x12569d 3 1 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 55) (.out 0x1256a0 (subR32Imm32Effect 0x1256a0 6 1 0x10000) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 56) (.out 0x1256a0 (subR32Imm32Effect 0x1256a0 6 1 0x10000) (EffectPart.reads (.flag .CF) [.gpr 1] []) (.flag .CF)) #v[53]
    (.letOp (n := 57) (.exec 0x1256a0 (fun s => s.RIP = 0x1256a0) (subR32Imm32Effect 0x1256a0 6 1 0x10000) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 58) (.out 0x1256a6 (atFlags (condHolds 3) (setccR8Effect 0x1256a6 3 0)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 0))) #v[0, 56]
    (.letOp (n := 59) (.exec 0x1256a6 (fun s => s.RIP = 0x1256a6) (atFlags (condHolds 3) (setccR8Effect 0x1256a6 3 0)) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[0, 56]
    (.letOp (n := 60) (.out 0x1256a9 (cmpR32Imm32Effect 0x1256a9 6 1 0xff0000) (EffectPart.reads (.flag .CF) [.gpr 1] []) (.flag .CF)) #v[55]
    (.letOp (n := 61) (.exec 0x1256a9 (fun s => s.RIP = 0x1256a9) (cmpR32Imm32Effect 0x1256a9 6 1 0xff0000) (Reg.operands [.gpr 1] [])) #v[55]
    (.letOp (n := 62) (.out 0x1256af (movR8Imm8Effect 0x1256af 2 1 0x84) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[55]
    (.letOp (n := 63) (.exec 0x1256af (fun s => s.RIP = 0x1256af) (movR8Imm8Effect 0x1256af 2 1 0x84) (Reg.operands [.gpr 1] [])) #v[55]
    (.letOp (n := 64) (.out 0x1256b1 (atFlags StatusFlags.CF (sbbR8Imm8Effect 0x1256b1 3 1 0x0)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[62, 60]
    (.letOp (n := 65) (.exec 0x1256b1 (fun s => s.RIP = 0x1256b1) (atFlags StatusFlags.CF (sbbR8Imm8Effect 0x1256b1 3 1 0x0)) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[62, 60]
    (.terminate (.br ⟨.l1256b4, RegMap.args [(0, 58), (1, 64), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩))))))))))))))

def bytes_l12569d : List UInt8 :=
  [0x44, 0x89, 0xE9, 0x81, 0xE9, 0x00, 0x00, 0x01, 0x00, 0x0F, 0x93, 0xC0, 0x81, 0xF9, 0x00, 0x00,
    0xFF, 0x00, 0xB1, 0x84, 0x80, 0xD9, 0x00]

theorem code_l12569d : ∀ x ∈ codeRange 0x12569d bytes_l12569d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2569d 23 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1256b4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1256b4 (testR8R8Effect 0x1256b4 2 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[0, 0]
    (.letOp (n := 54) (.exec 0x1256b4 (fun s => s.RIP = 0x1256b4) (testR8R8Effect 0x1256b4 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l1256c1, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l1256b8, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l1256b4 : List UInt8 :=
  [0x84, 0xC0, 0x74, 0x09]

theorem code_l1256b4 : ∀ x ∈ codeRange 0x1256b4 bytes_l1256b4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x256b4 4 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1256b8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1256b8 (cmpR8R8Effect 0x1256b8 3 1 15) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 15] []) (.flag .ZF)) #v[1, 15]
    (.letOp (n := 54) (.exec 0x1256b8 (fun s => s.RIP = 0x1256b8) (cmpR8R8Effect 0x1256b8 3 1 15) (Reg.operands [.gpr 1, .gpr 15] [])) #v[1, 15]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l1254d3, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l1256c1, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l1256b8 : List UInt8 :=
  [0x44, 0x38, 0xF9, 0x0F, 0x84, 0x12, 0xFE, 0xFF, 0xFF]

theorem code_l1256b8 : ∀ x ∈ codeRange 0x1256b8 bytes_l1256b8, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x256b8 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1256c1 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1256c1 (StorePre 0x1256c1 5 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x1256c1 + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x1256c1 (.base 14 (.d8 0x20)) 0x1) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 54) (.out 0x1256c6 (movR32M32Effect 0x1256c6 1 (.base 14 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[14]
    (.letOp (n := 55) (.exec 0x1256c6 (LoadPre 0x1256c6 (fun s => AddrMode.addr (.base 14 (.d8 0x1c)) s (0x1256c6 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x1256c6 1 (.base 14 (.d8 0x1c))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 56) (.out 0x1256ca (movR32Imm32Effect 0x1256ca 5 0 0x1) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 57) (.exec 0x1256ca (fun s => s.RIP = 0x1256ca) (movR32Imm32Effect 0x1256ca 5 0 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 58) (.out 0x1256cf (movR32Imm32Effect 0x1256cf 5 2 0xd) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 59) (.exec 0x1256cf (fun s => s.RIP = 0x1256cf) (movR32Imm32Effect 0x1256cf 5 2 0xd) (Reg.operands [] [])) #v[]
    (.letOp (n := 60) (.out 0x1256d4 (movR64M64Effect 0x1256d4 13 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 61) (.exec 0x1256d4 (LoadPre 0x1256d4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1256d4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1256d4 13 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.br ⟨.l125575, RegMap.args [(0, 56), (1, 54), (2, 58), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 60), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩))))))))))

def bytes_l1256c1 : List UInt8 :=
  [0x41, 0xC6, 0x46, 0x20, 0x01, 0x41, 0x8B, 0x4E, 0x1C, 0xB8, 0x01, 0x00, 0x00, 0x00, 0xBA, 0x0D,
    0x00, 0x00, 0x00, 0x4C, 0x8B, 0x6C, 0x24, 0x48, 0xE9, 0x97, 0xFE, 0xFF, 0xFF]

theorem code_l1256c1 : ∀ x ∈ codeRange 0x1256c1 bytes_l1256c1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x256c1 29 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1256de : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1256de (movR32M32LowEffect 0x1256de 1 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x1256de (LoadPre 0x1256de (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x1256de + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1256de 1 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1256e2 (movR64M64Effect 0x1256e2 2 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 56) (.exec 0x1256e2 (LoadPre 0x1256e2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1256e2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1256e2 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1256e7 (movR64M64Effect 0x1256e7 6 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 58) (.exec 0x1256e7 (LoadPre 0x1256e7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1256e7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1256e7 6 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x1256ec (movR64M64Effect 0x1256ec 7 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 60) (.exec 0x1256ec (LoadPre 0x1256ec (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1256ec + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1256ec 7 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x1256f1 (StorePre 0x1256f1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1256f1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1256f1 7 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x1256f6 (movR64M64Effect 0x1256f6 7 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 63) (.exec 0x1256f6 (LoadPre 0x1256f6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1256f6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1256f6 7 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x1256fb (StorePre 0x1256fb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1256fb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1256fb 7 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x125700 (movR64M64Effect 0x125700 7 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 66) (.exec 0x125700 (LoadPre 0x125700 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x125700 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125700 7 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x125705 (StorePre 0x125705 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x125705 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125705 7 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x12570a (movR64M64Effect 0x12570a 7 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 69) (.exec 0x12570a (LoadPre 0x12570a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x12570a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12570a 7 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.exec 0x12570f (StorePre 0x12570f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x12570f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12570f 7 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[68, 4]
    (.letOp (n := 71) (.out 0x125714 (movR64M64Effect 0x125714 12 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 72) (.exec 0x125714 (LoadPre 0x125714 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x125714 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125714 12 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.out 0x125719 (movR64M64Effect 0x125719 13 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 74) (.exec 0x125719 (LoadPre 0x125719 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x125719 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125719 13 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.br ⟨.l125575, RegMap.args [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (12, 71), (13, 73), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩)))))))))))))))))))))))

def bytes_l1256de : List UInt8 :=
  [0x8B, 0x4C, 0x24, 0x0C, 0x48, 0x8B, 0x54, 0x24, 0x10, 0x48, 0x8B, 0x74, 0x24, 0x18, 0x48, 0x8B,
    0x7C, 0x24, 0x20, 0x48, 0x89, 0x7C, 0x24, 0x50, 0x48, 0x8B, 0x7C, 0x24, 0x28, 0x48, 0x89, 0x7C,
    0x24, 0x58, 0x48, 0x8B, 0x7C, 0x24, 0x30, 0x48, 0x89, 0x7C, 0x24, 0x60, 0x48, 0x8B, 0x7C, 0x24,
    0x38, 0x48, 0x89, 0x7C, 0x24, 0x68, 0x4C, 0x8B, 0x64, 0x24, 0x40, 0x4C, 0x8B, 0x6C, 0x24, 0x48,
    0xE9, 0x52, 0xFE, 0xFF, 0xFF]

theorem code_l1256de : ∀ x ∈ codeRange 0x1256de bytes_l1256de, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x256de 69 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l125723 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x125723 (addR32Imm32Effect 0x125723 6 2 0xffffff00) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[2]
    (.letOp (n := 54) (.exec 0x125723 (fun s => s.RIP = 0x125723) (addR32Imm32Effect 0x125723 6 2 0xffffff00) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 55) (.out 0x125729 (movR8Imm8Effect 0x125729 2 1 0x82) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1]
    (.letOp (n := 56) (.exec 0x125729 (fun s => s.RIP = 0x125729) (movR8Imm8Effect 0x125729 2 1 0x82) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 57) (.out 0x12572b (cmpR32Imm32Effect 0x12572b 6 2 0xff00) (EffectPart.reads (.flag .CF) [.gpr 2] []) (.flag .CF)) #v[53]
    (.letOp (n := 58) (.exec 0x12572b (fun s => s.RIP = 0x12572b) (cmpR32Imm32Effect 0x12572b 6 2 0xff00) (Reg.operands [.gpr 2] [])) #v[53]
    (.letOp (n := 59) (.out 0x125731 (movR64M64Effect 0x125731 12 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 60) (.exec 0x125731 (LoadPre 0x125731 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x125731 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125731 12 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.pure (condOp 3)) #v[57]
    (.terminate (.condBr (Fin.last 61) ⟨.l12569d, RegMap.args [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 13), (14, 14), (15, 15), (16, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ ⟨.l12573c, RegMap.args [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 13), (14, 14), (15, 15), (16, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩))))))))))

def bytes_l125723 : List UInt8 :=
  [0x81, 0xC2, 0x00, 0xFF, 0xFF, 0xFF, 0xB1, 0x82, 0x81, 0xFA, 0x00, 0xFF, 0x00, 0x00, 0x4C, 0x8B,
    0x64, 0x24, 0x40, 0x0F, 0x83, 0x61, 0xFF, 0xFF, 0xFF]

theorem code_l125723 : ∀ x ∈ codeRange 0x125723 bytes_l125723, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x25723 25 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12573c : Block Op Label signature Reg.count 53 :=
  .terminate (.br ⟨.l1256b4, RegMap.args (entryMap (live .l12573c)) 53⟩)

def bytes_l12573c : List UInt8 :=
  [0xE9, 0x73, 0xFF, 0xFF, 0xFF]

theorem code_l12573c : ∀ x ∈ codeRange 0x12573c bytes_l12573c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2573c 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l125741 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x125741 (movR32Imm32Effect 0x125741 5 7 0x1) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 54) (.exec 0x125741 (fun s => s.RIP = 0x125741) (movR32Imm32Effect 0x125741 5 7 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x125746 (movR64Imm32Effect 0x125746 2 0x2036e0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 56) (.exec 0x125746 (fun s => s.RIP = 0x125746) (movR64Imm32Effect 0x125746 2 0x2036e0) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x12574d (callEffect (fun _ => 0x129c90) 0x125752) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x12574d (PushPre 0x12574d 5) (callEffect (fun _ => 0x129c90) 0x125752) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x125752⟩) #v[]
    (.terminate (.call ⟨.l129c90, RegMap.args [(2, 55), (4, 57), (5, 5), (6, 6), (7, 53)] 60⟩ { target := .l125752, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l125741 : List UInt8 :=
  [0xBF, 0x01, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC2, 0xE0, 0x36, 0x20, 0x00, 0xE8, 0x3E, 0x45, 0x00,
    0x00]

theorem code_l125741 : ∀ x ∈ codeRange 0x125741 bytes_l125741, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x25741 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l125752 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x125752 (fun s => s.RIP = 0x125752) (fun _ => nopEffect 0x125752 10) (Reg.operands [] [])) #v[]
    (.letOp (n := 54) (.exec 0x12575c (fun s => s.RIP = 0x12575c) (fun _ => nopEffect 0x12575c 4) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l125760, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l125752 : List UInt8 :=
  [0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00, 0x0F, 0x1F, 0x40, 0x00]

theorem code_l125752 : ∀ x ∈ codeRange 0x125752 bytes_l125752, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x25752 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l125760 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x125760 (testR64R64Effect 0x125760 6 6) (EffectPart.reads (.flag .ZF) [.gpr 6, .gpr 6] []) (.flag .ZF)) #v[6, 6]
    (.letOp (n := 54) (.exec 0x125760 (fun s => s.RIP = 0x125760) (testR64R64Effect 0x125760 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l12576f, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l125765, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l125760 : List UInt8 :=
  [0x48, 0x85, 0xF6, 0x74, 0x0A]

theorem code_l125760 : ∀ x ∈ codeRange 0x125760 bytes_l125760, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x25760 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l125765 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x125765 (movzxR32M8Effect 0x125765 5 0 (.sib 7 (some 6) 0 (.d8 0xff))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 6] []) (.reg (.gpr 0))) #v[7, 6]
    (.letOp (n := 54) (.exec 0x125765 (LoadPre 0x125765 (fun s => AddrMode.addr (.sib 7 (some 6) 0 (.d8 0xff)) s (0x125765 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x125765 5 0 (.sib 7 (some 6) 0 (.d8 0xff))) (Reg.operands [.gpr 7, .gpr 6] [])) #v[7, 6]
    (.letOp (n := 55) (.out 0x12576a (andAlImm8Effect 0x12576a 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x12576a (fun s => s.RIP = 0x12576a) (andAlImm8Effect 0x12576a 0x1) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x12576c (orAlImm8Effect 0x12576c 0x2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[55]
    (.letOp (n := 58) (.exec 0x12576c (fun s => s.RIP = 0x12576c) (orAlImm8Effect 0x12576c 0x2) (Reg.operands [.gpr 0] [])) #v[55]
    (.letOp (n := 59) (.out 0x12576e (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[4]
    (.letOp (n := 60) (.out 0x12576e (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 61) (.exec 0x12576e (RetPre 0x12576e) (retEffect) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.ret (RegMap.args [(0, 57), (1, 1), (2, 2), (3, 3), (4, 60), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62) (some ⟨59, by decide⟩)))))))))))

def bytes_l125765 : List UInt8 :=
  [0x0F, 0xB6, 0x44, 0x37, 0xFF, 0x24, 0x01, 0x0C, 0x02, 0xC3]

theorem code_l125765 : ∀ x ∈ codeRange 0x125765 bytes_l125765, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x25765 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12576f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12576f (pushR64Effect 0x12576f 1 0) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 0] []) (.reg (.gpr 4))) #v[4, 0]
    (.letOp (n := 54) (.exec 0x12576f (PushPre 0x12576f 1) (pushR64Effect 0x12576f 1 0) (Reg.operands [.gpr 4, .gpr 0] [])) #v[4, 0]
    (.letOp (n := 55) (.out 0x125770 (movR32Imm32Effect 0x125770 5 6 0x12) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 56) (.exec 0x125770 (fun s => s.RIP = 0x125770) (movR32Imm32Effect 0x125770 5 6 0x12) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x125775 (movR64Imm32Effect 0x125775 7 0x2036b0) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 58) (.exec 0x125775 (fun s => s.RIP = 0x125775) (movR64Imm32Effect 0x125775 7 0x2036b0) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x12577c (movR64Imm32Effect 0x12577c 2 0x2036c8) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 60) (.exec 0x12577c (fun s => s.RIP = 0x12577c) (movR64Imm32Effect 0x12577c 2 0x2036c8) (Reg.operands [] [])) #v[]
    (.letOp (n := 61) (.out 0x125783 (callEffect (fun _ => 0x129560) 0x125788) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[53]
    (.letOp (n := 62) (.exec 0x125783 (PushPre 0x125783 5) (callEffect (fun _ => 0x129560) 0x125788) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 63) (.const ⟨64, 0x125788⟩) #v[]
    (.terminate (.call ⟨.l129560, RegMap.args [(0, 0), (2, 59), (4, 61), (5, 5), (6, 55), (7, 57)] 64⟩ { target := .l125788, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l12576f : List UInt8 :=
  [0x50, 0xBE, 0x12, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC7, 0xB0, 0x36, 0x20, 0x00, 0x48, 0xC7, 0xC2,
    0xC8, 0x36, 0x20, 0x00, 0xE8, 0xD8, 0x3D, 0x00, 0x00]

theorem code_l12576f : ∀ x ∈ codeRange 0x12576f bytes_l12576f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2576f 25 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l125788 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x125788 (fun s => s.RIP = 0x125788) (fun _ => nopEffect 0x125788 8) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l125790, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 54⟩))

def bytes_l125788 : List UInt8 :=
  [0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem code_l125788 : ∀ x ∈ codeRange 0x125788 bytes_l125788, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x25788 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l125790 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x125790 (pushR64Effect 0x125790 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x125790 (PushPre 0x125790 1) (pushR64Effect 0x125790 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x125791 (pushR64Effect 0x125791 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x125791 (PushPre 0x125791 2) (pushR64Effect 0x125791 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x125793 (pushR64Effect 0x125793 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x125793 (PushPre 0x125793 2) (pushR64Effect 0x125793 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x125795 (pushR64Effect 0x125795 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[57, 3]
    (.letOp (n := 60) (.exec 0x125795 (PushPre 0x125795 1) (pushR64Effect 0x125795 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[57, 3]
    (.letOp (n := 61) (.out 0x125796 (subR64Imm32Effect 0x125796 4 0x138) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 62) (.exec 0x125796 (fun s => s.RIP = 0x125796) (subR64Imm32Effect 0x125796 4 0x138) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 63) (.out 0x12579d (movR64R64Effect 0x12579d 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 64) (.exec 0x12579d (fun s => s.RIP = 0x12579d) (movR64R64Effect 0x12579d 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 65) (.out 0x1257a0 (leaR64Effect 0x1257a0 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[61]
    (.letOp (n := 66) (.exec 0x1257a0 (fun s => s.RIP = 0x1257a0) (leaR64Effect 0x1257a0 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 67) (.out 0x1257a5 (callEffect (fun _ => 0x127690) 0x1257aa) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 68) (.exec 0x1257a5 (PushPre 0x1257a5 5) (callEffect (fun _ => 0x127690) 0x1257aa) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 69) (.const ⟨64, 0x1257aa⟩) #v[]
    (.terminate (.call ⟨.l127690, RegMap.args [(2, 2), (3, 63), (4, 67), (5, 5), (6, 6), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 70⟩ { target := .l1257aa, kept := #v[], arity := rfl, guard := some (Fin.last 69) }))))))))))))))))))

def bytes_l125790 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x53, 0x48, 0x81, 0xEC, 0x38, 0x01, 0x00, 0x00, 0x48, 0x89, 0xFB,
    0x48, 0x8D, 0x7C, 0x24, 0x08, 0xE8, 0xE6, 0x1E, 0x00, 0x00]

theorem code_l125790 : ∀ x ∈ codeRange 0x125790 bytes_l125790, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x25790 26 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1257aa : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1257aa (movR32M32LowEffect 0x1257aa 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1257aa (LoadPre 0x1257aa (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1257aa + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1257aa 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1257ae (cmpR32Imm8Effect 0x1257ae 3 0 0x2) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x1257ae (fun s => s.RIP = 0x1257ae) (cmpR32Imm8Effect 0x1257ae 3 0 0x2) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l1259f4, RegMap.args [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l1257b7, RegMap.args [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l1257aa : List UInt8 :=
  [0x8B, 0x44, 0x24, 0x08, 0x83, 0xF8, 0x02, 0x0F, 0x85, 0x3D, 0x02, 0x00, 0x00]

theorem code_l1257aa : ∀ x ∈ codeRange 0x1257aa bytes_l1257aa, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x257aa 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1257b7_1 : Block Op Label signature Reg.count 82 :=
  .letOp (n := 82) (.out 0x125832 (movR64M64Effect 0x125832 0 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 83) (.exec 0x125832 (LoadPre 0x125832 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x125832 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125832 0 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 84) (.exec 0x12583a (StorePre 0x12583a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe4)) s (0x12583a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x12583a 0 (.sib 4 none 0 (.d32 0xe4))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[82, 4]
    (.letOp (n := 85) (.out 0x125842 (movR64M64Effect 0x125842 0 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 86) (.exec 0x125842 (LoadPre 0x125842 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x125842 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125842 0 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 87) (.out 0x12584a (movR64M64Effect 0x12584a 1 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 88) (.exec 0x12584a (LoadPre 0x12584a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x12584a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x12584a 1 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 89) (.exec 0x125852 (StorePre 0x125852 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xdc)) s (0x125852 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x125852 1 (.sib 4 none 0 (.d32 0xdc))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[87, 4]
    (.letOp (n := 90) (.exec 0x12585a (StorePre 0x12585a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd4)) s (0x12585a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x12585a 0 (.sib 4 none 0 (.d32 0xd4))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[85, 4]
    (.letOp (n := 91) (.out 0x125862 (leaR64Effect 0x125862 7 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 92) (.exec 0x125862 (fun s => s.RIP = 0x125862) (leaR64Effect 0x125862 7 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 93) (.out 0x12586a (leaR64Effect 0x12586a 6 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 94) (.exec 0x12586a (fun s => s.RIP = 0x12586a) (leaR64Effect 0x12586a 6 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 95) (.out 0x125872 (callEffect (fun _ => 0x125450) 0x125877) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 96) (.exec 0x125872 (PushPre 0x125872 5) (callEffect (fun _ => 0x125450) 0x125877) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 97) (.const ⟨64, 0x125877⟩) #v[]
    (.terminate (.call ⟨.l125450, RegMap.args [(0, 85), (1, 87), (2, 58), (3, 3), (4, 95), (5, 5), (6, 93), (7, 91), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 98⟩ { target := .l125877, kept := #v[], arity := rfl, guard := some (Fin.last 97) })))))))))))))))))

def bytes_l1257b7_1 : List UInt8 :=
  [0x48, 0x8B, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0xE4, 0x00, 0x00, 0x00,
    0x48, 0x8B, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x8C, 0x24, 0x88, 0x00, 0x00, 0x00,
    0x48, 0x89, 0x8C, 0x24, 0xDC, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0xD4, 0x00, 0x00, 0x00,
    0x48, 0x8D, 0xBC, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0x8D, 0xB4, 0x24, 0xC8, 0x00, 0x00, 0x00,
    0xE8, 0xD9, 0xFB, 0xFF, 0xFF]

theorem code_l1257b7_1 : ∀ x ∈ codeRange 0x125832 bytes_l1257b7_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x25832 69 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1257b7 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1257b7 (movzxR32M8Effect 0x1257b7 5 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1257b7 (LoadPre 0x1257b7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1257b7 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1257b7 5 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1257bc (movzxR32M16Effect 0x1257bc 5 1 (.sib 4 none 0 (.d8 0x11))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x1257bc (LoadPre 0x1257bc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x11)) s (0x1257bc + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x1257bc 5 1 (.sib 4 none 0 (.d8 0x11))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x1257c1 (StorePre 0x1257c1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1257c1 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1257c1 5 1 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 58) (.out 0x1257c6 (movzxR32M8Effect 0x1257c6 5 2 (.sib 4 none 0 (.d8 0x13))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 59) (.exec 0x1257c6 (LoadPre 0x1257c6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x13)) s (0x1257c6 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1257c6 5 2 (.sib 4 none 0 (.d8 0x13))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.exec 0x1257cb (StorePre 0x1257cb 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x62)) s (0x1257cb + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1257cb 4 2 (.sib 4 none 0 (.d8 0x62))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[58, 4]
    (.letOp (n := 61) (.out 0x1257cf (movR64M64Effect 0x1257cf 6 (.sib 4 none 0 (.d8 0x14))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 62) (.exec 0x1257cf (LoadPre 0x1257cf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x1257cf + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1257cf 6 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x1257d4 (movR64M64Effect 0x1257d4 7 (.sib 4 none 0 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 64) (.exec 0x1257d4 (LoadPre 0x1257d4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x1257d4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1257d4 7 (.sib 4 none 0 (.d8 0x1c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.exec 0x1257d9 (StorePre 0x1257d9 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1257d9 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1257d9 7 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[63, 4]
    (.letOp (n := 66) (.out 0x1257e1 (movR64M64Effect 0x1257e1 7 (.sib 4 none 0 (.d8 0x24))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 67) (.exec 0x1257e1 (LoadPre 0x1257e1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x1257e1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1257e1 7 (.sib 4 none 0 (.d8 0x24))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.exec 0x1257e6 (StorePre 0x1257e6 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1257e6 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1257e6 7 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[66, 4]
    (.letOp (n := 69) (.out 0x1257ee (movR64M64Effect 0x1257ee 7 (.sib 4 none 0 (.d8 0x2c))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 70) (.exec 0x1257ee (LoadPre 0x1257ee (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x1257ee + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1257ee 7 (.sib 4 none 0 (.d8 0x2c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.exec 0x1257f3 (StorePre 0x1257f3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x1257f3 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1257f3 7 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[69, 4]
    (.letOp (n := 72) (.out 0x1257fb (movR32M32LowEffect 0x1257fb 7 (.sib 4 none 0 (.d8 0x34))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 73) (.exec 0x1257fb (LoadPre 0x1257fb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x1257fb + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1257fb 7 (.sib 4 none 0 (.d8 0x34))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.exec 0x1257ff (StorePre 0x1257ff 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x1257ff + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x1257ff 7 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[72, 4]
    (.letOp (n := 75) (.exec 0x125806 (StorePre 0x125806 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x125806 + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x125806 7 0 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 76) (.exec 0x12580d (StorePre 0x12580d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc9)) s (0x12580d + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x12580d 8 1 (.sib 4 none 0 (.d32 0xc9))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 77) (.exec 0x125815 (StorePre 0x125815 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xcb)) s (0x125815 + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x125815 7 2 (.sib 4 none 0 (.d32 0xcb))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[58, 4]
    (.letOp (n := 78) (.exec 0x12581c (StorePre 0x12581c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xcc)) s (0x12581c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x12581c 6 (.sib 4 none 0 (.d32 0xcc))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 79) (.out 0x125824 (movR32M32LowEffect 0x125824 0 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 80) (.exec 0x125824 (LoadPre 0x125824 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x125824 + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x125824 0 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 81) (.exec 0x12582b (StorePre 0x12582b 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xec)) s (0x12582b + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x12582b 0 (.sib 4 none 0 (.d32 0xec))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[79, 4]
    (b_l1257b7_1)))))))))))))))))))))))))))))

def bytes_l1257b7 : List UInt8 :=
  [0x0F, 0xB6, 0x44, 0x24, 0x10, 0x0F, 0xB7, 0x4C, 0x24, 0x11, 0x66, 0x89, 0x4C, 0x24, 0x60, 0x0F,
    0xB6, 0x54, 0x24, 0x13, 0x88, 0x54, 0x24, 0x62, 0x48, 0x8B, 0x74, 0x24, 0x14, 0x48, 0x8B, 0x7C,
    0x24, 0x1C, 0x48, 0x89, 0xBC, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x7C, 0x24, 0x24, 0x48,
    0x89, 0xBC, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x7C, 0x24, 0x2C, 0x48, 0x89, 0xBC, 0x24,
    0x90, 0x00, 0x00, 0x00, 0x8B, 0x7C, 0x24, 0x34, 0x89, 0xBC, 0x24, 0x98, 0x00, 0x00, 0x00, 0x88,
    0x84, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x66, 0x89, 0x8C, 0x24, 0xC9, 0x00, 0x00, 0x00, 0x88, 0x94,
    0x24, 0xCB, 0x00, 0x00, 0x00, 0x48, 0x89, 0xB4, 0x24, 0xCC, 0x00, 0x00, 0x00, 0x8B, 0x84, 0x24,
    0x98, 0x00, 0x00, 0x00, 0x89, 0x84, 0x24, 0xEC, 0x00, 0x00, 0x00] ++ bytes_l1257b7_1

theorem code_l1257b7 : ∀ x ∈ codeRange 0x1257b7 bytes_l1257b7, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x257b7 123 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1257b7_1

@[cfg_block] def b_l125877 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x125877 (movR32M32LowEffect 0x125877 0 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x125877 (LoadPre 0x125877 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x125877 + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x125877 0 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x12587e (movR64M64Effect 0x12587e 1 (.sib 4 none 0 (.d32 0x84))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x12587e (LoadPre 0x12587e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x84)) s (0x12587e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x12587e 1 (.sib 4 none 0 (.d32 0x84))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x125886 (StorePre 0x125886 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x125886 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x125886 1 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 58) (.out 0x12588e (movR64M64Effect 0x12588e 1 (.sib 4 none 0 (.d32 0x8c))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 59) (.exec 0x12588e (LoadPre 0x12588e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x8c)) s (0x12588e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x12588e 1 (.sib 4 none 0 (.d32 0x8c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.exec 0x125896 (StorePre 0x125896 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x125896 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x125896 1 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[58, 4]
    (.letOp (n := 61) (.out 0x12589e (cmpR32Imm8Effect 0x12589e 3 0 0x2) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[53]
    (.letOp (n := 62) (.exec 0x12589e (fun s => s.RIP = 0x12589e) (cmpR32Imm8Effect 0x12589e 3 0 0x2) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 63) (.pure (condOp 5)) #v[61]
    (.terminate (.condBr (Fin.last 63) ⟨.l125aac, RegMap.args [(0, 53), (1, 58), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 61), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ ⟨.l1258a7, RegMap.args [(0, 53), (1, 58), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 61), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩))))))))))))

def bytes_l125877 : List UInt8 :=
  [0x8B, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x8C, 0x24, 0x84, 0x00, 0x00, 0x00, 0x48,
    0x89, 0x8C, 0x24, 0xF0, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x8C, 0x24, 0x8C, 0x00, 0x00, 0x00, 0x48,
    0x89, 0x8C, 0x24, 0xF8, 0x00, 0x00, 0x00, 0x83, 0xF8, 0x02, 0x0F, 0x85, 0x05, 0x02, 0x00, 0x00]

theorem code_l125877 : ∀ x ∈ codeRange 0x125877 bytes_l125877, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x25877 48 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1258a7 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1258a7 (movR64M64Effect 0x1258a7 6 (.sib 4 none 0 (.d32 0xf0))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 54) (.exec 0x1258a7 (LoadPre 0x1258a7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x1258a7 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1258a7 6 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1258af (movR64M64Effect 0x1258af 0 (.sib 4 none 0 (.d32 0xf8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 56) (.exec 0x1258af (LoadPre 0x1258af (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x1258af + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1258af 0 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x1258b7 (StorePre 0x1258b7 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x1258b7 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1258b7 6 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 58) (.exec 0x1258bf (StorePre 0x1258bf 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x1258bf + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1258bf 0 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 59) (.out 0x1258c7 (leaR64Effect 0x1258c7 7 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 60) (.exec 0x1258c7 (fun s => s.RIP = 0x1258c7) (leaR64Effect 0x1258c7 7 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x1258cf (movR32Imm32Effect 0x1258cf 5 2 0xa) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 62) (.exec 0x1258cf (fun s => s.RIP = 0x1258cf) (movR32Imm32Effect 0x1258cf 5 2 0xa) (Reg.operands [] [])) #v[]
    (.letOp (n := 63) (.out 0x1258d4 (callEffect (fun _ => 0x1276d0) 0x1258d9) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 64) (.exec 0x1258d4 (PushPre 0x1258d4 5) (callEffect (fun _ => 0x1276d0) 0x1258d9) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.const ⟨64, 0x1258d9⟩) #v[]
    (.terminate (.call ⟨.l1276d0, RegMap.args [(0, 55), (1, 1), (2, 61), (3, 3), (4, 63), (5, 5), (6, 53), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩ { target := .l1258d9, kept := #v[], arity := rfl, guard := some (Fin.last 65) }))))))))))))))

def bytes_l1258a7 : List UInt8 :=
  [0x48, 0x8B, 0xB4, 0x24, 0xF0, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x84, 0x24, 0xF8, 0x00, 0x00, 0x00,
    0x48, 0x89, 0xB4, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0xC0, 0x00, 0x00, 0x00,
    0x48, 0x8D, 0xBC, 0x24, 0x80, 0x00, 0x00, 0x00, 0xBA, 0x0A, 0x00, 0x00, 0x00, 0xE8, 0xF7, 0x1D,
    0x00, 0x00]

theorem code_l1258a7 : ∀ x ∈ codeRange 0x1258a7 bytes_l1258a7, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x258a7 50 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1258d9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1258d9 (movR32M32LowEffect 0x1258d9 0 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1258d9 (LoadPre 0x1258d9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1258d9 + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x1258d9 0 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1258e0 (cmpR32Imm8Effect 0x1258e0 3 0 0x2) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x1258e0 (fun s => s.RIP = 0x1258e0) (cmpR32Imm8Effect 0x1258e0 3 0 0x2) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l125b07, RegMap.args [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l1258e9, RegMap.args [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l1258d9 : List UInt8 :=
  [0x8B, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x83, 0xF8, 0x02, 0x0F, 0x85, 0x1E, 0x02, 0x00, 0x00]

theorem code_l1258d9 : ∀ x ∈ codeRange 0x1258d9 bytes_l1258d9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x258d9 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1258e9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1258e9 (leaR64Effect 0x1258e9 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x1258e9 (fun s => s.RIP = 0x1258e9) (leaR64Effect 0x1258e9 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1258ee (leaR64Effect 0x1258ee 6 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 56) (.exec 0x1258ee (fun s => s.RIP = 0x1258ee) (leaR64Effect 0x1258ee 6 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1258f6 (leaR64Effect 0x1258f6 2 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 58) (.exec 0x1258f6 (fun s => s.RIP = 0x1258f6) (leaR64Effect 0x1258f6 2 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x1258fe (callEffect (fun _ => 0x126a30) 0x125903) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x1258fe (PushPre 0x1258fe 5) (callEffect (fun _ => 0x126a30) 0x125903) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x125903⟩) #v[]
    (.terminate (.call ⟨.l126a30, RegMap.args [(1, 1), (2, 57), (3, 3), (4, 59), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l125903, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l1258e9 : List UInt8 :=
  [0x48, 0x8D, 0x7C, 0x24, 0x08, 0x48, 0x8D, 0xB4, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x94,
    0x24, 0xB8, 0x00, 0x00, 0x00, 0xE8, 0x2D, 0x11, 0x00, 0x00]

theorem code_l1258e9 : ∀ x ∈ codeRange 0x1258e9 bytes_l1258e9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x258e9 26 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l125903 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x125903 (movR32M32LowEffect 0x125903 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x125903 (LoadPre 0x125903 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x125903 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x125903 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x125907 (cmpMImm8Effect 0x125907 5 32 (.sib 4 none 0 (.d8 0x8)) 0x1) (EffectPart.reads (.flag .ZF) [.gpr 4] []) (.flag .ZF)) #v[4]
    (.letOp (n := 56) (.exec 0x125907 (LoadPre 0x125907 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x125907 + BitVec.ofNat 64 5)) 4) (cmpMImm8Effect 0x125907 5 32 (.sib 4 none 0 (.d8 0x8)) 0x1) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.pure (condOp 4)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l125b60, RegMap.args [(0, 53), (3, 3), (4, 4), (11, 11), (12, 12), (13, 13), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l125912, RegMap.args [(0, 53), (3, 3), (4, 4), (11, 11), (12, 12), (13, 13), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l125903 : List UInt8 :=
  [0x8B, 0x44, 0x24, 0x10, 0x83, 0x7C, 0x24, 0x08, 0x01, 0x0F, 0x84, 0x4E, 0x02, 0x00, 0x00]

theorem code_l125903 : ∀ x ∈ codeRange 0x125903 bytes_l125903, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x25903 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l125912_1 : Block Op Label signature Reg.count 86 :=
  .letOp (n := 86) (.out 0x125973 (movR64M64Effect 0x125973 10 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 87) (.exec 0x125973 (LoadPre 0x125973 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x125973 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125973 10 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 88) (.exec 0x125978 (StorePre 0x125978 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x125978 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x125978 10 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[86, 4]
    (.letOp (n := 89) (.exec 0x125980 (StorePre 0x125980 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x125980 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x125980 9 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[84, 4]
    (.letOp (n := 90) (.out 0x125988 (movzxR32M16Effect 0x125988 5 9 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 91) (.exec 0x125988 (LoadPre 0x125988 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x125988 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x125988 5 9 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 92) (.exec 0x12598d (StorePre 0x12598d 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x12598d + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x12598d 6 9 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[90, 4]
    (.letOp (n := 93) (.out 0x125993 (movzxR32M8Effect 0x125993 6 9 (.sib 4 none 0 (.d8 0x2))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 94) (.exec 0x125993 (LoadPre 0x125993 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2)) s (0x125993 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x125993 6 9 (.sib 4 none 0 (.d8 0x2))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 95) (.exec 0x125999 (StorePre 0x125999 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6)) s (0x125999 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x125999 5 9 (.sib 4 none 0 (.d8 0x6))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[93, 4]
    (.letOp (n := 96) (.out 0x12599e (movR64M64Effect 0x12599e 9 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 97) (.exec 0x12599e (LoadPre 0x12599e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x12599e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12599e 9 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 98) (.out 0x1259a3 (movR64M64Effect 0x1259a3 10 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 99) (.exec 0x1259a3 (LoadPre 0x1259a3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x1259a3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1259a3 10 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 100) (.exec 0x1259a8 (StorePre 0x1259a8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x1259a8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1259a8 9 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[96, 4]
    (.letOp (n := 101) (.exec 0x1259b0 (StorePre 0x1259b0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x1259b0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1259b0 10 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[98, 4]
    (.letOp (n := 102) (.out 0x1259b8 (movR64M64Effect 0x1259b8 9 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 103) (.exec 0x1259b8 (LoadPre 0x1259b8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x1259b8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1259b8 9 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 104) (.exec 0x1259bd (StorePre 0x1259bd 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x1259bd + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1259bd 9 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[102, 4]
    (.letOp (n := 105) (.out 0x1259c5 (movR32M32Effect 0x1259c5 9 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 106) (.exec 0x1259c5 (LoadPre 0x1259c5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1259c5 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x1259c5 9 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 107) (.exec 0x1259ca (StorePre 0x1259ca 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x1259ca + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x1259ca 9 (.sib 4 none 0 (.d32 0x118))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[105, 4]
    (.letOp (n := 108) (.out 0x1259d2 (movR32M32Effect 0x1259d2 9 (.sib 4 none 0 (.d32 0xe4))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 109) (.exec 0x1259d2 (LoadPre 0x1259d2 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe4)) s (0x1259d2 + BitVec.ofNat 64 8)) 4) (movR32M32Effect 0x1259d2 9 (.sib 4 none 0 (.d32 0xe4))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 110) (.out 0x1259da (movR32Imm32Effect 0x1259da 5 5 0x1) (EffectPart.reads (.reg (.gpr 5)) [] []) (.reg (.gpr 5))) #v[]
    (.letOp (n := 111) (.exec 0x1259da (fun s => s.RIP = 0x1259da) (movR32Imm32Effect 0x1259da 5 5 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 112) (.out 0x1259df (testM8Imm8Effect 0x1259df 8 (.sib 4 none 0 (.d32 0xe8)) 0x1) (EffectPart.reads (.flag .ZF) [.gpr 4] []) (.flag .ZF)) #v[4]
    (.letOp (n := 113) (.exec 0x1259df (LoadPre 0x1259df (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x1259df + BitVec.ofNat 64 8)) 1) (testM8Imm8Effect 0x1259df 8 (.sib 4 none 0 (.d32 0xe8)) 0x1) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 114) (.pure (condOp 4)) #v[112]
    (.terminate (.condBr (Fin.last 114) ⟨.l125cb5, RegMap.args [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (5, 110), (6, 79), (7, 53), (8, 65), (9, 108), (10, 98), (11, 11), (12, 12), (13, 13), (19, 112), (22, 22), (39, 39), (50, 50), (51, 51)] 115⟩ ⟨.l1259ed, RegMap.args [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (5, 110), (6, 79), (7, 53), (8, 65), (9, 108), (10, 98), (11, 11), (12, 12), (13, 13), (19, 112), (22, 22), (39, 39), (50, 50), (51, 51)] 115⟩))))))))))))))))))))))))))))))

def bytes_l125912_1 : List UInt8 :=
  [0x4C, 0x8B, 0x54, 0x24, 0x50, 0x4C, 0x89, 0x94, 0x24, 0x28, 0x01, 0x00, 0x00, 0x4C, 0x89, 0x8C,
    0x24, 0x20, 0x01, 0x00, 0x00, 0x44, 0x0F, 0xB7, 0x0C, 0x24, 0x66, 0x44, 0x89, 0x4C, 0x24, 0x04,
    0x44, 0x0F, 0xB6, 0x4C, 0x24, 0x02, 0x44, 0x88, 0x4C, 0x24, 0x06, 0x4C, 0x8B, 0x4C, 0x24, 0x60,
    0x4C, 0x8B, 0x54, 0x24, 0x68, 0x4C, 0x89, 0x8C, 0x24, 0x00, 0x01, 0x00, 0x00, 0x4C, 0x89, 0x94,
    0x24, 0x08, 0x01, 0x00, 0x00, 0x4C, 0x8B, 0x4C, 0x24, 0x70, 0x4C, 0x89, 0x8C, 0x24, 0x10, 0x01,
    0x00, 0x00, 0x44, 0x8B, 0x4C, 0x24, 0x78, 0x44, 0x89, 0x8C, 0x24, 0x18, 0x01, 0x00, 0x00, 0x44,
    0x8B, 0x8C, 0x24, 0xE4, 0x00, 0x00, 0x00, 0xBD, 0x01, 0x00, 0x00, 0x00, 0xF6, 0x84, 0x24, 0xE8,
    0x00, 0x00, 0x00, 0x01, 0x0F, 0x84, 0xC8, 0x02, 0x00, 0x00]

theorem code_l125912_1 : ∀ x ∈ codeRange 0x125973 bytes_l125912_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x25973 122 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l125912 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x125912 (movR32M32LowEffect 0x125912 7 (.sib 4 none 0 (.d8 0x14))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x125912 (LoadPre 0x125912 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x125912 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x125912 7 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x125916 (movzxR32M8Effect 0x125916 5 1 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x125916 (LoadPre 0x125916 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x125916 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x125916 5 1 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x12591b (movzxR32M16Effect 0x12591b 5 2 (.sib 4 none 0 (.d8 0x19))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 58) (.exec 0x12591b (LoadPre 0x12591b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x19)) s (0x12591b + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x12591b 5 2 (.sib 4 none 0 (.d8 0x19))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.exec 0x125920 (StorePre 0x125920 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x125920 + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x125920 4 2 (.sib 4 none 0 .none)) (Reg.operands [.gpr 2, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 60) (.out 0x125924 (movzxR32M8Effect 0x125924 5 2 (.sib 4 none 0 (.d8 0x1b))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 61) (.exec 0x125924 (LoadPre 0x125924 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1b)) s (0x125924 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x125924 5 2 (.sib 4 none 0 (.d8 0x1b))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.exec 0x125929 (StorePre 0x125929 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2)) s (0x125929 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x125929 4 2 (.sib 4 none 0 (.d8 0x2))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[60, 4]
    (.letOp (n := 63) (.out 0x12592d (movR32M32LowEffect 0x12592d 2 (.sib 4 none 0 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 64) (.exec 0x12592d (LoadPre 0x12592d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x12592d + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x12592d 2 (.sib 4 none 0 (.d8 0x1c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x125931 (movR32M32Effect 0x125931 8 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 66) (.exec 0x125931 (LoadPre 0x125931 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x125931 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x125931 8 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x125936 (movR64M64Effect 0x125936 6 (.sib 4 none 0 (.d8 0x24))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 68) (.exec 0x125936 (LoadPre 0x125936 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x125936 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125936 6 (.sib 4 none 0 (.d8 0x24))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.exec 0x12593b (StorePre 0x12593b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x12593b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12593b 6 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[67, 4]
    (.letOp (n := 70) (.out 0x125940 (movR64M64Effect 0x125940 6 (.sib 4 none 0 (.d8 0x2c))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 71) (.exec 0x125940 (LoadPre 0x125940 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x125940 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125940 6 (.sib 4 none 0 (.d8 0x2c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.exec 0x125945 (StorePre 0x125945 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x125945 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125945 6 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[70, 4]
    (.letOp (n := 73) (.out 0x12594a (movR64M64Effect 0x12594a 6 (.sib 4 none 0 (.d8 0x34))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 74) (.exec 0x12594a (LoadPre 0x12594a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x12594a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12594a 6 (.sib 4 none 0 (.d8 0x34))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.exec 0x12594f (StorePre 0x12594f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x12594f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12594f 6 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[73, 4]
    (.letOp (n := 76) (.out 0x125954 (movR32M32LowEffect 0x125954 6 (.sib 4 none 0 (.d8 0x3c))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 77) (.exec 0x125954 (LoadPre 0x125954 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x125954 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x125954 6 (.sib 4 none 0 (.d8 0x3c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 78) (.exec 0x125958 (StorePre 0x125958 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x125958 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x125958 6 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[76, 4]
    (.letOp (n := 79) (.out 0x12595c (movR64M64Effect 0x12595c 6 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 80) (.exec 0x12595c (LoadPre 0x12595c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x12595c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12595c 6 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 81) (.out 0x125961 (movR64M64Effect 0x125961 9 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 82) (.exec 0x125961 (LoadPre 0x125961 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x125961 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125961 9 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 83) (.exec 0x125966 (StorePre 0x125966 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x125966 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x125966 9 (.sib 4 none 0 (.d32 0x130))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[81, 4]
    (.letOp (n := 84) (.out 0x12596e (movR64M64Effect 0x12596e 9 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 85) (.exec 0x12596e (LoadPre 0x12596e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x12596e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12596e 9 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l125912_1)))))))))))))))))))))))))))))))))

def bytes_l125912 : List UInt8 :=
  [0x8B, 0x7C, 0x24, 0x14, 0x0F, 0xB6, 0x4C, 0x24, 0x18, 0x0F, 0xB7, 0x54, 0x24, 0x19, 0x66, 0x89,
    0x14, 0x24, 0x0F, 0xB6, 0x54, 0x24, 0x1B, 0x88, 0x54, 0x24, 0x02, 0x8B, 0x54, 0x24, 0x1C, 0x44,
    0x8B, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x74, 0x24, 0x24, 0x48, 0x89, 0x74, 0x24, 0x60, 0x48, 0x8B,
    0x74, 0x24, 0x2C, 0x48, 0x89, 0x74, 0x24, 0x68, 0x48, 0x8B, 0x74, 0x24, 0x34, 0x48, 0x89, 0x74,
    0x24, 0x70, 0x8B, 0x74, 0x24, 0x3C, 0x89, 0x74, 0x24, 0x78, 0x48, 0x8B, 0x74, 0x24, 0x40, 0x4C,
    0x8B, 0x4C, 0x24, 0x58, 0x4C, 0x89, 0x8C, 0x24, 0x30, 0x01, 0x00, 0x00, 0x4C, 0x8B, 0x4C, 0x24,
    0x48] ++ bytes_l125912_1

theorem code_l125912 : ∀ x ∈ codeRange 0x125912 bytes_l125912, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x25912 97 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l125912_1

@[cfg_block] def b_l1259ed : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1259ed (movR8Imm8Effect 0x1259ed 2 1 0x2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1]
    (.letOp (n := 54) (.exec 0x1259ed (fun s => s.RIP = 0x1259ed) (movR8Imm8Effect 0x1259ed 2 1 0x2) (Reg.operands [.gpr 1] [])) #v[1]
    (.terminate (.br ⟨.l125bf1, RegMap.args [(1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l1259ed : List UInt8 :=
  [0xB1, 0x02, 0xE9, 0xFD, 0x01, 0x00, 0x00]

theorem code_l1259ed : ∀ x ∈ codeRange 0x1259ed bytes_l1259ed, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x259ed 7 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1259f4_1 : Block Op Label signature Reg.count 86 :=
  .letOp (n := 86) (.exec 0x125a64 (StorePre 0x125a64 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x125a64 + BitVec.ofNat 64 9)) 2) (movM16R16Effect 0x125a64 9 9 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[84, 4]
    (.letOp (n := 87) (.out 0x125a6d (movR32M32Effect 0x125a6d 9 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 88) (.exec 0x125a6d (LoadPre 0x125a6d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x125a6d + BitVec.ofNat 64 8)) 4) (movR32M32Effect 0x125a6d 9 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 89) (.exec 0x125a75 (StorePre 0x125a75 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x125a75 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x125a75 9 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[87, 4]
    (.letOp (n := 90) (.out 0x125a7a (movR64M64Effect 0x125a7a 9 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 91) (.exec 0x125a7a (LoadPre 0x125a7a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x125a7a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125a7a 9 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 92) (.exec 0x125a82 (StorePre 0x125a82 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x125a82 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125a82 9 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[90, 4]
    (.letOp (n := 93) (.out 0x125a87 (movR64M64Effect 0x125a87 9 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 94) (.exec 0x125a87 (LoadPre 0x125a87 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x125a87 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125a87 9 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 95) (.out 0x125a8f (movR64M64Effect 0x125a8f 10 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 96) (.exec 0x125a8f (LoadPre 0x125a8f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x125a8f + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125a8f 10 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 97) (.exec 0x125a97 (StorePre 0x125a97 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x125a97 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125a97 10 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[95, 4]
    (.letOp (n := 98) (.exec 0x125a9c (StorePre 0x125a9c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x125a9c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125a9c 9 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[93, 4]
    (.letOp (n := 99) (.out 0x125aa1 (movR32Imm32Effect 0x125aa1 6 10 0x1) (EffectPart.reads (.reg (.gpr 10)) [] []) (.reg (.gpr 10))) #v[]
    (.letOp (n := 100) (.exec 0x125aa1 (fun s => s.RIP = 0x125aa1) (movR32Imm32Effect 0x125aa1 6 10 0x1) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l125bff, RegMap.args [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 79), (7, 53), (8, 65), (9, 93), (10, 99), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)] 101⟩))))))))))))))))

def bytes_l1259f4_1 : List UInt8 :=
  [0x66, 0x44, 0x89, 0x8C, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x44, 0x8B, 0x8C, 0x24, 0x98, 0x00, 0x00,
    0x00, 0x44, 0x89, 0x4C, 0x24, 0x20, 0x4C, 0x8B, 0x8C, 0x24, 0x90, 0x00, 0x00, 0x00, 0x4C, 0x89,
    0x4C, 0x24, 0x18, 0x4C, 0x8B, 0x8C, 0x24, 0x80, 0x00, 0x00, 0x00, 0x4C, 0x8B, 0x94, 0x24, 0x88,
    0x00, 0x00, 0x00, 0x4C, 0x89, 0x54, 0x24, 0x10, 0x4C, 0x89, 0x4C, 0x24, 0x08, 0x41, 0xBA, 0x01,
    0x00, 0x00, 0x00, 0xE9, 0x53, 0x01, 0x00, 0x00]

theorem code_l1259f4_1 : ∀ x ∈ codeRange 0x125a64 bytes_l1259f4_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x25a64 72 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1259f4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1259f4 (movR32M32LowEffect 0x1259f4 7 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x1259f4 (LoadPre 0x1259f4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x1259f4 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1259f4 7 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1259f8 (movzxR32M8Effect 0x1259f8 5 1 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x1259f8 (LoadPre 0x1259f8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1259f8 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1259f8 5 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1259fd (movzxR32M16Effect 0x1259fd 5 2 (.sib 4 none 0 (.d8 0x11))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 58) (.exec 0x1259fd (LoadPre 0x1259fd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x11)) s (0x1259fd + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x1259fd 5 2 (.sib 4 none 0 (.d8 0x11))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.exec 0x125a02 (StorePre 0x125a02 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x125a02 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x125a02 5 2 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 60) (.out 0x125a07 (movzxR32M8Effect 0x125a07 5 2 (.sib 4 none 0 (.d8 0x13))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 61) (.exec 0x125a07 (LoadPre 0x125a07 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x13)) s (0x125a07 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x125a07 5 2 (.sib 4 none 0 (.d8 0x13))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.exec 0x125a0c (StorePre 0x125a0c 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x62)) s (0x125a0c + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x125a0c 4 2 (.sib 4 none 0 (.d8 0x62))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[60, 4]
    (.letOp (n := 63) (.out 0x125a10 (movR32M32LowEffect 0x125a10 2 (.sib 4 none 0 (.d8 0x14))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 64) (.exec 0x125a10 (LoadPre 0x125a10 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x125a10 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x125a10 2 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x125a14 (movR32M32Effect 0x125a14 8 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 66) (.exec 0x125a14 (LoadPre 0x125a14 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x125a14 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x125a14 8 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x125a19 (movR64M64Effect 0x125a19 6 (.sib 4 none 0 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 68) (.exec 0x125a19 (LoadPre 0x125a19 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x125a19 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125a19 6 (.sib 4 none 0 (.d8 0x1c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.exec 0x125a1e (StorePre 0x125a1e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x125a1e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x125a1e 6 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[67, 4]
    (.letOp (n := 70) (.out 0x125a26 (movR64M64Effect 0x125a26 6 (.sib 4 none 0 (.d8 0x24))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 71) (.exec 0x125a26 (LoadPre 0x125a26 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x125a26 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125a26 6 (.sib 4 none 0 (.d8 0x24))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.exec 0x125a2b (StorePre 0x125a2b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x125a2b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x125a2b 6 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[70, 4]
    (.letOp (n := 73) (.out 0x125a33 (movR64M64Effect 0x125a33 6 (.sib 4 none 0 (.d8 0x2c))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 74) (.exec 0x125a33 (LoadPre 0x125a33 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x125a33 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125a33 6 (.sib 4 none 0 (.d8 0x2c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.exec 0x125a38 (StorePre 0x125a38 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x125a38 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x125a38 6 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[73, 4]
    (.letOp (n := 76) (.out 0x125a40 (movR32M32LowEffect 0x125a40 6 (.sib 4 none 0 (.d8 0x34))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 77) (.exec 0x125a40 (LoadPre 0x125a40 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x125a40 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x125a40 6 (.sib 4 none 0 (.d8 0x34))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 78) (.exec 0x125a44 (StorePre 0x125a44 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x125a44 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x125a44 6 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[76, 4]
    (.letOp (n := 79) (.out 0x125a4b (movR64M64Effect 0x125a4b 6 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 80) (.exec 0x125a4b (LoadPre 0x125a4b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x125a4b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125a4b 6 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 81) (.out 0x125a50 (movzxR32M8Effect 0x125a50 6 9 (.sib 4 none 0 (.d8 0x62))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 82) (.exec 0x125a50 (LoadPre 0x125a50 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x62)) s (0x125a50 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x125a50 6 9 (.sib 4 none 0 (.d8 0x62))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 83) (.exec 0x125a56 (StorePre 0x125a56 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xba)) s (0x125a56 + BitVec.ofNat 64 8)) 1) (movM8R8Effect 0x125a56 8 9 (.sib 4 none 0 (.d32 0xba))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[81, 4]
    (.letOp (n := 84) (.out 0x125a5e (movzxR32M16Effect 0x125a5e 6 9 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 85) (.exec 0x125a5e (LoadPre 0x125a5e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x125a5e + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x125a5e 6 9 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l1259f4_1)))))))))))))))))))))))))))))))))

def bytes_l1259f4 : List UInt8 :=
  [0x8B, 0x7C, 0x24, 0x0C, 0x0F, 0xB6, 0x4C, 0x24, 0x10, 0x0F, 0xB7, 0x54, 0x24, 0x11, 0x66, 0x89,
    0x54, 0x24, 0x60, 0x0F, 0xB6, 0x54, 0x24, 0x13, 0x88, 0x54, 0x24, 0x62, 0x8B, 0x54, 0x24, 0x14,
    0x44, 0x8B, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x74, 0x24, 0x1C, 0x48, 0x89, 0xB4, 0x24, 0x80, 0x00,
    0x00, 0x00, 0x48, 0x8B, 0x74, 0x24, 0x24, 0x48, 0x89, 0xB4, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48,
    0x8B, 0x74, 0x24, 0x2C, 0x48, 0x89, 0xB4, 0x24, 0x90, 0x00, 0x00, 0x00, 0x8B, 0x74, 0x24, 0x34,
    0x89, 0xB4, 0x24, 0x98, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x74, 0x24, 0x38, 0x44, 0x0F, 0xB6, 0x4C,
    0x24, 0x62, 0x44, 0x88, 0x8C, 0x24, 0xBA, 0x00, 0x00, 0x00, 0x44, 0x0F, 0xB7, 0x4C, 0x24, 0x60] ++ bytes_l1259f4_1

theorem code_l1259f4 : ∀ x ∈ codeRange 0x1259f4 bytes_l1259f4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x259f4 112 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1259f4_1

@[cfg_block] def b_l125aac : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x125aac (movR32M32LowEffect 0x125aac 1 (.sib 4 none 0 (.d32 0xb4))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x125aac (LoadPre 0x125aac (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb4)) s (0x125aac + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x125aac 1 (.sib 4 none 0 (.d32 0xb4))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x125ab3 (StorePre 0x125ab3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x125ab3 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x125ab3 1 (.sib 4 none 0 (.d8 0x44))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x125ab7 (movR64M64Effect 0x125ab7 1 (.sib 4 none 0 (.d32 0xac))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 57) (.exec 0x125ab7 (LoadPre 0x125ab7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xac)) s (0x125ab7 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125ab7 1 (.sib 4 none 0 (.d32 0xac))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x125abf (StorePre 0x125abf 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x125abf + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125abf 1 (.sib 4 none 0 (.d8 0x3c))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x125ac4 (movR64M64Effect 0x125ac4 1 (.sib 4 none 0 (.d32 0xa4))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 60) (.exec 0x125ac4 (LoadPre 0x125ac4 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa4)) s (0x125ac4 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125ac4 1 (.sib 4 none 0 (.d32 0xa4))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x125acc (StorePre 0x125acc 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x125acc + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125acc 1 (.sib 4 none 0 (.d8 0x34))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x125ad1 (movR64M64Effect 0x125ad1 1 (.sib 4 none 0 (.d32 0x94))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 63) (.exec 0x125ad1 (LoadPre 0x125ad1 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x94)) s (0x125ad1 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125ad1 1 (.sib 4 none 0 (.d32 0x94))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x125ad9 (movR64M64Effect 0x125ad9 2 (.sib 4 none 0 (.d32 0x9c))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 65) (.exec 0x125ad9 (LoadPre 0x125ad9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9c)) s (0x125ad9 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125ad9 2 (.sib 4 none 0 (.d32 0x9c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x125ae1 (StorePre 0x125ae1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x125ae1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125ae1 2 (.sib 4 none 0 (.d8 0x2c))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x125ae6 (StorePre 0x125ae6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x125ae6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125ae6 1 (.sib 4 none 0 (.d8 0x24))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x125aeb (movR64M64Effect 0x125aeb 1 (.sib 4 none 0 (.d32 0xf0))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 69) (.exec 0x125aeb (LoadPre 0x125aeb (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x125aeb + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125aeb 1 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.out 0x125af3 (movR64M64Effect 0x125af3 2 (.sib 4 none 0 (.d32 0xf8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 71) (.exec 0x125af3 (LoadPre 0x125af3 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x125af3 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125af3 2 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.exec 0x125afb (StorePre 0x125afb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x125afb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125afb 1 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[68, 4]
    (.letOp (n := 73) (.exec 0x125b00 (StorePre 0x125b00 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x125b00 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125b00 2 (.sib 4 none 0 (.d8 0x1c))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[70, 4]
    (.terminate (.br ⟨.l125b60, RegMap.args [(0, 0), (1, 68), (2, 70), (3, 3), (4, 4), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)] 74⟩))))))))))))))))))))))

def bytes_l125aac : List UInt8 :=
  [0x8B, 0x8C, 0x24, 0xB4, 0x00, 0x00, 0x00, 0x89, 0x4C, 0x24, 0x44, 0x48, 0x8B, 0x8C, 0x24, 0xAC,
    0x00, 0x00, 0x00, 0x48, 0x89, 0x4C, 0x24, 0x3C, 0x48, 0x8B, 0x8C, 0x24, 0xA4, 0x00, 0x00, 0x00,
    0x48, 0x89, 0x4C, 0x24, 0x34, 0x48, 0x8B, 0x8C, 0x24, 0x94, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x94,
    0x24, 0x9C, 0x00, 0x00, 0x00, 0x48, 0x89, 0x54, 0x24, 0x2C, 0x48, 0x89, 0x4C, 0x24, 0x24, 0x48,
    0x8B, 0x8C, 0x24, 0xF0, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x94, 0x24, 0xF8, 0x00, 0x00, 0x00, 0x48,
    0x89, 0x4C, 0x24, 0x14, 0x48, 0x89, 0x54, 0x24, 0x1C, 0xEB, 0x59]

theorem code_l125aac : ∀ x ∈ codeRange 0x125aac bytes_l125aac, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x25aac 91 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l125b07 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x125b07 (movR64M64Effect 0x125b07 1 (.sib 4 none 0 (.d32 0x84))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x125b07 (LoadPre 0x125b07 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x84)) s (0x125b07 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125b07 1 (.sib 4 none 0 (.d32 0x84))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x125b0f (movR64M64Effect 0x125b0f 2 (.sib 4 none 0 (.d32 0x8c))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 56) (.exec 0x125b0f (LoadPre 0x125b0f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x8c)) s (0x125b0f + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125b0f 2 (.sib 4 none 0 (.d32 0x8c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x125b17 (StorePre 0x125b17 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x125b17 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125b17 2 (.sib 4 none 0 (.d8 0x1c))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 58) (.out 0x125b1c (movR64M64Effect 0x125b1c 2 (.sib 4 none 0 (.d32 0x94))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 59) (.exec 0x125b1c (LoadPre 0x125b1c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x94)) s (0x125b1c + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125b1c 2 (.sib 4 none 0 (.d32 0x94))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.exec 0x125b24 (StorePre 0x125b24 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x125b24 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125b24 2 (.sib 4 none 0 (.d8 0x24))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[58, 4]
    (.letOp (n := 61) (.out 0x125b29 (movR64M64Effect 0x125b29 2 (.sib 4 none 0 (.d32 0x9c))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 62) (.exec 0x125b29 (LoadPre 0x125b29 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9c)) s (0x125b29 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125b29 2 (.sib 4 none 0 (.d32 0x9c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x125b31 (StorePre 0x125b31 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x125b31 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125b31 2 (.sib 4 none 0 (.d8 0x2c))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.out 0x125b36 (movR64M64Effect 0x125b36 2 (.sib 4 none 0 (.d32 0xa4))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 65) (.exec 0x125b36 (LoadPre 0x125b36 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa4)) s (0x125b36 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125b36 2 (.sib 4 none 0 (.d32 0xa4))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x125b3e (StorePre 0x125b3e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x125b3e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125b3e 2 (.sib 4 none 0 (.d8 0x34))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.out 0x125b43 (movR64M64Effect 0x125b43 2 (.sib 4 none 0 (.d32 0xac))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 68) (.exec 0x125b43 (LoadPre 0x125b43 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xac)) s (0x125b43 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125b43 2 (.sib 4 none 0 (.d32 0xac))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.exec 0x125b4b (StorePre 0x125b4b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x125b4b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125b4b 2 (.sib 4 none 0 (.d8 0x3c))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[67, 4]
    (.letOp (n := 70) (.out 0x125b50 (movR32M32LowEffect 0x125b50 2 (.sib 4 none 0 (.d32 0xb4))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 71) (.exec 0x125b50 (LoadPre 0x125b50 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb4)) s (0x125b50 + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x125b50 2 (.sib 4 none 0 (.d32 0xb4))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.exec 0x125b57 (StorePre 0x125b57 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x125b57 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x125b57 2 (.sib 4 none 0 (.d8 0x44))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[70, 4]
    (.letOp (n := 73) (.exec 0x125b5b (StorePre 0x125b5b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x125b5b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125b5b 1 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[53, 4]
    (.terminate (.br ⟨.l125b60, RegMap.args [(0, 0), (1, 53), (2, 70), (3, 3), (4, 4), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)] 74⟩))))))))))))))))))))))

def bytes_l125b07 : List UInt8 :=
  [0x48, 0x8B, 0x8C, 0x24, 0x84, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x94, 0x24, 0x8C, 0x00, 0x00, 0x00,
    0x48, 0x89, 0x54, 0x24, 0x1C, 0x48, 0x8B, 0x94, 0x24, 0x94, 0x00, 0x00, 0x00, 0x48, 0x89, 0x54,
    0x24, 0x24, 0x48, 0x8B, 0x94, 0x24, 0x9C, 0x00, 0x00, 0x00, 0x48, 0x89, 0x54, 0x24, 0x2C, 0x48,
    0x8B, 0x94, 0x24, 0xA4, 0x00, 0x00, 0x00, 0x48, 0x89, 0x54, 0x24, 0x34, 0x48, 0x8B, 0x94, 0x24,
    0xAC, 0x00, 0x00, 0x00, 0x48, 0x89, 0x54, 0x24, 0x3C, 0x8B, 0x94, 0x24, 0xB4, 0x00, 0x00, 0x00,
    0x89, 0x54, 0x24, 0x44, 0x48, 0x89, 0x4C, 0x24, 0x14]

theorem code_l125b07 : ∀ x ∈ codeRange 0x125b07 bytes_l125b07, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x25b07 89 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l125b60_1 : Block Op Label signature Reg.count 86 :=
  .letOp (n := 86) (.exec 0x125bc1 (StorePre 0x125bc1 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x125bc1 + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x125bc1 8 7 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[84, 4]
    (.letOp (n := 87) (.out 0x125bc9 (movR32M32LowEffect 0x125bc9 7 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 88) (.exec 0x125bc9 (LoadPre 0x125bc9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x125bc9 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x125bc9 7 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 89) (.exec 0x125bcd (StorePre 0x125bcd 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x125bcd + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x125bcd 7 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[87, 4]
    (.letOp (n := 90) (.out 0x125bd1 (movR64M64Effect 0x125bd1 7 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 91) (.exec 0x125bd1 (LoadPre 0x125bd1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x125bd1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125bd1 7 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 92) (.exec 0x125bd6 (StorePre 0x125bd6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x125bd6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125bd6 7 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[90, 4]
    (.letOp (n := 93) (.out 0x125bdb (movR64M64Effect 0x125bdb 7 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 94) (.exec 0x125bdb (LoadPre 0x125bdb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x125bdb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125bdb 7 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 95) (.out 0x125be0 (movR64M64Effect 0x125be0 8 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 96) (.exec 0x125be0 (LoadPre 0x125be0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x125be0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125be0 8 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 97) (.exec 0x125be5 (StorePre 0x125be5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x125be5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125be5 8 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[95, 4]
    (.letOp (n := 98) (.exec 0x125bea (StorePre 0x125bea 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x125bea + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125bea 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[93, 4]
    (.letOp (n := 99) (.out 0x125bef (movR32R32Effect 0x125bef 2 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[0]
    (.letOp (n := 100) (.exec 0x125bef (fun s => s.RIP = 0x125bef) (movR32R32Effect 0x125bef 2 5 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.terminate (.br ⟨.l125bf1, RegMap.args [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (5, 99), (6, 79), (7, 93), (8, 95), (9, 53), (11, 65), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)] 101⟩))))))))))))))))

def bytes_l125b60_1 : List UInt8 :=
  [0x66, 0x89, 0xBC, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x8B, 0x7C, 0x24, 0x78, 0x89, 0x7C, 0x24, 0x20,
    0x48, 0x8B, 0x7C, 0x24, 0x70, 0x48, 0x89, 0x7C, 0x24, 0x18, 0x48, 0x8B, 0x7C, 0x24, 0x60, 0x4C,
    0x8B, 0x44, 0x24, 0x68, 0x4C, 0x89, 0x44, 0x24, 0x10, 0x48, 0x89, 0x7C, 0x24, 0x08, 0x89, 0xC5]

theorem code_l125b60_1 : ∀ x ∈ codeRange 0x125bc1 bytes_l125b60_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x25bc1 48 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l125b60 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x125b60 (movR32M32Effect 0x125b60 9 (.sib 4 none 0 (.d8 0x14))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 54) (.exec 0x125b60 (LoadPre 0x125b60 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x125b60 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x125b60 9 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x125b65 (movzxR32M8Effect 0x125b65 5 1 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x125b65 (LoadPre 0x125b65 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x125b65 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x125b65 5 1 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x125b6a (movzxR32M16Effect 0x125b6a 5 2 (.sib 4 none 0 (.d8 0x19))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 58) (.exec 0x125b6a (LoadPre 0x125b6a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x19)) s (0x125b6a + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x125b6a 5 2 (.sib 4 none 0 (.d8 0x19))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.exec 0x125b6f (StorePre 0x125b6f 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x125b6f + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x125b6f 4 2 (.sib 4 none 0 .none)) (Reg.operands [.gpr 2, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 60) (.out 0x125b73 (movzxR32M8Effect 0x125b73 5 2 (.sib 4 none 0 (.d8 0x1b))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 61) (.exec 0x125b73 (LoadPre 0x125b73 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1b)) s (0x125b73 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x125b73 5 2 (.sib 4 none 0 (.d8 0x1b))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.exec 0x125b78 (StorePre 0x125b78 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2)) s (0x125b78 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x125b78 4 2 (.sib 4 none 0 (.d8 0x2))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[60, 4]
    (.letOp (n := 63) (.out 0x125b7c (movR32M32LowEffect 0x125b7c 2 (.sib 4 none 0 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 64) (.exec 0x125b7c (LoadPre 0x125b7c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x125b7c + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x125b7c 2 (.sib 4 none 0 (.d8 0x1c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x125b80 (movR32M32Effect 0x125b80 11 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 66) (.exec 0x125b80 (LoadPre 0x125b80 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x125b80 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x125b80 11 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x125b85 (movR64M64Effect 0x125b85 6 (.sib 4 none 0 (.d8 0x24))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 68) (.exec 0x125b85 (LoadPre 0x125b85 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x125b85 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125b85 6 (.sib 4 none 0 (.d8 0x24))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.exec 0x125b8a (StorePre 0x125b8a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x125b8a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125b8a 6 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[67, 4]
    (.letOp (n := 70) (.out 0x125b8f (movR64M64Effect 0x125b8f 6 (.sib 4 none 0 (.d8 0x2c))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 71) (.exec 0x125b8f (LoadPre 0x125b8f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x125b8f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125b8f 6 (.sib 4 none 0 (.d8 0x2c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.exec 0x125b94 (StorePre 0x125b94 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x125b94 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125b94 6 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[70, 4]
    (.letOp (n := 73) (.out 0x125b99 (movR64M64Effect 0x125b99 6 (.sib 4 none 0 (.d8 0x34))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 74) (.exec 0x125b99 (LoadPre 0x125b99 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x125b99 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125b99 6 (.sib 4 none 0 (.d8 0x34))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.exec 0x125b9e (StorePre 0x125b9e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x125b9e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125b9e 6 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[73, 4]
    (.letOp (n := 76) (.out 0x125ba3 (movR32M32LowEffect 0x125ba3 6 (.sib 4 none 0 (.d8 0x3c))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 77) (.exec 0x125ba3 (LoadPre 0x125ba3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x125ba3 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x125ba3 6 (.sib 4 none 0 (.d8 0x3c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 78) (.exec 0x125ba7 (StorePre 0x125ba7 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x125ba7 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x125ba7 6 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[76, 4]
    (.letOp (n := 79) (.out 0x125bab (movR64M64Effect 0x125bab 6 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 80) (.exec 0x125bab (LoadPre 0x125bab (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x125bab + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125bab 6 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 81) (.out 0x125bb0 (movzxR32M8Effect 0x125bb0 5 7 (.sib 4 none 0 (.d8 0x2))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 82) (.exec 0x125bb0 (LoadPre 0x125bb0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2)) s (0x125bb0 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x125bb0 5 7 (.sib 4 none 0 (.d8 0x2))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 83) (.exec 0x125bb5 (StorePre 0x125bb5 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xba)) s (0x125bb5 + BitVec.ofNat 64 8)) 1) (movM8R8Effect 0x125bb5 8 7 (.sib 4 none 0 (.d32 0xba))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[81, 4]
    (.letOp (n := 84) (.out 0x125bbd (movzxR32M16Effect 0x125bbd 4 7 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 85) (.exec 0x125bbd (LoadPre 0x125bbd (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x125bbd + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x125bbd 4 7 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l125b60_1)))))))))))))))))))))))))))))))))

def bytes_l125b60 : List UInt8 :=
  [0x44, 0x8B, 0x4C, 0x24, 0x14, 0x0F, 0xB6, 0x4C, 0x24, 0x18, 0x0F, 0xB7, 0x54, 0x24, 0x19, 0x66,
    0x89, 0x14, 0x24, 0x0F, 0xB6, 0x54, 0x24, 0x1B, 0x88, 0x54, 0x24, 0x02, 0x8B, 0x54, 0x24, 0x1C,
    0x44, 0x8B, 0x5C, 0x24, 0x20, 0x48, 0x8B, 0x74, 0x24, 0x24, 0x48, 0x89, 0x74, 0x24, 0x60, 0x48,
    0x8B, 0x74, 0x24, 0x2C, 0x48, 0x89, 0x74, 0x24, 0x68, 0x48, 0x8B, 0x74, 0x24, 0x34, 0x48, 0x89,
    0x74, 0x24, 0x70, 0x8B, 0x74, 0x24, 0x3C, 0x89, 0x74, 0x24, 0x78, 0x48, 0x8B, 0x74, 0x24, 0x40,
    0x0F, 0xB6, 0x7C, 0x24, 0x02, 0x40, 0x88, 0xBC, 0x24, 0xBA, 0x00, 0x00, 0x00, 0x0F, 0xB7, 0x3C,
    0x24] ++ bytes_l125b60_1

theorem code_l125b60 : ∀ x ∈ codeRange 0x125b60 bytes_l125b60, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x25b60 97 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l125b60_1

@[cfg_block] def b_l125bf1 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x125bf1 (movR32Imm32Effect 0x125bf1 6 10 0x1) (EffectPart.reads (.reg (.gpr 10)) [] []) (.reg (.gpr 10))) #v[]
    (.letOp (n := 54) (.exec 0x125bf1 (fun s => s.RIP = 0x125bf1) (movR32Imm32Effect 0x125bf1 6 10 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x125bf7 (movR32R32Effect 0x125bf7 2 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[5]
    (.letOp (n := 56) (.exec 0x125bf7 (fun s => s.RIP = 0x125bf7) (movR32R32Effect 0x125bf7 2 0 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 57) (.out 0x125bf9 (movR32R32Effect 0x125bf9 3 7 9) (EffectPart.reads (.reg (.gpr 7)) [.gpr 9] []) (.reg (.gpr 7))) #v[9]
    (.letOp (n := 58) (.exec 0x125bf9 (fun s => s.RIP = 0x125bf9) (movR32R32Effect 0x125bf9 3 7 9) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 59) (.out 0x125bfc (movR32R32Effect 0x125bfc 3 8 11) (EffectPart.reads (.reg (.gpr 8)) [.gpr 11] []) (.reg (.gpr 8))) #v[11]
    (.letOp (n := 60) (.exec 0x125bfc (fun s => s.RIP = 0x125bfc) (movR32R32Effect 0x125bfc 3 8 11) (Reg.operands [.gpr 11] [])) #v[11]
    (.terminate (.br ⟨.l125bff, RegMap.args [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 57), (8, 59), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩)))))))))

def bytes_l125bf1 : List UInt8 :=
  [0x41, 0xBA, 0x01, 0x00, 0x00, 0x00, 0x89, 0xE8, 0x44, 0x89, 0xCF, 0x45, 0x89, 0xD8]

theorem code_l125bf1 : ∀ x ∈ codeRange 0x125bf1 bytes_l125bf1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x25bf1 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l125bff_1 : Block Op Label signature Reg.count 82 :=
  .letOp (n := 82) (.out 0x125c81 (movR32M32Effect 0x125c81 9 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 83) (.exec 0x125c81 (LoadPre 0x125c81 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x125c81 + BitVec.ofNat 64 8)) 4) (movR32M32Effect 0x125c81 9 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 84) (.exec 0x125c89 (StorePre 0x125c89 4 (fun s => AddrMode.addr (.base 3 (.d8 0x34)) s (0x125c89 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x125c89 9 (.base 3 (.d8 0x34))) (Reg.operands [.gpr 9, .gpr 3] [])) #v[82, 3]
    (.letOp (n := 85) (.exec 0x125c8d (StorePre 0x125c8d 3 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x125c8d + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x125c8d 0 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (.letOp (n := 86) (.exec 0x125c90 (StorePre 0x125c90 3 (fun s => AddrMode.addr (.base 3 (.d8 0xc)) s (0x125c90 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x125c90 7 (.base 3 (.d8 0xc))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[7, 3]
    (.letOp (n := 87) (.exec 0x125c93 (StorePre 0x125c93 3 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x125c93 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x125c93 3 1 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[1, 3]
    (.letOp (n := 88) (.exec 0x125c96 (StorePre 0x125c96 3 (fun s => AddrMode.addr (.base 3 (.d8 0x14)) s (0x125c96 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x125c96 2 (.base 3 (.d8 0x14))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[2, 3]
    (.letOp (n := 89) (.exec 0x125c99 (StorePre 0x125c99 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x125c99 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x125c99 8 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 8, .gpr 3] [])) #v[8, 3]
    (.letOp (n := 90) (.exec 0x125c9d (StorePre 0x125c9d 4 (fun s => AddrMode.addr (.base 3 (.d8 0x38)) s (0x125c9d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125c9d 6 (.base 3 (.d8 0x38))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[6, 3]
    (.letOp (n := 91) (.exec 0x125ca1 (StorePre 0x125ca1 3 (fun s => AddrMode.addr (.base 3 .none) s (0x125ca1 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x125ca1 10 (.base 3 .none)) (Reg.operands [.gpr 10, .gpr 3] [])) #v[10, 3]
    (.letOp (n := 92) (.out 0x125ca4 (movR64R64Effect 0x125ca4 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 93) (.exec 0x125ca4 (fun s => s.RIP = 0x125ca4) (movR64R64Effect 0x125ca4 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 94) (.out 0x125ca7 (addR64Imm32Effect 0x125ca7 4 0x138) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 95) (.exec 0x125ca7 (fun s => s.RIP = 0x125ca7) (addR64Imm32Effect 0x125ca7 4 0x138) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 96) (.out 0x125cae (popR64Effect 0x125cae 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[94]
    (.letOp (n := 97) (.out 0x125cae (popR64Effect 0x125cae 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[94]
    (.letOp (n := 98) (.exec 0x125cae (PopPre 0x125cae) (popR64Effect 0x125cae 1 3) (Reg.operands [.gpr 4] [])) #v[94]
    (.letOp (n := 99) (.out 0x125caf (popR64Effect 0x125caf 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[97]
    (.letOp (n := 100) (.out 0x125caf (popR64Effect 0x125caf 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[97]
    (.letOp (n := 101) (.exec 0x125caf (PopPre 0x125caf) (popR64Effect 0x125caf 2 14) (Reg.operands [.gpr 4] [])) #v[97]
    (.letOp (n := 102) (.out 0x125cb1 (popR64Effect 0x125cb1 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[100]
    (.letOp (n := 103) (.out 0x125cb1 (popR64Effect 0x125cb1 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[100]
    (.letOp (n := 104) (.exec 0x125cb1 (PopPre 0x125cb1) (popR64Effect 0x125cb1 2 15) (Reg.operands [.gpr 4] [])) #v[100]
    (.letOp (n := 105) (.out 0x125cb3 (popR64Effect 0x125cb3 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[103]
    (.letOp (n := 106) (.out 0x125cb3 (popR64Effect 0x125cb3 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[103]
    (.letOp (n := 107) (.exec 0x125cb3 (PopPre 0x125cb3) (popR64Effect 0x125cb3 1 5) (Reg.operands [.gpr 4] [])) #v[103]
    (.letOp (n := 108) (.out 0x125cb4 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[106]
    (.letOp (n := 109) (.out 0x125cb4 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[106]
    (.letOp (n := 110) (.exec 0x125cb4 (RetPre 0x125cb4) (retEffect) (Reg.operands [.gpr 4] [])) #v[106]
    (.terminate (.ret (RegMap.args [(0, 92), (1, 1), (2, 2), (3, 96), (4, 109), (5, 105), (6, 6), (7, 7), (8, 8), (9, 82), (10, 10), (11, 75), (12, 12), (13, 13), (14, 99), (15, 102), (22, 22), (39, 39), (50, 50), (51, 51)] 111) (some ⟨108, by decide⟩)))))))))))))))))))))))))))))))

def bytes_l125bff_1 : List UInt8 :=
  [0x44, 0x8B, 0x8C, 0x24, 0x98, 0x00, 0x00, 0x00, 0x44, 0x89, 0x4B, 0x34, 0x89, 0x43, 0x08, 0x89,
    0x7B, 0x0C, 0x88, 0x4B, 0x10, 0x89, 0x53, 0x14, 0x44, 0x89, 0x43, 0x18, 0x48, 0x89, 0x73, 0x38,
    0x4C, 0x89, 0x13, 0x48, 0x89, 0xD8, 0x48, 0x81, 0xC4, 0x38, 0x01, 0x00, 0x00, 0x5B, 0x41, 0x5E,
    0x41, 0x5F, 0x5D, 0xC3]

theorem code_l125bff_1 : ∀ x ∈ codeRange 0x125c81 bytes_l125bff_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x25c81 52 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l125bff : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x125bff (movzxR32M16Effect 0x125bff 9 9 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 54) (.exec 0x125bff (LoadPre 0x125bff (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x125bff + BitVec.ofNat 64 9)) 2) (movzxR32M16Effect 0x125bff 9 9 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x125c08 (StorePre 0x125c08 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x125c08 + BitVec.ofNat 64 9)) 2) (movM16R16Effect 0x125c08 9 9 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x125c11 (movzxR32M8Effect 0x125c11 9 11 (.sib 4 none 0 (.d32 0xba))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 57) (.exec 0x125c11 (LoadPre 0x125c11 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xba)) s (0x125c11 + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x125c11 9 11 (.sib 4 none 0 (.d32 0xba))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x125c1a (StorePre 0x125c1a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xca)) s (0x125c1a + BitVec.ofNat 64 8)) 1) (movM8R8Effect 0x125c1a 8 11 (.sib 4 none 0 (.d32 0xca))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x125c22 (movR64M64Effect 0x125c22 14 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 60) (.exec 0x125c22 (LoadPre 0x125c22 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x125c22 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125c22 14 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x125c27 (movR64M64Effect 0x125c27 15 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 62) (.exec 0x125c27 (LoadPre 0x125c27 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x125c27 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125c27 15 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x125c2c (StorePre 0x125c2c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x125c2c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x125c2c 14 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 64) (.exec 0x125c34 (StorePre 0x125c34 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x125c34 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x125c34 15 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 65) (.out 0x125c3c (movR64M64Effect 0x125c3c 14 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 66) (.exec 0x125c3c (LoadPre 0x125c3c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x125c3c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125c3c 14 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x125c41 (StorePre 0x125c41 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x125c41 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x125c41 14 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x125c49 (movR32M32LowEffect 0x125c49 5 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 69) (.exec 0x125c49 (LoadPre 0x125c49 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x125c49 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x125c49 5 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.exec 0x125c4d (StorePre 0x125c4d 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x125c4d + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x125c4d 5 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[68, 4]
    (.letOp (n := 71) (.exec 0x125c54 (StorePre 0x125c54 4 (fun s => AddrMode.addr (.base 3 (.d8 0x13)) s (0x125c54 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x125c54 4 11 (.base 3 (.d8 0x13))) (Reg.operands [.gpr 11, .gpr 3] [])) #v[56, 3]
    (.letOp (n := 72) (.exec 0x125c58 (StorePre 0x125c58 5 (fun s => AddrMode.addr (.base 3 (.d8 0x11)) s (0x125c58 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x125c58 5 9 (.base 3 (.d8 0x11))) (Reg.operands [.gpr 9, .gpr 3] [])) #v[53, 3]
    (.letOp (n := 73) (.out 0x125c5d (movR64M64Effect 0x125c5d 9 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 74) (.exec 0x125c5d (LoadPre 0x125c5d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x125c5d + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125c5d 9 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.out 0x125c65 (movR64M64Effect 0x125c65 11 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 76) (.exec 0x125c65 (LoadPre 0x125c65 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x125c65 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125c65 11 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 77) (.exec 0x125c6d (StorePre 0x125c6d 4 (fun s => AddrMode.addr (.base 3 (.d8 0x1c)) s (0x125c6d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125c6d 9 (.base 3 (.d8 0x1c))) (Reg.operands [.gpr 9, .gpr 3] [])) #v[73, 3]
    (.letOp (n := 78) (.exec 0x125c71 (StorePre 0x125c71 4 (fun s => AddrMode.addr (.base 3 (.d8 0x24)) s (0x125c71 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125c71 11 (.base 3 (.d8 0x24))) (Reg.operands [.gpr 11, .gpr 3] [])) #v[75, 3]
    (.letOp (n := 79) (.out 0x125c75 (movR64M64Effect 0x125c75 9 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 80) (.exec 0x125c75 (LoadPre 0x125c75 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x125c75 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125c75 9 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 81) (.exec 0x125c7d (StorePre 0x125c7d 4 (fun s => AddrMode.addr (.base 3 (.d8 0x2c)) s (0x125c7d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125c7d 9 (.base 3 (.d8 0x2c))) (Reg.operands [.gpr 9, .gpr 3] [])) #v[79, 3]
    (b_l125bff_1)))))))))))))))))))))))))))))

def bytes_l125bff : List UInt8 :=
  [0x44, 0x0F, 0xB7, 0x8C, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x66, 0x44, 0x89, 0x8C, 0x24, 0xC8, 0x00,
    0x00, 0x00, 0x44, 0x0F, 0xB6, 0x9C, 0x24, 0xBA, 0x00, 0x00, 0x00, 0x44, 0x88, 0x9C, 0x24, 0xCA,
    0x00, 0x00, 0x00, 0x4C, 0x8B, 0x74, 0x24, 0x08, 0x4C, 0x8B, 0x7C, 0x24, 0x10, 0x4C, 0x89, 0xB4,
    0x24, 0x80, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xBC, 0x24, 0x88, 0x00, 0x00, 0x00, 0x4C, 0x8B, 0x74,
    0x24, 0x18, 0x4C, 0x89, 0xB4, 0x24, 0x90, 0x00, 0x00, 0x00, 0x8B, 0x6C, 0x24, 0x20, 0x89, 0xAC,
    0x24, 0x98, 0x00, 0x00, 0x00, 0x44, 0x88, 0x5B, 0x13, 0x66, 0x44, 0x89, 0x4B, 0x11, 0x4C, 0x8B,
    0x8C, 0x24, 0x80, 0x00, 0x00, 0x00, 0x4C, 0x8B, 0x9C, 0x24, 0x88, 0x00, 0x00, 0x00, 0x4C, 0x89,
    0x4B, 0x1C, 0x4C, 0x89, 0x5B, 0x24, 0x4C, 0x8B, 0x8C, 0x24, 0x90, 0x00, 0x00, 0x00, 0x4C, 0x89,
    0x4B, 0x2C] ++ bytes_l125bff_1

theorem code_l125bff : ∀ x ∈ codeRange 0x125bff bytes_l125bff, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x25bff 130 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l125bff_1

@[cfg_block] def b_l125cb5 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x125cb5 (movR32M32Effect 0x125cb5 11 (.sib 4 none 0 (.d32 0xe0))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 54) (.exec 0x125cb5 (LoadPre 0x125cb5 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x125cb5 + BitVec.ofNat 64 8)) 4) (movR32M32Effect 0x125cb5 11 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x125cbd (subR32R32Effect 0x125cbd 3 11 9) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 9] []) (.reg (.gpr 11))) #v[53, 9]
    (.letOp (n := 56) (.out 0x125cbd (subR32R32Effect 0x125cbd 3 11 9) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 9] []) (.flag .CF)) #v[53, 9]
    (.letOp (n := 57) (.out 0x125cbd (subR32R32Effect 0x125cbd 3 11 9) (EffectPart.reads (.flag .ZF) [.gpr 11, .gpr 9] []) (.flag .ZF)) #v[53, 9]
    (.letOp (n := 58) (.exec 0x125cbd (fun s => s.RIP = 0x125cbd) (subR32R32Effect 0x125cbd 3 11 9) (Reg.operands [.gpr 11, .gpr 9] [])) #v[53, 9]
    (.letOp (n := 59) (.pure (condOp 6)) #v[56, 57]
    (.terminate (.condBr (Fin.last 59) ⟨.l125ccc, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 55), (12, 12), (13, 13), (16, 56), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l125cc2, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 55), (12, 12), (13, 13), (16, 56), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l125cb5 : List UInt8 :=
  [0x44, 0x8B, 0x9C, 0x24, 0xE0, 0x00, 0x00, 0x00, 0x45, 0x29, 0xCB, 0x76, 0x0A]

theorem code_l125cb5 : ∀ x ∈ codeRange 0x125cb5 bytes_l125cb5, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x25cb5 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l125cc2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x125cc2 (movR8Imm8Effect 0x125cc2 2 1 0x13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1]
    (.letOp (n := 54) (.exec 0x125cc2 (fun s => s.RIP = 0x125cc2) (movR8Imm8Effect 0x125cc2 2 1 0x13) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 55) (.out 0x125cc4 (movR32R32Effect 0x125cc4 3 2 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9] []) (.reg (.gpr 2))) #v[9]
    (.letOp (n := 56) (.exec 0x125cc4 (fun s => s.RIP = 0x125cc4) (movR32R32Effect 0x125cc4 3 2 9) (Reg.operands [.gpr 9] [])) #v[9]
    (.terminate (.br ⟨.l125bf1, RegMap.args [(1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l125cc2 : List UInt8 :=
  [0xB1, 0x13, 0x44, 0x89, 0xCA, 0xE9, 0x25, 0xFF, 0xFF, 0xFF]

theorem code_l125cc2 : ∀ x ∈ codeRange 0x125cc2 bytes_l125cc2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x25cc2 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l125ccc : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x125ccc (movzxR32M8Effect 0x125ccc 6 9 (.sib 4 none 0 (.d8 0x6))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 54) (.exec 0x125ccc (LoadPre 0x125ccc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6)) s (0x125ccc + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x125ccc 6 9 (.sib 4 none 0 (.d8 0x6))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x125cd2 (StorePre 0x125cd2 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xba)) s (0x125cd2 + BitVec.ofNat 64 8)) 1) (movM8R8Effect 0x125cd2 8 9 (.sib 4 none 0 (.d32 0xba))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x125cda (movzxR32M16Effect 0x125cda 6 9 (.sib 4 none 0 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 57) (.exec 0x125cda (LoadPre 0x125cda (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x125cda + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x125cda 6 9 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x125ce0 (StorePre 0x125ce0 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x125ce0 + BitVec.ofNat 64 9)) 2) (movM16R16Effect 0x125ce0 9 9 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x125ce9 (movR64M64Effect 0x125ce9 9 (.sib 4 none 0 (.d32 0x100))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 60) (.exec 0x125ce9 (LoadPre 0x125ce9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x125ce9 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125ce9 9 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x125cf1 (movR64M64Effect 0x125cf1 10 (.sib 4 none 0 (.d32 0x108))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 62) (.exec 0x125cf1 (LoadPre 0x125cf1 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x125cf1 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125cf1 10 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x125cf9 (StorePre 0x125cf9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x125cf9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125cf9 9 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 64) (.exec 0x125cfe (StorePre 0x125cfe 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x125cfe + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125cfe 10 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 65) (.out 0x125d03 (movR64M64Effect 0x125d03 9 (.sib 4 none 0 (.d32 0x110))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 66) (.exec 0x125d03 (LoadPre 0x125d03 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x125d03 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125d03 9 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x125d0b (StorePre 0x125d0b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x125d0b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125d0b 9 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x125d10 (movR32M32Effect 0x125d10 9 (.sib 4 none 0 (.d32 0x118))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 69) (.exec 0x125d10 (LoadPre 0x125d10 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x125d10 + BitVec.ofNat 64 8)) 4) (movR32M32Effect 0x125d10 9 (.sib 4 none 0 (.d32 0x118))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.exec 0x125d18 (StorePre 0x125d18 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x125d18 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x125d18 9 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[68, 4]
    (.letOp (n := 71) (.out 0x125d1d (movR64M64Effect 0x125d1d 9 (.sib 4 none 0 (.d32 0x130))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 72) (.exec 0x125d1d (LoadPre 0x125d1d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x125d1d + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125d1d 9 (.sib 4 none 0 (.d32 0x130))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.exec 0x125d25 (StorePre 0x125d25 4 (fun s => AddrMode.addr (.base 3 (.d8 0x50)) s (0x125d25 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125d25 9 (.base 3 (.d8 0x50))) (Reg.operands [.gpr 9, .gpr 3] [])) #v[71, 3]
    (.letOp (n := 74) (.out 0x125d29 (movR64M64Effect 0x125d29 9 (.sib 4 none 0 (.d32 0x120))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 75) (.exec 0x125d29 (LoadPre 0x125d29 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x125d29 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125d29 9 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 76) (.out 0x125d31 (movR64M64Effect 0x125d31 10 (.sib 4 none 0 (.d32 0x128))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 77) (.exec 0x125d31 (LoadPre 0x125d31 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x125d31 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125d31 10 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 78) (.exec 0x125d39 (StorePre 0x125d39 4 (fun s => AddrMode.addr (.base 3 (.d8 0x48)) s (0x125d39 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125d39 10 (.base 3 (.d8 0x48))) (Reg.operands [.gpr 10, .gpr 3] [])) #v[76, 3]
    (.letOp (n := 79) (.exec 0x125d3d (StorePre 0x125d3d 4 (fun s => AddrMode.addr (.base 3 (.d8 0x40)) s (0x125d3d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125d3d 9 (.base 3 (.d8 0x40))) (Reg.operands [.gpr 9, .gpr 3] [])) #v[74, 3]
    (.letOp (n := 80) (.out 0x125d41 (xorR32R32Effect 0x125d41 3 10 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 10] []) (.reg (.gpr 10))) #v[76, 76]
    (.letOp (n := 81) (.exec 0x125d41 (fun s => s.RIP = 0x125d41) (xorR32R32Effect 0x125d41 3 10 10) (Reg.operands [.gpr 10, .gpr 10] [])) #v[76, 76]
    (.terminate (.br ⟨.l125bff, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 74), (10, 80), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)] 82⟩))))))))))))))))))))))))))))))

def bytes_l125ccc : List UInt8 :=
  [0x44, 0x0F, 0xB6, 0x4C, 0x24, 0x06, 0x44, 0x88, 0x8C, 0x24, 0xBA, 0x00, 0x00, 0x00, 0x44, 0x0F,
    0xB7, 0x4C, 0x24, 0x04, 0x66, 0x44, 0x89, 0x8C, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x4C, 0x8B, 0x8C,
    0x24, 0x00, 0x01, 0x00, 0x00, 0x4C, 0x8B, 0x94, 0x24, 0x08, 0x01, 0x00, 0x00, 0x4C, 0x89, 0x4C,
    0x24, 0x08, 0x4C, 0x89, 0x54, 0x24, 0x10, 0x4C, 0x8B, 0x8C, 0x24, 0x10, 0x01, 0x00, 0x00, 0x4C,
    0x89, 0x4C, 0x24, 0x18, 0x44, 0x8B, 0x8C, 0x24, 0x18, 0x01, 0x00, 0x00, 0x44, 0x89, 0x4C, 0x24,
    0x20, 0x4C, 0x8B, 0x8C, 0x24, 0x30, 0x01, 0x00, 0x00, 0x4C, 0x89, 0x4B, 0x50, 0x4C, 0x8B, 0x8C,
    0x24, 0x20, 0x01, 0x00, 0x00, 0x4C, 0x8B, 0x94, 0x24, 0x28, 0x01, 0x00, 0x00, 0x4C, 0x89, 0x53,
    0x48, 0x4C, 0x89, 0x4B, 0x40, 0x45, 0x31, 0xD2, 0xE9, 0xB6, 0xFE, 0xFF, 0xFF]

theorem code_l125ccc : ∀ x ∈ codeRange 0x125ccc bytes_l125ccc, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x25ccc 125 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l125d50 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x125d50 (pushR64Effect 0x125d50 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x125d50 (PushPre 0x125d50 1) (pushR64Effect 0x125d50 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x125d51 (pushR64Effect 0x125d51 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x125d51 (PushPre 0x125d51 2) (pushR64Effect 0x125d51 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x125d53 (pushR64Effect 0x125d53 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x125d53 (PushPre 0x125d53 2) (pushR64Effect 0x125d53 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x125d55 (pushR64Effect 0x125d55 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x125d55 (PushPre 0x125d55 2) (pushR64Effect 0x125d55 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x125d57 (pushR64Effect 0x125d57 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x125d57 (PushPre 0x125d57 2) (pushR64Effect 0x125d57 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x125d59 (pushR64Effect 0x125d59 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x125d59 (PushPre 0x125d59 1) (pushR64Effect 0x125d59 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x125d5a (subR64Imm32Effect 0x125d5a 4 0xd8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x125d5a (fun s => s.RIP = 0x125d5a) (subR64Imm32Effect 0x125d5a 4 0xd8) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x125d61 (movR32R32Effect 0x125d61 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2]
    (.letOp (n := 68) (.exec 0x125d61 (fun s => s.RIP = 0x125d61) (movR32R32Effect 0x125d61 2 1 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 69) (.out 0x125d63 (movR64R64Effect 0x125d63 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 6] []) (.reg (.gpr 14))) #v[6]
    (.letOp (n := 70) (.exec 0x125d63 (fun s => s.RIP = 0x125d63) (movR64R64Effect 0x125d63 14 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 71) (.out 0x125d66 (movR64R64Effect 0x125d66 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 72) (.exec 0x125d66 (fun s => s.RIP = 0x125d66) (movR64R64Effect 0x125d66 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 73) (.out 0x125d69 (leaR64Effect 0x125d69 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[65]
    (.letOp (n := 74) (.exec 0x125d69 (fun s => s.RIP = 0x125d69) (leaR64Effect 0x125d69 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 75) (.out 0x125d6e (movR32Imm32Effect 0x125d6e 5 2 0x80) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 76) (.exec 0x125d6e (fun s => s.RIP = 0x125d6e) (movR32Imm32Effect 0x125d6e 5 2 0x80) (Reg.operands [] [])) #v[]
    (.letOp (n := 77) (.out 0x125d73 (callEffect (fun _ => 0x124290) 0x125d78) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 78) (.exec 0x125d73 (PushPre 0x125d73 5) (callEffect (fun _ => 0x124290) 0x125d78) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 79) (.const ⟨64, 0x125d78⟩) #v[]
    (.terminate (.call ⟨.l124290, RegMap.args [(1, 67), (2, 75), (3, 71), (4, 77), (5, 5), (6, 6), (7, 73), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 80⟩ { target := .l125d78, kept := #v[], arity := rfl, guard := some (Fin.last 79) }))))))))))))))))))))))))))))

def bytes_l125d50 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0xD8, 0x00, 0x00,
    0x00, 0x89, 0xD1, 0x49, 0x89, 0xF6, 0x48, 0x89, 0xFB, 0x48, 0x8D, 0x7C, 0x24, 0x08, 0xBA, 0x80,
    0x00, 0x00, 0x00, 0xE8, 0x18, 0xE5, 0xFF, 0xFF]

theorem code_l125d50 : ∀ x ∈ codeRange 0x125d50 bytes_l125d50, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x25d50 40 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l125d78 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x125d78 (movR32M32LowEffect 0x125d78 1 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x125d78 (LoadPre 0x125d78 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x125d78 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x125d78 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x125d7c (movzxR32M8Effect 0x125d7c 5 0 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 56) (.exec 0x125d7c (LoadPre 0x125d7c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x125d7c + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x125d7c 5 0 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x125d81 (cmpR32Imm8Effect 0x125d81 3 1 0x2) (EffectPart.reads (.flag .ZF) [.gpr 1] []) (.flag .ZF)) #v[53]
    (.letOp (n := 58) (.exec 0x125d81 (fun s => s.RIP = 0x125d81) (cmpR32Imm8Effect 0x125d81 3 1 0x2) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 59) (.pure (condOp 5)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l125e55, RegMap.args [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l125d8a, RegMap.args [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l125d78 : List UInt8 :=
  [0x8B, 0x4C, 0x24, 0x08, 0x0F, 0xB6, 0x44, 0x24, 0x0C, 0x83, 0xF9, 0x02, 0x0F, 0x85, 0xCB, 0x00,
    0x00, 0x00]

theorem code_l125d78 : ∀ x ∈ codeRange 0x125d78 bytes_l125d78, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x25d78 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l125d8a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x125d8a (testAlImm8Effect 0x125d8a 0x1) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[0]
    (.letOp (n := 54) (.exec 0x125d8a (fun s => s.RIP = 0x125d8a) (testAlImm8Effect 0x125d8a 0x1) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l125e9c, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l125d92, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l125d8a : List UInt8 :=
  [0xA8, 0x01, 0x0F, 0x84, 0x0A, 0x01, 0x00, 0x00]

theorem code_l125d8a : ∀ x ∈ codeRange 0x125d8a bytes_l125d8a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x25d8a 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l125d92 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x125d92 (leaR64Effect 0x125d92 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x125d92 (fun s => s.RIP = 0x125d92) (leaR64Effect 0x125d92 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x125d97 (movR64R64Effect 0x125d97 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 56) (.exec 0x125d97 (fun s => s.RIP = 0x125d97) (movR64R64Effect 0x125d97 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x125d9a (callEffect (fun _ => 0x125450) 0x125d9f) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x125d9a (PushPre 0x125d9a 5) (callEffect (fun _ => 0x125450) 0x125d9f) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x125d9f⟩) #v[]
    (.terminate (.call ⟨.l125450, RegMap.args [(3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ { target := .l125d9f, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l125d92 : List UInt8 :=
  [0x48, 0x8D, 0x7C, 0x24, 0x08, 0x4C, 0x89, 0xF6, 0xE8, 0xB1, 0xF6, 0xFF, 0xFF]

theorem code_l125d92 : ∀ x ∈ codeRange 0x125d92 bytes_l125d92, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x25d92 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l125d9f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x125d9f (movR32M32LowEffect 0x125d9f 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x125d9f (LoadPre 0x125d9f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x125d9f + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x125d9f 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x125da3 (cmpR32Imm8Effect 0x125da3 3 0 0x2) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x125da3 (fun s => s.RIP = 0x125da3) (cmpR32Imm8Effect 0x125da3 3 0 0x2) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l125eab, RegMap.args [(0, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (13, 13), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l125dac, RegMap.args [(0, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (13, 13), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l125d9f : List UInt8 :=
  [0x8B, 0x44, 0x24, 0x08, 0x83, 0xF8, 0x02, 0x0F, 0x85, 0xFF, 0x00, 0x00, 0x00]

theorem code_l125d9f : ∀ x ∈ codeRange 0x125d9f bytes_l125d9f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x25d9f 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l125dac : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x125dac (movR32M32Effect 0x125dac 10 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 54) (.exec 0x125dac (LoadPre 0x125dac (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x125dac + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x125dac 10 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x125db1 (movR32M32Effect 0x125db1 15 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 56) (.exec 0x125db1 (LoadPre 0x125db1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x125db1 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x125db1 15 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x125db6 (movR32R32Effect 0x125db6 3 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 10] []) (.reg (.gpr 11))) #v[53]
    (.letOp (n := 58) (.exec 0x125db6 (fun s => s.RIP = 0x125db6) (movR32R32Effect 0x125db6 3 11 10) (Reg.operands [.gpr 10] [])) #v[53]
    (.letOp (n := 59) (.out 0x125db9 (shrR32Effect 0x125db9 4 11 8) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[57]
    (.letOp (n := 60) (.exec 0x125db9 (fun s => s.RIP = 0x125db9) (shrR32Effect 0x125db9 4 11 8) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[57]
    (.letOp (n := 61) (.out 0x125dbd (movzxR32R8Effect 0x125dbd 4 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 62) (.exec 0x125dbd (fun s => s.RIP = 0x125dbd) (movzxR32R8Effect 0x125dbd 4 0 10) (Reg.operands [.gpr 10] [])) #v[53]
    (.letOp (n := 63) (.out 0x125dc1 (leaR32Effect 0x125dc1 3 1 (.base 0 (.d8 0xea))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[61]
    (.letOp (n := 64) (.exec 0x125dc1 (fun s => s.RIP = 0x125dc1) (leaR32Effect 0x125dc1 3 1 (.base 0 (.d8 0xea))) (Reg.operands [.gpr 0] [])) #v[61]
    (.letOp (n := 65) (.out 0x125dc4 (cmpR32Imm8Effect 0x125dc4 3 1 0x3) (EffectPart.reads (.flag .CF) [.gpr 1] []) (.flag .CF)) #v[63]
    (.letOp (n := 66) (.exec 0x125dc4 (fun s => s.RIP = 0x125dc4) (cmpR32Imm8Effect 0x125dc4 3 1 0x3) (Reg.operands [.gpr 1] [])) #v[63]
    (.letOp (n := 67) (.pure (condOp 3)) #v[65]
    (.terminate (.condBr (Fin.last 67) ⟨.l125f11, RegMap.args [(0, 61), (1, 63), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 59), (13, 13), (14, 14), (15, 55), (16, 65), (22, 22), (39, 39), (50, 50), (51, 51)] 68⟩ ⟨.l125dcd, RegMap.args [(0, 61), (1, 63), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 59), (13, 13), (14, 14), (15, 55), (16, 65), (22, 22), (39, 39), (50, 50), (51, 51)] 68⟩))))))))))))))))

def bytes_l125dac : List UInt8 :=
  [0x44, 0x8B, 0x54, 0x24, 0x0C, 0x44, 0x8B, 0x7C, 0x24, 0x10, 0x45, 0x89, 0xD3, 0x41, 0xC1, 0xEB,
    0x08, 0x41, 0x0F, 0xB6, 0xC2, 0x8D, 0x48, 0xEA, 0x83, 0xF9, 0x03, 0x0F, 0x83, 0x44, 0x01, 0x00,
    0x00]

theorem code_l125dac : ∀ x ∈ codeRange 0x125dac bytes_l125dac, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x25dac 33 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l125dcd : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x125dcd (testR8Imm8Effect 0x125dcd 11 0x1) (EffectPart.reads (.flag .ZF) [.gpr 11] []) (.flag .ZF)) #v[11]
    (.letOp (n := 54) (.exec 0x125dcd (fun s => s.RIP = 0x125dcd) (testR8Imm8Effect 0x125dcd 11 0x1) (Reg.operands [.gpr 11] [])) #v[11]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l125f4e, RegMap.args [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l125dd7, RegMap.args [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l125dcd : List UInt8 :=
  [0x41, 0xF6, 0xC3, 0x01, 0x0F, 0x84, 0x77, 0x01, 0x00, 0x00]

theorem code_l125dcd : ∀ x ∈ codeRange 0x125dcd bytes_l125dcd, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x25dcd 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l125dd7 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x125dd7 (cmpR8Imm8Effect 0x125dd7 4 10 0x17) (EffectPart.reads (.flag .ZF) [.gpr 10] []) (.flag .ZF)) #v[10]
    (.letOp (n := 54) (.exec 0x125dd7 (fun s => s.RIP = 0x125dd7) (cmpR8Imm8Effect 0x125dd7 4 10 0x17) (Reg.operands [.gpr 10] [])) #v[10]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l125f19, RegMap.args [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l125de1, RegMap.args [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l125dd7 : List UInt8 :=
  [0x41, 0x80, 0xFA, 0x17, 0x0F, 0x85, 0x38, 0x01, 0x00, 0x00]

theorem code_l125dd7 : ∀ x ∈ codeRange 0x125dd7 bytes_l125dd7, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x25dd7 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l125de1 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x125de1 (movR64Imm64Effect 0x125de1 13 0xffffffff00000000) (EffectPart.reads (.reg (.gpr 13)) [] []) (.reg (.gpr 13))) #v[]
    (.letOp (n := 54) (.exec 0x125de1 (fun s => s.RIP = 0x125de1) (movR64Imm64Effect 0x125de1 13 0xffffffff00000000) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x125deb (movR32M32Effect 0x125deb 12 (.base 14 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 14] []) (.reg (.gpr 12))) #v[14]
    (.letOp (n := 56) (.exec 0x125deb (LoadPre 0x125deb (fun s => AddrMode.addr (.base 14 (.d8 0x1c)) s (0x125deb + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x125deb 12 (.base 14 (.d8 0x1c))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x125def (movR32M32LowEffect 0x125def 5 (.sib 4 none 0 (.d8 0x14))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 58) (.exec 0x125def (LoadPre 0x125def (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x125def + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x125def 5 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x125df3 (addR32R32Effect 0x125df3 3 5 12) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 12] []) (.reg (.gpr 5))) #v[57, 55]
    (.letOp (n := 60) (.out 0x125df3 (addR32R32Effect 0x125df3 3 5 12) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 12] []) (.flag .CF)) #v[57, 55]
    (.letOp (n := 61) (.exec 0x125df3 (fun s => s.RIP = 0x125df3) (addR32R32Effect 0x125df3 3 5 12) (Reg.operands [.gpr 5, .gpr 12] [])) #v[57, 55]
    (.letOp (n := 62) (.pure (condOp 2)) #v[60]
    (.terminate (.condBr (Fin.last 62) ⟨.l1262d1, RegMap.args [(0, 0), (2, 2), (3, 3), (4, 4), (5, 59), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 53), (14, 14), (15, 15), (16, 60), (22, 22), (39, 39), (50, 50), (51, 51)] 63⟩ ⟨.l125dfc, RegMap.args [(0, 0), (2, 2), (3, 3), (4, 4), (5, 59), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 53), (14, 14), (15, 15), (16, 60), (22, 22), (39, 39), (50, 50), (51, 51)] 63⟩)))))))))))

def bytes_l125de1 : List UInt8 :=
  [0x49, 0xBD, 0x00, 0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF, 0x45, 0x8B, 0x66, 0x1C, 0x8B, 0x6C,
    0x24, 0x14, 0x44, 0x01, 0xE5, 0x0F, 0x82, 0xD5, 0x04, 0x00, 0x00]

theorem code_l125de1 : ∀ x ∈ codeRange 0x125de1 bytes_l125de1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x25de1 27 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l125dfc : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x125dfc (movR64M64Effect 0x125dfc 6 (.base 14 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 54) (.exec 0x125dfc (LoadPre 0x125dfc (fun s => AddrMode.addr (.base 14 .none) s (0x125dfc + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x125dfc 6 (.base 14 .none)) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 55) (.out 0x125dff (movR64M64Effect 0x125dff 2 (.base 14 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14] []) (.reg (.gpr 2))) #v[14]
    (.letOp (n := 56) (.exec 0x125dff (LoadPre 0x125dff (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x125dff + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x125dff 2 (.base 14 (.d8 0x8))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x125e03 (leaR64Effect 0x125e03 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 58) (.exec 0x125e03 (fun s => s.RIP = 0x125e03) (leaR64Effect 0x125e03 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.exec 0x125e08 (StorePre 0x125e08 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x125e08 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x125e08 6 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 60) (.exec 0x125e10 (StorePre 0x125e10 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x125e10 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x125e10 2 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 61) (.out 0x125e18 (movR32R32Effect 0x125e18 2 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[5]
    (.letOp (n := 62) (.exec 0x125e18 (fun s => s.RIP = 0x125e18) (movR32R32Effect 0x125e18 2 1 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 63) (.out 0x125e1a (callEffect (fun _ => 0x127c50) 0x125e1f) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 64) (.exec 0x125e1a (PushPre 0x125e1a 5) (callEffect (fun _ => 0x127c50) 0x125e1f) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.const ⟨64, 0x125e1f⟩) #v[]
    (.terminate (.call ⟨.l127c50, RegMap.args [(1, 61), (2, 55), (3, 3), (4, 63), (5, 5), (6, 53), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩ { target := .l125e1f, kept := #v[], arity := rfl, guard := some (Fin.last 65) }))))))))))))))

def bytes_l125dfc : List UInt8 :=
  [0x49, 0x8B, 0x36, 0x49, 0x8B, 0x56, 0x08, 0x48, 0x8D, 0x7C, 0x24, 0x08, 0x48, 0x89, 0xB4, 0x24,
    0xC0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x94, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x89, 0xE9, 0xE8, 0x31,
    0x1E, 0x00, 0x00]

theorem code_l125dfc : ∀ x ∈ codeRange 0x125dfc bytes_l125dfc, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x25dfc 35 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l125e1f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x125e1f (movR32M32LowEffect 0x125e1f 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x125e1f (LoadPre 0x125e1f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x125e1f + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x125e1f 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x125e23 (cmpR32Imm8Effect 0x125e23 3 0 0x2) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x125e23 (fun s => s.RIP = 0x125e23) (cmpR32Imm8Effect 0x125e23 3 0 0x2) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l126009, RegMap.args [(0, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l125e2c, RegMap.args [(0, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l125e1f : List UInt8 :=
  [0x8B, 0x44, 0x24, 0x08, 0x83, 0xF8, 0x02, 0x0F, 0x85, 0xDD, 0x01, 0x00, 0x00]

theorem code_l125e1f : ∀ x ∈ codeRange 0x125e1f bytes_l125e1f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x25e1f 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l125e2c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x125e2c (movR64M64Effect 0x125e2c 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x125e2c (LoadPre 0x125e2c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x125e2c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125e2c 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x125e31 (movR64M64Effect 0x125e31 1 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x125e31 (LoadPre 0x125e31 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x125e31 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125e31 1 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x125e36 (StorePre 0x125e36 3 (fun s => AddrMode.addr (.base 14 .none) s (0x125e36 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x125e36 0 (.base 14 .none)) (Reg.operands [.gpr 0, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 58) (.exec 0x125e39 (StorePre 0x125e39 4 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x125e39 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125e39 1 (.base 14 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x125e3d (movR64M64Effect 0x125e3d 0 (.base 14 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[14]
    (.letOp (n := 60) (.exec 0x125e3d (LoadPre 0x125e3d (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x125e3d + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x125e3d 0 (.base 14 (.d8 0x10))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 61) (.out 0x125e41 (cmpR64Imm8Effect 0x125e41 0 0x3f) (EffectPart.reads (.flag .CF) [.gpr 0] []) (.flag .CF)) #v[59]
    (.letOp (n := 62) (.out 0x125e41 (cmpR64Imm8Effect 0x125e41 0 0x3f) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[59]
    (.letOp (n := 63) (.exec 0x125e41 (fun s => s.RIP = 0x125e41) (cmpR64Imm8Effect 0x125e41 0 0x3f) (Reg.operands [.gpr 0] [])) #v[59]
    (.letOp (n := 64) (.pure (condOp 6)) #v[61, 62]
    (.terminate (.condBr (Fin.last 64) ⟨.l12604b, RegMap.args [(0, 59), (1, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 61), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)] 65⟩ ⟨.l125e4b, RegMap.args [(0, 59), (1, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 61), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)] 65⟩)))))))))))))

def bytes_l125e2c : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x10, 0x48, 0x8B, 0x4C, 0x24, 0x18, 0x49, 0x89, 0x06, 0x49, 0x89, 0x4E,
    0x08, 0x49, 0x8B, 0x46, 0x10, 0x48, 0x83, 0xF8, 0x3F, 0x0F, 0x86, 0x00, 0x02, 0x00, 0x00]

theorem code_l125e2c : ∀ x ∈ codeRange 0x125e2c bytes_l125e2c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x25e2c 31 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l125e4b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x125e4b (movR32Imm32Effect 0x125e4b 5 1 0x6) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 54) (.exec 0x125e4b (fun s => s.RIP = 0x125e4b) (movR32Imm32Effect 0x125e4b 5 1 0x6) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l126068, RegMap.args [(1, 53), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l125e4b : List UInt8 :=
  [0xB9, 0x06, 0x00, 0x00, 0x00, 0xE9, 0x13, 0x02, 0x00, 0x00]

theorem code_l125e4b : ∀ x ∈ codeRange 0x125e4b bytes_l125e4b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x25e4b 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l125e55 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x125e55 (movR32M32LowEffect 0x125e55 2 (.sib 4 none 0 (.d8 0x3c))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 54) (.exec 0x125e55 (LoadPre 0x125e55 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x125e55 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x125e55 2 (.sib 4 none 0 (.d8 0x3c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x125e59 (StorePre 0x125e59 3 (fun s => AddrMode.addr (.base 3 (.d8 0x34)) s (0x125e59 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x125e59 2 (.base 3 (.d8 0x34))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[53, 3]
    (.letOp (n := 56) (.out 0x125e5c (movR64M64Effect 0x125e5c 2 (.sib 4 none 0 (.d8 0x35))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 57) (.exec 0x125e5c (LoadPre 0x125e5c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x35)) s (0x125e5c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125e5c 2 (.sib 4 none 0 (.d8 0x35))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x125e61 (StorePre 0x125e61 4 (fun s => AddrMode.addr (.base 3 (.d8 0x2d)) s (0x125e61 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125e61 2 (.base 3 (.d8 0x2d))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[56, 3]
    (.letOp (n := 59) (.out 0x125e65 (movR64M64Effect 0x125e65 2 (.sib 4 none 0 (.d8 0x2d))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 60) (.exec 0x125e65 (LoadPre 0x125e65 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2d)) s (0x125e65 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125e65 2 (.sib 4 none 0 (.d8 0x2d))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x125e6a (StorePre 0x125e6a 4 (fun s => AddrMode.addr (.base 3 (.d8 0x25)) s (0x125e6a + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125e6a 2 (.base 3 (.d8 0x25))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[59, 3]
    (.letOp (n := 62) (.out 0x125e6e (movR64M64Effect 0x125e6e 2 (.sib 4 none 0 (.d8 0x25))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 63) (.exec 0x125e6e (LoadPre 0x125e6e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x25)) s (0x125e6e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125e6e 2 (.sib 4 none 0 (.d8 0x25))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x125e73 (StorePre 0x125e73 4 (fun s => AddrMode.addr (.base 3 (.d8 0x1d)) s (0x125e73 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125e73 2 (.base 3 (.d8 0x1d))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[62, 3]
    (.letOp (n := 65) (.out 0x125e77 (movR64M64Effect 0x125e77 2 (.sib 4 none 0 (.d8 0x1d))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 66) (.exec 0x125e77 (LoadPre 0x125e77 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1d)) s (0x125e77 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125e77 2 (.sib 4 none 0 (.d8 0x1d))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x125e7c (StorePre 0x125e7c 4 (fun s => AddrMode.addr (.base 3 (.d8 0x15)) s (0x125e7c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125e7c 2 (.base 3 (.d8 0x15))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[65, 3]
    (.letOp (n := 68) (.out 0x125e80 (movR64M64Effect 0x125e80 2 (.sib 4 none 0 (.d8 0xd))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 69) (.exec 0x125e80 (LoadPre 0x125e80 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xd)) s (0x125e80 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125e80 2 (.sib 4 none 0 (.d8 0xd))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.out 0x125e85 (movR64M64Effect 0x125e85 6 (.sib 4 none 0 (.d8 0x15))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 71) (.exec 0x125e85 (LoadPre 0x125e85 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x15)) s (0x125e85 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125e85 6 (.sib 4 none 0 (.d8 0x15))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.exec 0x125e8a (StorePre 0x125e8a 4 (fun s => AddrMode.addr (.base 3 (.d8 0xd)) s (0x125e8a + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125e8a 6 (.base 3 (.d8 0xd))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[70, 3]
    (.letOp (n := 73) (.exec 0x125e8e (StorePre 0x125e8e 4 (fun s => AddrMode.addr (.base 3 (.d8 0x5)) s (0x125e8e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125e8e 2 (.base 3 (.d8 0x5))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[68, 3]
    (.letOp (n := 74) (.exec 0x125e92 (StorePre 0x125e92 2 (fun s => AddrMode.addr (.base 3 .none) s (0x125e92 + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x125e92 1 (.base 3 .none)) (Reg.operands [.gpr 1, .gpr 3] [])) #v[1, 3]
    (.letOp (n := 75) (.exec 0x125e94 (StorePre 0x125e94 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x125e94 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x125e94 3 0 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (.terminate (.br ⟨.l125ff4, RegMap.args [(0, 0), (1, 1), (2, 68), (3, 3), (4, 4), (6, 70), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 76⟩))))))))))))))))))))))))

def bytes_l125e55 : List UInt8 :=
  [0x8B, 0x54, 0x24, 0x3C, 0x89, 0x53, 0x34, 0x48, 0x8B, 0x54, 0x24, 0x35, 0x48, 0x89, 0x53, 0x2D,
    0x48, 0x8B, 0x54, 0x24, 0x2D, 0x48, 0x89, 0x53, 0x25, 0x48, 0x8B, 0x54, 0x24, 0x25, 0x48, 0x89,
    0x53, 0x1D, 0x48, 0x8B, 0x54, 0x24, 0x1D, 0x48, 0x89, 0x53, 0x15, 0x48, 0x8B, 0x54, 0x24, 0x0D,
    0x48, 0x8B, 0x74, 0x24, 0x15, 0x48, 0x89, 0x73, 0x0D, 0x48, 0x89, 0x53, 0x05, 0x89, 0x0B, 0x88,
    0x43, 0x04, 0xE9, 0x58, 0x01, 0x00, 0x00]

theorem code_l125e55 : ∀ x ∈ codeRange 0x125e55 bytes_l125e55, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x25e55 71 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l125e9c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x125e9c (StorePre 0x125e9c 4 (fun s => AddrMode.addr (.base 3 (.d8 0x24)) s (0x125e9c + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x125e9c (.base 3 (.d8 0x24)) 0x2) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 54) (.exec 0x125ea0 (StorePre 0x125ea0 6 (fun s => AddrMode.addr (.base 3 .none) s (0x125ea0 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x125ea0 6 (.base 3 .none) 0x2) (Reg.operands [.gpr 3] [])) #v[3]
    (.terminate (.br ⟨.l125ff4, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l125e9c : List UInt8 :=
  [0xC6, 0x43, 0x24, 0x02, 0xC7, 0x03, 0x02, 0x00, 0x00, 0x00, 0xE9, 0x49, 0x01, 0x00, 0x00]

theorem code_l125e9c : ∀ x ∈ codeRange 0x125e9c bytes_l125e9c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x25e9c 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l125eab : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x125eab (movzxR32M8Effect 0x125eab 5 2 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 54) (.exec 0x125eab (LoadPre 0x125eab (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x125eab + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x125eab 5 2 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x125eb0 (movzxR32M8Effect 0x125eb0 6 14 (.sib 4 none 0 (.d8 0xd))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 56) (.exec 0x125eb0 (LoadPre 0x125eb0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xd)) s (0x125eb0 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x125eb0 6 14 (.sib 4 none 0 (.d8 0xd))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x125eb6 (movzxR32M16Effect 0x125eb6 6 12 (.sib 4 none 0 (.d8 0xe))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 58) (.exec 0x125eb6 (LoadPre 0x125eb6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x125eb6 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x125eb6 6 12 (.sib 4 none 0 (.d8 0xe))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x125ebc (movR64M64Effect 0x125ebc 1 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 60) (.exec 0x125ebc (LoadPre 0x125ebc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x125ebc + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125ebc 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x125ec1 (movR32M32Effect 0x125ec1 15 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 62) (.exec 0x125ec1 (LoadPre 0x125ec1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x125ec1 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x125ec1 15 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x125ec6 (movzxR32M8Effect 0x125ec6 6 10 (.sib 4 none 0 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 64) (.exec 0x125ec6 (LoadPre 0x125ec6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x125ec6 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x125ec6 6 10 (.sib 4 none 0 (.d8 0x1c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x125ecc (movzxR32M8Effect 0x125ecc 6 11 (.sib 4 none 0 (.d8 0x1d))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 66) (.exec 0x125ecc (LoadPre 0x125ecc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1d)) s (0x125ecc + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x125ecc 6 11 (.sib 4 none 0 (.d8 0x1d))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x125ed2 (movzxR32M16Effect 0x125ed2 6 8 (.sib 4 none 0 (.d8 0x1e))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 68) (.exec 0x125ed2 (LoadPre 0x125ed2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1e)) s (0x125ed2 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x125ed2 6 8 (.sib 4 none 0 (.d8 0x1e))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.out 0x125ed8 (movR64M64Effect 0x125ed8 9 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 70) (.exec 0x125ed8 (LoadPre 0x125ed8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x125ed8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125ed8 9 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.out 0x125edd (movR64Imm64Effect 0x125edd 13 0xffffffff00000000) (EffectPart.reads (.reg (.gpr 13)) [] []) (.reg (.gpr 13))) #v[]
    (.letOp (n := 72) (.exec 0x125edd (fun s => s.RIP = 0x125edd) (movR64Imm64Effect 0x125edd 13 0xffffffff00000000) (Reg.operands [] [])) #v[]
    (.letOp (n := 73) (.out 0x125ee7 (andR64R64Effect 0x125ee7 13 9) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 9] []) (.reg (.gpr 13))) #v[71, 69]
    (.letOp (n := 74) (.exec 0x125ee7 (fun s => s.RIP = 0x125ee7) (andR64R64Effect 0x125ee7 13 9) (Reg.operands [.gpr 13, .gpr 9] [])) #v[71, 69]
    (.letOp (n := 75) (.out 0x125eea (movR32M32LowEffect 0x125eea 6 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 76) (.exec 0x125eea (LoadPre 0x125eea (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x125eea + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x125eea 6 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 77) (.out 0x125eee (movzxR32M8Effect 0x125eee 5 7 (.sib 4 none 0 (.d8 0x2c))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 78) (.exec 0x125eee (LoadPre 0x125eee (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x125eee + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x125eee 5 7 (.sib 4 none 0 (.d8 0x2c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.out 0x125ef3 (movR64M64Effect 0x125ef3 5 (.sib 4 none 0 (.d8 0x2d))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 80) (.exec 0x125ef3 (LoadPre 0x125ef3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2d)) s (0x125ef3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125ef3 5 (.sib 4 none 0 (.d8 0x2d))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 81) (.exec 0x125ef8 (StorePre 0x125ef8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x125ef8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125ef8 5 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[79, 4]
    (.letOp (n := 82) (.out 0x125efd (movR64M64Effect 0x125efd 5 (.sib 4 none 0 (.d8 0x35))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 83) (.exec 0x125efd (LoadPre 0x125efd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x35)) s (0x125efd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125efd 5 (.sib 4 none 0 (.d8 0x35))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 84) (.exec 0x125f02 (StorePre 0x125f02 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x125f02 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125f02 5 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[82, 4]
    (.letOp (n := 85) (.out 0x125f07 (movR32M32LowEffect 0x125f07 5 (.sib 4 none 0 (.d8 0x3c))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 86) (.exec 0x125f07 (LoadPre 0x125f07 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x125f07 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x125f07 5 (.sib 4 none 0 (.d8 0x3c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 87) (.exec 0x125f0b (StorePre 0x125f0b 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4f)) s (0x125f0b + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x125f0b 5 (.sib 4 none 0 (.d8 0x4f))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[85, 4]
    (.terminate (.br ⟨.l125f78, RegMap.args [(0, 0), (1, 59), (2, 53), (3, 3), (4, 4), (5, 85), (6, 75), (7, 77), (8, 67), (9, 69), (10, 63), (11, 65), (12, 57), (13, 73), (14, 55), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)] 88⟩))))))))))))))))))))))))))))))))))))

def bytes_l125eab : List UInt8 :=
  [0x0F, 0xB6, 0x54, 0x24, 0x0C, 0x44, 0x0F, 0xB6, 0x74, 0x24, 0x0D, 0x44, 0x0F, 0xB7, 0x64, 0x24,
    0x0E, 0x48, 0x8B, 0x4C, 0x24, 0x10, 0x44, 0x8B, 0x7C, 0x24, 0x18, 0x44, 0x0F, 0xB6, 0x54, 0x24,
    0x1C, 0x44, 0x0F, 0xB6, 0x5C, 0x24, 0x1D, 0x44, 0x0F, 0xB7, 0x44, 0x24, 0x1E, 0x4C, 0x8B, 0x4C,
    0x24, 0x20, 0x49, 0xBD, 0x00, 0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF, 0x4D, 0x21, 0xCD, 0x8B,
    0x74, 0x24, 0x28, 0x0F, 0xB6, 0x7C, 0x24, 0x2C, 0x48, 0x8B, 0x6C, 0x24, 0x2D, 0x48, 0x89, 0x6C,
    0x24, 0x40, 0x48, 0x8B, 0x6C, 0x24, 0x35, 0x48, 0x89, 0x6C, 0x24, 0x48, 0x8B, 0x6C, 0x24, 0x3C,
    0x89, 0x6C, 0x24, 0x4F, 0xEB, 0x67]

theorem code_l125eab : ∀ x ∈ codeRange 0x125eab bytes_l125eab, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x25eab 102 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l125f11 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x125f11 (addR32Imm8Effect 0x125f11 3 0 0xf6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 54) (.exec 0x125f11 (fun s => s.RIP = 0x125f11) (addR32Imm8Effect 0x125f11 3 0 0xf6) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x125f14 (cmpR32Imm8Effect 0x125f14 3 0 0x2) (EffectPart.reads (.flag .CF) [.gpr 0] []) (.flag .CF)) #v[53]
    (.letOp (n := 56) (.exec 0x125f14 (fun s => s.RIP = 0x125f14) (cmpR32Imm8Effect 0x125f14 3 0 0x2) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 3)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l125f4e, RegMap.args [(0, 53), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l125f19, RegMap.args [(0, 53), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l125f11 : List UInt8 :=
  [0x83, 0xC0, 0xF6, 0x83, 0xF8, 0x02, 0x73, 0x35]

theorem code_l125f11 : ∀ x ∈ codeRange 0x125f11 bytes_l125f11, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x25f11 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l125f19 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x125f19 (movR32R32Effect 0x125f19 3 8 10) (EffectPart.reads (.reg (.gpr 8)) [.gpr 10] []) (.reg (.gpr 8))) #v[10]
    (.letOp (n := 54) (.exec 0x125f19 (fun s => s.RIP = 0x125f19) (movR32R32Effect 0x125f19 3 8 10) (Reg.operands [.gpr 10] [])) #v[10]
    (.letOp (n := 55) (.out 0x125f1c (shrR32Effect 0x125f1c 4 8 16) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[53]
    (.letOp (n := 56) (.exec 0x125f1c (fun s => s.RIP = 0x125f1c) (shrR32Effect 0x125f1c 4 8 16) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 57) (.exec 0x125f20 (StorePre 0x125f20 5 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x125f20 + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x125f20 (.base 14 (.d8 0x20)) 0x1) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 58) (.out 0x125f25 (movR32M32Effect 0x125f25 2 (.base 14 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14] []) (.reg (.gpr 2))) #v[14]
    (.letOp (n := 59) (.exec 0x125f25 (LoadPre 0x125f25 (fun s => AddrMode.addr (.base 14 (.d8 0x1c)) s (0x125f25 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x125f25 2 (.base 14 (.d8 0x1c))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 60) (.out 0x125f29 (movR32R32Effect 0x125f29 3 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[58]
    (.letOp (n := 61) (.exec 0x125f29 (fun s => s.RIP = 0x125f29) (movR32R32Effect 0x125f29 3 14 2) (Reg.operands [.gpr 2] [])) #v[58]
    (.letOp (n := 62) (.out 0x125f2c (shrR32Effect 0x125f2c 4 14 8) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[60]
    (.letOp (n := 63) (.exec 0x125f2c (fun s => s.RIP = 0x125f2c) (shrR32Effect 0x125f2c 4 14 8) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[60]
    (.letOp (n := 64) (.out 0x125f30 (movR32R32Effect 0x125f30 3 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 2] []) (.reg (.gpr 12))) #v[58]
    (.letOp (n := 65) (.exec 0x125f30 (fun s => s.RIP = 0x125f30) (movR32R32Effect 0x125f30 3 12 2) (Reg.operands [.gpr 2] [])) #v[58]
    (.letOp (n := 66) (.out 0x125f33 (shrR32Effect 0x125f33 4 12 16) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[64]
    (.letOp (n := 67) (.exec 0x125f33 (fun s => s.RIP = 0x125f33) (shrR32Effect 0x125f33 4 12 16) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[64]
    (.letOp (n := 68) (.out 0x125f37 (movR32Imm32Effect 0x125f37 5 0 0x1) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 69) (.exec 0x125f37 (fun s => s.RIP = 0x125f37) (movR32Imm32Effect 0x125f37 5 0 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 70) (.out 0x125f3c (movR64Imm64Effect 0x125f3c 1 0xff00000011) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 71) (.exec 0x125f3c (fun s => s.RIP = 0x125f3c) (movR64Imm64Effect 0x125f3c 1 0xff00000011) (Reg.operands [] [])) #v[]
    (.letOp (n := 72) (.out 0x125f46 (xorR32R32Effect 0x125f46 3 13 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 13] []) (.reg (.gpr 13))) #v[13, 13]
    (.letOp (n := 73) (.exec 0x125f46 (fun s => s.RIP = 0x125f46) (xorR32R32Effect 0x125f46 3 13 13) (Reg.operands [.gpr 13, .gpr 13] [])) #v[13, 13]
    (.letOp (n := 74) (.out 0x125f49 (movR32R32Effect 0x125f49 3 9 15) (EffectPart.reads (.reg (.gpr 9)) [.gpr 15] []) (.reg (.gpr 9))) #v[15]
    (.letOp (n := 75) (.exec 0x125f49 (fun s => s.RIP = 0x125f49) (movR32R32Effect 0x125f49 3 9 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.terminate (.br ⟨.l125f78, RegMap.args [(0, 68), (1, 70), (2, 58), (3, 3), (4, 4), (6, 6), (7, 7), (8, 55), (9, 74), (10, 10), (11, 11), (12, 66), (13, 72), (14, 62), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 76⟩))))))))))))))))))))))))

def bytes_l125f19 : List UInt8 :=
  [0x45, 0x89, 0xD0, 0x41, 0xC1, 0xE8, 0x10, 0x41, 0xC6, 0x46, 0x20, 0x01, 0x41, 0x8B, 0x56, 0x1C,
    0x41, 0x89, 0xD6, 0x41, 0xC1, 0xEE, 0x08, 0x41, 0x89, 0xD4, 0x41, 0xC1, 0xEC, 0x10, 0xB8, 0x01,
    0x00, 0x00, 0x00, 0x48, 0xB9, 0x11, 0x00, 0x00, 0x00, 0xFF, 0x00, 0x00, 0x00, 0x45, 0x31, 0xED,
    0x45, 0x89, 0xF9, 0xEB, 0x2A]

theorem code_l125f19 : ∀ x ∈ codeRange 0x125f19 bytes_l125f19, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x25f19 53 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l125f4e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x125f4e (shlR64Effect 0x125f4e 4 10 32) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[10]
    (.letOp (n := 54) (.exec 0x125f4e (fun s => s.RIP = 0x125f4e) (shlR64Effect 0x125f4e 4 10 32) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[10]
    (.letOp (n := 55) (.exec 0x125f52 (StorePre 0x125f52 5 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x125f52 + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x125f52 (.base 14 (.d8 0x20)) 0x1) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 56) (.out 0x125f57 (movR32M32Effect 0x125f57 2 (.base 14 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14] []) (.reg (.gpr 2))) #v[14]
    (.letOp (n := 57) (.exec 0x125f57 (LoadPre 0x125f57 (fun s => AddrMode.addr (.base 14 (.d8 0x1c)) s (0x125f57 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x125f57 2 (.base 14 (.d8 0x1c))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 58) (.out 0x125f5b (movR32R32Effect 0x125f5b 3 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[56]
    (.letOp (n := 59) (.exec 0x125f5b (fun s => s.RIP = 0x125f5b) (movR32R32Effect 0x125f5b 3 14 2) (Reg.operands [.gpr 2] [])) #v[56]
    (.letOp (n := 60) (.out 0x125f5e (shrR32Effect 0x125f5e 4 14 8) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[58]
    (.letOp (n := 61) (.exec 0x125f5e (fun s => s.RIP = 0x125f5e) (shrR32Effect 0x125f5e 4 14 8) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[58]
    (.letOp (n := 62) (.out 0x125f62 (movR32R32Effect 0x125f62 3 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 2] []) (.reg (.gpr 12))) #v[56]
    (.letOp (n := 63) (.exec 0x125f62 (fun s => s.RIP = 0x125f62) (movR32R32Effect 0x125f62 3 12 2) (Reg.operands [.gpr 2] [])) #v[56]
    (.letOp (n := 64) (.out 0x125f65 (shrR32Effect 0x125f65 4 12 16) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[62]
    (.letOp (n := 65) (.exec 0x125f65 (fun s => s.RIP = 0x125f65) (shrR32Effect 0x125f65 4 12 16) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[62]
    (.letOp (n := 66) (.out 0x125f69 (orR64Imm8Effect 0x125f69 10 0x7) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[53]
    (.letOp (n := 67) (.exec 0x125f69 (fun s => s.RIP = 0x125f69) (orR64Imm8Effect 0x125f69 10 0x7) (Reg.operands [.gpr 10] [])) #v[53]
    (.letOp (n := 68) (.out 0x125f6d (movR32Imm32Effect 0x125f6d 5 0 0x1) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 69) (.exec 0x125f6d (fun s => s.RIP = 0x125f6d) (movR32Imm32Effect 0x125f6d 5 0 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 70) (.out 0x125f72 (xorR32R32Effect 0x125f72 3 13 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 13] []) (.reg (.gpr 13))) #v[13, 13]
    (.letOp (n := 71) (.exec 0x125f72 (fun s => s.RIP = 0x125f72) (xorR32R32Effect 0x125f72 3 13 13) (Reg.operands [.gpr 13, .gpr 13] [])) #v[13, 13]
    (.letOp (n := 72) (.out 0x125f75 (movR64R64Effect 0x125f75 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 10] []) (.reg (.gpr 1))) #v[66]
    (.letOp (n := 73) (.exec 0x125f75 (fun s => s.RIP = 0x125f75) (movR64R64Effect 0x125f75 1 10) (Reg.operands [.gpr 10] [])) #v[66]
    (.terminate (.br ⟨.l125f78, RegMap.args [(0, 68), (1, 72), (2, 56), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 66), (11, 11), (12, 64), (13, 70), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 74⟩))))))))))))))))))))))

def bytes_l125f4e : List UInt8 :=
  [0x49, 0xC1, 0xE2, 0x20, 0x41, 0xC6, 0x46, 0x20, 0x01, 0x41, 0x8B, 0x56, 0x1C, 0x41, 0x89, 0xD6,
    0x41, 0xC1, 0xEE, 0x08, 0x41, 0x89, 0xD4, 0x41, 0xC1, 0xEC, 0x10, 0x49, 0x83, 0xCA, 0x07, 0xB8,
    0x01, 0x00, 0x00, 0x00, 0x45, 0x31, 0xED, 0x4C, 0x89, 0xD1]

theorem code_l125f4e : ∀ x ∈ codeRange 0x125f4e bytes_l125f4e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x25f4e 42 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l125f78_1 : Block Op Label signature Reg.count 92 :=
  .letOp (n := 92) (.out 0x125fbf (movzxR32M16Effect 0x125fbf 6 9 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 93) (.exec 0x125fbf (LoadPre 0x125fbf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x125fbf + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x125fbf 6 9 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 94) (.exec 0x125fc5 (StorePre 0x125fc5 5 (fun s => AddrMode.addr (.base 3 (.d8 0x25)) s (0x125fc5 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x125fc5 5 9 (.base 3 (.d8 0x25))) (Reg.operands [.gpr 9, .gpr 3] [])) #v[92, 3]
    (.letOp (n := 95) (.out 0x125fca (movR64M64Effect 0x125fca 9 (.sib 4 none 0 (.d8 0x43))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 96) (.exec 0x125fca (LoadPre 0x125fca (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x43)) s (0x125fca + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125fca 9 (.sib 4 none 0 (.d8 0x43))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 97) (.out 0x125fcf (movR64M64Effect 0x125fcf 11 (.sib 4 none 0 (.d8 0x4b))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 98) (.exec 0x125fcf (LoadPre 0x125fcf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4b)) s (0x125fcf + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125fcf 11 (.sib 4 none 0 (.d8 0x4b))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 99) (.exec 0x125fd4 (StorePre 0x125fd4 4 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x125fd4 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125fd4 9 (.base 3 (.d8 0x28))) (Reg.operands [.gpr 9, .gpr 3] [])) #v[95, 3]
    (.letOp (n := 100) (.exec 0x125fd8 (StorePre 0x125fd8 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x125fd8 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125fd8 11 (.base 3 (.d8 0x30))) (Reg.operands [.gpr 11, .gpr 3] [])) #v[97, 3]
    (.letOp (n := 101) (.exec 0x125fdc (StorePre 0x125fdc 2 (fun s => AddrMode.addr (.base 3 .none) s (0x125fdc + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x125fdc 0 (.base 3 .none)) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (.letOp (n := 102) (.exec 0x125fde (StorePre 0x125fde 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x125fde + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x125fde 2 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[63, 3]
    (.letOp (n := 103) (.exec 0x125fe1 (StorePre 0x125fe1 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x125fe1 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125fe1 1 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[1, 3]
    (.letOp (n := 104) (.exec 0x125fe5 (StorePre 0x125fe5 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x125fe5 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125fe5 10 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 10, .gpr 3] [])) #v[83, 3]
    (.letOp (n := 105) (.exec 0x125fe9 (StorePre 0x125fe9 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x125fe9 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125fe9 8 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 8, .gpr 3] [])) #v[87, 3]
    (.letOp (n := 106) (.exec 0x125fed (StorePre 0x125fed 3 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x125fed + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x125fed 6 (.base 3 (.d8 0x20))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[6, 3]
    (.letOp (n := 107) (.exec 0x125ff0 (StorePre 0x125ff0 4 (fun s => AddrMode.addr (.base 3 (.d8 0x24)) s (0x125ff0 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x125ff0 4 7 (.base 3 (.d8 0x24))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[7, 3]
    (.terminate (.br ⟨.l125ff4, RegMap.args [(0, 0), (1, 1), (2, 63), (3, 3), (4, 4), (5, 59), (6, 6), (7, 7), (8, 87), (9, 95), (10, 83), (11, 97), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 108⟩)))))))))))))))))

def bytes_l125f78_1 : List UInt8 :=
  [0x44, 0x0F, 0xB7, 0x4C, 0x24, 0x40, 0x66, 0x44, 0x89, 0x4B, 0x25, 0x4C, 0x8B, 0x4C, 0x24, 0x43,
    0x4C, 0x8B, 0x5C, 0x24, 0x4B, 0x4C, 0x89, 0x4B, 0x28, 0x4C, 0x89, 0x5B, 0x30, 0x89, 0x03, 0x89,
    0x53, 0x04, 0x48, 0x89, 0x4B, 0x08, 0x4C, 0x89, 0x53, 0x10, 0x4C, 0x89, 0x43, 0x18, 0x89, 0x73,
    0x20, 0x40, 0x88, 0x7B, 0x24]

theorem code_l125f78_1 : ∀ x ∈ codeRange 0x125fbf bytes_l125f78_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x25fbf 53 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l125f78 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x125f78 (shlR32Effect 0x125f78 4 12 16) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[12]
    (.letOp (n := 54) (.exec 0x125f78 (fun s => s.RIP = 0x125f78) (shlR32Effect 0x125f78 4 12 16) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[12]
    (.letOp (n := 55) (.out 0x125f7c (movzxR32R8Effect 0x125f7c 4 5 14) (EffectPart.reads (.reg (.gpr 5)) [.gpr 14] []) (.reg (.gpr 5))) #v[14]
    (.letOp (n := 56) (.exec 0x125f7c (fun s => s.RIP = 0x125f7c) (movzxR32R8Effect 0x125f7c 4 5 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x125f80 (shlR32Effect 0x125f80 3 5 8) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[55]
    (.letOp (n := 58) (.exec 0x125f80 (fun s => s.RIP = 0x125f80) (shlR32Effect 0x125f80 3 5 8) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[55]
    (.letOp (n := 59) (.out 0x125f83 (orR32R32Effect 0x125f83 3 5 12) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 12] []) (.reg (.gpr 5))) #v[57, 53]
    (.letOp (n := 60) (.exec 0x125f83 (fun s => s.RIP = 0x125f83) (orR32R32Effect 0x125f83 3 5 12) (Reg.operands [.gpr 5, .gpr 12] [])) #v[57, 53]
    (.letOp (n := 61) (.out 0x125f86 (movzxR32R8Effect 0x125f86 3 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[2]
    (.letOp (n := 62) (.exec 0x125f86 (fun s => s.RIP = 0x125f86) (movzxR32R8Effect 0x125f86 3 2 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 63) (.out 0x125f89 (orR32R32Effect 0x125f89 2 2 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 5] []) (.reg (.gpr 2))) #v[61, 59]
    (.letOp (n := 64) (.exec 0x125f89 (fun s => s.RIP = 0x125f89) (orR32R32Effect 0x125f89 2 2 5) (Reg.operands [.gpr 2, .gpr 5] [])) #v[61, 59]
    (.letOp (n := 65) (.out 0x125f8b (movzxR32R16Effect 0x125f8b 4 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[8]
    (.letOp (n := 66) (.exec 0x125f8b (fun s => s.RIP = 0x125f8b) (movzxR32R16Effect 0x125f8b 4 8 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 67) (.out 0x125f8f (shlR64Effect 0x125f8f 4 8 48) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[65]
    (.letOp (n := 68) (.exec 0x125f8f (fun s => s.RIP = 0x125f8f) (shlR64Effect 0x125f8f 4 8 48) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[65]
    (.letOp (n := 69) (.out 0x125f93 (movzxR32R8Effect 0x125f93 4 11 11) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11] []) (.reg (.gpr 11))) #v[11]
    (.letOp (n := 70) (.exec 0x125f93 (fun s => s.RIP = 0x125f93) (movzxR32R8Effect 0x125f93 4 11 11) (Reg.operands [.gpr 11] [])) #v[11]
    (.letOp (n := 71) (.out 0x125f97 (shlR64Effect 0x125f97 4 11 40) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[69]
    (.letOp (n := 72) (.exec 0x125f97 (fun s => s.RIP = 0x125f97) (shlR64Effect 0x125f97 4 11 40) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[69]
    (.letOp (n := 73) (.out 0x125f9b (orR64R64Effect 0x125f9b 11 8) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 8] []) (.reg (.gpr 11))) #v[71, 67]
    (.letOp (n := 74) (.exec 0x125f9b (fun s => s.RIP = 0x125f9b) (orR64R64Effect 0x125f9b 11 8) (Reg.operands [.gpr 11, .gpr 8] [])) #v[71, 67]
    (.letOp (n := 75) (.out 0x125f9e (movzxR32R8Effect 0x125f9e 4 8 10) (EffectPart.reads (.reg (.gpr 8)) [.gpr 10] []) (.reg (.gpr 8))) #v[10]
    (.letOp (n := 76) (.exec 0x125f9e (fun s => s.RIP = 0x125f9e) (movzxR32R8Effect 0x125f9e 4 8 10) (Reg.operands [.gpr 10] [])) #v[10]
    (.letOp (n := 77) (.out 0x125fa2 (shlR64Effect 0x125fa2 4 8 32) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[75]
    (.letOp (n := 78) (.exec 0x125fa2 (fun s => s.RIP = 0x125fa2) (shlR64Effect 0x125fa2 4 8 32) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[75]
    (.letOp (n := 79) (.out 0x125fa6 (orR64R64Effect 0x125fa6 8 11) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 11] []) (.reg (.gpr 8))) #v[77, 73]
    (.letOp (n := 80) (.exec 0x125fa6 (fun s => s.RIP = 0x125fa6) (orR64R64Effect 0x125fa6 8 11) (Reg.operands [.gpr 8, .gpr 11] [])) #v[77, 73]
    (.letOp (n := 81) (.out 0x125fa9 (movR32R32Effect 0x125fa9 3 10 15) (EffectPart.reads (.reg (.gpr 10)) [.gpr 15] []) (.reg (.gpr 10))) #v[15]
    (.letOp (n := 82) (.exec 0x125fa9 (fun s => s.RIP = 0x125fa9) (movR32R32Effect 0x125fa9 3 10 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 83) (.out 0x125fac (orR64R64Effect 0x125fac 10 8) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 8] []) (.reg (.gpr 10))) #v[81, 79]
    (.letOp (n := 84) (.exec 0x125fac (fun s => s.RIP = 0x125fac) (orR64R64Effect 0x125fac 10 8) (Reg.operands [.gpr 10, .gpr 8] [])) #v[81, 79]
    (.letOp (n := 85) (.out 0x125faf (movR32R32Effect 0x125faf 3 8 9) (EffectPart.reads (.reg (.gpr 8)) [.gpr 9] []) (.reg (.gpr 8))) #v[9]
    (.letOp (n := 86) (.exec 0x125faf (fun s => s.RIP = 0x125faf) (movR32R32Effect 0x125faf 3 8 9) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 87) (.out 0x125fb2 (orR64R64Effect 0x125fb2 8 13) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 13] []) (.reg (.gpr 8))) #v[85, 13]
    (.letOp (n := 88) (.exec 0x125fb2 (fun s => s.RIP = 0x125fb2) (orR64R64Effect 0x125fb2 8 13) (Reg.operands [.gpr 8, .gpr 13] [])) #v[85, 13]
    (.letOp (n := 89) (.out 0x125fb5 (movzxR32M8Effect 0x125fb5 6 9 (.sib 4 none 0 (.d8 0x42))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 90) (.exec 0x125fb5 (LoadPre 0x125fb5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x42)) s (0x125fb5 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x125fb5 6 9 (.sib 4 none 0 (.d8 0x42))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 91) (.exec 0x125fbb (StorePre 0x125fbb 4 (fun s => AddrMode.addr (.base 3 (.d8 0x27)) s (0x125fbb + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x125fbb 4 9 (.base 3 (.d8 0x27))) (Reg.operands [.gpr 9, .gpr 3] [])) #v[89, 3]
    (b_l125f78_1)))))))))))))))))))))))))))))))))))))))

def bytes_l125f78 : List UInt8 :=
  [0x41, 0xC1, 0xE4, 0x10, 0x41, 0x0F, 0xB6, 0xEE, 0xC1, 0xE5, 0x08, 0x44, 0x09, 0xE5, 0x0F, 0xB6,
    0xD2, 0x09, 0xEA, 0x45, 0x0F, 0xB7, 0xC0, 0x49, 0xC1, 0xE0, 0x30, 0x45, 0x0F, 0xB6, 0xDB, 0x49,
    0xC1, 0xE3, 0x28, 0x4D, 0x09, 0xC3, 0x45, 0x0F, 0xB6, 0xC2, 0x49, 0xC1, 0xE0, 0x20, 0x4D, 0x09,
    0xD8, 0x45, 0x89, 0xFA, 0x4D, 0x09, 0xC2, 0x45, 0x89, 0xC8, 0x4D, 0x09, 0xE8, 0x44, 0x0F, 0xB6,
    0x4C, 0x24, 0x42, 0x44, 0x88, 0x4B, 0x27] ++ bytes_l125f78_1

theorem code_l125f78 : ∀ x ∈ codeRange 0x125f78 bytes_l125f78, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x25f78 71 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l125f78_1

@[cfg_block] def b_l125ff4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x125ff4 (movR64R64Effect 0x125ff4 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 54) (.exec 0x125ff4 (fun s => s.RIP = 0x125ff4) (movR64R64Effect 0x125ff4 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x125ff7 (addR64Imm32Effect 0x125ff7 4 0xd8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 56) (.exec 0x125ff7 (fun s => s.RIP = 0x125ff7) (addR64Imm32Effect 0x125ff7 4 0xd8) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x125ffe (popR64Effect 0x125ffe 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[55]
    (.letOp (n := 58) (.out 0x125ffe (popR64Effect 0x125ffe 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[55]
    (.letOp (n := 59) (.exec 0x125ffe (PopPre 0x125ffe) (popR64Effect 0x125ffe 1 3) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 60) (.out 0x125fff (popR64Effect 0x125fff 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[58]
    (.letOp (n := 61) (.out 0x125fff (popR64Effect 0x125fff 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[58]
    (.letOp (n := 62) (.exec 0x125fff (PopPre 0x125fff) (popR64Effect 0x125fff 2 12) (Reg.operands [.gpr 4] [])) #v[58]
    (.letOp (n := 63) (.out 0x126001 (popR64Effect 0x126001 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[61]
    (.letOp (n := 64) (.out 0x126001 (popR64Effect 0x126001 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 65) (.exec 0x126001 (PopPre 0x126001) (popR64Effect 0x126001 2 13) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 66) (.out 0x126003 (popR64Effect 0x126003 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[64]
    (.letOp (n := 67) (.out 0x126003 (popR64Effect 0x126003 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[64]
    (.letOp (n := 68) (.exec 0x126003 (PopPre 0x126003) (popR64Effect 0x126003 2 14) (Reg.operands [.gpr 4] [])) #v[64]
    (.letOp (n := 69) (.out 0x126005 (popR64Effect 0x126005 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[67]
    (.letOp (n := 70) (.out 0x126005 (popR64Effect 0x126005 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[67]
    (.letOp (n := 71) (.exec 0x126005 (PopPre 0x126005) (popR64Effect 0x126005 2 15) (Reg.operands [.gpr 4] [])) #v[67]
    (.letOp (n := 72) (.out 0x126007 (popR64Effect 0x126007 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[70]
    (.letOp (n := 73) (.out 0x126007 (popR64Effect 0x126007 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[70]
    (.letOp (n := 74) (.exec 0x126007 (PopPre 0x126007) (popR64Effect 0x126007 1 5) (Reg.operands [.gpr 4] [])) #v[70]
    (.letOp (n := 75) (.out 0x126008 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[73]
    (.letOp (n := 76) (.out 0x126008 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[73]
    (.letOp (n := 77) (.exec 0x126008 (RetPre 0x126008) (retEffect) (Reg.operands [.gpr 4] [])) #v[73]
    (.terminate (.ret (RegMap.args [(0, 53), (1, 1), (2, 2), (3, 57), (4, 76), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 78) (some ⟨75, by decide⟩)))))))))))))))))))))))))))

def bytes_l125ff4 : List UInt8 :=
  [0x48, 0x89, 0xD8, 0x48, 0x81, 0xC4, 0xD8, 0x00, 0x00, 0x00, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41,
    0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l125ff4 : ∀ x ∈ codeRange 0x125ff4 bytes_l125ff4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x25ff4 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126009 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126009 (movR32M32LowEffect 0x126009 2 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 54) (.exec 0x126009 (LoadPre 0x126009 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x126009 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x126009 2 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x12600d (movR64M64Effect 0x12600d 1 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x12600d (LoadPre 0x12600d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x12600d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12600d 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x126012 (movR64M64Effect 0x126012 5 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 58) (.exec 0x126012 (LoadPre 0x126012 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x126012 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126012 5 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x126017 (movR64M64Effect 0x126017 9 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 60) (.exec 0x126017 (LoadPre 0x126017 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x126017 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126017 9 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x12601c (movR32M32LowEffect 0x12601c 6 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 62) (.exec 0x12601c (LoadPre 0x12601c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x12601c + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x12601c 6 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x126020 (movzxR32M8Effect 0x126020 5 7 (.sib 4 none 0 (.d8 0x2c))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 64) (.exec 0x126020 (LoadPre 0x126020 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x126020 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x126020 5 7 (.sib 4 none 0 (.d8 0x2c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x126025 (movR64M64Effect 0x126025 8 (.sib 4 none 0 (.d8 0x2d))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 66) (.exec 0x126025 (LoadPre 0x126025 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2d)) s (0x126025 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126025 8 (.sib 4 none 0 (.d8 0x2d))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x12602a (StorePre 0x12602a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x12602a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12602a 8 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x12602f (movR64M64Effect 0x12602f 8 (.sib 4 none 0 (.d8 0x35))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 69) (.exec 0x12602f (LoadPre 0x12602f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x35)) s (0x12602f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12602f 8 (.sib 4 none 0 (.d8 0x35))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.exec 0x126034 (StorePre 0x126034 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x126034 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126034 8 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[68, 4]
    (.letOp (n := 71) (.out 0x126039 (movR32M32Effect 0x126039 8 (.sib 4 none 0 (.d8 0x3c))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 72) (.exec 0x126039 (LoadPre 0x126039 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x126039 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x126039 8 (.sib 4 none 0 (.d8 0x3c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.exec 0x12603e (StorePre 0x12603e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x67)) s (0x12603e + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x12603e 8 (.sib 4 none 0 (.d8 0x67))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[71, 4]
    (.terminate (.br ⟨.l126043, RegMap.args [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 57), (6, 61), (7, 63), (8, 71), (9, 59), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)] 74⟩))))))))))))))))))))))

def bytes_l126009 : List UInt8 :=
  [0x8B, 0x54, 0x24, 0x0C, 0x48, 0x8B, 0x4C, 0x24, 0x10, 0x48, 0x8B, 0x6C, 0x24, 0x18, 0x4C, 0x8B,
    0x4C, 0x24, 0x20, 0x8B, 0x74, 0x24, 0x28, 0x0F, 0xB6, 0x7C, 0x24, 0x2C, 0x4C, 0x8B, 0x44, 0x24,
    0x2D, 0x4C, 0x89, 0x44, 0x24, 0x58, 0x4C, 0x8B, 0x44, 0x24, 0x35, 0x4C, 0x89, 0x44, 0x24, 0x60,
    0x44, 0x8B, 0x44, 0x24, 0x3C, 0x44, 0x89, 0x44, 0x24, 0x67]

theorem code_l126009 : ∀ x ∈ codeRange 0x126009 bytes_l126009, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26009 58 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126043 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126043 (movR64R64Effect 0x126043 8 5) (EffectPart.reads (.reg (.gpr 8)) [.gpr 5] []) (.reg (.gpr 8))) #v[5]
    (.letOp (n := 54) (.exec 0x126043 (fun s => s.RIP = 0x126043) (movR64R64Effect 0x126043 8 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 55) (.out 0x126046 (andR64R64Effect 0x126046 8 13) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 13] []) (.reg (.gpr 8))) #v[53, 13]
    (.letOp (n := 56) (.exec 0x126046 (fun s => s.RIP = 0x126046) (andR64R64Effect 0x126046 8 13) (Reg.operands [.gpr 8, .gpr 13] [])) #v[53, 13]
    (.terminate (.br ⟨.l126076, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (9, 9), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l126043 : List UInt8 :=
  [0x49, 0x89, 0xE8, 0x4D, 0x21, 0xE8, 0xEB, 0x2B]

theorem code_l126043 : ∀ x ∈ codeRange 0x126043 bytes_l126043, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26043 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12604b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12604b (incR64Effect 0x12604b 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 54) (.exec 0x12604b (fun s => s.RIP = 0x12604b) (incR64Effect 0x12604b 0) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[0]
    (.letOp (n := 55) (.exec 0x12604e (StorePre 0x12604e 4 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x12604e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12604e 0 (.base 14 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 56) (.out 0x126052 (movR32M32Effect 0x126052 12 (.base 14 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 14] []) (.reg (.gpr 12))) #v[14]
    (.letOp (n := 57) (.exec 0x126052 (LoadPre 0x126052 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x126052 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x126052 12 (.base 14 (.d8 0x18))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 58) (.out 0x126056 (cmpR32R32Effect 0x126056 3 5 12) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 12] []) (.flag .CF)) #v[5, 56]
    (.letOp (n := 59) (.out 0x126056 (cmpR32R32Effect 0x126056 3 5 12) (EffectPart.reads (.flag .ZF) [.gpr 5, .gpr 12] []) (.flag .ZF)) #v[5, 56]
    (.letOp (n := 60) (.exec 0x126056 (fun s => s.RIP = 0x126056) (cmpR32R32Effect 0x126056 3 5 12) (Reg.operands [.gpr 5, .gpr 12] [])) #v[5, 56]
    (.letOp (n := 61) (.pure (condOp 6)) #v[58, 59]
    (.terminate (.condBr (Fin.last 61) ⟨.l1260bf, RegMap.args [(0, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 56), (13, 13), (14, 14), (15, 15), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ ⟨.l12605b, RegMap.args [(0, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 56), (13, 13), (14, 14), (15, 15), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩))))))))))

def bytes_l12604b : List UInt8 :=
  [0x48, 0xFF, 0xC0, 0x49, 0x89, 0x46, 0x10, 0x45, 0x8B, 0x66, 0x18, 0x44, 0x39, 0xE5, 0x76, 0x64]

theorem code_l12604b : ∀ x ∈ codeRange 0x12604b bytes_l12604b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2604b 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12605b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12605b (leaR32Effect 0x12605b 5 1 (.sib 12 none 0 (.d8 0x1))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 12] []) (.reg (.gpr 1))) #v[12]
    (.letOp (n := 54) (.exec 0x12605b (fun s => s.RIP = 0x12605b) (leaR32Effect 0x12605b 5 1 (.sib 12 none 0 (.d8 0x1))) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 55) (.out 0x126060 (shlR64Effect 0x126060 4 1 32) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 56) (.exec 0x126060 (fun s => s.RIP = 0x126060) (shlR64Effect 0x126060 4 1 32) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 57) (.out 0x126064 (orR64Imm8Effect 0x126064 1 0x3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[55]
    (.letOp (n := 58) (.exec 0x126064 (fun s => s.RIP = 0x126064) (orR64Imm8Effect 0x126064 1 0x3) (Reg.operands [.gpr 1] [])) #v[55]
    (.terminate (.br ⟨.l126068, RegMap.args [(1, 57), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l12605b : List UInt8 :=
  [0x41, 0x8D, 0x4C, 0x24, 0x01, 0x48, 0xC1, 0xE1, 0x20, 0x48, 0x83, 0xC9, 0x03]

theorem code_l12605b : ∀ x ∈ codeRange 0x12605b bytes_l12605b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2605b 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126068 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126068 (movR32Imm32Effect 0x126068 5 0 0x1) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 54) (.exec 0x126068 (fun s => s.RIP = 0x126068) (movR32Imm32Effect 0x126068 5 0 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x12606d (xorR32R32Effect 0x12606d 3 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 8] []) (.reg (.gpr 8))) #v[8, 8]
    (.letOp (n := 56) (.exec 0x12606d (fun s => s.RIP = 0x12606d) (xorR32R32Effect 0x12606d 3 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[8, 8]
    (.letOp (n := 57) (.out 0x126070 (movR32R32Effect 0x126070 3 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12] []) (.reg (.gpr 2))) #v[12]
    (.letOp (n := 58) (.exec 0x126070 (fun s => s.RIP = 0x126070) (movR32R32Effect 0x126070 3 2 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 59) (.out 0x126073 (movR32R32Effect 0x126073 3 5 12) (EffectPart.reads (.reg (.gpr 5)) [.gpr 12] []) (.reg (.gpr 5))) #v[12]
    (.letOp (n := 60) (.exec 0x126073 (fun s => s.RIP = 0x126073) (movR32R32Effect 0x126073 3 5 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.terminate (.br ⟨.l126076, RegMap.args [(0, 53), (1, 1), (2, 57), (3, 3), (4, 4), (5, 59), (6, 6), (7, 7), (8, 55), (9, 9), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩)))))))))

def bytes_l126068 : List UInt8 :=
  [0xB8, 0x01, 0x00, 0x00, 0x00, 0x45, 0x31, 0xC0, 0x44, 0x89, 0xE2, 0x44, 0x89, 0xE5]

theorem code_l126068 : ∀ x ∈ codeRange 0x126068 bytes_l126068, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26068 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126076 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126076 (movR32M32Effect 0x126076 10 (.sib 4 none 0 (.d8 0x67))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 54) (.exec 0x126076 (LoadPre 0x126076 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x67)) s (0x126076 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x126076 10 (.sib 4 none 0 (.d8 0x67))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x12607b (StorePre 0x12607b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4f)) s (0x12607b + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x12607b 10 (.sib 4 none 0 (.d8 0x4f))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x126080 (movR64M64Effect 0x126080 10 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 57) (.exec 0x126080 (LoadPre 0x126080 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x126080 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126080 10 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.out 0x126085 (movR64M64Effect 0x126085 11 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 59) (.exec 0x126085 (LoadPre 0x126085 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x126085 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126085 11 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.exec 0x12608a (StorePre 0x12608a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x12608a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12608a 11 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[58, 4]
    (.letOp (n := 61) (.exec 0x12608f (StorePre 0x12608f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x12608f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12608f 10 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 62) (.out 0x126094 (movR32R32Effect 0x126094 3 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[2]
    (.letOp (n := 63) (.exec 0x126094 (fun s => s.RIP = 0x126094) (movR32R32Effect 0x126094 3 14 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 64) (.out 0x126097 (shrR32Effect 0x126097 4 14 8) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[62]
    (.letOp (n := 65) (.exec 0x126097 (fun s => s.RIP = 0x126097) (shrR32Effect 0x126097 4 14 8) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[62]
    (.letOp (n := 66) (.out 0x12609b (movR32R32Effect 0x12609b 3 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 2] []) (.reg (.gpr 12))) #v[2]
    (.letOp (n := 67) (.exec 0x12609b (fun s => s.RIP = 0x12609b) (movR32R32Effect 0x12609b 3 12 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 68) (.out 0x12609e (shrR32Effect 0x12609e 4 12 16) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[66]
    (.letOp (n := 69) (.exec 0x12609e (fun s => s.RIP = 0x12609e) (shrR32Effect 0x12609e 4 12 16) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[66]
    (.letOp (n := 70) (.out 0x1260a2 (movR64R64Effect 0x1260a2 10 8) (EffectPart.reads (.reg (.gpr 10)) [.gpr 8] []) (.reg (.gpr 10))) #v[8]
    (.letOp (n := 71) (.exec 0x1260a2 (fun s => s.RIP = 0x1260a2) (movR64R64Effect 0x1260a2 10 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 72) (.out 0x1260a5 (shrR64Effect 0x1260a5 4 10 32) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[70]
    (.letOp (n := 73) (.exec 0x1260a5 (fun s => s.RIP = 0x1260a5) (shrR64Effect 0x1260a5 4 10 32) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[70]
    (.letOp (n := 74) (.out 0x1260a9 (movR64R64Effect 0x1260a9 11 8) (EffectPart.reads (.reg (.gpr 11)) [.gpr 8] []) (.reg (.gpr 11))) #v[8]
    (.letOp (n := 75) (.exec 0x1260a9 (fun s => s.RIP = 0x1260a9) (movR64R64Effect 0x1260a9 11 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 76) (.out 0x1260ac (shrR64Effect 0x1260ac 4 11 40) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[74]
    (.letOp (n := 77) (.exec 0x1260ac (fun s => s.RIP = 0x1260ac) (shrR64Effect 0x1260ac 4 11 40) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[74]
    (.letOp (n := 78) (.out 0x1260b0 (shrR64Effect 0x1260b0 4 8 48) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[8]
    (.letOp (n := 79) (.exec 0x1260b0 (fun s => s.RIP = 0x1260b0) (shrR64Effect 0x1260b0 4 8 48) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[8]
    (.letOp (n := 80) (.out 0x1260b4 (andR64R64Effect 0x1260b4 13 9) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 9] []) (.reg (.gpr 13))) #v[13, 9]
    (.letOp (n := 81) (.exec 0x1260b4 (fun s => s.RIP = 0x1260b4) (andR64R64Effect 0x1260b4 13 9) (Reg.operands [.gpr 13, .gpr 9] [])) #v[13, 9]
    (.letOp (n := 82) (.out 0x1260b7 (movR32R32Effect 0x1260b7 3 15 5) (EffectPart.reads (.reg (.gpr 15)) [.gpr 5] []) (.reg (.gpr 15))) #v[5]
    (.letOp (n := 83) (.exec 0x1260b7 (fun s => s.RIP = 0x1260b7) (movR32R32Effect 0x1260b7 3 15 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.terminate (.br ⟨.l125f78, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 78), (9, 9), (10, 72), (11, 76), (12, 68), (13, 80), (14, 64), (15, 82), (22, 22), (39, 39), (50, 50), (51, 51)] 84⟩))))))))))))))))))))))))))))))))

def bytes_l126076 : List UInt8 :=
  [0x44, 0x8B, 0x54, 0x24, 0x67, 0x44, 0x89, 0x54, 0x24, 0x4F, 0x4C, 0x8B, 0x54, 0x24, 0x58, 0x4C,
    0x8B, 0x5C, 0x24, 0x60, 0x4C, 0x89, 0x5C, 0x24, 0x48, 0x4C, 0x89, 0x54, 0x24, 0x40, 0x41, 0x89,
    0xD6, 0x41, 0xC1, 0xEE, 0x08, 0x41, 0x89, 0xD4, 0x41, 0xC1, 0xEC, 0x10, 0x4D, 0x89, 0xC2, 0x49,
    0xC1, 0xEA, 0x20, 0x4D, 0x89, 0xC3, 0x49, 0xC1, 0xEB, 0x28, 0x49, 0xC1, 0xE8, 0x30, 0x4D, 0x21,
    0xCD, 0x41, 0x89, 0xEF, 0xE9, 0xB9, 0xFE, 0xFF, 0xFF]

theorem code_l126076 : ∀ x ∈ codeRange 0x126076 bytes_l126076, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26076 73 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1260bf : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1260bf (StorePre 0x1260bf 4 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x1260bf + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x1260bf 5 (.base 14 (.d8 0x18))) (Reg.operands [.gpr 5, .gpr 14] [])) #v[5, 14]
    (.letOp (n := 54) (.out 0x1260c3 (leaR64Effect 0x1260c3 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 55) (.exec 0x1260c3 (fun s => s.RIP = 0x1260c3) (leaR64Effect 0x1260c3 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x1260c8 (movR64R64Effect 0x1260c8 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 57) (.exec 0x1260c8 (fun s => s.RIP = 0x1260c8) (movR64R64Effect 0x1260c8 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 58) (.out 0x1260cb (callEffect (fun _ => 0x125450) 0x1260d0) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 59) (.exec 0x1260cb (PushPre 0x1260cb 5) (callEffect (fun _ => 0x125450) 0x1260d0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.const ⟨64, 0x1260d0⟩) #v[]
    (.terminate (.call ⟨.l125450, RegMap.args [(3, 3), (4, 58), (5, 5), (6, 56), (7, 54), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩ { target := .l1260d0, kept := #v[], arity := rfl, guard := some (Fin.last 60) })))))))))

def bytes_l1260bf : List UInt8 :=
  [0x41, 0x89, 0x6E, 0x18, 0x48, 0x8D, 0x7C, 0x24, 0x08, 0x4C, 0x89, 0xF6, 0xE8, 0x80, 0xF3, 0xFF,
    0xFF]

theorem code_l1260bf : ∀ x ∈ codeRange 0x1260bf bytes_l1260bf, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x260bf 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1260d0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1260d0 (movR32M32LowEffect 0x1260d0 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1260d0 (LoadPre 0x1260d0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1260d0 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1260d0 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1260d4 (movR64M64Effect 0x1260d4 1 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x1260d4 (LoadPre 0x1260d4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x1260d4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1260d4 1 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x1260d9 (StorePre 0x1260d9 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x1260d9 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1260d9 1 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 58) (.out 0x1260e1 (movR64M64Effect 0x1260e1 1 (.sib 4 none 0 (.d8 0x14))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 59) (.exec 0x1260e1 (LoadPre 0x1260e1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x1260e1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1260e1 1 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.exec 0x1260e6 (StorePre 0x1260e6 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x1260e6 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1260e6 1 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[58, 4]
    (.letOp (n := 61) (.out 0x1260ee (cmpR32Imm8Effect 0x1260ee 3 0 0x2) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[53]
    (.letOp (n := 62) (.exec 0x1260ee (fun s => s.RIP = 0x1260ee) (cmpR32Imm8Effect 0x1260ee 3 0 0x2) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 63) (.pure (condOp 5)) #v[61]
    (.terminate (.condBr (Fin.last 63) ⟨.l12614f, RegMap.args [(0, 53), (1, 58), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 61), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ ⟨.l1260f3, RegMap.args [(0, 53), (1, 58), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 61), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩))))))))))))

def bytes_l1260d0 : List UInt8 :=
  [0x8B, 0x44, 0x24, 0x08, 0x48, 0x8B, 0x4C, 0x24, 0x0C, 0x48, 0x89, 0x8C, 0x24, 0xA8, 0x00, 0x00,
    0x00, 0x48, 0x8B, 0x4C, 0x24, 0x14, 0x48, 0x89, 0x8C, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x83, 0xF8,
    0x02, 0x75, 0x5C]

theorem code_l1260d0 : ∀ x ∈ codeRange 0x1260d0 bytes_l1260d0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x260d0 35 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1260f3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1260f3 (movR64M64Effect 0x1260f3 6 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 54) (.exec 0x1260f3 (LoadPre 0x1260f3 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x1260f3 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1260f3 6 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1260fb (movR64M64Effect 0x1260fb 0 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 56) (.exec 0x1260fb (LoadPre 0x1260fb (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x1260fb + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1260fb 0 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x126103 (StorePre 0x126103 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x126103 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x126103 6 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 58) (.exec 0x12610b (StorePre 0x12610b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x12610b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x12610b 0 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 59) (.out 0x126113 (leaR64Effect 0x126113 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 60) (.exec 0x126113 (fun s => s.RIP = 0x126113) (leaR64Effect 0x126113 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x126118 (movR32Imm32Effect 0x126118 5 2 0x2) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 62) (.exec 0x126118 (fun s => s.RIP = 0x126118) (movR32Imm32Effect 0x126118 5 2 0x2) (Reg.operands [] [])) #v[]
    (.letOp (n := 63) (.out 0x12611d (callEffect (fun _ => 0x1276d0) 0x126122) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 64) (.exec 0x12611d (PushPre 0x12611d 5) (callEffect (fun _ => 0x1276d0) 0x126122) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.const ⟨64, 0x126122⟩) #v[]
    (.terminate (.call ⟨.l1276d0, RegMap.args [(0, 55), (1, 1), (2, 61), (3, 3), (4, 63), (5, 5), (6, 53), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩ { target := .l126122, kept := #v[], arity := rfl, guard := some (Fin.last 65) }))))))))))))))

def bytes_l1260f3 : List UInt8 :=
  [0x48, 0x8B, 0xB4, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00,
    0x48, 0x89, 0xB4, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0xD0, 0x00, 0x00, 0x00,
    0x48, 0x8D, 0x7C, 0x24, 0x08, 0xBA, 0x02, 0x00, 0x00, 0x00, 0xE8, 0xAE, 0x15, 0x00, 0x00]

theorem code_l1260f3 : ∀ x ∈ codeRange 0x1260f3 bytes_l1260f3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x260f3 47 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126122 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126122 (movR32M32LowEffect 0x126122 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x126122 (LoadPre 0x126122 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x126122 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x126122 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x126126 (cmpR32Imm8Effect 0x126126 3 0 0x2) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x126126 (fun s => s.RIP = 0x126126) (cmpR32Imm8Effect 0x126126 3 0 0x2) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l1261aa, RegMap.args [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l12612b, RegMap.args [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l126122 : List UInt8 :=
  [0x8B, 0x44, 0x24, 0x08, 0x83, 0xF8, 0x02, 0x75, 0x7F]

theorem code_l126122 : ∀ x ∈ codeRange 0x126122 bytes_l126122, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26122 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12612b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12612b (leaR64Effect 0x12612b 7 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x12612b (fun s => s.RIP = 0x12612b) (leaR64Effect 0x12612b 7 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x126130 (leaR64Effect 0x126130 2 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 56) (.exec 0x126130 (fun s => s.RIP = 0x126130) (leaR64Effect 0x126130 2 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x126138 (movR64R64Effect 0x126138 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 58) (.exec 0x126138 (fun s => s.RIP = 0x126138) (movR64R64Effect 0x126138 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 59) (.out 0x12613b (callEffect (fun _ => 0x126d20) 0x126140) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x12613b (PushPre 0x12613b 5) (callEffect (fun _ => 0x126d20) 0x126140) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x126140⟩) #v[]
    (.terminate (.call ⟨.l126d20, RegMap.args [(1, 1), (2, 55), (3, 3), (4, 59), (5, 5), (6, 57), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l126140, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l12612b : List UInt8 :=
  [0x48, 0x8D, 0x7C, 0x24, 0x70, 0x48, 0x8D, 0x94, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF6,
    0xE8, 0xE0, 0x0B, 0x00, 0x00]

theorem code_l12612b : ∀ x ∈ codeRange 0x12612b bytes_l12612b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2612b 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126140 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126140 (movR32M32LowEffect 0x126140 0 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x126140 (LoadPre 0x126140 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x126140 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x126140 0 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x126144 (cmpR32Imm8Effect 0x126144 3 0 0x2) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x126144 (fun s => s.RIP = 0x126144) (cmpR32Imm8Effect 0x126144 3 0 0x2) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x126147 (atFlags (condHolds 5) (setccR8Effect 0x126147 3 1)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 1))) #v[1, 55]
    (.letOp (n := 58) (.exec 0x126147 (fun s => s.RIP = 0x126147) (atFlags (condHolds 5) (setccR8Effect 0x126147 3 1)) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[1, 55]
    (.terminate (.br ⟨.l1261ff, RegMap.args [(0, 53), (1, 57), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l126140 : List UInt8 :=
  [0x8B, 0x44, 0x24, 0x70, 0x83, 0xF8, 0x02, 0x0F, 0x95, 0xC1, 0xE9, 0xB0, 0x00, 0x00, 0x00]

theorem code_l126140 : ∀ x ∈ codeRange 0x126140 bytes_l126140, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26140 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12614f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12614f (movR32M32LowEffect 0x12614f 1 (.sib 4 none 0 (.d8 0x3c))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x12614f (LoadPre 0x12614f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x12614f + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x12614f 1 (.sib 4 none 0 (.d8 0x3c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x126153 (StorePre 0x126153 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa4)) s (0x126153 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x126153 1 (.sib 4 none 0 (.d32 0xa4))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x12615a (movR64M64Effect 0x12615a 1 (.sib 4 none 0 (.d8 0x34))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 57) (.exec 0x12615a (LoadPre 0x12615a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x12615a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12615a 1 (.sib 4 none 0 (.d8 0x34))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x12615f (StorePre 0x12615f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9c)) s (0x12615f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x12615f 1 (.sib 4 none 0 (.d32 0x9c))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x126167 (movR64M64Effect 0x126167 1 (.sib 4 none 0 (.d8 0x2c))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 60) (.exec 0x126167 (LoadPre 0x126167 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x126167 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126167 1 (.sib 4 none 0 (.d8 0x2c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x12616c (StorePre 0x12616c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x94)) s (0x12616c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x12616c 1 (.sib 4 none 0 (.d32 0x94))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x126174 (movR64M64Effect 0x126174 1 (.sib 4 none 0 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 63) (.exec 0x126174 (LoadPre 0x126174 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x126174 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126174 1 (.sib 4 none 0 (.d8 0x1c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x126179 (movR64M64Effect 0x126179 2 (.sib 4 none 0 (.d8 0x24))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 65) (.exec 0x126179 (LoadPre 0x126179 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x126179 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126179 2 (.sib 4 none 0 (.d8 0x24))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x12617e (StorePre 0x12617e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x8c)) s (0x12617e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x12617e 2 (.sib 4 none 0 (.d32 0x8c))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x126186 (StorePre 0x126186 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x84)) s (0x126186 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x126186 1 (.sib 4 none 0 (.d32 0x84))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x12618e (movR64M64Effect 0x12618e 1 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 69) (.exec 0x12618e (LoadPre 0x12618e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x12618e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x12618e 1 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.out 0x126196 (movR64M64Effect 0x126196 2 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 71) (.exec 0x126196 (LoadPre 0x126196 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x126196 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x126196 2 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.exec 0x12619e (StorePre 0x12619e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x74)) s (0x12619e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12619e 1 (.sib 4 none 0 (.d8 0x74))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[68, 4]
    (.letOp (n := 73) (.exec 0x1261a3 (StorePre 0x1261a3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7c)) s (0x1261a3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1261a3 2 (.sib 4 none 0 (.d8 0x7c))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[70, 4]
    (.terminate (.br ⟨.l1261fd, RegMap.args [(0, 0), (1, 68), (2, 70), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 74⟩))))))))))))))))))))))

def bytes_l12614f : List UInt8 :=
  [0x8B, 0x4C, 0x24, 0x3C, 0x89, 0x8C, 0x24, 0xA4, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x4C, 0x24, 0x34,
    0x48, 0x89, 0x8C, 0x24, 0x9C, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x4C, 0x24, 0x2C, 0x48, 0x89, 0x8C,
    0x24, 0x94, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x4C, 0x24, 0x1C, 0x48, 0x8B, 0x54, 0x24, 0x24, 0x48,
    0x89, 0x94, 0x24, 0x8C, 0x00, 0x00, 0x00, 0x48, 0x89, 0x8C, 0x24, 0x84, 0x00, 0x00, 0x00, 0x48,
    0x8B, 0x8C, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x94, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x48,
    0x89, 0x4C, 0x24, 0x74, 0x48, 0x89, 0x54, 0x24, 0x7C, 0xEB, 0x53]

theorem code_l12614f : ∀ x ∈ codeRange 0x12614f bytes_l12614f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2614f 91 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1261aa : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1261aa (movR64M64Effect 0x1261aa 1 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x1261aa (LoadPre 0x1261aa (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x1261aa + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1261aa 1 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1261af (movR64M64Effect 0x1261af 2 (.sib 4 none 0 (.d8 0x14))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 56) (.exec 0x1261af (LoadPre 0x1261af (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x1261af + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1261af 2 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x1261b4 (StorePre 0x1261b4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7c)) s (0x1261b4 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1261b4 2 (.sib 4 none 0 (.d8 0x7c))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 58) (.out 0x1261b9 (movR64M64Effect 0x1261b9 2 (.sib 4 none 0 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 59) (.exec 0x1261b9 (LoadPre 0x1261b9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x1261b9 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1261b9 2 (.sib 4 none 0 (.d8 0x1c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.exec 0x1261be (StorePre 0x1261be 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x84)) s (0x1261be + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1261be 2 (.sib 4 none 0 (.d32 0x84))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[58, 4]
    (.letOp (n := 61) (.out 0x1261c6 (movR64M64Effect 0x1261c6 2 (.sib 4 none 0 (.d8 0x24))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 62) (.exec 0x1261c6 (LoadPre 0x1261c6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x1261c6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1261c6 2 (.sib 4 none 0 (.d8 0x24))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x1261cb (StorePre 0x1261cb 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x8c)) s (0x1261cb + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1261cb 2 (.sib 4 none 0 (.d32 0x8c))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.out 0x1261d3 (movR64M64Effect 0x1261d3 2 (.sib 4 none 0 (.d8 0x2c))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 65) (.exec 0x1261d3 (LoadPre 0x1261d3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x1261d3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1261d3 2 (.sib 4 none 0 (.d8 0x2c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x1261d8 (StorePre 0x1261d8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x94)) s (0x1261d8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1261d8 2 (.sib 4 none 0 (.d32 0x94))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.out 0x1261e0 (movR64M64Effect 0x1261e0 2 (.sib 4 none 0 (.d8 0x34))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 68) (.exec 0x1261e0 (LoadPre 0x1261e0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x1261e0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1261e0 2 (.sib 4 none 0 (.d8 0x34))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.exec 0x1261e5 (StorePre 0x1261e5 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9c)) s (0x1261e5 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1261e5 2 (.sib 4 none 0 (.d32 0x9c))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[67, 4]
    (.letOp (n := 70) (.out 0x1261ed (movR32M32LowEffect 0x1261ed 2 (.sib 4 none 0 (.d8 0x3c))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 71) (.exec 0x1261ed (LoadPre 0x1261ed (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x1261ed + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1261ed 2 (.sib 4 none 0 (.d8 0x3c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.exec 0x1261f1 (StorePre 0x1261f1 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa4)) s (0x1261f1 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x1261f1 2 (.sib 4 none 0 (.d32 0xa4))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[70, 4]
    (.letOp (n := 73) (.exec 0x1261f8 (StorePre 0x1261f8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x74)) s (0x1261f8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1261f8 1 (.sib 4 none 0 (.d8 0x74))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[53, 4]
    (.terminate (.br ⟨.l1261fd, RegMap.args [(0, 0), (1, 53), (2, 70), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 74⟩))))))))))))))))))))))

def bytes_l1261aa : List UInt8 :=
  [0x48, 0x8B, 0x4C, 0x24, 0x0C, 0x48, 0x8B, 0x54, 0x24, 0x14, 0x48, 0x89, 0x54, 0x24, 0x7C, 0x48,
    0x8B, 0x54, 0x24, 0x1C, 0x48, 0x89, 0x94, 0x24, 0x84, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x54, 0x24,
    0x24, 0x48, 0x89, 0x94, 0x24, 0x8C, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x54, 0x24, 0x2C, 0x48, 0x89,
    0x94, 0x24, 0x94, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x54, 0x24, 0x34, 0x48, 0x89, 0x94, 0x24, 0x9C,
    0x00, 0x00, 0x00, 0x8B, 0x54, 0x24, 0x3C, 0x89, 0x94, 0x24, 0xA4, 0x00, 0x00, 0x00, 0x48, 0x89,
    0x4C, 0x24, 0x74]

theorem code_l1261aa : ∀ x ∈ codeRange 0x1261aa bytes_l1261aa, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x261aa 83 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1261fd : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1261fd (movR8Imm8Effect 0x1261fd 2 1 0x1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1]
    (.letOp (n := 54) (.exec 0x1261fd (fun s => s.RIP = 0x1261fd) (movR8Imm8Effect 0x1261fd 2 1 0x1) (Reg.operands [.gpr 1] [])) #v[1]
    (.terminate (.br ⟨.l1261ff, RegMap.args [(0, 0), (1, 53), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l1261fd : List UInt8 :=
  [0xB1, 0x01]

theorem code_l1261fd : ∀ x ∈ codeRange 0x1261fd bytes_l1261fd, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x261fd 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1261ff : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1261ff (movR32M32Effect 0x1261ff 5 (.base 14 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 14] []) (.reg (.gpr 5))) #v[14]
    (.letOp (n := 54) (.exec 0x1261ff (LoadPre 0x1261ff (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x1261ff + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x1261ff 5 (.base 14 (.d8 0x18))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 55) (.out 0x126203 (movR32M32Effect 0x126203 2 (.base 14 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14] []) (.reg (.gpr 2))) #v[14]
    (.letOp (n := 56) (.exec 0x126203 (LoadPre 0x126203 (fun s => AddrMode.addr (.base 14 (.d8 0x1c)) s (0x126203 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x126203 2 (.base 14 (.d8 0x1c))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x126207 (subR32R32Effect 0x126207 2 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 2] []) (.reg (.gpr 5))) #v[53, 55]
    (.letOp (n := 58) (.out 0x126207 (subR32R32Effect 0x126207 2 5 2) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 2] []) (.flag .CF)) #v[53, 55]
    (.letOp (n := 59) (.out 0x126207 (subR32R32Effect 0x126207 2 5 2) (EffectPart.reads (.flag .ZF) [.gpr 5, .gpr 2] []) (.flag .ZF)) #v[53, 55]
    (.letOp (n := 60) (.exec 0x126207 (fun s => s.RIP = 0x126207) (subR32R32Effect 0x126207 2 5 2) (Reg.operands [.gpr 5, .gpr 2] [])) #v[53, 55]
    (.letOp (n := 61) (.out 0x126209 (atFlags (condHolds 6) (setccR8Effect 0x126209 4 6)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF]) (.reg (.gpr 6))) #v[6, 58, 59]
    (.letOp (n := 62) (.exec 0x126209 (fun s => s.RIP = 0x126209) (atFlags (condHolds 6) (setccR8Effect 0x126209 4 6)) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF])) #v[6, 58, 59]
    (.letOp (n := 63) (.out 0x12620d (movR64M64Effect 0x12620d 7 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 64) (.exec 0x12620d (LoadPre 0x12620d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x12620d + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x12620d 7 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.exec 0x126215 (StorePre 0x126215 3 (fun s => AddrMode.addr (.base 14 .none) s (0x126215 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x126215 7 (.base 14 .none)) (Reg.operands [.gpr 7, .gpr 14] [])) #v[63, 14]
    (.letOp (n := 66) (.out 0x126218 (movR64M64Effect 0x126218 7 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 67) (.exec 0x126218 (LoadPre 0x126218 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x126218 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x126218 7 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.exec 0x126220 (StorePre 0x126220 4 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x126220 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126220 7 (.base 14 (.d8 0x8))) (Reg.operands [.gpr 7, .gpr 14] [])) #v[66, 14]
    (.letOp (n := 69) (.exec 0x126224 (StorePre 0x126224 4 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x126224 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x126224 12 (.base 14 (.d8 0x18))) (Reg.operands [.gpr 12, .gpr 14] [])) #v[12, 14]
    (.letOp (n := 70) (.out 0x126228 (movR64M64Effect 0x126228 7 (.base 14 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 71) (.exec 0x126228 (LoadPre 0x126228 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x126228 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x126228 7 (.base 14 (.d8 0x10))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x12622c (cmpR64Imm8Effect 0x12622c 7 0x1) (EffectPart.reads (.flag .CF) [.gpr 7] []) (.flag .CF)) #v[70]
    (.letOp (n := 73) (.exec 0x12622c (fun s => s.RIP = 0x12622c) (cmpR64Imm8Effect 0x12622c 7 0x1) (Reg.operands [.gpr 7] [])) #v[70]
    (.letOp (n := 74) (.out 0x126230 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x126230 7 0xff)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[70, 72]
    (.letOp (n := 75) (.exec 0x126230 (fun s => s.RIP = 0x126230) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x126230 7 0xff)) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[70, 72]
    (.letOp (n := 76) (.exec 0x126234 (StorePre 0x126234 4 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x126234 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126234 7 (.base 14 (.d8 0x10))) (Reg.operands [.gpr 7, .gpr 14] [])) #v[74, 14]
    (.letOp (n := 77) (.out 0x126238 (orR8R8Effect 0x126238 3 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[61, 1]
    (.letOp (n := 78) (.out 0x126238 (orR8R8Effect 0x126238 3 6 1) (EffectPart.reads (.flag .ZF) [.gpr 6, .gpr 1] []) (.flag .ZF)) #v[61, 1]
    (.letOp (n := 79) (.exec 0x126238 (fun s => s.RIP = 0x126238) (orR8R8Effect 0x126238 3 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[61, 1]
    (.letOp (n := 80) (.pure (condOp 4)) #v[78]
    (.terminate (.condBr (Fin.last 80) ⟨.l1262b4, RegMap.args [(0, 0), (1, 1), (2, 55), (3, 3), (4, 4), (5, 57), (6, 77), (7, 74), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 78), (22, 22), (39, 39), (50, 50), (51, 51)] 81⟩ ⟨.l12623d, RegMap.args [(0, 0), (1, 1), (2, 55), (3, 3), (4, 4), (5, 57), (6, 77), (7, 74), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 78), (22, 22), (39, 39), (50, 50), (51, 51)] 81⟩)))))))))))))))))))))))))))))

def bytes_l1261ff : List UInt8 :=
  [0x41, 0x8B, 0x6E, 0x18, 0x41, 0x8B, 0x56, 0x1C, 0x29, 0xD5, 0x40, 0x0F, 0x96, 0xC6, 0x48, 0x8B,
    0xBC, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x49, 0x89, 0x3E, 0x48, 0x8B, 0xBC, 0x24, 0xB8, 0x00, 0x00,
    0x00, 0x49, 0x89, 0x7E, 0x08, 0x45, 0x89, 0x66, 0x18, 0x49, 0x8B, 0x7E, 0x10, 0x48, 0x83, 0xFF,
    0x01, 0x48, 0x83, 0xD7, 0xFF, 0x49, 0x89, 0x7E, 0x10, 0x40, 0x08, 0xCE, 0x74, 0x77]

theorem code_l1261ff : ∀ x ∈ codeRange 0x1261ff bytes_l1261ff, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x261ff 62 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12623d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12623d (movR32M32LowEffect 0x12623d 2 (.sib 4 none 0 (.d8 0x74))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 54) (.exec 0x12623d (LoadPre 0x12623d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x74)) s (0x12623d + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x12623d 2 (.sib 4 none 0 (.d8 0x74))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x126241 (movR64M64Effect 0x126241 1 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x126241 (LoadPre 0x126241 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x126241 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126241 1 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x126246 (movR64M64Effect 0x126246 5 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 58) (.exec 0x126246 (LoadPre 0x126246 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x126246 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x126246 5 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x12624e (movR64M64Effect 0x12624e 9 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 60) (.exec 0x12624e (LoadPre 0x12624e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x12624e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x12624e 9 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x126256 (movR32M32LowEffect 0x126256 6 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 62) (.exec 0x126256 (LoadPre 0x126256 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x126256 + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x126256 6 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x12625d (movzxR32M8Effect 0x12625d 8 7 (.sib 4 none 0 (.d32 0x94))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 64) (.exec 0x12625d (LoadPre 0x12625d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x94)) s (0x12625d + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x12625d 8 7 (.sib 4 none 0 (.d32 0x94))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x126265 (movR64M64Effect 0x126265 8 (.sib 4 none 0 (.d32 0x95))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 66) (.exec 0x126265 (LoadPre 0x126265 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x95)) s (0x126265 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x126265 8 (.sib 4 none 0 (.d32 0x95))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x12626d (StorePre 0x12626d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x12626d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12626d 8 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x126272 (movR64M64Effect 0x126272 8 (.sib 4 none 0 (.d32 0x9d))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 69) (.exec 0x126272 (LoadPre 0x126272 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9d)) s (0x126272 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x126272 8 (.sib 4 none 0 (.d32 0x9d))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.exec 0x12627a (StorePre 0x12627a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x12627a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12627a 8 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[68, 4]
    (.letOp (n := 71) (.out 0x12627f (movR32M32Effect 0x12627f 8 (.sib 4 none 0 (.d32 0xa4))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 72) (.exec 0x12627f (LoadPre 0x12627f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa4)) s (0x12627f + BitVec.ofNat 64 8)) 4) (movR32M32Effect 0x12627f 8 (.sib 4 none 0 (.d32 0xa4))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.exec 0x126287 (StorePre 0x126287 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x67)) s (0x126287 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x126287 8 (.sib 4 none 0 (.d8 0x67))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[71, 4]
    (.letOp (n := 74) (.out 0x12628c (cmpR32Imm8Effect 0x12628c 3 0 0x2) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[0]
    (.letOp (n := 75) (.exec 0x12628c (fun s => s.RIP = 0x12628c) (cmpR32Imm8Effect 0x12628c 3 0 0x2) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 76) (.pure (condOp 5)) #v[74]
    (.terminate (.condBr (Fin.last 76) ⟨.l126043, RegMap.args [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 57), (6, 61), (7, 63), (8, 71), (9, 59), (10, 10), (11, 11), (13, 13), (15, 15), (19, 74), (22, 22), (39, 39), (50, 50), (51, 51)] 77⟩ ⟨.l126295, RegMap.args [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 57), (6, 61), (7, 63), (8, 71), (9, 59), (10, 10), (11, 11), (13, 13), (15, 15), (19, 74), (22, 22), (39, 39), (50, 50), (51, 51)] 77⟩)))))))))))))))))))))))))

def bytes_l12623d : List UInt8 :=
  [0x8B, 0x54, 0x24, 0x74, 0x48, 0x8B, 0x4C, 0x24, 0x78, 0x48, 0x8B, 0xAC, 0x24, 0x80, 0x00, 0x00,
    0x00, 0x4C, 0x8B, 0x8C, 0x24, 0x88, 0x00, 0x00, 0x00, 0x8B, 0xB4, 0x24, 0x90, 0x00, 0x00, 0x00,
    0x0F, 0xB6, 0xBC, 0x24, 0x94, 0x00, 0x00, 0x00, 0x4C, 0x8B, 0x84, 0x24, 0x95, 0x00, 0x00, 0x00,
    0x4C, 0x89, 0x44, 0x24, 0x58, 0x4C, 0x8B, 0x84, 0x24, 0x9D, 0x00, 0x00, 0x00, 0x4C, 0x89, 0x44,
    0x24, 0x60, 0x44, 0x8B, 0x84, 0x24, 0xA4, 0x00, 0x00, 0x00, 0x44, 0x89, 0x44, 0x24, 0x67, 0x83,
    0xF8, 0x02, 0x0F, 0x85, 0xAE, 0xFD, 0xFF, 0xFF]

theorem code_l12623d : ∀ x ∈ codeRange 0x12623d bytes_l12623d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2623d 88 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126295 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x126295 (StorePre 0x126295 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x126295 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126295 1 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[1, 3]
    (.letOp (n := 54) (.exec 0x126299 (StorePre 0x126299 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x126299 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126299 5 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 5, .gpr 3] [])) #v[5, 3]
    (.letOp (n := 55) (.exec 0x12629d (StorePre 0x12629d 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x12629d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12629d 9 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 9, .gpr 3] [])) #v[9, 3]
    (.letOp (n := 56) (.exec 0x1262a1 (StorePre 0x1262a1 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x1262a1 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x1262a1 15 (.base 3 (.d8 0x20))) (Reg.operands [.gpr 15, .gpr 3] [])) #v[15, 3]
    (.letOp (n := 57) (.exec 0x1262a5 (StorePre 0x1262a5 4 (fun s => AddrMode.addr (.base 3 (.d8 0x24)) s (0x1262a5 + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x1262a5 (.base 3 (.d8 0x24)) 0x0) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 58) (.exec 0x1262a9 (StorePre 0x1262a9 6 (fun s => AddrMode.addr (.base 3 .none) s (0x1262a9 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x1262a9 6 (.base 3 .none) 0x2) (Reg.operands [.gpr 3] [])) #v[3]
    (.terminate (.br ⟨.l125ff4, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l126295 : List UInt8 :=
  [0x48, 0x89, 0x4B, 0x08, 0x48, 0x89, 0x6B, 0x10, 0x4C, 0x89, 0x4B, 0x18, 0x44, 0x89, 0x7B, 0x20,
    0xC6, 0x43, 0x24, 0x00, 0xC7, 0x03, 0x02, 0x00, 0x00, 0x00, 0xE9, 0x40, 0xFD, 0xFF, 0xFF]

theorem code_l126295 : ∀ x ∈ codeRange 0x126295 bytes_l126295, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26295 31 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1262b4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1262b4 (StorePre 0x1262b4 5 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x1262b4 + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x1262b4 (.base 14 (.d8 0x20)) 0x1) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 54) (.out 0x1262b9 (movR64R64Effect 0x1262b9 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2]
    (.letOp (n := 55) (.exec 0x1262b9 (fun s => s.RIP = 0x1262b9) (movR64R64Effect 0x1262b9 1 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 56) (.out 0x1262bc (shlR64Effect 0x1262bc 4 1 32) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[54]
    (.letOp (n := 57) (.exec 0x1262bc (fun s => s.RIP = 0x1262bc) (shlR64Effect 0x1262bc 4 1 32) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[54]
    (.letOp (n := 58) (.out 0x1262c0 (orR64Imm8Effect 0x1262c0 1 0x13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[56]
    (.letOp (n := 59) (.exec 0x1262c0 (fun s => s.RIP = 0x1262c0) (orR64Imm8Effect 0x1262c0 1 0x13) (Reg.operands [.gpr 1] [])) #v[56]
    (.letOp (n := 60) (.out 0x1262c4 (movR32Imm32Effect 0x1262c4 5 0 0x1) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 61) (.exec 0x1262c4 (fun s => s.RIP = 0x1262c4) (movR32Imm32Effect 0x1262c4 5 0 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 62) (.out 0x1262c9 (xorR32R32Effect 0x1262c9 3 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 8] []) (.reg (.gpr 8))) #v[8, 8]
    (.letOp (n := 63) (.exec 0x1262c9 (fun s => s.RIP = 0x1262c9) (xorR32R32Effect 0x1262c9 3 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[8, 8]
    (.terminate (.br ⟨.l126076, RegMap.args [(0, 60), (1, 58), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 62), (9, 9), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩))))))))))))

def bytes_l1262b4 : List UInt8 :=
  [0x41, 0xC6, 0x46, 0x20, 0x01, 0x48, 0x89, 0xD1, 0x48, 0xC1, 0xE1, 0x20, 0x48, 0x83, 0xC9, 0x13,
    0xB8, 0x01, 0x00, 0x00, 0x00, 0x45, 0x31, 0xC0, 0xE9, 0xA5, 0xFD, 0xFF, 0xFF]

theorem code_l1262b4 : ∀ x ∈ codeRange 0x1262b4 bytes_l1262b4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x262b4 29 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1262d1 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1262d1 (xorR32R32Effect 0x1262d1 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[0, 0]
    (.letOp (n := 54) (.exec 0x1262d1 (fun s => s.RIP = 0x1262d1) (xorR32R32Effect 0x1262d1 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.letOp (n := 55) (.out 0x1262d3 (movR32Imm32Effect 0x1262d3 5 1 0xc) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 56) (.exec 0x1262d3 (fun s => s.RIP = 0x1262d3) (movR32Imm32Effect 0x1262d3 5 1 0xc) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x1262d8 (xorR32R32Effect 0x1262d8 3 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 8] []) (.reg (.gpr 8))) #v[8, 8]
    (.letOp (n := 58) (.exec 0x1262d8 (fun s => s.RIP = 0x1262d8) (xorR32R32Effect 0x1262d8 3 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[8, 8]
    (.terminate (.br ⟨.l126076, RegMap.args [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 57), (9, 9), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l1262d1 : List UInt8 :=
  [0x31, 0xC0, 0xB9, 0x0C, 0x00, 0x00, 0x00, 0x45, 0x31, 0xC0, 0xE9, 0x96, 0xFD, 0xFF, 0xFF]

theorem code_l1262d1 : ∀ x ∈ codeRange 0x1262d1 bytes_l1262d1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x262d1 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1262e0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1262e0 (pushR64Effect 0x1262e0 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x1262e0 (PushPre 0x1262e0 1) (pushR64Effect 0x1262e0 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x1262e1 (pushR64Effect 0x1262e1 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x1262e1 (PushPre 0x1262e1 2) (pushR64Effect 0x1262e1 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x1262e3 (pushR64Effect 0x1262e3 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x1262e3 (PushPre 0x1262e3 2) (pushR64Effect 0x1262e3 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x1262e5 (pushR64Effect 0x1262e5 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x1262e5 (PushPre 0x1262e5 2) (pushR64Effect 0x1262e5 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x1262e7 (pushR64Effect 0x1262e7 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x1262e7 (PushPre 0x1262e7 2) (pushR64Effect 0x1262e7 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x1262e9 (pushR64Effect 0x1262e9 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x1262e9 (PushPre 0x1262e9 1) (pushR64Effect 0x1262e9 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x1262ea (subR64Imm32Effect 0x1262ea 4 0xb8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x1262ea (fun s => s.RIP = 0x1262ea) (subR64Imm32Effect 0x1262ea 4 0xb8) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x1262f1 (movR32R32Effect 0x1262f1 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2]
    (.letOp (n := 68) (.exec 0x1262f1 (fun s => s.RIP = 0x1262f1) (movR32R32Effect 0x1262f1 2 1 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 69) (.out 0x1262f3 (movR64R64Effect 0x1262f3 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 6] []) (.reg (.gpr 14))) #v[6]
    (.letOp (n := 70) (.exec 0x1262f3 (fun s => s.RIP = 0x1262f3) (movR64R64Effect 0x1262f3 14 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 71) (.out 0x1262f6 (movR64R64Effect 0x1262f6 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 72) (.exec 0x1262f6 (fun s => s.RIP = 0x1262f6) (movR64R64Effect 0x1262f6 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 73) (.out 0x1262f9 (leaR64Effect 0x1262f9 7 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[65]
    (.letOp (n := 74) (.exec 0x1262f9 (fun s => s.RIP = 0x1262f9) (leaR64Effect 0x1262f9 7 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 75) (.out 0x1262fe (movR32Imm32Effect 0x1262fe 5 2 0x80) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 76) (.exec 0x1262fe (fun s => s.RIP = 0x1262fe) (movR32Imm32Effect 0x1262fe 5 2 0x80) (Reg.operands [] [])) #v[]
    (.letOp (n := 77) (.out 0x126303 (callEffect (fun _ => 0x124290) 0x126308) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 78) (.exec 0x126303 (PushPre 0x126303 5) (callEffect (fun _ => 0x124290) 0x126308) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 79) (.const ⟨64, 0x126308⟩) #v[]
    (.terminate (.call ⟨.l124290, RegMap.args [(1, 67), (2, 75), (3, 71), (4, 77), (5, 5), (6, 6), (7, 73), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 80⟩ { target := .l126308, kept := #v[], arity := rfl, guard := some (Fin.last 79) }))))))))))))))))))))))))))))

def bytes_l1262e0 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0xB8, 0x00, 0x00,
    0x00, 0x89, 0xD1, 0x49, 0x89, 0xF6, 0x48, 0x89, 0xFB, 0x48, 0x8D, 0x7C, 0x24, 0x20, 0xBA, 0x80,
    0x00, 0x00, 0x00, 0xE8, 0x88, 0xDF, 0xFF, 0xFF]

theorem code_l1262e0 : ∀ x ∈ codeRange 0x1262e0 bytes_l1262e0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x262e0 40 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126308 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126308 (movR32M32LowEffect 0x126308 1 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x126308 (LoadPre 0x126308 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x126308 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x126308 1 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x12630c (movzxR32M8Effect 0x12630c 5 0 (.sib 4 none 0 (.d8 0x24))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 56) (.exec 0x12630c (LoadPre 0x12630c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x12630c + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x12630c 5 0 (.sib 4 none 0 (.d8 0x24))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x126311 (cmpR32Imm8Effect 0x126311 3 1 0x2) (EffectPart.reads (.flag .ZF) [.gpr 1] []) (.flag .ZF)) #v[53]
    (.letOp (n := 58) (.exec 0x126311 (fun s => s.RIP = 0x126311) (cmpR32Imm8Effect 0x126311 3 1 0x2) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 59) (.pure (condOp 5)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l1263d9, RegMap.args [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l12631a, RegMap.args [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l126308 : List UInt8 :=
  [0x8B, 0x4C, 0x24, 0x20, 0x0F, 0xB6, 0x44, 0x24, 0x24, 0x83, 0xF9, 0x02, 0x0F, 0x85, 0xBF, 0x00,
    0x00, 0x00]

theorem code_l126308 : ∀ x ∈ codeRange 0x126308 bytes_l126308, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26308 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12631a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12631a (testAlImm8Effect 0x12631a 0x1) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[0]
    (.letOp (n := 54) (.exec 0x12631a (fun s => s.RIP = 0x12631a) (testAlImm8Effect 0x12631a 0x1) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l126420, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l126322, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l12631a : List UInt8 :=
  [0xA8, 0x01, 0x0F, 0x84, 0xFE, 0x00, 0x00, 0x00]

theorem code_l12631a : ∀ x ∈ codeRange 0x12631a bytes_l12631a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2631a 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126322 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126322 (leaR64Effect 0x126322 7 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x126322 (fun s => s.RIP = 0x126322) (leaR64Effect 0x126322 7 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x126327 (movR64R64Effect 0x126327 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 56) (.exec 0x126327 (fun s => s.RIP = 0x126327) (movR64R64Effect 0x126327 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x12632a (callEffect (fun _ => 0x125450) 0x12632f) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x12632a (PushPre 0x12632a 5) (callEffect (fun _ => 0x125450) 0x12632f) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x12632f⟩) #v[]
    (.terminate (.call ⟨.l125450, RegMap.args [(3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ { target := .l12632f, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l126322 : List UInt8 :=
  [0x48, 0x8D, 0x7C, 0x24, 0x20, 0x4C, 0x89, 0xF6, 0xE8, 0x21, 0xF1, 0xFF, 0xFF]

theorem code_l126322 : ∀ x ∈ codeRange 0x126322 bytes_l126322, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26322 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12632f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12632f (movR32M32LowEffect 0x12632f 1 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x12632f (LoadPre 0x12632f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x12632f + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x12632f 1 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x126333 (movzxR32M8Effect 0x126333 5 0 (.sib 4 none 0 (.d8 0x24))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 56) (.exec 0x126333 (LoadPre 0x126333 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x126333 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x126333 5 0 (.sib 4 none 0 (.d8 0x24))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x126338 (movzxR32M8Effect 0x126338 6 11 (.sib 4 none 0 (.d8 0x25))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 58) (.exec 0x126338 (LoadPre 0x126338 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x25)) s (0x126338 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x126338 6 11 (.sib 4 none 0 (.d8 0x25))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x12633e (movzxR32M16Effect 0x12633e 6 10 (.sib 4 none 0 (.d8 0x26))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 60) (.exec 0x12633e (LoadPre 0x12633e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x26)) s (0x12633e + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x12633e 6 10 (.sib 4 none 0 (.d8 0x26))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x126344 (movR32M32Effect 0x126344 13 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 62) (.exec 0x126344 (LoadPre 0x126344 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x126344 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x126344 13 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x126349 (movR32M32LowEffect 0x126349 5 (.sib 4 none 0 (.d8 0x2c))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 64) (.exec 0x126349 (LoadPre 0x126349 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x126349 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x126349 5 (.sib 4 none 0 (.d8 0x2c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x12634d (cmpR32Imm8Effect 0x12634d 3 1 0x2) (EffectPart.reads (.flag .ZF) [.gpr 1] []) (.flag .ZF)) #v[53]
    (.letOp (n := 66) (.exec 0x12634d (fun s => s.RIP = 0x12634d) (cmpR32Imm8Effect 0x12634d 3 1 0x2) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 67) (.pure (condOp 5)) #v[65]
    (.terminate (.condBr (Fin.last 67) ⟨.l12642f, RegMap.args [(0, 55), (1, 53), (3, 3), (4, 4), (5, 63), (6, 6), (7, 7), (8, 8), (9, 9), (10, 59), (11, 57), (13, 61), (14, 14), (15, 15), (19, 65), (22, 22), (39, 39), (50, 50), (51, 51)] 68⟩ ⟨.l126356, RegMap.args [(0, 55), (1, 53), (3, 3), (4, 4), (5, 63), (6, 6), (7, 7), (8, 8), (9, 9), (10, 59), (11, 57), (13, 61), (14, 14), (15, 15), (19, 65), (22, 22), (39, 39), (50, 50), (51, 51)] 68⟩))))))))))))))))

def bytes_l12632f : List UInt8 :=
  [0x8B, 0x4C, 0x24, 0x20, 0x0F, 0xB6, 0x44, 0x24, 0x24, 0x44, 0x0F, 0xB6, 0x5C, 0x24, 0x25, 0x44,
    0x0F, 0xB7, 0x54, 0x24, 0x26, 0x44, 0x8B, 0x6C, 0x24, 0x28, 0x8B, 0x6C, 0x24, 0x2C, 0x83, 0xF9,
    0x02, 0x0F, 0x85, 0xD9, 0x00, 0x00, 0x00]

theorem code_l12632f : ∀ x ∈ codeRange 0x12632f bytes_l12632f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2632f 39 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126356 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126356 (movzxR32R8Effect 0x126356 3 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[0]
    (.letOp (n := 54) (.exec 0x126356 (fun s => s.RIP = 0x126356) (movzxR32R8Effect 0x126356 3 1 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x126359 (leaR32Effect 0x126359 3 2 (.base 1 (.d8 0xea))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[53]
    (.letOp (n := 56) (.exec 0x126359 (fun s => s.RIP = 0x126359) (leaR32Effect 0x126359 3 2 (.base 1 (.d8 0xea))) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 57) (.out 0x12635c (cmpR32Imm8Effect 0x12635c 3 2 0x3) (EffectPart.reads (.flag .CF) [.gpr 2] []) (.flag .CF)) #v[55]
    (.letOp (n := 58) (.exec 0x12635c (fun s => s.RIP = 0x12635c) (cmpR32Imm8Effect 0x12635c 3 2 0x3) (Reg.operands [.gpr 2] [])) #v[55]
    (.letOp (n := 59) (.pure (condOp 3)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l126480, RegMap.args [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (16, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l126365, RegMap.args [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (16, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l126356 : List UInt8 :=
  [0x0F, 0xB6, 0xC8, 0x8D, 0x51, 0xEA, 0x83, 0xFA, 0x03, 0x0F, 0x83, 0x1B, 0x01, 0x00, 0x00]

theorem code_l126356 : ∀ x ∈ codeRange 0x126356 bytes_l126356, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26356 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126365 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126365 (testR8Imm8Effect 0x126365 11 0x1) (EffectPart.reads (.flag .ZF) [.gpr 11] []) (.flag .ZF)) #v[11]
    (.letOp (n := 54) (.exec 0x126365 (fun s => s.RIP = 0x126365) (testR8Imm8Effect 0x126365 11 0x1) (Reg.operands [.gpr 11] [])) #v[11]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l1264c1, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l12636f, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l126365 : List UInt8 :=
  [0x41, 0xF6, 0xC3, 0x01, 0x0F, 0x84, 0x52, 0x01, 0x00, 0x00]

theorem code_l126365 : ∀ x ∈ codeRange 0x126365 bytes_l126365, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26365 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12636f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12636f (cmpAlImm8Effect 0x12636f 0x17) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[0]
    (.letOp (n := 54) (.exec 0x12636f (fun s => s.RIP = 0x12636f) (cmpAlImm8Effect 0x12636f 0x17) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l126488, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l126377, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l12636f : List UInt8 :=
  [0x3C, 0x17, 0x0F, 0x85, 0x11, 0x01, 0x00, 0x00]

theorem code_l12636f : ∀ x ∈ codeRange 0x12636f bytes_l12636f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2636f 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126377 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126377 (movR32M32Effect 0x126377 15 (.base 14 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 14] []) (.reg (.gpr 15))) #v[14]
    (.letOp (n := 54) (.exec 0x126377 (LoadPre 0x126377 (fun s => AddrMode.addr (.base 14 (.d8 0x1c)) s (0x126377 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x126377 15 (.base 14 (.d8 0x1c))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 55) (.out 0x12637b (addR32R32Effect 0x12637b 3 5 15) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 15] []) (.reg (.gpr 5))) #v[5, 53]
    (.letOp (n := 56) (.out 0x12637b (addR32R32Effect 0x12637b 3 5 15) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 15] []) (.flag .CF)) #v[5, 53]
    (.letOp (n := 57) (.exec 0x12637b (fun s => s.RIP = 0x12637b) (addR32R32Effect 0x12637b 3 5 15) (Reg.operands [.gpr 5, .gpr 15] [])) #v[5, 53]
    (.letOp (n := 58) (.pure (condOp 2)) #v[56]
    (.terminate (.condBr (Fin.last 58) ⟨.l1267ac, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 53), (16, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩ ⟨.l126384, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 53), (16, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l126377 : List UInt8 :=
  [0x45, 0x8B, 0x7E, 0x1C, 0x44, 0x01, 0xFD, 0x0F, 0x82, 0x28, 0x04, 0x00, 0x00]

theorem code_l126377 : ∀ x ∈ codeRange 0x126377 bytes_l126377, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26377 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126384 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126384 (movR64M64Effect 0x126384 6 (.base 14 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 54) (.exec 0x126384 (LoadPre 0x126384 (fun s => AddrMode.addr (.base 14 .none) s (0x126384 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x126384 6 (.base 14 .none)) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 55) (.out 0x126387 (movR64M64Effect 0x126387 12 (.base 14 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 14] []) (.reg (.gpr 12))) #v[14]
    (.letOp (n := 56) (.exec 0x126387 (LoadPre 0x126387 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x126387 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x126387 12 (.base 14 (.d8 0x8))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x12638b (leaR64Effect 0x12638b 7 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 58) (.exec 0x12638b (fun s => s.RIP = 0x12638b) (leaR64Effect 0x12638b 7 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.exec 0x126390 (StorePre 0x126390 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x126390 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x126390 6 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 60) (.out 0x126398 (movR64R64Effect 0x126398 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12] []) (.reg (.gpr 2))) #v[55]
    (.letOp (n := 61) (.exec 0x126398 (fun s => s.RIP = 0x126398) (movR64R64Effect 0x126398 2 12) (Reg.operands [.gpr 12] [])) #v[55]
    (.letOp (n := 62) (.out 0x12639b (movR32R32Effect 0x12639b 2 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[5]
    (.letOp (n := 63) (.exec 0x12639b (fun s => s.RIP = 0x12639b) (movR32R32Effect 0x12639b 2 1 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 64) (.out 0x12639d (callEffect (fun _ => 0x127c50) 0x1263a2) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 65) (.exec 0x12639d (PushPre 0x12639d 5) (callEffect (fun _ => 0x127c50) 0x1263a2) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.const ⟨64, 0x1263a2⟩) #v[]
    (.terminate (.call ⟨.l127c50, RegMap.args [(1, 62), (2, 60), (3, 3), (4, 64), (5, 5), (6, 53), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩ { target := .l1263a2, kept := #v[], arity := rfl, guard := some (Fin.last 66) })))))))))))))))

def bytes_l126384 : List UInt8 :=
  [0x49, 0x8B, 0x36, 0x4D, 0x8B, 0x66, 0x08, 0x48, 0x8D, 0x7C, 0x24, 0x20, 0x48, 0x89, 0xB4, 0x24,
    0x80, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xE2, 0x89, 0xE9, 0xE8, 0xAE, 0x18, 0x00, 0x00]

theorem code_l126384 : ∀ x ∈ codeRange 0x126384 bytes_l126384, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26384 30 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1263a2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1263a2 (movR32M32LowEffect 0x1263a2 1 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x1263a2 (LoadPre 0x1263a2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1263a2 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1263a2 1 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1263a6 (cmpR32Imm8Effect 0x1263a6 3 1 0x2) (EffectPart.reads (.flag .ZF) [.gpr 1] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x1263a6 (fun s => s.RIP = 0x1263a6) (cmpR32Imm8Effect 0x1263a6 3 1 0x2) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l126577, RegMap.args [(1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l1263af, RegMap.args [(1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l1263a2 : List UInt8 :=
  [0x8B, 0x4C, 0x24, 0x20, 0x83, 0xF9, 0x02, 0x0F, 0x85, 0xC8, 0x01, 0x00, 0x00]

theorem code_l1263a2 : ∀ x ∈ codeRange 0x1263a2 bytes_l1263a2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x263a2 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1263af : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1263af (movR64M64Effect 0x1263af 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1263af (LoadPre 0x1263af (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1263af + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1263af 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1263b4 (movR64M64Effect 0x1263b4 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x1263b4 (LoadPre 0x1263b4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1263b4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1263b4 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x1263b9 (StorePre 0x1263b9 3 (fun s => AddrMode.addr (.base 14 .none) s (0x1263b9 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x1263b9 0 (.base 14 .none)) (Reg.operands [.gpr 0, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 58) (.exec 0x1263bc (StorePre 0x1263bc 4 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x1263bc + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1263bc 1 (.base 14 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x1263c0 (movR64M64Effect 0x1263c0 0 (.base 14 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[14]
    (.letOp (n := 60) (.exec 0x1263c0 (LoadPre 0x1263c0 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x1263c0 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1263c0 0 (.base 14 (.d8 0x10))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 61) (.out 0x1263c4 (cmpR64Imm8Effect 0x1263c4 0 0x3f) (EffectPart.reads (.flag .CF) [.gpr 0] []) (.flag .CF)) #v[59]
    (.letOp (n := 62) (.out 0x1263c4 (cmpR64Imm8Effect 0x1263c4 0 0x3f) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[59]
    (.letOp (n := 63) (.exec 0x1263c4 (fun s => s.RIP = 0x1263c4) (cmpR64Imm8Effect 0x1263c4 0 0x3f) (Reg.operands [.gpr 0] [])) #v[59]
    (.letOp (n := 64) (.pure (condOp 6)) #v[61, 62]
    (.terminate (.condBr (Fin.last 64) ⟨.l1265d4, RegMap.args [(0, 59), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 61), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)] 65⟩ ⟨.l1263ce, RegMap.args [(0, 59), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 61), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)] 65⟩)))))))))))))

def bytes_l1263af : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x49, 0x89, 0x06, 0x49, 0x89, 0x4E,
    0x08, 0x49, 0x8B, 0x46, 0x10, 0x48, 0x83, 0xF8, 0x3F, 0x0F, 0x86, 0x06, 0x02, 0x00, 0x00]

theorem code_l1263af : ∀ x ∈ codeRange 0x1263af bytes_l1263af, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x263af 31 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1263ce : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1263ce (movR32Imm32Effect 0x1263ce 6 8 0x6) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 54) (.exec 0x1263ce (fun s => s.RIP = 0x1263ce) (movR32Imm32Effect 0x1263ce 6 8 0x6) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l1265f0, RegMap.args [(2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l1263ce : List UInt8 :=
  [0x41, 0xB8, 0x06, 0x00, 0x00, 0x00, 0xE9, 0x17, 0x02, 0x00, 0x00]

theorem code_l1263ce : ∀ x ∈ codeRange 0x1263ce bytes_l1263ce, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x263ce 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1263d9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1263d9 (movR32M32LowEffect 0x1263d9 2 (.sib 4 none 0 (.d8 0x54))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 54) (.exec 0x1263d9 (LoadPre 0x1263d9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x54)) s (0x1263d9 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1263d9 2 (.sib 4 none 0 (.d8 0x54))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x1263dd (StorePre 0x1263dd 3 (fun s => AddrMode.addr (.base 3 (.d8 0x34)) s (0x1263dd + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x1263dd 2 (.base 3 (.d8 0x34))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[53, 3]
    (.letOp (n := 56) (.out 0x1263e0 (movR64M64Effect 0x1263e0 2 (.sib 4 none 0 (.d8 0x4d))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 57) (.exec 0x1263e0 (LoadPre 0x1263e0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4d)) s (0x1263e0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1263e0 2 (.sib 4 none 0 (.d8 0x4d))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x1263e5 (StorePre 0x1263e5 4 (fun s => AddrMode.addr (.base 3 (.d8 0x2d)) s (0x1263e5 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1263e5 2 (.base 3 (.d8 0x2d))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[56, 3]
    (.letOp (n := 59) (.out 0x1263e9 (movR64M64Effect 0x1263e9 2 (.sib 4 none 0 (.d8 0x45))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 60) (.exec 0x1263e9 (LoadPre 0x1263e9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x45)) s (0x1263e9 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1263e9 2 (.sib 4 none 0 (.d8 0x45))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x1263ee (StorePre 0x1263ee 4 (fun s => AddrMode.addr (.base 3 (.d8 0x25)) s (0x1263ee + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1263ee 2 (.base 3 (.d8 0x25))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[59, 3]
    (.letOp (n := 62) (.out 0x1263f2 (movR64M64Effect 0x1263f2 2 (.sib 4 none 0 (.d8 0x3d))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 63) (.exec 0x1263f2 (LoadPre 0x1263f2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3d)) s (0x1263f2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1263f2 2 (.sib 4 none 0 (.d8 0x3d))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x1263f7 (StorePre 0x1263f7 4 (fun s => AddrMode.addr (.base 3 (.d8 0x1d)) s (0x1263f7 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1263f7 2 (.base 3 (.d8 0x1d))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[62, 3]
    (.letOp (n := 65) (.out 0x1263fb (movR64M64Effect 0x1263fb 2 (.sib 4 none 0 (.d8 0x35))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 66) (.exec 0x1263fb (LoadPre 0x1263fb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x35)) s (0x1263fb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1263fb 2 (.sib 4 none 0 (.d8 0x35))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x126400 (StorePre 0x126400 4 (fun s => AddrMode.addr (.base 3 (.d8 0x15)) s (0x126400 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126400 2 (.base 3 (.d8 0x15))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[65, 3]
    (.letOp (n := 68) (.out 0x126404 (movR64M64Effect 0x126404 2 (.sib 4 none 0 (.d8 0x25))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 69) (.exec 0x126404 (LoadPre 0x126404 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x25)) s (0x126404 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126404 2 (.sib 4 none 0 (.d8 0x25))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.out 0x126409 (movR64M64Effect 0x126409 6 (.sib 4 none 0 (.d8 0x2d))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 71) (.exec 0x126409 (LoadPre 0x126409 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2d)) s (0x126409 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126409 6 (.sib 4 none 0 (.d8 0x2d))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.exec 0x12640e (StorePre 0x12640e 4 (fun s => AddrMode.addr (.base 3 (.d8 0xd)) s (0x12640e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12640e 6 (.base 3 (.d8 0xd))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[70, 3]
    (.letOp (n := 73) (.exec 0x126412 (StorePre 0x126412 4 (fun s => AddrMode.addr (.base 3 (.d8 0x5)) s (0x126412 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126412 2 (.base 3 (.d8 0x5))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[68, 3]
    (.letOp (n := 74) (.exec 0x126416 (StorePre 0x126416 2 (fun s => AddrMode.addr (.base 3 .none) s (0x126416 + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x126416 1 (.base 3 .none)) (Reg.operands [.gpr 1, .gpr 3] [])) #v[1, 3]
    (.letOp (n := 75) (.exec 0x126418 (StorePre 0x126418 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x126418 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x126418 3 0 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (.terminate (.br ⟨.l126562, RegMap.args [(0, 0), (1, 1), (2, 68), (3, 3), (4, 4), (6, 70), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 76⟩))))))))))))))))))))))))

def bytes_l1263d9 : List UInt8 :=
  [0x8B, 0x54, 0x24, 0x54, 0x89, 0x53, 0x34, 0x48, 0x8B, 0x54, 0x24, 0x4D, 0x48, 0x89, 0x53, 0x2D,
    0x48, 0x8B, 0x54, 0x24, 0x45, 0x48, 0x89, 0x53, 0x25, 0x48, 0x8B, 0x54, 0x24, 0x3D, 0x48, 0x89,
    0x53, 0x1D, 0x48, 0x8B, 0x54, 0x24, 0x35, 0x48, 0x89, 0x53, 0x15, 0x48, 0x8B, 0x54, 0x24, 0x25,
    0x48, 0x8B, 0x74, 0x24, 0x2D, 0x48, 0x89, 0x73, 0x0D, 0x48, 0x89, 0x53, 0x05, 0x89, 0x0B, 0x88,
    0x43, 0x04, 0xE9, 0x42, 0x01, 0x00, 0x00]

theorem code_l1263d9 : ∀ x ∈ codeRange 0x1263d9 bytes_l1263d9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x263d9 71 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126420 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x126420 (StorePre 0x126420 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x126420 + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x126420 (.base 3 (.d8 0x30)) 0x2) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 54) (.exec 0x126424 (StorePre 0x126424 6 (fun s => AddrMode.addr (.base 3 .none) s (0x126424 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x126424 6 (.base 3 .none) 0x2) (Reg.operands [.gpr 3] [])) #v[3]
    (.terminate (.br ⟨.l126562, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l126420 : List UInt8 :=
  [0xC6, 0x43, 0x30, 0x02, 0xC7, 0x03, 0x02, 0x00, 0x00, 0x00, 0xE9, 0x33, 0x01, 0x00, 0x00]

theorem code_l126420 : ∀ x ∈ codeRange 0x126420 bytes_l126420, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26420 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12642f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12642f (movR32M32Effect 0x12642f 8 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 54) (.exec 0x12642f (LoadPre 0x12642f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x12642f + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x12642f 8 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x126434 (movR64M64Effect 0x126434 2 (.sib 4 none 0 (.d8 0x34))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 56) (.exec 0x126434 (LoadPre 0x126434 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x126434 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126434 2 (.sib 4 none 0 (.d8 0x34))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x126439 (StorePre 0x126439 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x126439 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126439 2 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 58) (.out 0x12643e (movR32M32Effect 0x12643e 14 (.sib 4 none 0 (.d8 0x3c))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 59) (.exec 0x12643e (LoadPre 0x12643e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x12643e + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x12643e 14 (.sib 4 none 0 (.d8 0x3c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.out 0x126443 (movR64M64Effect 0x126443 15 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 61) (.exec 0x126443 (LoadPre 0x126443 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x126443 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126443 15 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.out 0x126448 (movR32M32LowEffect 0x126448 2 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 63) (.exec 0x126448 (LoadPre 0x126448 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x126448 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x126448 2 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x12644c (movR32M32LowEffect 0x12644c 6 (.sib 4 none 0 (.d8 0x4c))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 65) (.exec 0x12644c (LoadPre 0x12644c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4c)) s (0x12644c + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x12644c 6 (.sib 4 none 0 (.d8 0x4c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.out 0x126450 (movzxR32M8Effect 0x126450 5 7 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 67) (.exec 0x126450 (LoadPre 0x126450 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x126450 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x126450 5 7 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.out 0x126455 (movzxR32M16Effect 0x126455 6 9 (.sib 4 none 0 (.d8 0x51))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 69) (.exec 0x126455 (LoadPre 0x126455 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x51)) s (0x126455 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x126455 6 9 (.sib 4 none 0 (.d8 0x51))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.exec 0x12645b (StorePre 0x12645b 5 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x12645b + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x12645b 5 9 (.sib 4 none 0 .none)) (Reg.operands [.gpr 9, .gpr 4] [])) #v[68, 4]
    (.letOp (n := 71) (.out 0x126460 (movzxR32M8Effect 0x126460 6 9 (.sib 4 none 0 (.d8 0x53))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 72) (.exec 0x126460 (LoadPre 0x126460 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x53)) s (0x126460 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x126460 6 9 (.sib 4 none 0 (.d8 0x53))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.exec 0x126466 (StorePre 0x126466 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2)) s (0x126466 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x126466 5 9 (.sib 4 none 0 (.d8 0x2))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[71, 4]
    (.letOp (n := 74) (.out 0x12646b (movR32M32Effect 0x12646b 9 (.sib 4 none 0 (.d8 0x54))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 75) (.exec 0x12646b (LoadPre 0x12646b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x54)) s (0x12646b + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x12646b 9 (.sib 4 none 0 (.d8 0x54))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 76) (.exec 0x126470 (StorePre 0x126470 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x126470 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x126470 13 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[13, 4]
    (.letOp (n := 77) (.exec 0x126475 (StorePre 0x126475 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x126475 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x126475 5 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[5, 4]
    (.letOp (n := 78) (.exec 0x126479 (StorePre 0x126479 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x126479 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x126479 8 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[53, 4]
    (.terminate (.br ⟨.l1264f8, RegMap.args [(0, 0), (1, 1), (2, 62), (3, 3), (4, 4), (5, 5), (6, 64), (7, 66), (8, 53), (9, 74), (10, 10), (11, 11), (13, 13), (14, 58), (15, 60), (22, 22), (39, 39), (50, 50), (51, 51)] 79⟩)))))))))))))))))))))))))))

def bytes_l12642f : List UInt8 :=
  [0x44, 0x8B, 0x44, 0x24, 0x30, 0x48, 0x8B, 0x54, 0x24, 0x34, 0x48, 0x89, 0x54, 0x24, 0x14, 0x44,
    0x8B, 0x74, 0x24, 0x3C, 0x4C, 0x8B, 0x7C, 0x24, 0x40, 0x8B, 0x54, 0x24, 0x48, 0x8B, 0x74, 0x24,
    0x4C, 0x0F, 0xB6, 0x7C, 0x24, 0x50, 0x44, 0x0F, 0xB7, 0x4C, 0x24, 0x51, 0x66, 0x44, 0x89, 0x0C,
    0x24, 0x44, 0x0F, 0xB6, 0x4C, 0x24, 0x53, 0x44, 0x88, 0x4C, 0x24, 0x02, 0x44, 0x8B, 0x4C, 0x24,
    0x54, 0x44, 0x89, 0x6C, 0x24, 0x08, 0x89, 0x6C, 0x24, 0x0C, 0x44, 0x89, 0x44, 0x24, 0x10, 0xEB,
    0x78]

theorem code_l12642f : ∀ x ∈ codeRange 0x12642f bytes_l12642f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2642f 81 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126480 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126480 (addR32Imm8Effect 0x126480 3 1 0xf6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1]
    (.letOp (n := 54) (.exec 0x126480 (fun s => s.RIP = 0x126480) (addR32Imm8Effect 0x126480 3 1 0xf6) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 55) (.out 0x126483 (cmpR32Imm8Effect 0x126483 3 1 0x2) (EffectPart.reads (.flag .CF) [.gpr 1] []) (.flag .CF)) #v[53]
    (.letOp (n := 56) (.exec 0x126483 (fun s => s.RIP = 0x126483) (cmpR32Imm8Effect 0x126483 3 1 0x2) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 3)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l1264c1, RegMap.args [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l126488, RegMap.args [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l126480 : List UInt8 :=
  [0x83, 0xC1, 0xF6, 0x83, 0xF9, 0x02, 0x73, 0x39]

theorem code_l126480 : ∀ x ∈ codeRange 0x126480 bytes_l126480, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26480 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126488 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x126488 (StorePre 0x126488 5 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x126488 + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x126488 (.base 14 (.d8 0x20)) 0x1) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 54) (.out 0x12648d (movR32M32Effect 0x12648d 1 (.base 14 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[14]
    (.letOp (n := 55) (.exec 0x12648d (LoadPre 0x12648d (fun s => AddrMode.addr (.base 14 (.d8 0x1c)) s (0x12648d + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x12648d 1 (.base 14 (.d8 0x1c))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 56) (.exec 0x126491 (StorePre 0x126491 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x126491 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x126491 (.sib 4 none 0 (.d8 0x8)) 0x11) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x126496 (StorePre 0x126496 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x126496 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x126496 (.sib 4 none 0 (.d8 0xc)) 0xff) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x12649b (StorePre 0x12649b 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x12649b + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x12649b 4 0 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[0, 4]
    (.letOp (n := 59) (.exec 0x12649f (StorePre 0x12649f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x15)) s (0x12649f + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x12649f 5 11 (.sib 4 none 0 (.d8 0x15))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[11, 4]
    (.letOp (n := 60) (.exec 0x1264a4 (StorePre 0x1264a4 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x16)) s (0x1264a4 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x1264a4 6 10 (.sib 4 none 0 (.d8 0x16))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[10, 4]
    (.letOp (n := 61) (.out 0x1264aa (movR32R32Effect 0x1264aa 3 10 1) (EffectPart.reads (.reg (.gpr 10)) [.gpr 1] []) (.reg (.gpr 10))) #v[54]
    (.letOp (n := 62) (.exec 0x1264aa (fun s => s.RIP = 0x1264aa) (movR32R32Effect 0x1264aa 3 10 1) (Reg.operands [.gpr 1] [])) #v[54]
    (.letOp (n := 63) (.out 0x1264ad (movR32R32Effect 0x1264ad 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[54]
    (.letOp (n := 64) (.exec 0x1264ad (fun s => s.RIP = 0x1264ad) (movR32R32Effect 0x1264ad 2 0 1) (Reg.operands [.gpr 1] [])) #v[54]
    (.letOp (n := 65) (.out 0x1264af (movR32R32Effect 0x1264af 3 11 1) (EffectPart.reads (.reg (.gpr 11)) [.gpr 1] []) (.reg (.gpr 11))) #v[54]
    (.letOp (n := 66) (.exec 0x1264af (fun s => s.RIP = 0x1264af) (movR32R32Effect 0x1264af 3 11 1) (Reg.operands [.gpr 1] [])) #v[54]
    (.letOp (n := 67) (.out 0x1264b2 (shrR32Effect 0x1264b2 4 11 8) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[65]
    (.letOp (n := 68) (.exec 0x1264b2 (fun s => s.RIP = 0x1264b2) (shrR32Effect 0x1264b2 4 11 8) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[65]
    (.letOp (n := 69) (.out 0x1264b6 (shrR32Effect 0x1264b6 4 10 16) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[61]
    (.letOp (n := 70) (.exec 0x1264b6 (fun s => s.RIP = 0x1264b6) (shrR32Effect 0x1264b6 4 10 16) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[61]
    (.letOp (n := 71) (.exec 0x1264ba (StorePre 0x1264ba 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1264ba + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x1264ba 13 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[13, 4]
    (.terminate (.br ⟨.l1264f3, RegMap.args [(0, 63), (1, 54), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 69), (11, 67), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩))))))))))))))))))))

def bytes_l126488 : List UInt8 :=
  [0x41, 0xC6, 0x46, 0x20, 0x01, 0x41, 0x8B, 0x4E, 0x1C, 0xC6, 0x44, 0x24, 0x08, 0x11, 0xC6, 0x44,
    0x24, 0x0C, 0xFF, 0x88, 0x44, 0x24, 0x14, 0x44, 0x88, 0x5C, 0x24, 0x15, 0x66, 0x44, 0x89, 0x54,
    0x24, 0x16, 0x41, 0x89, 0xCA, 0x89, 0xC8, 0x41, 0x89, 0xCB, 0x41, 0xC1, 0xEB, 0x08, 0x41, 0xC1,
    0xEA, 0x10, 0x44, 0x89, 0x6C, 0x24, 0x18, 0xEB, 0x32]

theorem code_l126488 : ∀ x ∈ codeRange 0x126488 bytes_l126488, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26488 57 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1264c1 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1264c1 (StorePre 0x1264c1 5 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x1264c1 + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x1264c1 (.base 14 (.d8 0x20)) 0x1) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 54) (.out 0x1264c6 (movR32M32Effect 0x1264c6 1 (.base 14 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[14]
    (.letOp (n := 55) (.exec 0x1264c6 (LoadPre 0x1264c6 (fun s => AddrMode.addr (.base 14 (.d8 0x1c)) s (0x1264c6 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x1264c6 1 (.base 14 (.d8 0x1c))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 56) (.exec 0x1264ca (StorePre 0x1264ca 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1264ca + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x1264ca (.sib 4 none 0 (.d8 0x8)) 0x7) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x1264cf (StorePre 0x1264cf 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x1264cf + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1264cf 4 0 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[0, 4]
    (.letOp (n := 58) (.exec 0x1264d3 (StorePre 0x1264d3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xd)) s (0x1264d3 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1264d3 5 11 (.sib 4 none 0 (.d8 0xd))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[11, 4]
    (.letOp (n := 59) (.exec 0x1264d8 (StorePre 0x1264d8 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x1264d8 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x1264d8 6 10 (.sib 4 none 0 (.d8 0xe))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[10, 4]
    (.letOp (n := 60) (.out 0x1264de (movR32R32Effect 0x1264de 3 10 1) (EffectPart.reads (.reg (.gpr 10)) [.gpr 1] []) (.reg (.gpr 10))) #v[54]
    (.letOp (n := 61) (.exec 0x1264de (fun s => s.RIP = 0x1264de) (movR32R32Effect 0x1264de 3 10 1) (Reg.operands [.gpr 1] [])) #v[54]
    (.letOp (n := 62) (.out 0x1264e1 (movR32R32Effect 0x1264e1 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[54]
    (.letOp (n := 63) (.exec 0x1264e1 (fun s => s.RIP = 0x1264e1) (movR32R32Effect 0x1264e1 2 0 1) (Reg.operands [.gpr 1] [])) #v[54]
    (.letOp (n := 64) (.out 0x1264e3 (movR32R32Effect 0x1264e3 3 11 1) (EffectPart.reads (.reg (.gpr 11)) [.gpr 1] []) (.reg (.gpr 11))) #v[54]
    (.letOp (n := 65) (.exec 0x1264e3 (fun s => s.RIP = 0x1264e3) (movR32R32Effect 0x1264e3 3 11 1) (Reg.operands [.gpr 1] [])) #v[54]
    (.letOp (n := 66) (.out 0x1264e6 (shrR32Effect 0x1264e6 4 11 8) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[64]
    (.letOp (n := 67) (.exec 0x1264e6 (fun s => s.RIP = 0x1264e6) (shrR32Effect 0x1264e6 4 11 8) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[64]
    (.letOp (n := 68) (.out 0x1264ea (shrR32Effect 0x1264ea 4 10 16) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[60]
    (.letOp (n := 69) (.exec 0x1264ea (fun s => s.RIP = 0x1264ea) (shrR32Effect 0x1264ea 4 10 16) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[60]
    (.letOp (n := 70) (.exec 0x1264ee (StorePre 0x1264ee 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1264ee + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x1264ee 13 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[13, 4]
    (.terminate (.br ⟨.l1264f3, RegMap.args [(0, 62), (1, 54), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 68), (11, 66), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 71⟩)))))))))))))))))))

def bytes_l1264c1 : List UInt8 :=
  [0x41, 0xC6, 0x46, 0x20, 0x01, 0x41, 0x8B, 0x4E, 0x1C, 0xC6, 0x44, 0x24, 0x08, 0x07, 0x88, 0x44,
    0x24, 0x0C, 0x44, 0x88, 0x5C, 0x24, 0x0D, 0x66, 0x44, 0x89, 0x54, 0x24, 0x0E, 0x41, 0x89, 0xCA,
    0x89, 0xC8, 0x41, 0x89, 0xCB, 0x41, 0xC1, 0xEB, 0x08, 0x41, 0xC1, 0xEA, 0x10, 0x44, 0x89, 0x6C,
    0x24, 0x10]

theorem code_l1264c1 : ∀ x ∈ codeRange 0x1264c1 bytes_l1264c1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x264c1 50 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1264f3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1264f3 (movR32Imm32Effect 0x1264f3 5 1 0x1) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 54) (.exec 0x1264f3 (fun s => s.RIP = 0x1264f3) (movR32Imm32Effect 0x1264f3 5 1 0x1) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l1264f8, RegMap.args [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l1264f3 : List UInt8 :=
  [0xB9, 0x01, 0x00, 0x00, 0x00]

theorem code_l1264f3 : ∀ x ∈ codeRange 0x1264f3 bytes_l1264f3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x264f3 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1264f8_1 : Block Op Label signature Reg.count 82 :=
  .letOp (n := 82) (.exec 0x126547 (StorePre 0x126547 3 (fun s => AddrMode.addr (.base 3 (.d8 0x2c)) s (0x126547 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x126547 6 (.base 3 (.d8 0x2c))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[6, 3]
    (.letOp (n := 83) (.exec 0x12654a (StorePre 0x12654a 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x12654a + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x12654a 4 7 (.base 3 (.d8 0x30))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[7, 3]
    (.letOp (n := 84) (.out 0x12654e (movzxR32M16Effect 0x12654e 4 0 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 85) (.exec 0x12654e (LoadPre 0x12654e (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x12654e + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x12654e 4 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 86) (.exec 0x126552 (StorePre 0x126552 4 (fun s => AddrMode.addr (.base 3 (.d8 0x31)) s (0x126552 + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x126552 4 0 (.base 3 (.d8 0x31))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[84, 3]
    (.letOp (n := 87) (.out 0x126556 (movzxR32M8Effect 0x126556 5 0 (.sib 4 none 0 (.d8 0x2))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 88) (.exec 0x126556 (LoadPre 0x126556 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2)) s (0x126556 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x126556 5 0 (.sib 4 none 0 (.d8 0x2))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 89) (.exec 0x12655b (StorePre 0x12655b 3 (fun s => AddrMode.addr (.base 3 (.d8 0x33)) s (0x12655b + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x12655b 3 0 (.base 3 (.d8 0x33))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[87, 3]
    (.letOp (n := 90) (.exec 0x12655e (StorePre 0x12655e 4 (fun s => AddrMode.addr (.base 3 (.d8 0x34)) s (0x12655e + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x12655e 9 (.base 3 (.d8 0x34))) (Reg.operands [.gpr 9, .gpr 3] [])) #v[9, 3]
    (.terminate (.br ⟨.l126562, RegMap.args [(0, 87), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 65), (9, 9), (10, 68), (11, 70), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 91⟩))))))))))

def bytes_l1264f8_1 : List UInt8 :=
  [0x89, 0x73, 0x2C, 0x40, 0x88, 0x7B, 0x30, 0x0F, 0xB7, 0x04, 0x24, 0x66, 0x89, 0x43, 0x31, 0x0F,
    0xB6, 0x44, 0x24, 0x02, 0x88, 0x43, 0x33, 0x44, 0x89, 0x4B, 0x34]

theorem code_l1264f8_1 : ∀ x ∈ codeRange 0x126547 bytes_l1264f8_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26547 27 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1264f8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1264f8 (shlR32Effect 0x1264f8 4 10 16) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[10]
    (.letOp (n := 54) (.exec 0x1264f8 (fun s => s.RIP = 0x1264f8) (shlR32Effect 0x1264f8 4 10 16) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[10]
    (.letOp (n := 55) (.out 0x1264fc (movzxR32R8Effect 0x1264fc 4 8 11) (EffectPart.reads (.reg (.gpr 8)) [.gpr 11] []) (.reg (.gpr 8))) #v[11]
    (.letOp (n := 56) (.exec 0x1264fc (fun s => s.RIP = 0x1264fc) (movzxR32R8Effect 0x1264fc 4 8 11) (Reg.operands [.gpr 11] [])) #v[11]
    (.letOp (n := 57) (.out 0x126500 (shlR32Effect 0x126500 4 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[55]
    (.letOp (n := 58) (.exec 0x126500 (fun s => s.RIP = 0x126500) (shlR32Effect 0x126500 4 8 8) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[55]
    (.letOp (n := 59) (.out 0x126504 (orR32R32Effect 0x126504 3 8 10) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 10] []) (.reg (.gpr 8))) #v[57, 53]
    (.letOp (n := 60) (.exec 0x126504 (fun s => s.RIP = 0x126504) (orR32R32Effect 0x126504 3 8 10) (Reg.operands [.gpr 8, .gpr 10] [])) #v[57, 53]
    (.letOp (n := 61) (.out 0x126507 (movzxR32R8Effect 0x126507 3 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 62) (.exec 0x126507 (fun s => s.RIP = 0x126507) (movzxR32R8Effect 0x126507 3 0 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 63) (.out 0x12650a (orR32R32Effect 0x12650a 3 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 8] []) (.reg (.gpr 0))) #v[61, 59]
    (.letOp (n := 64) (.exec 0x12650a (fun s => s.RIP = 0x12650a) (orR32R32Effect 0x12650a 3 0 8) (Reg.operands [.gpr 0, .gpr 8] [])) #v[61, 59]
    (.letOp (n := 65) (.out 0x12650d (movR32M32Effect 0x12650d 8 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 66) (.exec 0x12650d (LoadPre 0x12650d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x12650d + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x12650d 8 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x126512 (StorePre 0x126512 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x126512 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x126512 8 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x126517 (movR64M64Effect 0x126517 10 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 69) (.exec 0x126517 (LoadPre 0x126517 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x126517 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126517 10 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.out 0x12651c (movR64M64Effect 0x12651c 11 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 71) (.exec 0x12651c (LoadPre 0x12651c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x12651c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12651c 11 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.exec 0x126521 (StorePre 0x126521 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x126521 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126521 11 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[70, 4]
    (.letOp (n := 73) (.exec 0x126526 (StorePre 0x126526 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x126526 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126526 10 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[68, 4]
    (.letOp (n := 74) (.exec 0x12652b (StorePre 0x12652b 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x12652b + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x12652b 8 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 8, .gpr 3] [])) #v[65, 3]
    (.letOp (n := 75) (.exec 0x12652f (StorePre 0x12652f 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x12652f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12652f 11 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 11, .gpr 3] [])) #v[70, 3]
    (.letOp (n := 76) (.exec 0x126533 (StorePre 0x126533 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x126533 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126533 10 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 10, .gpr 3] [])) #v[68, 3]
    (.letOp (n := 77) (.exec 0x126537 (StorePre 0x126537 2 (fun s => AddrMode.addr (.base 3 .none) s (0x126537 + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x126537 1 (.base 3 .none)) (Reg.operands [.gpr 1, .gpr 3] [])) #v[1, 3]
    (.letOp (n := 78) (.exec 0x126539 (StorePre 0x126539 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x126539 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x126539 0 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[63, 3]
    (.letOp (n := 79) (.exec 0x12653c (StorePre 0x12653c 4 (fun s => AddrMode.addr (.base 3 (.d8 0x1c)) s (0x12653c + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x12653c 14 (.base 3 (.d8 0x1c))) (Reg.operands [.gpr 14, .gpr 3] [])) #v[14, 3]
    (.letOp (n := 80) (.exec 0x126540 (StorePre 0x126540 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x126540 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126540 15 (.base 3 (.d8 0x20))) (Reg.operands [.gpr 15, .gpr 3] [])) #v[15, 3]
    (.letOp (n := 81) (.exec 0x126544 (StorePre 0x126544 3 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x126544 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x126544 2 (.base 3 (.d8 0x28))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[2, 3]
    (b_l1264f8_1)))))))))))))))))))))))))))))

def bytes_l1264f8 : List UInt8 :=
  [0x41, 0xC1, 0xE2, 0x10, 0x45, 0x0F, 0xB6, 0xC3, 0x41, 0xC1, 0xE0, 0x08, 0x45, 0x09, 0xD0, 0x0F,
    0xB6, 0xC0, 0x44, 0x09, 0xC0, 0x44, 0x8B, 0x44, 0x24, 0x18, 0x44, 0x89, 0x44, 0x24, 0x78, 0x4C,
    0x8B, 0x54, 0x24, 0x08, 0x4C, 0x8B, 0x5C, 0x24, 0x10, 0x4C, 0x89, 0x5C, 0x24, 0x70, 0x4C, 0x89,
    0x54, 0x24, 0x68, 0x44, 0x89, 0x43, 0x18, 0x4C, 0x89, 0x5B, 0x10, 0x4C, 0x89, 0x53, 0x08, 0x89,
    0x0B, 0x89, 0x43, 0x04, 0x44, 0x89, 0x73, 0x1C, 0x4C, 0x89, 0x7B, 0x20, 0x89, 0x53, 0x28] ++ bytes_l1264f8_1

theorem code_l1264f8 : ∀ x ∈ codeRange 0x1264f8 bytes_l1264f8, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x264f8 79 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1264f8_1

@[cfg_block] def b_l126562 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126562 (movR64R64Effect 0x126562 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 54) (.exec 0x126562 (fun s => s.RIP = 0x126562) (movR64R64Effect 0x126562 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x126565 (addR64Imm32Effect 0x126565 4 0xb8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 56) (.exec 0x126565 (fun s => s.RIP = 0x126565) (addR64Imm32Effect 0x126565 4 0xb8) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x12656c (popR64Effect 0x12656c 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[55]
    (.letOp (n := 58) (.out 0x12656c (popR64Effect 0x12656c 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[55]
    (.letOp (n := 59) (.exec 0x12656c (PopPre 0x12656c) (popR64Effect 0x12656c 1 3) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 60) (.out 0x12656d (popR64Effect 0x12656d 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[58]
    (.letOp (n := 61) (.out 0x12656d (popR64Effect 0x12656d 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[58]
    (.letOp (n := 62) (.exec 0x12656d (PopPre 0x12656d) (popR64Effect 0x12656d 2 12) (Reg.operands [.gpr 4] [])) #v[58]
    (.letOp (n := 63) (.out 0x12656f (popR64Effect 0x12656f 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[61]
    (.letOp (n := 64) (.out 0x12656f (popR64Effect 0x12656f 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 65) (.exec 0x12656f (PopPre 0x12656f) (popR64Effect 0x12656f 2 13) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 66) (.out 0x126571 (popR64Effect 0x126571 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[64]
    (.letOp (n := 67) (.out 0x126571 (popR64Effect 0x126571 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[64]
    (.letOp (n := 68) (.exec 0x126571 (PopPre 0x126571) (popR64Effect 0x126571 2 14) (Reg.operands [.gpr 4] [])) #v[64]
    (.letOp (n := 69) (.out 0x126573 (popR64Effect 0x126573 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[67]
    (.letOp (n := 70) (.out 0x126573 (popR64Effect 0x126573 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[67]
    (.letOp (n := 71) (.exec 0x126573 (PopPre 0x126573) (popR64Effect 0x126573 2 15) (Reg.operands [.gpr 4] [])) #v[67]
    (.letOp (n := 72) (.out 0x126575 (popR64Effect 0x126575 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[70]
    (.letOp (n := 73) (.out 0x126575 (popR64Effect 0x126575 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[70]
    (.letOp (n := 74) (.exec 0x126575 (PopPre 0x126575) (popR64Effect 0x126575 1 5) (Reg.operands [.gpr 4] [])) #v[70]
    (.letOp (n := 75) (.out 0x126576 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[73]
    (.letOp (n := 76) (.out 0x126576 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[73]
    (.letOp (n := 77) (.exec 0x126576 (RetPre 0x126576) (retEffect) (Reg.operands [.gpr 4] [])) #v[73]
    (.terminate (.ret (RegMap.args [(0, 53), (1, 1), (2, 2), (3, 57), (4, 76), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 78) (some ⟨75, by decide⟩)))))))))))))))))))))))))))

def bytes_l126562 : List UInt8 :=
  [0x48, 0x89, 0xD8, 0x48, 0x81, 0xC4, 0xB8, 0x00, 0x00, 0x00, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41,
    0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l126562 : ∀ x ∈ codeRange 0x126562 bytes_l126562, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26562 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126577 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126577 (movR32M32LowEffect 0x126577 0 (.sib 4 none 0 (.d8 0x24))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x126577 (LoadPre 0x126577 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x126577 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x126577 0 (.sib 4 none 0 (.d8 0x24))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x12657b (movR64M64Effect 0x12657b 8 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 56) (.exec 0x12657b (LoadPre 0x12657b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x12657b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12657b 8 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x126580 (movR64M64Effect 0x126580 11 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 58) (.exec 0x126580 (LoadPre 0x126580 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x126580 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126580 11 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x126585 (movR32M32Effect 0x126585 10 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 60) (.exec 0x126585 (LoadPre 0x126585 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x126585 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x126585 10 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x12658a (movR64M64Effect 0x12658a 2 (.sib 4 none 0 (.d8 0x3c))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 62) (.exec 0x12658a (LoadPre 0x12658a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x12658a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12658a 2 (.sib 4 none 0 (.d8 0x3c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x12658f (StorePre 0x12658f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x12658f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12658f 2 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.out 0x126594 (movR32M32LowEffect 0x126594 2 (.sib 4 none 0 (.d8 0x44))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 65) (.exec 0x126594 (LoadPre 0x126594 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x126594 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x126594 2 (.sib 4 none 0 (.d8 0x44))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x126598 (StorePre 0x126598 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x126598 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x126598 2 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.out 0x12659c (movR32M32LowEffect 0x12659c 2 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 68) (.exec 0x12659c (LoadPre 0x12659c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x12659c + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x12659c 2 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.out 0x1265a0 (movR32M32LowEffect 0x1265a0 6 (.sib 4 none 0 (.d8 0x4c))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 70) (.exec 0x1265a0 (LoadPre 0x1265a0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4c)) s (0x1265a0 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1265a0 6 (.sib 4 none 0 (.d8 0x4c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.out 0x1265a4 (movzxR32M8Effect 0x1265a4 5 7 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 72) (.exec 0x1265a4 (LoadPre 0x1265a4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1265a4 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1265a4 5 7 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.out 0x1265a9 (movzxR32M16Effect 0x1265a9 6 9 (.sib 4 none 0 (.d8 0x51))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 74) (.exec 0x1265a9 (LoadPre 0x1265a9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x51)) s (0x1265a9 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x1265a9 6 9 (.sib 4 none 0 (.d8 0x51))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.exec 0x1265af (StorePre 0x1265af 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x1265af + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x1265af 6 9 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[73, 4]
    (.letOp (n := 76) (.out 0x1265b5 (movzxR32M8Effect 0x1265b5 6 9 (.sib 4 none 0 (.d8 0x53))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 77) (.exec 0x1265b5 (LoadPre 0x1265b5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x53)) s (0x1265b5 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1265b5 6 9 (.sib 4 none 0 (.d8 0x53))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 78) (.exec 0x1265bb (StorePre 0x1265bb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6)) s (0x1265bb + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1265bb 5 9 (.sib 4 none 0 (.d8 0x6))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[76, 4]
    (.letOp (n := 79) (.out 0x1265c0 (movR32M32Effect 0x1265c0 9 (.sib 4 none 0 (.d8 0x54))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 80) (.exec 0x1265c0 (LoadPre 0x1265c0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x54)) s (0x1265c0 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x1265c0 9 (.sib 4 none 0 (.d8 0x54))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 81) (.out 0x1265c5 (movR64Imm64Effect 0x1265c5 14 0xffffffff00000000) (EffectPart.reads (.reg (.gpr 14)) [] []) (.reg (.gpr 14))) #v[]
    (.letOp (n := 82) (.exec 0x1265c5 (fun s => s.RIP = 0x1265c5) (movR64Imm64Effect 0x1265c5 14 0xffffffff00000000) (Reg.operands [] [])) #v[]
    (.letOp (n := 83) (.out 0x1265cf (andR64R64Effect 0x1265cf 14 11) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 11] []) (.reg (.gpr 14))) #v[81, 57]
    (.letOp (n := 84) (.exec 0x1265cf (fun s => s.RIP = 0x1265cf) (andR64R64Effect 0x1265cf 14 11) (Reg.operands [.gpr 14, .gpr 11] [])) #v[81, 57]
    (.terminate (.br ⟨.l1265fe, RegMap.args [(0, 53), (1, 1), (2, 67), (3, 3), (4, 4), (6, 69), (7, 71), (8, 55), (9, 79), (10, 59), (11, 57), (14, 83), (22, 22), (39, 39), (50, 50), (51, 51)] 85⟩)))))))))))))))))))))))))))))))))

def bytes_l126577 : List UInt8 :=
  [0x8B, 0x44, 0x24, 0x24, 0x4C, 0x8B, 0x44, 0x24, 0x28, 0x4C, 0x8B, 0x5C, 0x24, 0x30, 0x44, 0x8B,
    0x54, 0x24, 0x38, 0x48, 0x8B, 0x54, 0x24, 0x3C, 0x48, 0x89, 0x54, 0x24, 0x58, 0x8B, 0x54, 0x24,
    0x44, 0x89, 0x54, 0x24, 0x60, 0x8B, 0x54, 0x24, 0x48, 0x8B, 0x74, 0x24, 0x4C, 0x0F, 0xB6, 0x7C,
    0x24, 0x50, 0x44, 0x0F, 0xB7, 0x4C, 0x24, 0x51, 0x66, 0x44, 0x89, 0x4C, 0x24, 0x04, 0x44, 0x0F,
    0xB6, 0x4C, 0x24, 0x53, 0x44, 0x88, 0x4C, 0x24, 0x06, 0x44, 0x8B, 0x4C, 0x24, 0x54, 0x49, 0xBE,
    0x00, 0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF, 0x4D, 0x21, 0xDE, 0xEB, 0x2A]

theorem code_l126577 : ∀ x ∈ codeRange 0x126577 bytes_l126577, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26577 93 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1265d4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1265d4 (incR64Effect 0x1265d4 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 54) (.exec 0x1265d4 (fun s => s.RIP = 0x1265d4) (incR64Effect 0x1265d4 0) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[0]
    (.letOp (n := 55) (.exec 0x1265d7 (StorePre 0x1265d7 4 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x1265d7 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1265d7 0 (.base 14 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 56) (.out 0x1265db (movR32M32Effect 0x1265db 15 (.base 14 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 14] []) (.reg (.gpr 15))) #v[14]
    (.letOp (n := 57) (.exec 0x1265db (LoadPre 0x1265db (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x1265db + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x1265db 15 (.base 14 (.d8 0x18))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 58) (.out 0x1265df (cmpR32R32Effect 0x1265df 3 5 15) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 15] []) (.flag .CF)) #v[5, 56]
    (.letOp (n := 59) (.out 0x1265df (cmpR32R32Effect 0x1265df 3 5 15) (EffectPart.reads (.flag .ZF) [.gpr 5, .gpr 15] []) (.flag .ZF)) #v[5, 56]
    (.letOp (n := 60) (.exec 0x1265df (fun s => s.RIP = 0x1265df) (cmpR32R32Effect 0x1265df 3 5 15) (Reg.operands [.gpr 5, .gpr 15] [])) #v[5, 56]
    (.letOp (n := 61) (.pure (condOp 6)) #v[58, 59]
    (.terminate (.condBr (Fin.last 61) ⟨.l126663, RegMap.args [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 56), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ ⟨.l1265e4, RegMap.args [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 56), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩))))))))))

def bytes_l1265d4 : List UInt8 :=
  [0x48, 0xFF, 0xC0, 0x49, 0x89, 0x46, 0x10, 0x45, 0x8B, 0x7E, 0x18, 0x44, 0x39, 0xFD, 0x76, 0x7F]

theorem code_l1265d4 : ∀ x ∈ codeRange 0x1265d4 bytes_l1265d4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x265d4 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1265e4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1265e4 (leaR32Effect 0x1265e4 4 8 (.base 15 (.d8 0x1))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 15] []) (.reg (.gpr 8))) #v[15]
    (.letOp (n := 54) (.exec 0x1265e4 (fun s => s.RIP = 0x1265e4) (leaR32Effect 0x1265e4 4 8 (.base 15 (.d8 0x1))) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.out 0x1265e8 (shlR64Effect 0x1265e8 4 8 32) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[53]
    (.letOp (n := 56) (.exec 0x1265e8 (fun s => s.RIP = 0x1265e8) (shlR64Effect 0x1265e8 4 8 32) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 57) (.out 0x1265ec (orR64Imm8Effect 0x1265ec 8 0x3) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[55]
    (.letOp (n := 58) (.exec 0x1265ec (fun s => s.RIP = 0x1265ec) (orR64Imm8Effect 0x1265ec 8 0x3) (Reg.operands [.gpr 8] [])) #v[55]
    (.terminate (.br ⟨.l1265f0, RegMap.args [(2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 57), (9, 9), (10, 10), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l1265e4 : List UInt8 :=
  [0x45, 0x8D, 0x47, 0x01, 0x49, 0xC1, 0xE0, 0x20, 0x49, 0x83, 0xC8, 0x03]

theorem code_l1265e4 : ∀ x ∈ codeRange 0x1265e4 bytes_l1265e4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x265e4 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1265f0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1265f0 (movR32Imm32Effect 0x1265f0 5 1 0x1) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 54) (.exec 0x1265f0 (fun s => s.RIP = 0x1265f0) (movR32Imm32Effect 0x1265f0 5 1 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x1265f5 (xorR32R32Effect 0x1265f5 3 14 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 14] []) (.reg (.gpr 14))) #v[14, 14]
    (.letOp (n := 56) (.exec 0x1265f5 (fun s => s.RIP = 0x1265f5) (xorR32R32Effect 0x1265f5 3 14 14) (Reg.operands [.gpr 14, .gpr 14] [])) #v[14, 14]
    (.letOp (n := 57) (.out 0x1265f8 (movR32R32Effect 0x1265f8 3 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[15]
    (.letOp (n := 58) (.exec 0x1265f8 (fun s => s.RIP = 0x1265f8) (movR32R32Effect 0x1265f8 3 0 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 59) (.out 0x1265fb (movR32R32Effect 0x1265fb 3 11 15) (EffectPart.reads (.reg (.gpr 11)) [.gpr 15] []) (.reg (.gpr 11))) #v[15]
    (.letOp (n := 60) (.exec 0x1265fb (fun s => s.RIP = 0x1265fb) (movR32R32Effect 0x1265fb 3 11 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.terminate (.br ⟨.l1265fe, RegMap.args [(0, 57), (1, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 59), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩)))))))))

def bytes_l1265f0 : List UInt8 :=
  [0xB9, 0x01, 0x00, 0x00, 0x00, 0x45, 0x31, 0xF6, 0x44, 0x89, 0xF8, 0x45, 0x89, 0xFB]

theorem code_l1265f0 : ∀ x ∈ codeRange 0x1265f0 bytes_l1265f0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x265f0 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1265fe : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1265fe (movR32R32Effect 0x1265fe 3 12 11) (EffectPart.reads (.reg (.gpr 12)) [.gpr 11] []) (.reg (.gpr 12))) #v[11]
    (.letOp (n := 54) (.exec 0x1265fe (fun s => s.RIP = 0x1265fe) (movR32R32Effect 0x1265fe 3 12 11) (Reg.operands [.gpr 11] [])) #v[11]
    (.letOp (n := 55) (.out 0x126601 (orR64R64Effect 0x126601 12 14) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 14] []) (.reg (.gpr 12))) #v[53, 14]
    (.letOp (n := 56) (.exec 0x126601 (fun s => s.RIP = 0x126601) (orR64R64Effect 0x126601 12 14) (Reg.operands [.gpr 12, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 57) (.out 0x126604 (movR32M32Effect 0x126604 11 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 58) (.exec 0x126604 (LoadPre 0x126604 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x126604 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x126604 11 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.exec 0x126609 (StorePre 0x126609 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x126609 + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x126609 11 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 60) (.out 0x126611 (movR64M64Effect 0x126611 14 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 61) (.exec 0x126611 (LoadPre 0x126611 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x126611 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126611 14 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.out 0x126616 (movzxR32M16Effect 0x126616 5 5 (.sib 4 none 0 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 63) (.exec 0x126616 (LoadPre 0x126616 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x126616 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x126616 5 5 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x12661b (StorePre 0x12661b 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x12661b + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x12661b 4 5 (.sib 4 none 0 .none)) (Reg.operands [.gpr 5, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x12661f (movzxR32M8Effect 0x12661f 5 5 (.sib 4 none 0 (.d8 0x6))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 66) (.exec 0x12661f (LoadPre 0x12661f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6)) s (0x12661f + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x12661f 5 5 (.sib 4 none 0 (.d8 0x6))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x126624 (StorePre 0x126624 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2)) s (0x126624 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x126624 5 5 (.sib 4 none 0 (.d8 0x2))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.exec 0x126629 (StorePre 0x126629 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x126629 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x126629 14 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[60, 4]
    (.letOp (n := 69) (.exec 0x126631 (StorePre 0x126631 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x126631 + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x126631 11 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 70) (.exec 0x126639 (StorePre 0x126639 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x126639 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x126639 10 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[10, 4]
    (.letOp (n := 71) (.out 0x12663e (movR64M64Effect 0x12663e 15 (.sib 4 none 0 (.d32 0x8c))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 72) (.exec 0x12663e (LoadPre 0x12663e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x8c)) s (0x12663e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x12663e 15 (.sib 4 none 0 (.d32 0x8c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.out 0x126646 (movR32R32Effect 0x126646 3 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[0]
    (.letOp (n := 74) (.exec 0x126646 (fun s => s.RIP = 0x126646) (movR32R32Effect 0x126646 3 11 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 75) (.out 0x126649 (shrR32Effect 0x126649 4 11 8) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[73]
    (.letOp (n := 76) (.exec 0x126649 (fun s => s.RIP = 0x126649) (shrR32Effect 0x126649 4 11 8) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[73]
    (.letOp (n := 77) (.out 0x12664d (movR32R32Effect 0x12664d 3 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[0]
    (.letOp (n := 78) (.exec 0x12664d (fun s => s.RIP = 0x12664d) (movR32R32Effect 0x12664d 3 10 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 79) (.out 0x126650 (shrR32Effect 0x126650 4 10 16) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[77]
    (.letOp (n := 80) (.exec 0x126650 (fun s => s.RIP = 0x126650) (shrR32Effect 0x126650 4 10 16) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[77]
    (.letOp (n := 81) (.exec 0x126654 (StorePre 0x126654 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x126654 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126654 8 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[8, 4]
    (.letOp (n := 82) (.exec 0x126659 (StorePre 0x126659 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x126659 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126659 12 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[55, 4]
    (.terminate (.br ⟨.l1264f8, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 65), (6, 6), (7, 7), (8, 8), (9, 9), (10, 79), (11, 75), (12, 55), (14, 60), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)] 83⟩)))))))))))))))))))))))))))))))

def bytes_l1265fe : List UInt8 :=
  [0x45, 0x89, 0xDC, 0x4D, 0x09, 0xF4, 0x44, 0x8B, 0x5C, 0x24, 0x60, 0x44, 0x89, 0x9C, 0x24, 0xA0,
    0x00, 0x00, 0x00, 0x4C, 0x8B, 0x74, 0x24, 0x58, 0x0F, 0xB7, 0x6C, 0x24, 0x04, 0x66, 0x89, 0x2C,
    0x24, 0x0F, 0xB6, 0x6C, 0x24, 0x06, 0x40, 0x88, 0x6C, 0x24, 0x02, 0x4C, 0x89, 0xB4, 0x24, 0x88,
    0x00, 0x00, 0x00, 0x44, 0x89, 0x9C, 0x24, 0x90, 0x00, 0x00, 0x00, 0x44, 0x89, 0x54, 0x24, 0x18,
    0x4C, 0x8B, 0xBC, 0x24, 0x8C, 0x00, 0x00, 0x00, 0x41, 0x89, 0xC3, 0x41, 0xC1, 0xEB, 0x08, 0x41,
    0x89, 0xC2, 0x41, 0xC1, 0xEA, 0x10, 0x4C, 0x89, 0x44, 0x24, 0x08, 0x4C, 0x89, 0x64, 0x24, 0x10,
    0xE9, 0x95, 0xFE, 0xFF, 0xFF]

theorem code_l1265fe : ∀ x ∈ codeRange 0x1265fe bytes_l1265fe, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x265fe 101 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126663 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x126663 (StorePre 0x126663 4 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x126663 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x126663 5 (.base 14 (.d8 0x18))) (Reg.operands [.gpr 5, .gpr 14] [])) #v[5, 14]
    (.letOp (n := 54) (.out 0x126667 (leaR64Effect 0x126667 7 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 55) (.exec 0x126667 (fun s => s.RIP = 0x126667) (leaR64Effect 0x126667 7 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x12666c (movR64R64Effect 0x12666c 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 57) (.exec 0x12666c (fun s => s.RIP = 0x12666c) (movR64R64Effect 0x12666c 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 58) (.out 0x12666f (callEffect (fun _ => 0x124ae0) 0x126674) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 59) (.exec 0x12666f (PushPre 0x12666f 5) (callEffect (fun _ => 0x124ae0) 0x126674) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.const ⟨64, 0x126674⟩) #v[]
    (.terminate (.call ⟨.l124ae0, RegMap.args [(3, 3), (4, 58), (5, 5), (6, 56), (7, 54), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩ { target := .l126674, kept := #v[], arity := rfl, guard := some (Fin.last 60) })))))))))

def bytes_l126663 : List UInt8 :=
  [0x41, 0x89, 0x6E, 0x18, 0x48, 0x8D, 0x7C, 0x24, 0x20, 0x4C, 0x89, 0xF6, 0xE8, 0x6C, 0xE4, 0xFF,
    0xFF]

theorem code_l126663 : ∀ x ∈ codeRange 0x126663 bytes_l126663, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26663 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126674 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126674 (movR32M32Effect 0x126674 11 (.base 14 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 14] []) (.reg (.gpr 11))) #v[14]
    (.letOp (n := 54) (.exec 0x126674 (LoadPre 0x126674 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x126674 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x126674 11 (.base 14 (.d8 0x18))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 55) (.out 0x126678 (movR32M32Effect 0x126678 0 (.base 14 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[14]
    (.letOp (n := 56) (.exec 0x126678 (LoadPre 0x126678 (fun s => AddrMode.addr (.base 14 (.d8 0x1c)) s (0x126678 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x126678 0 (.base 14 (.d8 0x1c))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x12667c (subR32R32Effect 0x12667c 3 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0] []) (.reg (.gpr 11))) #v[53, 55]
    (.letOp (n := 58) (.out 0x12667c (subR32R32Effect 0x12667c 3 11 0) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 0] []) (.flag .CF)) #v[53, 55]
    (.letOp (n := 59) (.out 0x12667c (subR32R32Effect 0x12667c 3 11 0) (EffectPart.reads (.flag .ZF) [.gpr 11, .gpr 0] []) (.flag .ZF)) #v[53, 55]
    (.letOp (n := 60) (.exec 0x12667c (fun s => s.RIP = 0x12667c) (subR32R32Effect 0x12667c 3 11 0) (Reg.operands [.gpr 11, .gpr 0] [])) #v[53, 55]
    (.letOp (n := 61) (.out 0x12667f (atFlags (condHolds 6) (setccR8Effect 0x12667f 3 2)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF]) (.reg (.gpr 2))) #v[2, 58, 59]
    (.letOp (n := 62) (.exec 0x12667f (fun s => s.RIP = 0x12667f) (atFlags (condHolds 6) (setccR8Effect 0x12667f 3 2)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF])) #v[2, 58, 59]
    (.letOp (n := 63) (.out 0x126682 (movR64M64Effect 0x126682 1 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 64) (.exec 0x126682 (LoadPre 0x126682 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x126682 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x126682 1 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.exec 0x12668a (StorePre 0x12668a 3 (fun s => AddrMode.addr (.base 14 .none) s (0x12668a + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x12668a 1 (.base 14 .none)) (Reg.operands [.gpr 1, .gpr 14] [])) #v[63, 14]
    (.letOp (n := 66) (.exec 0x12668d (StorePre 0x12668d 4 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x12668d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12668d 12 (.base 14 (.d8 0x8))) (Reg.operands [.gpr 12, .gpr 14] [])) #v[12, 14]
    (.letOp (n := 67) (.exec 0x126691 (StorePre 0x126691 4 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x126691 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x126691 15 (.base 14 (.d8 0x18))) (Reg.operands [.gpr 15, .gpr 14] [])) #v[15, 14]
    (.letOp (n := 68) (.out 0x126695 (movR64M64Effect 0x126695 1 (.base 14 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[14]
    (.letOp (n := 69) (.exec 0x126695 (LoadPre 0x126695 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x126695 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x126695 1 (.base 14 (.d8 0x10))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 70) (.out 0x126699 (cmpR64Imm8Effect 0x126699 1 0x1) (EffectPart.reads (.flag .CF) [.gpr 1] []) (.flag .CF)) #v[68]
    (.letOp (n := 71) (.exec 0x126699 (fun s => s.RIP = 0x126699) (cmpR64Imm8Effect 0x126699 1 0x1) (Reg.operands [.gpr 1] [])) #v[68]
    (.letOp (n := 72) (.out 0x12669d (atFlags StatusFlags.CF (adcR64Imm8Effect 0x12669d 1 0xff)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[68, 70]
    (.letOp (n := 73) (.exec 0x12669d (fun s => s.RIP = 0x12669d) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x12669d 1 0xff)) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[68, 70]
    (.letOp (n := 74) (.exec 0x1266a1 (StorePre 0x1266a1 4 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x1266a1 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1266a1 1 (.base 14 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 14] [])) #v[72, 14]
    (.letOp (n := 75) (.out 0x1266a5 (movR32M32LowEffect 0x1266a5 1 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 76) (.exec 0x1266a5 (LoadPre 0x1266a5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1266a5 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1266a5 1 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 77) (.out 0x1266a9 (cmpR32Imm8Effect 0x1266a9 3 1 0x2) (EffectPart.reads (.flag .ZF) [.gpr 1] []) (.flag .ZF)) #v[75]
    (.letOp (n := 78) (.exec 0x1266a9 (fun s => s.RIP = 0x1266a9) (cmpR32Imm8Effect 0x1266a9 3 1 0x2) (Reg.operands [.gpr 1] [])) #v[75]
    (.letOp (n := 79) (.out 0x1266ac (atFlags (condHolds 5) (setccR8Effect 0x1266ac 4 6)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 6))) #v[6, 77]
    (.letOp (n := 80) (.exec 0x1266ac (fun s => s.RIP = 0x1266ac) (atFlags (condHolds 5) (setccR8Effect 0x1266ac 4 6)) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[6, 77]
    (.letOp (n := 81) (.out 0x1266b0 (orR8R8Effect 0x1266b0 3 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[79, 61]
    (.letOp (n := 82) (.out 0x1266b0 (orR8R8Effect 0x1266b0 3 6 2) (EffectPart.reads (.flag .ZF) [.gpr 6, .gpr 2] []) (.flag .ZF)) #v[79, 61]
    (.letOp (n := 83) (.exec 0x1266b0 (fun s => s.RIP = 0x1266b0) (orR8R8Effect 0x1266b0 3 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[79, 61]
    (.letOp (n := 84) (.pure (condOp 4)) #v[82]
    (.terminate (.condBr (Fin.last 84) ⟨.l126778, RegMap.args [(0, 55), (1, 75), (2, 61), (3, 3), (4, 4), (6, 81), (7, 7), (9, 9), (10, 10), (11, 57), (12, 12), (13, 13), (14, 14), (15, 15), (19, 82), (22, 22), (39, 39), (50, 50), (51, 51)] 85⟩ ⟨.l1266b9, RegMap.args [(0, 55), (1, 75), (2, 61), (3, 3), (4, 4), (6, 81), (7, 7), (9, 9), (10, 10), (11, 57), (12, 12), (13, 13), (14, 14), (15, 15), (19, 82), (22, 22), (39, 39), (50, 50), (51, 51)] 85⟩)))))))))))))))))))))))))))))))))

def bytes_l126674 : List UInt8 :=
  [0x45, 0x8B, 0x5E, 0x18, 0x41, 0x8B, 0x46, 0x1C, 0x41, 0x29, 0xC3, 0x0F, 0x96, 0xC2, 0x48, 0x8B,
    0x8C, 0x24, 0x80, 0x00, 0x00, 0x00, 0x49, 0x89, 0x0E, 0x4D, 0x89, 0x66, 0x08, 0x45, 0x89, 0x7E,
    0x18, 0x49, 0x8B, 0x4E, 0x10, 0x48, 0x83, 0xF9, 0x01, 0x48, 0x83, 0xD1, 0xFF, 0x49, 0x89, 0x4E,
    0x10, 0x8B, 0x4C, 0x24, 0x20, 0x83, 0xF9, 0x02, 0x40, 0x0F, 0x95, 0xC6, 0x40, 0x08, 0xD6, 0x0F,
    0x84, 0xBF, 0x00, 0x00, 0x00]

theorem code_l126674 : ∀ x ∈ codeRange 0x126674 bytes_l126674, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26674 69 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1266b9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1266b9 (movR32M32LowEffect 0x1266b9 0 (.sib 4 none 0 (.d8 0x24))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1266b9 (LoadPre 0x1266b9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x1266b9 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1266b9 0 (.sib 4 none 0 (.d8 0x24))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1266bd (movR64M64Effect 0x1266bd 8 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 56) (.exec 0x1266bd (LoadPre 0x1266bd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1266bd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1266bd 8 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1266c2 (movR64M64Effect 0x1266c2 11 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 58) (.exec 0x1266c2 (LoadPre 0x1266c2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1266c2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1266c2 11 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x1266c7 (movR32M32Effect 0x1266c7 10 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 60) (.exec 0x1266c7 (LoadPre 0x1266c7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1266c7 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x1266c7 10 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x1266cc (movR64M64Effect 0x1266cc 2 (.sib 4 none 0 (.d8 0x3c))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 62) (.exec 0x1266cc (LoadPre 0x1266cc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x1266cc + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1266cc 2 (.sib 4 none 0 (.d8 0x3c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x1266d1 (StorePre 0x1266d1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1266d1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1266d1 2 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.out 0x1266d6 (movR32M32LowEffect 0x1266d6 2 (.sib 4 none 0 (.d8 0x44))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 65) (.exec 0x1266d6 (LoadPre 0x1266d6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x1266d6 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1266d6 2 (.sib 4 none 0 (.d8 0x44))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x1266da (StorePre 0x1266da 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1266da + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x1266da 2 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.out 0x1266de (movR32M32LowEffect 0x1266de 2 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 68) (.exec 0x1266de (LoadPre 0x1266de (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1266de + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1266de 2 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.out 0x1266e2 (movR32M32LowEffect 0x1266e2 6 (.sib 4 none 0 (.d8 0x4c))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 70) (.exec 0x1266e2 (LoadPre 0x1266e2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4c)) s (0x1266e2 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1266e2 6 (.sib 4 none 0 (.d8 0x4c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.out 0x1266e6 (movzxR32M8Effect 0x1266e6 5 7 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 72) (.exec 0x1266e6 (LoadPre 0x1266e6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1266e6 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1266e6 5 7 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.out 0x1266eb (movzxR32M16Effect 0x1266eb 6 9 (.sib 4 none 0 (.d8 0x51))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 74) (.exec 0x1266eb (LoadPre 0x1266eb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x51)) s (0x1266eb + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x1266eb 6 9 (.sib 4 none 0 (.d8 0x51))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.exec 0x1266f1 (StorePre 0x1266f1 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x1266f1 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x1266f1 6 9 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[73, 4]
    (.letOp (n := 76) (.out 0x1266f7 (movzxR32M8Effect 0x1266f7 6 9 (.sib 4 none 0 (.d8 0x53))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 77) (.exec 0x1266f7 (LoadPre 0x1266f7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x53)) s (0x1266f7 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1266f7 6 9 (.sib 4 none 0 (.d8 0x53))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 78) (.exec 0x1266fd (StorePre 0x1266fd 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6)) s (0x1266fd + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1266fd 5 9 (.sib 4 none 0 (.d8 0x6))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[76, 4]
    (.letOp (n := 79) (.out 0x126702 (cmpR32Imm8Effect 0x126702 3 1 0x2) (EffectPart.reads (.flag .ZF) [.gpr 1] []) (.flag .ZF)) #v[1]
    (.letOp (n := 80) (.exec 0x126702 (fun s => s.RIP = 0x126702) (cmpR32Imm8Effect 0x126702 3 1 0x2) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 81) (.pure (condOp 5)) #v[79]
    (.terminate (.condBr (Fin.last 81) ⟨.l126795, RegMap.args [(0, 53), (1, 1), (2, 67), (3, 3), (4, 4), (6, 69), (7, 71), (8, 55), (9, 76), (10, 59), (11, 57), (13, 13), (19, 79), (22, 22), (39, 39), (50, 50), (51, 51)] 82⟩ ⟨.l12670b, RegMap.args [(0, 53), (1, 1), (2, 67), (3, 3), (4, 4), (6, 69), (7, 71), (8, 55), (9, 76), (10, 59), (11, 57), (13, 13), (19, 79), (22, 22), (39, 39), (50, 50), (51, 51)] 82⟩))))))))))))))))))))))))))))))

def bytes_l1266b9 : List UInt8 :=
  [0x8B, 0x44, 0x24, 0x24, 0x4C, 0x8B, 0x44, 0x24, 0x28, 0x4C, 0x8B, 0x5C, 0x24, 0x30, 0x44, 0x8B,
    0x54, 0x24, 0x38, 0x48, 0x8B, 0x54, 0x24, 0x3C, 0x48, 0x89, 0x54, 0x24, 0x58, 0x8B, 0x54, 0x24,
    0x44, 0x89, 0x54, 0x24, 0x60, 0x8B, 0x54, 0x24, 0x48, 0x8B, 0x74, 0x24, 0x4C, 0x0F, 0xB6, 0x7C,
    0x24, 0x50, 0x44, 0x0F, 0xB7, 0x4C, 0x24, 0x51, 0x66, 0x44, 0x89, 0x4C, 0x24, 0x04, 0x44, 0x0F,
    0xB6, 0x4C, 0x24, 0x53, 0x44, 0x88, 0x4C, 0x24, 0x06, 0x83, 0xF9, 0x02, 0x0F, 0x85, 0x8A, 0x00,
    0x00, 0x00]

theorem code_l1266b9 : ∀ x ∈ codeRange 0x1266b9 bytes_l1266b9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x266b9 82 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12670b_1 : Block Op Label signature Reg.count 81 :=
  .letOp (n := 81) (.exec 0x126763 (StorePre 0x126763 3 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x126763 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x126763 1 (.base 3 (.d8 0x28))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[53, 3]
    (.letOp (n := 82) (.exec 0x126766 (StorePre 0x126766 3 (fun s => AddrMode.addr (.base 3 (.d8 0x2c)) s (0x126766 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x126766 2 (.base 3 (.d8 0x2c))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[2, 3]
    (.letOp (n := 83) (.exec 0x126769 (StorePre 0x126769 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x126769 + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x126769 (.base 3 (.d8 0x30)) 0x0) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 84) (.exec 0x12676d (StorePre 0x12676d 6 (fun s => AddrMode.addr (.base 3 .none) s (0x12676d + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x12676d 6 (.base 3 .none) 0x2) (Reg.operands [.gpr 3] [])) #v[3]
    (.terminate (.br ⟨.l126562, RegMap.args [(0, 72), (1, 53), (2, 2), (3, 3), (4, 4), (6, 55), (7, 74), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)] 85⟩)))))

def bytes_l12670b_1 : List UInt8 :=
  [0x89, 0x4B, 0x28, 0x89, 0x53, 0x2C, 0xC6, 0x43, 0x30, 0x00, 0xC7, 0x03, 0x02, 0x00, 0x00, 0x00,
    0xE9, 0xEA, 0xFD, 0xFF, 0xFF]

theorem code_l12670b_1 : ∀ x ∈ codeRange 0x126763 bytes_l12670b_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26763 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12670b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12670b (movR32M32LowEffect 0x12670b 1 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x12670b (LoadPre 0x12670b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x12670b + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x12670b 1 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x12670f (movR64M64Effect 0x12670f 6 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 56) (.exec 0x12670f (LoadPre 0x12670f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x12670f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12670f 6 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x126714 (StorePre 0x126714 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x126714 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x126714 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[0, 4]
    (.letOp (n := 58) (.exec 0x126718 (StorePre 0x126718 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x126718 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126718 8 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[8, 4]
    (.letOp (n := 59) (.exec 0x12671d (StorePre 0x12671d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x12671d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12671d 11 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[11, 4]
    (.letOp (n := 60) (.out 0x126722 (movR32M32LowEffect 0x126722 0 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 61) (.exec 0x126722 (LoadPre 0x126722 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x126722 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x126722 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.exec 0x126726 (StorePre 0x126726 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x126726 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x126726 0 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[60, 4]
    (.letOp (n := 63) (.out 0x12672a (movR64M64Effect 0x12672a 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 64) (.exec 0x12672a (LoadPre 0x12672a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x12672a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12672a 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.exec 0x12672f (StorePre 0x12672f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x12672f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12672f 0 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[63, 4]
    (.letOp (n := 66) (.out 0x126734 (movR64M64Effect 0x126734 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 67) (.exec 0x126734 (LoadPre 0x126734 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x126734 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126734 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.exec 0x126739 (StorePre 0x126739 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x126739 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126739 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[66, 4]
    (.letOp (n := 69) (.out 0x12673e (movR32M32LowEffect 0x12673e 0 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 70) (.exec 0x12673e (LoadPre 0x12673e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x12673e + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x12673e 0 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.exec 0x126742 (StorePre 0x126742 3 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x126742 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x126742 0 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[69, 3]
    (.letOp (n := 72) (.out 0x126745 (movR64M64Effect 0x126745 0 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 73) (.exec 0x126745 (LoadPre 0x126745 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x126745 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126745 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.out 0x12674a (movR64M64Effect 0x12674a 7 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 75) (.exec 0x12674a (LoadPre 0x12674a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x12674a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12674a 7 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 76) (.exec 0x12674f (StorePre 0x12674f 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x12674f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12674f 7 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[74, 3]
    (.letOp (n := 77) (.exec 0x126753 (StorePre 0x126753 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x126753 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126753 0 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[72, 3]
    (.letOp (n := 78) (.exec 0x126757 (StorePre 0x126757 4 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x126757 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x126757 13 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 13, .gpr 3] [])) #v[13, 3]
    (.letOp (n := 79) (.exec 0x12675b (StorePre 0x12675b 4 (fun s => AddrMode.addr (.base 3 (.d8 0x1c)) s (0x12675b + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x12675b 10 (.base 3 (.d8 0x1c))) (Reg.operands [.gpr 10, .gpr 3] [])) #v[10, 3]
    (.letOp (n := 80) (.exec 0x12675f (StorePre 0x12675f 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x12675f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12675f 6 (.base 3 (.d8 0x20))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[55, 3]
    (b_l12670b_1))))))))))))))))))))))))))))

def bytes_l12670b : List UInt8 :=
  [0x8B, 0x4C, 0x24, 0x60, 0x48, 0x8B, 0x74, 0x24, 0x58, 0x89, 0x44, 0x24, 0x08, 0x4C, 0x89, 0x44,
    0x24, 0x0C, 0x4C, 0x89, 0x5C, 0x24, 0x14, 0x8B, 0x44, 0x24, 0x18, 0x89, 0x44, 0x24, 0x78, 0x48,
    0x8B, 0x44, 0x24, 0x10, 0x48, 0x89, 0x44, 0x24, 0x70, 0x48, 0x8B, 0x44, 0x24, 0x08, 0x48, 0x89,
    0x44, 0x24, 0x68, 0x8B, 0x44, 0x24, 0x78, 0x89, 0x43, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x68, 0x48,
    0x8B, 0x7C, 0x24, 0x70, 0x48, 0x89, 0x7B, 0x10, 0x48, 0x89, 0x43, 0x08, 0x44, 0x89, 0x6B, 0x04,
    0x44, 0x89, 0x53, 0x1C, 0x48, 0x89, 0x73, 0x20] ++ bytes_l12670b_1

theorem code_l12670b : ∀ x ∈ codeRange 0x12670b bytes_l12670b, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x2670b 88 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l12670b_1

@[cfg_block] def b_l126778 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x126778 (StorePre 0x126778 5 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x126778 + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x126778 (.base 14 (.d8 0x20)) 0x1) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 54) (.out 0x12677d (movR64R64Effect 0x12677d 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[0]
    (.letOp (n := 55) (.exec 0x12677d (fun s => s.RIP = 0x12677d) (movR64R64Effect 0x12677d 8 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 56) (.out 0x126780 (shlR64Effect 0x126780 4 8 32) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[54]
    (.letOp (n := 57) (.exec 0x126780 (fun s => s.RIP = 0x126780) (shlR64Effect 0x126780 4 8 32) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[54]
    (.letOp (n := 58) (.out 0x126784 (orR64Imm8Effect 0x126784 8 0x13) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[56]
    (.letOp (n := 59) (.exec 0x126784 (fun s => s.RIP = 0x126784) (orR64Imm8Effect 0x126784 8 0x13) (Reg.operands [.gpr 8] [])) #v[56]
    (.letOp (n := 60) (.out 0x126788 (movR32Imm32Effect 0x126788 5 1 0x1) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 61) (.exec 0x126788 (fun s => s.RIP = 0x126788) (movR32Imm32Effect 0x126788 5 1 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 62) (.out 0x12678d (xorR32R32Effect 0x12678d 3 14 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 14] []) (.reg (.gpr 14))) #v[14, 14]
    (.letOp (n := 63) (.exec 0x12678d (fun s => s.RIP = 0x12678d) (xorR32R32Effect 0x12678d 3 14 14) (Reg.operands [.gpr 14, .gpr 14] [])) #v[14, 14]
    (.terminate (.br ⟨.l1265fe, RegMap.args [(0, 0), (1, 60), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 58), (9, 9), (10, 10), (11, 11), (14, 62), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩))))))))))))

def bytes_l126778 : List UInt8 :=
  [0x41, 0xC6, 0x46, 0x20, 0x01, 0x49, 0x89, 0xC0, 0x49, 0xC1, 0xE0, 0x20, 0x49, 0x83, 0xC8, 0x13,
    0xB9, 0x01, 0x00, 0x00, 0x00, 0x45, 0x31, 0xF6, 0xE9, 0x69, 0xFE, 0xFF, 0xFF]

theorem code_l126778 : ∀ x ∈ codeRange 0x126778 bytes_l126778, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26778 29 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126795 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126795 (movR64Imm64Effect 0x126795 14 0xffffffff00000000) (EffectPart.reads (.reg (.gpr 14)) [] []) (.reg (.gpr 14))) #v[]
    (.letOp (n := 54) (.exec 0x126795 (fun s => s.RIP = 0x126795) (movR64Imm64Effect 0x126795 14 0xffffffff00000000) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x12679f (andR64R64Effect 0x12679f 14 11) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 11] []) (.reg (.gpr 14))) #v[53, 11]
    (.letOp (n := 56) (.exec 0x12679f (fun s => s.RIP = 0x12679f) (andR64R64Effect 0x12679f 14 11) (Reg.operands [.gpr 14, .gpr 11] [])) #v[53, 11]
    (.letOp (n := 57) (.out 0x1267a2 (movR32M32Effect 0x1267a2 9 (.sib 4 none 0 (.d8 0x54))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 58) (.exec 0x1267a2 (LoadPre 0x1267a2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x54)) s (0x1267a2 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x1267a2 9 (.sib 4 none 0 (.d8 0x54))) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.br ⟨.l1265fe, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 57), (10, 10), (11, 11), (14, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l126795 : List UInt8 :=
  [0x49, 0xBE, 0x00, 0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF, 0x4D, 0x21, 0xDE, 0x44, 0x8B, 0x4C,
    0x24, 0x54, 0xE9, 0x52, 0xFE, 0xFF, 0xFF]

theorem code_l126795 : ∀ x ∈ codeRange 0x126795 bytes_l126795, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26795 23 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1267ac : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1267ac (xorR32R32Effect 0x1267ac 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[1, 1]
    (.letOp (n := 54) (.exec 0x1267ac (fun s => s.RIP = 0x1267ac) (xorR32R32Effect 0x1267ac 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[1, 1]
    (.letOp (n := 55) (.out 0x1267ae (movR32Imm32Effect 0x1267ae 6 8 0xc) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 56) (.exec 0x1267ae (fun s => s.RIP = 0x1267ae) (movR32Imm32Effect 0x1267ae 6 8 0xc) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x1267b4 (xorR32R32Effect 0x1267b4 3 14 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 14] []) (.reg (.gpr 14))) #v[14, 14]
    (.letOp (n := 58) (.exec 0x1267b4 (fun s => s.RIP = 0x1267b4) (xorR32R32Effect 0x1267b4 3 14 14) (Reg.operands [.gpr 14, .gpr 14] [])) #v[14, 14]
    (.terminate (.br ⟨.l1265fe, RegMap.args [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 55), (9, 9), (10, 10), (11, 11), (14, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l1267ac : List UInt8 :=
  [0x31, 0xC9, 0x41, 0xB8, 0x0C, 0x00, 0x00, 0x00, 0x45, 0x31, 0xF6, 0xE9, 0x42, 0xFE, 0xFF, 0xFF]

theorem code_l1267ac : ∀ x ∈ codeRange 0x1267ac bytes_l1267ac, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x267ac 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1267c0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1267c0 (pushR64Effect 0x1267c0 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x1267c0 (PushPre 0x1267c0 1) (pushR64Effect 0x1267c0 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x1267c1 (pushR64Effect 0x1267c1 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x1267c1 (PushPre 0x1267c1 2) (pushR64Effect 0x1267c1 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x1267c3 (pushR64Effect 0x1267c3 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x1267c3 (PushPre 0x1267c3 2) (pushR64Effect 0x1267c3 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x1267c5 (pushR64Effect 0x1267c5 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x1267c5 (PushPre 0x1267c5 2) (pushR64Effect 0x1267c5 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x1267c7 (pushR64Effect 0x1267c7 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x1267c7 (PushPre 0x1267c7 2) (pushR64Effect 0x1267c7 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x1267c9 (pushR64Effect 0x1267c9 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x1267c9 (PushPre 0x1267c9 1) (pushR64Effect 0x1267c9 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x1267ca (subR64Imm32Effect 0x1267ca 4 0x98) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x1267ca (fun s => s.RIP = 0x1267ca) (subR64Imm32Effect 0x1267ca 4 0x98) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x1267d1 (movR64R64Effect 0x1267d1 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 68) (.exec 0x1267d1 (fun s => s.RIP = 0x1267d1) (movR64R64Effect 0x1267d1 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 69) (.out 0x1267d4 (movR32M32Effect 0x1267d4 15 (.base 6 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 6] []) (.reg (.gpr 15))) #v[6]
    (.letOp (n := 70) (.exec 0x1267d4 (LoadPre 0x1267d4 (fun s => AddrMode.addr (.base 6 (.d8 0x1c)) s (0x1267d4 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x1267d4 15 (.base 6 (.d8 0x1c))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 71) (.out 0x1267d8 (movR32M32LowEffect 0x1267d8 5 (.base 2 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[2]
    (.letOp (n := 72) (.exec 0x1267d8 (LoadPre 0x1267d8 (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x1267d8 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x1267d8 5 (.base 2 (.d8 0x8))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 73) (.out 0x1267db (addR32R32Effect 0x1267db 3 5 15) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 15] []) (.reg (.gpr 5))) #v[71, 69]
    (.letOp (n := 74) (.out 0x1267db (addR32R32Effect 0x1267db 3 5 15) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 15] []) (.flag .CF)) #v[71, 69]
    (.letOp (n := 75) (.exec 0x1267db (fun s => s.RIP = 0x1267db) (addR32R32Effect 0x1267db 3 5 15) (Reg.operands [.gpr 5, .gpr 15] [])) #v[71, 69]
    (.letOp (n := 76) (.pure (condOp 2)) #v[74]
    (.terminate (.condBr (Fin.last 76) ⟨.l126a1c, RegMap.args [(1, 1), (2, 2), (3, 67), (4, 65), (5, 73), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 69), (16, 74), (22, 22), (39, 39), (50, 50), (51, 51)] 77⟩ ⟨.l1267e4, RegMap.args [(1, 1), (2, 2), (3, 67), (4, 65), (5, 73), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 69), (16, 74), (22, 22), (39, 39), (50, 50), (51, 51)] 77⟩)))))))))))))))))))))))))

def bytes_l1267c0 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0x98, 0x00, 0x00,
    0x00, 0x48, 0x89, 0xFB, 0x44, 0x8B, 0x7E, 0x1C, 0x8B, 0x6A, 0x08, 0x44, 0x01, 0xFD, 0x0F, 0x82,
    0x38, 0x02, 0x00, 0x00]

theorem code_l1267c0 : ∀ x ∈ codeRange 0x1267c0 bytes_l1267c0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x267c0 36 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1267e4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1267e4 (movR64R64Effect 0x1267e4 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[2]
    (.letOp (n := 54) (.exec 0x1267e4 (fun s => s.RIP = 0x1267e4) (movR64R64Effect 0x1267e4 13 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 55) (.out 0x1267e7 (movR64R64Effect 0x1267e7 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 6] []) (.reg (.gpr 14))) #v[6]
    (.letOp (n := 56) (.exec 0x1267e7 (fun s => s.RIP = 0x1267e7) (movR64R64Effect 0x1267e7 14 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 57) (.out 0x1267ea (movR64M64Effect 0x1267ea 6 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[6]
    (.letOp (n := 58) (.exec 0x1267ea (LoadPre 0x1267ea (fun s => AddrMode.addr (.base 6 .none) s (0x1267ea + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1267ea 6 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 59) (.out 0x1267ed (movR64M64Effect 0x1267ed 12 (.base 14 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 14] []) (.reg (.gpr 12))) #v[55]
    (.letOp (n := 60) (.exec 0x1267ed (LoadPre 0x1267ed (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x1267ed + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1267ed 12 (.base 14 (.d8 0x8))) (Reg.operands [.gpr 14] [])) #v[55]
    (.letOp (n := 61) (.out 0x1267f1 (leaR64Effect 0x1267f1 7 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 62) (.exec 0x1267f1 (fun s => s.RIP = 0x1267f1) (leaR64Effect 0x1267f1 7 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x1267f6 (StorePre 0x1267f6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1267f6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1267f6 6 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 64) (.out 0x1267fb (movR64R64Effect 0x1267fb 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12] []) (.reg (.gpr 2))) #v[59]
    (.letOp (n := 65) (.exec 0x1267fb (fun s => s.RIP = 0x1267fb) (movR64R64Effect 0x1267fb 2 12) (Reg.operands [.gpr 12] [])) #v[59]
    (.letOp (n := 66) (.out 0x1267fe (movR32R32Effect 0x1267fe 2 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[5]
    (.letOp (n := 67) (.exec 0x1267fe (fun s => s.RIP = 0x1267fe) (movR32R32Effect 0x1267fe 2 1 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 68) (.out 0x126800 (callEffect (fun _ => 0x127c50) 0x126805) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 69) (.exec 0x126800 (PushPre 0x126800 5) (callEffect (fun _ => 0x127c50) 0x126805) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.const ⟨64, 0x126805⟩) #v[]
    (.terminate (.call ⟨.l127c50, RegMap.args [(1, 66), (2, 64), (3, 3), (4, 68), (5, 5), (6, 57), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 53), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 71⟩ { target := .l126805, kept := #v[], arity := rfl, guard := some (Fin.last 70) })))))))))))))))))))

def bytes_l1267e4 : List UInt8 :=
  [0x49, 0x89, 0xD5, 0x49, 0x89, 0xF6, 0x48, 0x8B, 0x36, 0x4D, 0x8B, 0x66, 0x08, 0x48, 0x8D, 0x7C,
    0x24, 0x40, 0x48, 0x89, 0x74, 0x24, 0x78, 0x4C, 0x89, 0xE2, 0x89, 0xE9, 0xE8, 0x4B, 0x14, 0x00,
    0x00]

theorem code_l1267e4 : ∀ x ∈ codeRange 0x1267e4 bytes_l1267e4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x267e4 33 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126805 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126805 (movR32M32LowEffect 0x126805 2 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 54) (.exec 0x126805 (LoadPre 0x126805 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x126805 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x126805 2 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x126809 (cmpR32Imm8Effect 0x126809 3 2 0x2) (EffectPart.reads (.flag .ZF) [.gpr 2] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x126809 (fun s => s.RIP = 0x126809) (cmpR32Imm8Effect 0x126809 3 2 0x2) (Reg.operands [.gpr 2] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l126830, RegMap.args [(2, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l12680e, RegMap.args [(2, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l126805 : List UInt8 :=
  [0x8B, 0x54, 0x24, 0x40, 0x83, 0xFA, 0x02, 0x75, 0x22]

theorem code_l126805 : ∀ x ∈ codeRange 0x126805 bytes_l126805, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26805 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12680e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12680e (movR64M64Effect 0x12680e 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x12680e (LoadPre 0x12680e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x12680e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12680e 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x126813 (movR64M64Effect 0x126813 1 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x126813 (LoadPre 0x126813 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x126813 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126813 1 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x126818 (StorePre 0x126818 3 (fun s => AddrMode.addr (.base 14 .none) s (0x126818 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x126818 0 (.base 14 .none)) (Reg.operands [.gpr 0, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 58) (.exec 0x12681b (StorePre 0x12681b 4 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x12681b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12681b 1 (.base 14 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x12681f (movR64M64Effect 0x12681f 0 (.base 14 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[14]
    (.letOp (n := 60) (.exec 0x12681f (LoadPre 0x12681f (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x12681f + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12681f 0 (.base 14 (.d8 0x10))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 61) (.out 0x126823 (cmpR64Imm8Effect 0x126823 0 0x3f) (EffectPart.reads (.flag .CF) [.gpr 0] []) (.flag .CF)) #v[59]
    (.letOp (n := 62) (.out 0x126823 (cmpR64Imm8Effect 0x126823 0 0x3f) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[59]
    (.letOp (n := 63) (.exec 0x126823 (fun s => s.RIP = 0x126823) (cmpR64Imm8Effect 0x126823 0 0x3f) (Reg.operands [.gpr 0] [])) #v[59]
    (.letOp (n := 64) (.pure (condOp 6)) #v[61, 62]
    (.terminate (.condBr (Fin.last 64) ⟨.l126875, RegMap.args [(0, 59), (1, 55), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 61), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)] 65⟩ ⟨.l126829, RegMap.args [(0, 59), (1, 55), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 61), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)] 65⟩)))))))))))))

def bytes_l12680e : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x8B, 0x4C, 0x24, 0x50, 0x49, 0x89, 0x06, 0x49, 0x89, 0x4E,
    0x08, 0x49, 0x8B, 0x46, 0x10, 0x48, 0x83, 0xF8, 0x3F, 0x76, 0x4C]

theorem code_l12680e : ∀ x ∈ codeRange 0x12680e bytes_l12680e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2680e 27 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126829 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126829 (movR32Imm32Effect 0x126829 5 0 0x6) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 54) (.exec 0x126829 (fun s => s.RIP = 0x126829) (movR32Imm32Effect 0x126829 5 0 0x6) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l126895, RegMap.args [(0, 53), (3, 3), (4, 4), (7, 7), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l126829 : List UInt8 :=
  [0xB8, 0x06, 0x00, 0x00, 0x00, 0xEB, 0x65]

theorem code_l126829 : ∀ x ∈ codeRange 0x126829 bytes_l126829, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26829 7 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126830 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126830 (movR32M32LowEffect 0x126830 1 (.sib 4 none 0 (.d8 0x44))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x126830 (LoadPre 0x126830 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x126830 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x126830 1 (.sib 4 none 0 (.d8 0x44))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x126834 (movR64M64Effect 0x126834 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 56) (.exec 0x126834 (LoadPre 0x126834 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x126834 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126834 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x126839 (movR64M64Effect 0x126839 6 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 58) (.exec 0x126839 (LoadPre 0x126839 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x126839 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126839 6 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x12683e (movR64M64Effect 0x12683e 7 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 60) (.exec 0x12683e (LoadPre 0x12683e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x12683e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12683e 7 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x126843 (StorePre 0x126843 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x126843 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126843 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x126848 (movR64M64Effect 0x126848 7 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 63) (.exec 0x126848 (LoadPre 0x126848 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x126848 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126848 7 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x12684d (StorePre 0x12684d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x12684d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12684d 7 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x126852 (movR64M64Effect 0x126852 7 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 66) (.exec 0x126852 (LoadPre 0x126852 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x126852 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126852 7 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x126857 (StorePre 0x126857 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x126857 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126857 7 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x12685c (movR64M64Effect 0x12685c 7 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 69) (.exec 0x12685c (LoadPre 0x12685c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x12685c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12685c 7 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.exec 0x126861 (StorePre 0x126861 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x126861 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126861 7 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[68, 4]
    (.terminate (.br ⟨.l126866, RegMap.args [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 68), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 71⟩)))))))))))))))))))

def bytes_l126830 : List UInt8 :=
  [0x8B, 0x4C, 0x24, 0x44, 0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x8B, 0x74, 0x24, 0x50, 0x48, 0x8B,
    0x7C, 0x24, 0x58, 0x48, 0x89, 0x7C, 0x24, 0x08, 0x48, 0x8B, 0x7C, 0x24, 0x60, 0x48, 0x89, 0x7C,
    0x24, 0x10, 0x48, 0x8B, 0x7C, 0x24, 0x68, 0x48, 0x89, 0x7C, 0x24, 0x18, 0x48, 0x8B, 0x7C, 0x24,
    0x70, 0x48, 0x89, 0x7C, 0x24, 0x20]

theorem code_l126830 : ∀ x ∈ codeRange 0x126830 bytes_l126830, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26830 54 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126866 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126866 (movR64Imm64Effect 0x126866 7 0xffffffff00000000) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 54) (.exec 0x126866 (fun s => s.RIP = 0x126866) (movR64Imm64Effect 0x126866 7 0xffffffff00000000) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x126870 (andR64R64Effect 0x126870 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[53, 6]
    (.letOp (n := 56) (.exec 0x126870 (fun s => s.RIP = 0x126870) (andR64R64Effect 0x126870 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[53, 6]
    (.terminate (.br ⟨.l1268a2, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 55), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l126866 : List UInt8 :=
  [0x48, 0xBF, 0x00, 0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF, 0x48, 0x21, 0xF7, 0xEB, 0x2D]

theorem code_l126866 : ∀ x ∈ codeRange 0x126866 bytes_l126866, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26866 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126875 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126875 (incR64Effect 0x126875 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 54) (.exec 0x126875 (fun s => s.RIP = 0x126875) (incR64Effect 0x126875 0) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[0]
    (.letOp (n := 55) (.exec 0x126878 (StorePre 0x126878 4 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x126878 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126878 0 (.base 14 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 56) (.out 0x12687c (movR32M32Effect 0x12687c 15 (.base 14 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 14] []) (.reg (.gpr 15))) #v[14]
    (.letOp (n := 57) (.exec 0x12687c (LoadPre 0x12687c (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x12687c + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x12687c 15 (.base 14 (.d8 0x18))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 58) (.out 0x126880 (cmpR32R32Effect 0x126880 3 5 15) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 15] []) (.flag .CF)) #v[5, 56]
    (.letOp (n := 59) (.out 0x126880 (cmpR32R32Effect 0x126880 3 5 15) (EffectPart.reads (.flag .ZF) [.gpr 5, .gpr 15] []) (.flag .ZF)) #v[5, 56]
    (.letOp (n := 60) (.exec 0x126880 (fun s => s.RIP = 0x126880) (cmpR32R32Effect 0x126880 3 5 15) (Reg.operands [.gpr 5, .gpr 15] [])) #v[5, 56]
    (.letOp (n := 61) (.pure (condOp 6)) #v[58, 59]
    (.terminate (.condBr (Fin.last 61) ⟨.l12690e, RegMap.args [(0, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 56), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ ⟨.l126889, RegMap.args [(0, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 56), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩))))))))))

def bytes_l126875 : List UInt8 :=
  [0x48, 0xFF, 0xC0, 0x49, 0x89, 0x46, 0x10, 0x45, 0x8B, 0x7E, 0x18, 0x44, 0x39, 0xFD, 0x0F, 0x86,
    0x85, 0x00, 0x00, 0x00]

theorem code_l126875 : ∀ x ∈ codeRange 0x126875 bytes_l126875, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26875 20 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126889 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126889 (leaR32Effect 0x126889 4 0 (.base 15 (.d8 0x1))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[15]
    (.letOp (n := 54) (.exec 0x126889 (fun s => s.RIP = 0x126889) (leaR32Effect 0x126889 4 0 (.base 15 (.d8 0x1))) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.out 0x12688d (shlR64Effect 0x12688d 4 0 32) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x12688d (fun s => s.RIP = 0x12688d) (shlR64Effect 0x12688d 4 0 32) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 57) (.out 0x126891 (orR64Imm8Effect 0x126891 0 0x3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[55]
    (.letOp (n := 58) (.exec 0x126891 (fun s => s.RIP = 0x126891) (orR64Imm8Effect 0x126891 0 0x3) (Reg.operands [.gpr 0] [])) #v[55]
    (.terminate (.br ⟨.l126895, RegMap.args [(0, 57), (3, 3), (4, 4), (7, 7), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l126889 : List UInt8 :=
  [0x41, 0x8D, 0x47, 0x01, 0x48, 0xC1, 0xE0, 0x20, 0x48, 0x83, 0xC8, 0x03]

theorem code_l126889 : ∀ x ∈ codeRange 0x126889 bytes_l126889, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26889 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126895 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126895 (movR32Imm32Effect 0x126895 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 54) (.exec 0x126895 (fun s => s.RIP = 0x126895) (movR32Imm32Effect 0x126895 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x12689a (xorR32R32Effect 0x12689a 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[7, 7]
    (.letOp (n := 56) (.exec 0x12689a (fun s => s.RIP = 0x12689a) (xorR32R32Effect 0x12689a 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[7, 7]
    (.letOp (n := 57) (.out 0x12689c (movR32R32Effect 0x12689c 3 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 15] []) (.reg (.gpr 1))) #v[15]
    (.letOp (n := 58) (.exec 0x12689c (fun s => s.RIP = 0x12689c) (movR32R32Effect 0x12689c 3 1 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 59) (.out 0x12689f (movR32R32Effect 0x12689f 3 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 60) (.exec 0x12689f (fun s => s.RIP = 0x12689f) (movR32R32Effect 0x12689f 3 6 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.terminate (.br ⟨.l1268a2, RegMap.args [(0, 0), (1, 57), (2, 53), (3, 3), (4, 4), (6, 59), (7, 55), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩)))))))))

def bytes_l126895 : List UInt8 :=
  [0xBA, 0x01, 0x00, 0x00, 0x00, 0x31, 0xFF, 0x44, 0x89, 0xF9, 0x44, 0x89, 0xFE]

theorem code_l126895 : ∀ x ∈ codeRange 0x126895 bytes_l126895, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26895 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1268a2_1 : Block Op Label signature Reg.count 83 :=
  .letOp (n := 83) (.exec 0x1268f1 (StorePre 0x1268f1 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x1268f1 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1268f1 0 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (.letOp (n := 84) (.exec 0x1268f5 (StorePre 0x1268f5 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x1268f5 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1268f5 6 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[55, 3]
    (.terminate (.br ⟨.l1268f9, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 75), (8, 77), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 85⟩)))

def bytes_l1268a2_1 : List UInt8 :=
  [0x48, 0x89, 0x43, 0x08, 0x48, 0x89, 0x73, 0x10]

theorem code_l1268a2_1 : ∀ x ∈ codeRange 0x1268f1 bytes_l1268a2_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x268f1 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1268a2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1268a2 (movR32R32Effect 0x1268a2 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[6]
    (.letOp (n := 54) (.exec 0x1268a2 (fun s => s.RIP = 0x1268a2) (movR32R32Effect 0x1268a2 2 6 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 55) (.out 0x1268a4 (orR64R64Effect 0x1268a4 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7] []) (.reg (.gpr 6))) #v[53, 7]
    (.letOp (n := 56) (.exec 0x1268a4 (fun s => s.RIP = 0x1268a4) (orR64R64Effect 0x1268a4 6 7) (Reg.operands [.gpr 6, .gpr 7] [])) #v[53, 7]
    (.letOp (n := 57) (.out 0x1268a7 (movR32M32LowEffect 0x1268a7 7 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 58) (.exec 0x1268a7 (LoadPre 0x1268a7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1268a7 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1268a7 7 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.exec 0x1268ab (StorePre 0x1268ab 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1268ab + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x1268ab 7 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 60) (.out 0x1268af (movR64M64Effect 0x1268af 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 61) (.exec 0x1268af (LoadPre 0x1268af (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1268af + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1268af 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.out 0x1268b4 (movR64M64Effect 0x1268b4 8 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 63) (.exec 0x1268b4 (LoadPre 0x1268b4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1268b4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1268b4 8 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x1268b9 (StorePre 0x1268b9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1268b9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1268b9 8 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.exec 0x1268be (StorePre 0x1268be 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1268be + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1268be 7 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[60, 4]
    (.letOp (n := 66) (.out 0x1268c3 (movR32M32LowEffect 0x1268c3 7 (.sib 4 none 0 (.d8 0x24))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 67) (.exec 0x1268c3 (LoadPre 0x1268c3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x1268c3 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1268c3 7 (.sib 4 none 0 (.d8 0x24))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.exec 0x1268c7 (StorePre 0x1268c7 3 (fun s => AddrMode.addr (.base 3 (.d8 0x34)) s (0x1268c7 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x1268c7 7 (.base 3 (.d8 0x34))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[66, 3]
    (.letOp (n := 69) (.out 0x1268ca (movR64M64Effect 0x1268ca 7 (.sib 4 none 0 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 70) (.exec 0x1268ca (LoadPre 0x1268ca (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x1268ca + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1268ca 7 (.sib 4 none 0 (.d8 0x1c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.exec 0x1268cf (StorePre 0x1268cf 4 (fun s => AddrMode.addr (.base 3 (.d8 0x2c)) s (0x1268cf + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1268cf 7 (.base 3 (.d8 0x2c))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[69, 3]
    (.letOp (n := 72) (.out 0x1268d3 (movR32M32LowEffect 0x1268d3 7 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 73) (.exec 0x1268d3 (LoadPre 0x1268d3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1268d3 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1268d3 7 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.exec 0x1268d7 (StorePre 0x1268d7 3 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x1268d7 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x1268d7 7 (.base 3 (.d8 0x28))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[72, 3]
    (.letOp (n := 75) (.out 0x1268da (movR64M64Effect 0x1268da 7 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 76) (.exec 0x1268da (LoadPre 0x1268da (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1268da + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1268da 7 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 77) (.out 0x1268df (movR64M64Effect 0x1268df 8 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 78) (.exec 0x1268df (LoadPre 0x1268df (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1268df + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1268df 8 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.exec 0x1268e4 (StorePre 0x1268e4 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x1268e4 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1268e4 8 (.base 3 (.d8 0x20))) (Reg.operands [.gpr 8, .gpr 3] [])) #v[77, 3]
    (.letOp (n := 80) (.exec 0x1268e8 (StorePre 0x1268e8 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x1268e8 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1268e8 7 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[75, 3]
    (.letOp (n := 81) (.exec 0x1268ec (StorePre 0x1268ec 2 (fun s => AddrMode.addr (.base 3 .none) s (0x1268ec + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x1268ec 2 (.base 3 .none)) (Reg.operands [.gpr 2, .gpr 3] [])) #v[2, 3]
    (.letOp (n := 82) (.exec 0x1268ee (StorePre 0x1268ee 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x1268ee + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x1268ee 1 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[1, 3]
    (b_l1268a2_1))))))))))))))))))))))))))))))

def bytes_l1268a2 : List UInt8 :=
  [0x89, 0xF6, 0x48, 0x09, 0xFE, 0x8B, 0x7C, 0x24, 0x18, 0x89, 0x7C, 0x24, 0x38, 0x48, 0x8B, 0x7C,
    0x24, 0x08, 0x4C, 0x8B, 0x44, 0x24, 0x10, 0x4C, 0x89, 0x44, 0x24, 0x30, 0x48, 0x89, 0x7C, 0x24,
    0x28, 0x8B, 0x7C, 0x24, 0x24, 0x89, 0x7B, 0x34, 0x48, 0x8B, 0x7C, 0x24, 0x1C, 0x48, 0x89, 0x7B,
    0x2C, 0x8B, 0x7C, 0x24, 0x38, 0x89, 0x7B, 0x28, 0x48, 0x8B, 0x7C, 0x24, 0x28, 0x4C, 0x8B, 0x44,
    0x24, 0x30, 0x4C, 0x89, 0x43, 0x20, 0x48, 0x89, 0x7B, 0x18, 0x89, 0x13, 0x89, 0x4B, 0x04] ++ bytes_l1268a2_1

theorem code_l1268a2 : ∀ x ∈ codeRange 0x1268a2 bytes_l1268a2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x268a2 79 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1268a2_1

@[cfg_block] def b_l1268f9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1268f9 (movR64R64Effect 0x1268f9 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 54) (.exec 0x1268f9 (fun s => s.RIP = 0x1268f9) (movR64R64Effect 0x1268f9 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x1268fc (addR64Imm32Effect 0x1268fc 4 0x98) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 56) (.exec 0x1268fc (fun s => s.RIP = 0x1268fc) (addR64Imm32Effect 0x1268fc 4 0x98) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x126903 (popR64Effect 0x126903 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[55]
    (.letOp (n := 58) (.out 0x126903 (popR64Effect 0x126903 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[55]
    (.letOp (n := 59) (.exec 0x126903 (PopPre 0x126903) (popR64Effect 0x126903 1 3) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 60) (.out 0x126904 (popR64Effect 0x126904 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[58]
    (.letOp (n := 61) (.out 0x126904 (popR64Effect 0x126904 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[58]
    (.letOp (n := 62) (.exec 0x126904 (PopPre 0x126904) (popR64Effect 0x126904 2 12) (Reg.operands [.gpr 4] [])) #v[58]
    (.letOp (n := 63) (.out 0x126906 (popR64Effect 0x126906 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[61]
    (.letOp (n := 64) (.out 0x126906 (popR64Effect 0x126906 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 65) (.exec 0x126906 (PopPre 0x126906) (popR64Effect 0x126906 2 13) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 66) (.out 0x126908 (popR64Effect 0x126908 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[64]
    (.letOp (n := 67) (.out 0x126908 (popR64Effect 0x126908 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[64]
    (.letOp (n := 68) (.exec 0x126908 (PopPre 0x126908) (popR64Effect 0x126908 2 14) (Reg.operands [.gpr 4] [])) #v[64]
    (.letOp (n := 69) (.out 0x12690a (popR64Effect 0x12690a 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[67]
    (.letOp (n := 70) (.out 0x12690a (popR64Effect 0x12690a 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[67]
    (.letOp (n := 71) (.exec 0x12690a (PopPre 0x12690a) (popR64Effect 0x12690a 2 15) (Reg.operands [.gpr 4] [])) #v[67]
    (.letOp (n := 72) (.out 0x12690c (popR64Effect 0x12690c 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[70]
    (.letOp (n := 73) (.out 0x12690c (popR64Effect 0x12690c 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[70]
    (.letOp (n := 74) (.exec 0x12690c (PopPre 0x12690c) (popR64Effect 0x12690c 1 5) (Reg.operands [.gpr 4] [])) #v[70]
    (.letOp (n := 75) (.out 0x12690d (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[73]
    (.letOp (n := 76) (.out 0x12690d (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[73]
    (.letOp (n := 77) (.exec 0x12690d (RetPre 0x12690d) (retEffect) (Reg.operands [.gpr 4] [])) #v[73]
    (.terminate (.ret (RegMap.args [(0, 53), (1, 1), (2, 2), (3, 57), (4, 76), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 78) (some ⟨75, by decide⟩)))))))))))))))))))))))))))

def bytes_l1268f9 : List UInt8 :=
  [0x48, 0x89, 0xD8, 0x48, 0x81, 0xC4, 0x98, 0x00, 0x00, 0x00, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41,
    0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l1268f9 : ∀ x ∈ codeRange 0x1268f9 bytes_l1268f9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x268f9 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12690e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x12690e (StorePre 0x12690e 4 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x12690e + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x12690e 5 (.base 14 (.d8 0x18))) (Reg.operands [.gpr 5, .gpr 14] [])) #v[5, 14]
    (.letOp (n := 54) (.out 0x126912 (leaR64Effect 0x126912 2 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 55) (.exec 0x126912 (fun s => s.RIP = 0x126912) (leaR64Effect 0x126912 2 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x12691a (movR64M64Effect 0x12691a 0 (.base 13 (.d8 0x0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[13]
    (.letOp (n := 57) (.exec 0x12691a (LoadPre 0x12691a (fun s => AddrMode.addr (.base 13 (.d8 0x0)) s (0x12691a + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12691a 0 (.base 13 (.d8 0x0))) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 58) (.out 0x12691e (movR64M64Effect 0x12691e 1 (.base 13 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 13] []) (.reg (.gpr 1))) #v[13]
    (.letOp (n := 59) (.exec 0x12691e (LoadPre 0x12691e (fun s => AddrMode.addr (.base 13 (.d8 0x8)) s (0x12691e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12691e 1 (.base 13 (.d8 0x8))) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 60) (.exec 0x126922 (StorePre 0x126922 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x126922 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x126922 1 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[58, 4]
    (.letOp (n := 61) (.exec 0x12692a (StorePre 0x12692a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x12692a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x12692a 0 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 62) (.exec 0x126932 (StorePre 0x126932 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x126932 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x126932 14 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[14, 4]
    (.letOp (n := 63) (.out 0x12693a (leaR64Effect 0x12693a 7 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 64) (.exec 0x12693a (fun s => s.RIP = 0x12693a) (leaR64Effect 0x12693a 7 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x12693f (movR64R64Effect 0x12693f 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 66) (.exec 0x12693f (fun s => s.RIP = 0x12693f) (movR64R64Effect 0x12693f 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 67) (.out 0x126942 (callEffect (fun _ => 0x1248c0) 0x126947) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 68) (.exec 0x126942 (PushPre 0x126942 5) (callEffect (fun _ => 0x1248c0) 0x126947) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.const ⟨64, 0x126947⟩) #v[]
    (.terminate (.call ⟨.l1248c0, RegMap.args [(0, 56), (1, 58), (2, 54), (3, 3), (4, 67), (5, 5), (6, 65), (7, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 70⟩ { target := .l126947, kept := #v[], arity := rfl, guard := some (Fin.last 69) }))))))))))))))))))

def bytes_l12690e : List UInt8 :=
  [0x41, 0x89, 0x6E, 0x18, 0x48, 0x8D, 0x94, 0x24, 0x88, 0x00, 0x00, 0x00, 0x49, 0x8B, 0x45, 0x00,
    0x49, 0x8B, 0x4D, 0x08, 0x48, 0x89, 0x8C, 0x24, 0x90, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24,
    0x88, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xB4, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x7C, 0x24,
    0x40, 0x4C, 0x89, 0xF6, 0xE8, 0x79, 0xDF, 0xFF, 0xFF]

theorem code_l12690e : ∀ x ∈ codeRange 0x12690e bytes_l12690e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2690e 57 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

end K256.Proofs.Signing.LIR
