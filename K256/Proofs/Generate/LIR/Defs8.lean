import K256.Proofs.Generate.LIR.Labels
import K256.Proofs.Common.CFG.EvalAttr
import K256.Proofs.Common.Lift.Generated.Footprints.Part1
import K256.Proofs.Common.Lift.Generated.Footprints.Part2
import K256.Proofs.Common.Lift.Generated.Footprints.Part3
import K256.Proofs.Common.Lift.Generated.Footprints.Part4
import K256.Proofs.Common.Lift.Generated.Footprints.Part5
import K256.Proofs.Generate.LIR.Generated.Footprints

namespace K256.Proofs.Generate.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Sec1.LIR

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
    (.letOp (n := 54) (.out 0x125790 (pushR64Effect 0x125790 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 55) (.exec 0x125790 (PushPre 0x125790 1) (pushR64Effect 0x125790 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 56) (.out 0x125791 (pushR64Effect 0x125791 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[54, 15]
    (.letOp (n := 57) (.exec 0x125791 (PushPre 0x125791 2) (pushR64Effect 0x125791 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[54, 15]
    (.letOp (n := 58) (.out 0x125793 (pushR64Effect 0x125793 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[56, 14]
    (.letOp (n := 59) (.exec 0x125793 (PushPre 0x125793 2) (pushR64Effect 0x125793 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[56, 14]
    (.letOp (n := 60) (.out 0x125795 (pushR64Effect 0x125795 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[58, 3]
    (.letOp (n := 61) (.exec 0x125795 (PushPre 0x125795 1) (pushR64Effect 0x125795 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[58, 3]
    (.letOp (n := 62) (.out 0x125796 (subR64Imm32Effect 0x125796 4 0x138) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[60]
    (.letOp (n := 63) (.exec 0x125796 (fun s => s.RIP = 0x125796) (subR64Imm32Effect 0x125796 4 0x138) (Reg.operands [.gpr 4] [])) #v[60]
    (.letOp (n := 64) (.out 0x12579d (movR64R64Effect 0x12579d 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 65) (.exec 0x12579d (fun s => s.RIP = 0x12579d) (movR64R64Effect 0x12579d 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 66) (.out 0x1257a0 (leaR64Effect 0x1257a0 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[62]
    (.letOp (n := 67) (.exec 0x1257a0 (fun s => s.RIP = 0x1257a0) (leaR64Effect 0x1257a0 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[62]
    (.letOp (n := 68) (.out 0x1257a5 (callEffect (fun _ => 0x127690) 0x1257aa) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[62]
    (.letOp (n := 69) (.exec 0x1257a5 (PushPre 0x1257a5 5) (callEffect (fun _ => 0x127690) 0x1257aa) (Reg.operands [.gpr 4] [])) #v[62]
    (.letOp (n := 70) (.const ⟨64, 0x1257aa⟩) #v[]
    (.terminate (.call ⟨.l127690, RegMap.args [(2, 2), (3, 64), (4, 68), (5, 5), (6, 6), (7, 66), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 71⟩ { target := .l1257aa, kept := #v[], arity := rfl, guard := some (Fin.last 70) })))))))))))))))))))

def bytes_l125788 : List UInt8 :=
  [0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00, 0x55, 0x41, 0x57, 0x41, 0x56, 0x53, 0x48, 0x81,
    0xEC, 0x38, 0x01, 0x00, 0x00, 0x48, 0x89, 0xFB, 0x48, 0x8D, 0x7C, 0x24, 0x08, 0xE8, 0xE6, 0x1E,
    0x00, 0x00]

theorem code_l125788 : ∀ x ∈ codeRange 0x125788 bytes_l125788, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x25788 34 (by decide +kernel)
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

@[cfg_block] def b_l126947 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126947 (movR32M32Effect 0x126947 6 (.base 14 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 54) (.exec 0x126947 (LoadPre 0x126947 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x126947 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x126947 6 (.base 14 (.d8 0x18))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 55) (.out 0x12694b (movR32M32Effect 0x12694b 1 (.base 14 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[14]
    (.letOp (n := 56) (.exec 0x12694b (LoadPre 0x12694b (fun s => AddrMode.addr (.base 14 (.d8 0x1c)) s (0x12694b + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x12694b 1 (.base 14 (.d8 0x1c))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x12694f (subR32R32Effect 0x12694f 2 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[53, 55]
    (.letOp (n := 58) (.out 0x12694f (subR32R32Effect 0x12694f 2 6 1) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 1] []) (.flag .CF)) #v[53, 55]
    (.letOp (n := 59) (.out 0x12694f (subR32R32Effect 0x12694f 2 6 1) (EffectPart.reads (.flag .ZF) [.gpr 6, .gpr 1] []) (.flag .ZF)) #v[53, 55]
    (.letOp (n := 60) (.exec 0x12694f (fun s => s.RIP = 0x12694f) (subR32R32Effect 0x12694f 2 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[53, 55]
    (.letOp (n := 61) (.out 0x126951 (atFlags (condHolds 6) (setccR8Effect 0x126951 3 0)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF]) (.reg (.gpr 0))) #v[0, 58, 59]
    (.letOp (n := 62) (.exec 0x126951 (fun s => s.RIP = 0x126951) (atFlags (condHolds 6) (setccR8Effect 0x126951 3 0)) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF])) #v[0, 58, 59]
    (.letOp (n := 63) (.out 0x126954 (movR64M64Effect 0x126954 2 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 64) (.exec 0x126954 (LoadPre 0x126954 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x126954 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126954 2 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.exec 0x126959 (StorePre 0x126959 3 (fun s => AddrMode.addr (.base 14 .none) s (0x126959 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x126959 2 (.base 14 .none)) (Reg.operands [.gpr 2, .gpr 14] [])) #v[63, 14]
    (.letOp (n := 66) (.exec 0x12695c (StorePre 0x12695c 4 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x12695c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12695c 12 (.base 14 (.d8 0x8))) (Reg.operands [.gpr 12, .gpr 14] [])) #v[12, 14]
    (.letOp (n := 67) (.exec 0x126960 (StorePre 0x126960 4 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x126960 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x126960 15 (.base 14 (.d8 0x18))) (Reg.operands [.gpr 15, .gpr 14] [])) #v[15, 14]
    (.letOp (n := 68) (.out 0x126964 (movR64M64Effect 0x126964 2 (.base 14 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14] []) (.reg (.gpr 2))) #v[14]
    (.letOp (n := 69) (.exec 0x126964 (LoadPre 0x126964 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x126964 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x126964 2 (.base 14 (.d8 0x10))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 70) (.out 0x126968 (cmpR64Imm8Effect 0x126968 2 0x1) (EffectPart.reads (.flag .CF) [.gpr 2] []) (.flag .CF)) #v[68]
    (.letOp (n := 71) (.exec 0x126968 (fun s => s.RIP = 0x126968) (cmpR64Imm8Effect 0x126968 2 0x1) (Reg.operands [.gpr 2] [])) #v[68]
    (.letOp (n := 72) (.out 0x12696c (atFlags StatusFlags.CF (adcR64Imm8Effect 0x12696c 2 0xff)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[68, 70]
    (.letOp (n := 73) (.exec 0x12696c (fun s => s.RIP = 0x12696c) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x12696c 2 0xff)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[68, 70]
    (.letOp (n := 74) (.exec 0x126970 (StorePre 0x126970 4 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x126970 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126970 2 (.base 14 (.d8 0x10))) (Reg.operands [.gpr 2, .gpr 14] [])) #v[72, 14]
    (.letOp (n := 75) (.out 0x126974 (movR32M32LowEffect 0x126974 2 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 76) (.exec 0x126974 (LoadPre 0x126974 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x126974 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x126974 2 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 77) (.out 0x126978 (cmpR32Imm8Effect 0x126978 3 2 0x2) (EffectPart.reads (.flag .ZF) [.gpr 2] []) (.flag .ZF)) #v[75]
    (.letOp (n := 78) (.exec 0x126978 (fun s => s.RIP = 0x126978) (cmpR32Imm8Effect 0x126978 3 2 0x2) (Reg.operands [.gpr 2] [])) #v[75]
    (.letOp (n := 79) (.out 0x12697b (atFlags (condHolds 5) (setccR8Effect 0x12697b 4 7)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 7))) #v[7, 77]
    (.letOp (n := 80) (.exec 0x12697b (fun s => s.RIP = 0x12697b) (atFlags (condHolds 5) (setccR8Effect 0x12697b 4 7)) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[7, 77]
    (.letOp (n := 81) (.out 0x12697f (orR8R8Effect 0x12697f 3 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[79, 61]
    (.letOp (n := 82) (.out 0x12697f (orR8R8Effect 0x12697f 3 7 0) (EffectPart.reads (.flag .ZF) [.gpr 7, .gpr 0] []) (.flag .ZF)) #v[79, 61]
    (.letOp (n := 83) (.exec 0x12697f (fun s => s.RIP = 0x12697f) (orR8R8Effect 0x12697f 3 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[79, 61]
    (.letOp (n := 84) (.pure (condOp 4)) #v[82]
    (.terminate (.condBr (Fin.last 84) ⟨.l126a00, RegMap.args [(0, 61), (1, 55), (2, 75), (3, 3), (4, 4), (6, 57), (7, 81), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 82), (22, 22), (39, 39), (50, 50), (51, 51)] 85⟩ ⟨.l126984, RegMap.args [(0, 61), (1, 55), (2, 75), (3, 3), (4, 4), (6, 57), (7, 81), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 82), (22, 22), (39, 39), (50, 50), (51, 51)] 85⟩)))))))))))))))))))))))))))))))))

def bytes_l126947 : List UInt8 :=
  [0x41, 0x8B, 0x76, 0x18, 0x41, 0x8B, 0x4E, 0x1C, 0x29, 0xCE, 0x0F, 0x96, 0xC0, 0x48, 0x8B, 0x54,
    0x24, 0x78, 0x49, 0x89, 0x16, 0x4D, 0x89, 0x66, 0x08, 0x45, 0x89, 0x7E, 0x18, 0x49, 0x8B, 0x56,
    0x10, 0x48, 0x83, 0xFA, 0x01, 0x48, 0x83, 0xD2, 0xFF, 0x49, 0x89, 0x56, 0x10, 0x8B, 0x54, 0x24,
    0x40, 0x83, 0xFA, 0x02, 0x40, 0x0F, 0x95, 0xC7, 0x40, 0x08, 0xC7, 0x74, 0x7C]

theorem code_l126947 : ∀ x ∈ codeRange 0x126947 bytes_l126947, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26947 61 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126984 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126984 (movR32M32LowEffect 0x126984 1 (.sib 4 none 0 (.d8 0x44))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x126984 (LoadPre 0x126984 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x126984 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x126984 1 (.sib 4 none 0 (.d8 0x44))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x126988 (movR64M64Effect 0x126988 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 56) (.exec 0x126988 (LoadPre 0x126988 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x126988 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126988 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x12698d (movR64M64Effect 0x12698d 6 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 58) (.exec 0x12698d (LoadPre 0x12698d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x12698d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12698d 6 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x126992 (movR64M64Effect 0x126992 7 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 60) (.exec 0x126992 (LoadPre 0x126992 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x126992 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126992 7 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x126997 (StorePre 0x126997 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x126997 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126997 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x12699c (movR64M64Effect 0x12699c 7 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 63) (.exec 0x12699c (LoadPre 0x12699c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x12699c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12699c 7 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x1269a1 (StorePre 0x1269a1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1269a1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1269a1 7 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x1269a6 (movR64M64Effect 0x1269a6 7 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 66) (.exec 0x1269a6 (LoadPre 0x1269a6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x1269a6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1269a6 7 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x1269ab (StorePre 0x1269ab 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1269ab + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1269ab 7 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x1269b0 (movR64M64Effect 0x1269b0 7 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 69) (.exec 0x1269b0 (LoadPre 0x1269b0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x1269b0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1269b0 7 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.exec 0x1269b5 (StorePre 0x1269b5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1269b5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1269b5 7 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[68, 4]
    (.letOp (n := 71) (.out 0x1269ba (cmpR32Imm8Effect 0x1269ba 3 2 0x2) (EffectPart.reads (.flag .ZF) [.gpr 2] []) (.flag .ZF)) #v[2]
    (.letOp (n := 72) (.exec 0x1269ba (fun s => s.RIP = 0x1269ba) (cmpR32Imm8Effect 0x1269ba 3 2 0x2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 73) (.pure (condOp 5)) #v[71]
    (.terminate (.condBr (Fin.last 73) ⟨.l126866, RegMap.args [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 68), (9, 9), (10, 10), (11, 11), (19, 71), (22, 22), (39, 39), (50, 50), (51, 51)] 74⟩ ⟨.l1269c3, RegMap.args [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 68), (9, 9), (10, 10), (11, 11), (19, 71), (22, 22), (39, 39), (50, 50), (51, 51)] 74⟩))))))))))))))))))))))

def bytes_l126984 : List UInt8 :=
  [0x8B, 0x4C, 0x24, 0x44, 0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x8B, 0x74, 0x24, 0x50, 0x48, 0x8B,
    0x7C, 0x24, 0x58, 0x48, 0x89, 0x7C, 0x24, 0x08, 0x48, 0x8B, 0x7C, 0x24, 0x60, 0x48, 0x89, 0x7C,
    0x24, 0x10, 0x48, 0x8B, 0x7C, 0x24, 0x68, 0x48, 0x89, 0x7C, 0x24, 0x18, 0x48, 0x8B, 0x7C, 0x24,
    0x70, 0x48, 0x89, 0x7C, 0x24, 0x20, 0x83, 0xFA, 0x02, 0x0F, 0x85, 0xA3, 0xFE, 0xFF, 0xFF]

theorem code_l126984 : ∀ x ∈ codeRange 0x126984 bytes_l126984, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26984 63 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1269c3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1269c3 (movR32M32LowEffect 0x1269c3 2 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 54) (.exec 0x1269c3 (LoadPre 0x1269c3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1269c3 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1269c3 2 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x1269c7 (StorePre 0x1269c7 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1269c7 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x1269c7 2 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x1269cb (movR64M64Effect 0x1269cb 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 57) (.exec 0x1269cb (LoadPre 0x1269cb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1269cb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1269cb 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.out 0x1269d0 (movR64M64Effect 0x1269d0 8 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 59) (.exec 0x1269d0 (LoadPre 0x1269d0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1269d0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1269d0 8 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.exec 0x1269d5 (StorePre 0x1269d5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1269d5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1269d5 8 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[58, 4]
    (.letOp (n := 61) (.exec 0x1269da (StorePre 0x1269da 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1269da + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1269da 7 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 62) (.exec 0x1269df (StorePre 0x1269df 3 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x1269df + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x1269df 2 (.base 3 (.d8 0x28))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[53, 3]
    (.letOp (n := 63) (.exec 0x1269e2 (StorePre 0x1269e2 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x1269e2 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1269e2 8 (.base 3 (.d8 0x20))) (Reg.operands [.gpr 8, .gpr 3] [])) #v[58, 3]
    (.letOp (n := 64) (.exec 0x1269e6 (StorePre 0x1269e6 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x1269e6 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1269e6 7 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[56, 3]
    (.letOp (n := 65) (.exec 0x1269ea (StorePre 0x1269ea 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x1269ea + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x1269ea 1 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[1, 3]
    (.letOp (n := 66) (.exec 0x1269ed (StorePre 0x1269ed 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x1269ed + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1269ed 0 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (.letOp (n := 67) (.exec 0x1269f1 (StorePre 0x1269f1 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x1269f1 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1269f1 6 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[6, 3]
    (.letOp (n := 68) (.exec 0x1269f5 (StorePre 0x1269f5 6 (fun s => AddrMode.addr (.base 3 .none) s (0x1269f5 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x1269f5 6 (.base 3 .none) 0x2) (Reg.operands [.gpr 3] [])) #v[3]
    (.terminate (.br ⟨.l1268f9, RegMap.args [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (6, 6), (7, 56), (8, 58), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 69⟩)))))))))))))))))

def bytes_l1269c3 : List UInt8 :=
  [0x8B, 0x54, 0x24, 0x18, 0x89, 0x54, 0x24, 0x38, 0x48, 0x8B, 0x7C, 0x24, 0x08, 0x4C, 0x8B, 0x44,
    0x24, 0x10, 0x4C, 0x89, 0x44, 0x24, 0x30, 0x48, 0x89, 0x7C, 0x24, 0x28, 0x89, 0x53, 0x28, 0x4C,
    0x89, 0x43, 0x20, 0x48, 0x89, 0x7B, 0x18, 0x89, 0x4B, 0x04, 0x48, 0x89, 0x43, 0x08, 0x48, 0x89,
    0x73, 0x10, 0xC7, 0x03, 0x02, 0x00, 0x00, 0x00, 0xE9, 0xF9, 0xFE, 0xFF, 0xFF]

theorem code_l1269c3 : ∀ x ∈ codeRange 0x1269c3 bytes_l1269c3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x269c3 61 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126a00 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x126a00 (StorePre 0x126a00 5 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x126a00 + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x126a00 (.base 14 (.d8 0x20)) 0x1) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 54) (.out 0x126a05 (movR64R64Effect 0x126a05 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[1]
    (.letOp (n := 55) (.exec 0x126a05 (fun s => s.RIP = 0x126a05) (movR64R64Effect 0x126a05 0 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 56) (.out 0x126a08 (shlR64Effect 0x126a08 4 0 32) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[54]
    (.letOp (n := 57) (.exec 0x126a08 (fun s => s.RIP = 0x126a08) (shlR64Effect 0x126a08 4 0 32) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[54]
    (.letOp (n := 58) (.out 0x126a0c (orR64Imm8Effect 0x126a0c 0 0x13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[56]
    (.letOp (n := 59) (.exec 0x126a0c (fun s => s.RIP = 0x126a0c) (orR64Imm8Effect 0x126a0c 0 0x13) (Reg.operands [.gpr 0] [])) #v[56]
    (.letOp (n := 60) (.out 0x126a10 (movR32Imm32Effect 0x126a10 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 61) (.exec 0x126a10 (fun s => s.RIP = 0x126a10) (movR32Imm32Effect 0x126a10 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 62) (.out 0x126a15 (xorR32R32Effect 0x126a15 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[7, 7]
    (.letOp (n := 63) (.exec 0x126a15 (fun s => s.RIP = 0x126a15) (xorR32R32Effect 0x126a15 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[7, 7]
    (.terminate (.br ⟨.l1268a2, RegMap.args [(0, 58), (1, 1), (2, 60), (3, 3), (4, 4), (6, 6), (7, 62), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩))))))))))))

def bytes_l126a00 : List UInt8 :=
  [0x41, 0xC6, 0x46, 0x20, 0x01, 0x48, 0x89, 0xC8, 0x48, 0xC1, 0xE0, 0x20, 0x48, 0x83, 0xC8, 0x13,
    0xBA, 0x01, 0x00, 0x00, 0x00, 0x31, 0xFF, 0xE9, 0x86, 0xFE, 0xFF, 0xFF]

theorem code_l126a00 : ∀ x ∈ codeRange 0x126a00 bytes_l126a00, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26a00 28 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126a1c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126a1c (xorR32R32Effect 0x126a1c 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[2, 2]
    (.letOp (n := 54) (.exec 0x126a1c (fun s => s.RIP = 0x126a1c) (xorR32R32Effect 0x126a1c 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 55) (.out 0x126a1e (movR32Imm32Effect 0x126a1e 5 0 0xc) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 56) (.exec 0x126a1e (fun s => s.RIP = 0x126a1e) (movR32Imm32Effect 0x126a1e 5 0 0xc) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x126a23 (xorR32R32Effect 0x126a23 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[7, 7]
    (.letOp (n := 58) (.exec 0x126a23 (fun s => s.RIP = 0x126a23) (xorR32R32Effect 0x126a23 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[7, 7]
    (.terminate (.br ⟨.l1268a2, RegMap.args [(0, 55), (1, 1), (2, 53), (3, 3), (4, 4), (6, 6), (7, 57), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l126a1c : List UInt8 :=
  [0x31, 0xD2, 0xB8, 0x0C, 0x00, 0x00, 0x00, 0x31, 0xFF, 0xE9, 0x78, 0xFE, 0xFF, 0xFF]

theorem code_l126a1c : ∀ x ∈ codeRange 0x126a1c bytes_l126a1c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26a1c 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126a30 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126a30 (pushR64Effect 0x126a30 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x126a30 (PushPre 0x126a30 1) (pushR64Effect 0x126a30 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x126a31 (pushR64Effect 0x126a31 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x126a31 (PushPre 0x126a31 2) (pushR64Effect 0x126a31 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x126a33 (pushR64Effect 0x126a33 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x126a33 (PushPre 0x126a33 2) (pushR64Effect 0x126a33 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x126a35 (pushR64Effect 0x126a35 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x126a35 (PushPre 0x126a35 2) (pushR64Effect 0x126a35 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x126a37 (pushR64Effect 0x126a37 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x126a37 (PushPre 0x126a37 2) (pushR64Effect 0x126a37 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x126a39 (pushR64Effect 0x126a39 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x126a39 (PushPre 0x126a39 1) (pushR64Effect 0x126a39 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x126a3a (subR64Imm32Effect 0x126a3a 4 0xd8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x126a3a (fun s => s.RIP = 0x126a3a) (subR64Imm32Effect 0x126a3a 4 0xd8) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x126a41 (movR64R64Effect 0x126a41 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 68) (.exec 0x126a41 (fun s => s.RIP = 0x126a41) (movR64R64Effect 0x126a41 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 69) (.out 0x126a44 (movR32M32Effect 0x126a44 15 (.base 6 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 6] []) (.reg (.gpr 15))) #v[6]
    (.letOp (n := 70) (.exec 0x126a44 (LoadPre 0x126a44 (fun s => AddrMode.addr (.base 6 (.d8 0x1c)) s (0x126a44 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x126a44 15 (.base 6 (.d8 0x1c))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 71) (.out 0x126a48 (movR32M32LowEffect 0x126a48 5 (.base 2 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[2]
    (.letOp (n := 72) (.exec 0x126a48 (LoadPre 0x126a48 (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x126a48 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x126a48 5 (.base 2 (.d8 0x8))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 73) (.out 0x126a4b (addR32R32Effect 0x126a4b 3 5 15) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 15] []) (.reg (.gpr 5))) #v[71, 69]
    (.letOp (n := 74) (.out 0x126a4b (addR32R32Effect 0x126a4b 3 5 15) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 15] []) (.flag .CF)) #v[71, 69]
    (.letOp (n := 75) (.exec 0x126a4b (fun s => s.RIP = 0x126a4b) (addR32R32Effect 0x126a4b 3 5 15) (Reg.operands [.gpr 5, .gpr 15] [])) #v[71, 69]
    (.letOp (n := 76) (.pure (condOp 2)) #v[74]
    (.terminate (.condBr (Fin.last 76) ⟨.l126d10, RegMap.args [(1, 1), (2, 2), (3, 67), (4, 65), (5, 73), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 69), (16, 74), (22, 22), (39, 39), (50, 50), (51, 51)] 77⟩ ⟨.l126a54, RegMap.args [(1, 1), (2, 2), (3, 67), (4, 65), (5, 73), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 69), (16, 74), (22, 22), (39, 39), (50, 50), (51, 51)] 77⟩)))))))))))))))))))))))))

def bytes_l126a30 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0xD8, 0x00, 0x00,
    0x00, 0x48, 0x89, 0xFB, 0x44, 0x8B, 0x7E, 0x1C, 0x8B, 0x6A, 0x08, 0x44, 0x01, 0xFD, 0x0F, 0x82,
    0xBC, 0x02, 0x00, 0x00]

theorem code_l126a30 : ∀ x ∈ codeRange 0x126a30 bytes_l126a30, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26a30 36 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126a54 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126a54 (movR64R64Effect 0x126a54 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[2]
    (.letOp (n := 54) (.exec 0x126a54 (fun s => s.RIP = 0x126a54) (movR64R64Effect 0x126a54 13 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 55) (.out 0x126a57 (movR64R64Effect 0x126a57 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 6] []) (.reg (.gpr 14))) #v[6]
    (.letOp (n := 56) (.exec 0x126a57 (fun s => s.RIP = 0x126a57) (movR64R64Effect 0x126a57 14 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 57) (.out 0x126a5a (movR64M64Effect 0x126a5a 6 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[6]
    (.letOp (n := 58) (.exec 0x126a5a (LoadPre 0x126a5a (fun s => AddrMode.addr (.base 6 .none) s (0x126a5a + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x126a5a 6 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 59) (.out 0x126a5d (movR64M64Effect 0x126a5d 12 (.base 14 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 14] []) (.reg (.gpr 12))) #v[55]
    (.letOp (n := 60) (.exec 0x126a5d (LoadPre 0x126a5d (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x126a5d + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x126a5d 12 (.base 14 (.d8 0x8))) (Reg.operands [.gpr 14] [])) #v[55]
    (.letOp (n := 61) (.out 0x126a61 (leaR64Effect 0x126a61 7 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 62) (.exec 0x126a61 (fun s => s.RIP = 0x126a61) (leaR64Effect 0x126a61 7 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x126a66 (StorePre 0x126a66 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x126a66 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x126a66 6 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 64) (.out 0x126a6e (movR64R64Effect 0x126a6e 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12] []) (.reg (.gpr 2))) #v[59]
    (.letOp (n := 65) (.exec 0x126a6e (fun s => s.RIP = 0x126a6e) (movR64R64Effect 0x126a6e 2 12) (Reg.operands [.gpr 12] [])) #v[59]
    (.letOp (n := 66) (.out 0x126a71 (movR32R32Effect 0x126a71 2 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[5]
    (.letOp (n := 67) (.exec 0x126a71 (fun s => s.RIP = 0x126a71) (movR32R32Effect 0x126a71 2 1 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 68) (.out 0x126a73 (callEffect (fun _ => 0x127c50) 0x126a78) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 69) (.exec 0x126a73 (PushPre 0x126a73 5) (callEffect (fun _ => 0x127c50) 0x126a78) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.const ⟨64, 0x126a78⟩) #v[]
    (.terminate (.call ⟨.l127c50, RegMap.args [(1, 66), (2, 64), (3, 3), (4, 68), (5, 5), (6, 57), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 53), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 71⟩ { target := .l126a78, kept := #v[], arity := rfl, guard := some (Fin.last 70) })))))))))))))))))))

def bytes_l126a54 : List UInt8 :=
  [0x49, 0x89, 0xD5, 0x49, 0x89, 0xF6, 0x48, 0x8B, 0x36, 0x4D, 0x8B, 0x66, 0x08, 0x48, 0x8D, 0x7C,
    0x24, 0x48, 0x48, 0x89, 0xB4, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xE2, 0x89, 0xE9, 0xE8,
    0xD8, 0x11, 0x00, 0x00]

theorem code_l126a54 : ∀ x ∈ codeRange 0x126a54 bytes_l126a54, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26a54 36 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126a78 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126a78 (movR32M32LowEffect 0x126a78 2 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 54) (.exec 0x126a78 (LoadPre 0x126a78 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x126a78 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x126a78 2 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x126a7c (cmpR32Imm8Effect 0x126a7c 3 2 0x2) (EffectPart.reads (.flag .ZF) [.gpr 2] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x126a7c (fun s => s.RIP = 0x126a7c) (cmpR32Imm8Effect 0x126a7c 3 2 0x2) (Reg.operands [.gpr 2] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l126aa3, RegMap.args [(2, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l126a81, RegMap.args [(2, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l126a78 : List UInt8 :=
  [0x8B, 0x54, 0x24, 0x48, 0x83, 0xFA, 0x02, 0x75, 0x22]

theorem code_l126a78 : ∀ x ∈ codeRange 0x126a78 bytes_l126a78, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26a78 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126a81 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126a81 (movR64M64Effect 0x126a81 0 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x126a81 (LoadPre 0x126a81 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x126a81 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126a81 0 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x126a86 (movR64M64Effect 0x126a86 1 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x126a86 (LoadPre 0x126a86 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x126a86 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126a86 1 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x126a8b (StorePre 0x126a8b 3 (fun s => AddrMode.addr (.base 14 .none) s (0x126a8b + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x126a8b 0 (.base 14 .none)) (Reg.operands [.gpr 0, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 58) (.exec 0x126a8e (StorePre 0x126a8e 4 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x126a8e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126a8e 1 (.base 14 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x126a92 (movR64M64Effect 0x126a92 0 (.base 14 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[14]
    (.letOp (n := 60) (.exec 0x126a92 (LoadPre 0x126a92 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x126a92 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x126a92 0 (.base 14 (.d8 0x10))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 61) (.out 0x126a96 (cmpR64Imm8Effect 0x126a96 0 0x3f) (EffectPart.reads (.flag .CF) [.gpr 0] []) (.flag .CF)) #v[59]
    (.letOp (n := 62) (.out 0x126a96 (cmpR64Imm8Effect 0x126a96 0 0x3f) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[59]
    (.letOp (n := 63) (.exec 0x126a96 (fun s => s.RIP = 0x126a96) (cmpR64Imm8Effect 0x126a96 0 0x3f) (Reg.operands [.gpr 0] [])) #v[59]
    (.letOp (n := 64) (.pure (condOp 6)) #v[61, 62]
    (.terminate (.condBr (Fin.last 64) ⟨.l126ae8, RegMap.args [(0, 59), (1, 55), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 61), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)] 65⟩ ⟨.l126a9c, RegMap.args [(0, 59), (1, 55), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 61), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)] 65⟩)))))))))))))

def bytes_l126a81 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x50, 0x48, 0x8B, 0x4C, 0x24, 0x58, 0x49, 0x89, 0x06, 0x49, 0x89, 0x4E,
    0x08, 0x49, 0x8B, 0x46, 0x10, 0x48, 0x83, 0xF8, 0x3F, 0x76, 0x4C]

theorem code_l126a81 : ∀ x ∈ codeRange 0x126a81 bytes_l126a81, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26a81 27 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126a9c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126a9c (movR32Imm32Effect 0x126a9c 5 0 0x6) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 54) (.exec 0x126a9c (fun s => s.RIP = 0x126a9c) (movR32Imm32Effect 0x126a9c 5 0 0x6) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l126b08, RegMap.args [(0, 53), (3, 3), (4, 4), (7, 7), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l126a9c : List UInt8 :=
  [0xB8, 0x06, 0x00, 0x00, 0x00, 0xEB, 0x65]

theorem code_l126a9c : ∀ x ∈ codeRange 0x126a9c bytes_l126a9c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26a9c 7 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126aa3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126aa3 (movR32M32LowEffect 0x126aa3 1 (.sib 4 none 0 (.d8 0x4c))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x126aa3 (LoadPre 0x126aa3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4c)) s (0x126aa3 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x126aa3 1 (.sib 4 none 0 (.d8 0x4c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x126aa7 (movR64M64Effect 0x126aa7 0 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 56) (.exec 0x126aa7 (LoadPre 0x126aa7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x126aa7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126aa7 0 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x126aac (movR64M64Effect 0x126aac 6 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 58) (.exec 0x126aac (LoadPre 0x126aac (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x126aac + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126aac 6 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x126ab1 (movR64M64Effect 0x126ab1 7 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 60) (.exec 0x126ab1 (LoadPre 0x126ab1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x126ab1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126ab1 7 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x126ab6 (StorePre 0x126ab6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x126ab6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126ab6 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x126abb (movR64M64Effect 0x126abb 7 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 63) (.exec 0x126abb (LoadPre 0x126abb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x126abb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126abb 7 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x126ac0 (StorePre 0x126ac0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x126ac0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126ac0 7 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x126ac5 (movR64M64Effect 0x126ac5 7 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 66) (.exec 0x126ac5 (LoadPre 0x126ac5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x126ac5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126ac5 7 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x126aca (StorePre 0x126aca 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x126aca + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126aca 7 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x126acf (movR64M64Effect 0x126acf 7 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 69) (.exec 0x126acf (LoadPre 0x126acf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x126acf + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126acf 7 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.exec 0x126ad4 (StorePre 0x126ad4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x126ad4 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126ad4 7 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[68, 4]
    (.terminate (.br ⟨.l126ad9, RegMap.args [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 68), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 71⟩)))))))))))))))))))

def bytes_l126aa3 : List UInt8 :=
  [0x8B, 0x4C, 0x24, 0x4C, 0x48, 0x8B, 0x44, 0x24, 0x50, 0x48, 0x8B, 0x74, 0x24, 0x58, 0x48, 0x8B,
    0x7C, 0x24, 0x60, 0x48, 0x89, 0x7C, 0x24, 0x08, 0x48, 0x8B, 0x7C, 0x24, 0x68, 0x48, 0x89, 0x7C,
    0x24, 0x10, 0x48, 0x8B, 0x7C, 0x24, 0x70, 0x48, 0x89, 0x7C, 0x24, 0x18, 0x48, 0x8B, 0x7C, 0x24,
    0x78, 0x48, 0x89, 0x7C, 0x24, 0x20]

theorem code_l126aa3 : ∀ x ∈ codeRange 0x126aa3 bytes_l126aa3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26aa3 54 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126ad9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126ad9 (movR64Imm64Effect 0x126ad9 7 0xffffffff00000000) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 54) (.exec 0x126ad9 (fun s => s.RIP = 0x126ad9) (movR64Imm64Effect 0x126ad9 7 0xffffffff00000000) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x126ae3 (andR64R64Effect 0x126ae3 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[53, 6]
    (.letOp (n := 56) (.exec 0x126ae3 (fun s => s.RIP = 0x126ae3) (andR64R64Effect 0x126ae3 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[53, 6]
    (.terminate (.br ⟨.l126b15, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 55), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l126ad9 : List UInt8 :=
  [0x48, 0xBF, 0x00, 0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF, 0x48, 0x21, 0xF7, 0xEB, 0x2D]

theorem code_l126ad9 : ∀ x ∈ codeRange 0x126ad9 bytes_l126ad9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26ad9 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126ae8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126ae8 (incR64Effect 0x126ae8 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 54) (.exec 0x126ae8 (fun s => s.RIP = 0x126ae8) (incR64Effect 0x126ae8 0) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[0]
    (.letOp (n := 55) (.exec 0x126aeb (StorePre 0x126aeb 4 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x126aeb + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126aeb 0 (.base 14 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 56) (.out 0x126aef (movR32M32Effect 0x126aef 15 (.base 14 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 14] []) (.reg (.gpr 15))) #v[14]
    (.letOp (n := 57) (.exec 0x126aef (LoadPre 0x126aef (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x126aef + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x126aef 15 (.base 14 (.d8 0x18))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 58) (.out 0x126af3 (cmpR32R32Effect 0x126af3 3 5 15) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 15] []) (.flag .CF)) #v[5, 56]
    (.letOp (n := 59) (.out 0x126af3 (cmpR32R32Effect 0x126af3 3 5 15) (EffectPart.reads (.flag .ZF) [.gpr 5, .gpr 15] []) (.flag .ZF)) #v[5, 56]
    (.letOp (n := 60) (.exec 0x126af3 (fun s => s.RIP = 0x126af3) (cmpR32R32Effect 0x126af3 3 5 15) (Reg.operands [.gpr 5, .gpr 15] [])) #v[5, 56]
    (.letOp (n := 61) (.pure (condOp 6)) #v[58, 59]
    (.terminate (.condBr (Fin.last 61) ⟨.l126b7c, RegMap.args [(0, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 56), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ ⟨.l126afc, RegMap.args [(0, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 56), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩))))))))))

def bytes_l126ae8 : List UInt8 :=
  [0x48, 0xFF, 0xC0, 0x49, 0x89, 0x46, 0x10, 0x45, 0x8B, 0x7E, 0x18, 0x44, 0x39, 0xFD, 0x0F, 0x86,
    0x80, 0x00, 0x00, 0x00]

theorem code_l126ae8 : ∀ x ∈ codeRange 0x126ae8 bytes_l126ae8, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26ae8 20 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126afc : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126afc (leaR32Effect 0x126afc 4 0 (.base 15 (.d8 0x1))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[15]
    (.letOp (n := 54) (.exec 0x126afc (fun s => s.RIP = 0x126afc) (leaR32Effect 0x126afc 4 0 (.base 15 (.d8 0x1))) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.out 0x126b00 (shlR64Effect 0x126b00 4 0 32) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x126b00 (fun s => s.RIP = 0x126b00) (shlR64Effect 0x126b00 4 0 32) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 57) (.out 0x126b04 (orR64Imm8Effect 0x126b04 0 0x3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[55]
    (.letOp (n := 58) (.exec 0x126b04 (fun s => s.RIP = 0x126b04) (orR64Imm8Effect 0x126b04 0 0x3) (Reg.operands [.gpr 0] [])) #v[55]
    (.terminate (.br ⟨.l126b08, RegMap.args [(0, 57), (3, 3), (4, 4), (7, 7), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l126afc : List UInt8 :=
  [0x41, 0x8D, 0x47, 0x01, 0x48, 0xC1, 0xE0, 0x20, 0x48, 0x83, 0xC8, 0x03]

theorem code_l126afc : ∀ x ∈ codeRange 0x126afc bytes_l126afc, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26afc 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126b08 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126b08 (movR32Imm32Effect 0x126b08 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 54) (.exec 0x126b08 (fun s => s.RIP = 0x126b08) (movR32Imm32Effect 0x126b08 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x126b0d (xorR32R32Effect 0x126b0d 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[7, 7]
    (.letOp (n := 56) (.exec 0x126b0d (fun s => s.RIP = 0x126b0d) (xorR32R32Effect 0x126b0d 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[7, 7]
    (.letOp (n := 57) (.out 0x126b0f (movR32R32Effect 0x126b0f 3 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 15] []) (.reg (.gpr 1))) #v[15]
    (.letOp (n := 58) (.exec 0x126b0f (fun s => s.RIP = 0x126b0f) (movR32R32Effect 0x126b0f 3 1 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 59) (.out 0x126b12 (movR32R32Effect 0x126b12 3 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 60) (.exec 0x126b12 (fun s => s.RIP = 0x126b12) (movR32R32Effect 0x126b12 3 6 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.terminate (.br ⟨.l126b15, RegMap.args [(0, 0), (1, 57), (2, 53), (3, 3), (4, 4), (6, 59), (7, 55), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩)))))))))

def bytes_l126b08 : List UInt8 :=
  [0xBA, 0x01, 0x00, 0x00, 0x00, 0x31, 0xFF, 0x44, 0x89, 0xF9, 0x44, 0x89, 0xFE]

theorem code_l126b08 : ∀ x ∈ codeRange 0x126b08 bytes_l126b08, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26b08 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126b15 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126b15 (movR32R32Effect 0x126b15 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[6]
    (.letOp (n := 54) (.exec 0x126b15 (fun s => s.RIP = 0x126b15) (movR32R32Effect 0x126b15 2 6 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 55) (.out 0x126b17 (orR64R64Effect 0x126b17 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7] []) (.reg (.gpr 6))) #v[53, 7]
    (.letOp (n := 56) (.exec 0x126b17 (fun s => s.RIP = 0x126b17) (orR64R64Effect 0x126b17 6 7) (Reg.operands [.gpr 6, .gpr 7] [])) #v[53, 7]
    (.letOp (n := 57) (.out 0x126b1a (movR64M64Effect 0x126b1a 7 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 58) (.exec 0x126b1a (LoadPre 0x126b1a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x126b1a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126b1a 7 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.exec 0x126b1f (StorePre 0x126b1f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x126b1f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126b1f 7 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 60) (.out 0x126b24 (movR64M64Effect 0x126b24 8 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 61) (.exec 0x126b24 (LoadPre 0x126b24 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x126b24 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126b24 8 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.exec 0x126b29 (StorePre 0x126b29 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x126b29 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126b29 8 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[60, 4]
    (.letOp (n := 63) (.out 0x126b2e (movR64M64Effect 0x126b2e 9 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 64) (.exec 0x126b2e (LoadPre 0x126b2e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x126b2e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126b2e 9 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x126b33 (movR64M64Effect 0x126b33 10 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 66) (.exec 0x126b33 (LoadPre 0x126b33 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x126b33 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126b33 10 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x126b38 (StorePre 0x126b38 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x126b38 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126b38 10 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.exec 0x126b3d (StorePre 0x126b3d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x126b3d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126b3d 9 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[63, 4]
    (.letOp (n := 69) (.exec 0x126b42 (StorePre 0x126b42 4 (fun s => AddrMode.addr (.base 3 (.d8 0x38)) s (0x126b42 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126b42 7 (.base 3 (.d8 0x38))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[57, 3]
    (.letOp (n := 70) (.exec 0x126b46 (StorePre 0x126b46 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x126b46 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126b46 8 (.base 3 (.d8 0x30))) (Reg.operands [.gpr 8, .gpr 3] [])) #v[60, 3]
    (.letOp (n := 71) (.exec 0x126b4a (StorePre 0x126b4a 4 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x126b4a + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126b4a 10 (.base 3 (.d8 0x28))) (Reg.operands [.gpr 10, .gpr 3] [])) #v[65, 3]
    (.letOp (n := 72) (.exec 0x126b4e (StorePre 0x126b4e 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x126b4e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126b4e 9 (.base 3 (.d8 0x20))) (Reg.operands [.gpr 9, .gpr 3] [])) #v[63, 3]
    (.letOp (n := 73) (.exec 0x126b52 (StorePre 0x126b52 3 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x126b52 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x126b52 2 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[2, 3]
    (.letOp (n := 74) (.exec 0x126b55 (StorePre 0x126b55 3 (fun s => AddrMode.addr (.base 3 (.d8 0xc)) s (0x126b55 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x126b55 1 (.base 3 (.d8 0xc))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[1, 3]
    (.letOp (n := 75) (.exec 0x126b58 (StorePre 0x126b58 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x126b58 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126b58 0 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (.letOp (n := 76) (.exec 0x126b5c (StorePre 0x126b5c 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x126b5c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126b5c 6 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[55, 3]
    (.letOp (n := 77) (.exec 0x126b60 (StorePre 0x126b60 7 (fun s => AddrMode.addr (.base 3 .none) s (0x126b60 + BitVec.ofNat 64 7)) 8) (movM64Imm32Effect 0x126b60 (.base 3 .none) 0x1) (Reg.operands [.gpr 3] [])) #v[3]
    (.terminate (.br ⟨.l126b67, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 57), (8, 60), (9, 63), (10, 65), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 78⟩))))))))))))))))))))))))))

def bytes_l126b15 : List UInt8 :=
  [0x89, 0xF6, 0x48, 0x09, 0xFE, 0x48, 0x8B, 0x7C, 0x24, 0x20, 0x48, 0x89, 0x7C, 0x24, 0x40, 0x4C,
    0x8B, 0x44, 0x24, 0x18, 0x4C, 0x89, 0x44, 0x24, 0x38, 0x4C, 0x8B, 0x4C, 0x24, 0x08, 0x4C, 0x8B,
    0x54, 0x24, 0x10, 0x4C, 0x89, 0x54, 0x24, 0x30, 0x4C, 0x89, 0x4C, 0x24, 0x28, 0x48, 0x89, 0x7B,
    0x38, 0x4C, 0x89, 0x43, 0x30, 0x4C, 0x89, 0x53, 0x28, 0x4C, 0x89, 0x4B, 0x20, 0x89, 0x53, 0x08,
    0x89, 0x4B, 0x0C, 0x48, 0x89, 0x43, 0x10, 0x48, 0x89, 0x73, 0x18, 0x48, 0xC7, 0x03, 0x01, 0x00,
    0x00, 0x00]

theorem code_l126b15 : ∀ x ∈ codeRange 0x126b15 bytes_l126b15, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26b15 82 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126b67 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126b67 (movR64R64Effect 0x126b67 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 54) (.exec 0x126b67 (fun s => s.RIP = 0x126b67) (movR64R64Effect 0x126b67 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x126b6a (addR64Imm32Effect 0x126b6a 4 0xd8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 56) (.exec 0x126b6a (fun s => s.RIP = 0x126b6a) (addR64Imm32Effect 0x126b6a 4 0xd8) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x126b71 (popR64Effect 0x126b71 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[55]
    (.letOp (n := 58) (.out 0x126b71 (popR64Effect 0x126b71 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[55]
    (.letOp (n := 59) (.exec 0x126b71 (PopPre 0x126b71) (popR64Effect 0x126b71 1 3) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 60) (.out 0x126b72 (popR64Effect 0x126b72 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[58]
    (.letOp (n := 61) (.out 0x126b72 (popR64Effect 0x126b72 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[58]
    (.letOp (n := 62) (.exec 0x126b72 (PopPre 0x126b72) (popR64Effect 0x126b72 2 12) (Reg.operands [.gpr 4] [])) #v[58]
    (.letOp (n := 63) (.out 0x126b74 (popR64Effect 0x126b74 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[61]
    (.letOp (n := 64) (.out 0x126b74 (popR64Effect 0x126b74 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 65) (.exec 0x126b74 (PopPre 0x126b74) (popR64Effect 0x126b74 2 13) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 66) (.out 0x126b76 (popR64Effect 0x126b76 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[64]
    (.letOp (n := 67) (.out 0x126b76 (popR64Effect 0x126b76 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[64]
    (.letOp (n := 68) (.exec 0x126b76 (PopPre 0x126b76) (popR64Effect 0x126b76 2 14) (Reg.operands [.gpr 4] [])) #v[64]
    (.letOp (n := 69) (.out 0x126b78 (popR64Effect 0x126b78 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[67]
    (.letOp (n := 70) (.out 0x126b78 (popR64Effect 0x126b78 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[67]
    (.letOp (n := 71) (.exec 0x126b78 (PopPre 0x126b78) (popR64Effect 0x126b78 2 15) (Reg.operands [.gpr 4] [])) #v[67]
    (.letOp (n := 72) (.out 0x126b7a (popR64Effect 0x126b7a 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[70]
    (.letOp (n := 73) (.out 0x126b7a (popR64Effect 0x126b7a 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[70]
    (.letOp (n := 74) (.exec 0x126b7a (PopPre 0x126b7a) (popR64Effect 0x126b7a 1 5) (Reg.operands [.gpr 4] [])) #v[70]
    (.letOp (n := 75) (.out 0x126b7b (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[73]
    (.letOp (n := 76) (.out 0x126b7b (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[73]
    (.letOp (n := 77) (.exec 0x126b7b (RetPre 0x126b7b) (retEffect) (Reg.operands [.gpr 4] [])) #v[73]
    (.terminate (.ret (RegMap.args [(0, 53), (1, 1), (2, 2), (3, 57), (4, 76), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 78) (some ⟨75, by decide⟩)))))))))))))))))))))))))))

def bytes_l126b67 : List UInt8 :=
  [0x48, 0x89, 0xD8, 0x48, 0x81, 0xC4, 0xD8, 0x00, 0x00, 0x00, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41,
    0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l126b67 : ∀ x ∈ codeRange 0x126b67 bytes_l126b67, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26b67 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126b7c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x126b7c (StorePre 0x126b7c 4 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x126b7c + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x126b7c 5 (.base 14 (.d8 0x18))) (Reg.operands [.gpr 5, .gpr 14] [])) #v[5, 14]
    (.letOp (n := 54) (.exec 0x126b80 (fun s => s.RIP = 0x126b80) (leaR64Effect 0x126b80 2 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x126b88 (movR64M64Effect 0x126b88 0 (.base 13 (.d8 0x0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[13]
    (.letOp (n := 56) (.exec 0x126b88 (LoadPre 0x126b88 (fun s => AddrMode.addr (.base 13 (.d8 0x0)) s (0x126b88 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x126b88 0 (.base 13 (.d8 0x0))) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 57) (.out 0x126b8c (movR64M64Effect 0x126b8c 1 (.base 13 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 13] []) (.reg (.gpr 1))) #v[13]
    (.letOp (n := 58) (.exec 0x126b8c (LoadPre 0x126b8c (fun s => AddrMode.addr (.base 13 (.d8 0x8)) s (0x126b8c + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x126b8c 1 (.base 13 (.d8 0x8))) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 59) (.exec 0x126b90 (StorePre 0x126b90 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x126b90 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x126b90 1 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 60) (.exec 0x126b98 (StorePre 0x126b98 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x126b98 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x126b98 0 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 61) (.exec 0x126ba0 (StorePre 0x126ba0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x126ba0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x126ba0 14 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[14, 4]
    (.letOp (n := 62) (.out 0x126ba8 (leaR64Effect 0x126ba8 7 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 63) (.exec 0x126ba8 (fun s => s.RIP = 0x126ba8) (leaR64Effect 0x126ba8 7 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x126bad (movR64R64Effect 0x126bad 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 65) (.exec 0x126bad (fun s => s.RIP = 0x126bad) (movR64R64Effect 0x126bad 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 66) (.out 0x126bb0 (callEffect (fun _ => 0x124de0) 0x126bb5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 67) (.exec 0x126bb0 (PushPre 0x126bb0 5) (callEffect (fun _ => 0x124de0) 0x126bb5) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.const ⟨64, 0x126bb5⟩) #v[]
    (.terminate (.call ⟨.l124de0, RegMap.args [(0, 55), (1, 57), (3, 3), (4, 66), (5, 5), (6, 64), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 69⟩ { target := .l126bb5, kept := #v[], arity := rfl, guard := some (Fin.last 68) })))))))))))))))))

def bytes_l126b7c : List UInt8 :=
  [0x41, 0x89, 0x6E, 0x18, 0x48, 0x8D, 0x94, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x49, 0x8B, 0x45, 0x00,
    0x49, 0x8B, 0x4D, 0x08, 0x48, 0x89, 0x8C, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24,
    0xC8, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xB4, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x7C, 0x24,
    0x48, 0x4C, 0x89, 0xF6, 0xE8, 0x2B, 0xE2, 0xFF, 0xFF]

theorem code_l126b7c : ∀ x ∈ codeRange 0x126b7c bytes_l126b7c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26b7c 57 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126bb5 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126bb5 (movR32M32Effect 0x126bb5 6 (.base 14 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 54) (.exec 0x126bb5 (LoadPre 0x126bb5 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x126bb5 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x126bb5 6 (.base 14 (.d8 0x18))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 55) (.out 0x126bb9 (movR32M32Effect 0x126bb9 1 (.base 14 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[14]
    (.letOp (n := 56) (.exec 0x126bb9 (LoadPre 0x126bb9 (fun s => AddrMode.addr (.base 14 (.d8 0x1c)) s (0x126bb9 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x126bb9 1 (.base 14 (.d8 0x1c))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x126bbd (subR32R32Effect 0x126bbd 2 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[53, 55]
    (.letOp (n := 58) (.out 0x126bbd (subR32R32Effect 0x126bbd 2 6 1) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 1] []) (.flag .CF)) #v[53, 55]
    (.letOp (n := 59) (.out 0x126bbd (subR32R32Effect 0x126bbd 2 6 1) (EffectPart.reads (.flag .ZF) [.gpr 6, .gpr 1] []) (.flag .ZF)) #v[53, 55]
    (.letOp (n := 60) (.exec 0x126bbd (fun s => s.RIP = 0x126bbd) (subR32R32Effect 0x126bbd 2 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[53, 55]
    (.letOp (n := 61) (.out 0x126bbf (atFlags (condHolds 6) (setccR8Effect 0x126bbf 3 0)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF]) (.reg (.gpr 0))) #v[0, 58, 59]
    (.letOp (n := 62) (.exec 0x126bbf (fun s => s.RIP = 0x126bbf) (atFlags (condHolds 6) (setccR8Effect 0x126bbf 3 0)) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF])) #v[0, 58, 59]
    (.letOp (n := 63) (.out 0x126bc2 (movR64M64Effect 0x126bc2 2 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 64) (.exec 0x126bc2 (LoadPre 0x126bc2 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x126bc2 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x126bc2 2 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.exec 0x126bca (StorePre 0x126bca 3 (fun s => AddrMode.addr (.base 14 .none) s (0x126bca + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x126bca 2 (.base 14 .none)) (Reg.operands [.gpr 2, .gpr 14] [])) #v[63, 14]
    (.letOp (n := 66) (.exec 0x126bcd (StorePre 0x126bcd 4 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x126bcd + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126bcd 12 (.base 14 (.d8 0x8))) (Reg.operands [.gpr 12, .gpr 14] [])) #v[12, 14]
    (.letOp (n := 67) (.exec 0x126bd1 (StorePre 0x126bd1 4 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x126bd1 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x126bd1 15 (.base 14 (.d8 0x18))) (Reg.operands [.gpr 15, .gpr 14] [])) #v[15, 14]
    (.letOp (n := 68) (.out 0x126bd5 (movR64M64Effect 0x126bd5 2 (.base 14 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14] []) (.reg (.gpr 2))) #v[14]
    (.letOp (n := 69) (.exec 0x126bd5 (LoadPre 0x126bd5 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x126bd5 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x126bd5 2 (.base 14 (.d8 0x10))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 70) (.out 0x126bd9 (cmpR64Imm8Effect 0x126bd9 2 0x1) (EffectPart.reads (.flag .CF) [.gpr 2] []) (.flag .CF)) #v[68]
    (.letOp (n := 71) (.exec 0x126bd9 (fun s => s.RIP = 0x126bd9) (cmpR64Imm8Effect 0x126bd9 2 0x1) (Reg.operands [.gpr 2] [])) #v[68]
    (.letOp (n := 72) (.out 0x126bdd (atFlags StatusFlags.CF (adcR64Imm8Effect 0x126bdd 2 0xff)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[68, 70]
    (.letOp (n := 73) (.exec 0x126bdd (fun s => s.RIP = 0x126bdd) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x126bdd 2 0xff)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[68, 70]
    (.letOp (n := 74) (.exec 0x126be1 (StorePre 0x126be1 4 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x126be1 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126be1 2 (.base 14 (.d8 0x10))) (Reg.operands [.gpr 2, .gpr 14] [])) #v[72, 14]
    (.letOp (n := 75) (.out 0x126be5 (movR64M64Effect 0x126be5 7 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 76) (.exec 0x126be5 (LoadPre 0x126be5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x126be5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126be5 7 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 77) (.out 0x126bea (movR32R32Effect 0x126bea 2 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7] []) (.reg (.gpr 2))) #v[75]
    (.letOp (n := 78) (.exec 0x126bea (fun s => s.RIP = 0x126bea) (movR32R32Effect 0x126bea 2 2 7) (Reg.operands [.gpr 7] [])) #v[75]
    (.letOp (n := 79) (.out 0x126bec (orR8R8Effect 0x126bec 2 2 0) (EffectPart.reads (.flag .ZF) [.gpr 2, .gpr 0] []) (.flag .ZF)) #v[77, 61]
    (.letOp (n := 80) (.exec 0x126bec (fun s => s.RIP = 0x126bec) (orR8R8Effect 0x126bec 2 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[77, 61]
    (.letOp (n := 81) (.pure (condOp 4)) #v[79]
    (.terminate (.condBr (Fin.last 81) ⟨.l126cf4, RegMap.args [(0, 61), (1, 55), (3, 3), (4, 4), (6, 57), (7, 75), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 79), (22, 22), (39, 39), (50, 50), (51, 51)] 82⟩ ⟨.l126bf4, RegMap.args [(0, 61), (1, 55), (3, 3), (4, 4), (6, 57), (7, 75), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 79), (22, 22), (39, 39), (50, 50), (51, 51)] 82⟩))))))))))))))))))))))))))))))

def bytes_l126bb5 : List UInt8 :=
  [0x41, 0x8B, 0x76, 0x18, 0x41, 0x8B, 0x4E, 0x1C, 0x29, 0xCE, 0x0F, 0x96, 0xC0, 0x48, 0x8B, 0x94,
    0x24, 0xA0, 0x00, 0x00, 0x00, 0x49, 0x89, 0x16, 0x4D, 0x89, 0x66, 0x08, 0x45, 0x89, 0x7E, 0x18,
    0x49, 0x8B, 0x56, 0x10, 0x48, 0x83, 0xFA, 0x01, 0x48, 0x83, 0xD2, 0xFF, 0x49, 0x89, 0x56, 0x10,
    0x48, 0x8B, 0x7C, 0x24, 0x48, 0x89, 0xFA, 0x08, 0xC2, 0x0F, 0x84, 0x00, 0x01, 0x00, 0x00]

theorem code_l126bb5 : ∀ x ∈ codeRange 0x126bb5 bytes_l126bb5, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26bb5 63 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126bf4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126bf4 (movR32M32LowEffect 0x126bf4 2 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 54) (.exec 0x126bf4 (LoadPre 0x126bf4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x126bf4 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x126bf4 2 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x126bf8 (movR32M32LowEffect 0x126bf8 1 (.sib 4 none 0 (.d8 0x54))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x126bf8 (LoadPre 0x126bf8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x54)) s (0x126bf8 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x126bf8 1 (.sib 4 none 0 (.d8 0x54))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x126bfc (movR64M64Effect 0x126bfc 0 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 58) (.exec 0x126bfc (LoadPre 0x126bfc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x126bfc + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126bfc 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x126c01 (movR64M64Effect 0x126c01 6 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 60) (.exec 0x126c01 (LoadPre 0x126c01 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x126c01 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126c01 6 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x126c06 (movR64M64Effect 0x126c06 8 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 62) (.exec 0x126c06 (LoadPre 0x126c06 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x126c06 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126c06 8 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x126c0b (StorePre 0x126c0b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x126c0b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126c0b 8 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.out 0x126c10 (movR64M64Effect 0x126c10 8 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 65) (.exec 0x126c10 (LoadPre 0x126c10 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x126c10 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126c10 8 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x126c15 (StorePre 0x126c15 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x126c15 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126c15 8 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.out 0x126c1a (movR64M64Effect 0x126c1a 8 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 68) (.exec 0x126c1a (LoadPre 0x126c1a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x126c1a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126c1a 8 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.exec 0x126c1f (StorePre 0x126c1f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x126c1f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126c1f 8 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[67, 4]
    (.letOp (n := 70) (.out 0x126c24 (movR64M64Effect 0x126c24 8 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 71) (.exec 0x126c24 (LoadPre 0x126c24 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x126c24 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x126c24 8 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.exec 0x126c2c (StorePre 0x126c2c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x126c2c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126c2c 8 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[70, 4]
    (.letOp (n := 73) (.out 0x126c31 (movR64M64Effect 0x126c31 8 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 74) (.exec 0x126c31 (LoadPre 0x126c31 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x126c31 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x126c31 8 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.exec 0x126c39 (StorePre 0x126c39 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x126c39 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x126c39 8 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[73, 4]
    (.letOp (n := 76) (.out 0x126c41 (movR64M64Effect 0x126c41 8 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 77) (.exec 0x126c41 (LoadPre 0x126c41 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x126c41 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x126c41 8 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 78) (.exec 0x126c49 (StorePre 0x126c49 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x126c49 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x126c49 8 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[76, 4]
    (.letOp (n := 79) (.out 0x126c51 (movR64M64Effect 0x126c51 8 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 80) (.exec 0x126c51 (LoadPre 0x126c51 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x126c51 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x126c51 8 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 81) (.exec 0x126c59 (StorePre 0x126c59 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x126c59 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x126c59 8 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[79, 4]
    (.letOp (n := 82) (.out 0x126c61 (testR64R64Effect 0x126c61 7 7) (EffectPart.reads (.flag .ZF) [.gpr 7, .gpr 7] []) (.flag .ZF)) #v[7, 7]
    (.letOp (n := 83) (.exec 0x126c61 (fun s => s.RIP = 0x126c61) (testR64R64Effect 0x126c61 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[7, 7]
    (.letOp (n := 84) (.pure (condOp 5)) #v[82]
    (.terminate (.condBr (Fin.last 84) ⟨.l126ad9, RegMap.args [(0, 57), (1, 55), (2, 53), (3, 3), (4, 4), (6, 59), (7, 7), (8, 79), (9, 9), (10, 10), (11, 11), (19, 82), (22, 22), (39, 39), (50, 50), (51, 51)] 85⟩ ⟨.l126c6a, RegMap.args [(0, 57), (1, 55), (2, 53), (3, 3), (4, 4), (6, 59), (7, 7), (8, 79), (9, 9), (10, 10), (11, 11), (19, 82), (22, 22), (39, 39), (50, 50), (51, 51)] 85⟩)))))))))))))))))))))))))))))))))

def bytes_l126bf4 : List UInt8 :=
  [0x8B, 0x54, 0x24, 0x50, 0x8B, 0x4C, 0x24, 0x54, 0x48, 0x8B, 0x44, 0x24, 0x58, 0x48, 0x8B, 0x74,
    0x24, 0x60, 0x4C, 0x8B, 0x44, 0x24, 0x68, 0x4C, 0x89, 0x44, 0x24, 0x08, 0x4C, 0x8B, 0x44, 0x24,
    0x70, 0x4C, 0x89, 0x44, 0x24, 0x10, 0x4C, 0x8B, 0x44, 0x24, 0x78, 0x4C, 0x89, 0x44, 0x24, 0x18,
    0x4C, 0x8B, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x4C, 0x89, 0x44, 0x24, 0x20, 0x4C, 0x8B, 0x84,
    0x24, 0x88, 0x00, 0x00, 0x00, 0x4C, 0x89, 0x84, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x4C, 0x8B, 0x84,
    0x24, 0x90, 0x00, 0x00, 0x00, 0x4C, 0x89, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x4C, 0x8B, 0x84,
    0x24, 0x98, 0x00, 0x00, 0x00, 0x4C, 0x89, 0x84, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x48, 0x85, 0xFF,
    0x0F, 0x85, 0x6F, 0xFE, 0xFF, 0xFF]

theorem code_l126bf4 : ∀ x ∈ codeRange 0x126bf4 bytes_l126bf4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26bf4 118 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126c6a_1 : Block Op Label signature Reg.count 84 :=
  .letOp (n := 84) (.exec 0x126cd2 (StorePre 0x126cd2 4 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x126cd2 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126cd2 8 (.base 3 (.d8 0x28))) (Reg.operands [.gpr 8, .gpr 3] [])) #v[82, 3]
    (.letOp (n := 85) (.exec 0x126cd6 (StorePre 0x126cd6 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x126cd6 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126cd6 7 (.base 3 (.d8 0x20))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[80, 3]
    (.letOp (n := 86) (.exec 0x126cda (StorePre 0x126cda 3 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x126cda + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x126cda 2 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[2, 3]
    (.letOp (n := 87) (.exec 0x126cdd (StorePre 0x126cdd 3 (fun s => AddrMode.addr (.base 3 (.d8 0xc)) s (0x126cdd + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x126cdd 1 (.base 3 (.d8 0xc))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[1, 3]
    (.letOp (n := 88) (.exec 0x126ce0 (StorePre 0x126ce0 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x126ce0 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126ce0 0 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (.letOp (n := 89) (.exec 0x126ce4 (StorePre 0x126ce4 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x126ce4 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126ce4 6 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[6, 3]
    (.letOp (n := 90) (.exec 0x126ce8 (StorePre 0x126ce8 7 (fun s => AddrMode.addr (.base 3 .none) s (0x126ce8 + BitVec.ofNat 64 7)) 8) (movM64Imm32Effect 0x126ce8 (.base 3 .none) 0x0) (Reg.operands [.gpr 3] [])) #v[3]
    (.terminate (.br ⟨.l126b67, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 80), (8, 82), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 91⟩))))))))

def bytes_l126c6a_1 : List UInt8 :=
  [0x4C, 0x89, 0x43, 0x28, 0x48, 0x89, 0x7B, 0x20, 0x89, 0x53, 0x08, 0x89, 0x4B, 0x0C, 0x48, 0x89,
    0x43, 0x10, 0x48, 0x89, 0x73, 0x18, 0x48, 0xC7, 0x03, 0x00, 0x00, 0x00, 0x00, 0xE9, 0x73, 0xFE,
    0xFF, 0xFF]

theorem code_l126c6a_1 : ∀ x ∈ codeRange 0x126cd2 bytes_l126c6a_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26cd2 34 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126c6a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126c6a (movR64M64Effect 0x126c6a 7 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x126c6a (LoadPre 0x126c6a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x126c6a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126c6a 7 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x126c6f (StorePre 0x126c6f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x126c6f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126c6f 7 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x126c74 (movR64M64Effect 0x126c74 7 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 57) (.exec 0x126c74 (LoadPre 0x126c74 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x126c74 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126c74 7 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x126c79 (StorePre 0x126c79 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x126c79 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126c79 7 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x126c7e (movR64M64Effect 0x126c7e 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 60) (.exec 0x126c7e (LoadPre 0x126c7e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x126c7e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126c7e 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x126c83 (movR64M64Effect 0x126c83 8 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 62) (.exec 0x126c83 (LoadPre 0x126c83 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x126c83 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126c83 8 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x126c88 (StorePre 0x126c88 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x126c88 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126c88 8 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.exec 0x126c8d (StorePre 0x126c8d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x126c8d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126c8d 7 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 65) (.out 0x126c92 (movR64M64Effect 0x126c92 7 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 66) (.exec 0x126c92 (LoadPre 0x126c92 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x126c92 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x126c92 7 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x126c9a (StorePre 0x126c9a 4 (fun s => AddrMode.addr (.base 3 (.d8 0x50)) s (0x126c9a + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126c9a 7 (.base 3 (.d8 0x50))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[65, 3]
    (.letOp (n := 68) (.out 0x126c9e (movR64M64Effect 0x126c9e 7 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 69) (.exec 0x126c9e (LoadPre 0x126c9e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x126c9e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x126c9e 7 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.out 0x126ca6 (movR64M64Effect 0x126ca6 8 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 71) (.exec 0x126ca6 (LoadPre 0x126ca6 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x126ca6 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x126ca6 8 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.exec 0x126cae (StorePre 0x126cae 4 (fun s => AddrMode.addr (.base 3 (.d8 0x48)) s (0x126cae + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126cae 8 (.base 3 (.d8 0x48))) (Reg.operands [.gpr 8, .gpr 3] [])) #v[70, 3]
    (.letOp (n := 73) (.exec 0x126cb2 (StorePre 0x126cb2 4 (fun s => AddrMode.addr (.base 3 (.d8 0x40)) s (0x126cb2 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126cb2 7 (.base 3 (.d8 0x40))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[68, 3]
    (.letOp (n := 74) (.out 0x126cb6 (movR64M64Effect 0x126cb6 7 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 75) (.exec 0x126cb6 (LoadPre 0x126cb6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x126cb6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126cb6 7 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 76) (.exec 0x126cbb (StorePre 0x126cbb 4 (fun s => AddrMode.addr (.base 3 (.d8 0x38)) s (0x126cbb + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126cbb 7 (.base 3 (.d8 0x38))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[74, 3]
    (.letOp (n := 77) (.out 0x126cbf (movR64M64Effect 0x126cbf 7 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 78) (.exec 0x126cbf (LoadPre 0x126cbf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x126cbf + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126cbf 7 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.exec 0x126cc4 (StorePre 0x126cc4 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x126cc4 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126cc4 7 (.base 3 (.d8 0x30))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[77, 3]
    (.letOp (n := 80) (.out 0x126cc8 (movR64M64Effect 0x126cc8 7 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 81) (.exec 0x126cc8 (LoadPre 0x126cc8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x126cc8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126cc8 7 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 82) (.out 0x126ccd (movR64M64Effect 0x126ccd 8 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 83) (.exec 0x126ccd (LoadPre 0x126ccd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x126ccd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126ccd 8 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l126c6a_1)))))))))))))))))))))))))))))))

def bytes_l126c6a : List UInt8 :=
  [0x48, 0x8B, 0x7C, 0x24, 0x20, 0x48, 0x89, 0x7C, 0x24, 0x40, 0x48, 0x8B, 0x7C, 0x24, 0x18, 0x48,
    0x89, 0x7C, 0x24, 0x38, 0x48, 0x8B, 0x7C, 0x24, 0x08, 0x4C, 0x8B, 0x44, 0x24, 0x10, 0x4C, 0x89,
    0x44, 0x24, 0x30, 0x48, 0x89, 0x7C, 0x24, 0x28, 0x48, 0x8B, 0xBC, 0x24, 0xB8, 0x00, 0x00, 0x00,
    0x48, 0x89, 0x7B, 0x50, 0x48, 0x8B, 0xBC, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x4C, 0x8B, 0x84, 0x24,
    0xB0, 0x00, 0x00, 0x00, 0x4C, 0x89, 0x43, 0x48, 0x48, 0x89, 0x7B, 0x40, 0x48, 0x8B, 0x7C, 0x24,
    0x40, 0x48, 0x89, 0x7B, 0x38, 0x48, 0x8B, 0x7C, 0x24, 0x38, 0x48, 0x89, 0x7B, 0x30, 0x48, 0x8B,
    0x7C, 0x24, 0x28, 0x4C, 0x8B, 0x44, 0x24, 0x30] ++ bytes_l126c6a_1

theorem code_l126c6a : ∀ x ∈ codeRange 0x126c6a bytes_l126c6a, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x26c6a 104 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l126c6a_1

@[cfg_block] def b_l126cf4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x126cf4 (StorePre 0x126cf4 5 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x126cf4 + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x126cf4 (.base 14 (.d8 0x20)) 0x1) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 54) (.out 0x126cf9 (movR64R64Effect 0x126cf9 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[1]
    (.letOp (n := 55) (.exec 0x126cf9 (fun s => s.RIP = 0x126cf9) (movR64R64Effect 0x126cf9 0 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 56) (.out 0x126cfc (shlR64Effect 0x126cfc 4 0 32) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[54]
    (.letOp (n := 57) (.exec 0x126cfc (fun s => s.RIP = 0x126cfc) (shlR64Effect 0x126cfc 4 0 32) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[54]
    (.letOp (n := 58) (.out 0x126d00 (orR64Imm8Effect 0x126d00 0 0x13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[56]
    (.letOp (n := 59) (.exec 0x126d00 (fun s => s.RIP = 0x126d00) (orR64Imm8Effect 0x126d00 0 0x13) (Reg.operands [.gpr 0] [])) #v[56]
    (.letOp (n := 60) (.out 0x126d04 (movR32Imm32Effect 0x126d04 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 61) (.exec 0x126d04 (fun s => s.RIP = 0x126d04) (movR32Imm32Effect 0x126d04 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 62) (.out 0x126d09 (xorR32R32Effect 0x126d09 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[7, 7]
    (.letOp (n := 63) (.exec 0x126d09 (fun s => s.RIP = 0x126d09) (xorR32R32Effect 0x126d09 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[7, 7]
    (.terminate (.br ⟨.l126b15, RegMap.args [(0, 58), (1, 1), (2, 60), (3, 3), (4, 4), (6, 6), (7, 62), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩))))))))))))

def bytes_l126cf4 : List UInt8 :=
  [0x41, 0xC6, 0x46, 0x20, 0x01, 0x48, 0x89, 0xC8, 0x48, 0xC1, 0xE0, 0x20, 0x48, 0x83, 0xC8, 0x13,
    0xBA, 0x01, 0x00, 0x00, 0x00, 0x31, 0xFF, 0xE9, 0x05, 0xFE, 0xFF, 0xFF]

theorem code_l126cf4 : ∀ x ∈ codeRange 0x126cf4 bytes_l126cf4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26cf4 28 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126d10 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126d10 (xorR32R32Effect 0x126d10 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[2, 2]
    (.letOp (n := 54) (.exec 0x126d10 (fun s => s.RIP = 0x126d10) (xorR32R32Effect 0x126d10 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 55) (.out 0x126d12 (movR32Imm32Effect 0x126d12 5 0 0xc) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 56) (.exec 0x126d12 (fun s => s.RIP = 0x126d12) (movR32Imm32Effect 0x126d12 5 0 0xc) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x126d17 (xorR32R32Effect 0x126d17 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[7, 7]
    (.letOp (n := 58) (.exec 0x126d17 (fun s => s.RIP = 0x126d17) (xorR32R32Effect 0x126d17 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[7, 7]
    (.terminate (.br ⟨.l126b15, RegMap.args [(0, 55), (1, 1), (2, 53), (3, 3), (4, 4), (6, 6), (7, 57), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l126d10 : List UInt8 :=
  [0x31, 0xD2, 0xB8, 0x0C, 0x00, 0x00, 0x00, 0x31, 0xFF, 0xE9, 0xF7, 0xFD, 0xFF, 0xFF]

theorem code_l126d10 : ∀ x ∈ codeRange 0x126d10 bytes_l126d10, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26d10 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126d20 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126d20 (pushR64Effect 0x126d20 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x126d20 (PushPre 0x126d20 1) (pushR64Effect 0x126d20 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x126d21 (pushR64Effect 0x126d21 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x126d21 (PushPre 0x126d21 2) (pushR64Effect 0x126d21 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x126d23 (pushR64Effect 0x126d23 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x126d23 (PushPre 0x126d23 2) (pushR64Effect 0x126d23 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x126d25 (pushR64Effect 0x126d25 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x126d25 (PushPre 0x126d25 2) (pushR64Effect 0x126d25 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x126d27 (pushR64Effect 0x126d27 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x126d27 (PushPre 0x126d27 2) (pushR64Effect 0x126d27 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x126d29 (pushR64Effect 0x126d29 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x126d29 (PushPre 0x126d29 1) (pushR64Effect 0x126d29 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x126d2a (subR64Imm32Effect 0x126d2a 4 0xa8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x126d2a (fun s => s.RIP = 0x126d2a) (subR64Imm32Effect 0x126d2a 4 0xa8) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x126d31 (movR64R64Effect 0x126d31 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 68) (.exec 0x126d31 (fun s => s.RIP = 0x126d31) (movR64R64Effect 0x126d31 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 69) (.out 0x126d34 (movR32M32LowEffect 0x126d34 5 (.base 2 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[2]
    (.letOp (n := 70) (.exec 0x126d34 (LoadPre 0x126d34 (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x126d34 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x126d34 5 (.base 2 (.d8 0x8))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 71) (.out 0x126d37 (movR32M32Effect 0x126d37 15 (.base 6 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 6] []) (.reg (.gpr 15))) #v[6]
    (.letOp (n := 72) (.exec 0x126d37 (LoadPre 0x126d37 (fun s => AddrMode.addr (.base 6 (.d8 0x1c)) s (0x126d37 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x126d37 15 (.base 6 (.d8 0x1c))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 73) (.out 0x126d3b (movR32R32Effect 0x126d3b 3 13 15) (EffectPart.reads (.reg (.gpr 13)) [.gpr 15] []) (.reg (.gpr 13))) #v[71]
    (.letOp (n := 74) (.exec 0x126d3b (fun s => s.RIP = 0x126d3b) (movR32R32Effect 0x126d3b 3 13 15) (Reg.operands [.gpr 15] [])) #v[71]
    (.letOp (n := 75) (.out 0x126d3e (addR32R32Effect 0x126d3e 3 13 5) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 5] []) (.reg (.gpr 13))) #v[73, 69]
    (.letOp (n := 76) (.out 0x126d3e (addR32R32Effect 0x126d3e 3 13 5) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 5] []) (.flag .CF)) #v[73, 69]
    (.letOp (n := 77) (.exec 0x126d3e (fun s => s.RIP = 0x126d3e) (addR32R32Effect 0x126d3e 3 13 5) (Reg.operands [.gpr 13, .gpr 5] [])) #v[73, 69]
    (.letOp (n := 78) (.pure (condOp 2)) #v[76]
    (.terminate (.condBr (Fin.last 78) ⟨.l127126, RegMap.args [(1, 1), (2, 2), (3, 67), (4, 65), (5, 69), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 75), (14, 14), (15, 71), (16, 76), (22, 22), (39, 39), (50, 50), (51, 51)] 79⟩ ⟨.l126d47, RegMap.args [(1, 1), (2, 2), (3, 67), (4, 65), (5, 69), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 75), (14, 14), (15, 71), (16, 76), (22, 22), (39, 39), (50, 50), (51, 51)] 79⟩)))))))))))))))))))))))))))

def bytes_l126d20 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0xA8, 0x00, 0x00,
    0x00, 0x48, 0x89, 0xFB, 0x8B, 0x6A, 0x08, 0x44, 0x8B, 0x7E, 0x1C, 0x45, 0x89, 0xFD, 0x41, 0x01,
    0xED, 0x0F, 0x82, 0xDF, 0x03, 0x00, 0x00]

theorem code_l126d20 : ∀ x ∈ codeRange 0x126d20 bytes_l126d20, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26d20 39 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126d47 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126d47 (movR64R64Effect 0x126d47 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 6] []) (.reg (.gpr 14))) #v[6]
    (.letOp (n := 54) (.exec 0x126d47 (fun s => s.RIP = 0x126d47) (movR64R64Effect 0x126d47 14 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 55) (.out 0x126d4a (movR64M64Effect 0x126d4a 6 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[6]
    (.letOp (n := 56) (.exec 0x126d4a (LoadPre 0x126d4a (fun s => AddrMode.addr (.base 6 .none) s (0x126d4a + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x126d4a 6 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 57) (.out 0x126d4d (movR64M64Effect 0x126d4d 2 (.base 14 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14] []) (.reg (.gpr 2))) #v[53]
    (.letOp (n := 58) (.exec 0x126d4d (LoadPre 0x126d4d (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x126d4d + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x126d4d 2 (.base 14 (.d8 0x8))) (Reg.operands [.gpr 14] [])) #v[53]
    (.letOp (n := 59) (.out 0x126d51 (leaR64Effect 0x126d51 7 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 60) (.exec 0x126d51 (fun s => s.RIP = 0x126d51) (leaR64Effect 0x126d51 7 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x126d56 (StorePre 0x126d56 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x126d56 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x126d56 6 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 62) (.exec 0x126d5e (StorePre 0x126d5e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x126d5e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x126d5e 2 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 63) (.out 0x126d66 (movR32R32Effect 0x126d66 3 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 13] []) (.reg (.gpr 1))) #v[13]
    (.letOp (n := 64) (.exec 0x126d66 (fun s => s.RIP = 0x126d66) (movR32R32Effect 0x126d66 3 1 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 65) (.out 0x126d69 (callEffect (fun _ => 0x127c50) 0x126d6e) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 66) (.exec 0x126d69 (PushPre 0x126d69 5) (callEffect (fun _ => 0x127c50) 0x126d6e) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.const ⟨64, 0x126d6e⟩) #v[]
    (.terminate (.call ⟨.l127c50, RegMap.args [(1, 63), (2, 57), (3, 3), (4, 65), (5, 5), (6, 55), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 68⟩ { target := .l126d6e, kept := #v[], arity := rfl, guard := some (Fin.last 67) }))))))))))))))))

def bytes_l126d47 : List UInt8 :=
  [0x49, 0x89, 0xF6, 0x48, 0x8B, 0x36, 0x49, 0x8B, 0x56, 0x08, 0x48, 0x8D, 0x7C, 0x24, 0x18, 0x48,
    0x89, 0xB4, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x94, 0x24, 0x98, 0x00, 0x00, 0x00, 0x44,
    0x89, 0xE9, 0xE8, 0xE2, 0x0E, 0x00, 0x00]

theorem code_l126d47 : ∀ x ∈ codeRange 0x126d47 bytes_l126d47, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26d47 39 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126d6e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126d6e (movR32M32Effect 0x126d6e 12 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 54) (.exec 0x126d6e (LoadPre 0x126d6e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x126d6e + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x126d6e 12 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x126d73 (cmpR32Imm8Effect 0x126d73 4 12 0x2) (EffectPart.reads (.flag .ZF) [.gpr 12] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x126d73 (fun s => s.RIP = 0x126d73) (cmpR32Imm8Effect 0x126d73 4 12 0x2) (Reg.operands [.gpr 12] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l126da9, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l126d79, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l126d6e : List UInt8 :=
  [0x44, 0x8B, 0x64, 0x24, 0x18, 0x41, 0x83, 0xFC, 0x02, 0x75, 0x30]

theorem code_l126d6e : ∀ x ∈ codeRange 0x126d6e bytes_l126d6e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26d6e 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126d79 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126d79 (movR64M64Effect 0x126d79 0 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x126d79 (LoadPre 0x126d79 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x126d79 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126d79 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x126d7e (movR64M64Effect 0x126d7e 1 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x126d7e (LoadPre 0x126d7e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x126d7e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126d7e 1 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x126d83 (StorePre 0x126d83 3 (fun s => AddrMode.addr (.base 14 .none) s (0x126d83 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x126d83 0 (.base 14 .none)) (Reg.operands [.gpr 0, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 58) (.exec 0x126d86 (StorePre 0x126d86 4 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x126d86 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126d86 1 (.base 14 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x126d8a (movR64M64Effect 0x126d8a 0 (.base 14 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[14]
    (.letOp (n := 60) (.exec 0x126d8a (LoadPre 0x126d8a (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x126d8a + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x126d8a 0 (.base 14 (.d8 0x10))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 61) (.out 0x126d8e (movR32Imm32Effect 0x126d8e 6 12 0x1) (EffectPart.reads (.reg (.gpr 12)) [] []) (.reg (.gpr 12))) #v[]
    (.letOp (n := 62) (.exec 0x126d8e (fun s => s.RIP = 0x126d8e) (movR32Imm32Effect 0x126d8e 6 12 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 63) (.out 0x126d94 (cmpR64Imm8Effect 0x126d94 0 0x3f) (EffectPart.reads (.flag .CF) [.gpr 0] []) (.flag .CF)) #v[59]
    (.letOp (n := 64) (.out 0x126d94 (cmpR64Imm8Effect 0x126d94 0 0x3f) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[59]
    (.letOp (n := 65) (.exec 0x126d94 (fun s => s.RIP = 0x126d94) (cmpR64Imm8Effect 0x126d94 0 0x3f) (Reg.operands [.gpr 0] [])) #v[59]
    (.letOp (n := 66) (.pure (condOp 6)) #v[63, 64]
    (.terminate (.condBr (Fin.last 66) ⟨.l126e83, RegMap.args [(0, 59), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 13), (14, 14), (15, 15), (16, 63), (19, 64), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩ ⟨.l126d9e, RegMap.args [(0, 59), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 13), (14, 14), (15, 15), (16, 63), (19, 64), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩)))))))))))))))

def bytes_l126d79 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x4C, 0x24, 0x28, 0x49, 0x89, 0x06, 0x49, 0x89, 0x4E,
    0x08, 0x49, 0x8B, 0x46, 0x10, 0x41, 0xBC, 0x01, 0x00, 0x00, 0x00, 0x48, 0x83, 0xF8, 0x3F, 0x0F,
    0x86, 0xE5, 0x00, 0x00, 0x00]

theorem code_l126d79 : ∀ x ∈ codeRange 0x126d79 bytes_l126d79, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26d79 37 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126d9e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126d9e (movR32Imm32Effect 0x126d9e 5 0 0x6) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 54) (.exec 0x126d9e (fun s => s.RIP = 0x126d9e) (movR32Imm32Effect 0x126d9e 5 0 0x6) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x126da3 (xorR32R32Effect 0x126da3 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[6, 6]
    (.letOp (n := 56) (.exec 0x126da3 (fun s => s.RIP = 0x126da3) (xorR32R32Effect 0x126da3 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 57) (.out 0x126da5 (xorR32R32Effect 0x126da5 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[1, 1]
    (.letOp (n := 58) (.exec 0x126da5 (fun s => s.RIP = 0x126da5) (xorR32R32Effect 0x126da5 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[1, 1]
    (.terminate (.br ⟨.l126e06, RegMap.args [(0, 53), (1, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l126d9e : List UInt8 :=
  [0xB8, 0x06, 0x00, 0x00, 0x00, 0x31, 0xF6, 0x31, 0xC9, 0xEB, 0x5D]

theorem code_l126d9e : ∀ x ∈ codeRange 0x126d9e bytes_l126d9e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26d9e 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126da9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126da9 (movR32M32Effect 0x126da9 15 (.sib 4 none 0 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 54) (.exec 0x126da9 (LoadPre 0x126da9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x126da9 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x126da9 15 (.sib 4 none 0 (.d8 0x1c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x126dae (movR64M64Effect 0x126dae 0 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 56) (.exec 0x126dae (LoadPre 0x126dae (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x126dae + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126dae 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x126db3 (movR64M64Effect 0x126db3 10 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 58) (.exec 0x126db3 (LoadPre 0x126db3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x126db3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126db3 10 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x126db8 (movzxR32M8Effect 0x126db8 6 13 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 60) (.exec 0x126db8 (LoadPre 0x126db8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x126db8 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x126db8 6 13 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x126dbe (movR64M64Effect 0x126dbe 1 (.sib 4 none 0 (.d8 0x31))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 62) (.exec 0x126dbe (LoadPre 0x126dbe (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x31)) s (0x126dbe + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126dbe 1 (.sib 4 none 0 (.d8 0x31))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x126dc3 (StorePre 0x126dc3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x126dc3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126dc3 1 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.out 0x126dc8 (movR64M64Effect 0x126dc8 1 (.sib 4 none 0 (.d8 0x39))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x126dc8 (LoadPre 0x126dc8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x39)) s (0x126dc8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126dc8 1 (.sib 4 none 0 (.d8 0x39))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x126dcd (StorePre 0x126dcd 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x126dcd + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x126dcd 1 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.out 0x126dd5 (movR64M64Effect 0x126dd5 1 (.sib 4 none 0 (.d8 0x41))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 68) (.exec 0x126dd5 (LoadPre 0x126dd5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x41)) s (0x126dd5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126dd5 1 (.sib 4 none 0 (.d8 0x41))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.exec 0x126dda (StorePre 0x126dda 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x126dda + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x126dda 1 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[67, 4]
    (.letOp (n := 70) (.out 0x126de2 (movR64M64Effect 0x126de2 1 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 71) (.exec 0x126de2 (LoadPre 0x126de2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x126de2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126de2 1 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.exec 0x126de7 (StorePre 0x126de7 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x8f)) s (0x126de7 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x126de7 1 (.sib 4 none 0 (.d32 0x8f))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[70, 4]
    (.letOp (n := 73) (.out 0x126def (movR64R64Effect 0x126def 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[55]
    (.letOp (n := 74) (.exec 0x126def (fun s => s.RIP = 0x126def) (movR64R64Effect 0x126def 5 0) (Reg.operands [.gpr 0] [])) #v[55]
    (.letOp (n := 75) (.out 0x126df2 (shrR64Effect 0x126df2 4 5 32) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[73]
    (.letOp (n := 76) (.exec 0x126df2 (fun s => s.RIP = 0x126df2) (shrR64Effect 0x126df2 4 5 32) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[73]
    (.letOp (n := 77) (.out 0x126df6 (movR64Imm64Effect 0x126df6 6 0xffffffff00000000) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 78) (.exec 0x126df6 (fun s => s.RIP = 0x126df6) (movR64Imm64Effect 0x126df6 6 0xffffffff00000000) (Reg.operands [] [])) #v[]
    (.letOp (n := 79) (.out 0x126e00 (andR64R64Effect 0x126e00 6 10) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 10] []) (.reg (.gpr 6))) #v[77, 57]
    (.letOp (n := 80) (.exec 0x126e00 (fun s => s.RIP = 0x126e00) (andR64R64Effect 0x126e00 6 10) (Reg.operands [.gpr 6, .gpr 10] [])) #v[77, 57]
    (.letOp (n := 81) (.out 0x126e03 (movR64R64Effect 0x126e03 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[55]
    (.letOp (n := 82) (.exec 0x126e03 (fun s => s.RIP = 0x126e03) (movR64R64Effect 0x126e03 1 0) (Reg.operands [.gpr 0] [])) #v[55]
    (.terminate (.br ⟨.l126e06, RegMap.args [(0, 55), (1, 81), (3, 3), (4, 4), (5, 75), (6, 79), (7, 7), (8, 8), (9, 9), (10, 57), (11, 11), (12, 12), (13, 59), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 83⟩)))))))))))))))))))))))))))))))

def bytes_l126da9 : List UInt8 :=
  [0x44, 0x8B, 0x7C, 0x24, 0x1C, 0x48, 0x8B, 0x44, 0x24, 0x20, 0x4C, 0x8B, 0x54, 0x24, 0x28, 0x44,
    0x0F, 0xB6, 0x6C, 0x24, 0x30, 0x48, 0x8B, 0x4C, 0x24, 0x31, 0x48, 0x89, 0x4C, 0x24, 0x78, 0x48,
    0x8B, 0x4C, 0x24, 0x39, 0x48, 0x89, 0x8C, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x4C, 0x24,
    0x41, 0x48, 0x89, 0x8C, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x4C, 0x24, 0x48, 0x48, 0x89,
    0x8C, 0x24, 0x8F, 0x00, 0x00, 0x00, 0x48, 0x89, 0xC5, 0x48, 0xC1, 0xED, 0x20, 0x48, 0xBE, 0x00,
    0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF, 0x4C, 0x21, 0xD6, 0x48, 0x89, 0xC1]

theorem code_l126da9 : ∀ x ∈ codeRange 0x126da9 bytes_l126da9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26da9 93 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126e06_1 : Block Op Label signature Reg.count 87 :=
  .letOp (n := 87) (.exec 0x126e5b (StorePre 0x126e5b 3 (fun s => AddrMode.addr (.base 3 (.d8 0x19)) s (0x126e5b + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x126e5b 2 (.base 3 (.d8 0x19))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[82, 3]
    (.letOp (n := 88) (.exec 0x126e5e (StorePre 0x126e5e 3 (fun s => AddrMode.addr (.base 3 .none) s (0x126e5e + BitVec.ofNat 64 3)) 4) (movM32R32Effect 0x126e5e 12 (.base 3 .none)) (Reg.operands [.gpr 12, .gpr 3] [])) #v[12, 3]
    (.letOp (n := 89) (.exec 0x126e61 (StorePre 0x126e61 4 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x126e61 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x126e61 15 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 15, .gpr 3] [])) #v[15, 3]
    (.letOp (n := 90) (.exec 0x126e65 (StorePre 0x126e65 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x126e65 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126e65 0 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 91) (.exec 0x126e69 (StorePre 0x126e69 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x126e69 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126e69 1 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[65, 3]
    (.letOp (n := 92) (.exec 0x126e6d (StorePre 0x126e6d 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x126e6d + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x126e6d 4 13 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 13, .gpr 3] [])) #v[13, 3]
    (.terminate (.br ⟨.l126e71, RegMap.args [(0, 61), (1, 65), (2, 82), (3, 3), (4, 4), (5, 53), (6, 84), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 93⟩)))))))

def bytes_l126e06_1 : List UInt8 :=
  [0x89, 0x53, 0x19, 0x44, 0x89, 0x23, 0x44, 0x89, 0x7B, 0x04, 0x48, 0x89, 0x43, 0x08, 0x48, 0x89,
    0x4B, 0x10, 0x44, 0x88, 0x6B, 0x18]

theorem code_l126e06_1 : ∀ x ∈ codeRange 0x126e5b bytes_l126e06_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26e5b 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126e06 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126e06 (shlR64Effect 0x126e06 4 5 32) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[5]
    (.letOp (n := 54) (.exec 0x126e06 (fun s => s.RIP = 0x126e06) (shlR64Effect 0x126e06 4 5 32) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5]
    (.letOp (n := 55) (.out 0x126e0a (andR32Imm32Effect 0x126e0a 6 1 0xffffff00) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1]
    (.letOp (n := 56) (.exec 0x126e0a (fun s => s.RIP = 0x126e0a) (andR32Imm32Effect 0x126e0a 6 1 0xffffff00) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 57) (.out 0x126e10 (orR64R64Effect 0x126e10 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 5] []) (.reg (.gpr 1))) #v[55, 53]
    (.letOp (n := 58) (.exec 0x126e10 (fun s => s.RIP = 0x126e10) (orR64R64Effect 0x126e10 1 5) (Reg.operands [.gpr 1, .gpr 5] [])) #v[55, 53]
    (.letOp (n := 59) (.out 0x126e13 (movzxR32R8Effect 0x126e13 3 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 60) (.exec 0x126e13 (fun s => s.RIP = 0x126e13) (movzxR32R8Effect 0x126e13 3 0 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 61) (.out 0x126e16 (orR64R64Effect 0x126e16 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[59, 57]
    (.letOp (n := 62) (.exec 0x126e16 (fun s => s.RIP = 0x126e16) (orR64R64Effect 0x126e16 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[59, 57]
    (.letOp (n := 63) (.out 0x126e19 (movR32R32Effect 0x126e19 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 10] []) (.reg (.gpr 1))) #v[10]
    (.letOp (n := 64) (.exec 0x126e19 (fun s => s.RIP = 0x126e19) (movR32R32Effect 0x126e19 3 1 10) (Reg.operands [.gpr 10] [])) #v[10]
    (.letOp (n := 65) (.out 0x126e1c (orR64R64Effect 0x126e1c 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[63, 6]
    (.letOp (n := 66) (.exec 0x126e1c (fun s => s.RIP = 0x126e1c) (orR64R64Effect 0x126e1c 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[63, 6]
    (.letOp (n := 67) (.out 0x126e1f (movR32M32LowEffect 0x126e1f 2 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 68) (.exec 0x126e1f (LoadPre 0x126e1f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x126e1f + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x126e1f 2 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.out 0x126e23 (movR32M32LowEffect 0x126e23 6 (.sib 4 none 0 (.d8 0x7b))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 70) (.exec 0x126e23 (LoadPre 0x126e23 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7b)) s (0x126e23 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x126e23 6 (.sib 4 none 0 (.d8 0x7b))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.exec 0x126e27 (StorePre 0x126e27 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x53)) s (0x126e27 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x126e27 6 (.sib 4 none 0 (.d8 0x53))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[69, 4]
    (.letOp (n := 72) (.exec 0x126e2b (StorePre 0x126e2b 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x126e2b + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x126e2b 2 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[67, 4]
    (.letOp (n := 73) (.out 0x126e2f (movR64M64Effect 0x126e2f 2 (.sib 4 none 0 (.d32 0x8f))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 74) (.exec 0x126e2f (LoadPre 0x126e2f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x8f)) s (0x126e2f + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x126e2f 2 (.sib 4 none 0 (.d32 0x8f))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.exec 0x126e37 (StorePre 0x126e37 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x126e37 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126e37 2 (.base 3 (.d8 0x30))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[73, 3]
    (.letOp (n := 76) (.out 0x126e3b (movR64M64Effect 0x126e3b 2 (.sib 4 none 0 (.d32 0x87))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 77) (.exec 0x126e3b (LoadPre 0x126e3b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x87)) s (0x126e3b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x126e3b 2 (.sib 4 none 0 (.d32 0x87))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 78) (.exec 0x126e43 (StorePre 0x126e43 4 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x126e43 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126e43 2 (.base 3 (.d8 0x28))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[76, 3]
    (.letOp (n := 79) (.out 0x126e47 (movR64M64Effect 0x126e47 2 (.sib 4 none 0 (.d8 0x7f))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 80) (.exec 0x126e47 (LoadPre 0x126e47 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7f)) s (0x126e47 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126e47 2 (.sib 4 none 0 (.d8 0x7f))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 81) (.exec 0x126e4c (StorePre 0x126e4c 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x126e4c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126e4c 2 (.base 3 (.d8 0x20))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[79, 3]
    (.letOp (n := 82) (.out 0x126e50 (movR32M32LowEffect 0x126e50 2 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 83) (.exec 0x126e50 (LoadPre 0x126e50 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x126e50 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x126e50 2 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 84) (.out 0x126e54 (movR32M32LowEffect 0x126e54 6 (.sib 4 none 0 (.d8 0x53))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 85) (.exec 0x126e54 (LoadPre 0x126e54 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x53)) s (0x126e54 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x126e54 6 (.sib 4 none 0 (.d8 0x53))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 86) (.exec 0x126e58 (StorePre 0x126e58 3 (fun s => AddrMode.addr (.base 3 (.d8 0x1c)) s (0x126e58 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x126e58 6 (.base 3 (.d8 0x1c))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[84, 3]
    (b_l126e06_1))))))))))))))))))))))))))))))))))

def bytes_l126e06 : List UInt8 :=
  [0x48, 0xC1, 0xE5, 0x20, 0x81, 0xE1, 0x00, 0xFF, 0xFF, 0xFF, 0x48, 0x09, 0xE9, 0x0F, 0xB6, 0xC0,
    0x48, 0x09, 0xC8, 0x44, 0x89, 0xD1, 0x48, 0x09, 0xF1, 0x8B, 0x54, 0x24, 0x78, 0x8B, 0x74, 0x24,
    0x7B, 0x89, 0x74, 0x24, 0x53, 0x89, 0x54, 0x24, 0x50, 0x48, 0x8B, 0x94, 0x24, 0x8F, 0x00, 0x00,
    0x00, 0x48, 0x89, 0x53, 0x30, 0x48, 0x8B, 0x94, 0x24, 0x87, 0x00, 0x00, 0x00, 0x48, 0x89, 0x53,
    0x28, 0x48, 0x8B, 0x54, 0x24, 0x7F, 0x48, 0x89, 0x53, 0x20, 0x8B, 0x54, 0x24, 0x50, 0x8B, 0x74,
    0x24, 0x53, 0x89, 0x73, 0x1C] ++ bytes_l126e06_1

theorem code_l126e06 : ∀ x ∈ codeRange 0x126e06 bytes_l126e06, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x26e06 85 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l126e06_1

@[cfg_block] def b_l126e71 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126e71 (addR64Imm32Effect 0x126e71 4 0xa8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 54) (.exec 0x126e71 (fun s => s.RIP = 0x126e71) (addR64Imm32Effect 0x126e71 4 0xa8) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x126e78 (popR64Effect 0x126e78 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[53]
    (.letOp (n := 56) (.out 0x126e78 (popR64Effect 0x126e78 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[53]
    (.letOp (n := 57) (.exec 0x126e78 (PopPre 0x126e78) (popR64Effect 0x126e78 1 3) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 58) (.out 0x126e79 (popR64Effect 0x126e79 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[56]
    (.letOp (n := 59) (.out 0x126e79 (popR64Effect 0x126e79 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[56]
    (.letOp (n := 60) (.exec 0x126e79 (PopPre 0x126e79) (popR64Effect 0x126e79 2 12) (Reg.operands [.gpr 4] [])) #v[56]
    (.letOp (n := 61) (.out 0x126e7b (popR64Effect 0x126e7b 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[59]
    (.letOp (n := 62) (.out 0x126e7b (popR64Effect 0x126e7b 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 63) (.exec 0x126e7b (PopPre 0x126e7b) (popR64Effect 0x126e7b 2 13) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 64) (.out 0x126e7d (popR64Effect 0x126e7d 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[62]
    (.letOp (n := 65) (.out 0x126e7d (popR64Effect 0x126e7d 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[62]
    (.letOp (n := 66) (.exec 0x126e7d (PopPre 0x126e7d) (popR64Effect 0x126e7d 2 14) (Reg.operands [.gpr 4] [])) #v[62]
    (.letOp (n := 67) (.out 0x126e7f (popR64Effect 0x126e7f 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[65]
    (.letOp (n := 68) (.out 0x126e7f (popR64Effect 0x126e7f 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 69) (.exec 0x126e7f (PopPre 0x126e7f) (popR64Effect 0x126e7f 2 15) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 70) (.out 0x126e81 (popR64Effect 0x126e81 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[68]
    (.letOp (n := 71) (.out 0x126e81 (popR64Effect 0x126e81 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[68]
    (.letOp (n := 72) (.exec 0x126e81 (PopPre 0x126e81) (popR64Effect 0x126e81 1 5) (Reg.operands [.gpr 4] [])) #v[68]
    (.letOp (n := 73) (.out 0x126e82 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[71]
    (.letOp (n := 74) (.out 0x126e82 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[71]
    (.letOp (n := 75) (.exec 0x126e82 (RetPre 0x126e82) (retEffect) (Reg.operands [.gpr 4] [])) #v[71]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 2), (3, 55), (4, 74), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 76) (some ⟨73, by decide⟩)))))))))))))))))))))))))

def bytes_l126e71 : List UInt8 :=
  [0x48, 0x81, 0xC4, 0xA8, 0x00, 0x00, 0x00, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F,
    0x5D, 0xC3]

theorem code_l126e71 : ∀ x ∈ codeRange 0x126e71 bytes_l126e71, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26e71 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126e83 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126e83 (incR64Effect 0x126e83 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 54) (.exec 0x126e83 (fun s => s.RIP = 0x126e83) (incR64Effect 0x126e83 0) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[0]
    (.letOp (n := 55) (.exec 0x126e86 (StorePre 0x126e86 4 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x126e86 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126e86 0 (.base 14 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 56) (.out 0x126e8a (movR32M32Effect 0x126e8a 15 (.base 14 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 14] []) (.reg (.gpr 15))) #v[14]
    (.letOp (n := 57) (.exec 0x126e8a (LoadPre 0x126e8a (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x126e8a + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x126e8a 15 (.base 14 (.d8 0x18))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 58) (.out 0x126e8e (cmpR32R32Effect 0x126e8e 3 13 15) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 15] []) (.flag .CF)) #v[13, 56]
    (.letOp (n := 59) (.out 0x126e8e (cmpR32R32Effect 0x126e8e 3 13 15) (EffectPart.reads (.flag .ZF) [.gpr 13, .gpr 15] []) (.flag .ZF)) #v[13, 56]
    (.letOp (n := 60) (.exec 0x126e8e (fun s => s.RIP = 0x126e8e) (cmpR32R32Effect 0x126e8e 3 13 15) (Reg.operands [.gpr 13, .gpr 15] [])) #v[13, 56]
    (.letOp (n := 61) (.pure (condOp 6)) #v[58, 59]
    (.terminate (.condBr (Fin.last 61) ⟨.l126ea8, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 56), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ ⟨.l126e93, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 56), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩))))))))))

def bytes_l126e83 : List UInt8 :=
  [0x48, 0xFF, 0xC0, 0x49, 0x89, 0x46, 0x10, 0x45, 0x8B, 0x7E, 0x18, 0x45, 0x39, 0xFD, 0x76, 0x15]

theorem code_l126e83 : ∀ x ∈ codeRange 0x126e83 bytes_l126e83, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26e83 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126e93 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126e93 (leaR32Effect 0x126e93 4 5 (.base 15 (.d8 0x1))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 15] []) (.reg (.gpr 5))) #v[15]
    (.letOp (n := 54) (.exec 0x126e93 (fun s => s.RIP = 0x126e93) (leaR32Effect 0x126e93 4 5 (.base 15 (.d8 0x1))) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.out 0x126e97 (movR32Imm32Effect 0x126e97 5 0 0x3) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 56) (.exec 0x126e97 (fun s => s.RIP = 0x126e97) (movR32Imm32Effect 0x126e97 5 0 0x3) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x126e9c (xorR32R32Effect 0x126e9c 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[6, 6]
    (.letOp (n := 58) (.exec 0x126e9c (fun s => s.RIP = 0x126e9c) (xorR32R32Effect 0x126e9c 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 59) (.out 0x126e9e (movR32R32Effect 0x126e9e 3 10 15) (EffectPart.reads (.reg (.gpr 10)) [.gpr 15] []) (.reg (.gpr 10))) #v[15]
    (.letOp (n := 60) (.exec 0x126e9e (fun s => s.RIP = 0x126e9e) (movR32R32Effect 0x126e9e 3 10 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 61) (.out 0x126ea1 (xorR32R32Effect 0x126ea1 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[1, 1]
    (.letOp (n := 62) (.exec 0x126ea1 (fun s => s.RIP = 0x126ea1) (xorR32R32Effect 0x126ea1 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[1, 1]
    (.terminate (.br ⟨.l126e06, RegMap.args [(0, 55), (1, 61), (3, 3), (4, 4), (5, 53), (6, 57), (7, 7), (8, 8), (9, 9), (10, 59), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 63⟩)))))))))))

def bytes_l126e93 : List UInt8 :=
  [0x41, 0x8D, 0x6F, 0x01, 0xB8, 0x03, 0x00, 0x00, 0x00, 0x31, 0xF6, 0x45, 0x89, 0xFA, 0x31, 0xC9,
    0xE9, 0x5E, 0xFF, 0xFF, 0xFF]

theorem code_l126e93 : ∀ x ∈ codeRange 0x126e93 bytes_l126e93, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26e93 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126ea8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x126ea8 (StorePre 0x126ea8 4 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x126ea8 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x126ea8 13 (.base 14 (.d8 0x18))) (Reg.operands [.gpr 13, .gpr 14] [])) #v[13, 14]
    (.letOp (n := 54) (.out 0x126eac (testR32R32Effect 0x126eac 2 5 5) (EffectPart.reads (.flag .ZF) [.gpr 5, .gpr 5] []) (.flag .ZF)) #v[5, 5]
    (.letOp (n := 55) (.exec 0x126eac (fun s => s.RIP = 0x126eac) (testR32R32Effect 0x126eac 2 5 5) (Reg.operands [.gpr 5, .gpr 5] [])) #v[5, 5]
    (.letOp (n := 56) (.pure (condOp 4)) #v[54]
    (.terminate (.condBr (Fin.last 56) ⟨.l126f85, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩ ⟨.l126eb4, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l126ea8 : List UInt8 :=
  [0x45, 0x89, 0x6E, 0x18, 0x85, 0xED, 0x0F, 0x84, 0xD1, 0x00, 0x00, 0x00]

theorem code_l126ea8 : ∀ x ∈ codeRange 0x126ea8 bytes_l126ea8, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26ea8 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126eb4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126eb4 (leaR64Effect 0x126eb4 7 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x126eb4 (fun s => s.RIP = 0x126eb4) (leaR64Effect 0x126eb4 7 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x126eb9 (movR64R64Effect 0x126eb9 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 56) (.exec 0x126eb9 (fun s => s.RIP = 0x126eb9) (movR64R64Effect 0x126eb9 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x126ebc (movR32Imm32Effect 0x126ebc 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x126ebc (fun s => s.RIP = 0x126ebc) (movR32Imm32Effect 0x126ebc 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x126ec1 (callEffect (fun _ => 0x127b80) 0x126ec6) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x126ec1 (PushPre 0x126ec1 5) (callEffect (fun _ => 0x127b80) 0x126ec6) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x126ec6⟩) #v[]
    (.terminate (.call ⟨.l127b80, RegMap.args [(2, 57), (3, 3), (4, 59), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l126ec6, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l126eb4 : List UInt8 :=
  [0x48, 0x8D, 0x7C, 0x24, 0x18, 0x4C, 0x89, 0xF6, 0xBA, 0x01, 0x00, 0x00, 0x00, 0xE8, 0xBA, 0x0C,
    0x00, 0x00]

theorem code_l126eb4 : ∀ x ∈ codeRange 0x126eb4 bytes_l126eb4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26eb4 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126ec6 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126ec6 (movR32M32LowEffect 0x126ec6 7 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x126ec6 (LoadPre 0x126ec6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x126ec6 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x126ec6 7 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x126eca (cmpR32Imm8Effect 0x126eca 3 7 0x2) (EffectPart.reads (.flag .ZF) [.gpr 7] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x126eca (fun s => s.RIP = 0x126eca) (cmpR32Imm8Effect 0x126eca 3 7 0x2) (Reg.operands [.gpr 7] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l126f21, RegMap.args [(3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l126ecf, RegMap.args [(3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l126ec6 : List UInt8 :=
  [0x8B, 0x7C, 0x24, 0x18, 0x83, 0xFF, 0x02, 0x75, 0x52]

theorem code_l126ec6 : ∀ x ∈ codeRange 0x126ec6 bytes_l126ec6, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26ec6 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126ecf : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126ecf (movR64M64Effect 0x126ecf 6 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 54) (.exec 0x126ecf (LoadPre 0x126ecf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x126ecf + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126ecf 6 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x126ed4 (cmpR64Imm8Effect 0x126ed4 6 0x1) (EffectPart.reads (.flag .ZF) [.gpr 6] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x126ed4 (fun s => s.RIP = 0x126ed4) (cmpR64Imm8Effect 0x126ed4 6 0x1) (Reg.operands [.gpr 6] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l127137, RegMap.args [(3, 3), (4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l126ede, RegMap.args [(3, 3), (4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l126ecf : List UInt8 :=
  [0x48, 0x8B, 0x74, 0x24, 0x28, 0x48, 0x83, 0xFE, 0x01, 0x0F, 0x85, 0x59, 0x02, 0x00, 0x00]

theorem code_l126ecf : ∀ x ∈ codeRange 0x126ecf bytes_l126ecf, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26ecf 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126ede : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126ede (decR32Effect 0x126ede 2 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[5]
    (.letOp (n := 54) (.exec 0x126ede (fun s => s.RIP = 0x126ede) (decR32Effect 0x126ede 2 5) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5]
    (.letOp (n := 55) (.out 0x126ee0 (movR64M64Effect 0x126ee0 0 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 56) (.exec 0x126ee0 (LoadPre 0x126ee0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x126ee0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126ee0 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x126ee5 (movzxR32M8Effect 0x126ee5 4 13 (.base 0 .none)) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[55]
    (.letOp (n := 58) (.exec 0x126ee5 (LoadPre 0x126ee5 (fun s => AddrMode.addr (.base 0 .none) s (0x126ee5 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x126ee5 4 13 (.base 0 .none)) (Reg.operands [.gpr 0] [])) #v[55]
    (.letOp (n := 59) (.out 0x126ee9 (leaR64Effect 0x126ee9 7 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 60) (.exec 0x126ee9 (fun s => s.RIP = 0x126ee9) (leaR64Effect 0x126ee9 7 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x126eee (movR64R64Effect 0x126eee 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 62) (.exec 0x126eee (fun s => s.RIP = 0x126eee) (movR64R64Effect 0x126eee 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 63) (.out 0x126ef1 (movR32R32Effect 0x126ef1 2 2 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5] []) (.reg (.gpr 2))) #v[53]
    (.letOp (n := 64) (.exec 0x126ef1 (fun s => s.RIP = 0x126ef1) (movR32R32Effect 0x126ef1 2 2 5) (Reg.operands [.gpr 5] [])) #v[53]
    (.letOp (n := 65) (.out 0x126ef3 (callEffect (fun _ => 0x127b80) 0x126ef8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 66) (.exec 0x126ef3 (PushPre 0x126ef3 5) (callEffect (fun _ => 0x127b80) 0x126ef8) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.const ⟨64, 0x126ef8⟩) #v[]
    (.terminate (.call ⟨.l127b80, RegMap.args [(0, 55), (2, 63), (3, 3), (4, 65), (5, 53), (6, 61), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 57), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 68⟩ { target := .l126ef8, kept := #v[], arity := rfl, guard := some (Fin.last 67) }))))))))))))))))

def bytes_l126ede : List UInt8 :=
  [0xFF, 0xCD, 0x48, 0x8B, 0x44, 0x24, 0x20, 0x44, 0x0F, 0xB6, 0x28, 0x48, 0x8D, 0x7C, 0x24, 0x18,
    0x4C, 0x89, 0xF6, 0x89, 0xEA, 0xE8, 0x88, 0x0C, 0x00, 0x00]

theorem code_l126ede : ∀ x ∈ codeRange 0x126ede bytes_l126ede, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26ede 26 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126ef8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126ef8 (movR32M32LowEffect 0x126ef8 7 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x126ef8 (LoadPre 0x126ef8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x126ef8 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x126ef8 7 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x126efc (cmpR32Imm8Effect 0x126efc 3 7 0x2) (EffectPart.reads (.flag .ZF) [.gpr 7] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x126efc (fun s => s.RIP = 0x126efc) (cmpR32Imm8Effect 0x126efc 3 7 0x2) (Reg.operands [.gpr 7] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l126f21, RegMap.args [(1, 1), (3, 3), (4, 4), (6, 6), (7, 53), (8, 8), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l126f01, RegMap.args [(1, 1), (3, 3), (4, 4), (6, 6), (7, 53), (8, 8), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l126ef8 : List UInt8 :=
  [0x8B, 0x7C, 0x24, 0x18, 0x83, 0xFF, 0x02, 0x75, 0x20]

theorem code_l126ef8 : ∀ x ∈ codeRange 0x126ef8 bytes_l126ef8, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26ef8 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126f01 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126f01 (movR64M64Effect 0x126f01 2 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 54) (.exec 0x126f01 (LoadPre 0x126f01 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x126f01 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126f01 2 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x126f06 (movR64R64Effect 0x126f06 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x126f06 (fun s => s.RIP = 0x126f06) (movR64R64Effect 0x126f06 0 2) (Reg.operands [.gpr 2] [])) #v[53]
    (.letOp (n := 57) (.out 0x126f09 (shrR64Effect 0x126f09 4 0 32) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.flag .ZF)) #v[55]
    (.letOp (n := 58) (.exec 0x126f09 (fun s => s.RIP = 0x126f09) (shrR64Effect 0x126f09 4 0 32) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[55]
    (.letOp (n := 59) (.pure (condOp 4)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l1270a3, RegMap.args [(1, 1), (2, 53), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l126f13, RegMap.args [(1, 1), (2, 53), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l126f01 : List UInt8 :=
  [0x48, 0x8B, 0x54, 0x24, 0x28, 0x48, 0x89, 0xD0, 0x48, 0xC1, 0xE8, 0x20, 0x0F, 0x84, 0x90, 0x01,
    0x00, 0x00]

theorem code_l126f01 : ∀ x ∈ codeRange 0x126f01 bytes_l126f01, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26f01 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126f13 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x126f13 (StorePre 0x126f13 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x126f13 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126f13 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2, 4]
    (.letOp (n := 54) (.out 0x126f18 (movR32Imm32Effect 0x126f18 5 1 0xc) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 55) (.exec 0x126f18 (fun s => s.RIP = 0x126f18) (movR32Imm32Effect 0x126f18 5 1 0xc) (Reg.operands [] [])) #v[]
    (.letOp (n := 56) (.out 0x126f1d (xorR32R32Effect 0x126f1d 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[7, 7]
    (.letOp (n := 57) (.exec 0x126f1d (fun s => s.RIP = 0x126f1d) (xorR32R32Effect 0x126f1d 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[7, 7]
    (.terminate (.br ⟨.l126f62, RegMap.args [(1, 54), (2, 2), (3, 3), (4, 4), (7, 56), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l126f13 : List UInt8 :=
  [0x48, 0x89, 0x54, 0x24, 0x10, 0xB9, 0x0C, 0x00, 0x00, 0x00, 0x31, 0xFF, 0xEB, 0x41]

theorem code_l126f13 : ∀ x ∈ codeRange 0x126f13 bytes_l126f13, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26f13 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126f21 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126f21 (movR32M32LowEffect 0x126f21 2 (.sib 4 none 0 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 54) (.exec 0x126f21 (LoadPre 0x126f21 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x126f21 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x126f21 2 (.sib 4 none 0 (.d8 0x1c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x126f25 (movR64M64Effect 0x126f25 1 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x126f25 (LoadPre 0x126f25 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x126f25 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126f25 1 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x126f2a (movR64M64Effect 0x126f2a 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 58) (.exec 0x126f2a (LoadPre 0x126f2a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x126f2a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126f2a 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.exec 0x126f2f (StorePre 0x126f2f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x126f2f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126f2f 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 60) (.out 0x126f34 (movzxR32M8Effect 0x126f34 6 13 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 61) (.exec 0x126f34 (LoadPre 0x126f34 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x126f34 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x126f34 6 13 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.out 0x126f3a (movR64M64Effect 0x126f3a 0 (.sib 4 none 0 (.d8 0x31))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x126f3a (LoadPre 0x126f3a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x31)) s (0x126f3a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126f3a 0 (.sib 4 none 0 (.d8 0x31))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x126f3f (StorePre 0x126f3f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x126f3f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126f3f 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x126f44 (movR64M64Effect 0x126f44 0 (.sib 4 none 0 (.d8 0x39))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 66) (.exec 0x126f44 (LoadPre 0x126f44 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x39)) s (0x126f44 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126f44 0 (.sib 4 none 0 (.d8 0x39))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x126f49 (StorePre 0x126f49 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x126f49 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126f49 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x126f4e (movR64M64Effect 0x126f4e 0 (.sib 4 none 0 (.d8 0x41))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 69) (.exec 0x126f4e (LoadPre 0x126f4e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x41)) s (0x126f4e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126f4e 0 (.sib 4 none 0 (.d8 0x41))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.exec 0x126f53 (StorePre 0x126f53 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x126f53 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126f53 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[68, 4]
    (.letOp (n := 71) (.out 0x126f58 (movR64M64Effect 0x126f58 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 72) (.exec 0x126f58 (LoadPre 0x126f58 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x126f58 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126f58 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.exec 0x126f5d (StorePre 0x126f5d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6f)) s (0x126f5d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126f5d 0 (.sib 4 none 0 (.d8 0x6f))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[71, 4]
    (.terminate (.br ⟨.l126f62, RegMap.args [(0, 71), (1, 55), (2, 53), (3, 3), (4, 4), (7, 7), (12, 12), (13, 60), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 74⟩))))))))))))))))))))))

def bytes_l126f21 : List UInt8 :=
  [0x8B, 0x54, 0x24, 0x1C, 0x48, 0x8B, 0x4C, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x28, 0x48, 0x89,
    0x44, 0x24, 0x10, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x30, 0x48, 0x8B, 0x44, 0x24, 0x31, 0x48, 0x89,
    0x44, 0x24, 0x58, 0x48, 0x8B, 0x44, 0x24, 0x39, 0x48, 0x89, 0x44, 0x24, 0x60, 0x48, 0x8B, 0x44,
    0x24, 0x41, 0x48, 0x89, 0x44, 0x24, 0x68, 0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24,
    0x6F]

theorem code_l126f21 : ∀ x ∈ codeRange 0x126f21 bytes_l126f21, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26f21 65 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126f62 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x126f62 (StorePre 0x126f62 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x126f62 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x126f62 2 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2, 4]
    (.letOp (n := 54) (.out 0x126f66 (movR32R32Effect 0x126f66 3 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[2]
    (.letOp (n := 55) (.exec 0x126f66 (fun s => s.RIP = 0x126f66) (movR32R32Effect 0x126f66 3 8 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 56) (.out 0x126f69 (andR32Imm32Effect 0x126f69 7 8 0xffffff00) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[54]
    (.letOp (n := 57) (.exec 0x126f69 (fun s => s.RIP = 0x126f69) (andR32Imm32Effect 0x126f69 7 8 0xffffff00) (Reg.operands [.gpr 8] [])) #v[54]
    (.letOp (n := 58) (.out 0x126f70 (movR64Imm64Effect 0x126f70 11 0xffffff0000000000) (EffectPart.reads (.reg (.gpr 11)) [] []) (.reg (.gpr 11))) #v[]
    (.letOp (n := 59) (.exec 0x126f70 (fun s => s.RIP = 0x126f70) (movR64Imm64Effect 0x126f70 11 0xffffff0000000000) (Reg.operands [] [])) #v[]
    (.letOp (n := 60) (.out 0x126f7a (andR64R64Effect 0x126f7a 11 1) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 1] []) (.reg (.gpr 11))) #v[58, 1]
    (.letOp (n := 61) (.exec 0x126f7a (fun s => s.RIP = 0x126f7a) (andR64R64Effect 0x126f7a 11 1) (Reg.operands [.gpr 11, .gpr 1] [])) #v[58, 1]
    (.terminate (.br ⟨.l126f7d, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (7, 7), (8, 56), (11, 60), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩))))))))))

def bytes_l126f62 : List UInt8 :=
  [0x89, 0x54, 0x24, 0x0C, 0x41, 0x89, 0xD0, 0x41, 0x81, 0xE0, 0x00, 0xFF, 0xFF, 0xFF, 0x49, 0xBB,
    0x00, 0x00, 0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0x49, 0x21, 0xCB]

theorem code_l126f62 : ∀ x ∈ codeRange 0x126f62 bytes_l126f62, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26f62 27 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126f7d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126f7d (movR64R64Effect 0x126f7d 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 1] []) (.reg (.gpr 9))) #v[1]
    (.letOp (n := 54) (.exec 0x126f7d (fun s => s.RIP = 0x126f7d) (movR64R64Effect 0x126f7d 9 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 55) (.out 0x126f80 (movR64R64Effect 0x126f80 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[1]
    (.letOp (n := 56) (.exec 0x126f80 (fun s => s.RIP = 0x126f80) (movR64R64Effect 0x126f80 0 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.terminate (.br ⟨.l126f9f, RegMap.args [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (7, 7), (8, 8), (9, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l126f7d : List UInt8 :=
  [0x49, 0x89, 0xC9, 0x48, 0x89, 0xC8, 0xEB, 0x1A]

theorem code_l126f7d : ∀ x ∈ codeRange 0x126f7d bytes_l126f7d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26f7d 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126f85 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126f85 (movR32Imm32Effect 0x126f85 5 0 0xc) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 54) (.exec 0x126f85 (fun s => s.RIP = 0x126f85) (movR32Imm32Effect 0x126f85 5 0 0xc) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x126f8a (xorR32R32Effect 0x126f8a 3 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 8] []) (.reg (.gpr 8))) #v[8, 8]
    (.letOp (n := 56) (.exec 0x126f8a (fun s => s.RIP = 0x126f8a) (xorR32R32Effect 0x126f8a 3 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[8, 8]
    (.terminate (.br ⟨.l126f8d, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (7, 7), (8, 55), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l126f85 : List UInt8 :=
  [0xB8, 0x0C, 0x00, 0x00, 0x00, 0x45, 0x31, 0xC0]

theorem code_l126f85 : ∀ x ∈ codeRange 0x126f85 bytes_l126f85, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26f85 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126f8d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x126f8d (StorePre 0x126f8d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x126f8d + BitVec.ofNat 64 8)) 4) (movM32Imm32Effect 0x126f8d 8 (.sib 4 none 0 (.d8 0xc)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.out 0x126f95 (xorR32R32Effect 0x126f95 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[1, 1]
    (.letOp (n := 55) (.exec 0x126f95 (fun s => s.RIP = 0x126f95) (xorR32R32Effect 0x126f95 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[1, 1]
    (.letOp (n := 56) (.out 0x126f97 (xorR32R32Effect 0x126f97 3 11 11) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 11] []) (.reg (.gpr 11))) #v[11, 11]
    (.letOp (n := 57) (.exec 0x126f97 (fun s => s.RIP = 0x126f97) (xorR32R32Effect 0x126f97 3 11 11) (Reg.operands [.gpr 11, .gpr 11] [])) #v[11, 11]
    (.letOp (n := 58) (.out 0x126f9a (xorR32R32Effect 0x126f9a 3 9 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 9] []) (.reg (.gpr 9))) #v[9, 9]
    (.letOp (n := 59) (.exec 0x126f9a (fun s => s.RIP = 0x126f9a) (xorR32R32Effect 0x126f9a 3 9 9) (Reg.operands [.gpr 9, .gpr 9] [])) #v[9, 9]
    (.terminate (.br ⟨.l126f9d, RegMap.args [(0, 0), (1, 54), (2, 2), (3, 3), (4, 4), (7, 7), (8, 8), (9, 58), (11, 56), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l126f8d : List UInt8 :=
  [0xC7, 0x44, 0x24, 0x0C, 0x00, 0x00, 0x00, 0x00, 0x31, 0xC9, 0x45, 0x31, 0xDB, 0x45, 0x31, 0xC9]

theorem code_l126f8d : ∀ x ∈ codeRange 0x126f8d bytes_l126f8d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26f8d 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126f9d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126f9d (xorR32R32Effect 0x126f9d 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[7, 7]
    (.letOp (n := 54) (.exec 0x126f9d (fun s => s.RIP = 0x126f9d) (xorR32R32Effect 0x126f9d 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[7, 7]
    (.terminate (.br ⟨.l126f9f, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (7, 53), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l126f9d : List UInt8 :=
  [0x31, 0xFF]

theorem code_l126f9d : ∀ x ∈ codeRange 0x126f9d bytes_l126f9d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26f9d 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126f9f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126f9f (movR32M32Effect 0x126f9f 10 (.base 14 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 14] []) (.reg (.gpr 10))) #v[14]
    (.letOp (n := 54) (.exec 0x126f9f (LoadPre 0x126f9f (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x126f9f + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x126f9f 10 (.base 14 (.d8 0x18))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 55) (.out 0x126fa3 (movR32M32Effect 0x126fa3 5 (.base 14 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 14] []) (.reg (.gpr 5))) #v[14]
    (.letOp (n := 56) (.exec 0x126fa3 (LoadPre 0x126fa3 (fun s => AddrMode.addr (.base 14 (.d8 0x1c)) s (0x126fa3 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x126fa3 5 (.base 14 (.d8 0x1c))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x126fa7 (subR32R32Effect 0x126fa7 3 10 5) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 5] []) (.reg (.gpr 10))) #v[53, 55]
    (.letOp (n := 58) (.out 0x126fa7 (subR32R32Effect 0x126fa7 3 10 5) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 5] []) (.flag .CF)) #v[53, 55]
    (.letOp (n := 59) (.out 0x126fa7 (subR32R32Effect 0x126fa7 3 10 5) (EffectPart.reads (.flag .ZF) [.gpr 10, .gpr 5] []) (.flag .ZF)) #v[53, 55]
    (.letOp (n := 60) (.exec 0x126fa7 (fun s => s.RIP = 0x126fa7) (subR32R32Effect 0x126fa7 3 10 5) (Reg.operands [.gpr 10, .gpr 5] [])) #v[53, 55]
    (.letOp (n := 61) (.out 0x126faa (atFlags (condHolds 6) (setccR8Effect 0x126faa 3 2)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF]) (.reg (.gpr 2))) #v[2, 58, 59]
    (.letOp (n := 62) (.exec 0x126faa (fun s => s.RIP = 0x126faa) (atFlags (condHolds 6) (setccR8Effect 0x126faa 3 2)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF])) #v[2, 58, 59]
    (.letOp (n := 63) (.out 0x126fad (movR64M64Effect 0x126fad 6 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 64) (.exec 0x126fad (LoadPre 0x126fad (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x126fad + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x126fad 6 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.exec 0x126fb5 (StorePre 0x126fb5 3 (fun s => AddrMode.addr (.base 14 .none) s (0x126fb5 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x126fb5 6 (.base 14 .none)) (Reg.operands [.gpr 6, .gpr 14] [])) #v[63, 14]
    (.letOp (n := 66) (.out 0x126fb8 (movR64M64Effect 0x126fb8 6 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 67) (.exec 0x126fb8 (LoadPre 0x126fb8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x126fb8 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x126fb8 6 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.exec 0x126fc0 (StorePre 0x126fc0 4 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x126fc0 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126fc0 6 (.base 14 (.d8 0x8))) (Reg.operands [.gpr 6, .gpr 14] [])) #v[66, 14]
    (.letOp (n := 69) (.exec 0x126fc4 (StorePre 0x126fc4 4 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x126fc4 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x126fc4 15 (.base 14 (.d8 0x18))) (Reg.operands [.gpr 15, .gpr 14] [])) #v[15, 14]
    (.letOp (n := 70) (.out 0x126fc8 (movR64M64Effect 0x126fc8 15 (.base 14 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 14] []) (.reg (.gpr 15))) #v[14]
    (.letOp (n := 71) (.exec 0x126fc8 (LoadPre 0x126fc8 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x126fc8 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x126fc8 15 (.base 14 (.d8 0x10))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x126fcc (cmpR64Imm8Effect 0x126fcc 15 0x1) (EffectPart.reads (.flag .CF) [.gpr 15] []) (.flag .CF)) #v[70]
    (.letOp (n := 73) (.exec 0x126fcc (fun s => s.RIP = 0x126fcc) (cmpR64Imm8Effect 0x126fcc 15 0x1) (Reg.operands [.gpr 15] [])) #v[70]
    (.letOp (n := 74) (.out 0x126fd0 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x126fd0 15 0xff)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 15))) #v[70, 72]
    (.letOp (n := 75) (.exec 0x126fd0 (fun s => s.RIP = 0x126fd0) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x126fd0 15 0xff)) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[70, 72]
    (.letOp (n := 76) (.exec 0x126fd4 (StorePre 0x126fd4 4 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x126fd4 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126fd4 15 (.base 14 (.d8 0x10))) (Reg.operands [.gpr 15, .gpr 14] [])) #v[74, 14]
    (.letOp (n := 77) (.out 0x126fd8 (cmpR32Imm8Effect 0x126fd8 3 7 0x2) (EffectPart.reads (.flag .ZF) [.gpr 7] []) (.flag .ZF)) #v[7]
    (.letOp (n := 78) (.exec 0x126fd8 (fun s => s.RIP = 0x126fd8) (cmpR32Imm8Effect 0x126fd8 3 7 0x2) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 79) (.out 0x126fdb (atFlags (condHolds 5) (setccR8Effect 0x126fdb 4 15)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 15))) #v[74, 77]
    (.letOp (n := 80) (.exec 0x126fdb (fun s => s.RIP = 0x126fdb) (atFlags (condHolds 5) (setccR8Effect 0x126fdb 4 15)) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[74, 77]
    (.letOp (n := 81) (.out 0x126fdf (orR8R8Effect 0x126fdf 3 15 2) (EffectPart.reads (.flag .ZF) [.gpr 15, .gpr 2] []) (.flag .ZF)) #v[79, 61]
    (.letOp (n := 82) (.exec 0x126fdf (fun s => s.RIP = 0x126fdf) (orR8R8Effect 0x126fdf 3 15 2) (Reg.operands [.gpr 15, .gpr 2] [])) #v[79, 61]
    (.letOp (n := 83) (.pure (condOp 4)) #v[81]
    (.terminate (.condBr (Fin.last 83) ⟨.l127063, RegMap.args [(0, 0), (1, 1), (2, 61), (3, 3), (4, 4), (5, 55), (6, 66), (7, 7), (8, 8), (9, 9), (10, 57), (11, 11), (12, 12), (13, 13), (14, 14), (19, 81), (22, 22), (39, 39), (50, 50), (51, 51)] 84⟩ ⟨.l126fe4, RegMap.args [(0, 0), (1, 1), (2, 61), (3, 3), (4, 4), (5, 55), (6, 66), (7, 7), (8, 8), (9, 9), (10, 57), (11, 11), (12, 12), (13, 13), (14, 14), (19, 81), (22, 22), (39, 39), (50, 50), (51, 51)] 84⟩))))))))))))))))))))))))))))))))

def bytes_l126f9f : List UInt8 :=
  [0x45, 0x8B, 0x56, 0x18, 0x41, 0x8B, 0x6E, 0x1C, 0x41, 0x29, 0xEA, 0x0F, 0x96, 0xC2, 0x48, 0x8B,
    0xB4, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x49, 0x89, 0x36, 0x48, 0x8B, 0xB4, 0x24, 0x98, 0x00, 0x00,
    0x00, 0x49, 0x89, 0x76, 0x08, 0x45, 0x89, 0x7E, 0x18, 0x4D, 0x8B, 0x7E, 0x10, 0x49, 0x83, 0xFF,
    0x01, 0x49, 0x83, 0xD7, 0xFF, 0x4D, 0x89, 0x7E, 0x10, 0x83, 0xFF, 0x02, 0x41, 0x0F, 0x95, 0xC7,
    0x41, 0x08, 0xD7, 0x74, 0x7F]

theorem code_l126f9f : ∀ x ∈ codeRange 0x126f9f bytes_l126f9f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26f9f 69 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126fe4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126fe4 (movR64Imm64Effect 0x126fe4 2 0xff00000000) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 54) (.exec 0x126fe4 (fun s => s.RIP = 0x126fe4) (movR64Imm64Effect 0x126fe4 2 0xff00000000) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x126fee (andR64R64Effect 0x126fee 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2] []) (.reg (.gpr 9))) #v[9, 53]
    (.letOp (n := 56) (.exec 0x126fee (fun s => s.RIP = 0x126fee) (andR64R64Effect 0x126fee 9 2) (Reg.operands [.gpr 9, .gpr 2] [])) #v[9, 53]
    (.letOp (n := 57) (.out 0x126ff1 (orR64R64Effect 0x126ff1 9 11) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 11] []) (.reg (.gpr 9))) #v[55, 11]
    (.letOp (n := 58) (.exec 0x126ff1 (fun s => s.RIP = 0x126ff1) (orR64R64Effect 0x126ff1 9 11) (Reg.operands [.gpr 9, .gpr 11] [])) #v[55, 11]
    (.letOp (n := 59) (.out 0x126ff4 (movR64M64Effect 0x126ff4 2 (.sib 4 none 0 (.d8 0x6f))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 60) (.exec 0x126ff4 (LoadPre 0x126ff4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6f)) s (0x126ff4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126ff4 2 (.sib 4 none 0 (.d8 0x6f))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x126ff9 (StorePre 0x126ff9 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x8f)) s (0x126ff9 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x126ff9 2 (.sib 4 none 0 (.d32 0x8f))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x127001 (movR64M64Effect 0x127001 2 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 63) (.exec 0x127001 (LoadPre 0x127001 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x127001 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x127001 2 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x127006 (StorePre 0x127006 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x127006 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x127006 2 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x12700e (movR64M64Effect 0x12700e 2 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 66) (.exec 0x12700e (LoadPre 0x12700e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x12700e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12700e 2 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x127013 (movR64M64Effect 0x127013 10 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 68) (.exec 0x127013 (LoadPre 0x127013 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x127013 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x127013 10 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.exec 0x127018 (StorePre 0x127018 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x127018 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x127018 10 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[67, 4]
    (.letOp (n := 70) (.exec 0x127020 (StorePre 0x127020 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x127020 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x127020 2 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 71) (.out 0x127025 (cmpR32Imm8Effect 0x127025 3 7 0x2) (EffectPart.reads (.flag .ZF) [.gpr 7] []) (.flag .ZF)) #v[7]
    (.letOp (n := 72) (.exec 0x127025 (fun s => s.RIP = 0x127025) (cmpR32Imm8Effect 0x127025 3 7 0x2) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 73) (.pure (condOp 5)) #v[71]
    (.terminate (.condBr (Fin.last 73) ⟨.l127079, RegMap.args [(0, 0), (1, 1), (2, 65), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 57), (10, 67), (11, 11), (13, 13), (19, 71), (22, 22), (39, 39), (50, 50), (51, 51)] 74⟩ ⟨.l12702a, RegMap.args [(0, 0), (1, 1), (2, 65), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 57), (10, 67), (11, 11), (13, 13), (19, 71), (22, 22), (39, 39), (50, 50), (51, 51)] 74⟩))))))))))))))))))))))

def bytes_l126fe4 : List UInt8 :=
  [0x48, 0xBA, 0x00, 0x00, 0x00, 0x00, 0xFF, 0x00, 0x00, 0x00, 0x49, 0x21, 0xD1, 0x4D, 0x09, 0xD9,
    0x48, 0x8B, 0x54, 0x24, 0x6F, 0x48, 0x89, 0x94, 0x24, 0x8F, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x54,
    0x24, 0x68, 0x48, 0x89, 0x94, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x54, 0x24, 0x58, 0x4C,
    0x8B, 0x54, 0x24, 0x60, 0x4C, 0x89, 0x94, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0x89, 0x54, 0x24,
    0x78, 0x83, 0xFF, 0x02, 0x75, 0x4F]

theorem code_l126fe4 : ∀ x ∈ codeRange 0x126fe4 bytes_l126fe4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26fe4 70 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12702a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12702a (andR32Imm32Effect 0x12702a 6 1 0xffffff00) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1]
    (.letOp (n := 54) (.exec 0x12702a (fun s => s.RIP = 0x12702a) (andR32Imm32Effect 0x12702a 6 1 0xffffff00) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 55) (.out 0x127030 (movzxR32R8Effect 0x127030 3 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 56) (.exec 0x127030 (fun s => s.RIP = 0x127030) (movzxR32R8Effect 0x127030 3 0 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 57) (.out 0x127033 (orR64R64Effect 0x127033 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[55, 53]
    (.letOp (n := 58) (.exec 0x127033 (fun s => s.RIP = 0x127033) (orR64R64Effect 0x127033 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[55, 53]
    (.letOp (n := 59) (.out 0x127036 (orR64R64Effect 0x127036 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[57, 9]
    (.letOp (n := 60) (.exec 0x127036 (fun s => s.RIP = 0x127036) (orR64R64Effect 0x127036 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[57, 9]
    (.letOp (n := 61) (.out 0x127039 (movR32M32LowEffect 0x127039 1 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 62) (.exec 0x127039 (LoadPre 0x127039 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x127039 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x127039 1 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x12703d (movR32M32LowEffect 0x12703d 2 (.sib 4 none 0 (.d8 0x5b))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 64) (.exec 0x12703d (LoadPre 0x12703d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5b)) s (0x12703d + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x12703d 2 (.sib 4 none 0 (.d8 0x5b))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.exec 0x127041 (StorePre 0x127041 3 (fun s => AddrMode.addr (.base 3 (.d8 0x1c)) s (0x127041 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x127041 2 (.base 3 (.d8 0x1c))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[63, 3]
    (.letOp (n := 66) (.exec 0x127044 (StorePre 0x127044 3 (fun s => AddrMode.addr (.base 3 (.d8 0x19)) s (0x127044 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x127044 1 (.base 3 (.d8 0x19))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 67) (.exec 0x127047 (StorePre 0x127047 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x127047 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x127047 0 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[59, 3]
    (.letOp (n := 68) (.out 0x12704b (movR64M64Effect 0x12704b 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 69) (.exec 0x12704b (LoadPre 0x12704b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x12704b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12704b 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.exec 0x127050 (StorePre 0x127050 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x127050 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x127050 0 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[68, 3]
    (.letOp (n := 71) (.exec 0x127054 (StorePre 0x127054 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x127054 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x127054 4 13 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 13, .gpr 3] [])) #v[13, 3]
    (.letOp (n := 72) (.exec 0x127058 (StorePre 0x127058 6 (fun s => AddrMode.addr (.base 3 .none) s (0x127058 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x127058 6 (.base 3 .none) 0x2) (Reg.operands [.gpr 3] [])) #v[3]
    (.terminate (.br ⟨.l126e71, RegMap.args [(0, 68), (1, 61), (2, 63), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)] 73⟩)))))))))))))))))))))

def bytes_l12702a : List UInt8 :=
  [0x81, 0xE1, 0x00, 0xFF, 0xFF, 0xFF, 0x0F, 0xB6, 0xC0, 0x48, 0x09, 0xC8, 0x4C, 0x09, 0xC8, 0x8B,
    0x4C, 0x24, 0x58, 0x8B, 0x54, 0x24, 0x5B, 0x89, 0x53, 0x1C, 0x89, 0x4B, 0x19, 0x48, 0x89, 0x43,
    0x08, 0x48, 0x8B, 0x44, 0x24, 0x10, 0x48, 0x89, 0x43, 0x10, 0x44, 0x88, 0x6B, 0x18, 0xC7, 0x03,
    0x02, 0x00, 0x00, 0x00, 0xE9, 0x0E, 0xFE, 0xFF, 0xFF]

theorem code_l12702a : ∀ x ∈ codeRange 0x12702a bytes_l12702a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2702a 57 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127063 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x127063 (StorePre 0x127063 5 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x127063 + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x127063 (.base 14 (.d8 0x20)) 0x1) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 54) (.out 0x127068 (movR32Imm32Effect 0x127068 5 0 0x13) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 55) (.exec 0x127068 (fun s => s.RIP = 0x127068) (movR32Imm32Effect 0x127068 5 0 0x13) (Reg.operands [] [])) #v[]
    (.letOp (n := 56) (.out 0x12706d (xorR32R32Effect 0x12706d 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[6, 6]
    (.letOp (n := 57) (.exec 0x12706d (fun s => s.RIP = 0x12706d) (xorR32R32Effect 0x12706d 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 58) (.out 0x12706f (movR32R32Effect 0x12706f 3 15 5) (EffectPart.reads (.reg (.gpr 15)) [.gpr 5] []) (.reg (.gpr 15))) #v[5]
    (.letOp (n := 59) (.exec 0x12706f (fun s => s.RIP = 0x12706f) (movR32R32Effect 0x12706f 3 15 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 60) (.out 0x127072 (xorR32R32Effect 0x127072 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[1, 1]
    (.letOp (n := 61) (.exec 0x127072 (fun s => s.RIP = 0x127072) (xorR32R32Effect 0x127072 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[1, 1]
    (.terminate (.br ⟨.l126e06, RegMap.args [(0, 54), (1, 60), (3, 3), (4, 4), (5, 5), (6, 56), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩))))))))))

def bytes_l127063 : List UInt8 :=
  [0x41, 0xC6, 0x46, 0x20, 0x01, 0xB8, 0x13, 0x00, 0x00, 0x00, 0x31, 0xF6, 0x41, 0x89, 0xEF, 0x31,
    0xC9, 0xE9, 0x8D, 0xFD, 0xFF, 0xFF]

theorem code_l127063 : ∀ x ∈ codeRange 0x127063 bytes_l127063, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27063 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127079 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x127079 (movzxR32M8Effect 0x127079 6 15 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 54) (.exec 0x127079 (LoadPre 0x127079 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x127079 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x127079 6 15 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x12707f (orR32R32Effect 0x12707f 3 15 8) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 8] []) (.reg (.gpr 15))) #v[53, 8]
    (.letOp (n := 56) (.exec 0x12707f (fun s => s.RIP = 0x12707f) (orR32R32Effect 0x12707f 3 15 8) (Reg.operands [.gpr 15, .gpr 8] [])) #v[53, 8]
    (.letOp (n := 57) (.out 0x127082 (shrR64Effect 0x127082 4 9 32) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[9]
    (.letOp (n := 58) (.exec 0x127082 (fun s => s.RIP = 0x127082) (shrR64Effect 0x127082 4 9 32) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[9]
    (.letOp (n := 59) (.out 0x127086 (movR64Imm64Effect 0x127086 6 0xffffffff00000000) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 60) (.exec 0x127086 (fun s => s.RIP = 0x127086) (movR64Imm64Effect 0x127086 6 0xffffffff00000000) (Reg.operands [] [])) #v[]
    (.letOp (n := 61) (.out 0x127090 (movR64M64Effect 0x127090 10 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 62) (.exec 0x127090 (LoadPre 0x127090 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x127090 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x127090 10 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x127095 (andR64R64Effect 0x127095 6 10) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 10] []) (.reg (.gpr 6))) #v[59, 61]
    (.letOp (n := 64) (.exec 0x127095 (fun s => s.RIP = 0x127095) (andR64R64Effect 0x127095 6 10) (Reg.operands [.gpr 6, .gpr 10] [])) #v[59, 61]
    (.letOp (n := 65) (.out 0x127098 (movR32R32Effect 0x127098 3 12 7) (EffectPart.reads (.reg (.gpr 12)) [.gpr 7] []) (.reg (.gpr 12))) #v[7]
    (.letOp (n := 66) (.exec 0x127098 (fun s => s.RIP = 0x127098) (movR32R32Effect 0x127098 3 12 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 67) (.out 0x12709b (movR32R32Effect 0x12709b 3 5 9) (EffectPart.reads (.reg (.gpr 5)) [.gpr 9] []) (.reg (.gpr 5))) #v[57]
    (.letOp (n := 68) (.exec 0x12709b (fun s => s.RIP = 0x12709b) (movR32R32Effect 0x12709b 3 5 9) (Reg.operands [.gpr 9] [])) #v[57]
    (.terminate (.br ⟨.l126e06, RegMap.args [(0, 0), (1, 1), (3, 3), (4, 4), (5, 67), (6, 63), (7, 7), (8, 8), (9, 57), (10, 61), (11, 11), (12, 65), (13, 13), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 69⟩)))))))))))))))))

def bytes_l127079 : List UInt8 :=
  [0x44, 0x0F, 0xB6, 0x7C, 0x24, 0x0C, 0x45, 0x09, 0xC7, 0x49, 0xC1, 0xE9, 0x20, 0x48, 0xBE, 0x00,
    0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF, 0x4C, 0x8B, 0x54, 0x24, 0x10, 0x4C, 0x21, 0xD6, 0x41,
    0x89, 0xFC, 0x44, 0x89, 0xCD, 0xE9, 0x63, 0xFD, 0xFF, 0xFF]

theorem code_l127079 : ∀ x ∈ codeRange 0x127079 bytes_l127079, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27079 42 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1270a3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1270a3 (movR64Imm64Effect 0x1270a3 9 0x200000000) (EffectPart.reads (.reg (.gpr 9)) [] []) (.reg (.gpr 9))) #v[]
    (.letOp (n := 54) (.exec 0x1270a3 (fun s => s.RIP = 0x1270a3) (movR64Imm64Effect 0x1270a3 9 0x200000000) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x1270ad (movR32Imm32Effect 0x1270ad 5 0 0x15) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 56) (.exec 0x1270ad (fun s => s.RIP = 0x1270ad) (movR32Imm32Effect 0x1270ad 5 0 0x15) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x1270b2 (cmpR8Imm8Effect 0x1270b2 4 13 0x7) (EffectPart.reads (.flag .CF) [.gpr 13] []) (.flag .CF)) #v[13]
    (.letOp (n := 58) (.out 0x1270b2 (cmpR8Imm8Effect 0x1270b2 4 13 0x7) (EffectPart.reads (.flag .ZF) [.gpr 13] []) (.flag .ZF)) #v[13]
    (.letOp (n := 59) (.exec 0x1270b2 (fun s => s.RIP = 0x1270b2) (cmpR8Imm8Effect 0x1270b2 4 13 0x7) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 60) (.pure (condOp 7)) #v[57, 58]
    (.terminate (.condBr (Fin.last 60) ⟨.l1270ca, RegMap.args [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩ ⟨.l1270b8, RegMap.args [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩)))))))))

def bytes_l1270a3 : List UInt8 :=
  [0x49, 0xB9, 0x00, 0x00, 0x00, 0x00, 0x02, 0x00, 0x00, 0x00, 0xB8, 0x15, 0x00, 0x00, 0x00, 0x41,
    0x80, 0xFD, 0x07, 0x77, 0x12]

theorem code_l1270a3 : ∀ x ∈ codeRange 0x1270a3 bytes_l1270a3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x270a3 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1270b8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1270b8 (testR8R8Effect 0x1270b8 3 13 13) (EffectPart.reads (.flag .ZF) [.gpr 13, .gpr 13] []) (.flag .ZF)) #v[13, 13]
    (.letOp (n := 54) (.exec 0x1270b8 (fun s => s.RIP = 0x1270b8) (testR8R8Effect 0x1270b8 3 13 13) (Reg.operands [.gpr 13, .gpr 13] [])) #v[13, 13]
    (.letOp (n := 55) (.out 0x1270bb (atFlags (condHolds 5) (setccR8Effect 0x1270bb 3 1)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 1))) #v[1, 53]
    (.letOp (n := 56) (.exec 0x1270bb (fun s => s.RIP = 0x1270bb) (atFlags (condHolds 5) (setccR8Effect 0x1270bb 3 1)) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[1, 53]
    (.letOp (n := 57) (.out 0x1270be (testR64R64Effect 0x1270be 2 2) (EffectPart.reads (.flag .ZF) [.gpr 2, .gpr 2] []) (.flag .ZF)) #v[2, 2]
    (.letOp (n := 58) (.exec 0x1270be (fun s => s.RIP = 0x1270be) (testR64R64Effect 0x1270be 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 59) (.out 0x1270c1 (atFlags (condHolds 4) (setccR8Effect 0x1270c1 4 6)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 6))) #v[6, 57]
    (.letOp (n := 60) (.exec 0x1270c1 (fun s => s.RIP = 0x1270c1) (atFlags (condHolds 4) (setccR8Effect 0x1270c1 4 6)) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[6, 57]
    (.letOp (n := 61) (.out 0x1270c5 (testR8R8Effect 0x1270c5 3 1 6) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 6] []) (.flag .ZF)) #v[55, 59]
    (.letOp (n := 62) (.exec 0x1270c5 (fun s => s.RIP = 0x1270c5) (testR8R8Effect 0x1270c5 3 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[55, 59]
    (.letOp (n := 63) (.pure (condOp 4)) #v[61]
    (.terminate (.condBr (Fin.last 63) ⟨.l1270df, RegMap.args [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (6, 59), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 61), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ ⟨.l1270ca, RegMap.args [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (6, 59), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 61), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩))))))))))))

def bytes_l1270b8 : List UInt8 :=
  [0x45, 0x84, 0xED, 0x0F, 0x95, 0xC1, 0x48, 0x85, 0xD2, 0x40, 0x0F, 0x94, 0xC6, 0x40, 0x84, 0xF1,
    0x74, 0x15]

theorem code_l1270b8 : ∀ x ∈ codeRange 0x1270b8 bytes_l1270b8, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x270b8 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1270ca : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1270ca (xorR32R32Effect 0x1270ca 3 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 8] []) (.reg (.gpr 8))) #v[8, 8]
    (.letOp (n := 54) (.exec 0x1270ca (fun s => s.RIP = 0x1270ca) (xorR32R32Effect 0x1270ca 3 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[8, 8]
    (.letOp (n := 55) (.exec 0x1270cd (StorePre 0x1270cd 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x1270cd + BitVec.ofNat 64 8)) 4) (movM32Imm32Effect 0x1270cd 8 (.sib 4 none 0 (.d8 0xc)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x1270d5 (xorR32R32Effect 0x1270d5 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[1, 1]
    (.letOp (n := 57) (.exec 0x1270d5 (fun s => s.RIP = 0x1270d5) (xorR32R32Effect 0x1270d5 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[1, 1]
    (.letOp (n := 58) (.out 0x1270d7 (xorR32R32Effect 0x1270d7 3 11 11) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 11] []) (.reg (.gpr 11))) #v[11, 11]
    (.letOp (n := 59) (.exec 0x1270d7 (fun s => s.RIP = 0x1270d7) (xorR32R32Effect 0x1270d7 3 11 11) (Reg.operands [.gpr 11, .gpr 11] [])) #v[11, 11]
    (.terminate (.br ⟨.l126f9d, RegMap.args [(0, 0), (1, 56), (2, 2), (3, 3), (4, 4), (7, 7), (8, 53), (9, 9), (11, 58), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l1270ca : List UInt8 :=
  [0x45, 0x31, 0xC0, 0xC7, 0x44, 0x24, 0x0C, 0x00, 0x00, 0x00, 0x00, 0x31, 0xC9, 0x45, 0x31, 0xDB,
    0xE9, 0xBE, 0xFE, 0xFF, 0xFF]

theorem code_l1270ca : ∀ x ∈ codeRange 0x1270ca bytes_l1270ca, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x270ca 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1270df : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1270df (movzxR32R8Effect 0x1270df 4 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[13]
    (.letOp (n := 54) (.exec 0x1270df (fun s => s.RIP = 0x1270df) (movzxR32R8Effect 0x1270df 4 0 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 55) (.out 0x1270e3 (leaR64Effect 0x1270e3 1 (.abs (some 2) 3 0x0)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2]
    (.letOp (n := 56) (.exec 0x1270e3 (fun s => s.RIP = 0x1270e3) (leaR64Effect 0x1270e3 1 (.abs (some 2) 3 0x0)) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 57) (.out 0x1270eb (xorR32R32Effect 0x1270eb 3 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 8] []) (.reg (.gpr 8))) #v[8, 8]
    (.letOp (n := 58) (.exec 0x1270eb (fun s => s.RIP = 0x1270eb) (xorR32R32Effect 0x1270eb 3 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[8, 8]
    (.letOp (n := 59) (.out 0x1270ee (cmpR64R64Effect 0x1270ee 1 0) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 0] []) (.flag .CF)) #v[55, 53]
    (.letOp (n := 60) (.exec 0x1270ee (fun s => s.RIP = 0x1270ee) (cmpR64R64Effect 0x1270ee 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[55, 53]
    (.letOp (n := 61) (.pure (condOp 3)) #v[59]
    (.terminate (.condBr (Fin.last 61) ⟨.l1270fd, RegMap.args [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (7, 7), (8, 57), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ ⟨.l1270f3, RegMap.args [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (7, 7), (8, 57), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩))))))))))

def bytes_l1270df : List UInt8 :=
  [0x41, 0x0F, 0xB6, 0xC5, 0x48, 0x8D, 0x0C, 0xD5, 0x00, 0x00, 0x00, 0x00, 0x45, 0x31, 0xC0, 0x48,
    0x39, 0xC1, 0x73, 0x0A]

theorem code_l1270df : ∀ x ∈ codeRange 0x1270df bytes_l1270df, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x270df 20 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1270f3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1270f3 (movR32Imm32Effect 0x1270f3 5 0 0xc) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 54) (.exec 0x1270f3 (fun s => s.RIP = 0x1270f3) (movR32Imm32Effect 0x1270f3 5 0 0xc) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l126f8d, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l1270f3 : List UInt8 :=
  [0xB8, 0x0C, 0x00, 0x00, 0x00, 0xE9, 0x90, 0xFE, 0xFF, 0xFF]

theorem code_l1270f3 : ∀ x ∈ codeRange 0x1270f3 bytes_l1270f3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x270f3 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1270fd : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1270fd (StorePre 0x1270fd 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1270fd + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1270fd 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2, 4]
    (.letOp (n := 54) (.out 0x127102 (movR64M64Effect 0x127102 1 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 55) (.exec 0x127102 (LoadPre 0x127102 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x127102 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x127102 1 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x127107 (movR64Imm64Effect 0x127107 11 0xffffff0000000000) (EffectPart.reads (.reg (.gpr 11)) [] []) (.reg (.gpr 11))) #v[]
    (.letOp (n := 57) (.exec 0x127107 (fun s => s.RIP = 0x127107) (movR64Imm64Effect 0x127107 11 0xffffff0000000000) (Reg.operands [] [])) #v[]
    (.letOp (n := 58) (.out 0x127111 (andR64R64Effect 0x127111 11 1) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 1] []) (.reg (.gpr 11))) #v[56, 54]
    (.letOp (n := 59) (.exec 0x127111 (fun s => s.RIP = 0x127111) (andR64R64Effect 0x127111 11 1) (Reg.operands [.gpr 11, .gpr 1] [])) #v[56, 54]
    (.letOp (n := 60) (.out 0x127114 (movR32Imm32Effect 0x127114 5 7 0x2) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 61) (.exec 0x127114 (fun s => s.RIP = 0x127114) (movR32Imm32Effect 0x127114 5 7 0x2) (Reg.operands [] [])) #v[]
    (.letOp (n := 62) (.exec 0x127119 (StorePre 0x127119 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x127119 + BitVec.ofNat 64 8)) 4) (movM32Imm32Effect 0x127119 8 (.sib 4 none 0 (.d8 0xc)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.br ⟨.l126f7d, RegMap.args [(1, 54), (2, 2), (3, 3), (4, 4), (7, 60), (8, 8), (11, 58), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 63⟩)))))))))))

def bytes_l1270fd : List UInt8 :=
  [0x48, 0x89, 0x54, 0x24, 0x10, 0x48, 0x8B, 0x4C, 0x24, 0x20, 0x49, 0xBB, 0x00, 0x00, 0x00, 0x00,
    0x00, 0xFF, 0xFF, 0xFF, 0x49, 0x21, 0xCB, 0xBF, 0x02, 0x00, 0x00, 0x00, 0xC7, 0x44, 0x24, 0x0C,
    0x00, 0x00, 0x00, 0x00, 0xE9, 0x57, 0xFE, 0xFF, 0xFF]

theorem code_l1270fd : ∀ x ∈ codeRange 0x1270fd bytes_l1270fd, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x270fd 41 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127126 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x127126 (xorR32R32Effect 0x127126 3 12 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 12] []) (.reg (.gpr 12))) #v[12, 12]
    (.letOp (n := 54) (.exec 0x127126 (fun s => s.RIP = 0x127126) (xorR32R32Effect 0x127126 3 12 12) (Reg.operands [.gpr 12, .gpr 12] [])) #v[12, 12]
    (.letOp (n := 55) (.out 0x127129 (movR32Imm32Effect 0x127129 5 0 0xc) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 56) (.exec 0x127129 (fun s => s.RIP = 0x127129) (movR32Imm32Effect 0x127129 5 0 0xc) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x12712e (xorR32R32Effect 0x12712e 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[6, 6]
    (.letOp (n := 58) (.exec 0x12712e (fun s => s.RIP = 0x12712e) (xorR32R32Effect 0x12712e 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 59) (.out 0x127130 (xorR32R32Effect 0x127130 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[1, 1]
    (.letOp (n := 60) (.exec 0x127130 (fun s => s.RIP = 0x127130) (xorR32R32Effect 0x127130 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[1, 1]
    (.terminate (.br ⟨.l126e06, RegMap.args [(0, 55), (1, 59), (3, 3), (4, 4), (5, 5), (6, 57), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩)))))))))

def bytes_l127126 : List UInt8 :=
  [0x45, 0x31, 0xE4, 0xB8, 0x0C, 0x00, 0x00, 0x00, 0x31, 0xF6, 0x31, 0xC9, 0xE9, 0xCF, 0xFC, 0xFF,
    0xFF]

theorem code_l127126 : ∀ x ∈ codeRange 0x127126 bytes_l127126, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27126 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127137 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x127137 (movR32Imm32Effect 0x127137 5 7 0x1) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 54) (.exec 0x127137 (fun s => s.RIP = 0x127137) (movR32Imm32Effect 0x127137 5 7 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x12713c (movR64Imm32Effect 0x12713c 2 0x2036e0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 56) (.exec 0x12713c (fun s => s.RIP = 0x12713c) (movR64Imm32Effect 0x12713c 2 0x2036e0) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x127143 (callEffect (fun _ => 0x129c90) 0x127148) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x127143 (PushPre 0x127143 5) (callEffect (fun _ => 0x129c90) 0x127148) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x127148⟩) #v[]
    (.terminate (.call ⟨.l129c90, RegMap.args [(2, 55), (4, 57), (5, 5), (6, 6), (7, 53)] 60⟩ { target := .l127148, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l127137 : List UInt8 :=
  [0xBF, 0x01, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC2, 0xE0, 0x36, 0x20, 0x00, 0xE8, 0x48, 0x2B, 0x00,
    0x00]

theorem code_l127137 : ∀ x ∈ codeRange 0x127137 bytes_l127137, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27137 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127148 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x127148 (fun s => s.RIP = 0x127148) (fun _ => nopEffect 0x127148 8) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l127150, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 54⟩))

def bytes_l127148 : List UInt8 :=
  [0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem code_l127148 : ∀ x ∈ codeRange 0x127148 bytes_l127148, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27148 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127150 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x127150 (pushR64Effect 0x127150 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x127150 (PushPre 0x127150 1) (pushR64Effect 0x127150 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x127151 (pushR64Effect 0x127151 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x127151 (PushPre 0x127151 2) (pushR64Effect 0x127151 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x127153 (pushR64Effect 0x127153 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x127153 (PushPre 0x127153 2) (pushR64Effect 0x127153 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x127155 (pushR64Effect 0x127155 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x127155 (PushPre 0x127155 2) (pushR64Effect 0x127155 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x127157 (pushR64Effect 0x127157 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x127157 (PushPre 0x127157 2) (pushR64Effect 0x127157 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x127159 (pushR64Effect 0x127159 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x127159 (PushPre 0x127159 1) (pushR64Effect 0x127159 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x12715a (subR64Imm32Effect 0x12715a 4 0x88) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x12715a (fun s => s.RIP = 0x12715a) (subR64Imm32Effect 0x12715a 4 0x88) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x127161 (movR64R64Effect 0x127161 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 68) (.exec 0x127161 (fun s => s.RIP = 0x127161) (movR64R64Effect 0x127161 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 69) (.out 0x127164 (movR32M32LowEffect 0x127164 5 (.base 2 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[2]
    (.letOp (n := 70) (.exec 0x127164 (LoadPre 0x127164 (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x127164 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x127164 5 (.base 2 (.d8 0x8))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 71) (.out 0x127167 (movR32M32Effect 0x127167 15 (.base 6 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 6] []) (.reg (.gpr 15))) #v[6]
    (.letOp (n := 72) (.exec 0x127167 (LoadPre 0x127167 (fun s => AddrMode.addr (.base 6 (.d8 0x1c)) s (0x127167 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x127167 15 (.base 6 (.d8 0x1c))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 73) (.out 0x12716b (movR32R32Effect 0x12716b 3 13 15) (EffectPart.reads (.reg (.gpr 13)) [.gpr 15] []) (.reg (.gpr 13))) #v[71]
    (.letOp (n := 74) (.exec 0x12716b (fun s => s.RIP = 0x12716b) (movR32R32Effect 0x12716b 3 13 15) (Reg.operands [.gpr 15] [])) #v[71]
    (.letOp (n := 75) (.out 0x12716e (addR32R32Effect 0x12716e 3 13 5) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 5] []) (.reg (.gpr 13))) #v[73, 69]
    (.letOp (n := 76) (.out 0x12716e (addR32R32Effect 0x12716e 3 13 5) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 5] []) (.flag .CF)) #v[73, 69]
    (.letOp (n := 77) (.exec 0x12716e (fun s => s.RIP = 0x12716e) (addR32R32Effect 0x12716e 3 13 5) (Reg.operands [.gpr 13, .gpr 5] [])) #v[73, 69]
    (.letOp (n := 78) (.pure (condOp 2)) #v[76]
    (.terminate (.condBr (Fin.last 78) ⟨.l1273aa, RegMap.args [(1, 1), (2, 2), (3, 67), (4, 65), (5, 69), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 75), (14, 14), (15, 71), (16, 76), (22, 22), (39, 39), (50, 50), (51, 51)] 79⟩ ⟨.l127177, RegMap.args [(1, 1), (2, 2), (3, 67), (4, 65), (5, 69), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 75), (14, 14), (15, 71), (16, 76), (22, 22), (39, 39), (50, 50), (51, 51)] 79⟩)))))))))))))))))))))))))))

def bytes_l127150 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0x88, 0x00, 0x00,
    0x00, 0x48, 0x89, 0xFB, 0x8B, 0x6A, 0x08, 0x44, 0x8B, 0x7E, 0x1C, 0x45, 0x89, 0xFD, 0x41, 0x01,
    0xED, 0x0F, 0x82, 0x33, 0x02, 0x00, 0x00]

theorem code_l127150 : ∀ x ∈ codeRange 0x127150 bytes_l127150, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27150 39 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127177 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x127177 (movR64R64Effect 0x127177 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 6] []) (.reg (.gpr 14))) #v[6]
    (.letOp (n := 54) (.exec 0x127177 (fun s => s.RIP = 0x127177) (movR64R64Effect 0x127177 14 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 55) (.out 0x12717a (movR64M64Effect 0x12717a 6 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[6]
    (.letOp (n := 56) (.exec 0x12717a (LoadPre 0x12717a (fun s => AddrMode.addr (.base 6 .none) s (0x12717a + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x12717a 6 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 57) (.out 0x12717d (movR64M64Effect 0x12717d 12 (.base 14 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 14] []) (.reg (.gpr 12))) #v[53]
    (.letOp (n := 58) (.exec 0x12717d (LoadPre 0x12717d (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x12717d + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12717d 12 (.base 14 (.d8 0x8))) (Reg.operands [.gpr 14] [])) #v[53]
    (.letOp (n := 59) (.out 0x127181 (leaR64Effect 0x127181 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 60) (.exec 0x127181 (fun s => s.RIP = 0x127181) (leaR64Effect 0x127181 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x127186 (StorePre 0x127186 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x127186 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x127186 6 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 62) (.out 0x12718b (movR64R64Effect 0x12718b 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12] []) (.reg (.gpr 2))) #v[57]
    (.letOp (n := 63) (.exec 0x12718b (fun s => s.RIP = 0x12718b) (movR64R64Effect 0x12718b 2 12) (Reg.operands [.gpr 12] [])) #v[57]
    (.letOp (n := 64) (.out 0x12718e (movR32R32Effect 0x12718e 3 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 13] []) (.reg (.gpr 1))) #v[13]
    (.letOp (n := 65) (.exec 0x12718e (fun s => s.RIP = 0x12718e) (movR32R32Effect 0x12718e 3 1 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 66) (.out 0x127191 (callEffect (fun _ => 0x127c50) 0x127196) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 67) (.exec 0x127191 (PushPre 0x127191 5) (callEffect (fun _ => 0x127c50) 0x127196) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.const ⟨64, 0x127196⟩) #v[]
    (.terminate (.call ⟨.l127c50, RegMap.args [(1, 64), (2, 62), (3, 3), (4, 66), (5, 5), (6, 55), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 69⟩ { target := .l127196, kept := #v[], arity := rfl, guard := some (Fin.last 68) })))))))))))))))))

def bytes_l127177 : List UInt8 :=
  [0x49, 0x89, 0xF6, 0x48, 0x8B, 0x36, 0x4D, 0x8B, 0x66, 0x08, 0x48, 0x8D, 0x7C, 0x24, 0x08, 0x48,
    0x89, 0x74, 0x24, 0x40, 0x4C, 0x89, 0xE2, 0x44, 0x89, 0xE9, 0xE8, 0xBA, 0x0A, 0x00, 0x00]

theorem code_l127177 : ∀ x ∈ codeRange 0x127177 bytes_l127177, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27177 31 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127196 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x127196 (movR32M32LowEffect 0x127196 1 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x127196 (LoadPre 0x127196 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x127196 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x127196 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x12719a (cmpR32Imm8Effect 0x12719a 3 1 0x2) (EffectPart.reads (.flag .ZF) [.gpr 1] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x12719a (fun s => s.RIP = 0x12719a) (cmpR32Imm8Effect 0x12719a 3 1 0x2) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l1271c1, RegMap.args [(1, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l12719f, RegMap.args [(1, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l127196 : List UInt8 :=
  [0x8B, 0x4C, 0x24, 0x08, 0x83, 0xF9, 0x02, 0x75, 0x22]

theorem code_l127196 : ∀ x ∈ codeRange 0x127196 bytes_l127196, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27196 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12719f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12719f (movR64M64Effect 0x12719f 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x12719f (LoadPre 0x12719f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x12719f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12719f 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1271a4 (movR64M64Effect 0x1271a4 1 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x1271a4 (LoadPre 0x1271a4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1271a4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1271a4 1 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x1271a9 (StorePre 0x1271a9 3 (fun s => AddrMode.addr (.base 14 .none) s (0x1271a9 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x1271a9 0 (.base 14 .none)) (Reg.operands [.gpr 0, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 58) (.exec 0x1271ac (StorePre 0x1271ac 4 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x1271ac + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1271ac 1 (.base 14 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x1271b0 (movR64M64Effect 0x1271b0 0 (.base 14 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[14]
    (.letOp (n := 60) (.exec 0x1271b0 (LoadPre 0x1271b0 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x1271b0 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1271b0 0 (.base 14 (.d8 0x10))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 61) (.out 0x1271b4 (cmpR64Imm8Effect 0x1271b4 0 0x3f) (EffectPart.reads (.flag .CF) [.gpr 0] []) (.flag .CF)) #v[59]
    (.letOp (n := 62) (.out 0x1271b4 (cmpR64Imm8Effect 0x1271b4 0 0x3f) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[59]
    (.letOp (n := 63) (.exec 0x1271b4 (fun s => s.RIP = 0x1271b4) (cmpR64Imm8Effect 0x1271b4 0 0x3f) (Reg.operands [.gpr 0] [])) #v[59]
    (.letOp (n := 64) (.pure (condOp 6)) #v[61, 62]
    (.terminate (.condBr (Fin.last 64) ⟨.l127206, RegMap.args [(0, 59), (1, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 61), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)] 65⟩ ⟨.l1271ba, RegMap.args [(0, 59), (1, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 61), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)] 65⟩)))))))))))))

def bytes_l12719f : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x10, 0x48, 0x8B, 0x4C, 0x24, 0x18, 0x49, 0x89, 0x06, 0x49, 0x89, 0x4E,
    0x08, 0x49, 0x8B, 0x46, 0x10, 0x48, 0x83, 0xF8, 0x3F, 0x76, 0x4C]

theorem code_l12719f : ∀ x ∈ codeRange 0x12719f bytes_l12719f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2719f 27 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1271ba : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1271ba (movR32Imm32Effect 0x1271ba 5 0 0x6) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 54) (.exec 0x1271ba (fun s => s.RIP = 0x1271ba) (movR32Imm32Effect 0x1271ba 5 0 0x6) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l127222, RegMap.args [(0, 53), (3, 3), (4, 4), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l1271ba : List UInt8 :=
  [0xB8, 0x06, 0x00, 0x00, 0x00, 0xEB, 0x61]

theorem code_l1271ba : ∀ x ∈ codeRange 0x1271ba bytes_l1271ba, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x271ba 7 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

end K256.Proofs.Generate.LIR
