import ChaCha20Poly1305.Proofs.Decrypt.Movsd
import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Labels
import ChaCha20Poly1305.Proofs.Common.CFG.EvalAttr
import ChaCha20Poly1305.Proofs.Common.Lift.Generated.Footprints

namespace ChaCha20Poly1305.Proofs.Decrypt.Lifted

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift

@[cfg_block] def b_l101db0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101db0 (andR32R32Effect 0x101db0 2 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[1, 7]
    (.letOp (n := 54) (.exec 0x101db0 (fun s => s.RIP = 0x101db0) (andR32R32Effect 0x101db0 2 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[1, 7]
    (.letOp (n := 55) (.out 0x101db2 (orR32R32Effect 0x101db2 2 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 3] []) (.reg (.gpr 1))) #v[53, 3]
    (.letOp (n := 56) (.exec 0x101db2 (fun s => s.RIP = 0x101db2) (orR32R32Effect 0x101db2 2 1 3) (Reg.operands [.gpr 1, .gpr 3] [])) #v[53, 3]
    (.letOp (n := 57) (.out 0x101db4 (andR32R32Effect 0x101db4 2 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 7] []) (.reg (.gpr 2))) #v[2, 7]
    (.letOp (n := 58) (.exec 0x101db4 (fun s => s.RIP = 0x101db4) (andR32R32Effect 0x101db4 2 2 7) (Reg.operands [.gpr 2, .gpr 7] [])) #v[2, 7]
    (.letOp (n := 59) (.out 0x101db6 (orR32R32Effect 0x101db6 3 2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 13] []) (.reg (.gpr 2))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x101db6 (fun s => s.RIP = 0x101db6) (orR32R32Effect 0x101db6 3 2 13) (Reg.operands [.gpr 2, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x101db9 (andR32R32Effect 0x101db9 3 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 8] []) (.reg (.gpr 7))) #v[7, 8]
    (.letOp (n := 62) (.exec 0x101db9 (fun s => s.RIP = 0x101db9) (andR32R32Effect 0x101db9 3 7 8) (Reg.operands [.gpr 7, .gpr 8] [])) #v[7, 8]
    (.letOp (n := 63) (.out 0x101dbc (orR32R32Effect 0x101dbc 3 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 14] []) (.reg (.gpr 7))) #v[61, 14]
    (.letOp (n := 64) (.exec 0x101dbc (fun s => s.RIP = 0x101dbc) (orR32R32Effect 0x101dbc 3 7 14) (Reg.operands [.gpr 7, .gpr 14] [])) #v[61, 14]
    (.letOp (n := 65) (.out 0x101dbf (movR32R32Effect 0x101dbf 3 8 9) (EffectPart.reads (.reg (.gpr 8)) [.gpr 9] []) (.reg (.gpr 8))) #v[9]
    (.letOp (n := 66) (.exec 0x101dbf (fun s => s.RIP = 0x101dbf) (movR32R32Effect 0x101dbf 3 8 9) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 67) (.out 0x101dc2 (shlR32Effect 0x101dc2 4 8 26) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[65]
    (.letOp (n := 68) (.exec 0x101dc2 (fun s => s.RIP = 0x101dc2) (shlR32Effect 0x101dc2 4 8 26) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[65]
    (.letOp (n := 69) (.out 0x101dc6 (orR32R32Effect 0x101dc6 3 8 10) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 10] []) (.reg (.gpr 8))) #v[67, 10]
    (.letOp (n := 70) (.exec 0x101dc6 (fun s => s.RIP = 0x101dc6) (orR32R32Effect 0x101dc6 3 8 10) (Reg.operands [.gpr 8, .gpr 10] [])) #v[67, 10]
    (.letOp (n := 71) (.out 0x101dc9 (shrR32Effect 0x101dc9 4 9 6) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[9]
    (.letOp (n := 72) (.exec 0x101dc9 (fun s => s.RIP = 0x101dc9) (shrR32Effect 0x101dc9 4 9 6) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[9]
    (.letOp (n := 73) (.out 0x101dcd (movR32R32Effect 0x101dcd 3 10 1) (EffectPart.reads (.reg (.gpr 10)) [.gpr 1] []) (.reg (.gpr 10))) #v[55]
    (.letOp (n := 74) (.exec 0x101dcd (fun s => s.RIP = 0x101dcd) (movR32R32Effect 0x101dcd 3 10 1) (Reg.operands [.gpr 1] [])) #v[55]
    (.letOp (n := 75) (.out 0x101dd0 (shlR32Effect 0x101dd0 4 10 20) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[73]
    (.letOp (n := 76) (.exec 0x101dd0 (fun s => s.RIP = 0x101dd0) (shlR32Effect 0x101dd0 4 10 20) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[73]
    (.letOp (n := 77) (.out 0x101dd4 (orR32R32Effect 0x101dd4 3 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9] []) (.reg (.gpr 10))) #v[75, 71]
    (.letOp (n := 78) (.exec 0x101dd4 (fun s => s.RIP = 0x101dd4) (orR32R32Effect 0x101dd4 3 10 9) (Reg.operands [.gpr 10, .gpr 9] [])) #v[75, 71]
    (.letOp (n := 79) (.out 0x101dd7 (shrR32Effect 0x101dd7 3 1 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[55]
    (.letOp (n := 80) (.exec 0x101dd7 (fun s => s.RIP = 0x101dd7) (shrR32Effect 0x101dd7 3 1 12) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[55]
    (.letOp (n := 81) (.out 0x101dda (movR32R32Effect 0x101dda 3 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[59]
    (.letOp (n := 82) (.exec 0x101dda (fun s => s.RIP = 0x101dda) (movR32R32Effect 0x101dda 3 9 2) (Reg.operands [.gpr 2] [])) #v[59]
    (.letOp (n := 83) (.out 0x101ddd (shlR32Effect 0x101ddd 4 9 14) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[81]
    (.letOp (n := 84) (.exec 0x101ddd (fun s => s.RIP = 0x101ddd) (shlR32Effect 0x101ddd 4 9 14) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[81]
    (.letOp (n := 85) (.out 0x101de1 (orR32R32Effect 0x101de1 3 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1] []) (.reg (.gpr 9))) #v[83, 79]
    (.letOp (n := 86) (.exec 0x101de1 (fun s => s.RIP = 0x101de1) (orR32R32Effect 0x101de1 3 9 1) (Reg.operands [.gpr 9, .gpr 1] [])) #v[83, 79]
    (.letOp (n := 87) (.out 0x101de4 (shrR32Effect 0x101de4 3 2 18) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[59]
    (.letOp (n := 88) (.exec 0x101de4 (fun s => s.RIP = 0x101de4) (shrR32Effect 0x101de4 3 2 18) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[59]
    (.letOp (n := 89) (.out 0x101de7 (shlR32Effect 0x101de7 3 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[63]
    (.letOp (n := 90) (.exec 0x101de7 (fun s => s.RIP = 0x101de7) (shlR32Effect 0x101de7 3 7 8) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[63]
    (.letOp (n := 91) (.out 0x101dea (orR32R32Effect 0x101dea 2 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2] []) (.reg (.gpr 7))) #v[89, 87]
    (.letOp (n := 92) (.exec 0x101dea (fun s => s.RIP = 0x101dea) (orR32R32Effect 0x101dea 2 7 2) (Reg.operands [.gpr 7, .gpr 2] [])) #v[89, 87]
    (.terminate (.br ⟨.l101dec, RegMap.args [(0, 0), (1, 79), (2, 87), (3, 3), (4, 4), (6, 6), (7, 91), (8, 69), (9, 85), (10, 77), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)] 93⟩)))))))))))))))))))))))))))))))))))))))))

def bytes_l101db0 : List UInt8 :=
  [0x21, 0xF9, 0x09, 0xD9, 0x21, 0xFA, 0x44, 0x09, 0xEA, 0x44, 0x21, 0xC7, 0x44, 0x09, 0xF7, 0x45,
    0x89, 0xC8, 0x41, 0xC1, 0xE0, 0x1A, 0x45, 0x09, 0xD0, 0x41, 0xC1, 0xE9, 0x06, 0x41, 0x89, 0xCA,
    0x41, 0xC1, 0xE2, 0x14, 0x45, 0x09, 0xCA, 0xC1, 0xE9, 0x0C, 0x41, 0x89, 0xD1, 0x41, 0xC1, 0xE1,
    0x0E, 0x41, 0x09, 0xC9, 0xC1, 0xEA, 0x12, 0xC1, 0xE7, 0x08, 0x09, 0xD7]

theorem code_l101db0 : ∀ x ∈ codeRange 0x101db0 bytes_l101db0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1db0 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101dec : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101dec (addR32M32Effect 0x101dec 3 8 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6] []) (.reg (.gpr 8))) #v[8, 6]
    (.letOp (n := 54) (.out 0x101dec (addR32M32Effect 0x101dec 3 8 (.base 6 .none)) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 6] []) (.flag .CF)) #v[8, 6]
    (.letOp (n := 55) (.exec 0x101dec (LoadPre 0x101dec (fun s => AddrMode.addr (.base 6 .none) s (0x101dec + BitVec.ofNat 64 3)) 4) (addR32M32Effect 0x101dec 3 8 (.base 6 .none)) (Reg.operands [.gpr 8, .gpr 6] [])) #v[8, 6]
    (.letOp (n := 56) (.out 0x101def (movR32M32LowEffect 0x101def 1 (.base 6 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[6]
    (.letOp (n := 57) (.exec 0x101def (LoadPre 0x101def (fun s => AddrMode.addr (.base 6 (.d8 0x4)) s (0x101def + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x101def 1 (.base 6 (.d8 0x4))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 58) (.out 0x101df2 (movR32M32LowEffect 0x101df2 2 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6] []) (.reg (.gpr 2))) #v[6]
    (.letOp (n := 59) (.exec 0x101df2 (LoadPre 0x101df2 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x101df2 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x101df2 2 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 60) (.out 0x101df5 (atFlags StatusFlags.CF (adcR64R64Effect 0x101df5 1 10)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[56, 10, 54]
    (.letOp (n := 61) (.exec 0x101df5 (fun s => s.RIP = 0x101df5) (atFlags StatusFlags.CF (adcR64R64Effect 0x101df5 1 10)) (Reg.operands [.gpr 1, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[56, 10, 54]
    (.letOp (n := 62) (.out 0x101df8 (movR32R32Effect 0x101df8 3 10 1) (EffectPart.reads (.reg (.gpr 10)) [.gpr 1] []) (.reg (.gpr 10))) #v[60]
    (.letOp (n := 63) (.exec 0x101df8 (fun s => s.RIP = 0x101df8) (movR32R32Effect 0x101df8 3 10 1) (Reg.operands [.gpr 1] [])) #v[60]
    (.letOp (n := 64) (.out 0x101dfb (addR64R64Effect 0x101dfb 2 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 9] []) (.reg (.gpr 2))) #v[58, 9]
    (.letOp (n := 65) (.exec 0x101dfb (fun s => s.RIP = 0x101dfb) (addR64R64Effect 0x101dfb 2 9) (Reg.operands [.gpr 2, .gpr 9] [])) #v[58, 9]
    (.letOp (n := 66) (.out 0x101dfe (shrR64Effect 0x101dfe 4 1 32) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[60]
    (.letOp (n := 67) (.exec 0x101dfe (fun s => s.RIP = 0x101dfe) (shrR64Effect 0x101dfe 4 1 32) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[60]
    (.letOp (n := 68) (.out 0x101e02 (addR64R64Effect 0x101e02 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[66, 64]
    (.letOp (n := 69) (.exec 0x101e02 (fun s => s.RIP = 0x101e02) (addR64R64Effect 0x101e02 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[66, 64]
    (.letOp (n := 70) (.out 0x101e05 (addR32M32Effect 0x101e05 3 7 (.base 6 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[7, 6]
    (.letOp (n := 71) (.exec 0x101e05 (LoadPre 0x101e05 (fun s => AddrMode.addr (.base 6 (.d8 0xc)) s (0x101e05 + BitVec.ofNat 64 3)) 4) (addR32M32Effect 0x101e05 3 7 (.base 6 (.d8 0xc))) (Reg.operands [.gpr 7, .gpr 6] [])) #v[7, 6]
    (.letOp (n := 72) (.out 0x101e08 (movR32R32Effect 0x101e08 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[68]
    (.letOp (n := 73) (.exec 0x101e08 (fun s => s.RIP = 0x101e08) (movR32R32Effect 0x101e08 2 2 1) (Reg.operands [.gpr 1] [])) #v[68]
    (.letOp (n := 74) (.out 0x101e0a (shrR64Effect 0x101e0a 4 1 32) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[68]
    (.letOp (n := 75) (.exec 0x101e0a (fun s => s.RIP = 0x101e0a) (shrR64Effect 0x101e0a 4 1 32) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[68]
    (.letOp (n := 76) (.out 0x101e0e (addR32R32Effect 0x101e0e 2 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[74, 70]
    (.letOp (n := 77) (.exec 0x101e0e (fun s => s.RIP = 0x101e0e) (addR32R32Effect 0x101e0e 2 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[74, 70]
    (.letOp (n := 78) (.exec 0x101e10 (StorePre 0x101e10 3 (fun s => AddrMode.addr (.base 0 .none) s (0x101e10 + BitVec.ofNat 64 3)) 4) (movM32R32Effect 0x101e10 8 (.base 0 .none)) (Reg.operands [.gpr 8, .gpr 0] [])) #v[53, 0]
    (.letOp (n := 79) (.exec 0x101e13 (StorePre 0x101e13 4 (fun s => AddrMode.addr (.base 0 (.d8 0x4)) s (0x101e13 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x101e13 10 (.base 0 (.d8 0x4))) (Reg.operands [.gpr 10, .gpr 0] [])) #v[62, 0]
    (.letOp (n := 80) (.exec 0x101e17 (StorePre 0x101e17 3 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x101e17 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x101e17 2 (.base 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 0] [])) #v[72, 0]
    (.letOp (n := 81) (.exec 0x101e1a (StorePre 0x101e1a 3 (fun s => AddrMode.addr (.base 0 (.d8 0xc)) s (0x101e1a + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x101e1a 1 (.base 0 (.d8 0xc))) (Reg.operands [.gpr 1, .gpr 0] [])) #v[76, 0]
    (.letOp (n := 82) (.out 0x101e1d (popR64Effect 0x101e1d 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 83) (.out 0x101e1d (popR64Effect 0x101e1d 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 84) (.exec 0x101e1d (PopPre 0x101e1d) (popR64Effect 0x101e1d 1 3) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 85) (.out 0x101e1e (popR64Effect 0x101e1e 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[83]
    (.letOp (n := 86) (.out 0x101e1e (popR64Effect 0x101e1e 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[83]
    (.letOp (n := 87) (.exec 0x101e1e (PopPre 0x101e1e) (popR64Effect 0x101e1e 2 12) (Reg.operands [.gpr 4] [])) #v[83]
    (.letOp (n := 88) (.out 0x101e20 (popR64Effect 0x101e20 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[86]
    (.letOp (n := 89) (.out 0x101e20 (popR64Effect 0x101e20 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[86]
    (.letOp (n := 90) (.exec 0x101e20 (PopPre 0x101e20) (popR64Effect 0x101e20 2 13) (Reg.operands [.gpr 4] [])) #v[86]
    (.letOp (n := 91) (.out 0x101e22 (popR64Effect 0x101e22 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[89]
    (.letOp (n := 92) (.out 0x101e22 (popR64Effect 0x101e22 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[89]
    (.letOp (n := 93) (.exec 0x101e22 (PopPre 0x101e22) (popR64Effect 0x101e22 2 14) (Reg.operands [.gpr 4] [])) #v[89]
    (.terminate (.br ⟨.l101e24, RegMap.args [(0, 0), (1, 76), (2, 72), (3, 82), (4, 92), (6, 6), (7, 70), (8, 53), (9, 9), (10, 62), (12, 85), (13, 88), (14, 91), (22, 22), (39, 39), (50, 50), (51, 51)] 94⟩))))))))))))))))))))))))))))))))))))))))))

def bytes_l101dec : List UInt8 :=
  [0x44, 0x03, 0x06, 0x8B, 0x4E, 0x04, 0x8B, 0x56, 0x08, 0x4C, 0x11, 0xD1, 0x41, 0x89, 0xCA, 0x4C,
    0x01, 0xCA, 0x48, 0xC1, 0xE9, 0x20, 0x48, 0x01, 0xD1, 0x03, 0x7E, 0x0C, 0x89, 0xCA, 0x48, 0xC1,
    0xE9, 0x20, 0x01, 0xF9, 0x44, 0x89, 0x00, 0x44, 0x89, 0x50, 0x04, 0x89, 0x50, 0x08, 0x89, 0x48,
    0x0C, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E]

theorem code_l101dec : ∀ x ∈ codeRange 0x101dec bytes_l101dec, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1dec 56 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101e24 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101e24 (popR64Effect 0x101e24 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 54) (.out 0x101e24 (popR64Effect 0x101e24 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 55) (.exec 0x101e24 (PopPre 0x101e24) (popR64Effect 0x101e24 2 15) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x101e26 (popR64Effect 0x101e26 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[54]
    (.letOp (n := 57) (.out 0x101e26 (popR64Effect 0x101e26 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[54]
    (.letOp (n := 58) (.exec 0x101e26 (PopPre 0x101e26) (popR64Effect 0x101e26 1 5) (Reg.operands [.gpr 4] [])) #v[54]
    (.letOp (n := 59) (.out 0x101e27 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[57]
    (.letOp (n := 60) (.out 0x101e27 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[57]
    (.letOp (n := 61) (.exec 0x101e27 (RetPre 0x101e27) (retEffect) (Reg.operands [.gpr 4] [])) #v[57]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 60), (5, 56), (6, 6), (7, 7), (9, 9), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 62) (some ⟨59, by decide⟩)))))))))))

def bytes_l101e24 : List UInt8 :=
  [0x41, 0x5F, 0x5D, 0xC3]

theorem code_l101e24 : ∀ x ∈ codeRange 0x101e24 bytes_l101e24, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1e24 4 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101e30 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101e30 (xorR32R32Effect 0x101e30 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[2, 2]
    (.letOp (n := 54) (.exec 0x101e30 (fun s => s.RIP = 0x101e30) (xorR32R32Effect 0x101e30 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.terminate (.br ⟨.l101ab0, RegMap.args [(2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l101e30 : List UInt8 :=
  [0x31, 0xD2, 0xE9, 0x79, 0xFC, 0xFF, 0xFF]

theorem code_l101e30 : ∀ x ∈ codeRange 0x101e30 bytes_l101e30, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1e30 7 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101e40_1 : Block Op Label signature Reg.count 90 :=
  .letOp (n := 90) (.exec 0x101e9f (StorePre 0x101e9f 3 (fun s => AddrMode.addr (.base 0 .none) s (0x101e9f + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x101e9f 10 (.base 0 .none)) (Reg.operands [.gpr 10, .gpr 0] [])) #v[86, 53]
    (.letOp (n := 91) (.exec 0x101ea2 (StorePre 0x101ea2 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x101ea2 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x101ea2 6 (.base 0 (.d8 0x8))) (Reg.operands [.gpr 6, .gpr 0] [])) #v[88, 53]
    (.letOp (n := 92) (.exec 0x101ea6 (StorePre 0x101ea6 3 (fun s => AddrMode.addr (.base 0 (.d8 0x10)) s (0x101ea6 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x101ea6 1 (.base 0 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 0] [])) #v[60, 53]
    (.letOp (n := 93) (.exec 0x101ea9 (StorePre 0x101ea9 3 (fun s => AddrMode.addr (.base 0 (.d8 0x14)) s (0x101ea9 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x101ea9 2 (.base 0 (.d8 0x14))) (Reg.operands [.gpr 2, .gpr 0] [])) #v[68, 53]
    (.letOp (n := 94) (.exec 0x101eac (StorePre 0x101eac 3 (fun s => AddrMode.addr (.base 0 (.d8 0x18)) s (0x101eac + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x101eac 7 (.base 0 (.d8 0x18))) (Reg.operands [.gpr 7, .gpr 0] [])) #v[72, 53]
    (.letOp (n := 95) (.exec 0x101eaf (StorePre 0x101eaf 4 (fun s => AddrMode.addr (.base 0 (.d8 0x1c)) s (0x101eaf + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x101eaf 8 (.base 0 (.d8 0x1c))) (Reg.operands [.gpr 8, .gpr 0] [])) #v[78, 53]
    (.letOp (n := 96) (.exec 0x101eb3 (StorePre 0x101eb3 4 (fun s => AddrMode.addr (.base 0 (.d8 0x20)) s (0x101eb3 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x101eb3 9 (.base 0 (.d8 0x20))) (Reg.operands [.gpr 9, .gpr 0] [])) #v[84, 53]
    (.letOp (n := 97) (.out 0x101eb7 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[4]
    (.letOp (n := 98) (.out 0x101eb7 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 99) (.exec 0x101eb7 (RetPre 0x101eb7) (retEffect) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.ret (RegMap.args [(0, 53), (1, 60), (2, 68), (3, 3), (4, 98), (5, 5), (6, 88), (7, 72), (8, 78), (9, 84), (10, 86), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 100) (some ⟨97, by decide⟩))))))))))))

def bytes_l101e40_1 : List UInt8 :=
  [0x4C, 0x89, 0x10, 0x48, 0x89, 0x70, 0x08, 0x89, 0x48, 0x10, 0x89, 0x50, 0x14, 0x89, 0x78, 0x18,
    0x44, 0x89, 0x40, 0x1C, 0x44, 0x89, 0x48, 0x20, 0xC3]

theorem code_l101e40_1 : ∀ x ∈ codeRange 0x101e9f bytes_l101e40_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1e9f 25 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101e40 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101e40 (movR64R64Effect 0x101e40 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 54) (.exec 0x101e40 (fun s => s.RIP = 0x101e40) (movR64R64Effect 0x101e40 0 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 55) (.exec 0x101e43 (StorePre 0x101e43 7 (fun s => AddrMode.addr (.base 7 (.d8 0x34)) s (0x101e43 + BitVec.ofNat 64 7)) 4) (movM32Imm32Effect 0x101e43 7 (.base 7 (.d8 0x34)) 0x0) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 56) (.exec 0x101e4a (StorePre 0x101e4a 8 (fun s => AddrMode.addr (.base 7 (.d8 0x2c)) s (0x101e4a + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x101e4a (.base 7 (.d8 0x2c)) 0x0) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 57) (.exec 0x101e52 (StorePre 0x101e52 8 (fun s => AddrMode.addr (.base 7 (.d8 0x24)) s (0x101e52 + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x101e52 (.base 7 (.d8 0x24)) 0x0) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 58) (.out 0x101e5a (movR32Imm32Effect 0x101e5a 5 1 0x3ffffff) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 59) (.exec 0x101e5a (fun s => s.RIP = 0x101e5a) (movR32Imm32Effect 0x101e5a 5 1 0x3ffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 60) (.out 0x101e5f (andR32M32Effect 0x101e5f 2 1 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[58, 6]
    (.letOp (n := 61) (.exec 0x101e5f (LoadPre 0x101e5f (fun s => AddrMode.addr (.base 6 .none) s (0x101e5f + BitVec.ofNat 64 2)) 4) (andR32M32Effect 0x101e5f 2 1 (.base 6 .none)) (Reg.operands [.gpr 1, .gpr 6] [])) #v[58, 6]
    (.letOp (n := 62) (.out 0x101e61 (movR32M32LowEffect 0x101e61 2 (.base 6 (.d8 0x3))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6] []) (.reg (.gpr 2))) #v[6]
    (.letOp (n := 63) (.exec 0x101e61 (LoadPre 0x101e61 (fun s => AddrMode.addr (.base 6 (.d8 0x3)) s (0x101e61 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x101e61 2 (.base 6 (.d8 0x3))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 64) (.out 0x101e64 (movR32M32LowEffect 0x101e64 7 (.base 6 (.d8 0x6))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[6]
    (.letOp (n := 65) (.exec 0x101e64 (LoadPre 0x101e64 (fun s => AddrMode.addr (.base 6 (.d8 0x6)) s (0x101e64 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x101e64 7 (.base 6 (.d8 0x6))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 66) (.out 0x101e67 (shrR32Effect 0x101e67 3 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[62]
    (.letOp (n := 67) (.exec 0x101e67 (fun s => s.RIP = 0x101e67) (shrR32Effect 0x101e67 3 2 2) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[62]
    (.letOp (n := 68) (.out 0x101e6a (andR32Imm32Effect 0x101e6a 6 2 0x3ffff03) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[66]
    (.letOp (n := 69) (.exec 0x101e6a (fun s => s.RIP = 0x101e6a) (andR32Imm32Effect 0x101e6a 6 2 0x3ffff03) (Reg.operands [.gpr 2] [])) #v[66]
    (.letOp (n := 70) (.out 0x101e70 (shrR32Effect 0x101e70 3 7 4) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[64]
    (.letOp (n := 71) (.exec 0x101e70 (fun s => s.RIP = 0x101e70) (shrR32Effect 0x101e70 3 7 4) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[64]
    (.letOp (n := 72) (.out 0x101e73 (andR32Imm32Effect 0x101e73 6 7 0x3ffc0ff) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[70]
    (.letOp (n := 73) (.exec 0x101e73 (fun s => s.RIP = 0x101e73) (andR32Imm32Effect 0x101e73 6 7 0x3ffc0ff) (Reg.operands [.gpr 7] [])) #v[70]
    (.letOp (n := 74) (.out 0x101e79 (movR32M32Effect 0x101e79 8 (.base 6 (.d8 0x9))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 6] []) (.reg (.gpr 8))) #v[6]
    (.letOp (n := 75) (.exec 0x101e79 (LoadPre 0x101e79 (fun s => AddrMode.addr (.base 6 (.d8 0x9)) s (0x101e79 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x101e79 8 (.base 6 (.d8 0x9))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 76) (.out 0x101e7d (shrR32Effect 0x101e7d 4 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[74]
    (.letOp (n := 77) (.exec 0x101e7d (fun s => s.RIP = 0x101e7d) (shrR32Effect 0x101e7d 4 8 6) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[74]
    (.letOp (n := 78) (.out 0x101e81 (andR32Imm32Effect 0x101e81 7 8 0x3f03fff) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[76]
    (.letOp (n := 79) (.exec 0x101e81 (fun s => s.RIP = 0x101e81) (andR32Imm32Effect 0x101e81 7 8 0x3f03fff) (Reg.operands [.gpr 8] [])) #v[76]
    (.letOp (n := 80) (.out 0x101e88 (movR32M32Effect 0x101e88 9 (.base 6 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 6] []) (.reg (.gpr 9))) #v[6]
    (.letOp (n := 81) (.exec 0x101e88 (LoadPre 0x101e88 (fun s => AddrMode.addr (.base 6 (.d8 0xc)) s (0x101e88 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x101e88 9 (.base 6 (.d8 0xc))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 82) (.out 0x101e8c (shrR32Effect 0x101e8c 4 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[80]
    (.letOp (n := 83) (.exec 0x101e8c (fun s => s.RIP = 0x101e8c) (shrR32Effect 0x101e8c 4 9 8) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[80]
    (.letOp (n := 84) (.out 0x101e90 (andR32Imm32Effect 0x101e90 7 9 0xfffff) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[82]
    (.letOp (n := 85) (.exec 0x101e90 (fun s => s.RIP = 0x101e90) (andR32Imm32Effect 0x101e90 7 9 0xfffff) (Reg.operands [.gpr 9] [])) #v[82]
    (.letOp (n := 86) (.out 0x101e97 (movR64M64Effect 0x101e97 10 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 6] []) (.reg (.gpr 10))) #v[6]
    (.letOp (n := 87) (.exec 0x101e97 (LoadPre 0x101e97 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x101e97 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x101e97 10 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 88) (.out 0x101e9b (movR64M64Effect 0x101e9b 6 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[6]
    (.letOp (n := 89) (.exec 0x101e9b (LoadPre 0x101e9b (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x101e9b + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x101e9b 6 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 6] [])) #v[6]
    (b_l101e40_1)))))))))))))))))))))))))))))))))))))

def bytes_l101e40 : List UInt8 :=
  [0x48, 0x89, 0xF8, 0xC7, 0x47, 0x34, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x47, 0x2C, 0x00, 0x00,
    0x00, 0x00, 0x48, 0xC7, 0x47, 0x24, 0x00, 0x00, 0x00, 0x00, 0xB9, 0xFF, 0xFF, 0xFF, 0x03, 0x23,
    0x0E, 0x8B, 0x56, 0x03, 0x8B, 0x7E, 0x06, 0xC1, 0xEA, 0x02, 0x81, 0xE2, 0x03, 0xFF, 0xFF, 0x03,
    0xC1, 0xEF, 0x04, 0x81, 0xE7, 0xFF, 0xC0, 0xFF, 0x03, 0x44, 0x8B, 0x46, 0x09, 0x41, 0xC1, 0xE8,
    0x06, 0x41, 0x81, 0xE0, 0xFF, 0x3F, 0xF0, 0x03, 0x44, 0x8B, 0x4E, 0x0C, 0x41, 0xC1, 0xE9, 0x08,
    0x41, 0x81, 0xE1, 0xFF, 0xFF, 0x0F, 0x00, 0x4C, 0x8B, 0x56, 0x10, 0x48, 0x8B, 0x76, 0x18] ++ bytes_l101e40_1

theorem code_l101e40 : ∀ x ∈ codeRange 0x101e40 bytes_l101e40, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1e40 95 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l101e40_1

@[cfg_block] def b_l102020 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x102020 (cmpR64M64Effect 0x102020 6 (.base 7 (.d8 0x10))) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 7] []) (.flag .CF)) #v[6, 7]
    (.letOp (n := 54) (.out 0x102020 (cmpR64M64Effect 0x102020 6 (.base 7 (.d8 0x10))) (EffectPart.reads (.flag .ZF) [.gpr 6, .gpr 7] []) (.flag .ZF)) #v[6, 7]
    (.letOp (n := 55) (.exec 0x102020 (LoadPre 0x102020 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x102020 + BitVec.ofNat 64 4)) 8) (cmpR64M64Effect 0x102020 6 (.base 7 (.d8 0x10))) (Reg.operands [.gpr 6, .gpr 7] [])) #v[6, 7]
    (.letOp (n := 56) (.pure (condOp 7)) #v[53, 54]
    (.terminate (.condBr (Fin.last 56) ⟨.l10202a, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩ ⟨.l102026, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l102020 : List UInt8 :=
  [0x48, 0x3B, 0x77, 0x10, 0x77, 0x04]

theorem code_l102020 : ∀ x ∈ codeRange 0x102020 bytes_l102020, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2020 6 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l102026 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x102026 (StorePre 0x102026 4 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x102026 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x102026 6 (.base 7 (.d8 0x10))) (Reg.operands [.gpr 6, .gpr 7] [])) #v[6, 7]
    (.terminate (.br ⟨.l10202a, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 54⟩))

def bytes_l102026 : List UInt8 :=
  [0x48, 0x89, 0x77, 0x10]

theorem code_l102026 : ∀ x ∈ codeRange 0x102026 bytes_l102026, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2026 4 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10202a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10202a (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[4]
    (.letOp (n := 54) (.out 0x10202a (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 55) (.exec 0x10202a (RetPre 0x10202a) (retEffect) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 54), (5, 5), (6, 6), (7, 7), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 56) (some ⟨53, by decide⟩)))))

def bytes_l10202a : List UInt8 :=
  [0xC3]

theorem code_l10202a : ∀ x ∈ codeRange 0x10202a bytes_l10202a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x202a 1 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l102d70_1 : Block Op Label signature Reg.count 94 :=
  .letOp (n := 94) (.out 0x102db4 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[4]
    (.letOp (n := 95) (.out 0x102db4 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 96) (.exec 0x102db4 (RetPre 0x102db4) (retEffect) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.ret (RegMap.args [(0, 92), (1, 90), (2, 55), (3, 3), (4, 95), (5, 5), (6, 77), (7, 89), (8, 79), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 97) (some ⟨94, by decide⟩)))))

def bytes_l102d70_1 : List UInt8 :=
  [0xC3]

theorem code_l102d70_1 : ∀ x ∈ codeRange 0x102db4 bytes_l102d70_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2db4 1 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l102d70 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x102d70 (movR64R64Effect 0x102d70 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[2]
    (.letOp (n := 54) (.exec 0x102d70 (fun s => s.RIP = 0x102d70) (movR64R64Effect 0x102d70 8 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 55) (.out 0x102d73 (movR64R64Effect 0x102d73 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7] []) (.reg (.gpr 2))) #v[7]
    (.letOp (n := 56) (.exec 0x102d73 (fun s => s.RIP = 0x102d73) (movR64R64Effect 0x102d73 2 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 57) (.out 0x102d76 (movzxR32R8Effect 0x102d76 4 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[6]
    (.letOp (n := 58) (.exec 0x102d76 (fun s => s.RIP = 0x102d76) (movzxR32R8Effect 0x102d76 4 1 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 59) (.out 0x102d7a (movR64Imm64Effect 0x102d7a 0 0x101010101010101) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 60) (.exec 0x102d7a (fun s => s.RIP = 0x102d7a) (movR64Imm64Effect 0x102d7a 0 0x101010101010101) (Reg.operands [] [])) #v[]
    (.letOp (n := 61) (.out 0x102d84 (imulR64R64Effect 0x102d84 4 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[59, 57]
    (.letOp (n := 62) (.exec 0x102d84 (fun s => s.RIP = 0x102d84) (imulR64R64Effect 0x102d84 4 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[59, 57]
    (.letOp (n := 63) (.out 0x102d88 (movR32R32Effect 0x102d88 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[55]
    (.letOp (n := 64) (.exec 0x102d88 (fun s => s.RIP = 0x102d88) (movR32R32Effect 0x102d88 2 1 2) (Reg.operands [.gpr 2] [])) #v[55]
    (.letOp (n := 65) (.out 0x102d8a (negR32Effect 0x102d8a 2 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[63]
    (.letOp (n := 66) (.exec 0x102d8a (fun s => s.RIP = 0x102d8a) (negR32Effect 0x102d8a 2 1) (Reg.operands [.gpr 1] [])) #v[63]
    (.letOp (n := 67) (.out 0x102d8c (andR32Imm8Effect 0x102d8c 3 1 0x7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 68) (.exec 0x102d8c (fun s => s.RIP = 0x102d8c) (andR32Imm8Effect 0x102d8c 3 1 0x7) (Reg.operands [.gpr 1] [])) #v[65]
    (.letOp (n := 69) (.out 0x102d8f (cmpR64R64Effect 0x102d8f 8 1) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 1] []) (.flag .CF)) #v[53, 67]
    (.letOp (n := 70) (.exec 0x102d8f (fun s => s.RIP = 0x102d8f) (cmpR64R64Effect 0x102d8f 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[53, 67]
    (.letOp (n := 71) (.out 0x102d92 (atFlags (condHolds 2) (cmovR64R64Effect 0x102d92 4 1 8)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[67, 53, 69]
    (.letOp (n := 72) (.exec 0x102d92 (fun s => s.RIP = 0x102d92) (atFlags (condHolds 2) (cmovR64R64Effect 0x102d92 4 1 8)) (Reg.operands [.gpr 1, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[67, 53, 69]
    (.letOp (n := 73) (.out 0x102d96 (subR64R64Effect 0x102d96 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[53, 71]
    (.letOp (n := 74) (.exec 0x102d96 (fun s => s.RIP = 0x102d96) (subR64R64Effect 0x102d96 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[53, 71]
    (.letOp (n := 75) (.out 0x102d99 (movR64R64Effect 0x102d99 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 8] []) (.reg (.gpr 6))) #v[73]
    (.letOp (n := 76) (.exec 0x102d99 (fun s => s.RIP = 0x102d99) (movR64R64Effect 0x102d99 6 8) (Reg.operands [.gpr 8] [])) #v[73]
    (.letOp (n := 77) (.out 0x102d9c (shrR64Effect 0x102d9c 4 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[75]
    (.letOp (n := 78) (.exec 0x102d9c (fun s => s.RIP = 0x102d9c) (shrR64Effect 0x102d9c 4 6 3) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[75]
    (.letOp (n := 79) (.out 0x102da0 (andR32Imm8Effect 0x102da0 4 8 0x7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[73]
    (.letOp (n := 80) (.exec 0x102da0 (fun s => s.RIP = 0x102da0) (andR32Imm8Effect 0x102da0 4 8 0x7) (Reg.operands [.gpr 8] [])) #v[73]
    (.letOp (n := 81) (.out 0x102da4 (repStosbEffect 0x102da4) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 7))) #v[61, 7, 71, 22]
    (.letOp (n := 82) (.exec 0x102da4 (RepPre 0x102da4 (RepStosbPre 0x102da4)) (repStosbEffect 0x102da4) (Reg.operands [.gpr 0, .gpr 7, .gpr 1, .df] [])) #v[61, 7, 71, 22]
    (.letOp (n := 83) (.out 0x102da6 (movR64R64Effect 0x102da6 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[77]
    (.letOp (n := 84) (.exec 0x102da6 (fun s => s.RIP = 0x102da6) (movR64R64Effect 0x102da6 1 6) (Reg.operands [.gpr 6] [])) #v[77]
    (.letOp (n := 85) (.out 0x102da9 (repStosqEffect 0x102da9) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 7))) #v[61, 81, 83, 22]
    (.letOp (n := 86) (.exec 0x102da9 (RepPre 0x102da9 (RepStosqPre 0x102da9)) (repStosqEffect 0x102da9) (Reg.operands [.gpr 0, .gpr 7, .gpr 1, .df] [])) #v[61, 81, 83, 22]
    (.letOp (n := 87) (.out 0x102dac (movR64R64Effect 0x102dac 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 8] []) (.reg (.gpr 1))) #v[79]
    (.letOp (n := 88) (.exec 0x102dac (fun s => s.RIP = 0x102dac) (movR64R64Effect 0x102dac 1 8) (Reg.operands [.gpr 8] [])) #v[79]
    (.letOp (n := 89) (.out 0x102daf (repStosbEffect 0x102daf) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 7))) #v[61, 85, 87, 22]
    (.letOp (n := 90) (.out 0x102daf (repStosbEffect 0x102daf) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 1))) #v[61, 85, 87, 22]
    (.letOp (n := 91) (.exec 0x102daf (RepPre 0x102daf (RepStosbPre 0x102daf)) (repStosbEffect 0x102daf) (Reg.operands [.gpr 0, .gpr 7, .gpr 1, .df] [])) #v[61, 85, 87, 22]
    (.letOp (n := 92) (.out 0x102db1 (movR64R64Effect 0x102db1 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[55]
    (.letOp (n := 93) (.exec 0x102db1 (fun s => s.RIP = 0x102db1) (movR64R64Effect 0x102db1 0 2) (Reg.operands [.gpr 2] [])) #v[55]
    (b_l102d70_1)))))))))))))))))))))))))))))))))))))))))

def bytes_l102d70 : List UInt8 :=
  [0x49, 0x89, 0xD0, 0x48, 0x89, 0xFA, 0x40, 0x0F, 0xB6, 0xCE, 0x48, 0xB8, 0x01, 0x01, 0x01, 0x01,
    0x01, 0x01, 0x01, 0x01, 0x48, 0x0F, 0xAF, 0xC1, 0x89, 0xD1, 0xF7, 0xD9, 0x83, 0xE1, 0x07, 0x49,
    0x39, 0xC8, 0x49, 0x0F, 0x42, 0xC8, 0x49, 0x29, 0xC8, 0x4C, 0x89, 0xC6, 0x48, 0xC1, 0xEE, 0x03,
    0x41, 0x83, 0xE0, 0x07, 0xF3, 0xAA, 0x48, 0x89, 0xF1, 0xF3, 0x48, 0xAB, 0x4C, 0x89, 0xC1, 0xF3,
    0xAA, 0x48, 0x89, 0xD0] ++ bytes_l102d70_1

theorem code_l102d70 : ∀ x ∈ codeRange 0x102d70 bytes_l102d70, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x2d70 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l102d70_1

@[cfg_block] def b_l102dc0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x102dc0 (movR64R64Effect 0x102dc0 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 54) (.exec 0x102dc0 (fun s => s.RIP = 0x102dc0) (movR64R64Effect 0x102dc0 0 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 55) (.out 0x102dc3 (movR32R32Effect 0x102dc3 3 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[53]
    (.letOp (n := 56) (.exec 0x102dc3 (fun s => s.RIP = 0x102dc3) (movR32R32Effect 0x102dc3 3 8 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x102dc6 (negR32Effect 0x102dc6 3 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[55]
    (.letOp (n := 58) (.exec 0x102dc6 (fun s => s.RIP = 0x102dc6) (negR32Effect 0x102dc6 3 8) (Reg.operands [.gpr 8] [])) #v[55]
    (.letOp (n := 59) (.out 0x102dc9 (andR32Imm8Effect 0x102dc9 4 8 0x7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[57]
    (.letOp (n := 60) (.exec 0x102dc9 (fun s => s.RIP = 0x102dc9) (andR32Imm8Effect 0x102dc9 4 8 0x7) (Reg.operands [.gpr 8] [])) #v[57]
    (.letOp (n := 61) (.out 0x102dcd (cmpR64R64Effect 0x102dcd 2 8) (EffectPart.reads (.flag .CF) [.gpr 2, .gpr 8] []) (.flag .CF)) #v[2, 59]
    (.letOp (n := 62) (.exec 0x102dcd (fun s => s.RIP = 0x102dcd) (cmpR64R64Effect 0x102dcd 2 8) (Reg.operands [.gpr 2, .gpr 8] [])) #v[2, 59]
    (.letOp (n := 63) (.out 0x102dd0 (atFlags (condHolds 2) (cmovR64R64Effect 0x102dd0 4 8 2)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[59, 2, 61]
    (.letOp (n := 64) (.exec 0x102dd0 (fun s => s.RIP = 0x102dd0) (atFlags (condHolds 2) (cmovR64R64Effect 0x102dd0 4 8 2)) (Reg.operands [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[59, 2, 61]
    (.letOp (n := 65) (.out 0x102dd4 (movR64R64Effect 0x102dd4 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 8] []) (.reg (.gpr 1))) #v[63]
    (.letOp (n := 66) (.exec 0x102dd4 (fun s => s.RIP = 0x102dd4) (movR64R64Effect 0x102dd4 1 8) (Reg.operands [.gpr 8] [])) #v[63]
    (.letOp (n := 67) (.out 0x102dd7 (repMovsbEffect 0x102dd7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 6))) #v[6, 7, 65, 22]
    (.letOp (n := 68) (.out 0x102dd7 (repMovsbEffect 0x102dd7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 7))) #v[6, 7, 65, 22]
    (.letOp (n := 69) (.exec 0x102dd7 (RepPre 0x102dd7 (RepMovsbPre 0x102dd7)) (repMovsbEffect 0x102dd7) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[6, 7, 65, 22]
    (.letOp (n := 70) (.out 0x102dd9 (subR64R64Effect 0x102dd9 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 8] []) (.reg (.gpr 2))) #v[2, 63]
    (.letOp (n := 71) (.exec 0x102dd9 (fun s => s.RIP = 0x102dd9) (subR64R64Effect 0x102dd9 2 8) (Reg.operands [.gpr 2, .gpr 8] [])) #v[2, 63]
    (.letOp (n := 72) (.out 0x102ddc (movR64R64Effect 0x102ddc 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[70]
    (.letOp (n := 73) (.exec 0x102ddc (fun s => s.RIP = 0x102ddc) (movR64R64Effect 0x102ddc 1 2) (Reg.operands [.gpr 2] [])) #v[70]
    (.letOp (n := 74) (.out 0x102ddf (shrR64Effect 0x102ddf 4 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[72]
    (.letOp (n := 75) (.exec 0x102ddf (fun s => s.RIP = 0x102ddf) (shrR64Effect 0x102ddf 4 1 3) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[72]
    (.letOp (n := 76) (.out 0x102de3 (repMovsqEffect 0x102de3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 6))) #v[67, 68, 74, 22]
    (.letOp (n := 77) (.out 0x102de3 (repMovsqEffect 0x102de3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 7))) #v[67, 68, 74, 22]
    (.letOp (n := 78) (.exec 0x102de3 (RepPre 0x102de3 (RepMovsqPre 0x102de3)) (repMovsqEffect 0x102de3) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[67, 68, 74, 22]
    (.letOp (n := 79) (.out 0x102de6 (andR32Imm8Effect 0x102de6 3 2 0x7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[70]
    (.letOp (n := 80) (.exec 0x102de6 (fun s => s.RIP = 0x102de6) (andR32Imm8Effect 0x102de6 3 2 0x7) (Reg.operands [.gpr 2] [])) #v[70]
    (.letOp (n := 81) (.out 0x102de9 (movR64R64Effect 0x102de9 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[79]
    (.letOp (n := 82) (.exec 0x102de9 (fun s => s.RIP = 0x102de9) (movR64R64Effect 0x102de9 1 2) (Reg.operands [.gpr 2] [])) #v[79]
    (.letOp (n := 83) (.out 0x102dec (repMovsbEffect 0x102dec) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 6))) #v[76, 77, 81, 22]
    (.letOp (n := 84) (.out 0x102dec (repMovsbEffect 0x102dec) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 7))) #v[76, 77, 81, 22]
    (.letOp (n := 85) (.out 0x102dec (repMovsbEffect 0x102dec) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 1))) #v[76, 77, 81, 22]
    (.letOp (n := 86) (.exec 0x102dec (RepPre 0x102dec (RepMovsbPre 0x102dec)) (repMovsbEffect 0x102dec) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[76, 77, 81, 22]
    (.letOp (n := 87) (.out 0x102dee (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[4]
    (.letOp (n := 88) (.out 0x102dee (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 89) (.exec 0x102dee (RetPre 0x102dee) (retEffect) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.ret (RegMap.args [(0, 53), (1, 85), (2, 79), (3, 3), (4, 88), (5, 5), (6, 83), (7, 84), (8, 63), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 90) (some ⟨87, by decide⟩)))))))))))))))))))))))))))))))))))))))

def bytes_l102dc0 : List UInt8 :=
  [0x48, 0x89, 0xF8, 0x41, 0x89, 0xC0, 0x41, 0xF7, 0xD8, 0x41, 0x83, 0xE0, 0x07, 0x4C, 0x39, 0xC2,
    0x4C, 0x0F, 0x42, 0xC2, 0x4C, 0x89, 0xC1, 0xF3, 0xA4, 0x4C, 0x29, 0xC2, 0x48, 0x89, 0xD1, 0x48,
    0xC1, 0xE9, 0x03, 0xF3, 0x48, 0xA5, 0x83, 0xE2, 0x07, 0x48, 0x89, 0xD1, 0xF3, 0xA4, 0xC3]

theorem code_l102dc0 : ∀ x ∈ codeRange 0x102dc0 bytes_l102dc0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2dc0 47 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

end ChaCha20Poly1305.Proofs.Decrypt.Lifted
