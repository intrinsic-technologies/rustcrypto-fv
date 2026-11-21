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

@[cfg_block] def b_l11776a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11776a (movR64M64Effect 0x11776a 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x11776a (LoadPre 0x11776a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x11776a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11776a 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x11776f (StorePre 0x11776f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11776f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11776f 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x117774 (movR64M64Effect 0x117774 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x117774 (LoadPre 0x117774 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x117774 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117774 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x117779 (StorePre 0x117779 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x117779 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117779 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x11777e (movR64M64Effect 0x11777e 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x11777e (LoadPre 0x11777e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11777e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11777e 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x117783 (StorePre 0x117783 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x117783 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117783 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x117788 (movR64M64Effect 0x117788 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x117788 (LoadPre 0x117788 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x117788 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117788 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x11778d (movR64M64Effect 0x11778d 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x11778d (LoadPre 0x11778d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11778d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11778d 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x117792 (StorePre 0x117792 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x117792 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117792 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x117797 (StorePre 0x117797 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x117797 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x117797 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x11779b (movR64R64Effect 0x11779b 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x11779b (fun s => s.RIP = 0x11779b) (movR64R64Effect 0x11779b 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x11779e (movR64R64Effect 0x11779e 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x11779e (fun s => s.RIP = 0x11779e) (movR64R64Effect 0x11779e 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x1177a1 (callEffect (fun _ => 0x1145f0) 0x1177a6) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x1177a1 (PushPre 0x1177a1 5) (callEffect (fun _ => 0x1145f0) 0x1177a6) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x1177a6⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l1177a6, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l11776a : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x4A, 0xCE, 0xFF, 0xFF]

theorem code_l11776a : ∀ x ∈ codeRange 0x11776a bytes_l11776a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1776a 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1177a6 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1177a6 (movR64M64Effect 0x1177a6 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1177a6 (LoadPre 0x1177a6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1177a6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1177a6 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x1177ab (StorePre 0x1177ab 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1177ab + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1177ab 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x1177b0 (movR64M64Effect 0x1177b0 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x1177b0 (LoadPre 0x1177b0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1177b0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1177b0 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x1177b5 (StorePre 0x1177b5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1177b5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1177b5 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x1177ba (movR64M64Effect 0x1177ba 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x1177ba (LoadPre 0x1177ba (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1177ba + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1177ba 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x1177bf (StorePre 0x1177bf 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1177bf + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1177bf 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x1177c4 (movR64M64Effect 0x1177c4 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x1177c4 (LoadPre 0x1177c4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1177c4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1177c4 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x1177c9 (movR64M64Effect 0x1177c9 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x1177c9 (LoadPre 0x1177c9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1177c9 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1177c9 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x1177ce (StorePre 0x1177ce 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1177ce + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1177ce 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x1177d3 (StorePre 0x1177d3 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1177d3 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1177d3 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x1177d7 (movR64R64Effect 0x1177d7 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x1177d7 (fun s => s.RIP = 0x1177d7) (movR64R64Effect 0x1177d7 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x1177da (movR64R64Effect 0x1177da 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x1177da (fun s => s.RIP = 0x1177da) (movR64R64Effect 0x1177da 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x1177dd (callEffect (fun _ => 0x1145f0) 0x1177e2) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x1177dd (PushPre 0x1177dd 5) (callEffect (fun _ => 0x1145f0) 0x1177e2) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x1177e2⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l1177e2, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l1177a6 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x0E, 0xCE, 0xFF, 0xFF]

theorem code_l1177a6 : ∀ x ∈ codeRange 0x1177a6 bytes_l1177a6, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x177a6 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1177e2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1177e2 (movR64M64Effect 0x1177e2 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1177e2 (LoadPre 0x1177e2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1177e2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1177e2 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x1177e7 (StorePre 0x1177e7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1177e7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1177e7 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x1177ec (movR64M64Effect 0x1177ec 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x1177ec (LoadPre 0x1177ec (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1177ec + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1177ec 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x1177f1 (StorePre 0x1177f1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1177f1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1177f1 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x1177f6 (movR64M64Effect 0x1177f6 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x1177f6 (LoadPre 0x1177f6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1177f6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1177f6 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x1177fb (StorePre 0x1177fb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1177fb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1177fb 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x117800 (movR64M64Effect 0x117800 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x117800 (LoadPre 0x117800 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x117800 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117800 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x117805 (movR64M64Effect 0x117805 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x117805 (LoadPre 0x117805 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x117805 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117805 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x11780a (StorePre 0x11780a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11780a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11780a 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x11780f (StorePre 0x11780f 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x11780f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11780f 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x117813 (movR64R64Effect 0x117813 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x117813 (fun s => s.RIP = 0x117813) (movR64R64Effect 0x117813 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x117816 (movR64R64Effect 0x117816 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x117816 (fun s => s.RIP = 0x117816) (movR64R64Effect 0x117816 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x117819 (callEffect (fun _ => 0x1145f0) 0x11781e) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x117819 (PushPre 0x117819 5) (callEffect (fun _ => 0x1145f0) 0x11781e) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x11781e⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l11781e, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l1177e2 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0xD2, 0xCD, 0xFF, 0xFF]

theorem code_l1177e2 : ∀ x ∈ codeRange 0x1177e2 bytes_l1177e2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x177e2 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11781e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11781e (movR64M64Effect 0x11781e 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x11781e (LoadPre 0x11781e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x11781e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11781e 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x117823 (StorePre 0x117823 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x117823 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117823 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x117828 (movR64M64Effect 0x117828 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x117828 (LoadPre 0x117828 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x117828 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117828 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x11782d (StorePre 0x11782d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11782d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11782d 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x117832 (movR64M64Effect 0x117832 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x117832 (LoadPre 0x117832 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x117832 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117832 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x117837 (StorePre 0x117837 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x117837 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117837 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x11783c (movR64M64Effect 0x11783c 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x11783c (LoadPre 0x11783c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11783c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11783c 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x117841 (movR64M64Effect 0x117841 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x117841 (LoadPre 0x117841 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x117841 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117841 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x117846 (StorePre 0x117846 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x117846 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117846 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x11784b (StorePre 0x11784b 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x11784b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11784b 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x11784f (movR64R64Effect 0x11784f 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x11784f (fun s => s.RIP = 0x11784f) (movR64R64Effect 0x11784f 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x117852 (movR64R64Effect 0x117852 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x117852 (fun s => s.RIP = 0x117852) (movR64R64Effect 0x117852 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x117855 (callEffect (fun _ => 0x1145f0) 0x11785a) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x117855 (PushPre 0x117855 5) (callEffect (fun _ => 0x1145f0) 0x11785a) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x11785a⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l11785a, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l11781e : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x96, 0xCD, 0xFF, 0xFF]

theorem code_l11781e : ∀ x ∈ codeRange 0x11781e bytes_l11781e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1781e 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11785a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11785a (movR64M64Effect 0x11785a 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x11785a (LoadPre 0x11785a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x11785a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11785a 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x11785f (StorePre 0x11785f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11785f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11785f 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x117864 (movR64M64Effect 0x117864 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x117864 (LoadPre 0x117864 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x117864 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117864 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x117869 (StorePre 0x117869 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x117869 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117869 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x11786e (movR64M64Effect 0x11786e 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x11786e (LoadPre 0x11786e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11786e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11786e 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x117873 (StorePre 0x117873 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x117873 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117873 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x117878 (movR64M64Effect 0x117878 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x117878 (LoadPre 0x117878 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x117878 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117878 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x11787d (movR64M64Effect 0x11787d 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x11787d (LoadPre 0x11787d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11787d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11787d 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x117882 (StorePre 0x117882 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x117882 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117882 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x117887 (StorePre 0x117887 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x117887 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x117887 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x11788b (movR64R64Effect 0x11788b 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x11788b (fun s => s.RIP = 0x11788b) (movR64R64Effect 0x11788b 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x11788e (movR64R64Effect 0x11788e 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x11788e (fun s => s.RIP = 0x11788e) (movR64R64Effect 0x11788e 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x117891 (callEffect (fun _ => 0x1145f0) 0x117896) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x117891 (PushPre 0x117891 5) (callEffect (fun _ => 0x1145f0) 0x117896) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x117896⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l117896, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l11785a : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x5A, 0xCD, 0xFF, 0xFF]

theorem code_l11785a : ∀ x ∈ codeRange 0x11785a bytes_l11785a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1785a 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l117896 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x117896 (movR64M64Effect 0x117896 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x117896 (LoadPre 0x117896 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x117896 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117896 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x11789b (StorePre 0x11789b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11789b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11789b 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x1178a0 (movR64M64Effect 0x1178a0 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x1178a0 (LoadPre 0x1178a0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1178a0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1178a0 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x1178a5 (StorePre 0x1178a5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1178a5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1178a5 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x1178aa (movR64M64Effect 0x1178aa 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x1178aa (LoadPre 0x1178aa (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1178aa + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1178aa 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x1178af (StorePre 0x1178af 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1178af + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1178af 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x1178b4 (movR64M64Effect 0x1178b4 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x1178b4 (LoadPre 0x1178b4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1178b4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1178b4 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x1178b9 (movR64M64Effect 0x1178b9 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x1178b9 (LoadPre 0x1178b9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1178b9 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1178b9 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x1178be (StorePre 0x1178be 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1178be + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1178be 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x1178c3 (StorePre 0x1178c3 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1178c3 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1178c3 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x1178c7 (movR64R64Effect 0x1178c7 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x1178c7 (fun s => s.RIP = 0x1178c7) (movR64R64Effect 0x1178c7 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x1178ca (movR64R64Effect 0x1178ca 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x1178ca (fun s => s.RIP = 0x1178ca) (movR64R64Effect 0x1178ca 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x1178cd (callEffect (fun _ => 0x1145f0) 0x1178d2) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x1178cd (PushPre 0x1178cd 5) (callEffect (fun _ => 0x1145f0) 0x1178d2) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x1178d2⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l1178d2, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l117896 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x1E, 0xCD, 0xFF, 0xFF]

theorem code_l117896 : ∀ x ∈ codeRange 0x117896 bytes_l117896, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x17896 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1178d2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1178d2 (movR64M64Effect 0x1178d2 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1178d2 (LoadPre 0x1178d2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1178d2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1178d2 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x1178d7 (StorePre 0x1178d7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1178d7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1178d7 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x1178dc (movR64M64Effect 0x1178dc 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x1178dc (LoadPre 0x1178dc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1178dc + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1178dc 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x1178e1 (StorePre 0x1178e1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1178e1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1178e1 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x1178e6 (movR64M64Effect 0x1178e6 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x1178e6 (LoadPre 0x1178e6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1178e6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1178e6 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x1178eb (StorePre 0x1178eb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1178eb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1178eb 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x1178f0 (movR64M64Effect 0x1178f0 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x1178f0 (LoadPre 0x1178f0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1178f0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1178f0 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x1178f5 (movR64M64Effect 0x1178f5 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x1178f5 (LoadPre 0x1178f5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1178f5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1178f5 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x1178fa (StorePre 0x1178fa 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1178fa + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1178fa 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x1178ff (StorePre 0x1178ff 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1178ff + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1178ff 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x117903 (movR64R64Effect 0x117903 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x117903 (fun s => s.RIP = 0x117903) (movR64R64Effect 0x117903 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x117906 (movR64R64Effect 0x117906 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x117906 (fun s => s.RIP = 0x117906) (movR64R64Effect 0x117906 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x117909 (callEffect (fun _ => 0x1145f0) 0x11790e) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x117909 (PushPre 0x117909 5) (callEffect (fun _ => 0x1145f0) 0x11790e) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x11790e⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l11790e, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l1178d2 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0xE2, 0xCC, 0xFF, 0xFF]

theorem code_l1178d2 : ∀ x ∈ codeRange 0x1178d2 bytes_l1178d2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x178d2 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11790e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11790e (movR64M64Effect 0x11790e 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x11790e (LoadPre 0x11790e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x11790e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11790e 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x117913 (StorePre 0x117913 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x117913 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117913 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x117918 (movR64M64Effect 0x117918 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x117918 (LoadPre 0x117918 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x117918 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117918 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x11791d (StorePre 0x11791d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11791d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11791d 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x117922 (movR64M64Effect 0x117922 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x117922 (LoadPre 0x117922 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x117922 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117922 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x117927 (StorePre 0x117927 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x117927 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117927 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x11792c (movR64M64Effect 0x11792c 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x11792c (LoadPre 0x11792c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11792c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11792c 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x117931 (movR64M64Effect 0x117931 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x117931 (LoadPre 0x117931 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x117931 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117931 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x117936 (StorePre 0x117936 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x117936 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117936 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x11793b (StorePre 0x11793b 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x11793b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11793b 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x11793f (movR64R64Effect 0x11793f 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x11793f (fun s => s.RIP = 0x11793f) (movR64R64Effect 0x11793f 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x117942 (movR64R64Effect 0x117942 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x117942 (fun s => s.RIP = 0x117942) (movR64R64Effect 0x117942 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x117945 (callEffect (fun _ => 0x1145f0) 0x11794a) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x117945 (PushPre 0x117945 5) (callEffect (fun _ => 0x1145f0) 0x11794a) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x11794a⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l11794a, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l11790e : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0xA6, 0xCC, 0xFF, 0xFF]

theorem code_l11790e : ∀ x ∈ codeRange 0x11790e bytes_l11790e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1790e 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11794a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11794a (movR64M64Effect 0x11794a 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x11794a (LoadPre 0x11794a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x11794a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11794a 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x11794f (StorePre 0x11794f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11794f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11794f 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x117954 (movR64M64Effect 0x117954 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x117954 (LoadPre 0x117954 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x117954 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117954 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x117959 (StorePre 0x117959 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x117959 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117959 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x11795e (movR64M64Effect 0x11795e 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x11795e (LoadPre 0x11795e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11795e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11795e 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x117963 (StorePre 0x117963 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x117963 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117963 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x117968 (movR64M64Effect 0x117968 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x117968 (LoadPre 0x117968 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x117968 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117968 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x11796d (movR64M64Effect 0x11796d 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x11796d (LoadPre 0x11796d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11796d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11796d 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x117972 (StorePre 0x117972 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x117972 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117972 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x117977 (StorePre 0x117977 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x117977 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x117977 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x11797b (movR64R64Effect 0x11797b 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x11797b (fun s => s.RIP = 0x11797b) (movR64R64Effect 0x11797b 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x11797e (movR64R64Effect 0x11797e 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x11797e (fun s => s.RIP = 0x11797e) (movR64R64Effect 0x11797e 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x117981 (callEffect (fun _ => 0x1145f0) 0x117986) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x117981 (PushPre 0x117981 5) (callEffect (fun _ => 0x1145f0) 0x117986) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x117986⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l117986, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l11794a : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x6A, 0xCC, 0xFF, 0xFF]

theorem code_l11794a : ∀ x ∈ codeRange 0x11794a bytes_l11794a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1794a 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l117986 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x117986 (movR64M64Effect 0x117986 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x117986 (LoadPre 0x117986 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x117986 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117986 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x11798b (StorePre 0x11798b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11798b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11798b 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x117990 (movR64M64Effect 0x117990 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x117990 (LoadPre 0x117990 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x117990 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117990 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x117995 (StorePre 0x117995 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x117995 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117995 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x11799a (movR64M64Effect 0x11799a 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x11799a (LoadPre 0x11799a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11799a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11799a 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x11799f (StorePre 0x11799f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11799f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11799f 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x1179a4 (movR64M64Effect 0x1179a4 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x1179a4 (LoadPre 0x1179a4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1179a4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1179a4 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x1179a9 (movR64M64Effect 0x1179a9 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x1179a9 (LoadPre 0x1179a9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1179a9 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1179a9 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x1179ae (StorePre 0x1179ae 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1179ae + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1179ae 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x1179b3 (StorePre 0x1179b3 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1179b3 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1179b3 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x1179b7 (movR64R64Effect 0x1179b7 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x1179b7 (fun s => s.RIP = 0x1179b7) (movR64R64Effect 0x1179b7 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x1179ba (movR64R64Effect 0x1179ba 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x1179ba (fun s => s.RIP = 0x1179ba) (movR64R64Effect 0x1179ba 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x1179bd (callEffect (fun _ => 0x1145f0) 0x1179c2) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x1179bd (PushPre 0x1179bd 5) (callEffect (fun _ => 0x1145f0) 0x1179c2) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x1179c2⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l1179c2, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l117986 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x2E, 0xCC, 0xFF, 0xFF]

theorem code_l117986 : ∀ x ∈ codeRange 0x117986 bytes_l117986, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x17986 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1179c2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1179c2 (movR64M64Effect 0x1179c2 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1179c2 (LoadPre 0x1179c2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1179c2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1179c2 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x1179c7 (StorePre 0x1179c7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1179c7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1179c7 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x1179cc (movR64M64Effect 0x1179cc 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x1179cc (LoadPre 0x1179cc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1179cc + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1179cc 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x1179d1 (StorePre 0x1179d1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1179d1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1179d1 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x1179d6 (movR64M64Effect 0x1179d6 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x1179d6 (LoadPre 0x1179d6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1179d6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1179d6 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x1179db (StorePre 0x1179db 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1179db + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1179db 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x1179e0 (movR64M64Effect 0x1179e0 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x1179e0 (LoadPre 0x1179e0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1179e0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1179e0 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x1179e5 (movR64M64Effect 0x1179e5 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x1179e5 (LoadPre 0x1179e5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1179e5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1179e5 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x1179ea (StorePre 0x1179ea 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1179ea + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1179ea 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x1179ef (StorePre 0x1179ef 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1179ef + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1179ef 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x1179f3 (movR64R64Effect 0x1179f3 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x1179f3 (fun s => s.RIP = 0x1179f3) (movR64R64Effect 0x1179f3 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x1179f6 (movR64R64Effect 0x1179f6 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x1179f6 (fun s => s.RIP = 0x1179f6) (movR64R64Effect 0x1179f6 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x1179f9 (callEffect (fun _ => 0x1145f0) 0x1179fe) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x1179f9 (PushPre 0x1179f9 5) (callEffect (fun _ => 0x1145f0) 0x1179fe) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x1179fe⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l1179fe, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l1179c2 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0xF2, 0xCB, 0xFF, 0xFF]

theorem code_l1179c2 : ∀ x ∈ codeRange 0x1179c2 bytes_l1179c2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x179c2 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1179fe : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1179fe (movR64M64Effect 0x1179fe 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1179fe (LoadPre 0x1179fe (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1179fe + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1179fe 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x117a03 (StorePre 0x117a03 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x117a03 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117a03 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x117a08 (movR64M64Effect 0x117a08 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x117a08 (LoadPre 0x117a08 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x117a08 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117a08 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x117a0d (StorePre 0x117a0d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x117a0d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117a0d 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x117a12 (movR64M64Effect 0x117a12 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x117a12 (LoadPre 0x117a12 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x117a12 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117a12 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x117a17 (StorePre 0x117a17 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x117a17 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117a17 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x117a1c (movR64M64Effect 0x117a1c 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x117a1c (LoadPre 0x117a1c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x117a1c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117a1c 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x117a21 (movR64M64Effect 0x117a21 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x117a21 (LoadPre 0x117a21 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x117a21 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117a21 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x117a26 (StorePre 0x117a26 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x117a26 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117a26 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x117a2b (StorePre 0x117a2b 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x117a2b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x117a2b 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x117a2f (movR64R64Effect 0x117a2f 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x117a2f (fun s => s.RIP = 0x117a2f) (movR64R64Effect 0x117a2f 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x117a32 (movR64R64Effect 0x117a32 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x117a32 (fun s => s.RIP = 0x117a32) (movR64R64Effect 0x117a32 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x117a35 (callEffect (fun _ => 0x1145f0) 0x117a3a) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x117a35 (PushPre 0x117a35 5) (callEffect (fun _ => 0x1145f0) 0x117a3a) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x117a3a⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l117a3a, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l1179fe : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0xB6, 0xCB, 0xFF, 0xFF]

theorem code_l1179fe : ∀ x ∈ codeRange 0x1179fe bytes_l1179fe, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x179fe 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l117a3a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x117a3a (movR64M64Effect 0x117a3a 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x117a3a (LoadPre 0x117a3a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x117a3a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117a3a 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x117a3f (StorePre 0x117a3f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x117a3f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117a3f 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x117a44 (movR64M64Effect 0x117a44 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x117a44 (LoadPre 0x117a44 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x117a44 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117a44 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x117a49 (StorePre 0x117a49 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x117a49 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117a49 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x117a4e (movR64M64Effect 0x117a4e 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x117a4e (LoadPre 0x117a4e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x117a4e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117a4e 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x117a53 (StorePre 0x117a53 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x117a53 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117a53 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x117a58 (movR64M64Effect 0x117a58 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x117a58 (LoadPre 0x117a58 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x117a58 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117a58 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x117a5d (movR64M64Effect 0x117a5d 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x117a5d (LoadPre 0x117a5d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x117a5d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117a5d 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x117a62 (StorePre 0x117a62 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x117a62 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117a62 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x117a67 (StorePre 0x117a67 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x117a67 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x117a67 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x117a6b (movR64R64Effect 0x117a6b 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x117a6b (fun s => s.RIP = 0x117a6b) (movR64R64Effect 0x117a6b 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x117a6e (movR64R64Effect 0x117a6e 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x117a6e (fun s => s.RIP = 0x117a6e) (movR64R64Effect 0x117a6e 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x117a71 (callEffect (fun _ => 0x1145f0) 0x117a76) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x117a71 (PushPre 0x117a71 5) (callEffect (fun _ => 0x1145f0) 0x117a76) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x117a76⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l117a76, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l117a3a : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x7A, 0xCB, 0xFF, 0xFF]

theorem code_l117a3a : ∀ x ∈ codeRange 0x117a3a bytes_l117a3a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x17a3a 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l117a76 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x117a76 (movR64M64Effect 0x117a76 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x117a76 (LoadPre 0x117a76 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x117a76 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117a76 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x117a7b (StorePre 0x117a7b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x117a7b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117a7b 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x117a80 (movR64M64Effect 0x117a80 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x117a80 (LoadPre 0x117a80 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x117a80 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117a80 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x117a85 (StorePre 0x117a85 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x117a85 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117a85 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x117a8a (movR64M64Effect 0x117a8a 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x117a8a (LoadPre 0x117a8a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x117a8a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117a8a 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x117a8f (StorePre 0x117a8f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x117a8f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117a8f 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x117a94 (movR64M64Effect 0x117a94 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x117a94 (LoadPre 0x117a94 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x117a94 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117a94 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x117a99 (movR64M64Effect 0x117a99 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x117a99 (LoadPre 0x117a99 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x117a99 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117a99 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x117a9e (StorePre 0x117a9e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x117a9e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117a9e 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x117aa3 (StorePre 0x117aa3 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x117aa3 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x117aa3 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x117aa7 (movR64R64Effect 0x117aa7 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x117aa7 (fun s => s.RIP = 0x117aa7) (movR64R64Effect 0x117aa7 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x117aaa (movR64R64Effect 0x117aaa 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x117aaa (fun s => s.RIP = 0x117aaa) (movR64R64Effect 0x117aaa 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x117aad (callEffect (fun _ => 0x1145f0) 0x117ab2) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x117aad (PushPre 0x117aad 5) (callEffect (fun _ => 0x1145f0) 0x117ab2) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x117ab2⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l117ab2, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l117a76 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x3E, 0xCB, 0xFF, 0xFF]

theorem code_l117a76 : ∀ x ∈ codeRange 0x117a76 bytes_l117a76, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x17a76 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l117ab2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x117ab2 (movR64M64Effect 0x117ab2 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x117ab2 (LoadPre 0x117ab2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x117ab2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117ab2 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x117ab7 (StorePre 0x117ab7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x117ab7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117ab7 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x117abc (movR64M64Effect 0x117abc 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x117abc (LoadPre 0x117abc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x117abc + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117abc 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x117ac1 (StorePre 0x117ac1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x117ac1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117ac1 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x117ac6 (movR64M64Effect 0x117ac6 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x117ac6 (LoadPre 0x117ac6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x117ac6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117ac6 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x117acb (StorePre 0x117acb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x117acb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117acb 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x117ad0 (movR64M64Effect 0x117ad0 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x117ad0 (LoadPre 0x117ad0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x117ad0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117ad0 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x117ad5 (movR64M64Effect 0x117ad5 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x117ad5 (LoadPre 0x117ad5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x117ad5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117ad5 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x117ada (StorePre 0x117ada 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x117ada + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117ada 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x117adf (StorePre 0x117adf 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x117adf + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x117adf 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x117ae3 (movR64R64Effect 0x117ae3 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x117ae3 (fun s => s.RIP = 0x117ae3) (movR64R64Effect 0x117ae3 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x117ae6 (movR64R64Effect 0x117ae6 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x117ae6 (fun s => s.RIP = 0x117ae6) (movR64R64Effect 0x117ae6 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x117ae9 (callEffect (fun _ => 0x1145f0) 0x117aee) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x117ae9 (PushPre 0x117ae9 5) (callEffect (fun _ => 0x1145f0) 0x117aee) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x117aee⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l117aee, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l117ab2 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x02, 0xCB, 0xFF, 0xFF]

theorem code_l117ab2 : ∀ x ∈ codeRange 0x117ab2 bytes_l117ab2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x17ab2 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l117aee : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x117aee (movR64M64Effect 0x117aee 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x117aee (LoadPre 0x117aee (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x117aee + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117aee 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x117af3 (StorePre 0x117af3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x117af3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117af3 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x117af8 (movR64M64Effect 0x117af8 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x117af8 (LoadPre 0x117af8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x117af8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117af8 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x117afd (StorePre 0x117afd 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x117afd + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117afd 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x117b02 (movR64M64Effect 0x117b02 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x117b02 (LoadPre 0x117b02 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x117b02 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117b02 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x117b07 (StorePre 0x117b07 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x117b07 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117b07 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x117b0c (movR64M64Effect 0x117b0c 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x117b0c (LoadPre 0x117b0c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x117b0c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117b0c 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x117b11 (movR64M64Effect 0x117b11 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x117b11 (LoadPre 0x117b11 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x117b11 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117b11 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x117b16 (StorePre 0x117b16 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x117b16 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117b16 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x117b1b (StorePre 0x117b1b 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x117b1b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x117b1b 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x117b1f (movR64R64Effect 0x117b1f 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x117b1f (fun s => s.RIP = 0x117b1f) (movR64R64Effect 0x117b1f 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x117b22 (movR64R64Effect 0x117b22 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x117b22 (fun s => s.RIP = 0x117b22) (movR64R64Effect 0x117b22 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x117b25 (callEffect (fun _ => 0x1145f0) 0x117b2a) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x117b25 (PushPre 0x117b25 5) (callEffect (fun _ => 0x1145f0) 0x117b2a) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x117b2a⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l117b2a, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l117aee : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0xC6, 0xCA, 0xFF, 0xFF]

theorem code_l117aee : ∀ x ∈ codeRange 0x117aee bytes_l117aee, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x17aee 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l117b2a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x117b2a (movR64M64Effect 0x117b2a 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x117b2a (LoadPre 0x117b2a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x117b2a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117b2a 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x117b2f (StorePre 0x117b2f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x117b2f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117b2f 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x117b34 (movR64M64Effect 0x117b34 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x117b34 (LoadPre 0x117b34 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x117b34 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117b34 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x117b39 (StorePre 0x117b39 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x117b39 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117b39 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x117b3e (movR64M64Effect 0x117b3e 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x117b3e (LoadPre 0x117b3e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x117b3e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117b3e 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x117b43 (StorePre 0x117b43 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x117b43 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117b43 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x117b48 (movR64M64Effect 0x117b48 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x117b48 (LoadPre 0x117b48 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x117b48 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117b48 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x117b4d (movR64M64Effect 0x117b4d 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x117b4d (LoadPre 0x117b4d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x117b4d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117b4d 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x117b52 (StorePre 0x117b52 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x117b52 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117b52 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x117b57 (StorePre 0x117b57 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x117b57 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x117b57 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x117b5b (movR64R64Effect 0x117b5b 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x117b5b (fun s => s.RIP = 0x117b5b) (movR64R64Effect 0x117b5b 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x117b5e (movR64R64Effect 0x117b5e 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x117b5e (fun s => s.RIP = 0x117b5e) (movR64R64Effect 0x117b5e 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x117b61 (callEffect (fun _ => 0x1145f0) 0x117b66) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x117b61 (PushPre 0x117b61 5) (callEffect (fun _ => 0x1145f0) 0x117b66) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x117b66⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l117b66, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l117b2a : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x8A, 0xCA, 0xFF, 0xFF]

theorem code_l117b2a : ∀ x ∈ codeRange 0x117b2a bytes_l117b2a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x17b2a 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l117b66 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x117b66 (movR64M64Effect 0x117b66 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x117b66 (LoadPre 0x117b66 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x117b66 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117b66 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x117b6b (StorePre 0x117b6b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x117b6b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117b6b 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x117b70 (movR64M64Effect 0x117b70 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x117b70 (LoadPre 0x117b70 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x117b70 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117b70 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x117b75 (StorePre 0x117b75 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x117b75 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117b75 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x117b7a (movR64M64Effect 0x117b7a 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x117b7a (LoadPre 0x117b7a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x117b7a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117b7a 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x117b7f (StorePre 0x117b7f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x117b7f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117b7f 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x117b84 (movR64M64Effect 0x117b84 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x117b84 (LoadPre 0x117b84 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x117b84 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117b84 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x117b89 (movR64M64Effect 0x117b89 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x117b89 (LoadPre 0x117b89 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x117b89 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117b89 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x117b8e (StorePre 0x117b8e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x117b8e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117b8e 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x117b93 (StorePre 0x117b93 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x117b93 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x117b93 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x117b97 (movR64R64Effect 0x117b97 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x117b97 (fun s => s.RIP = 0x117b97) (movR64R64Effect 0x117b97 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x117b9a (movR64R64Effect 0x117b9a 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x117b9a (fun s => s.RIP = 0x117b9a) (movR64R64Effect 0x117b9a 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x117b9d (callEffect (fun _ => 0x1145f0) 0x117ba2) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x117b9d (PushPre 0x117b9d 5) (callEffect (fun _ => 0x1145f0) 0x117ba2) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x117ba2⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l117ba2, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l117b66 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x4E, 0xCA, 0xFF, 0xFF]

theorem code_l117b66 : ∀ x ∈ codeRange 0x117b66 bytes_l117b66, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x17b66 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l117ba2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x117ba2 (movR64M64Effect 0x117ba2 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x117ba2 (LoadPre 0x117ba2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x117ba2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117ba2 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x117ba7 (StorePre 0x117ba7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x117ba7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117ba7 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x117bac (movR64M64Effect 0x117bac 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x117bac (LoadPre 0x117bac (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x117bac + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117bac 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x117bb1 (StorePre 0x117bb1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x117bb1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117bb1 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x117bb6 (movR64M64Effect 0x117bb6 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x117bb6 (LoadPre 0x117bb6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x117bb6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117bb6 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x117bbb (StorePre 0x117bbb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x117bbb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117bbb 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x117bc0 (movR64M64Effect 0x117bc0 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x117bc0 (LoadPre 0x117bc0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x117bc0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117bc0 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x117bc5 (movR64M64Effect 0x117bc5 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x117bc5 (LoadPre 0x117bc5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x117bc5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117bc5 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x117bca (StorePre 0x117bca 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x117bca + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117bca 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x117bcf (StorePre 0x117bcf 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x117bcf + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x117bcf 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x117bd3 (movR64R64Effect 0x117bd3 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x117bd3 (fun s => s.RIP = 0x117bd3) (movR64R64Effect 0x117bd3 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x117bd6 (movR64R64Effect 0x117bd6 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x117bd6 (fun s => s.RIP = 0x117bd6) (movR64R64Effect 0x117bd6 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x117bd9 (callEffect (fun _ => 0x1145f0) 0x117bde) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x117bd9 (PushPre 0x117bd9 5) (callEffect (fun _ => 0x1145f0) 0x117bde) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x117bde⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l117bde, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l117ba2 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x12, 0xCA, 0xFF, 0xFF]

theorem code_l117ba2 : ∀ x ∈ codeRange 0x117ba2 bytes_l117ba2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x17ba2 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

def b_l117bde_12 : Block Op Label signature Reg.count 567 :=
  .letOp (n := 567) (.exec 0x118014 (StorePre 0x118014 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x118014 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x118014 1 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[528, 4]
    (.letOp (n := 568) (.exec 0x11801c (StorePre 0x11801c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11801c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11801c 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[528, 4]
    (.letOp (n := 569) (.exec 0x118021 (StorePre 0x118021 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x118021 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x118021 12 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[555, 4]
    (.letOp (n := 570) (.exec 0x118026 (StorePre 0x118026 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x118026 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x118026 12 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[555, 4]
    (.letOp (n := 571) (.exec 0x11802b (StorePre 0x11802b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x11802b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11802b 3 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[561, 4]
    (.letOp (n := 572) (.exec 0x118030 (StorePre 0x118030 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x118030 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x118030 3 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[561, 4]
    (.letOp (n := 573) (.out 0x118035 (movR32Imm32Effect 0x118035 5 3 0x2c) (EffectPart.reads (.reg (.gpr 3)) [] []) (.reg (.gpr 3))) #v[]
    (.letOp (n := 574) (.exec 0x118035 (fun s => s.RIP = 0x118035) (movR32Imm32Effect 0x118035 5 3 0x2c) (Reg.operands [] [])) #v[]
    (.letOp (n := 575) (.exec 0x11803a (fun s => s.RIP = 0x11803a) (fun _ => nopEffect 0x11803a 6) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l118040, RegMap.args [(0, 557), (1, 528), (2, 553), (3, 573), (4, 4), (5, 374), (6, 526), (7, 493), (8, 522), (9, 435), (10, 461), (11, 458), (12, 555), (13, 497), (14, 524), (15, 482), (22, 22), (39, 39), (50, 50), (51, 51)] 576⟩))))))))))

def bytes_l117bde_12 : List UInt8 :=
  [0x48, 0x89, 0x8C, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0x89, 0x4C, 0x24, 0x10, 0x4C, 0x89, 0x64,
    0x24, 0x50, 0x4C, 0x89, 0x64, 0x24, 0x18, 0x48, 0x89, 0x5C, 0x24, 0x58, 0x48, 0x89, 0x5C, 0x24,
    0x20, 0xBB, 0x2C, 0x00, 0x00, 0x00, 0x66, 0x0F, 0x1F, 0x44, 0x00, 0x00]

theorem code_l117bde_12 : ∀ x ∈ codeRange 0x118014 bytes_l117bde_12, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x18014 44 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

def b_l117bde_11 : Block Op Label signature Reg.count 530 :=
  .letOp (n := 530) (.out 0x117fbe (movR64R64Effect 0x117fbe 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[522]
    (.letOp (n := 531) (.exec 0x117fbe (fun s => s.RIP = 0x117fbe) (movR64R64Effect 0x117fbe 0 8) (Reg.operands [.gpr 8] [])) #v[522]
    (.letOp (n := 532) (.out 0x117fc1 (mulR64Effect 0x117fc1 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[497, 530]
    (.letOp (n := 533) (.out 0x117fc1 (mulR64Effect 0x117fc1 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[497, 530]
    (.letOp (n := 534) (.exec 0x117fc1 (fun s => s.RIP = 0x117fc1) (mulR64Effect 0x117fc1 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[497, 530]
    (.letOp (n := 535) (.out 0x117fc4 (andR64R64Effect 0x117fc4 12 7) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 7] []) (.reg (.gpr 12))) #v[155, 493]
    (.letOp (n := 536) (.exec 0x117fc4 (fun s => s.RIP = 0x117fc4) (andR64R64Effect 0x117fc4 12 7) (Reg.operands [.gpr 12, .gpr 7] [])) #v[155, 493]
    (.letOp (n := 537) (.out 0x117fc7 (addR64R64Effect 0x117fc7 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 0] []) (.reg (.gpr 12))) #v[535, 532]
    (.letOp (n := 538) (.out 0x117fc7 (addR64R64Effect 0x117fc7 12 0) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 0] []) (.flag .CF)) #v[535, 532]
    (.letOp (n := 539) (.exec 0x117fc7 (fun s => s.RIP = 0x117fc7) (addR64R64Effect 0x117fc7 12 0) (Reg.operands [.gpr 12, .gpr 0] [])) #v[535, 532]
    (.letOp (n := 540) (.out 0x117fca (atFlags StatusFlags.CF (adcR64Imm8Effect 0x117fca 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[533, 538]
    (.letOp (n := 541) (.exec 0x117fca (fun s => s.RIP = 0x117fca) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x117fca 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[533, 538]
    (.letOp (n := 542) (.out 0x117fce (movR64M64Effect 0x117fce 0 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 543) (.exec 0x117fce (LoadPre 0x117fce (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x117fce + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117fce 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 544) (.exec 0x117fd3 (StorePre 0x117fd3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x117fd3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117fd3 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[542, 4]
    (.letOp (n := 545) (.out 0x117fd8 (addR64R64Effect 0x117fd8 12 6) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 6] []) (.reg (.gpr 12))) #v[537, 526]
    (.letOp (n := 546) (.out 0x117fd8 (addR64R64Effect 0x117fd8 12 6) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 6] []) (.flag .CF)) #v[537, 526]
    (.letOp (n := 547) (.exec 0x117fd8 (fun s => s.RIP = 0x117fd8) (addR64R64Effect 0x117fd8 12 6) (Reg.operands [.gpr 12, .gpr 6] [])) #v[537, 526]
    (.letOp (n := 548) (.out 0x117fdb (atFlags StatusFlags.CF (adcR64Imm8Effect 0x117fdb 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[540, 546]
    (.letOp (n := 549) (.exec 0x117fdb (fun s => s.RIP = 0x117fdb) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x117fdb 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[540, 546]
    (.letOp (n := 550) (.out 0x117fdf (movR64M64Effect 0x117fdf 0 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 551) (.exec 0x117fdf (LoadPre 0x117fdf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x117fdf + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117fdf 0 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 552) (.exec 0x117fe4 (StorePre 0x117fe4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x117fe4 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117fe4 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[550, 4]
    (.letOp (n := 553) (.out 0x117fe9 (shldR64R64Effect 0x117fe9 5 2 12 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[548, 545]
    (.letOp (n := 554) (.exec 0x117fe9 (fun s => s.RIP = 0x117fe9) (shldR64R64Effect 0x117fe9 5 2 12 12) (Reg.operands [.gpr 2, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[548, 545]
    (.letOp (n := 555) (.out 0x117fee (andR64R64Effect 0x117fee 12 7) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 7] []) (.reg (.gpr 12))) #v[545, 493]
    (.letOp (n := 556) (.exec 0x117fee (fun s => s.RIP = 0x117fee) (andR64R64Effect 0x117fee 12 7) (Reg.operands [.gpr 12, .gpr 7] [])) #v[545, 493]
    (.letOp (n := 557) (.out 0x117ff1 (movR64Imm64Effect 0x117ff1 0 0xffffffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 558) (.exec 0x117ff1 (fun s => s.RIP = 0x117ff1) (movR64Imm64Effect 0x117ff1 0 0xffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 559) (.out 0x117ffb (andR64R64Effect 0x117ffb 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0] []) (.reg (.gpr 3))) #v[245, 557]
    (.letOp (n := 560) (.exec 0x117ffb (fun s => s.RIP = 0x117ffb) (andR64R64Effect 0x117ffb 3 0) (Reg.operands [.gpr 3, .gpr 0] [])) #v[245, 557]
    (.letOp (n := 561) (.out 0x117ffe (addR64R64Effect 0x117ffe 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 2] []) (.reg (.gpr 3))) #v[559, 553]
    (.letOp (n := 562) (.exec 0x117ffe (fun s => s.RIP = 0x117ffe) (addR64R64Effect 0x117ffe 3 2) (Reg.operands [.gpr 3, .gpr 2] [])) #v[559, 553]
    (.letOp (n := 563) (.exec 0x118001 (StorePre 0x118001 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x118001 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x118001 5 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[374, 4]
    (.letOp (n := 564) (.exec 0x118006 (StorePre 0x118006 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x118006 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x118006 5 (.sib 4 none 0 .none)) (Reg.operands [.gpr 5, .gpr 4] [])) #v[374, 4]
    (.letOp (n := 565) (.exec 0x11800a (StorePre 0x11800a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x11800a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11800a 10 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[461, 4]
    (.letOp (n := 566) (.exec 0x11800f (StorePre 0x11800f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11800f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11800f 10 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[461, 4]
    (b_l117bde_12)))))))))))))))))))))))))))))))))))))

def bytes_l117bde_11 : List UInt8 :=
  [0x4C, 0x89, 0xC0, 0x49, 0xF7, 0xE5, 0x49, 0x21, 0xFC, 0x49, 0x01, 0xC4, 0x48, 0x83, 0xD2, 0x00,
    0x48, 0x8B, 0x44, 0x24, 0x58, 0x48, 0x89, 0x44, 0x24, 0x20, 0x49, 0x01, 0xF4, 0x48, 0x83, 0xD2,
    0x00, 0x48, 0x8B, 0x44, 0x24, 0x50, 0x48, 0x89, 0x44, 0x24, 0x18, 0x4C, 0x0F, 0xA4, 0xE2, 0x0C,
    0x49, 0x21, 0xFC, 0x48, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x48, 0x21, 0xC3,
    0x48, 0x01, 0xD3, 0x48, 0x89, 0x6C, 0x24, 0x78, 0x48, 0x89, 0x2C, 0x24, 0x4C, 0x89, 0x54, 0x24,
    0x60, 0x4C, 0x89, 0x54, 0x24, 0x08] ++ bytes_l117bde_12

theorem code_l117bde_11 : ∀ x ∈ codeRange 0x117fbe bytes_l117bde_11, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x17fbe 86 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l117bde_12

def b_l117bde_10 : Block Op Label signature Reg.count 484 :=
  .letOp (n := 484) (.out 0x117f5d (atFlags StatusFlags.CF (adcR64R64Effect 0x117f5d 8 2)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[468, 475, 480]
    (.letOp (n := 485) (.exec 0x117f5d (fun s => s.RIP = 0x117f5d) (atFlags StatusFlags.CF (adcR64R64Effect 0x117f5d 8 2)) (Reg.operands [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[468, 475, 480]
    (.letOp (n := 486) (.out 0x117f60 (addR64R64Effect 0x117f60 14 7) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 7] []) (.reg (.gpr 14))) #v[479, 409]
    (.letOp (n := 487) (.out 0x117f60 (addR64R64Effect 0x117f60 14 7) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 7] []) (.flag .CF)) #v[479, 409]
    (.letOp (n := 488) (.exec 0x117f60 (fun s => s.RIP = 0x117f60) (addR64R64Effect 0x117f60 14 7) (Reg.operands [.gpr 14, .gpr 7] [])) #v[479, 409]
    (.letOp (n := 489) (.out 0x117f63 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x117f63 8 0x0)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[484, 487]
    (.letOp (n := 490) (.exec 0x117f63 (fun s => s.RIP = 0x117f63) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x117f63 8 0x0)) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[484, 487]
    (.letOp (n := 491) (.out 0x117f67 (movR64R64Effect 0x117f67 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[486]
    (.letOp (n := 492) (.exec 0x117f67 (fun s => s.RIP = 0x117f67) (movR64R64Effect 0x117f67 0 14) (Reg.operands [.gpr 14] [])) #v[486]
    (.letOp (n := 493) (.out 0x117f6a (movR64Imm64Effect 0x117f6a 7 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 494) (.exec 0x117f6a (fun s => s.RIP = 0x117f6a) (movR64Imm64Effect 0x117f6a 7 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 495) (.out 0x117f74 (andR64R64Effect 0x117f74 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[491, 493]
    (.letOp (n := 496) (.exec 0x117f74 (fun s => s.RIP = 0x117f74) (andR64R64Effect 0x117f74 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[491, 493]
    (.letOp (n := 497) (.out 0x117f77 (movR64Imm64Effect 0x117f77 13 0x1000003d10) (EffectPart.reads (.reg (.gpr 13)) [] []) (.reg (.gpr 13))) #v[]
    (.letOp (n := 498) (.exec 0x117f77 (fun s => s.RIP = 0x117f77) (movR64Imm64Effect 0x117f77 13 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 499) (.out 0x117f81 (mulR64Effect 0x117f81 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[497, 495]
    (.letOp (n := 500) (.out 0x117f81 (mulR64Effect 0x117f81 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[497, 495]
    (.letOp (n := 501) (.exec 0x117f81 (fun s => s.RIP = 0x117f81) (mulR64Effect 0x117f81 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[497, 495]
    (.letOp (n := 502) (.out 0x117f84 (addR64M64Effect 0x117f84 1 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 4] []) (.reg (.gpr 1))) #v[451, 4]
    (.letOp (n := 503) (.out 0x117f84 (addR64M64Effect 0x117f84 1 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 4] []) (.flag .CF)) #v[451, 4]
    (.letOp (n := 504) (.exec 0x117f84 (LoadPre 0x117f84 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x117f84 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x117f84 1 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[451, 4]
    (.letOp (n := 505) (.out 0x117f8c (atFlags StatusFlags.CF (adcR64M64Effect 0x117f8c 6 (.sib 4 none 0 (.d32 0x98)))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 6))) #v[449, 4, 503]
    (.letOp (n := 506) (.exec 0x117f8c (LoadPre 0x117f8c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x117f8c + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x117f8c 6 (.sib 4 none 0 (.d32 0x98)))) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[449, 4, 503]
    (.letOp (n := 507) (.out 0x117f94 (addR64R64Effect 0x117f94 1 11) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 11] []) (.reg (.gpr 1))) #v[502, 458]
    (.letOp (n := 508) (.out 0x117f94 (addR64R64Effect 0x117f94 1 11) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 11] []) (.flag .CF)) #v[502, 458]
    (.letOp (n := 509) (.exec 0x117f94 (fun s => s.RIP = 0x117f94) (addR64R64Effect 0x117f94 1 11) (Reg.operands [.gpr 1, .gpr 11] [])) #v[502, 458]
    (.letOp (n := 510) (.out 0x117f97 (atFlags StatusFlags.CF (adcR64M64Effect 0x117f97 6 (.sib 4 none 0 (.d32 0x80)))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 6))) #v[505, 4, 508]
    (.letOp (n := 511) (.exec 0x117f97 (LoadPre 0x117f97 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x117f97 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x117f97 6 (.sib 4 none 0 (.d32 0x80)))) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[505, 4, 508]
    (.letOp (n := 512) (.out 0x117f9f (addR64R64Effect 0x117f9f 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[507, 499]
    (.letOp (n := 513) (.out 0x117f9f (addR64R64Effect 0x117f9f 1 0) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 0] []) (.flag .CF)) #v[507, 499]
    (.letOp (n := 514) (.exec 0x117f9f (fun s => s.RIP = 0x117f9f) (addR64R64Effect 0x117f9f 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[507, 499]
    (.letOp (n := 515) (.out 0x117fa2 (atFlags StatusFlags.CF (adcR64R64Effect 0x117fa2 6 2)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[510, 500, 513]
    (.letOp (n := 516) (.exec 0x117fa2 (fun s => s.RIP = 0x117fa2) (atFlags StatusFlags.CF (adcR64R64Effect 0x117fa2 6 2)) (Reg.operands [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[510, 500, 513]
    (.letOp (n := 517) (.out 0x117fa5 (addR64R64Effect 0x117fa5 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 9] []) (.reg (.gpr 1))) #v[512, 435]
    (.letOp (n := 518) (.out 0x117fa5 (addR64R64Effect 0x117fa5 1 9) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 9] []) (.flag .CF)) #v[512, 435]
    (.letOp (n := 519) (.exec 0x117fa5 (fun s => s.RIP = 0x117fa5) (addR64R64Effect 0x117fa5 1 9) (Reg.operands [.gpr 1, .gpr 9] [])) #v[512, 435]
    (.letOp (n := 520) (.out 0x117fa8 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x117fa8 6 0x0)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[515, 518]
    (.letOp (n := 521) (.exec 0x117fa8 (fun s => s.RIP = 0x117fa8) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x117fa8 6 0x0)) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[515, 518]
    (.letOp (n := 522) (.out 0x117fac (shldR64R64Effect 0x117fac 5 8 14 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[489, 486]
    (.letOp (n := 523) (.exec 0x117fac (fun s => s.RIP = 0x117fac) (shldR64R64Effect 0x117fac 5 8 14 12) (Reg.operands [.gpr 8, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[489, 486]
    (.letOp (n := 524) (.out 0x117fb1 (leaR64Effect 0x117fb1 14 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 525) (.exec 0x117fb1 (fun s => s.RIP = 0x117fb1) (leaR64Effect 0x117fb1 14 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 526) (.out 0x117fb6 (shldR64R64Effect 0x117fb6 5 6 1 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[520, 517]
    (.letOp (n := 527) (.exec 0x117fb6 (fun s => s.RIP = 0x117fb6) (shldR64R64Effect 0x117fb6 5 6 1 12) (Reg.operands [.gpr 6, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[520, 517]
    (.letOp (n := 528) (.out 0x117fbb (andR64R64Effect 0x117fbb 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[517, 493]
    (.letOp (n := 529) (.exec 0x117fbb (fun s => s.RIP = 0x117fbb) (andR64R64Effect 0x117fbb 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[517, 493]
    (b_l117bde_11))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l117bde_10 : List UInt8 :=
  [0x49, 0x11, 0xD0, 0x49, 0x01, 0xFE, 0x49, 0x83, 0xD0, 0x00, 0x4C, 0x89, 0xF0, 0x48, 0xBF, 0xFF,
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48, 0x21, 0xF8, 0x49, 0xBD, 0x10, 0x3D, 0x00, 0x00,
    0x10, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE5, 0x48, 0x03, 0x8C, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x48,
    0x13, 0xB4, 0x24, 0x98, 0x00, 0x00, 0x00, 0x4C, 0x01, 0xD9, 0x48, 0x13, 0xB4, 0x24, 0x80, 0x00,
    0x00, 0x00, 0x48, 0x01, 0xC1, 0x48, 0x11, 0xD6, 0x4C, 0x01, 0xC9, 0x48, 0x83, 0xD6, 0x00, 0x4D,
    0x0F, 0xA4, 0xF0, 0x0C, 0x4C, 0x8D, 0x74, 0x24, 0x28, 0x48, 0x0F, 0xA4, 0xCE, 0x0C, 0x48, 0x21,
    0xF9] ++ bytes_l117bde_11

theorem code_l117bde_10 : ∀ x ∈ codeRange 0x117f5d bytes_l117bde_10, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x17f5d 97 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l117bde_11

def b_l117bde_9 : Block Op Label signature Reg.count 442 :=
  .letOp (n := 442) (.exec 0x117ef8 (StorePre 0x117ef8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x117ef8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x117ef8 2 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[440, 4]
    (.letOp (n := 443) (.exec 0x117f00 (StorePre 0x117f00 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x117f00 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x117f00 0 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[439, 4]
    (.letOp (n := 444) (.out 0x117f08 (movR64M64Effect 0x117f08 0 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 445) (.exec 0x117f08 (LoadPre 0x117f08 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x117f08 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x117f08 0 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 446) (.out 0x117f10 (mulM64Effect 0x117f10 8 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[444, 4]
    (.letOp (n := 447) (.out 0x117f10 (mulM64Effect 0x117f10 8 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[444, 4]
    (.letOp (n := 448) (.exec 0x117f10 (LoadPre 0x117f10 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x117f10 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x117f10 8 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[444, 4]
    (.letOp (n := 449) (.out 0x117f18 (movR64R64Effect 0x117f18 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[447]
    (.letOp (n := 450) (.exec 0x117f18 (fun s => s.RIP = 0x117f18) (movR64R64Effect 0x117f18 6 2) (Reg.operands [.gpr 2] [])) #v[447]
    (.letOp (n := 451) (.out 0x117f1b (movR64R64Effect 0x117f1b 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[446]
    (.letOp (n := 452) (.exec 0x117f1b (fun s => s.RIP = 0x117f1b) (movR64R64Effect 0x117f1b 1 0) (Reg.operands [.gpr 0] [])) #v[446]
    (.letOp (n := 453) (.out 0x117f1e (movR64M64Effect 0x117f1e 0 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 454) (.exec 0x117f1e (LoadPre 0x117f1e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x117f1e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x117f1e 0 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 455) (.out 0x117f26 (mulM64Effect 0x117f26 8 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[453, 4]
    (.letOp (n := 456) (.out 0x117f26 (mulM64Effect 0x117f26 8 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[453, 4]
    (.letOp (n := 457) (.exec 0x117f26 (LoadPre 0x117f26 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x117f26 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x117f26 8 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[453, 4]
    (.letOp (n := 458) (.out 0x117f2e (movR64R64Effect 0x117f2e 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[455]
    (.letOp (n := 459) (.exec 0x117f2e (fun s => s.RIP = 0x117f2e) (movR64R64Effect 0x117f2e 11 0) (Reg.operands [.gpr 0] [])) #v[455]
    (.letOp (n := 460) (.exec 0x117f31 (StorePre 0x117f31 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x117f31 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x117f31 2 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[456, 4]
    (.letOp (n := 461) (.out 0x117f39 (andR64R64Effect 0x117f39 10 14) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 14] []) (.reg (.gpr 10))) #v[430, 411]
    (.letOp (n := 462) (.exec 0x117f39 (fun s => s.RIP = 0x117f39) (andR64R64Effect 0x117f39 10 14) (Reg.operands [.gpr 10, .gpr 14] [])) #v[430, 411]
    (.letOp (n := 463) (.out 0x117f3c (movR64M64Effect 0x117f3c 0 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 464) (.exec 0x117f3c (LoadPre 0x117f3c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x117f3c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117f3c 0 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 465) (.out 0x117f41 (mulM64Effect 0x117f41 5 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[463, 4]
    (.letOp (n := 466) (.out 0x117f41 (mulM64Effect 0x117f41 5 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[463, 4]
    (.letOp (n := 467) (.exec 0x117f41 (LoadPre 0x117f41 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x117f41 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x117f41 5 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[463, 4]
    (.letOp (n := 468) (.out 0x117f46 (movR64R64Effect 0x117f46 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[466]
    (.letOp (n := 469) (.exec 0x117f46 (fun s => s.RIP = 0x117f46) (movR64R64Effect 0x117f46 8 2) (Reg.operands [.gpr 2] [])) #v[466]
    (.letOp (n := 470) (.out 0x117f49 (movR64R64Effect 0x117f49 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[465]
    (.letOp (n := 471) (.exec 0x117f49 (fun s => s.RIP = 0x117f49) (movR64R64Effect 0x117f49 15 0) (Reg.operands [.gpr 0] [])) #v[465]
    (.letOp (n := 472) (.out 0x117f4c (movR64M64Effect 0x117f4c 0 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 473) (.exec 0x117f4c (LoadPre 0x117f4c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x117f4c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117f4c 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 474) (.out 0x117f51 (mulR64Effect 0x117f51 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[389, 472]
    (.letOp (n := 475) (.out 0x117f51 (mulR64Effect 0x117f51 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[389, 472]
    (.letOp (n := 476) (.exec 0x117f51 (fun s => s.RIP = 0x117f51) (mulR64Effect 0x117f51 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[389, 472]
    (.letOp (n := 477) (.out 0x117f54 (movR64R64Effect 0x117f54 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[474]
    (.letOp (n := 478) (.exec 0x117f54 (fun s => s.RIP = 0x117f54) (movR64R64Effect 0x117f54 14 0) (Reg.operands [.gpr 0] [])) #v[474]
    (.letOp (n := 479) (.out 0x117f57 (addR64R64Effect 0x117f57 14 15) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 15] []) (.reg (.gpr 14))) #v[477, 470]
    (.letOp (n := 480) (.out 0x117f57 (addR64R64Effect 0x117f57 14 15) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 15] []) (.flag .CF)) #v[477, 470]
    (.letOp (n := 481) (.exec 0x117f57 (fun s => s.RIP = 0x117f57) (addR64R64Effect 0x117f57 14 15) (Reg.operands [.gpr 14, .gpr 15] [])) #v[477, 470]
    (.letOp (n := 482) (.out 0x117f5a (movR64R64Effect 0x117f5a 15 4) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 483) (.exec 0x117f5a (fun s => s.RIP = 0x117f5a) (movR64R64Effect 0x117f5a 15 4) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l117bde_10))))))))))))))))))))))))))))))))))))))))))

def bytes_l117bde_9 : List UInt8 :=
  [0x48, 0x89, 0x94, 0x24, 0x98, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0xB8, 0x00, 0x00, 0x00,
    0x48, 0x8B, 0x84, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xA4, 0x24, 0x80, 0x00, 0x00, 0x00,
    0x48, 0x89, 0xD6, 0x48, 0x89, 0xC1, 0x48, 0x8B, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0xF7,
    0xA4, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x49, 0x89, 0xC3, 0x48, 0x89, 0x94, 0x24, 0x80, 0x00, 0x00,
    0x00, 0x4D, 0x21, 0xF2, 0x48, 0x8B, 0x44, 0x24, 0x70, 0x48, 0xF7, 0x64, 0x24, 0x50, 0x49, 0x89,
    0xD0, 0x49, 0x89, 0xC7, 0x48, 0x8B, 0x44, 0x24, 0x68, 0x49, 0xF7, 0xE5, 0x49, 0x89, 0xC6, 0x4D,
    0x01, 0xFE, 0x49, 0x89, 0xE7] ++ bytes_l117bde_10

theorem code_l117bde_9 : ∀ x ∈ codeRange 0x117ef8 bytes_l117bde_9, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x17ef8 101 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l117bde_10

def b_l117bde_8 : Block Op Label signature Reg.count 394 :=
  .letOp (n := 394) (.out 0x117e9c (addR64R64Effect 0x117e9c 14 11) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 11] []) (.reg (.gpr 14))) #v[383, 368]
    (.letOp (n := 395) (.out 0x117e9c (addR64R64Effect 0x117e9c 14 11) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 11] []) (.flag .CF)) #v[383, 368]
    (.letOp (n := 396) (.exec 0x117e9c (fun s => s.RIP = 0x117e9c) (addR64R64Effect 0x117e9c 14 11) (Reg.operands [.gpr 14, .gpr 11] [])) #v[383, 368]
    (.letOp (n := 397) (.out 0x117e9f (atFlags StatusFlags.CF (adcR64R64Effect 0x117e9f 7 1)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[381, 370, 395]
    (.letOp (n := 398) (.exec 0x117e9f (fun s => s.RIP = 0x117e9f) (atFlags StatusFlags.CF (adcR64R64Effect 0x117e9f 7 1)) (Reg.operands [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[381, 370, 395]
    (.letOp (n := 399) (.out 0x117ea2 (addR64R64Effect 0x117ea2 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[391, 394]
    (.letOp (n := 400) (.out 0x117ea2 (addR64R64Effect 0x117ea2 0 14) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 14] []) (.flag .CF)) #v[391, 394]
    (.letOp (n := 401) (.exec 0x117ea2 (fun s => s.RIP = 0x117ea2) (addR64R64Effect 0x117ea2 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[391, 394]
    (.letOp (n := 402) (.out 0x117ea5 (atFlags StatusFlags.CF (adcR64R64Effect 0x117ea5 7 2)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[397, 392, 400]
    (.letOp (n := 403) (.exec 0x117ea5 (fun s => s.RIP = 0x117ea5) (atFlags StatusFlags.CF (adcR64R64Effect 0x117ea5 7 2)) (Reg.operands [.gpr 7, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[397, 392, 400]
    (.letOp (n := 404) (.out 0x117ea8 (addR64R64Effect 0x117ea8 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[399, 321]
    (.letOp (n := 405) (.out 0x117ea8 (addR64R64Effect 0x117ea8 0 6) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 6] []) (.flag .CF)) #v[399, 321]
    (.letOp (n := 406) (.exec 0x117ea8 (fun s => s.RIP = 0x117ea8) (addR64R64Effect 0x117ea8 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[399, 321]
    (.letOp (n := 407) (.out 0x117eab (atFlags StatusFlags.CF (adcR64Imm8Effect 0x117eab 7 0x0)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[402, 405]
    (.letOp (n := 408) (.exec 0x117eab (fun s => s.RIP = 0x117eab) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x117eab 7 0x0)) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[402, 405]
    (.letOp (n := 409) (.out 0x117eaf (shldR64R64Effect 0x117eaf 5 7 0 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[407, 404]
    (.letOp (n := 410) (.exec 0x117eaf (fun s => s.RIP = 0x117eaf) (shldR64R64Effect 0x117eaf 5 7 0 12) (Reg.operands [.gpr 7, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[407, 404]
    (.letOp (n := 411) (.out 0x117eb4 (movR64Imm64Effect 0x117eb4 14 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 14)) [] []) (.reg (.gpr 14))) #v[]
    (.letOp (n := 412) (.exec 0x117eb4 (fun s => s.RIP = 0x117eb4) (movR64Imm64Effect 0x117eb4 14 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 413) (.out 0x117ebe (andR64R64Effect 0x117ebe 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[404, 411]
    (.letOp (n := 414) (.exec 0x117ebe (fun s => s.RIP = 0x117ebe) (andR64R64Effect 0x117ebe 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[404, 411]
    (.letOp (n := 415) (.out 0x117ec1 (movR64Imm64Effect 0x117ec1 1 0x1000003d10) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 416) (.exec 0x117ec1 (fun s => s.RIP = 0x117ec1) (movR64Imm64Effect 0x117ec1 1 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 417) (.out 0x117ecb (mulR64Effect 0x117ecb 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[415, 413]
    (.letOp (n := 418) (.out 0x117ecb (mulR64Effect 0x117ecb 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[415, 413]
    (.letOp (n := 419) (.exec 0x117ecb (fun s => s.RIP = 0x117ecb) (mulR64Effect 0x117ecb 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[415, 413]
    (.letOp (n := 420) (.out 0x117ece (addR64M64Effect 0x117ece 10 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 4] []) (.reg (.gpr 10))) #v[361, 4]
    (.letOp (n := 421) (.out 0x117ece (addR64M64Effect 0x117ece 10 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 4] []) (.flag .CF)) #v[361, 4]
    (.letOp (n := 422) (.exec 0x117ece (LoadPre 0x117ece (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x117ece + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x117ece 10 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[361, 4]
    (.letOp (n := 423) (.out 0x117ed6 (atFlags StatusFlags.CF (adcR64M64Effect 0x117ed6 9 (.sib 4 none 0 (.d32 0x98)))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 9))) #v[359, 4, 421]
    (.letOp (n := 424) (.exec 0x117ed6 (LoadPre 0x117ed6 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x117ed6 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x117ed6 9 (.sib 4 none 0 (.d32 0x98)))) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[359, 4, 421]
    (.letOp (n := 425) (.out 0x117ede (addR64R64Effect 0x117ede 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0] []) (.reg (.gpr 10))) #v[420, 417]
    (.letOp (n := 426) (.out 0x117ede (addR64R64Effect 0x117ede 10 0) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 0] []) (.flag .CF)) #v[420, 417]
    (.letOp (n := 427) (.exec 0x117ede (fun s => s.RIP = 0x117ede) (addR64R64Effect 0x117ede 10 0) (Reg.operands [.gpr 10, .gpr 0] [])) #v[420, 417]
    (.letOp (n := 428) (.out 0x117ee1 (atFlags StatusFlags.CF (adcR64R64Effect 0x117ee1 9 2)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[423, 418, 426]
    (.letOp (n := 429) (.exec 0x117ee1 (fun s => s.RIP = 0x117ee1) (atFlags StatusFlags.CF (adcR64R64Effect 0x117ee1 9 2)) (Reg.operands [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[423, 418, 426]
    (.letOp (n := 430) (.out 0x117ee4 (addR64R64Effect 0x117ee4 10 8) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 8] []) (.reg (.gpr 10))) #v[425, 345]
    (.letOp (n := 431) (.out 0x117ee4 (addR64R64Effect 0x117ee4 10 8) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 8] []) (.flag .CF)) #v[425, 345]
    (.letOp (n := 432) (.exec 0x117ee4 (fun s => s.RIP = 0x117ee4) (addR64R64Effect 0x117ee4 10 8) (Reg.operands [.gpr 10, .gpr 8] [])) #v[425, 345]
    (.letOp (n := 433) (.out 0x117ee7 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x117ee7 9 0x0)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[428, 431]
    (.letOp (n := 434) (.exec 0x117ee7 (fun s => s.RIP = 0x117ee7) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x117ee7 9 0x0)) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[428, 431]
    (.letOp (n := 435) (.out 0x117eeb (shldR64R64Effect 0x117eeb 5 9 10 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[433, 430]
    (.letOp (n := 436) (.exec 0x117eeb (fun s => s.RIP = 0x117eeb) (shldR64R64Effect 0x117eeb 5 9 10 12) (Reg.operands [.gpr 9, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[433, 430]
    (.letOp (n := 437) (.out 0x117ef0 (movR64R64Effect 0x117ef0 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[385]
    (.letOp (n := 438) (.exec 0x117ef0 (fun s => s.RIP = 0x117ef0) (movR64R64Effect 0x117ef0 0 15) (Reg.operands [.gpr 15] [])) #v[385]
    (.letOp (n := 439) (.out 0x117ef3 (mulM64Effect 0x117ef3 5 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[437, 4]
    (.letOp (n := 440) (.out 0x117ef3 (mulM64Effect 0x117ef3 5 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[437, 4]
    (.letOp (n := 441) (.exec 0x117ef3 (LoadPre 0x117ef3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x117ef3 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x117ef3 5 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[437, 4]
    (b_l117bde_9))))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l117bde_8 : List UInt8 :=
  [0x4D, 0x01, 0xDE, 0x48, 0x11, 0xCF, 0x4C, 0x01, 0xF0, 0x48, 0x11, 0xD7, 0x48, 0x01, 0xF0, 0x48,
    0x83, 0xD7, 0x00, 0x48, 0x0F, 0xA4, 0xC7, 0x0C, 0x49, 0xBE, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0x0F, 0x00, 0x4C, 0x21, 0xF0, 0x48, 0xB9, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48,
    0xF7, 0xE1, 0x4C, 0x03, 0x94, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x4C, 0x13, 0x8C, 0x24, 0x98, 0x00,
    0x00, 0x00, 0x49, 0x01, 0xC2, 0x49, 0x11, 0xD1, 0x4D, 0x01, 0xC2, 0x49, 0x83, 0xD1, 0x00, 0x4D,
    0x0F, 0xA4, 0xD1, 0x0C, 0x4C, 0x89, 0xF8, 0x48, 0xF7, 0x64, 0x24, 0x60] ++ bytes_l117bde_9

theorem code_l117bde_8 : ∀ x ∈ codeRange 0x117e9c bytes_l117bde_8, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x17e9c 92 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l117bde_9

def b_l117bde_7 : Block Op Label signature Reg.count 352 :=
  .letOp (n := 352) (.exec 0x117e35 (StorePre 0x117e35 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x117e35 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x117e35 2 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[350, 4]
    (.letOp (n := 353) (.exec 0x117e3d (StorePre 0x117e3d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x117e3d + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x117e3d 0 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[349, 4]
    (.letOp (n := 354) (.out 0x117e45 (movR64M64Effect 0x117e45 0 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 355) (.exec 0x117e45 (LoadPre 0x117e45 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x117e45 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x117e45 0 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 356) (.out 0x117e4d (mulM64Effect 0x117e4d 8 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[354, 4]
    (.letOp (n := 357) (.out 0x117e4d (mulM64Effect 0x117e4d 8 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[354, 4]
    (.letOp (n := 358) (.exec 0x117e4d (LoadPre 0x117e4d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x117e4d + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x117e4d 8 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[354, 4]
    (.letOp (n := 359) (.out 0x117e55 (movR64R64Effect 0x117e55 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[357]
    (.letOp (n := 360) (.exec 0x117e55 (fun s => s.RIP = 0x117e55) (movR64R64Effect 0x117e55 9 2) (Reg.operands [.gpr 2] [])) #v[357]
    (.letOp (n := 361) (.out 0x117e58 (movR64R64Effect 0x117e58 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[356]
    (.letOp (n := 362) (.exec 0x117e58 (fun s => s.RIP = 0x117e58) (movR64R64Effect 0x117e58 10 0) (Reg.operands [.gpr 0] [])) #v[356]
    (.letOp (n := 363) (.out 0x117e5b (movR64M64Effect 0x117e5b 0 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 364) (.exec 0x117e5b (LoadPre 0x117e5b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x117e5b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117e5b 0 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 365) (.out 0x117e60 (mulM64Effect 0x117e60 8 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[363, 4]
    (.letOp (n := 366) (.out 0x117e60 (mulM64Effect 0x117e60 8 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[363, 4]
    (.letOp (n := 367) (.exec 0x117e60 (LoadPre 0x117e60 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x117e60 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x117e60 8 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[363, 4]
    (.letOp (n := 368) (.out 0x117e68 (movR64R64Effect 0x117e68 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[365]
    (.letOp (n := 369) (.exec 0x117e68 (fun s => s.RIP = 0x117e68) (movR64R64Effect 0x117e68 11 0) (Reg.operands [.gpr 0] [])) #v[365]
    (.letOp (n := 370) (.out 0x117e6b (movR64R64Effect 0x117e6b 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[366]
    (.letOp (n := 371) (.exec 0x117e6b (fun s => s.RIP = 0x117e6b) (movR64R64Effect 0x117e6b 1 2) (Reg.operands [.gpr 2] [])) #v[366]
    (.letOp (n := 372) (.out 0x117e6e (movR64Imm64Effect 0x117e6e 15 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 15)) [] []) (.reg (.gpr 15))) #v[]
    (.letOp (n := 373) (.exec 0x117e6e (fun s => s.RIP = 0x117e6e) (movR64Imm64Effect 0x117e6e 15 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 374) (.out 0x117e78 (andR64R64Effect 0x117e78 5 15) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 15] []) (.reg (.gpr 5))) #v[340, 372]
    (.letOp (n := 375) (.exec 0x117e78 (fun s => s.RIP = 0x117e78) (andR64R64Effect 0x117e78 5 15) (Reg.operands [.gpr 5, .gpr 15] [])) #v[340, 372]
    (.letOp (n := 376) (.out 0x117e7b (movR64M64Effect 0x117e7b 0 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 377) (.exec 0x117e7b (LoadPre 0x117e7b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x117e7b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117e7b 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 378) (.out 0x117e80 (mulR64Effect 0x117e80 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[285, 376]
    (.letOp (n := 379) (.out 0x117e80 (mulR64Effect 0x117e80 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[285, 376]
    (.letOp (n := 380) (.exec 0x117e80 (fun s => s.RIP = 0x117e80) (mulR64Effect 0x117e80 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[285, 376]
    (.letOp (n := 381) (.out 0x117e83 (movR64R64Effect 0x117e83 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[379]
    (.letOp (n := 382) (.exec 0x117e83 (fun s => s.RIP = 0x117e83) (movR64R64Effect 0x117e83 7 2) (Reg.operands [.gpr 2] [])) #v[379]
    (.letOp (n := 383) (.out 0x117e86 (movR64R64Effect 0x117e86 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[378]
    (.letOp (n := 384) (.exec 0x117e86 (fun s => s.RIP = 0x117e86) (movR64R64Effect 0x117e86 14 0) (Reg.operands [.gpr 0] [])) #v[378]
    (.letOp (n := 385) (.out 0x117e89 (movR64M64Effect 0x117e89 15 (.sib 4 none 0 (.d32 0x108))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 386) (.exec 0x117e89 (LoadPre 0x117e89 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x117e89 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x117e89 15 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 387) (.out 0x117e91 (movR64R64Effect 0x117e91 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[385]
    (.letOp (n := 388) (.exec 0x117e91 (fun s => s.RIP = 0x117e91) (movR64R64Effect 0x117e91 0 15) (Reg.operands [.gpr 15] [])) #v[385]
    (.letOp (n := 389) (.out 0x117e94 (movR64M64Effect 0x117e94 13 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 390) (.exec 0x117e94 (LoadPre 0x117e94 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x117e94 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117e94 13 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 391) (.out 0x117e99 (mulR64Effect 0x117e99 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[389, 387]
    (.letOp (n := 392) (.out 0x117e99 (mulR64Effect 0x117e99 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[389, 387]
    (.letOp (n := 393) (.exec 0x117e99 (fun s => s.RIP = 0x117e99) (mulR64Effect 0x117e99 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[389, 387]
    (b_l117bde_8))))))))))))))))))))))))))))))))))))))))))

def bytes_l117bde_7 : List UInt8 :=
  [0x48, 0x89, 0x94, 0x24, 0x98, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0xB8, 0x00, 0x00, 0x00,
    0x48, 0x8B, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xA4, 0x24, 0x80, 0x00, 0x00, 0x00,
    0x49, 0x89, 0xD1, 0x49, 0x89, 0xC2, 0x48, 0x8B, 0x44, 0x24, 0x70, 0x48, 0xF7, 0xA4, 0x24, 0xC8,
    0x00, 0x00, 0x00, 0x49, 0x89, 0xC3, 0x48, 0x89, 0xD1, 0x49, 0xBF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0x0F, 0x00, 0x4C, 0x21, 0xFD, 0x48, 0x8B, 0x44, 0x24, 0x68, 0x49, 0xF7, 0xE5, 0x48, 0x89,
    0xD7, 0x49, 0x89, 0xC6, 0x4C, 0x8B, 0xBC, 0x24, 0x08, 0x01, 0x00, 0x00, 0x4C, 0x89, 0xF8, 0x4C,
    0x8B, 0x6C, 0x24, 0x58, 0x49, 0xF7, 0xE5] ++ bytes_l117bde_8

theorem code_l117bde_7 : ∀ x ∈ codeRange 0x117e35 bytes_l117bde_7, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x17e35 103 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l117bde_8

def b_l117bde_6 : Block Op Label signature Reg.count 306 :=
  .letOp (n := 306) (.out 0x117ddc (addR64R64Effect 0x117ddc 11 14) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 14] []) (.reg (.gpr 11))) #v[301, 292]
    (.letOp (n := 307) (.out 0x117ddc (addR64R64Effect 0x117ddc 11 14) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 14] []) (.flag .CF)) #v[301, 292]
    (.letOp (n := 308) (.exec 0x117ddc (fun s => s.RIP = 0x117ddc) (addR64R64Effect 0x117ddc 11 14) (Reg.operands [.gpr 11, .gpr 14] [])) #v[301, 292]
    (.letOp (n := 309) (.out 0x117ddf (atFlags StatusFlags.CF (adcR64R64Effect 0x117ddf 6 10)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[304, 290, 307]
    (.letOp (n := 310) (.exec 0x117ddf (fun s => s.RIP = 0x117ddf) (atFlags StatusFlags.CF (adcR64R64Effect 0x117ddf 6 10)) (Reg.operands [.gpr 6, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[304, 290, 307]
    (.letOp (n := 311) (.out 0x117de2 (addR64R64Effect 0x117de2 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[298, 306]
    (.letOp (n := 312) (.out 0x117de2 (addR64R64Effect 0x117de2 0 11) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 11] []) (.flag .CF)) #v[298, 306]
    (.letOp (n := 313) (.exec 0x117de2 (fun s => s.RIP = 0x117de2) (addR64R64Effect 0x117de2 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[298, 306]
    (.letOp (n := 314) (.out 0x117de5 (atFlags StatusFlags.CF (adcR64R64Effect 0x117de5 6 2)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[309, 299, 312]
    (.letOp (n := 315) (.exec 0x117de5 (fun s => s.RIP = 0x117de5) (atFlags StatusFlags.CF (adcR64R64Effect 0x117de5 6 2)) (Reg.operands [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[309, 299, 312]
    (.letOp (n := 316) (.out 0x117de8 (addR64R64Effect 0x117de8 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[311, 250]
    (.letOp (n := 317) (.out 0x117de8 (addR64R64Effect 0x117de8 0 1) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 1] []) (.flag .CF)) #v[311, 250]
    (.letOp (n := 318) (.exec 0x117de8 (fun s => s.RIP = 0x117de8) (addR64R64Effect 0x117de8 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[311, 250]
    (.letOp (n := 319) (.out 0x117deb (atFlags StatusFlags.CF (adcR64Imm8Effect 0x117deb 6 0x0)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[314, 317]
    (.letOp (n := 320) (.exec 0x117deb (fun s => s.RIP = 0x117deb) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x117deb 6 0x0)) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[314, 317]
    (.letOp (n := 321) (.out 0x117def (shldR64R64Effect 0x117def 5 6 0 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[319, 316]
    (.letOp (n := 322) (.exec 0x117def (fun s => s.RIP = 0x117def) (shldR64R64Effect 0x117def 5 6 0 12) (Reg.operands [.gpr 6, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[319, 316]
    (.letOp (n := 323) (.out 0x117df4 (shlR64Effect 0x117df4 4 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[316]
    (.letOp (n := 324) (.exec 0x117df4 (fun s => s.RIP = 0x117df4) (shlR64Effect 0x117df4 4 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[316]
    (.letOp (n := 325) (.out 0x117df8 (movR64Imm64Effect 0x117df8 1 0xfffffffffffff0) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 326) (.exec 0x117df8 (fun s => s.RIP = 0x117df8) (movR64Imm64Effect 0x117df8 1 0xfffffffffffff0) (Reg.operands [] [])) #v[]
    (.letOp (n := 327) (.out 0x117e02 (andR64R64Effect 0x117e02 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[323, 325]
    (.letOp (n := 328) (.exec 0x117e02 (fun s => s.RIP = 0x117e02) (andR64R64Effect 0x117e02 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[323, 325]
    (.letOp (n := 329) (.out 0x117e05 (orR64R64Effect 0x117e05 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 15] []) (.reg (.gpr 0))) #v[327, 272]
    (.letOp (n := 330) (.exec 0x117e05 (fun s => s.RIP = 0x117e05) (orR64R64Effect 0x117e05 0 15) (Reg.operands [.gpr 0, .gpr 15] [])) #v[327, 272]
    (.letOp (n := 331) (.out 0x117e08 (movR64Imm64Effect 0x117e08 1 0x1000003d1) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 332) (.exec 0x117e08 (fun s => s.RIP = 0x117e08) (movR64Imm64Effect 0x117e08 1 0x1000003d1) (Reg.operands [] [])) #v[]
    (.letOp (n := 333) (.out 0x117e12 (mulR64Effect 0x117e12 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[331, 329]
    (.letOp (n := 334) (.out 0x117e12 (mulR64Effect 0x117e12 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[331, 329]
    (.letOp (n := 335) (.exec 0x117e12 (fun s => s.RIP = 0x117e12) (mulR64Effect 0x117e12 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[331, 329]
    (.letOp (n := 336) (.out 0x117e15 (movR64R64Effect 0x117e15 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[334]
    (.letOp (n := 337) (.exec 0x117e15 (fun s => s.RIP = 0x117e15) (movR64R64Effect 0x117e15 8 2) (Reg.operands [.gpr 2] [])) #v[334]
    (.letOp (n := 338) (.out 0x117e18 (movR64R64Effect 0x117e18 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[333]
    (.letOp (n := 339) (.exec 0x117e18 (fun s => s.RIP = 0x117e18) (movR64R64Effect 0x117e18 5 0) (Reg.operands [.gpr 0] [])) #v[333]
    (.letOp (n := 340) (.out 0x117e1b (addR64M64Effect 0x117e1b 5 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 4] []) (.reg (.gpr 5))) #v[338, 4]
    (.letOp (n := 341) (.out 0x117e1b (addR64M64Effect 0x117e1b 5 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 4] []) (.flag .CF)) #v[338, 4]
    (.letOp (n := 342) (.exec 0x117e1b (LoadPre 0x117e1b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x117e1b + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x117e1b 5 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[338, 4]
    (.letOp (n := 343) (.out 0x117e23 (atFlags StatusFlags.CF (adcR64M64Effect 0x117e23 8 (.sib 4 none 0 (.d8 0x78)))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 8))) #v[336, 4, 341]
    (.letOp (n := 344) (.exec 0x117e23 (LoadPre 0x117e23 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x117e23 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x117e23 8 (.sib 4 none 0 (.d8 0x78)))) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[336, 4, 341]
    (.letOp (n := 345) (.out 0x117e28 (shldR64R64Effect 0x117e28 5 8 5 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[343, 340]
    (.letOp (n := 346) (.exec 0x117e28 (fun s => s.RIP = 0x117e28) (shldR64R64Effect 0x117e28 5 8 5 12) (Reg.operands [.gpr 8, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[343, 340]
    (.letOp (n := 347) (.out 0x117e2d (movR64R64Effect 0x117e2d 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[294]
    (.letOp (n := 348) (.exec 0x117e2d (fun s => s.RIP = 0x117e2d) (movR64R64Effect 0x117e2d 0 7) (Reg.operands [.gpr 7] [])) #v[294]
    (.letOp (n := 349) (.out 0x117e30 (mulM64Effect 0x117e30 5 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[347, 4]
    (.letOp (n := 350) (.out 0x117e30 (mulM64Effect 0x117e30 5 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[347, 4]
    (.letOp (n := 351) (.exec 0x117e30 (LoadPre 0x117e30 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x117e30 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x117e30 5 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[347, 4]
    (b_l117bde_7))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l117bde_6 : List UInt8 :=
  [0x4D, 0x01, 0xF3, 0x4C, 0x11, 0xD6, 0x4C, 0x01, 0xD8, 0x48, 0x11, 0xD6, 0x48, 0x01, 0xC8, 0x48,
    0x83, 0xD6, 0x00, 0x48, 0x0F, 0xA4, 0xC6, 0x0C, 0x48, 0xC1, 0xE0, 0x04, 0x48, 0xB9, 0xF0, 0xFF,
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x48, 0x21, 0xC8, 0x4C, 0x09, 0xF8, 0x48, 0xB9, 0xD1, 0x03,
    0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE1, 0x49, 0x89, 0xD0, 0x48, 0x89, 0xC5, 0x48,
    0x03, 0xAC, 0x24, 0x98, 0x00, 0x00, 0x00, 0x4C, 0x13, 0x44, 0x24, 0x78, 0x49, 0x0F, 0xA4, 0xE8,
    0x0C, 0x48, 0x89, 0xF8, 0x48, 0xF7, 0x64, 0x24, 0x60] ++ bytes_l117bde_7

theorem code_l117bde_6 : ∀ x ∈ codeRange 0x117ddc bytes_l117bde_6, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x17ddc 89 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l117bde_7

def b_l117bde_5 : Block Op Label signature Reg.count 262 :=
  .letOp (n := 262) (.exec 0x117d83 (StorePre 0x117d83 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x117d83 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x117d83 0 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[258, 4]
    (.letOp (n := 263) (.out 0x117d8b (movR64M64Effect 0x117d8b 0 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 264) (.exec 0x117d8b (LoadPre 0x117d8b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x117d8b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117d8b 0 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 265) (.out 0x117d90 (mulM64Effect 0x117d90 8 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[263, 4]
    (.letOp (n := 266) (.out 0x117d90 (mulM64Effect 0x117d90 8 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[263, 4]
    (.letOp (n := 267) (.exec 0x117d90 (LoadPre 0x117d90 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x117d90 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x117d90 8 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[263, 4]
    (.letOp (n := 268) (.out 0x117d98 (movR64R64Effect 0x117d98 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[265]
    (.letOp (n := 269) (.exec 0x117d98 (fun s => s.RIP = 0x117d98) (movR64R64Effect 0x117d98 8 0) (Reg.operands [.gpr 0] [])) #v[265]
    (.letOp (n := 270) (.out 0x117d9b (movR64R64Effect 0x117d9b 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[266]
    (.letOp (n := 271) (.exec 0x117d9b (fun s => s.RIP = 0x117d9b) (movR64R64Effect 0x117d9b 9 2) (Reg.operands [.gpr 2] [])) #v[266]
    (.letOp (n := 272) (.out 0x117d9e (andR32Imm8Effect 0x117d9e 4 15 0xf) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15] []) (.reg (.gpr 15))) #v[254]
    (.letOp (n := 273) (.exec 0x117d9e (fun s => s.RIP = 0x117d9e) (andR32Imm8Effect 0x117d9e 4 15 0xf) (Reg.operands [.gpr 15] [])) #v[254]
    (.letOp (n := 274) (.out 0x117da2 (movR64M64Effect 0x117da2 0 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 275) (.exec 0x117da2 (LoadPre 0x117da2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x117da2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117da2 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 276) (.out 0x117da7 (mulR64Effect 0x117da7 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[182, 274]
    (.letOp (n := 277) (.out 0x117da7 (mulR64Effect 0x117da7 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[182, 274]
    (.letOp (n := 278) (.exec 0x117da7 (fun s => s.RIP = 0x117da7) (mulR64Effect 0x117da7 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[182, 274]
    (.letOp (n := 279) (.out 0x117daa (movR64R64Effect 0x117daa 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[277]
    (.letOp (n := 280) (.exec 0x117daa (fun s => s.RIP = 0x117daa) (movR64R64Effect 0x117daa 6 2) (Reg.operands [.gpr 2] [])) #v[277]
    (.letOp (n := 281) (.out 0x117dad (movR64R64Effect 0x117dad 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[276]
    (.letOp (n := 282) (.exec 0x117dad (fun s => s.RIP = 0x117dad) (movR64R64Effect 0x117dad 11 0) (Reg.operands [.gpr 0] [])) #v[276]
    (.letOp (n := 283) (.out 0x117db0 (movR64M64Effect 0x117db0 0 (.sib 4 none 0 (.d32 0x108))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 284) (.exec 0x117db0 (LoadPre 0x117db0 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x117db0 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x117db0 0 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 285) (.out 0x117db8 (movR64M64Effect 0x117db8 13 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 286) (.exec 0x117db8 (LoadPre 0x117db8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x117db8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117db8 13 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 287) (.out 0x117dbd (mulR64Effect 0x117dbd 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[285, 283]
    (.letOp (n := 288) (.out 0x117dbd (mulR64Effect 0x117dbd 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[285, 283]
    (.letOp (n := 289) (.exec 0x117dbd (fun s => s.RIP = 0x117dbd) (mulR64Effect 0x117dbd 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[285, 283]
    (.letOp (n := 290) (.out 0x117dc0 (movR64R64Effect 0x117dc0 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[288]
    (.letOp (n := 291) (.exec 0x117dc0 (fun s => s.RIP = 0x117dc0) (movR64R64Effect 0x117dc0 10 2) (Reg.operands [.gpr 2] [])) #v[288]
    (.letOp (n := 292) (.out 0x117dc3 (movR64R64Effect 0x117dc3 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[287]
    (.letOp (n := 293) (.exec 0x117dc3 (fun s => s.RIP = 0x117dc3) (movR64R64Effect 0x117dc3 14 0) (Reg.operands [.gpr 0] [])) #v[287]
    (.letOp (n := 294) (.out 0x117dc6 (movR64M64Effect 0x117dc6 7 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 295) (.exec 0x117dc6 (LoadPre 0x117dc6 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x117dc6 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x117dc6 7 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 296) (.out 0x117dce (movR64R64Effect 0x117dce 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[294]
    (.letOp (n := 297) (.exec 0x117dce (fun s => s.RIP = 0x117dce) (movR64R64Effect 0x117dce 0 7) (Reg.operands [.gpr 7] [])) #v[294]
    (.letOp (n := 298) (.out 0x117dd1 (mulM64Effect 0x117dd1 5 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[296, 4]
    (.letOp (n := 299) (.out 0x117dd1 (mulM64Effect 0x117dd1 5 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[296, 4]
    (.letOp (n := 300) (.exec 0x117dd1 (LoadPre 0x117dd1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x117dd1 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x117dd1 5 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[296, 4]
    (.letOp (n := 301) (.out 0x117dd6 (addR64R64Effect 0x117dd6 11 8) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 8] []) (.reg (.gpr 11))) #v[281, 268]
    (.letOp (n := 302) (.out 0x117dd6 (addR64R64Effect 0x117dd6 11 8) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 8] []) (.flag .CF)) #v[281, 268]
    (.letOp (n := 303) (.exec 0x117dd6 (fun s => s.RIP = 0x117dd6) (addR64R64Effect 0x117dd6 11 8) (Reg.operands [.gpr 11, .gpr 8] [])) #v[281, 268]
    (.letOp (n := 304) (.out 0x117dd9 (atFlags StatusFlags.CF (adcR64R64Effect 0x117dd9 6 9)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[279, 270, 302]
    (.letOp (n := 305) (.exec 0x117dd9 (fun s => s.RIP = 0x117dd9) (atFlags StatusFlags.CF (adcR64R64Effect 0x117dd9 6 9)) (Reg.operands [.gpr 6, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[279, 270, 302]
    (b_l117bde_6))))))))))))))))))))))))))))))))))))))))))))

def bytes_l117bde_5 : List UInt8 :=
  [0x48, 0x89, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x70, 0x48, 0xF7, 0xA4,
    0x24, 0x80, 0x00, 0x00, 0x00, 0x49, 0x89, 0xC0, 0x49, 0x89, 0xD1, 0x41, 0x83, 0xE7, 0x0F, 0x48,
    0x8B, 0x44, 0x24, 0x68, 0x49, 0xF7, 0xE2, 0x48, 0x89, 0xD6, 0x49, 0x89, 0xC3, 0x48, 0x8B, 0x84,
    0x24, 0x08, 0x01, 0x00, 0x00, 0x4C, 0x8B, 0x6C, 0x24, 0x50, 0x49, 0xF7, 0xE5, 0x49, 0x89, 0xD2,
    0x49, 0x89, 0xC6, 0x48, 0x8B, 0xBC, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x48, 0x89, 0xF8, 0x48, 0xF7,
    0x64, 0x24, 0x58, 0x4D, 0x01, 0xC3, 0x4C, 0x11, 0xCE] ++ bytes_l117bde_6

theorem code_l117bde_5 : ∀ x ∈ codeRange 0x117d83 bytes_l117bde_5, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x17d83 89 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l117bde_6

def b_l117bde_4 : Block Op Label signature Reg.count 215 :=
  .letOp (n := 215) (.out 0x117d30 (mulR64Effect 0x117d30 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[209, 213]
    (.letOp (n := 216) (.out 0x117d30 (mulR64Effect 0x117d30 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[209, 213]
    (.letOp (n := 217) (.exec 0x117d30 (fun s => s.RIP = 0x117d30) (mulR64Effect 0x117d30 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[209, 213]
    (.letOp (n := 218) (.out 0x117d33 (addR64R64Effect 0x117d33 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[211, 216]
    (.letOp (n := 219) (.exec 0x117d33 (fun s => s.RIP = 0x117d33) (addR64R64Effect 0x117d33 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[211, 216]
    (.letOp (n := 220) (.out 0x117d36 (addR64M64Effect 0x117d36 3 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 4] []) (.reg (.gpr 3))) #v[178, 4]
    (.letOp (n := 221) (.out 0x117d36 (addR64M64Effect 0x117d36 3 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 4] []) (.flag .CF)) #v[178, 4]
    (.letOp (n := 222) (.exec 0x117d36 (LoadPre 0x117d36 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x117d36 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x117d36 3 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[178, 4]
    (.letOp (n := 223) (.out 0x117d3e (atFlags StatusFlags.CF (adcR64M64Effect 0x117d3e 1 (.sib 4 none 0 (.d8 0x78)))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 1))) #v[176, 4, 221]
    (.letOp (n := 224) (.exec 0x117d3e (LoadPre 0x117d3e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x117d3e + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x117d3e 1 (.sib 4 none 0 (.d8 0x78)))) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[176, 4, 221]
    (.letOp (n := 225) (.out 0x117d43 (addR64R64Effect 0x117d43 3 5) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 5] []) (.reg (.gpr 3))) #v[220, 188]
    (.letOp (n := 226) (.out 0x117d43 (addR64R64Effect 0x117d43 3 5) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 5] []) (.flag .CF)) #v[220, 188]
    (.letOp (n := 227) (.exec 0x117d43 (fun s => s.RIP = 0x117d43) (addR64R64Effect 0x117d43 3 5) (Reg.operands [.gpr 3, .gpr 5] [])) #v[220, 188]
    (.letOp (n := 228) (.out 0x117d46 (atFlags StatusFlags.CF (adcR64M64Effect 0x117d46 1 (.sib 4 none 0 (.d32 0xb8)))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 1))) #v[223, 4, 226]
    (.letOp (n := 229) (.exec 0x117d46 (LoadPre 0x117d46 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x117d46 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x117d46 1 (.sib 4 none 0 (.d32 0xb8)))) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[223, 4, 226]
    (.letOp (n := 230) (.out 0x117d4e (addR64R64Effect 0x117d4e 3 15) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 15] []) (.reg (.gpr 3))) #v[225, 196]
    (.letOp (n := 231) (.out 0x117d4e (addR64R64Effect 0x117d4e 3 15) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 15] []) (.flag .CF)) #v[225, 196]
    (.letOp (n := 232) (.exec 0x117d4e (fun s => s.RIP = 0x117d4e) (addR64R64Effect 0x117d4e 3 15) (Reg.operands [.gpr 3, .gpr 15] [])) #v[225, 196]
    (.letOp (n := 233) (.out 0x117d51 (atFlags StatusFlags.CF (adcR64M64Effect 0x117d51 1 (.sib 4 none 0 (.d32 0xe8)))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 1))) #v[228, 4, 231]
    (.letOp (n := 234) (.exec 0x117d51 (LoadPre 0x117d51 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x117d51 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x117d51 1 (.sib 4 none 0 (.d32 0xe8)))) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[228, 4, 231]
    (.letOp (n := 235) (.out 0x117d59 (addR64R64Effect 0x117d59 3 8) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 8] []) (.reg (.gpr 3))) #v[230, 203]
    (.letOp (n := 236) (.out 0x117d59 (addR64R64Effect 0x117d59 3 8) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 8] []) (.flag .CF)) #v[230, 203]
    (.letOp (n := 237) (.exec 0x117d59 (fun s => s.RIP = 0x117d59) (addR64R64Effect 0x117d59 3 8) (Reg.operands [.gpr 3, .gpr 8] [])) #v[230, 203]
    (.letOp (n := 238) (.out 0x117d5c (atFlags StatusFlags.CF (adcR64R64Effect 0x117d5c 1 14)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[233, 205, 236]
    (.letOp (n := 239) (.exec 0x117d5c (fun s => s.RIP = 0x117d5c) (atFlags StatusFlags.CF (adcR64R64Effect 0x117d5c 1 14)) (Reg.operands [.gpr 1, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[233, 205, 236]
    (.letOp (n := 240) (.out 0x117d5f (addR64R64Effect 0x117d5f 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0] []) (.reg (.gpr 3))) #v[235, 215]
    (.letOp (n := 241) (.out 0x117d5f (addR64R64Effect 0x117d5f 3 0) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 0] []) (.flag .CF)) #v[235, 215]
    (.letOp (n := 242) (.exec 0x117d5f (fun s => s.RIP = 0x117d5f) (addR64R64Effect 0x117d5f 3 0) (Reg.operands [.gpr 3, .gpr 0] [])) #v[235, 215]
    (.letOp (n := 243) (.out 0x117d62 (atFlags StatusFlags.CF (adcR64R64Effect 0x117d62 1 6)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[238, 218, 241]
    (.letOp (n := 244) (.exec 0x117d62 (fun s => s.RIP = 0x117d62) (atFlags StatusFlags.CF (adcR64R64Effect 0x117d62 1 6)) (Reg.operands [.gpr 1, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[238, 218, 241]
    (.letOp (n := 245) (.out 0x117d65 (addR64R64Effect 0x117d65 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 7] []) (.reg (.gpr 3))) #v[240, 160]
    (.letOp (n := 246) (.out 0x117d65 (addR64R64Effect 0x117d65 3 7) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 7] []) (.flag .CF)) #v[240, 160]
    (.letOp (n := 247) (.exec 0x117d65 (fun s => s.RIP = 0x117d65) (addR64R64Effect 0x117d65 3 7) (Reg.operands [.gpr 3, .gpr 7] [])) #v[240, 160]
    (.letOp (n := 248) (.out 0x117d68 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x117d68 1 0x0)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[243, 246]
    (.letOp (n := 249) (.exec 0x117d68 (fun s => s.RIP = 0x117d68) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x117d68 1 0x0)) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[243, 246]
    (.letOp (n := 250) (.out 0x117d6c (shldR64R64Effect 0x117d6c 5 1 3 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[248, 245]
    (.letOp (n := 251) (.exec 0x117d6c (fun s => s.RIP = 0x117d6c) (shldR64R64Effect 0x117d6c 5 1 3 12) (Reg.operands [.gpr 1, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[248, 245]
    (.letOp (n := 252) (.out 0x117d71 (movR64R64Effect 0x117d71 15 3) (EffectPart.reads (.reg (.gpr 15)) [.gpr 3] []) (.reg (.gpr 15))) #v[245]
    (.letOp (n := 253) (.exec 0x117d71 (fun s => s.RIP = 0x117d71) (movR64R64Effect 0x117d71 15 3) (Reg.operands [.gpr 3] [])) #v[245]
    (.letOp (n := 254) (.out 0x117d74 (shrR64Effect 0x117d74 4 15 48) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[252]
    (.letOp (n := 255) (.exec 0x117d74 (fun s => s.RIP = 0x117d74) (shrR64Effect 0x117d74 4 15 48) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[252]
    (.letOp (n := 256) (.out 0x117d78 (movR64R64Effect 0x117d78 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[109]
    (.letOp (n := 257) (.exec 0x117d78 (fun s => s.RIP = 0x117d78) (movR64R64Effect 0x117d78 0 13) (Reg.operands [.gpr 13] [])) #v[109]
    (.letOp (n := 258) (.out 0x117d7b (mulR64Effect 0x117d7b 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[164, 256]
    (.letOp (n := 259) (.out 0x117d7b (mulR64Effect 0x117d7b 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[164, 256]
    (.letOp (n := 260) (.exec 0x117d7b (fun s => s.RIP = 0x117d7b) (mulR64Effect 0x117d7b 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[164, 256]
    (.letOp (n := 261) (.exec 0x117d7e (StorePre 0x117d7e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x117d7e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117d7e 2 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[259, 4]
    (b_l117bde_5)))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l117bde_4 : List UInt8 :=
  [0x48, 0xF7, 0xE2, 0x48, 0x01, 0xD6, 0x48, 0x03, 0x9C, 0x24, 0x98, 0x00, 0x00, 0x00, 0x48, 0x13,
    0x4C, 0x24, 0x78, 0x48, 0x01, 0xEB, 0x48, 0x13, 0x8C, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x4C, 0x01,
    0xFB, 0x48, 0x13, 0x8C, 0x24, 0xE8, 0x00, 0x00, 0x00, 0x4C, 0x01, 0xC3, 0x4C, 0x11, 0xF1, 0x48,
    0x01, 0xC3, 0x48, 0x11, 0xF1, 0x48, 0x01, 0xFB, 0x48, 0x83, 0xD1, 0x00, 0x48, 0x0F, 0xA4, 0xD9,
    0x0C, 0x49, 0x89, 0xDF, 0x49, 0xC1, 0xEF, 0x30, 0x4C, 0x89, 0xE8, 0x49, 0xF7, 0xE1, 0x48, 0x89,
    0x54, 0x24, 0x78] ++ bytes_l117bde_5

theorem code_l117bde_4 : ∀ x ∈ codeRange 0x117d30 bytes_l117bde_4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x17d30 83 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l117bde_5

def b_l117bde_3 : Block Op Label signature Reg.count 173 :=
  .letOp (n := 173) (.out 0x117cda (mulR64Effect 0x117cda 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 0] []) (.reg (.gpr 0))) #v[64, 171]
    (.letOp (n := 174) (.out 0x117cda (mulR64Effect 0x117cda 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3, .gpr 0] []) (.reg (.gpr 2))) #v[64, 171]
    (.letOp (n := 175) (.exec 0x117cda (fun s => s.RIP = 0x117cda) (mulR64Effect 0x117cda 3) (Reg.operands [.gpr 3, .gpr 0] [])) #v[64, 171]
    (.letOp (n := 176) (.out 0x117cdd (movR64R64Effect 0x117cdd 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[174]
    (.letOp (n := 177) (.exec 0x117cdd (fun s => s.RIP = 0x117cdd) (movR64R64Effect 0x117cdd 1 2) (Reg.operands [.gpr 2] [])) #v[174]
    (.letOp (n := 178) (.out 0x117ce0 (movR64R64Effect 0x117ce0 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[173]
    (.letOp (n := 179) (.exec 0x117ce0 (fun s => s.RIP = 0x117ce0) (movR64R64Effect 0x117ce0 3 0) (Reg.operands [.gpr 0] [])) #v[173]
    (.letOp (n := 180) (.out 0x117ce3 (movR64R64Effect 0x117ce3 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[5]
    (.letOp (n := 181) (.exec 0x117ce3 (fun s => s.RIP = 0x117ce3) (movR64R64Effect 0x117ce3 0 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 182) (.out 0x117ce6 (movR64M64Effect 0x117ce6 10 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 183) (.exec 0x117ce6 (LoadPre 0x117ce6 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x117ce6 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x117ce6 10 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 184) (.out 0x117cee (mulR64Effect 0x117cee 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[182, 180]
    (.letOp (n := 185) (.out 0x117cee (mulR64Effect 0x117cee 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[182, 180]
    (.letOp (n := 186) (.exec 0x117cee (fun s => s.RIP = 0x117cee) (mulR64Effect 0x117cee 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[182, 180]
    (.letOp (n := 187) (.exec 0x117cf1 (StorePre 0x117cf1 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x117cf1 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x117cf1 2 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[185, 4]
    (.letOp (n := 188) (.out 0x117cf9 (movR64R64Effect 0x117cf9 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[184]
    (.letOp (n := 189) (.exec 0x117cf9 (fun s => s.RIP = 0x117cf9) (movR64R64Effect 0x117cf9 5 0) (Reg.operands [.gpr 0] [])) #v[184]
    (.letOp (n := 190) (.out 0x117cfc (movR64R64Effect 0x117cfc 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[92]
    (.letOp (n := 191) (.exec 0x117cfc (fun s => s.RIP = 0x117cfc) (movR64R64Effect 0x117cfc 0 14) (Reg.operands [.gpr 14] [])) #v[92]
    (.letOp (n := 192) (.out 0x117cff (mulM64Effect 0x117cff 5 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[190, 4]
    (.letOp (n := 193) (.out 0x117cff (mulM64Effect 0x117cff 5 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[190, 4]
    (.letOp (n := 194) (.exec 0x117cff (LoadPre 0x117cff (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x117cff + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x117cff 5 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[190, 4]
    (.letOp (n := 195) (.exec 0x117d04 (StorePre 0x117d04 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x117d04 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x117d04 2 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[193, 4]
    (.letOp (n := 196) (.out 0x117d0c (movR64R64Effect 0x117d0c 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[192]
    (.letOp (n := 197) (.exec 0x117d0c (fun s => s.RIP = 0x117d0c) (movR64R64Effect 0x117d0c 15 0) (Reg.operands [.gpr 0] [])) #v[192]
    (.letOp (n := 198) (.out 0x117d0f (movR64R64Effect 0x117d0f 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[109]
    (.letOp (n := 199) (.exec 0x117d0f (fun s => s.RIP = 0x117d0f) (movR64R64Effect 0x117d0f 0 13) (Reg.operands [.gpr 13] [])) #v[109]
    (.letOp (n := 200) (.out 0x117d12 (mulR64Effect 0x117d12 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[133, 198]
    (.letOp (n := 201) (.out 0x117d12 (mulR64Effect 0x117d12 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[133, 198]
    (.letOp (n := 202) (.exec 0x117d12 (fun s => s.RIP = 0x117d12) (mulR64Effect 0x117d12 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[133, 198]
    (.letOp (n := 203) (.out 0x117d15 (movR64R64Effect 0x117d15 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[200]
    (.letOp (n := 204) (.exec 0x117d15 (fun s => s.RIP = 0x117d15) (movR64R64Effect 0x117d15 8 0) (Reg.operands [.gpr 0] [])) #v[200]
    (.letOp (n := 205) (.out 0x117d18 (movR64R64Effect 0x117d18 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[201]
    (.letOp (n := 206) (.exec 0x117d18 (fun s => s.RIP = 0x117d18) (movR64R64Effect 0x117d18 14 2) (Reg.operands [.gpr 2] [])) #v[201]
    (.letOp (n := 207) (.out 0x117d1b (shrR64Effect 0x117d1b 4 6 52) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[136]
    (.letOp (n := 208) (.exec 0x117d1b (fun s => s.RIP = 0x117d1b) (shrR64Effect 0x117d1b 4 6 52) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[136]
    (.letOp (n := 209) (.out 0x117d1f (movR64Imm64Effect 0x117d1f 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 210) (.exec 0x117d1f (fun s => s.RIP = 0x117d1f) (movR64Imm64Effect 0x117d1f 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 211) (.out 0x117d29 (imulR64R64Effect 0x117d29 4 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[207, 209]
    (.letOp (n := 212) (.exec 0x117d29 (fun s => s.RIP = 0x117d29) (imulR64R64Effect 0x117d29 4 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[207, 209]
    (.letOp (n := 213) (.out 0x117d2d (movR64R64Effect 0x117d2d 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[140]
    (.letOp (n := 214) (.exec 0x117d2d (fun s => s.RIP = 0x117d2d) (movR64R64Effect 0x117d2d 0 11) (Reg.operands [.gpr 11] [])) #v[140]
    (b_l117bde_4))))))))))))))))))))))))))))))))))))))))))

def bytes_l117bde_3 : List UInt8 :=
  [0x48, 0xF7, 0xE3, 0x48, 0x89, 0xD1, 0x48, 0x89, 0xC3, 0x48, 0x89, 0xE8, 0x4C, 0x8B, 0x94, 0x24,
    0xC8, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE2, 0x48, 0x89, 0x94, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x48,
    0x89, 0xC5, 0x4C, 0x89, 0xF0, 0x48, 0xF7, 0x64, 0x24, 0x50, 0x48, 0x89, 0x94, 0x24, 0xE8, 0x00,
    0x00, 0x00, 0x49, 0x89, 0xC7, 0x4C, 0x89, 0xE8, 0x49, 0xF7, 0xE0, 0x49, 0x89, 0xC0, 0x49, 0x89,
    0xD6, 0x48, 0xC1, 0xEE, 0x34, 0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48,
    0x0F, 0xAF, 0xF2, 0x4C, 0x89, 0xD8] ++ bytes_l117bde_4

theorem code_l117bde_3 : ∀ x ∈ codeRange 0x117cda bytes_l117bde_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x17cda 86 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l117bde_4

def b_l117bde_2 : Block Op Label signature Reg.count 133 :=
  .letOp (n := 133) (.out 0x117c81 (movR64R64Effect 0x117c81 8 11) (EffectPart.reads (.reg (.gpr 8)) [.gpr 11] []) (.reg (.gpr 8))) #v[53]
    (.letOp (n := 134) (.exec 0x117c81 (fun s => s.RIP = 0x117c81) (movR64R64Effect 0x117c81 8 11) (Reg.operands [.gpr 11] [])) #v[53]
    (.letOp (n := 135) (.exec 0x117c84 (StorePre 0x117c84 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x117c84 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117c84 11 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 136) (.out 0x117c89 (movR64R64Effect 0x117c89 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[131]
    (.letOp (n := 137) (.exec 0x117c89 (fun s => s.RIP = 0x117c89) (movR64R64Effect 0x117c89 6 2) (Reg.operands [.gpr 2] [])) #v[131]
    (.letOp (n := 138) (.out 0x117c8c (movR64R64Effect 0x117c8c 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[131]
    (.letOp (n := 139) (.exec 0x117c8c (fun s => s.RIP = 0x117c8c) (movR64R64Effect 0x117c8c 11 2) (Reg.operands [.gpr 2] [])) #v[131]
    (.letOp (n := 140) (.out 0x117c8f (shldR64R64Effect 0x117c8f 5 11 0 12) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[138, 130]
    (.letOp (n := 141) (.exec 0x117c8f (fun s => s.RIP = 0x117c8f) (shldR64R64Effect 0x117c8f 5 11 0 12) (Reg.operands [.gpr 11, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[138, 130]
    (.letOp (n := 142) (.out 0x117c94 (movR64Imm64Effect 0x117c94 2 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 143) (.exec 0x117c94 (fun s => s.RIP = 0x117c94) (movR64Imm64Effect 0x117c94 2 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 144) (.out 0x117c9e (andR64R64Effect 0x117c9e 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[130, 142]
    (.letOp (n := 145) (.exec 0x117c9e (fun s => s.RIP = 0x117c9e) (andR64R64Effect 0x117c9e 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[130, 142]
    (.letOp (n := 146) (.out 0x117ca1 (movR64Imm64Effect 0x117ca1 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 147) (.exec 0x117ca1 (fun s => s.RIP = 0x117ca1) (movR64Imm64Effect 0x117ca1 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 148) (.out 0x117cab (mulR64Effect 0x117cab 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[146, 144]
    (.letOp (n := 149) (.out 0x117cab (mulR64Effect 0x117cab 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[146, 144]
    (.letOp (n := 150) (.exec 0x117cab (fun s => s.RIP = 0x117cab) (mulR64Effect 0x117cab 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[146, 144]
    (.letOp (n := 151) (.out 0x117cae (movR64R64Effect 0x117cae 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[149]
    (.letOp (n := 152) (.exec 0x117cae (fun s => s.RIP = 0x117cae) (movR64R64Effect 0x117cae 7 2) (Reg.operands [.gpr 2] [])) #v[149]
    (.letOp (n := 153) (.out 0x117cb1 (movR64R64Effect 0x117cb1 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[148]
    (.letOp (n := 154) (.exec 0x117cb1 (fun s => s.RIP = 0x117cb1) (movR64R64Effect 0x117cb1 12 0) (Reg.operands [.gpr 0] [])) #v[148]
    (.letOp (n := 155) (.out 0x117cb4 (addR64R64Effect 0x117cb4 12 10) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 10] []) (.reg (.gpr 12))) #v[153, 120]
    (.letOp (n := 156) (.out 0x117cb4 (addR64R64Effect 0x117cb4 12 10) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 10] []) (.flag .CF)) #v[153, 120]
    (.letOp (n := 157) (.exec 0x117cb4 (fun s => s.RIP = 0x117cb4) (addR64R64Effect 0x117cb4 12 10) (Reg.operands [.gpr 12, .gpr 10] [])) #v[153, 120]
    (.letOp (n := 158) (.out 0x117cb7 (atFlags StatusFlags.CF (adcR64R64Effect 0x117cb7 7 9)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[151, 123, 156]
    (.letOp (n := 159) (.exec 0x117cb7 (fun s => s.RIP = 0x117cb7) (atFlags StatusFlags.CF (adcR64R64Effect 0x117cb7 7 9)) (Reg.operands [.gpr 7, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[151, 123, 156]
    (.letOp (n := 160) (.out 0x117cba (shldR64R64Effect 0x117cba 5 7 12 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[158, 155]
    (.letOp (n := 161) (.exec 0x117cba (fun s => s.RIP = 0x117cba) (shldR64R64Effect 0x117cba 5 7 12 12) (Reg.operands [.gpr 7, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[158, 155]
    (.letOp (n := 162) (.out 0x117cbf (movR64R64Effect 0x117cbf 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[125]
    (.letOp (n := 163) (.exec 0x117cbf (fun s => s.RIP = 0x117cbf) (movR64R64Effect 0x117cbf 0 1) (Reg.operands [.gpr 1] [])) #v[125]
    (.letOp (n := 164) (.out 0x117cc2 (movR64M64Effect 0x117cc2 9 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 165) (.exec 0x117cc2 (LoadPre 0x117cc2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x117cc2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117cc2 9 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 166) (.out 0x117cc7 (mulR64Effect 0x117cc7 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[164, 162]
    (.letOp (n := 167) (.out 0x117cc7 (mulR64Effect 0x117cc7 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[164, 162]
    (.letOp (n := 168) (.exec 0x117cc7 (fun s => s.RIP = 0x117cc7) (mulR64Effect 0x117cc7 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[164, 162]
    (.letOp (n := 169) (.exec 0x117cca (StorePre 0x117cca 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x117cca + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117cca 2 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[167, 4]
    (.letOp (n := 170) (.exec 0x117ccf (StorePre 0x117ccf 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x117ccf + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x117ccf 0 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[166, 4]
    (.letOp (n := 171) (.out 0x117cd7 (movR64R64Effect 0x117cd7 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[15]
    (.letOp (n := 172) (.exec 0x117cd7 (fun s => s.RIP = 0x117cd7) (movR64R64Effect 0x117cd7 0 15) (Reg.operands [.gpr 15] [])) #v[15]
    (b_l117bde_3))))))))))))))))))))))))))))))))))))))))

def bytes_l117bde_2 : List UInt8 :=
  [0x4D, 0x89, 0xD8, 0x4C, 0x89, 0x5C, 0x24, 0x58, 0x48, 0x89, 0xD6, 0x49, 0x89, 0xD3, 0x49, 0x0F,
    0xA4, 0xC3, 0x0C, 0x48, 0xBA, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48, 0x21, 0xD0,
    0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x48, 0x89, 0xD7,
    0x49, 0x89, 0xC4, 0x4D, 0x01, 0xD4, 0x4C, 0x11, 0xCF, 0x4C, 0x0F, 0xA4, 0xE7, 0x0C, 0x48, 0x89,
    0xC8, 0x4C, 0x8B, 0x4C, 0x24, 0x60, 0x49, 0xF7, 0xE1, 0x48, 0x89, 0x54, 0x24, 0x78, 0x48, 0x89,
    0x84, 0x24, 0x98, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF8] ++ bytes_l117bde_3

theorem code_l117bde_2 : ∀ x ∈ codeRange 0x117c81 bytes_l117bde_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x17c81 89 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l117bde_3

def b_l117bde_1 : Block Op Label signature Reg.count 90 :=
  .letOp (n := 90) (.out 0x117c39 (atFlags StatusFlags.CF (adcR64R64Effect 0x117c39 7 1)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[83, 72, 88]
    (.letOp (n := 91) (.exec 0x117c39 (fun s => s.RIP = 0x117c39) (atFlags StatusFlags.CF (adcR64R64Effect 0x117c39 7 1)) (Reg.operands [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[83, 72, 88]
    (.letOp (n := 92) (.out 0x117c3c (movR64R64Effect 0x117c3c 14 13) (EffectPart.reads (.reg (.gpr 14)) [.gpr 13] []) (.reg (.gpr 14))) #v[13]
    (.letOp (n := 93) (.exec 0x117c3c (fun s => s.RIP = 0x117c3c) (movR64R64Effect 0x117c3c 14 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 94) (.exec 0x117c3f (StorePre 0x117c3f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x117c3f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x117c3f 13 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[13, 4]
    (.letOp (n := 95) (.out 0x117c47 (movR64R64Effect 0x117c47 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[13]
    (.letOp (n := 96) (.exec 0x117c47 (fun s => s.RIP = 0x117c47) (movR64R64Effect 0x117c47 0 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 97) (.out 0x117c4a (mulR64Effect 0x117c4a 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[58, 95]
    (.letOp (n := 98) (.out 0x117c4a (mulR64Effect 0x117c4a 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[58, 95]
    (.letOp (n := 99) (.exec 0x117c4a (fun s => s.RIP = 0x117c4a) (mulR64Effect 0x117c4a 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[58, 95]
    (.letOp (n := 100) (.out 0x117c4d (movR64R64Effect 0x117c4d 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[98]
    (.letOp (n := 101) (.exec 0x117c4d (fun s => s.RIP = 0x117c4d) (movR64R64Effect 0x117c4d 1 2) (Reg.operands [.gpr 2] [])) #v[98]
    (.letOp (n := 102) (.out 0x117c50 (movR64R64Effect 0x117c50 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[97]
    (.letOp (n := 103) (.exec 0x117c50 (fun s => s.RIP = 0x117c50) (movR64R64Effect 0x117c50 6 0) (Reg.operands [.gpr 0] [])) #v[97]
    (.letOp (n := 104) (.out 0x117c53 (addR64R64Effect 0x117c53 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 8] []) (.reg (.gpr 6))) #v[102, 87]
    (.letOp (n := 105) (.out 0x117c53 (addR64R64Effect 0x117c53 6 8) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 8] []) (.flag .CF)) #v[102, 87]
    (.letOp (n := 106) (.exec 0x117c53 (fun s => s.RIP = 0x117c53) (addR64R64Effect 0x117c53 6 8) (Reg.operands [.gpr 6, .gpr 8] [])) #v[102, 87]
    (.letOp (n := 107) (.out 0x117c56 (atFlags StatusFlags.CF (adcR64R64Effect 0x117c56 1 7)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[100, 90, 105]
    (.letOp (n := 108) (.exec 0x117c56 (fun s => s.RIP = 0x117c56) (atFlags StatusFlags.CF (adcR64R64Effect 0x117c56 1 7)) (Reg.operands [.gpr 1, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[100, 90, 105]
    (.letOp (n := 109) (.out 0x117c59 (movR64M64Effect 0x117c59 13 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 110) (.exec 0x117c59 (LoadPre 0x117c59 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x117c59 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x117c59 13 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 111) (.out 0x117c61 (movR64R64Effect 0x117c61 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[109]
    (.letOp (n := 112) (.exec 0x117c61 (fun s => s.RIP = 0x117c61) (movR64R64Effect 0x117c61 0 13) (Reg.operands [.gpr 13] [])) #v[109]
    (.letOp (n := 113) (.out 0x117c64 (mulR64Effect 0x117c64 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[55, 111]
    (.letOp (n := 114) (.out 0x117c64 (mulR64Effect 0x117c64 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[55, 111]
    (.letOp (n := 115) (.exec 0x117c64 (fun s => s.RIP = 0x117c64) (mulR64Effect 0x117c64 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[55, 111]
    (.letOp (n := 116) (.out 0x117c67 (movR64R64Effect 0x117c67 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[114]
    (.letOp (n := 117) (.exec 0x117c67 (fun s => s.RIP = 0x117c67) (movR64R64Effect 0x117c67 9 2) (Reg.operands [.gpr 2] [])) #v[114]
    (.letOp (n := 118) (.out 0x117c6a (movR64R64Effect 0x117c6a 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[113]
    (.letOp (n := 119) (.exec 0x117c6a (fun s => s.RIP = 0x117c6a) (movR64R64Effect 0x117c6a 10 0) (Reg.operands [.gpr 0] [])) #v[113]
    (.letOp (n := 120) (.out 0x117c6d (addR64R64Effect 0x117c6d 10 6) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 6] []) (.reg (.gpr 10))) #v[118, 104]
    (.letOp (n := 121) (.out 0x117c6d (addR64R64Effect 0x117c6d 10 6) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 6] []) (.flag .CF)) #v[118, 104]
    (.letOp (n := 122) (.exec 0x117c6d (fun s => s.RIP = 0x117c6d) (addR64R64Effect 0x117c6d 10 6) (Reg.operands [.gpr 10, .gpr 6] [])) #v[118, 104]
    (.letOp (n := 123) (.out 0x117c70 (atFlags StatusFlags.CF (adcR64R64Effect 0x117c70 9 1)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[116, 107, 121]
    (.letOp (n := 124) (.exec 0x117c70 (fun s => s.RIP = 0x117c70) (atFlags StatusFlags.CF (adcR64R64Effect 0x117c70 9 1)) (Reg.operands [.gpr 9, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[116, 107, 121]
    (.letOp (n := 125) (.out 0x117c73 (movR64R64Effect 0x117c73 1 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 12] []) (.reg (.gpr 1))) #v[12]
    (.letOp (n := 126) (.exec 0x117c73 (fun s => s.RIP = 0x117c73) (movR64R64Effect 0x117c73 1 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 127) (.exec 0x117c76 (StorePre 0x117c76 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x117c76 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117c76 12 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[12, 4]
    (.letOp (n := 128) (.out 0x117c7b (movR64R64Effect 0x117c7b 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[12]
    (.letOp (n := 129) (.exec 0x117c7b (fun s => s.RIP = 0x117c7b) (movR64R64Effect 0x117c7b 0 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 130) (.out 0x117c7e (mulR64Effect 0x117c7e 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[53, 128]
    (.letOp (n := 131) (.out 0x117c7e (mulR64Effect 0x117c7e 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[53, 128]
    (.letOp (n := 132) (.exec 0x117c7e (fun s => s.RIP = 0x117c7e) (mulR64Effect 0x117c7e 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[53, 128]
    (b_l117bde_2)))))))))))))))))))))))))))))))))))))))))))

def bytes_l117bde_1 : List UInt8 :=
  [0x48, 0x11, 0xCF, 0x4D, 0x89, 0xEE, 0x4C, 0x89, 0xAC, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x4C, 0x89,
    0xE8, 0x49, 0xF7, 0xE2, 0x48, 0x89, 0xD1, 0x48, 0x89, 0xC6, 0x4C, 0x01, 0xC6, 0x48, 0x11, 0xF9,
    0x4C, 0x8B, 0xAC, 0x24, 0x88, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xE8, 0x49, 0xF7, 0xE1, 0x49, 0x89,
    0xD1, 0x49, 0x89, 0xC2, 0x49, 0x01, 0xF2, 0x49, 0x11, 0xC9, 0x4C, 0x89, 0xE1, 0x4C, 0x89, 0x64,
    0x24, 0x70, 0x4C, 0x89, 0xE0, 0x49, 0xF7, 0xE3] ++ bytes_l117bde_2

theorem code_l117bde_1 : ∀ x ∈ codeRange 0x117c39 bytes_l117bde_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x17c39 72 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l117bde_2

def b_l117bde : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x117bde (movR64M64Effect 0x117bde 11 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 54) (.exec 0x117bde (LoadPre 0x117bde (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x117bde + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117bde 11 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x117be3 (movR64M64Effect 0x117be3 9 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 56) (.exec 0x117be3 (LoadPre 0x117be3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x117be3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117be3 9 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x117be8 (StorePre 0x117be8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x117be8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117be8 9 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 58) (.out 0x117bed (movR64M64Effect 0x117bed 10 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 59) (.exec 0x117bed (LoadPre 0x117bed (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x117bed + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117bed 10 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.exec 0x117bf2 (StorePre 0x117bf2 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x117bf2 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x117bf2 10 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[58, 4]
    (.letOp (n := 61) (.out 0x117bfa (movR64M64Effect 0x117bfa 1 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 62) (.exec 0x117bfa (LoadPre 0x117bfa (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x117bfa + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117bfa 1 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x117bff (StorePre 0x117bff 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x117bff + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117bff 1 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.out 0x117c04 (movR64M64Effect 0x117c04 3 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 65) (.exec 0x117c04 (LoadPre 0x117c04 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x117c04 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x117c04 3 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x117c09 (StorePre 0x117c09 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x117c09 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x117c09 15 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[15, 4]
    (.letOp (n := 67) (.out 0x117c0e (movR64R64Effect 0x117c0e 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[15]
    (.letOp (n := 68) (.exec 0x117c0e (fun s => s.RIP = 0x117c0e) (movR64R64Effect 0x117c0e 0 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 69) (.out 0x117c11 (mulR64Effect 0x117c11 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[61, 67]
    (.letOp (n := 70) (.out 0x117c11 (mulR64Effect 0x117c11 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[61, 67]
    (.letOp (n := 71) (.exec 0x117c11 (fun s => s.RIP = 0x117c11) (mulR64Effect 0x117c11 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[61, 67]
    (.letOp (n := 72) (.out 0x117c14 (movR64R64Effect 0x117c14 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[70]
    (.letOp (n := 73) (.exec 0x117c14 (fun s => s.RIP = 0x117c14) (movR64R64Effect 0x117c14 1 2) (Reg.operands [.gpr 2] [])) #v[70]
    (.letOp (n := 74) (.out 0x117c17 (movR64R64Effect 0x117c17 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[69]
    (.letOp (n := 75) (.exec 0x117c17 (fun s => s.RIP = 0x117c17) (movR64R64Effect 0x117c17 6 0) (Reg.operands [.gpr 0] [])) #v[69]
    (.letOp (n := 76) (.exec 0x117c1a (StorePre 0x117c1a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x117c1a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x117c1a 5 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[5, 4]
    (.letOp (n := 77) (.out 0x117c22 (movR64R64Effect 0x117c22 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[5]
    (.letOp (n := 78) (.exec 0x117c22 (fun s => s.RIP = 0x117c22) (movR64R64Effect 0x117c22 0 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 79) (.out 0x117c25 (mulR64Effect 0x117c25 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 0] []) (.reg (.gpr 0))) #v[64, 77]
    (.letOp (n := 80) (.out 0x117c25 (mulR64Effect 0x117c25 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3, .gpr 0] []) (.reg (.gpr 2))) #v[64, 77]
    (.letOp (n := 81) (.exec 0x117c25 (fun s => s.RIP = 0x117c25) (mulR64Effect 0x117c25 3) (Reg.operands [.gpr 3, .gpr 0] [])) #v[64, 77]
    (.letOp (n := 82) (.exec 0x117c28 (StorePre 0x117c28 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x117c28 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x117c28 3 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 83) (.out 0x117c30 (movR64R64Effect 0x117c30 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[80]
    (.letOp (n := 84) (.exec 0x117c30 (fun s => s.RIP = 0x117c30) (movR64R64Effect 0x117c30 7 2) (Reg.operands [.gpr 2] [])) #v[80]
    (.letOp (n := 85) (.out 0x117c33 (movR64R64Effect 0x117c33 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[79]
    (.letOp (n := 86) (.exec 0x117c33 (fun s => s.RIP = 0x117c33) (movR64R64Effect 0x117c33 8 0) (Reg.operands [.gpr 0] [])) #v[79]
    (.letOp (n := 87) (.out 0x117c36 (addR64R64Effect 0x117c36 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6] []) (.reg (.gpr 8))) #v[85, 74]
    (.letOp (n := 88) (.out 0x117c36 (addR64R64Effect 0x117c36 8 6) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 6] []) (.flag .CF)) #v[85, 74]
    (.letOp (n := 89) (.exec 0x117c36 (fun s => s.RIP = 0x117c36) (addR64R64Effect 0x117c36 8 6) (Reg.operands [.gpr 8, .gpr 6] [])) #v[85, 74]
    (b_l117bde_1)))))))))))))))))))))))))))))))))))))

def bytes_l117bde : List UInt8 :=
  [0x4C, 0x8B, 0x5C, 0x24, 0x48, 0x4C, 0x8B, 0x4C, 0x24, 0x40, 0x4C, 0x89, 0x4C, 0x24, 0x50, 0x4C,
    0x8B, 0x54, 0x24, 0x38, 0x4C, 0x89, 0x94, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x4C, 0x24,
    0x28, 0x48, 0x89, 0x4C, 0x24, 0x60, 0x48, 0x8B, 0x5C, 0x24, 0x30, 0x4C, 0x89, 0x7C, 0x24, 0x68,
    0x4C, 0x89, 0xF8, 0x48, 0xF7, 0xE1, 0x48, 0x89, 0xD1, 0x48, 0x89, 0xC6, 0x48, 0x89, 0xAC, 0x24,
    0x08, 0x01, 0x00, 0x00, 0x48, 0x89, 0xE8, 0x48, 0xF7, 0xE3, 0x48, 0x89, 0x9C, 0x24, 0x80, 0x00,
    0x00, 0x00, 0x48, 0x89, 0xD7, 0x49, 0x89, 0xC0, 0x49, 0x01, 0xF0] ++ bytes_l117bde_1

theorem code_l117bde : ∀ x ∈ codeRange 0x117bde bytes_l117bde, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x17bde 91 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l117bde_1

@[cfg_block] def b_l118040 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x118040 (movR64R64Effect 0x118040 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 54) (.exec 0x118040 (fun s => s.RIP = 0x118040) (movR64R64Effect 0x118040 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 55) (.out 0x118043 (movR64R64Effect 0x118043 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 56) (.exec 0x118043 (fun s => s.RIP = 0x118043) (movR64R64Effect 0x118043 6 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 57) (.out 0x118046 (callEffect (fun _ => 0x1145f0) 0x11804b) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x118046 (PushPre 0x118046 5) (callEffect (fun _ => 0x1145f0) 0x11804b) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x11804b⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ { target := .l11804b, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l118040 : List UInt8 :=
  [0x4C, 0x89, 0xF7, 0x4C, 0x89, 0xFE, 0xE8, 0xA5, 0xC5, 0xFF, 0xFF]

theorem code_l118040 : ∀ x ∈ codeRange 0x118040 bytes_l118040, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x18040 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11804b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11804b (movR64M64Effect 0x11804b 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x11804b (LoadPre 0x11804b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x11804b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11804b 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x118050 (StorePre 0x118050 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x118050 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x118050 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x118055 (movR64M64Effect 0x118055 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x118055 (LoadPre 0x118055 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x118055 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x118055 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x11805a (StorePre 0x11805a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11805a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11805a 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x11805f (movR64M64Effect 0x11805f 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x11805f (LoadPre 0x11805f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11805f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11805f 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x118064 (StorePre 0x118064 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x118064 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x118064 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x118069 (movR64M64Effect 0x118069 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x118069 (LoadPre 0x118069 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x118069 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x118069 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x11806e (movR64M64Effect 0x11806e 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x11806e (LoadPre 0x11806e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11806e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11806e 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x118073 (StorePre 0x118073 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x118073 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x118073 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x118078 (StorePre 0x118078 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x118078 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x118078 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x11807c (decR64Effect 0x11807c 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[3]
    (.letOp (n := 69) (.out 0x11807c (decR64Effect 0x11807c 3) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.flag .ZF)) #v[3]
    (.letOp (n := 70) (.exec 0x11807c (fun s => s.RIP = 0x11807c) (decR64Effect 0x11807c 3) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3]
    (.letOp (n := 71) (.pure (condOp 5)) #v[69]
    (.terminate (.condBr (Fin.last 71) ⟨.l118040, RegMap.args [(0, 62), (1, 64), (3, 68), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (19, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩ ⟨.l118081, RegMap.args [(0, 62), (1, 64), (3, 68), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (19, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩))))))))))))))))))))

def bytes_l11804b : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0xFF, 0xCB, 0x75, 0xBF]

theorem code_l11804b : ∀ x ∈ codeRange 0x11804b bytes_l11804b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1804b 54 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

def b_l118081_11 : Block Op Label signature Reg.count 537 :=
  .letOp (n := 537) (.out 0x11846b (shldR64R64Effect 0x11846b 5 2 12 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[535, 532]
    (.letOp (n := 538) (.exec 0x11846b (fun s => s.RIP = 0x11846b) (shldR64R64Effect 0x11846b 5 2 12 12) (Reg.operands [.gpr 2, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[535, 532]
    (.letOp (n := 539) (.out 0x118470 (andR64R64Effect 0x118470 12 10) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 10] []) (.reg (.gpr 12))) #v[532, 406]
    (.letOp (n := 540) (.exec 0x118470 (fun s => s.RIP = 0x118470) (andR64R64Effect 0x118470 12 10) (Reg.operands [.gpr 12, .gpr 10] [])) #v[532, 406]
    (.letOp (n := 541) (.out 0x118473 (movR64Imm64Effect 0x118473 0 0xffffffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 542) (.exec 0x118473 (fun s => s.RIP = 0x118473) (movR64Imm64Effect 0x118473 0 0xffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 543) (.out 0x11847d (andR64R64Effect 0x11847d 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0] []) (.reg (.gpr 9))) #v[238, 541]
    (.letOp (n := 544) (.exec 0x11847d (fun s => s.RIP = 0x11847d) (andR64R64Effect 0x11847d 9 0) (Reg.operands [.gpr 9, .gpr 0] [])) #v[238, 541]
    (.letOp (n := 545) (.out 0x118480 (addR64R64Effect 0x118480 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2] []) (.reg (.gpr 9))) #v[543, 537]
    (.letOp (n := 546) (.exec 0x118480 (fun s => s.RIP = 0x118480) (addR64R64Effect 0x118480 9 2) (Reg.operands [.gpr 9, .gpr 2] [])) #v[543, 537]
    (.letOp (n := 547) (.out 0x118483 (movR64M64Effect 0x118483 0 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 548) (.exec 0x118483 (LoadPre 0x118483 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x118483 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x118483 0 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 549) (.exec 0x11848b (StorePre 0x11848b 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x11848b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11848b 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[547, 4]
    (.letOp (n := 550) (.exec 0x11848f (StorePre 0x11848f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x11848f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11848f 13 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[457, 4]
    (.letOp (n := 551) (.exec 0x118497 (StorePre 0x118497 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x118497 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x118497 13 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[457, 4]
    (.letOp (n := 552) (.exec 0x11849c (StorePre 0x11849c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11849c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11849c 5 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[523, 4]
    (.letOp (n := 553) (.exec 0x1184a1 (StorePre 0x1184a1 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x1184a1 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1184a1 12 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[539, 4]
    (.letOp (n := 554) (.exec 0x1184a9 (StorePre 0x1184a9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1184a9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1184a9 12 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[539, 4]
    (.letOp (n := 555) (.exec 0x1184ae (StorePre 0x1184ae 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x1184ae + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1184ae 9 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[545, 4]
    (.letOp (n := 556) (.exec 0x1184b6 (StorePre 0x1184b6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1184b6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1184b6 9 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[545, 4]
    (.letOp (n := 557) (.out 0x1184bb (movR32Imm32Effect 0x1184bb 6 15 0x58) (EffectPart.reads (.reg (.gpr 15)) [] []) (.reg (.gpr 15))) #v[]
    (.letOp (n := 558) (.exec 0x1184bb (fun s => s.RIP = 0x1184bb) (movR32Imm32Effect 0x1184bb 6 15 0x58) (Reg.operands [] [])) #v[]
    (.letOp (n := 559) (.out 0x1184c1 (leaR64Effect 0x1184c1 3 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 560) (.exec 0x1184c1 (fun s => s.RIP = 0x1184c1) (leaR64Effect 0x1184c1 3 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 561) (.out 0x1184c6 (movR64R64Effect 0x1184c6 14 4) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 562) (.exec 0x1184c6 (fun s => s.RIP = 0x1184c6) (movR64R64Effect 0x1184c6 14 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 563) (.exec 0x1184c9 (fun s => s.RIP = 0x1184c9) (fun _ => nopEffect 0x1184c9 7) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l1184d0, RegMap.args [(0, 547), (1, 430), (2, 537), (3, 559), (4, 4), (5, 523), (6, 516), (7, 489), (8, 514), (9, 545), (10, 406), (11, 455), (12, 539), (13, 457), (14, 561), (15, 557), (22, 22), (39, 39), (50, 50), (51, 51)] 564⟩))))))))))))))))))))))))))))

def bytes_l118081_11 : List UInt8 :=
  [0x4C, 0x0F, 0xA4, 0xE2, 0x0C, 0x4D, 0x21, 0xD4, 0x48, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0x00, 0x00, 0x49, 0x21, 0xC1, 0x49, 0x01, 0xD1, 0x48, 0x8B, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00,
    0x48, 0x89, 0x04, 0x24, 0x4C, 0x89, 0xAC, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x4C, 0x89, 0x6C, 0x24,
    0x08, 0x48, 0x89, 0x6C, 0x24, 0x10, 0x4C, 0x89, 0xA4, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x4C, 0x89,
    0x64, 0x24, 0x18, 0x4C, 0x89, 0x8C, 0x24, 0xE8, 0x00, 0x00, 0x00, 0x4C, 0x89, 0x4C, 0x24, 0x20,
    0x41, 0xBF, 0x58, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x5C, 0x24, 0x28, 0x49, 0x89, 0xE6, 0x0F, 0x1F,
    0x80, 0x00, 0x00, 0x00, 0x00]

theorem code_l118081_11 : ∀ x ∈ codeRange 0x11846b bytes_l118081_11, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1846b 101 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

def b_l118081_10 : Block Op Label signature Reg.count 489 :=
  .letOp (n := 489) (.out 0x118417 (movR64Imm64Effect 0x118417 7 0x1000003d10) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 490) (.exec 0x118417 (fun s => s.RIP = 0x118417) (movR64Imm64Effect 0x118417 7 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 491) (.out 0x118421 (mulR64Effect 0x118421 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[489, 487]
    (.letOp (n := 492) (.out 0x118421 (mulR64Effect 0x118421 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[489, 487]
    (.letOp (n := 493) (.exec 0x118421 (fun s => s.RIP = 0x118421) (mulR64Effect 0x118421 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[489, 487]
    (.letOp (n := 494) (.out 0x118424 (addR64M64Effect 0x118424 5 (.sib 4 none 0 (.d32 0xe0))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 4] []) (.reg (.gpr 5))) #v[446, 4]
    (.letOp (n := 495) (.out 0x118424 (addR64M64Effect 0x118424 5 (.sib 4 none 0 (.d32 0xe0))) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 4] []) (.flag .CF)) #v[446, 4]
    (.letOp (n := 496) (.exec 0x118424 (LoadPre 0x118424 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x118424 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x118424 5 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[446, 4]
    (.letOp (n := 497) (.out 0x11842c (atFlags StatusFlags.CF (adcR64M64Effect 0x11842c 6 (.sib 4 none 0 (.d32 0x118)))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 6))) #v[444, 4, 495]
    (.letOp (n := 498) (.exec 0x11842c (LoadPre 0x11842c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x11842c + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x11842c 6 (.sib 4 none 0 (.d32 0x118)))) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[444, 4, 495]
    (.letOp (n := 499) (.out 0x118434 (addR64R64Effect 0x118434 5 3) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 3] []) (.reg (.gpr 5))) #v[494, 453]
    (.letOp (n := 500) (.out 0x118434 (addR64R64Effect 0x118434 5 3) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 3] []) (.flag .CF)) #v[494, 453]
    (.letOp (n := 501) (.exec 0x118434 (fun s => s.RIP = 0x118434) (addR64R64Effect 0x118434 5 3) (Reg.operands [.gpr 5, .gpr 3] [])) #v[494, 453]
    (.letOp (n := 502) (.out 0x118437 (atFlags StatusFlags.CF (adcR64R64Effect 0x118437 6 11)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[497, 455, 500]
    (.letOp (n := 503) (.exec 0x118437 (fun s => s.RIP = 0x118437) (atFlags StatusFlags.CF (adcR64R64Effect 0x118437 6 11)) (Reg.operands [.gpr 6, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[497, 455, 500]
    (.letOp (n := 504) (.out 0x11843a (addR64R64Effect 0x11843a 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 0] []) (.reg (.gpr 5))) #v[499, 491]
    (.letOp (n := 505) (.out 0x11843a (addR64R64Effect 0x11843a 5 0) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 0] []) (.flag .CF)) #v[499, 491]
    (.letOp (n := 506) (.exec 0x11843a (fun s => s.RIP = 0x11843a) (addR64R64Effect 0x11843a 5 0) (Reg.operands [.gpr 5, .gpr 0] [])) #v[499, 491]
    (.letOp (n := 507) (.out 0x11843d (atFlags StatusFlags.CF (adcR64R64Effect 0x11843d 6 2)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[502, 492, 505]
    (.letOp (n := 508) (.exec 0x11843d (fun s => s.RIP = 0x11843d) (atFlags StatusFlags.CF (adcR64R64Effect 0x11843d 6 2)) (Reg.operands [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[502, 492, 505]
    (.letOp (n := 509) (.out 0x118440 (addR64R64Effect 0x118440 5 1) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 1] []) (.reg (.gpr 5))) #v[504, 430]
    (.letOp (n := 510) (.out 0x118440 (addR64R64Effect 0x118440 5 1) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 1] []) (.flag .CF)) #v[504, 430]
    (.letOp (n := 511) (.exec 0x118440 (fun s => s.RIP = 0x118440) (addR64R64Effect 0x118440 5 1) (Reg.operands [.gpr 5, .gpr 1] [])) #v[504, 430]
    (.letOp (n := 512) (.out 0x118443 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x118443 6 0x0)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[507, 510]
    (.letOp (n := 513) (.exec 0x118443 (fun s => s.RIP = 0x118443) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x118443 6 0x0)) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[507, 510]
    (.letOp (n := 514) (.out 0x118447 (shldR64R64Effect 0x118447 5 8 14 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[483, 480]
    (.letOp (n := 515) (.exec 0x118447 (fun s => s.RIP = 0x118447) (shldR64R64Effect 0x118447 5 8 14 12) (Reg.operands [.gpr 8, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[483, 480]
    (.letOp (n := 516) (.out 0x11844c (shldR64R64Effect 0x11844c 5 6 5 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[512, 509]
    (.letOp (n := 517) (.exec 0x11844c (fun s => s.RIP = 0x11844c) (shldR64R64Effect 0x11844c 5 6 5 12) (Reg.operands [.gpr 6, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[512, 509]
    (.letOp (n := 518) (.out 0x118451 (movR64R64Effect 0x118451 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[514]
    (.letOp (n := 519) (.exec 0x118451 (fun s => s.RIP = 0x118451) (movR64R64Effect 0x118451 0 8) (Reg.operands [.gpr 8] [])) #v[514]
    (.letOp (n := 520) (.out 0x118454 (mulR64Effect 0x118454 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[489, 518]
    (.letOp (n := 521) (.out 0x118454 (mulR64Effect 0x118454 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[489, 518]
    (.letOp (n := 522) (.exec 0x118454 (fun s => s.RIP = 0x118454) (mulR64Effect 0x118454 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[489, 518]
    (.letOp (n := 523) (.out 0x118457 (andR64R64Effect 0x118457 5 10) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 10] []) (.reg (.gpr 5))) #v[509, 406]
    (.letOp (n := 524) (.exec 0x118457 (fun s => s.RIP = 0x118457) (andR64R64Effect 0x118457 5 10) (Reg.operands [.gpr 5, .gpr 10] [])) #v[509, 406]
    (.letOp (n := 525) (.out 0x11845a (andR64R64Effect 0x11845a 12 10) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 10] []) (.reg (.gpr 12))) #v[146, 406]
    (.letOp (n := 526) (.exec 0x11845a (fun s => s.RIP = 0x11845a) (andR64R64Effect 0x11845a 12 10) (Reg.operands [.gpr 12, .gpr 10] [])) #v[146, 406]
    (.letOp (n := 527) (.out 0x11845d (addR64R64Effect 0x11845d 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 0] []) (.reg (.gpr 12))) #v[525, 520]
    (.letOp (n := 528) (.out 0x11845d (addR64R64Effect 0x11845d 12 0) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 0] []) (.flag .CF)) #v[525, 520]
    (.letOp (n := 529) (.exec 0x11845d (fun s => s.RIP = 0x11845d) (addR64R64Effect 0x11845d 12 0) (Reg.operands [.gpr 12, .gpr 0] [])) #v[525, 520]
    (.letOp (n := 530) (.out 0x118460 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x118460 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[521, 528]
    (.letOp (n := 531) (.exec 0x118460 (fun s => s.RIP = 0x118460) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x118460 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[521, 528]
    (.letOp (n := 532) (.out 0x118464 (addR64R64Effect 0x118464 12 6) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 6] []) (.reg (.gpr 12))) #v[527, 516]
    (.letOp (n := 533) (.out 0x118464 (addR64R64Effect 0x118464 12 6) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 6] []) (.flag .CF)) #v[527, 516]
    (.letOp (n := 534) (.exec 0x118464 (fun s => s.RIP = 0x118464) (addR64R64Effect 0x118464 12 6) (Reg.operands [.gpr 12, .gpr 6] [])) #v[527, 516]
    (.letOp (n := 535) (.out 0x118467 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x118467 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[530, 533]
    (.letOp (n := 536) (.exec 0x118467 (fun s => s.RIP = 0x118467) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x118467 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[530, 533]
    (b_l118081_11))))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l118081_10 : List UInt8 :=
  [0x48, 0xBF, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE7, 0x48, 0x03, 0xAC,
    0x24, 0xE0, 0x00, 0x00, 0x00, 0x48, 0x13, 0xB4, 0x24, 0x18, 0x01, 0x00, 0x00, 0x48, 0x01, 0xDD,
    0x4C, 0x11, 0xDE, 0x48, 0x01, 0xC5, 0x48, 0x11, 0xD6, 0x48, 0x01, 0xCD, 0x48, 0x83, 0xD6, 0x00,
    0x4D, 0x0F, 0xA4, 0xF0, 0x0C, 0x48, 0x0F, 0xA4, 0xEE, 0x0C, 0x4C, 0x89, 0xC0, 0x48, 0xF7, 0xE7,
    0x4C, 0x21, 0xD5, 0x4D, 0x21, 0xD4, 0x49, 0x01, 0xC4, 0x48, 0x83, 0xD2, 0x00, 0x49, 0x01, 0xF4,
    0x48, 0x83, 0xD2, 0x00] ++ bytes_l118081_11

theorem code_l118081_10 : ∀ x ∈ codeRange 0x118417 bytes_l118081_10, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x18417 84 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l118081_11

def b_l118081_9 : Block Op Label signature Reg.count 444 :=
  .letOp (n := 444) (.out 0x1183c5 (movR64R64Effect 0x1183c5 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[442]
    (.letOp (n := 445) (.exec 0x1183c5 (fun s => s.RIP = 0x1183c5) (movR64R64Effect 0x1183c5 6 2) (Reg.operands [.gpr 2] [])) #v[442]
    (.letOp (n := 446) (.out 0x1183c8 (movR64R64Effect 0x1183c8 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[441]
    (.letOp (n := 447) (.exec 0x1183c8 (fun s => s.RIP = 0x1183c8) (movR64R64Effect 0x1183c8 5 0) (Reg.operands [.gpr 0] [])) #v[441]
    (.letOp (n := 448) (.out 0x1183cb (movR64M64Effect 0x1183cb 0 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 449) (.exec 0x1183cb (LoadPre 0x1183cb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1183cb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1183cb 0 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 450) (.out 0x1183d0 (mulM64Effect 0x1183d0 8 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[448, 4]
    (.letOp (n := 451) (.out 0x1183d0 (mulM64Effect 0x1183d0 8 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[448, 4]
    (.letOp (n := 452) (.exec 0x1183d0 (LoadPre 0x1183d0 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x1183d0 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x1183d0 8 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[448, 4]
    (.letOp (n := 453) (.out 0x1183d8 (movR64R64Effect 0x1183d8 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[450]
    (.letOp (n := 454) (.exec 0x1183d8 (fun s => s.RIP = 0x1183d8) (movR64R64Effect 0x1183d8 3 0) (Reg.operands [.gpr 0] [])) #v[450]
    (.letOp (n := 455) (.out 0x1183db (movR64R64Effect 0x1183db 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[451]
    (.letOp (n := 456) (.exec 0x1183db (fun s => s.RIP = 0x1183db) (movR64R64Effect 0x1183db 11 2) (Reg.operands [.gpr 2] [])) #v[451]
    (.letOp (n := 457) (.out 0x1183de (andR64R64Effect 0x1183de 13 10) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 10] []) (.reg (.gpr 13))) #v[425, 406]
    (.letOp (n := 458) (.exec 0x1183de (fun s => s.RIP = 0x1183de) (andR64R64Effect 0x1183de 13 10) (Reg.operands [.gpr 13, .gpr 10] [])) #v[425, 406]
    (.letOp (n := 459) (.out 0x1183e1 (movR64M64Effect 0x1183e1 0 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 460) (.exec 0x1183e1 (LoadPre 0x1183e1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1183e1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1183e1 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 461) (.out 0x1183e6 (mulM64Effect 0x1183e6 8 (.sib 4 none 0 (.d32 0xe8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[459, 4]
    (.letOp (n := 462) (.out 0x1183e6 (mulM64Effect 0x1183e6 8 (.sib 4 none 0 (.d32 0xe8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[459, 4]
    (.letOp (n := 463) (.exec 0x1183e6 (LoadPre 0x1183e6 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x1183e6 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x1183e6 8 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[459, 4]
    (.letOp (n := 464) (.out 0x1183ee (movR64R64Effect 0x1183ee 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[462]
    (.letOp (n := 465) (.exec 0x1183ee (fun s => s.RIP = 0x1183ee) (movR64R64Effect 0x1183ee 8 2) (Reg.operands [.gpr 2] [])) #v[462]
    (.letOp (n := 466) (.out 0x1183f1 (movR64R64Effect 0x1183f1 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[461]
    (.letOp (n := 467) (.exec 0x1183f1 (fun s => s.RIP = 0x1183f1) (movR64R64Effect 0x1183f1 15 0) (Reg.operands [.gpr 0] [])) #v[461]
    (.letOp (n := 468) (.out 0x1183f4 (movR64M64Effect 0x1183f4 0 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 469) (.exec 0x1183f4 (LoadPre 0x1183f4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1183f4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1183f4 0 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 470) (.out 0x1183f9 (mulM64Effect 0x1183f9 8 (.sib 4 none 0 (.d32 0x110))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[468, 4]
    (.letOp (n := 471) (.out 0x1183f9 (mulM64Effect 0x1183f9 8 (.sib 4 none 0 (.d32 0x110))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[468, 4]
    (.letOp (n := 472) (.exec 0x1183f9 (LoadPre 0x1183f9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x1183f9 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x1183f9 8 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[468, 4]
    (.letOp (n := 473) (.out 0x118401 (movR64R64Effect 0x118401 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[470]
    (.letOp (n := 474) (.exec 0x118401 (fun s => s.RIP = 0x118401) (movR64R64Effect 0x118401 14 0) (Reg.operands [.gpr 0] [])) #v[470]
    (.letOp (n := 475) (.out 0x118404 (addR64R64Effect 0x118404 14 15) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 15] []) (.reg (.gpr 14))) #v[473, 466]
    (.letOp (n := 476) (.out 0x118404 (addR64R64Effect 0x118404 14 15) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 15] []) (.flag .CF)) #v[473, 466]
    (.letOp (n := 477) (.exec 0x118404 (fun s => s.RIP = 0x118404) (addR64R64Effect 0x118404 14 15) (Reg.operands [.gpr 14, .gpr 15] [])) #v[473, 466]
    (.letOp (n := 478) (.out 0x118407 (atFlags StatusFlags.CF (adcR64R64Effect 0x118407 8 2)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[464, 471, 476]
    (.letOp (n := 479) (.exec 0x118407 (fun s => s.RIP = 0x118407) (atFlags StatusFlags.CF (adcR64R64Effect 0x118407 8 2)) (Reg.operands [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[464, 471, 476]
    (.letOp (n := 480) (.out 0x11840a (addR64R64Effect 0x11840a 14 7) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 7] []) (.reg (.gpr 14))) #v[475, 404]
    (.letOp (n := 481) (.out 0x11840a (addR64R64Effect 0x11840a 14 7) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 7] []) (.flag .CF)) #v[475, 404]
    (.letOp (n := 482) (.exec 0x11840a (fun s => s.RIP = 0x11840a) (addR64R64Effect 0x11840a 14 7) (Reg.operands [.gpr 14, .gpr 7] [])) #v[475, 404]
    (.letOp (n := 483) (.out 0x11840d (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11840d 8 0x0)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[478, 481]
    (.letOp (n := 484) (.exec 0x11840d (fun s => s.RIP = 0x11840d) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11840d 8 0x0)) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[478, 481]
    (.letOp (n := 485) (.out 0x118411 (movR64R64Effect 0x118411 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[480]
    (.letOp (n := 486) (.exec 0x118411 (fun s => s.RIP = 0x118411) (movR64R64Effect 0x118411 0 14) (Reg.operands [.gpr 14] [])) #v[480]
    (.letOp (n := 487) (.out 0x118414 (andR64R64Effect 0x118414 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[485, 406]
    (.letOp (n := 488) (.exec 0x118414 (fun s => s.RIP = 0x118414) (andR64R64Effect 0x118414 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[485, 406]
    (b_l118081_10)))))))))))))))))))))))))))))))))))))))))))))

def bytes_l118081_9 : List UInt8 :=
  [0x48, 0x89, 0xD6, 0x48, 0x89, 0xC5, 0x48, 0x8B, 0x44, 0x24, 0x78, 0x48, 0xF7, 0xA4, 0x24, 0xC8,
    0x00, 0x00, 0x00, 0x48, 0x89, 0xC3, 0x49, 0x89, 0xD3, 0x4D, 0x21, 0xD5, 0x48, 0x8B, 0x44, 0x24,
    0x58, 0x48, 0xF7, 0xA4, 0x24, 0xE8, 0x00, 0x00, 0x00, 0x49, 0x89, 0xD0, 0x49, 0x89, 0xC7, 0x48,
    0x8B, 0x44, 0x24, 0x50, 0x48, 0xF7, 0xA4, 0x24, 0x10, 0x01, 0x00, 0x00, 0x49, 0x89, 0xC6, 0x4D,
    0x01, 0xFE, 0x49, 0x11, 0xD0, 0x49, 0x01, 0xFE, 0x49, 0x83, 0xD0, 0x00, 0x4C, 0x89, 0xF0, 0x4C,
    0x21, 0xD0] ++ bytes_l118081_10

theorem code_l118081_9 : ∀ x ∈ codeRange 0x1183c5 bytes_l118081_9, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x183c5 82 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l118081_10

def b_l118081_8 : Block Op Label signature Reg.count 399 :=
  .letOp (n := 399) (.out 0x118355 (addR64R64Effect 0x118355 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[394, 317]
    (.letOp (n := 400) (.out 0x118355 (addR64R64Effect 0x118355 0 6) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 6] []) (.flag .CF)) #v[394, 317]
    (.letOp (n := 401) (.exec 0x118355 (fun s => s.RIP = 0x118355) (addR64R64Effect 0x118355 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[394, 317]
    (.letOp (n := 402) (.out 0x118358 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x118358 7 0x0)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[397, 400]
    (.letOp (n := 403) (.exec 0x118358 (fun s => s.RIP = 0x118358) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x118358 7 0x0)) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[397, 400]
    (.letOp (n := 404) (.out 0x11835c (shldR64R64Effect 0x11835c 5 7 0 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[402, 399]
    (.letOp (n := 405) (.exec 0x11835c (fun s => s.RIP = 0x11835c) (shldR64R64Effect 0x11835c 5 7 0 12) (Reg.operands [.gpr 7, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[402, 399]
    (.letOp (n := 406) (.out 0x118361 (movR64Imm64Effect 0x118361 10 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 10)) [] []) (.reg (.gpr 10))) #v[]
    (.letOp (n := 407) (.exec 0x118361 (fun s => s.RIP = 0x118361) (movR64Imm64Effect 0x118361 10 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 408) (.out 0x11836b (andR64R64Effect 0x11836b 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[399, 406]
    (.letOp (n := 409) (.exec 0x11836b (fun s => s.RIP = 0x11836b) (andR64R64Effect 0x11836b 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[399, 406]
    (.letOp (n := 410) (.out 0x11836e (movR64Imm64Effect 0x11836e 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 411) (.exec 0x11836e (fun s => s.RIP = 0x11836e) (movR64Imm64Effect 0x11836e 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 412) (.out 0x118378 (mulR64Effect 0x118378 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[410, 408]
    (.letOp (n := 413) (.out 0x118378 (mulR64Effect 0x118378 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[410, 408]
    (.letOp (n := 414) (.exec 0x118378 (fun s => s.RIP = 0x118378) (mulR64Effect 0x118378 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[410, 408]
    (.letOp (n := 415) (.out 0x11837b (addR64M64Effect 0x11837b 13 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 4] []) (.reg (.gpr 13))) #v[357, 4]
    (.letOp (n := 416) (.out 0x11837b (addR64M64Effect 0x11837b 13 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 4] []) (.flag .CF)) #v[357, 4]
    (.letOp (n := 417) (.exec 0x11837b (LoadPre 0x11837b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x11837b + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x11837b 13 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[357, 4]
    (.letOp (n := 418) (.out 0x118383 (atFlags StatusFlags.CF (adcR64M64Effect 0x118383 1 (.sib 4 none 0 (.d32 0xe0)))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 1))) #v[355, 4, 416]
    (.letOp (n := 419) (.exec 0x118383 (LoadPre 0x118383 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x118383 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x118383 1 (.sib 4 none 0 (.d32 0xe0)))) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[355, 4, 416]
    (.letOp (n := 420) (.out 0x11838b (addR64R64Effect 0x11838b 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 0] []) (.reg (.gpr 13))) #v[415, 412]
    (.letOp (n := 421) (.out 0x11838b (addR64R64Effect 0x11838b 13 0) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 0] []) (.flag .CF)) #v[415, 412]
    (.letOp (n := 422) (.exec 0x11838b (fun s => s.RIP = 0x11838b) (addR64R64Effect 0x11838b 13 0) (Reg.operands [.gpr 13, .gpr 0] [])) #v[415, 412]
    (.letOp (n := 423) (.out 0x11838e (atFlags StatusFlags.CF (adcR64R64Effect 0x11838e 1 2)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[418, 413, 421]
    (.letOp (n := 424) (.exec 0x11838e (fun s => s.RIP = 0x11838e) (atFlags StatusFlags.CF (adcR64R64Effect 0x11838e 1 2)) (Reg.operands [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[418, 413, 421]
    (.letOp (n := 425) (.out 0x118391 (addR64R64Effect 0x118391 13 8) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 8] []) (.reg (.gpr 13))) #v[420, 339]
    (.letOp (n := 426) (.out 0x118391 (addR64R64Effect 0x118391 13 8) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 8] []) (.flag .CF)) #v[420, 339]
    (.letOp (n := 427) (.exec 0x118391 (fun s => s.RIP = 0x118391) (addR64R64Effect 0x118391 13 8) (Reg.operands [.gpr 13, .gpr 8] [])) #v[420, 339]
    (.letOp (n := 428) (.out 0x118394 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x118394 1 0x0)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[423, 426]
    (.letOp (n := 429) (.exec 0x118394 (fun s => s.RIP = 0x118394) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x118394 1 0x0)) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[423, 426]
    (.letOp (n := 430) (.out 0x118398 (shldR64R64Effect 0x118398 5 1 13 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[428, 425]
    (.letOp (n := 431) (.exec 0x118398 (fun s => s.RIP = 0x118398) (shldR64R64Effect 0x118398 5 1 13 12) (Reg.operands [.gpr 1, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[428, 425]
    (.letOp (n := 432) (.out 0x11839d (movR64R64Effect 0x11839d 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[382]
    (.letOp (n := 433) (.exec 0x11839d (fun s => s.RIP = 0x11839d) (movR64R64Effect 0x11839d 0 15) (Reg.operands [.gpr 15] [])) #v[382]
    (.letOp (n := 434) (.out 0x1183a0 (mulM64Effect 0x1183a0 8 (.sib 4 none 0 (.d32 0x118))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[432, 4]
    (.letOp (n := 435) (.out 0x1183a0 (mulM64Effect 0x1183a0 8 (.sib 4 none 0 (.d32 0x118))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[432, 4]
    (.letOp (n := 436) (.exec 0x1183a0 (LoadPre 0x1183a0 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x1183a0 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x1183a0 8 (.sib 4 none 0 (.d32 0x118))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[432, 4]
    (.letOp (n := 437) (.exec 0x1183a8 (StorePre 0x1183a8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x1183a8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1183a8 2 (.sib 4 none 0 (.d32 0x118))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[435, 4]
    (.letOp (n := 438) (.exec 0x1183b0 (StorePre 0x1183b0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x1183b0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1183b0 0 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[434, 4]
    (.letOp (n := 439) (.out 0x1183b8 (movR64M64Effect 0x1183b8 0 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 440) (.exec 0x1183b8 (LoadPre 0x1183b8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1183b8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1183b8 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 441) (.out 0x1183bd (mulM64Effect 0x1183bd 8 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[439, 4]
    (.letOp (n := 442) (.out 0x1183bd (mulM64Effect 0x1183bd 8 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[439, 4]
    (.letOp (n := 443) (.exec 0x1183bd (LoadPre 0x1183bd (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x1183bd + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x1183bd 8 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[439, 4]
    (b_l118081_9)))))))))))))))))))))))))))))))))))))))))))))

def bytes_l118081_8 : List UInt8 :=
  [0x48, 0x01, 0xF0, 0x48, 0x83, 0xD7, 0x00, 0x48, 0x0F, 0xA4, 0xC7, 0x0C, 0x49, 0xBA, 0xFF, 0xFF,
    0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x4C, 0x21, 0xD0, 0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10,
    0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x4C, 0x03, 0xAC, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x48, 0x13,
    0x8C, 0x24, 0xE0, 0x00, 0x00, 0x00, 0x49, 0x01, 0xC5, 0x48, 0x11, 0xD1, 0x4D, 0x01, 0xC5, 0x48,
    0x83, 0xD1, 0x00, 0x4C, 0x0F, 0xA4, 0xE9, 0x0C, 0x4C, 0x89, 0xF8, 0x48, 0xF7, 0xA4, 0x24, 0x18,
    0x01, 0x00, 0x00, 0x48, 0x89, 0x94, 0x24, 0x18, 0x01, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0xE0,
    0x00, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x60, 0x48, 0xF7, 0xA4, 0x24, 0xB8, 0x00, 0x00, 0x00] ++ bytes_l118081_9

theorem code_l118081_8 : ∀ x ∈ codeRange 0x118355 bytes_l118081_8, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x18355 112 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l118081_9

def b_l118081_7 : Block Op Label signature Reg.count 355 :=
  .letOp (n := 355) (.out 0x1182ff (movR64R64Effect 0x1182ff 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[353]
    (.letOp (n := 356) (.exec 0x1182ff (fun s => s.RIP = 0x1182ff) (movR64R64Effect 0x1182ff 1 2) (Reg.operands [.gpr 2] [])) #v[353]
    (.letOp (n := 357) (.out 0x118302 (movR64R64Effect 0x118302 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[352]
    (.letOp (n := 358) (.exec 0x118302 (fun s => s.RIP = 0x118302) (movR64R64Effect 0x118302 13 0) (Reg.operands [.gpr 0] [])) #v[352]
    (.letOp (n := 359) (.out 0x118305 (movR64M64Effect 0x118305 0 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 360) (.exec 0x118305 (LoadPre 0x118305 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x118305 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x118305 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 361) (.out 0x11830a (mulM64Effect 0x11830a 8 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[359, 4]
    (.letOp (n := 362) (.out 0x11830a (mulM64Effect 0x11830a 8 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[359, 4]
    (.letOp (n := 363) (.exec 0x11830a (LoadPre 0x11830a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x11830a + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x11830a 8 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[359, 4]
    (.letOp (n := 364) (.out 0x118312 (movR64R64Effect 0x118312 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[361]
    (.letOp (n := 365) (.exec 0x118312 (fun s => s.RIP = 0x118312) (movR64R64Effect 0x118312 11 0) (Reg.operands [.gpr 0] [])) #v[361]
    (.letOp (n := 366) (.out 0x118315 (movR64R64Effect 0x118315 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[362]
    (.letOp (n := 367) (.exec 0x118315 (fun s => s.RIP = 0x118315) (movR64R64Effect 0x118315 3 2) (Reg.operands [.gpr 2] [])) #v[362]
    (.letOp (n := 368) (.out 0x118318 (movR64Imm64Effect 0x118318 0 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 369) (.exec 0x118318 (fun s => s.RIP = 0x118318) (movR64Imm64Effect 0x118318 0 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 370) (.out 0x118322 (andR64R64Effect 0x118322 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 0] []) (.reg (.gpr 14))) #v[341, 368]
    (.letOp (n := 371) (.exec 0x118322 (fun s => s.RIP = 0x118322) (andR64R64Effect 0x118322 14 0) (Reg.operands [.gpr 14, .gpr 0] [])) #v[341, 368]
    (.letOp (n := 372) (.exec 0x118325 (StorePre 0x118325 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x118325 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x118325 14 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[370, 4]
    (.letOp (n := 373) (.out 0x11832d (movR64M64Effect 0x11832d 0 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 374) (.exec 0x11832d (LoadPre 0x11832d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x11832d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11832d 0 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 375) (.out 0x118332 (mulR64Effect 0x118332 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[279, 373]
    (.letOp (n := 376) (.out 0x118332 (mulR64Effect 0x118332 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[279, 373]
    (.letOp (n := 377) (.exec 0x118332 (fun s => s.RIP = 0x118332) (mulR64Effect 0x118332 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[279, 373]
    (.letOp (n := 378) (.out 0x118335 (movR64R64Effect 0x118335 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[376]
    (.letOp (n := 379) (.exec 0x118335 (fun s => s.RIP = 0x118335) (movR64R64Effect 0x118335 7 2) (Reg.operands [.gpr 2] [])) #v[376]
    (.letOp (n := 380) (.out 0x118338 (movR64R64Effect 0x118338 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[375]
    (.letOp (n := 381) (.exec 0x118338 (fun s => s.RIP = 0x118338) (movR64R64Effect 0x118338 14 0) (Reg.operands [.gpr 0] [])) #v[375]
    (.letOp (n := 382) (.out 0x11833b (movR64M64Effect 0x11833b 15 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 383) (.exec 0x11833b (LoadPre 0x11833b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x11833b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11833b 15 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 384) (.out 0x118343 (movR64R64Effect 0x118343 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[382]
    (.letOp (n := 385) (.exec 0x118343 (fun s => s.RIP = 0x118343) (movR64R64Effect 0x118343 0 15) (Reg.operands [.gpr 15] [])) #v[382]
    (.letOp (n := 386) (.out 0x118346 (mulR64Effect 0x118346 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[292, 384]
    (.letOp (n := 387) (.out 0x118346 (mulR64Effect 0x118346 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[292, 384]
    (.letOp (n := 388) (.exec 0x118346 (fun s => s.RIP = 0x118346) (mulR64Effect 0x118346 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[292, 384]
    (.letOp (n := 389) (.out 0x118349 (addR64R64Effect 0x118349 14 11) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 11] []) (.reg (.gpr 14))) #v[380, 364]
    (.letOp (n := 390) (.out 0x118349 (addR64R64Effect 0x118349 14 11) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 11] []) (.flag .CF)) #v[380, 364]
    (.letOp (n := 391) (.exec 0x118349 (fun s => s.RIP = 0x118349) (addR64R64Effect 0x118349 14 11) (Reg.operands [.gpr 14, .gpr 11] [])) #v[380, 364]
    (.letOp (n := 392) (.out 0x11834c (atFlags StatusFlags.CF (adcR64R64Effect 0x11834c 7 3)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[378, 366, 390]
    (.letOp (n := 393) (.exec 0x11834c (fun s => s.RIP = 0x11834c) (atFlags StatusFlags.CF (adcR64R64Effect 0x11834c 7 3)) (Reg.operands [.gpr 7, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[378, 366, 390]
    (.letOp (n := 394) (.out 0x11834f (addR64R64Effect 0x11834f 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[386, 389]
    (.letOp (n := 395) (.out 0x11834f (addR64R64Effect 0x11834f 0 14) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 14] []) (.flag .CF)) #v[386, 389]
    (.letOp (n := 396) (.exec 0x11834f (fun s => s.RIP = 0x11834f) (addR64R64Effect 0x11834f 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[386, 389]
    (.letOp (n := 397) (.out 0x118352 (atFlags StatusFlags.CF (adcR64R64Effect 0x118352 7 2)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[392, 387, 395]
    (.letOp (n := 398) (.exec 0x118352 (fun s => s.RIP = 0x118352) (atFlags StatusFlags.CF (adcR64R64Effect 0x118352 7 2)) (Reg.operands [.gpr 7, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[392, 387, 395]
    (b_l118081_8))))))))))))))))))))))))))))))))))))))))))))

def bytes_l118081_7 : List UInt8 :=
  [0x48, 0x89, 0xD1, 0x49, 0x89, 0xC5, 0x48, 0x8B, 0x44, 0x24, 0x58, 0x48, 0xF7, 0xA4, 0x24, 0xC8,
    0x00, 0x00, 0x00, 0x49, 0x89, 0xC3, 0x48, 0x89, 0xD3, 0x48, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0x0F, 0x00, 0x49, 0x21, 0xC6, 0x4C, 0x89, 0xB4, 0x24, 0x98, 0x00, 0x00, 0x00, 0x48, 0x8B,
    0x44, 0x24, 0x50, 0x48, 0xF7, 0xE5, 0x48, 0x89, 0xD7, 0x49, 0x89, 0xC6, 0x4C, 0x8B, 0xBC, 0x24,
    0x80, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF8, 0x49, 0xF7, 0xE2, 0x4D, 0x01, 0xDE, 0x48, 0x11, 0xDF,
    0x4C, 0x01, 0xF0, 0x48, 0x11, 0xD7] ++ bytes_l118081_8

theorem code_l118081_7 : ∀ x ∈ codeRange 0x1182ff bytes_l118081_7, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x182ff 86 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l118081_8

def b_l118081_6 : Block Op Label signature Reg.count 312 :=
  .letOp (n := 312) (.out 0x118294 (addR64R64Effect 0x118294 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[307, 243]
    (.letOp (n := 313) (.out 0x118294 (addR64R64Effect 0x118294 0 1) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 1] []) (.flag .CF)) #v[307, 243]
    (.letOp (n := 314) (.exec 0x118294 (fun s => s.RIP = 0x118294) (addR64R64Effect 0x118294 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[307, 243]
    (.letOp (n := 315) (.out 0x118297 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x118297 6 0x0)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[310, 313]
    (.letOp (n := 316) (.exec 0x118297 (fun s => s.RIP = 0x118297) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x118297 6 0x0)) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[310, 313]
    (.letOp (n := 317) (.out 0x11829b (shldR64R64Effect 0x11829b 5 6 0 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[315, 312]
    (.letOp (n := 318) (.exec 0x11829b (fun s => s.RIP = 0x11829b) (shldR64R64Effect 0x11829b 5 6 0 12) (Reg.operands [.gpr 6, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[315, 312]
    (.letOp (n := 319) (.out 0x1182a0 (shlR64Effect 0x1182a0 4 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[312]
    (.letOp (n := 320) (.exec 0x1182a0 (fun s => s.RIP = 0x1182a0) (shlR64Effect 0x1182a0 4 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[312]
    (.letOp (n := 321) (.out 0x1182a4 (movR64Imm64Effect 0x1182a4 1 0xfffffffffffff0) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 322) (.exec 0x1182a4 (fun s => s.RIP = 0x1182a4) (movR64Imm64Effect 0x1182a4 1 0xfffffffffffff0) (Reg.operands [] [])) #v[]
    (.letOp (n := 323) (.out 0x1182ae (andR64R64Effect 0x1182ae 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[319, 321]
    (.letOp (n := 324) (.exec 0x1182ae (fun s => s.RIP = 0x1182ae) (andR64R64Effect 0x1182ae 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[319, 321]
    (.letOp (n := 325) (.out 0x1182b1 (orR64R64Effect 0x1182b1 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 15] []) (.reg (.gpr 0))) #v[323, 266]
    (.letOp (n := 326) (.exec 0x1182b1 (fun s => s.RIP = 0x1182b1) (orR64R64Effect 0x1182b1 0 15) (Reg.operands [.gpr 0, .gpr 15] [])) #v[323, 266]
    (.letOp (n := 327) (.out 0x1182b4 (movR64Imm64Effect 0x1182b4 1 0x1000003d1) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 328) (.exec 0x1182b4 (fun s => s.RIP = 0x1182b4) (movR64Imm64Effect 0x1182b4 1 0x1000003d1) (Reg.operands [] [])) #v[]
    (.letOp (n := 329) (.out 0x1182be (mulR64Effect 0x1182be 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[327, 325]
    (.letOp (n := 330) (.out 0x1182be (mulR64Effect 0x1182be 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[327, 325]
    (.letOp (n := 331) (.exec 0x1182be (fun s => s.RIP = 0x1182be) (mulR64Effect 0x1182be 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[327, 325]
    (.letOp (n := 332) (.out 0x1182c1 (movR64R64Effect 0x1182c1 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[330]
    (.letOp (n := 333) (.exec 0x1182c1 (fun s => s.RIP = 0x1182c1) (movR64R64Effect 0x1182c1 8 2) (Reg.operands [.gpr 2] [])) #v[330]
    (.letOp (n := 334) (.out 0x1182c4 (addR64M64Effect 0x1182c4 0 (.sib 4 none 0 (.d32 0xe0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[329, 4]
    (.letOp (n := 335) (.out 0x1182c4 (addR64M64Effect 0x1182c4 0 (.sib 4 none 0 (.d32 0xe0))) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 4] []) (.flag .CF)) #v[329, 4]
    (.letOp (n := 336) (.exec 0x1182c4 (LoadPre 0x1182c4 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x1182c4 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x1182c4 0 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[329, 4]
    (.letOp (n := 337) (.out 0x1182cc (atFlags StatusFlags.CF (adcR64M64Effect 0x1182cc 8 (.sib 4 none 0 (.d32 0x98)))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 8))) #v[332, 4, 335]
    (.letOp (n := 338) (.exec 0x1182cc (LoadPre 0x1182cc (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x1182cc + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x1182cc 8 (.sib 4 none 0 (.d32 0x98)))) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[332, 4, 335]
    (.letOp (n := 339) (.out 0x1182d4 (shldR64R64Effect 0x1182d4 5 8 0 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[337, 334]
    (.letOp (n := 340) (.exec 0x1182d4 (fun s => s.RIP = 0x1182d4) (shldR64R64Effect 0x1182d4 5 8 0 12) (Reg.operands [.gpr 8, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[337, 334]
    (.letOp (n := 341) (.out 0x1182d9 (movR64R64Effect 0x1182d9 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[334]
    (.letOp (n := 342) (.exec 0x1182d9 (fun s => s.RIP = 0x1182d9) (movR64R64Effect 0x1182d9 14 0) (Reg.operands [.gpr 0] [])) #v[334]
    (.letOp (n := 343) (.out 0x1182dc (movR64R64Effect 0x1182dc 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[288]
    (.letOp (n := 344) (.exec 0x1182dc (fun s => s.RIP = 0x1182dc) (movR64R64Effect 0x1182dc 0 7) (Reg.operands [.gpr 7] [])) #v[288]
    (.letOp (n := 345) (.out 0x1182df (mulM64Effect 0x1182df 8 (.sib 4 none 0 (.d32 0x118))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[343, 4]
    (.letOp (n := 346) (.out 0x1182df (mulM64Effect 0x1182df 8 (.sib 4 none 0 (.d32 0x118))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[343, 4]
    (.letOp (n := 347) (.exec 0x1182df (LoadPre 0x1182df (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x1182df + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x1182df 8 (.sib 4 none 0 (.d32 0x118))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[343, 4]
    (.letOp (n := 348) (.exec 0x1182e7 (StorePre 0x1182e7 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x1182e7 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1182e7 2 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[346, 4]
    (.letOp (n := 349) (.exec 0x1182ef (StorePre 0x1182ef 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x1182ef + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1182ef 0 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[345, 4]
    (.letOp (n := 350) (.out 0x1182f7 (movR64M64Effect 0x1182f7 0 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 351) (.exec 0x1182f7 (LoadPre 0x1182f7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1182f7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1182f7 0 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 352) (.out 0x1182fc (mulR64Effect 0x1182fc 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[258, 350]
    (.letOp (n := 353) (.out 0x1182fc (mulR64Effect 0x1182fc 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[258, 350]
    (.letOp (n := 354) (.exec 0x1182fc (fun s => s.RIP = 0x1182fc) (mulR64Effect 0x1182fc 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[258, 350]
    (b_l118081_7)))))))))))))))))))))))))))))))))))))))))))

def bytes_l118081_6 : List UInt8 :=
  [0x48, 0x01, 0xC8, 0x48, 0x83, 0xD6, 0x00, 0x48, 0x0F, 0xA4, 0xC6, 0x0C, 0x48, 0xC1, 0xE0, 0x04,
    0x48, 0xB9, 0xF0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x48, 0x21, 0xC8, 0x4C, 0x09, 0xF8,
    0x48, 0xB9, 0xD1, 0x03, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE1, 0x49, 0x89, 0xD0,
    0x48, 0x03, 0x84, 0x24, 0xE0, 0x00, 0x00, 0x00, 0x4C, 0x13, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00,
    0x49, 0x0F, 0xA4, 0xC0, 0x0C, 0x49, 0x89, 0xC6, 0x48, 0x89, 0xF8, 0x48, 0xF7, 0xA4, 0x24, 0x18,
    0x01, 0x00, 0x00, 0x48, 0x89, 0x94, 0x24, 0xE0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0xD8,
    0x00, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x78, 0x49, 0xF7, 0xE5] ++ bytes_l118081_7

theorem code_l118081_6 : ∀ x ∈ codeRange 0x118294 bytes_l118081_6, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x18294 107 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l118081_7

def b_l118081_5 : Block Op Label signature Reg.count 266 :=
  .letOp (n := 266) (.out 0x11823a (andR32Imm8Effect 0x11823a 4 15 0xf) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15] []) (.reg (.gpr 15))) #v[247]
    (.letOp (n := 267) (.exec 0x11823a (fun s => s.RIP = 0x11823a) (andR32Imm8Effect 0x11823a 4 15 0xf) (Reg.operands [.gpr 15] [])) #v[247]
    (.letOp (n := 268) (.out 0x11823e (movR64M64Effect 0x11823e 0 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 269) (.exec 0x11823e (LoadPre 0x11823e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x11823e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11823e 0 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 270) (.out 0x118243 (mulM64Effect 0x118243 8 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[268, 4]
    (.letOp (n := 271) (.out 0x118243 (mulM64Effect 0x118243 8 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[268, 4]
    (.letOp (n := 272) (.exec 0x118243 (LoadPre 0x118243 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x118243 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x118243 8 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[268, 4]
    (.letOp (n := 273) (.out 0x11824b (movR64R64Effect 0x11824b 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[271]
    (.letOp (n := 274) (.exec 0x11824b (fun s => s.RIP = 0x11824b) (movR64R64Effect 0x11824b 6 2) (Reg.operands [.gpr 2] [])) #v[271]
    (.letOp (n := 275) (.out 0x11824e (movR64R64Effect 0x11824e 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[270]
    (.letOp (n := 276) (.exec 0x11824e (fun s => s.RIP = 0x11824e) (movR64R64Effect 0x11824e 11 0) (Reg.operands [.gpr 0] [])) #v[270]
    (.letOp (n := 277) (.out 0x118251 (movR64M64Effect 0x118251 0 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 278) (.exec 0x118251 (LoadPre 0x118251 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x118251 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x118251 0 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 279) (.out 0x118259 (movR64M64Effect 0x118259 5 (.sib 4 none 0 (.d32 0xe8))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 280) (.exec 0x118259 (LoadPre 0x118259 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x118259 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x118259 5 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 281) (.out 0x118261 (mulR64Effect 0x118261 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[279, 277]
    (.letOp (n := 282) (.out 0x118261 (mulR64Effect 0x118261 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[279, 277]
    (.letOp (n := 283) (.exec 0x118261 (fun s => s.RIP = 0x118261) (mulR64Effect 0x118261 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[279, 277]
    (.letOp (n := 284) (.out 0x118264 (movR64R64Effect 0x118264 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[282]
    (.letOp (n := 285) (.exec 0x118264 (fun s => s.RIP = 0x118264) (movR64R64Effect 0x118264 3 2) (Reg.operands [.gpr 2] [])) #v[282]
    (.letOp (n := 286) (.out 0x118267 (movR64R64Effect 0x118267 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[281]
    (.letOp (n := 287) (.exec 0x118267 (fun s => s.RIP = 0x118267) (movR64R64Effect 0x118267 14 0) (Reg.operands [.gpr 0] [])) #v[281]
    (.letOp (n := 288) (.out 0x11826a (movR64M64Effect 0x11826a 7 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 289) (.exec 0x11826a (LoadPre 0x11826a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x11826a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11826a 7 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 290) (.out 0x11826f (movR64R64Effect 0x11826f 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[288]
    (.letOp (n := 291) (.exec 0x11826f (fun s => s.RIP = 0x11826f) (movR64R64Effect 0x11826f 0 7) (Reg.operands [.gpr 7] [])) #v[288]
    (.letOp (n := 292) (.out 0x118272 (movR64M64Effect 0x118272 10 (.sib 4 none 0 (.d32 0x110))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 293) (.exec 0x118272 (LoadPre 0x118272 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x118272 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x118272 10 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 294) (.out 0x11827a (mulR64Effect 0x11827a 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[292, 290]
    (.letOp (n := 295) (.out 0x11827a (mulR64Effect 0x11827a 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[292, 290]
    (.letOp (n := 296) (.exec 0x11827a (fun s => s.RIP = 0x11827a) (mulR64Effect 0x11827a 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[292, 290]
    (.letOp (n := 297) (.out 0x11827d (addR64R64Effect 0x11827d 11 8) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 8] []) (.reg (.gpr 11))) #v[275, 263]
    (.letOp (n := 298) (.out 0x11827d (addR64R64Effect 0x11827d 11 8) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 8] []) (.flag .CF)) #v[275, 263]
    (.letOp (n := 299) (.exec 0x11827d (fun s => s.RIP = 0x11827d) (addR64R64Effect 0x11827d 11 8) (Reg.operands [.gpr 11, .gpr 8] [])) #v[275, 263]
    (.letOp (n := 300) (.out 0x118280 (atFlags StatusFlags.CF (adcR64M64Effect 0x118280 6 (.sib 4 none 0 (.d32 0xd8)))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 6))) #v[273, 4, 298]
    (.letOp (n := 301) (.exec 0x118280 (LoadPre 0x118280 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x118280 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x118280 6 (.sib 4 none 0 (.d32 0xd8)))) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[273, 4, 298]
    (.letOp (n := 302) (.out 0x118288 (addR64R64Effect 0x118288 11 14) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 14] []) (.reg (.gpr 11))) #v[297, 286]
    (.letOp (n := 303) (.out 0x118288 (addR64R64Effect 0x118288 11 14) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 14] []) (.flag .CF)) #v[297, 286]
    (.letOp (n := 304) (.exec 0x118288 (fun s => s.RIP = 0x118288) (addR64R64Effect 0x118288 11 14) (Reg.operands [.gpr 11, .gpr 14] [])) #v[297, 286]
    (.letOp (n := 305) (.out 0x11828b (atFlags StatusFlags.CF (adcR64R64Effect 0x11828b 6 3)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[300, 284, 303]
    (.letOp (n := 306) (.exec 0x11828b (fun s => s.RIP = 0x11828b) (atFlags StatusFlags.CF (adcR64R64Effect 0x11828b 6 3)) (Reg.operands [.gpr 6, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[300, 284, 303]
    (.letOp (n := 307) (.out 0x11828e (addR64R64Effect 0x11828e 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[294, 302]
    (.letOp (n := 308) (.out 0x11828e (addR64R64Effect 0x11828e 0 11) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 11] []) (.flag .CF)) #v[294, 302]
    (.letOp (n := 309) (.exec 0x11828e (fun s => s.RIP = 0x11828e) (addR64R64Effect 0x11828e 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[294, 302]
    (.letOp (n := 310) (.out 0x118291 (atFlags StatusFlags.CF (adcR64R64Effect 0x118291 6 2)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[305, 295, 308]
    (.letOp (n := 311) (.exec 0x118291 (fun s => s.RIP = 0x118291) (atFlags StatusFlags.CF (adcR64R64Effect 0x118291 6 2)) (Reg.operands [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[305, 295, 308]
    (b_l118081_6))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l118081_5 : List UInt8 :=
  [0x41, 0x83, 0xE7, 0x0F, 0x48, 0x8B, 0x44, 0x24, 0x50, 0x48, 0xF7, 0xA4, 0x24, 0xC8, 0x00, 0x00,
    0x00, 0x48, 0x89, 0xD6, 0x49, 0x89, 0xC3, 0x48, 0x8B, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48,
    0x8B, 0xAC, 0x24, 0xE8, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE5, 0x48, 0x89, 0xD3, 0x49, 0x89, 0xC6,
    0x48, 0x8B, 0x7C, 0x24, 0x60, 0x48, 0x89, 0xF8, 0x4C, 0x8B, 0x94, 0x24, 0x10, 0x01, 0x00, 0x00,
    0x49, 0xF7, 0xE2, 0x4D, 0x01, 0xC3, 0x48, 0x13, 0xB4, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x4D, 0x01,
    0xF3, 0x48, 0x11, 0xDE, 0x4C, 0x01, 0xD8, 0x48, 0x11, 0xD6] ++ bytes_l118081_6

theorem code_l118081_5 : ∀ x ∈ codeRange 0x11823a bytes_l118081_5, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1823a 90 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l118081_6

def b_l118081_4 : Block Op Label signature Reg.count 223 :=
  .letOp (n := 223) (.out 0x1181e4 (addR64R64Effect 0x1181e4 9 15) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 15] []) (.reg (.gpr 9))) #v[218, 187]
    (.letOp (n := 224) (.out 0x1181e4 (addR64R64Effect 0x1181e4 9 15) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 15] []) (.flag .CF)) #v[218, 187]
    (.letOp (n := 225) (.exec 0x1181e4 (fun s => s.RIP = 0x1181e4) (addR64R64Effect 0x1181e4 9 15) (Reg.operands [.gpr 9, .gpr 15] [])) #v[218, 187]
    (.letOp (n := 226) (.out 0x1181e7 (atFlags StatusFlags.CF (adcR64R64Effect 0x1181e7 1 3)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[221, 185, 224]
    (.letOp (n := 227) (.exec 0x1181e7 (fun s => s.RIP = 0x1181e7) (atFlags StatusFlags.CF (adcR64R64Effect 0x1181e7 1 3)) (Reg.operands [.gpr 1, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[221, 185, 224]
    (.letOp (n := 228) (.out 0x1181ea (addR64R64Effect 0x1181ea 9 5) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 5] []) (.reg (.gpr 9))) #v[223, 196]
    (.letOp (n := 229) (.out 0x1181ea (addR64R64Effect 0x1181ea 9 5) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 5] []) (.flag .CF)) #v[223, 196]
    (.letOp (n := 230) (.exec 0x1181ea (fun s => s.RIP = 0x1181ea) (addR64R64Effect 0x1181ea 9 5) (Reg.operands [.gpr 9, .gpr 5] [])) #v[223, 196]
    (.letOp (n := 231) (.out 0x1181ed (atFlags StatusFlags.CF (adcR64R64Effect 0x1181ed 1 13)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[226, 198, 229]
    (.letOp (n := 232) (.exec 0x1181ed (fun s => s.RIP = 0x1181ed) (atFlags StatusFlags.CF (adcR64R64Effect 0x1181ed 1 13)) (Reg.operands [.gpr 1, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[226, 198, 229]
    (.letOp (n := 233) (.out 0x1181f0 (addR64R64Effect 0x1181f0 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0] []) (.reg (.gpr 9))) #v[228, 208]
    (.letOp (n := 234) (.out 0x1181f0 (addR64R64Effect 0x1181f0 9 0) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 0] []) (.flag .CF)) #v[228, 208]
    (.letOp (n := 235) (.exec 0x1181f0 (fun s => s.RIP = 0x1181f0) (addR64R64Effect 0x1181f0 9 0) (Reg.operands [.gpr 9, .gpr 0] [])) #v[228, 208]
    (.letOp (n := 236) (.out 0x1181f3 (atFlags StatusFlags.CF (adcR64R64Effect 0x1181f3 1 6)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[231, 211, 234]
    (.letOp (n := 237) (.exec 0x1181f3 (fun s => s.RIP = 0x1181f3) (atFlags StatusFlags.CF (adcR64R64Effect 0x1181f3 1 6)) (Reg.operands [.gpr 1, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[231, 211, 234]
    (.letOp (n := 238) (.out 0x1181f6 (addR64R64Effect 0x1181f6 9 7) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 7] []) (.reg (.gpr 9))) #v[233, 151]
    (.letOp (n := 239) (.out 0x1181f6 (addR64R64Effect 0x1181f6 9 7) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 7] []) (.flag .CF)) #v[233, 151]
    (.letOp (n := 240) (.exec 0x1181f6 (fun s => s.RIP = 0x1181f6) (addR64R64Effect 0x1181f6 9 7) (Reg.operands [.gpr 9, .gpr 7] [])) #v[233, 151]
    (.letOp (n := 241) (.out 0x1181f9 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1181f9 1 0x0)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[236, 239]
    (.letOp (n := 242) (.exec 0x1181f9 (fun s => s.RIP = 0x1181f9) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1181f9 1 0x0)) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[236, 239]
    (.letOp (n := 243) (.out 0x1181fd (shldR64R64Effect 0x1181fd 5 1 9 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[241, 238]
    (.letOp (n := 244) (.exec 0x1181fd (fun s => s.RIP = 0x1181fd) (shldR64R64Effect 0x1181fd 5 1 9 12) (Reg.operands [.gpr 1, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[241, 238]
    (.letOp (n := 245) (.out 0x118202 (movR64R64Effect 0x118202 15 9) (EffectPart.reads (.reg (.gpr 15)) [.gpr 9] []) (.reg (.gpr 15))) #v[238]
    (.letOp (n := 246) (.exec 0x118202 (fun s => s.RIP = 0x118202) (movR64R64Effect 0x118202 15 9) (Reg.operands [.gpr 9] [])) #v[238]
    (.letOp (n := 247) (.out 0x118205 (shrR64Effect 0x118205 4 15 48) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[245]
    (.letOp (n := 248) (.exec 0x118205 (fun s => s.RIP = 0x118205) (shrR64Effect 0x118205 4 15 48) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[245]
    (.letOp (n := 249) (.out 0x118209 (movR64R64Effect 0x118209 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[189]
    (.letOp (n := 250) (.exec 0x118209 (fun s => s.RIP = 0x118209) (movR64R64Effect 0x118209 0 8) (Reg.operands [.gpr 8] [])) #v[189]
    (.letOp (n := 251) (.out 0x11820c (mulR64Effect 0x11820c 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[158, 249]
    (.letOp (n := 252) (.out 0x11820c (mulR64Effect 0x11820c 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[158, 249]
    (.letOp (n := 253) (.exec 0x11820c (fun s => s.RIP = 0x11820c) (mulR64Effect 0x11820c 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[158, 249]
    (.letOp (n := 254) (.exec 0x11820f (StorePre 0x11820f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x11820f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11820f 2 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[252, 4]
    (.letOp (n := 255) (.exec 0x118217 (StorePre 0x118217 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x118217 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x118217 0 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[251, 4]
    (.letOp (n := 256) (.out 0x11821f (movR64M64Effect 0x11821f 0 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 257) (.exec 0x11821f (LoadPre 0x11821f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x11821f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11821f 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 258) (.out 0x118224 (movR64M64Effect 0x118224 13 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 259) (.exec 0x118224 (LoadPre 0x118224 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x118224 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x118224 13 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 260) (.out 0x11822c (mulR64Effect 0x11822c 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[258, 256]
    (.letOp (n := 261) (.out 0x11822c (mulR64Effect 0x11822c 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[258, 256]
    (.letOp (n := 262) (.exec 0x11822c (fun s => s.RIP = 0x11822c) (mulR64Effect 0x11822c 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[258, 256]
    (.letOp (n := 263) (.out 0x11822f (movR64R64Effect 0x11822f 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[260]
    (.letOp (n := 264) (.exec 0x11822f (fun s => s.RIP = 0x11822f) (movR64R64Effect 0x11822f 8 0) (Reg.operands [.gpr 0] [])) #v[260]
    (.letOp (n := 265) (.exec 0x118232 (StorePre 0x118232 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x118232 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x118232 2 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[261, 4]
    (b_l118081_5)))))))))))))))))))))))))))))))))))))))))))

def bytes_l118081_4 : List UInt8 :=
  [0x4D, 0x01, 0xF9, 0x48, 0x11, 0xD9, 0x49, 0x01, 0xE9, 0x4C, 0x11, 0xE9, 0x49, 0x01, 0xC1, 0x48,
    0x11, 0xF1, 0x49, 0x01, 0xF9, 0x48, 0x83, 0xD1, 0x00, 0x4C, 0x0F, 0xA4, 0xC9, 0x0C, 0x4D, 0x89,
    0xCF, 0x49, 0xC1, 0xEF, 0x30, 0x4C, 0x89, 0xC0, 0x49, 0xF7, 0xE2, 0x48, 0x89, 0x94, 0x24, 0x98,
    0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0xE0, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x58,
    0x4C, 0x8B, 0xAC, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE5, 0x49, 0x89, 0xC0, 0x48, 0x89,
    0x94, 0x24, 0xD8, 0x00, 0x00, 0x00] ++ bytes_l118081_5

theorem code_l118081_4 : ∀ x ∈ codeRange 0x1181e4 bytes_l118081_4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x181e4 86 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l118081_5

def b_l118081_3 : Block Op Label signature Reg.count 178 :=
  .letOp (n := 178) (.out 0x11818c (movR64R64Effect 0x11818c 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[174]
    (.letOp (n := 179) (.exec 0x11818c (fun s => s.RIP = 0x11818c) (movR64R64Effect 0x11818c 14 0) (Reg.operands [.gpr 0] [])) #v[174]
    (.letOp (n := 180) (.out 0x11818f (movR64M64Effect 0x11818f 0 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 181) (.exec 0x11818f (LoadPre 0x11818f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x11818f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11818f 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 182) (.out 0x118194 (mulR64Effect 0x118194 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[107, 180]
    (.letOp (n := 183) (.out 0x118194 (mulR64Effect 0x118194 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[107, 180]
    (.letOp (n := 184) (.exec 0x118194 (fun s => s.RIP = 0x118194) (mulR64Effect 0x118194 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[107, 180]
    (.letOp (n := 185) (.out 0x118197 (movR64R64Effect 0x118197 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[183]
    (.letOp (n := 186) (.exec 0x118197 (fun s => s.RIP = 0x118197) (movR64R64Effect 0x118197 3 2) (Reg.operands [.gpr 2] [])) #v[183]
    (.letOp (n := 187) (.out 0x11819a (movR64R64Effect 0x11819a 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[182]
    (.letOp (n := 188) (.exec 0x11819a (fun s => s.RIP = 0x11819a) (movR64R64Effect 0x11819a 15 0) (Reg.operands [.gpr 0] [])) #v[182]
    (.letOp (n := 189) (.out 0x11819d (movR64M64Effect 0x11819d 8 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 190) (.exec 0x11819d (LoadPre 0x11819d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x11819d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11819d 8 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 191) (.out 0x1181a2 (movR64R64Effect 0x1181a2 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[189]
    (.letOp (n := 192) (.exec 0x1181a2 (fun s => s.RIP = 0x1181a2) (movR64R64Effect 0x1181a2 0 8) (Reg.operands [.gpr 8] [])) #v[189]
    (.letOp (n := 193) (.out 0x1181a5 (mulR64Effect 0x1181a5 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[61, 191]
    (.letOp (n := 194) (.out 0x1181a5 (mulR64Effect 0x1181a5 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[61, 191]
    (.letOp (n := 195) (.exec 0x1181a5 (fun s => s.RIP = 0x1181a5) (mulR64Effect 0x1181a5 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[61, 191]
    (.letOp (n := 196) (.out 0x1181a8 (movR64R64Effect 0x1181a8 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[193]
    (.letOp (n := 197) (.exec 0x1181a8 (fun s => s.RIP = 0x1181a8) (movR64R64Effect 0x1181a8 5 0) (Reg.operands [.gpr 0] [])) #v[193]
    (.letOp (n := 198) (.out 0x1181ab (movR64R64Effect 0x1181ab 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[194]
    (.letOp (n := 199) (.exec 0x1181ab (fun s => s.RIP = 0x1181ab) (movR64R64Effect 0x1181ab 13 2) (Reg.operands [.gpr 2] [])) #v[194]
    (.letOp (n := 200) (.out 0x1181ae (shrR64Effect 0x1181ae 4 6 52) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[127]
    (.letOp (n := 201) (.exec 0x1181ae (fun s => s.RIP = 0x1181ae) (shrR64Effect 0x1181ae 4 6 52) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[127]
    (.letOp (n := 202) (.out 0x1181b2 (movR64Imm64Effect 0x1181b2 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 203) (.exec 0x1181b2 (fun s => s.RIP = 0x1181b2) (movR64Imm64Effect 0x1181b2 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 204) (.out 0x1181bc (imulR64R64Effect 0x1181bc 4 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[200, 202]
    (.letOp (n := 205) (.exec 0x1181bc (fun s => s.RIP = 0x1181bc) (imulR64R64Effect 0x1181bc 4 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[200, 202]
    (.letOp (n := 206) (.out 0x1181c0 (movR64R64Effect 0x1181c0 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[131]
    (.letOp (n := 207) (.exec 0x1181c0 (fun s => s.RIP = 0x1181c0) (movR64R64Effect 0x1181c0 0 11) (Reg.operands [.gpr 11] [])) #v[131]
    (.letOp (n := 208) (.out 0x1181c3 (mulR64Effect 0x1181c3 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[202, 206]
    (.letOp (n := 209) (.out 0x1181c3 (mulR64Effect 0x1181c3 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[202, 206]
    (.letOp (n := 210) (.exec 0x1181c3 (fun s => s.RIP = 0x1181c3) (mulR64Effect 0x1181c3 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[202, 206]
    (.letOp (n := 211) (.out 0x1181c6 (addR64R64Effect 0x1181c6 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[204, 209]
    (.letOp (n := 212) (.exec 0x1181c6 (fun s => s.RIP = 0x1181c6) (addR64R64Effect 0x1181c6 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[204, 209]
    (.letOp (n := 213) (.out 0x1181c9 (addR64M64Effect 0x1181c9 9 (.sib 4 none 0 (.d32 0xe0))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 4] []) (.reg (.gpr 9))) #v[170, 4]
    (.letOp (n := 214) (.out 0x1181c9 (addR64M64Effect 0x1181c9 9 (.sib 4 none 0 (.d32 0xe0))) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 4] []) (.flag .CF)) #v[170, 4]
    (.letOp (n := 215) (.exec 0x1181c9 (LoadPre 0x1181c9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x1181c9 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x1181c9 9 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[170, 4]
    (.letOp (n := 216) (.out 0x1181d1 (atFlags StatusFlags.CF (adcR64M64Effect 0x1181d1 1 (.sib 4 none 0 (.d32 0x98)))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 1))) #v[168, 4, 214]
    (.letOp (n := 217) (.exec 0x1181d1 (LoadPre 0x1181d1 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x1181d1 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x1181d1 1 (.sib 4 none 0 (.d32 0x98)))) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[168, 4, 214]
    (.letOp (n := 218) (.out 0x1181d9 (addR64R64Effect 0x1181d9 9 14) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 14] []) (.reg (.gpr 9))) #v[213, 178]
    (.letOp (n := 219) (.out 0x1181d9 (addR64R64Effect 0x1181d9 9 14) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 14] []) (.flag .CF)) #v[213, 178]
    (.letOp (n := 220) (.exec 0x1181d9 (fun s => s.RIP = 0x1181d9) (addR64R64Effect 0x1181d9 9 14) (Reg.operands [.gpr 9, .gpr 14] [])) #v[213, 178]
    (.letOp (n := 221) (.out 0x1181dc (atFlags StatusFlags.CF (adcR64M64Effect 0x1181dc 1 (.sib 4 none 0 (.d32 0xd8)))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 1))) #v[216, 4, 219]
    (.letOp (n := 222) (.exec 0x1181dc (LoadPre 0x1181dc (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x1181dc + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x1181dc 1 (.sib 4 none 0 (.d32 0xd8)))) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[216, 4, 219]
    (b_l118081_4)))))))))))))))))))))))))))))))))))))))))))))

def bytes_l118081_3 : List UInt8 :=
  [0x49, 0x89, 0xC6, 0x48, 0x8B, 0x44, 0x24, 0x60, 0x49, 0xF7, 0xE0, 0x48, 0x89, 0xD3, 0x49, 0x89,
    0xC7, 0x4C, 0x8B, 0x44, 0x24, 0x78, 0x4C, 0x89, 0xC0, 0x48, 0xF7, 0xE5, 0x48, 0x89, 0xC5, 0x49,
    0x89, 0xD5, 0x48, 0xC1, 0xEE, 0x34, 0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00,
    0x48, 0x0F, 0xAF, 0xF2, 0x4C, 0x89, 0xD8, 0x48, 0xF7, 0xE2, 0x48, 0x01, 0xD6, 0x4C, 0x03, 0x8C,
    0x24, 0xE0, 0x00, 0x00, 0x00, 0x48, 0x13, 0x8C, 0x24, 0x98, 0x00, 0x00, 0x00, 0x4D, 0x01, 0xF1,
    0x48, 0x13, 0x8C, 0x24, 0xD8, 0x00, 0x00, 0x00] ++ bytes_l118081_4

theorem code_l118081_3 : ∀ x ∈ codeRange 0x11818c bytes_l118081_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1818c 88 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l118081_4

def b_l118081_2 : Block Op Label signature Reg.count 137 :=
  .letOp (n := 137) (.out 0x11812c (movR64Imm64Effect 0x11812c 1 0x1000003d10) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 138) (.exec 0x11812c (fun s => s.RIP = 0x11812c) (movR64Imm64Effect 0x11812c 1 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 139) (.out 0x118136 (mulR64Effect 0x118136 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[137, 135]
    (.letOp (n := 140) (.out 0x118136 (mulR64Effect 0x118136 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[137, 135]
    (.letOp (n := 141) (.exec 0x118136 (fun s => s.RIP = 0x118136) (mulR64Effect 0x118136 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[137, 135]
    (.letOp (n := 142) (.out 0x118139 (movR64R64Effect 0x118139 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[140]
    (.letOp (n := 143) (.exec 0x118139 (fun s => s.RIP = 0x118139) (movR64R64Effect 0x118139 7 2) (Reg.operands [.gpr 2] [])) #v[140]
    (.letOp (n := 144) (.out 0x11813c (movR64R64Effect 0x11813c 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[139]
    (.letOp (n := 145) (.exec 0x11813c (fun s => s.RIP = 0x11813c) (movR64R64Effect 0x11813c 12 0) (Reg.operands [.gpr 0] [])) #v[139]
    (.letOp (n := 146) (.out 0x11813f (addR64R64Effect 0x11813f 12 10) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 10] []) (.reg (.gpr 12))) #v[144, 114]
    (.letOp (n := 147) (.out 0x11813f (addR64R64Effect 0x11813f 12 10) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 10] []) (.flag .CF)) #v[144, 114]
    (.letOp (n := 148) (.exec 0x11813f (fun s => s.RIP = 0x11813f) (addR64R64Effect 0x11813f 12 10) (Reg.operands [.gpr 12, .gpr 10] [])) #v[144, 114]
    (.letOp (n := 149) (.out 0x118142 (atFlags StatusFlags.CF (adcR64R64Effect 0x118142 7 9)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[142, 117, 147]
    (.letOp (n := 150) (.exec 0x118142 (fun s => s.RIP = 0x118142) (atFlags StatusFlags.CF (adcR64R64Effect 0x118142 7 9)) (Reg.operands [.gpr 7, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[142, 117, 147]
    (.letOp (n := 151) (.out 0x118145 (shldR64R64Effect 0x118145 5 7 12 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[149, 146]
    (.letOp (n := 152) (.exec 0x118145 (fun s => s.RIP = 0x118145) (shldR64R64Effect 0x118145 5 7 12 12) (Reg.operands [.gpr 7, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[149, 146]
    (.letOp (n := 153) (.out 0x11814a (movR64R64Effect 0x11814a 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[119]
    (.letOp (n := 154) (.exec 0x11814a (fun s => s.RIP = 0x11814a) (movR64R64Effect 0x11814a 0 3) (Reg.operands [.gpr 3] [])) #v[119]
    (.letOp (n := 155) (.out 0x11814d (mulR64Effect 0x11814d 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[53, 153]
    (.letOp (n := 156) (.out 0x11814d (mulR64Effect 0x11814d 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[53, 153]
    (.letOp (n := 157) (.exec 0x11814d (fun s => s.RIP = 0x11814d) (mulR64Effect 0x11814d 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[53, 153]
    (.letOp (n := 158) (.out 0x118150 (movR64R64Effect 0x118150 10 14) (EffectPart.reads (.reg (.gpr 10)) [.gpr 14] []) (.reg (.gpr 10))) #v[53]
    (.letOp (n := 159) (.exec 0x118150 (fun s => s.RIP = 0x118150) (movR64R64Effect 0x118150 10 14) (Reg.operands [.gpr 14] [])) #v[53]
    (.letOp (n := 160) (.exec 0x118153 (StorePre 0x118153 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x118153 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x118153 14 (.sib 4 none 0 (.d32 0x118))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 161) (.exec 0x11815b (StorePre 0x11815b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x11815b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11815b 2 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[156, 4]
    (.letOp (n := 162) (.exec 0x118163 (StorePre 0x118163 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x118163 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x118163 0 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[155, 4]
    (.letOp (n := 163) (.out 0x11816b (movR64M64Effect 0x11816b 0 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 164) (.exec 0x11816b (LoadPre 0x11816b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x11816b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11816b 0 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 165) (.out 0x118170 (mulR64Effect 0x118170 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[55, 163]
    (.letOp (n := 166) (.out 0x118170 (mulR64Effect 0x118170 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[55, 163]
    (.letOp (n := 167) (.exec 0x118170 (fun s => s.RIP = 0x118170) (mulR64Effect 0x118170 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[55, 163]
    (.letOp (n := 168) (.out 0x118173 (movR64R64Effect 0x118173 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[166]
    (.letOp (n := 169) (.exec 0x118173 (fun s => s.RIP = 0x118173) (movR64R64Effect 0x118173 1 2) (Reg.operands [.gpr 2] [])) #v[166]
    (.letOp (n := 170) (.out 0x118176 (movR64R64Effect 0x118176 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[165]
    (.letOp (n := 171) (.exec 0x118176 (fun s => s.RIP = 0x118176) (movR64R64Effect 0x118176 9 0) (Reg.operands [.gpr 0] [])) #v[165]
    (.letOp (n := 172) (.out 0x118179 (movR64M64Effect 0x118179 0 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 173) (.exec 0x118179 (LoadPre 0x118179 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x118179 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x118179 0 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 174) (.out 0x118181 (mulR64Effect 0x118181 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15, .gpr 0] []) (.reg (.gpr 0))) #v[57, 172]
    (.letOp (n := 175) (.out 0x118181 (mulR64Effect 0x118181 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15, .gpr 0] []) (.reg (.gpr 2))) #v[57, 172]
    (.letOp (n := 176) (.exec 0x118181 (fun s => s.RIP = 0x118181) (mulR64Effect 0x118181 15) (Reg.operands [.gpr 15, .gpr 0] [])) #v[57, 172]
    (.letOp (n := 177) (.exec 0x118184 (StorePre 0x118184 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x118184 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x118184 2 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[175, 4]
    (b_l118081_3)))))))))))))))))))))))))))))))))))))))))

def bytes_l118081_2 : List UInt8 :=
  [0x48, 0xB9, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE1, 0x48, 0x89, 0xD7,
    0x49, 0x89, 0xC4, 0x4D, 0x01, 0xD4, 0x4C, 0x11, 0xCF, 0x4C, 0x0F, 0xA4, 0xE7, 0x0C, 0x48, 0x89,
    0xD8, 0x49, 0xF7, 0xE6, 0x4D, 0x89, 0xF2, 0x4C, 0x89, 0xB4, 0x24, 0x18, 0x01, 0x00, 0x00, 0x48,
    0x89, 0x94, 0x24, 0x98, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0xE0, 0x00, 0x00, 0x00, 0x48,
    0x8B, 0x44, 0x24, 0x50, 0x49, 0xF7, 0xE5, 0x48, 0x89, 0xD1, 0x49, 0x89, 0xC1, 0x48, 0x8B, 0x84,
    0x24, 0x80, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE7, 0x48, 0x89, 0x94, 0x24, 0xD8, 0x00, 0x00, 0x00] ++ bytes_l118081_3

theorem code_l118081_2 : ∀ x ∈ codeRange 0x11812c bytes_l118081_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1812c 96 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l118081_3

def b_l118081_1 : Block Op Label signature Reg.count 95 :=
  .letOp (n := 95) (.out 0x1180d9 (movR64R64Effect 0x1180d9 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[89]
    (.letOp (n := 96) (.exec 0x1180d9 (fun s => s.RIP = 0x1180d9) (movR64R64Effect 0x1180d9 6 0) (Reg.operands [.gpr 0] [])) #v[89]
    (.letOp (n := 97) (.out 0x1180dc (addR64R64Effect 0x1180dc 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 8] []) (.reg (.gpr 6))) #v[95, 82]
    (.letOp (n := 98) (.out 0x1180dc (addR64R64Effect 0x1180dc 6 8) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 8] []) (.flag .CF)) #v[95, 82]
    (.letOp (n := 99) (.exec 0x1180dc (fun s => s.RIP = 0x1180dc) (addR64R64Effect 0x1180dc 6 8) (Reg.operands [.gpr 6, .gpr 8] [])) #v[95, 82]
    (.letOp (n := 100) (.out 0x1180df (atFlags StatusFlags.CF (adcR64R64Effect 0x1180df 1 7)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[93, 85, 98]
    (.letOp (n := 101) (.exec 0x1180df (fun s => s.RIP = 0x1180df) (atFlags StatusFlags.CF (adcR64R64Effect 0x1180df 1 7)) (Reg.operands [.gpr 1, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[93, 85, 98]
    (.letOp (n := 102) (.out 0x1180e2 (movR64M64Effect 0x1180e2 0 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 103) (.exec 0x1180e2 (LoadPre 0x1180e2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1180e2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1180e2 0 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 104) (.out 0x1180e7 (mulR64Effect 0x1180e7 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[59, 102]
    (.letOp (n := 105) (.out 0x1180e7 (mulR64Effect 0x1180e7 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[59, 102]
    (.letOp (n := 106) (.exec 0x1180e7 (fun s => s.RIP = 0x1180e7) (mulR64Effect 0x1180e7 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[59, 102]
    (.letOp (n := 107) (.out 0x1180ea (movR64R64Effect 0x1180ea 8 9) (EffectPart.reads (.reg (.gpr 8)) [.gpr 9] []) (.reg (.gpr 8))) #v[59]
    (.letOp (n := 108) (.exec 0x1180ea (fun s => s.RIP = 0x1180ea) (movR64R64Effect 0x1180ea 8 9) (Reg.operands [.gpr 9] [])) #v[59]
    (.letOp (n := 109) (.exec 0x1180ed (StorePre 0x1180ed 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x1180ed + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1180ed 9 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 110) (.out 0x1180f5 (movR64R64Effect 0x1180f5 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[105]
    (.letOp (n := 111) (.exec 0x1180f5 (fun s => s.RIP = 0x1180f5) (movR64R64Effect 0x1180f5 9 2) (Reg.operands [.gpr 2] [])) #v[105]
    (.letOp (n := 112) (.out 0x1180f8 (movR64R64Effect 0x1180f8 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[104]
    (.letOp (n := 113) (.exec 0x1180f8 (fun s => s.RIP = 0x1180f8) (movR64R64Effect 0x1180f8 10 0) (Reg.operands [.gpr 0] [])) #v[104]
    (.letOp (n := 114) (.out 0x1180fb (addR64R64Effect 0x1180fb 10 6) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 6] []) (.reg (.gpr 10))) #v[112, 97]
    (.letOp (n := 115) (.out 0x1180fb (addR64R64Effect 0x1180fb 10 6) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 6] []) (.flag .CF)) #v[112, 97]
    (.letOp (n := 116) (.exec 0x1180fb (fun s => s.RIP = 0x1180fb) (addR64R64Effect 0x1180fb 10 6) (Reg.operands [.gpr 10, .gpr 6] [])) #v[112, 97]
    (.letOp (n := 117) (.out 0x1180fe (atFlags StatusFlags.CF (adcR64R64Effect 0x1180fe 9 1)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[110, 100, 115]
    (.letOp (n := 118) (.exec 0x1180fe (fun s => s.RIP = 0x1180fe) (atFlags StatusFlags.CF (adcR64R64Effect 0x1180fe 9 1)) (Reg.operands [.gpr 9, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[110, 100, 115]
    (.letOp (n := 119) (.out 0x118101 (movR64M64Effect 0x118101 3 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 120) (.exec 0x118101 (LoadPre 0x118101 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x118101 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x118101 3 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 121) (.out 0x118106 (movR64R64Effect 0x118106 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[119]
    (.letOp (n := 122) (.exec 0x118106 (fun s => s.RIP = 0x118106) (movR64R64Effect 0x118106 0 3) (Reg.operands [.gpr 3] [])) #v[119]
    (.letOp (n := 123) (.out 0x118109 (mulR64Effect 0x118109 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[61, 121]
    (.letOp (n := 124) (.out 0x118109 (mulR64Effect 0x118109 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[61, 121]
    (.letOp (n := 125) (.exec 0x118109 (fun s => s.RIP = 0x118109) (mulR64Effect 0x118109 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[61, 121]
    (.letOp (n := 126) (.exec 0x11810c (StorePre 0x11810c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x11810c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11810c 5 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 127) (.out 0x118114 (movR64R64Effect 0x118114 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[124]
    (.letOp (n := 128) (.exec 0x118114 (fun s => s.RIP = 0x118114) (movR64R64Effect 0x118114 6 2) (Reg.operands [.gpr 2] [])) #v[124]
    (.letOp (n := 129) (.out 0x118117 (movR64R64Effect 0x118117 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[124]
    (.letOp (n := 130) (.exec 0x118117 (fun s => s.RIP = 0x118117) (movR64R64Effect 0x118117 11 2) (Reg.operands [.gpr 2] [])) #v[124]
    (.letOp (n := 131) (.out 0x11811a (shldR64R64Effect 0x11811a 5 11 0 12) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[129, 123]
    (.letOp (n := 132) (.exec 0x11811a (fun s => s.RIP = 0x11811a) (shldR64R64Effect 0x11811a 5 11 0 12) (Reg.operands [.gpr 11, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[129, 123]
    (.letOp (n := 133) (.out 0x11811f (movR64Imm64Effect 0x11811f 1 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 134) (.exec 0x11811f (fun s => s.RIP = 0x11811f) (movR64Imm64Effect 0x11811f 1 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 135) (.out 0x118129 (andR64R64Effect 0x118129 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[123, 133]
    (.letOp (n := 136) (.exec 0x118129 (fun s => s.RIP = 0x118129) (andR64R64Effect 0x118129 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[123, 133]
    (b_l118081_2))))))))))))))))))))))))))))))))))))))))))

def bytes_l118081_1 : List UInt8 :=
  [0x48, 0x89, 0xC6, 0x4C, 0x01, 0xC6, 0x48, 0x11, 0xF9, 0x48, 0x8B, 0x44, 0x24, 0x78, 0x49, 0xF7,
    0xE1, 0x4D, 0x89, 0xC8, 0x4C, 0x89, 0x8C, 0x24, 0xE8, 0x00, 0x00, 0x00, 0x49, 0x89, 0xD1, 0x49,
    0x89, 0xC2, 0x49, 0x01, 0xF2, 0x49, 0x11, 0xC9, 0x48, 0x8B, 0x5C, 0x24, 0x58, 0x48, 0x89, 0xD8,
    0x48, 0xF7, 0xE5, 0x48, 0x89, 0xAC, 0x24, 0x10, 0x01, 0x00, 0x00, 0x48, 0x89, 0xD6, 0x49, 0x89,
    0xD3, 0x49, 0x0F, 0xA4, 0xC3, 0x0C, 0x48, 0xB9, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00,
    0x48, 0x21, 0xC8] ++ bytes_l118081_2

theorem code_l118081_1 : ∀ x ∈ codeRange 0x1180d9 bytes_l118081_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x180d9 83 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l118081_2

def b_l118081 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x118081 (movR64M64Effect 0x118081 14 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 54) (.exec 0x118081 (LoadPre 0x118081 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x118081 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x118081 14 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x118085 (movR64M64Effect 0x118085 13 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 56) (.exec 0x118085 (LoadPre 0x118085 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x118085 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x118085 13 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x11808a (movR64M64Effect 0x11808a 15 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 58) (.exec 0x11808a (LoadPre 0x11808a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11808a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11808a 15 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x11808f (movR64M64Effect 0x11808f 9 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 60) (.exec 0x11808f (LoadPre 0x11808f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11808f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11808f 9 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x118094 (movR64M64Effect 0x118094 5 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 62) (.exec 0x118094 (LoadPre 0x118094 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x118094 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x118094 5 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x118099 (movR64M64Effect 0x118099 0 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 64) (.exec 0x118099 (LoadPre 0x118099 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x118099 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x118099 0 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x11809e (mulR64Effect 0x11809e 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[53, 63]
    (.letOp (n := 66) (.out 0x11809e (mulR64Effect 0x11809e 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[53, 63]
    (.letOp (n := 67) (.exec 0x11809e (fun s => s.RIP = 0x11809e) (mulR64Effect 0x11809e 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[53, 63]
    (.letOp (n := 68) (.out 0x1180a1 (movR64R64Effect 0x1180a1 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[66]
    (.letOp (n := 69) (.exec 0x1180a1 (fun s => s.RIP = 0x1180a1) (movR64R64Effect 0x1180a1 1 2) (Reg.operands [.gpr 2] [])) #v[66]
    (.letOp (n := 70) (.out 0x1180a4 (movR64R64Effect 0x1180a4 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[65]
    (.letOp (n := 71) (.exec 0x1180a4 (fun s => s.RIP = 0x1180a4) (movR64R64Effect 0x1180a4 6 0) (Reg.operands [.gpr 0] [])) #v[65]
    (.letOp (n := 72) (.out 0x1180a7 (movR64M64Effect 0x1180a7 0 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 73) (.exec 0x1180a7 (LoadPre 0x1180a7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1180a7 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1180a7 0 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.out 0x1180af (mulR64Effect 0x1180af 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[55, 72]
    (.letOp (n := 75) (.out 0x1180af (mulR64Effect 0x1180af 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[55, 72]
    (.letOp (n := 76) (.exec 0x1180af (fun s => s.RIP = 0x1180af) (mulR64Effect 0x1180af 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[55, 72]
    (.letOp (n := 77) (.exec 0x1180b2 (StorePre 0x1180b2 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x1180b2 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1180b2 13 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 78) (.out 0x1180ba (movR64R64Effect 0x1180ba 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[75]
    (.letOp (n := 79) (.exec 0x1180ba (fun s => s.RIP = 0x1180ba) (movR64R64Effect 0x1180ba 7 2) (Reg.operands [.gpr 2] [])) #v[75]
    (.letOp (n := 80) (.out 0x1180bd (movR64R64Effect 0x1180bd 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[74]
    (.letOp (n := 81) (.exec 0x1180bd (fun s => s.RIP = 0x1180bd) (movR64R64Effect 0x1180bd 8 0) (Reg.operands [.gpr 0] [])) #v[74]
    (.letOp (n := 82) (.out 0x1180c0 (addR64R64Effect 0x1180c0 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6] []) (.reg (.gpr 8))) #v[80, 70]
    (.letOp (n := 83) (.out 0x1180c0 (addR64R64Effect 0x1180c0 8 6) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 6] []) (.flag .CF)) #v[80, 70]
    (.letOp (n := 84) (.exec 0x1180c0 (fun s => s.RIP = 0x1180c0) (addR64R64Effect 0x1180c0 8 6) (Reg.operands [.gpr 8, .gpr 6] [])) #v[80, 70]
    (.letOp (n := 85) (.out 0x1180c3 (atFlags StatusFlags.CF (adcR64R64Effect 0x1180c3 7 1)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[78, 68, 83]
    (.letOp (n := 86) (.exec 0x1180c3 (fun s => s.RIP = 0x1180c3) (atFlags StatusFlags.CF (adcR64R64Effect 0x1180c3 7 1)) (Reg.operands [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[78, 68, 83]
    (.letOp (n := 87) (.out 0x1180c6 (movR64M64Effect 0x1180c6 0 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 88) (.exec 0x1180c6 (LoadPre 0x1180c6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1180c6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1180c6 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 89) (.out 0x1180cb (mulR64Effect 0x1180cb 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15, .gpr 0] []) (.reg (.gpr 0))) #v[57, 87]
    (.letOp (n := 90) (.out 0x1180cb (mulR64Effect 0x1180cb 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15, .gpr 0] []) (.reg (.gpr 2))) #v[57, 87]
    (.letOp (n := 91) (.exec 0x1180cb (fun s => s.RIP = 0x1180cb) (mulR64Effect 0x1180cb 15) (Reg.operands [.gpr 15, .gpr 0] [])) #v[57, 87]
    (.letOp (n := 92) (.exec 0x1180ce (StorePre 0x1180ce 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x1180ce + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1180ce 15 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 93) (.out 0x1180d6 (movR64R64Effect 0x1180d6 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[90]
    (.letOp (n := 94) (.exec 0x1180d6 (fun s => s.RIP = 0x1180d6) (movR64R64Effect 0x1180d6 1 2) (Reg.operands [.gpr 2] [])) #v[90]
    (b_l118081_1))))))))))))))))))))))))))))))))))))))))))

def bytes_l118081 : List UInt8 :=
  [0x4C, 0x8B, 0x34, 0x24, 0x4C, 0x8B, 0x6C, 0x24, 0x08, 0x4C, 0x8B, 0x7C, 0x24, 0x10, 0x4C, 0x8B,
    0x4C, 0x24, 0x18, 0x48, 0x8B, 0x6C, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x50, 0x49, 0xF7, 0xE6,
    0x48, 0x89, 0xD1, 0x48, 0x89, 0xC6, 0x48, 0x8B, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x49, 0xF7,
    0xE5, 0x4C, 0x89, 0xAC, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x48, 0x89, 0xD7, 0x49, 0x89, 0xC0, 0x49,
    0x01, 0xF0, 0x48, 0x11, 0xCF, 0x48, 0x8B, 0x44, 0x24, 0x60, 0x49, 0xF7, 0xE7, 0x4C, 0x89, 0xBC,
    0x24, 0xC8, 0x00, 0x00, 0x00, 0x48, 0x89, 0xD1] ++ bytes_l118081_1

theorem code_l118081 : ∀ x ∈ codeRange 0x118081 bytes_l118081, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x18081 88 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l118081_1

@[cfg_block] def b_l1184d0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1184d0 (movR64R64Effect 0x1184d0 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 54) (.exec 0x1184d0 (fun s => s.RIP = 0x1184d0) (movR64R64Effect 0x1184d0 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x1184d3 (movR64R64Effect 0x1184d3 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 56) (.exec 0x1184d3 (fun s => s.RIP = 0x1184d3) (movR64R64Effect 0x1184d3 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x1184d6 (callEffect (fun _ => 0x1145f0) 0x1184db) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x1184d6 (PushPre 0x1184d6 5) (callEffect (fun _ => 0x1145f0) 0x1184db) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x1184db⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ { target := .l1184db, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l1184d0 : List UInt8 :=
  [0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x15, 0xC1, 0xFF, 0xFF]

theorem code_l1184d0 : ∀ x ∈ codeRange 0x1184d0 bytes_l1184d0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x184d0 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1184db : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1184db (movR64M64Effect 0x1184db 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1184db (LoadPre 0x1184db (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1184db + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1184db 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x1184e0 (StorePre 0x1184e0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1184e0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1184e0 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x1184e5 (movR64M64Effect 0x1184e5 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x1184e5 (LoadPre 0x1184e5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1184e5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1184e5 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x1184ea (StorePre 0x1184ea 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1184ea + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1184ea 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x1184ef (movR64M64Effect 0x1184ef 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x1184ef (LoadPre 0x1184ef (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1184ef + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1184ef 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x1184f4 (StorePre 0x1184f4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1184f4 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1184f4 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x1184f9 (movR64M64Effect 0x1184f9 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x1184f9 (LoadPre 0x1184f9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1184f9 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1184f9 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x1184fe (movR64M64Effect 0x1184fe 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x1184fe (LoadPre 0x1184fe (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1184fe + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1184fe 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x118503 (StorePre 0x118503 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x118503 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x118503 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x118508 (StorePre 0x118508 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x118508 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x118508 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x11850c (decR64Effect 0x11850c 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[15]
    (.letOp (n := 69) (.out 0x11850c (decR64Effect 0x11850c 15) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.flag .ZF)) #v[15]
    (.letOp (n := 70) (.exec 0x11850c (fun s => s.RIP = 0x11850c) (decR64Effect 0x11850c 15) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[15]
    (.letOp (n := 71) (.pure (condOp 5)) #v[69]
    (.terminate (.condBr (Fin.last 71) ⟨.l1184d0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 68), (19, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩ ⟨.l118511, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 68), (19, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩))))))))))))))))))))

def bytes_l1184db : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x49, 0xFF, 0xCF, 0x75, 0xBF]

theorem code_l1184db : ∀ x ∈ codeRange 0x1184db bytes_l1184db, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x184db 54 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

def b_l118511_11 : Block Op Label signature Reg.count 538 :=
  .letOp (n := 538) (.out 0x11891b (addR64R64Effect 0x11891b 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[536, 532]
    (.letOp (n := 539) (.exec 0x11891b (fun s => s.RIP = 0x11891b) (addR64R64Effect 0x11891b 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[536, 532]
    (.letOp (n := 540) (.exec 0x11891e (StorePre 0x11891e 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x11891e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11891e 7 (.sib 4 none 0 .none)) (Reg.operands [.gpr 7, .gpr 4] [])) #v[366, 4]
    (.letOp (n := 541) (.exec 0x118922 (StorePre 0x118922 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x118922 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x118922 8 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[450, 4]
    (.letOp (n := 542) (.out 0x118927 (andR64R64Effect 0x118927 9 6) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 6] []) (.reg (.gpr 9))) #v[527, 364]
    (.letOp (n := 543) (.exec 0x118927 (fun s => s.RIP = 0x118927) (andR64R64Effect 0x118927 9 6) (Reg.operands [.gpr 9, .gpr 6] [])) #v[527, 364]
    (.letOp (n := 544) (.exec 0x11892a (StorePre 0x11892a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11892a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11892a 10 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[516, 4]
    (.letOp (n := 545) (.exec 0x11892f (StorePre 0x11892f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11892f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11892f 9 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[542, 4]
    (.letOp (n := 546) (.exec 0x118934 (StorePre 0x118934 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x118934 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x118934 1 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[538, 4]
    (.letOp (n := 547) (.out 0x118939 (movR32Imm32Effect 0x118939 6 15 0x2c) (EffectPart.reads (.reg (.gpr 15)) [] []) (.reg (.gpr 15))) #v[]
    (.letOp (n := 548) (.exec 0x118939 (fun s => s.RIP = 0x118939) (movR32Imm32Effect 0x118939 6 15 0x2c) (Reg.operands [] [])) #v[]
    (.letOp (n := 549) (.out 0x11893f (leaR64Effect 0x11893f 3 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 550) (.exec 0x11893f (fun s => s.RIP = 0x11893f) (leaR64Effect 0x11893f 3 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 551) (.out 0x118944 (movR64R64Effect 0x118944 14 4) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 552) (.exec 0x118944 (fun s => s.RIP = 0x118944) (movR64R64Effect 0x118944 14 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 553) (.exec 0x118947 (fun s => s.RIP = 0x118947) (fun _ => nopEffect 0x118947 9) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l118950, RegMap.args [(0, 534), (1, 538), (2, 532), (3, 549), (4, 4), (5, 459), (6, 364), (7, 366), (8, 450), (9, 542), (10, 516), (11, 482), (12, 446), (13, 473), (14, 551), (15, 547), (22, 22), (39, 39), (50, 50), (51, 51)] 554⟩)))))))))))))))))

def bytes_l118511_11 : List UInt8 :=
  [0x48, 0x01, 0xD1, 0x48, 0x89, 0x3C, 0x24, 0x4C, 0x89, 0x44, 0x24, 0x08, 0x49, 0x21, 0xF1, 0x4C,
    0x89, 0x54, 0x24, 0x10, 0x4C, 0x89, 0x4C, 0x24, 0x18, 0x48, 0x89, 0x4C, 0x24, 0x20, 0x41, 0xBF,
    0x2C, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x5C, 0x24, 0x28, 0x49, 0x89, 0xE6, 0x66, 0x0F, 0x1F, 0x84,
    0x00, 0x00, 0x00, 0x00, 0x00]

theorem code_l118511_11 : ∀ x ∈ codeRange 0x11891b bytes_l118511_11, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1891b 53 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

def b_l118511_10 : Block Op Label signature Reg.count 492 :=
  .letOp (n := 492) (.out 0x1188ca (addR64R64Effect 0x1188ca 10 12) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 12] []) (.reg (.gpr 10))) #v[487, 446]
    (.letOp (n := 493) (.out 0x1188ca (addR64R64Effect 0x1188ca 10 12) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 12] []) (.flag .CF)) #v[487, 446]
    (.letOp (n := 494) (.exec 0x1188ca (fun s => s.RIP = 0x1188ca) (addR64R64Effect 0x1188ca 10 12) (Reg.operands [.gpr 10, .gpr 12] [])) #v[487, 446]
    (.letOp (n := 495) (.out 0x1188cd (atFlags StatusFlags.CF (adcR64R64Effect 0x1188cd 15 14)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 15))) #v[490, 448, 493]
    (.letOp (n := 496) (.exec 0x1188cd (fun s => s.RIP = 0x1188cd) (atFlags StatusFlags.CF (adcR64R64Effect 0x1188cd 15 14)) (Reg.operands [.gpr 15, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[490, 448, 493]
    (.letOp (n := 497) (.out 0x1188d0 (addR64R64Effect 0x1188d0 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0] []) (.reg (.gpr 10))) #v[492, 484]
    (.letOp (n := 498) (.out 0x1188d0 (addR64R64Effect 0x1188d0 10 0) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 0] []) (.flag .CF)) #v[492, 484]
    (.letOp (n := 499) (.exec 0x1188d0 (fun s => s.RIP = 0x1188d0) (addR64R64Effect 0x1188d0 10 0) (Reg.operands [.gpr 10, .gpr 0] [])) #v[492, 484]
    (.letOp (n := 500) (.out 0x1188d3 (atFlags StatusFlags.CF (adcR64R64Effect 0x1188d3 15 2)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 15))) #v[495, 485, 498]
    (.letOp (n := 501) (.exec 0x1188d3 (fun s => s.RIP = 0x1188d3) (atFlags StatusFlags.CF (adcR64R64Effect 0x1188d3 15 2)) (Reg.operands [.gpr 15, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[495, 485, 498]
    (.letOp (n := 502) (.out 0x1188d6 (addR64R64Effect 0x1188d6 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9] []) (.reg (.gpr 10))) #v[497, 423]
    (.letOp (n := 503) (.out 0x1188d6 (addR64R64Effect 0x1188d6 10 9) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 9] []) (.flag .CF)) #v[497, 423]
    (.letOp (n := 504) (.exec 0x1188d6 (fun s => s.RIP = 0x1188d6) (addR64R64Effect 0x1188d6 10 9) (Reg.operands [.gpr 10, .gpr 9] [])) #v[497, 423]
    (.letOp (n := 505) (.out 0x1188d9 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1188d9 15 0x0)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 15))) #v[500, 503]
    (.letOp (n := 506) (.exec 0x1188d9 (fun s => s.RIP = 0x1188d9) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1188d9 15 0x0)) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[500, 503]
    (.letOp (n := 507) (.out 0x1188dd (shldR64R64Effect 0x1188dd 5 3 13 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[476, 473]
    (.letOp (n := 508) (.exec 0x1188dd (fun s => s.RIP = 0x1188dd) (shldR64R64Effect 0x1188dd 5 3 13 12) (Reg.operands [.gpr 3, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[476, 473]
    (.letOp (n := 509) (.out 0x1188e2 (shldR64R64Effect 0x1188e2 5 15 10 12) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[505, 502]
    (.letOp (n := 510) (.exec 0x1188e2 (fun s => s.RIP = 0x1188e2) (shldR64R64Effect 0x1188e2 5 15 10 12) (Reg.operands [.gpr 15, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[505, 502]
    (.letOp (n := 511) (.out 0x1188e7 (movR64R64Effect 0x1188e7 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[507]
    (.letOp (n := 512) (.exec 0x1188e7 (fun s => s.RIP = 0x1188e7) (movR64R64Effect 0x1188e7 0 3) (Reg.operands [.gpr 3] [])) #v[507]
    (.letOp (n := 513) (.out 0x1188ea (mulR64Effect 0x1188ea 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[482, 511]
    (.letOp (n := 514) (.out 0x1188ea (mulR64Effect 0x1188ea 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[482, 511]
    (.letOp (n := 515) (.exec 0x1188ea (fun s => s.RIP = 0x1188ea) (mulR64Effect 0x1188ea 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[482, 511]
    (.letOp (n := 516) (.out 0x1188ed (andR64R64Effect 0x1188ed 10 6) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 6] []) (.reg (.gpr 10))) #v[502, 364]
    (.letOp (n := 517) (.exec 0x1188ed (fun s => s.RIP = 0x1188ed) (andR64R64Effect 0x1188ed 10 6) (Reg.operands [.gpr 10, .gpr 6] [])) #v[502, 364]
    (.letOp (n := 518) (.out 0x1188f0 (movR64M64Effect 0x1188f0 9 (.sib 4 none 0 (.d32 0x178))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 519) (.exec 0x1188f0 (LoadPre 0x1188f0 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x178)) s (0x1188f0 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1188f0 9 (.sib 4 none 0 (.d32 0x178))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 520) (.out 0x1188f8 (andR64R64Effect 0x1188f8 9 6) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 6] []) (.reg (.gpr 9))) #v[518, 364]
    (.letOp (n := 521) (.exec 0x1188f8 (fun s => s.RIP = 0x1188f8) (andR64R64Effect 0x1188f8 9 6) (Reg.operands [.gpr 9, .gpr 6] [])) #v[518, 364]
    (.letOp (n := 522) (.out 0x1188fb (addR64R64Effect 0x1188fb 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0] []) (.reg (.gpr 9))) #v[520, 513]
    (.letOp (n := 523) (.out 0x1188fb (addR64R64Effect 0x1188fb 9 0) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 0] []) (.flag .CF)) #v[520, 513]
    (.letOp (n := 524) (.exec 0x1188fb (fun s => s.RIP = 0x1188fb) (addR64R64Effect 0x1188fb 9 0) (Reg.operands [.gpr 9, .gpr 0] [])) #v[520, 513]
    (.letOp (n := 525) (.out 0x1188fe (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1188fe 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[514, 523]
    (.letOp (n := 526) (.exec 0x1188fe (fun s => s.RIP = 0x1188fe) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1188fe 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[514, 523]
    (.letOp (n := 527) (.out 0x118902 (addR64R64Effect 0x118902 9 15) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 15] []) (.reg (.gpr 9))) #v[522, 509]
    (.letOp (n := 528) (.out 0x118902 (addR64R64Effect 0x118902 9 15) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 15] []) (.flag .CF)) #v[522, 509]
    (.letOp (n := 529) (.exec 0x118902 (fun s => s.RIP = 0x118902) (addR64R64Effect 0x118902 9 15) (Reg.operands [.gpr 9, .gpr 15] [])) #v[522, 509]
    (.letOp (n := 530) (.out 0x118905 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x118905 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[525, 528]
    (.letOp (n := 531) (.exec 0x118905 (fun s => s.RIP = 0x118905) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x118905 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[525, 528]
    (.letOp (n := 532) (.out 0x118909 (shldR64R64Effect 0x118909 5 2 9 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[530, 527]
    (.letOp (n := 533) (.exec 0x118909 (fun s => s.RIP = 0x118909) (shldR64R64Effect 0x118909 5 2 9 12) (Reg.operands [.gpr 2, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[530, 527]
    (.letOp (n := 534) (.out 0x11890e (movR64Imm64Effect 0x11890e 0 0xffffffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 535) (.exec 0x11890e (fun s => s.RIP = 0x11890e) (movR64Imm64Effect 0x11890e 0 0xffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 536) (.out 0x118918 (andR64R64Effect 0x118918 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[235, 534]
    (.letOp (n := 537) (.exec 0x118918 (fun s => s.RIP = 0x118918) (andR64R64Effect 0x118918 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[235, 534]
    (b_l118511_11))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l118511_10 : List UInt8 :=
  [0x4D, 0x01, 0xE2, 0x4D, 0x11, 0xF7, 0x49, 0x01, 0xC2, 0x49, 0x11, 0xD7, 0x4D, 0x01, 0xCA, 0x49,
    0x83, 0xD7, 0x00, 0x4C, 0x0F, 0xA4, 0xEB, 0x0C, 0x4D, 0x0F, 0xA4, 0xD7, 0x0C, 0x48, 0x89, 0xD8,
    0x49, 0xF7, 0xE3, 0x49, 0x21, 0xF2, 0x4C, 0x8B, 0x8C, 0x24, 0x78, 0x01, 0x00, 0x00, 0x49, 0x21,
    0xF1, 0x49, 0x01, 0xC1, 0x48, 0x83, 0xD2, 0x00, 0x4D, 0x01, 0xF9, 0x48, 0x83, 0xD2, 0x00, 0x4C,
    0x0F, 0xA4, 0xCA, 0x0C, 0x48, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x48, 0x21,
    0xC1] ++ bytes_l118511_11

theorem code_l118511_10 : ∀ x ∈ codeRange 0x1188ca bytes_l118511_10, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x188ca 81 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l118511_11

def b_l118511_9 : Block Op Label signature Reg.count 446 :=
  .letOp (n := 446) (.out 0x11886d (movR64R64Effect 0x11886d 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[443]
    (.letOp (n := 447) (.exec 0x11886d (fun s => s.RIP = 0x11886d) (movR64R64Effect 0x11886d 12 0) (Reg.operands [.gpr 0] [])) #v[443]
    (.letOp (n := 448) (.out 0x118870 (movR64R64Effect 0x118870 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[444]
    (.letOp (n := 449) (.exec 0x118870 (fun s => s.RIP = 0x118870) (movR64R64Effect 0x118870 14 2) (Reg.operands [.gpr 2] [])) #v[444]
    (.letOp (n := 450) (.out 0x118873 (andR64R64Effect 0x118873 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6] []) (.reg (.gpr 8))) #v[418, 364]
    (.letOp (n := 451) (.exec 0x118873 (fun s => s.RIP = 0x118873) (andR64R64Effect 0x118873 8 6) (Reg.operands [.gpr 8, .gpr 6] [])) #v[418, 364]
    (.letOp (n := 452) (.out 0x118876 (movR64M64Effect 0x118876 0 (.sib 4 none 0 (.d32 0xe8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 453) (.exec 0x118876 (LoadPre 0x118876 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x118876 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x118876 0 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 454) (.out 0x11887e (mulM64Effect 0x11887e 8 (.sib 4 none 0 (.d32 0x110))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[452, 4]
    (.letOp (n := 455) (.out 0x11887e (mulM64Effect 0x11887e 8 (.sib 4 none 0 (.d32 0x110))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[452, 4]
    (.letOp (n := 456) (.exec 0x11887e (LoadPre 0x11887e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x11887e + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x11887e 8 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[452, 4]
    (.letOp (n := 457) (.out 0x118886 (movR64R64Effect 0x118886 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[455]
    (.letOp (n := 458) (.exec 0x118886 (fun s => s.RIP = 0x118886) (movR64R64Effect 0x118886 3 2) (Reg.operands [.gpr 2] [])) #v[455]
    (.letOp (n := 459) (.out 0x118889 (movR64R64Effect 0x118889 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[454]
    (.letOp (n := 460) (.exec 0x118889 (fun s => s.RIP = 0x118889) (movR64R64Effect 0x118889 5 0) (Reg.operands [.gpr 0] [])) #v[454]
    (.letOp (n := 461) (.out 0x11888c (movR64M64Effect 0x11888c 0 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 462) (.exec 0x11888c (LoadPre 0x11888c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x11888c + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11888c 0 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 463) (.out 0x118894 (mulR64Effect 0x118894 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[379, 461]
    (.letOp (n := 464) (.out 0x118894 (mulR64Effect 0x118894 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[379, 461]
    (.letOp (n := 465) (.exec 0x118894 (fun s => s.RIP = 0x118894) (mulR64Effect 0x118894 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[379, 461]
    (.letOp (n := 466) (.out 0x118897 (movR64R64Effect 0x118897 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[463]
    (.letOp (n := 467) (.exec 0x118897 (fun s => s.RIP = 0x118897) (movR64R64Effect 0x118897 13 0) (Reg.operands [.gpr 0] [])) #v[463]
    (.letOp (n := 468) (.out 0x11889a (addR64R64Effect 0x11889a 13 5) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 5] []) (.reg (.gpr 13))) #v[466, 459]
    (.letOp (n := 469) (.out 0x11889a (addR64R64Effect 0x11889a 13 5) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 5] []) (.flag .CF)) #v[466, 459]
    (.letOp (n := 470) (.exec 0x11889a (fun s => s.RIP = 0x11889a) (addR64R64Effect 0x11889a 13 5) (Reg.operands [.gpr 13, .gpr 5] [])) #v[466, 459]
    (.letOp (n := 471) (.out 0x11889d (atFlags StatusFlags.CF (adcR64R64Effect 0x11889d 3 2)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[457, 464, 469]
    (.letOp (n := 472) (.exec 0x11889d (fun s => s.RIP = 0x11889d) (atFlags StatusFlags.CF (adcR64R64Effect 0x11889d 3 2)) (Reg.operands [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[457, 464, 469]
    (.letOp (n := 473) (.out 0x1188a0 (addR64R64Effect 0x1188a0 13 11) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 11] []) (.reg (.gpr 13))) #v[468, 399]
    (.letOp (n := 474) (.out 0x1188a0 (addR64R64Effect 0x1188a0 13 11) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 11] []) (.flag .CF)) #v[468, 399]
    (.letOp (n := 475) (.exec 0x1188a0 (fun s => s.RIP = 0x1188a0) (addR64R64Effect 0x1188a0 13 11) (Reg.operands [.gpr 13, .gpr 11] [])) #v[468, 399]
    (.letOp (n := 476) (.out 0x1188a3 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1188a3 3 0x0)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[471, 474]
    (.letOp (n := 477) (.exec 0x1188a3 (fun s => s.RIP = 0x1188a3) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1188a3 3 0x0)) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[471, 474]
    (.letOp (n := 478) (.out 0x1188a7 (movR64R64Effect 0x1188a7 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[473]
    (.letOp (n := 479) (.exec 0x1188a7 (fun s => s.RIP = 0x1188a7) (movR64R64Effect 0x1188a7 0 13) (Reg.operands [.gpr 13] [])) #v[473]
    (.letOp (n := 480) (.out 0x1188aa (andR64R64Effect 0x1188aa 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[478, 364]
    (.letOp (n := 481) (.exec 0x1188aa (fun s => s.RIP = 0x1188aa) (andR64R64Effect 0x1188aa 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[478, 364]
    (.letOp (n := 482) (.out 0x1188ad (movR64Imm64Effect 0x1188ad 11 0x1000003d10) (EffectPart.reads (.reg (.gpr 11)) [] []) (.reg (.gpr 11))) #v[]
    (.letOp (n := 483) (.exec 0x1188ad (fun s => s.RIP = 0x1188ad) (movR64Imm64Effect 0x1188ad 11 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 484) (.out 0x1188b7 (mulR64Effect 0x1188b7 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[482, 480]
    (.letOp (n := 485) (.out 0x1188b7 (mulR64Effect 0x1188b7 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[482, 480]
    (.letOp (n := 486) (.exec 0x1188b7 (fun s => s.RIP = 0x1188b7) (mulR64Effect 0x1188b7 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[482, 480]
    (.letOp (n := 487) (.out 0x1188ba (addR64M64Effect 0x1188ba 10 (.sib 4 none 0 (.d32 0x128))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 4] []) (.reg (.gpr 10))) #v[439, 4]
    (.letOp (n := 488) (.out 0x1188ba (addR64M64Effect 0x1188ba 10 (.sib 4 none 0 (.d32 0x128))) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 4] []) (.flag .CF)) #v[439, 4]
    (.letOp (n := 489) (.exec 0x1188ba (LoadPre 0x1188ba (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x1188ba + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x1188ba 10 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[439, 4]
    (.letOp (n := 490) (.out 0x1188c2 (atFlags StatusFlags.CF (adcR64M64Effect 0x1188c2 15 (.sib 4 none 0 (.d32 0xd8)))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 15))) #v[437, 4, 488]
    (.letOp (n := 491) (.exec 0x1188c2 (LoadPre 0x1188c2 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x1188c2 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x1188c2 15 (.sib 4 none 0 (.d32 0xd8)))) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[437, 4, 488]
    (b_l118511_10))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l118511_9 : List UInt8 :=
  [0x49, 0x89, 0xC4, 0x49, 0x89, 0xD6, 0x49, 0x21, 0xF0, 0x48, 0x8B, 0x84, 0x24, 0xE8, 0x00, 0x00,
    0x00, 0x48, 0xF7, 0xA4, 0x24, 0x10, 0x01, 0x00, 0x00, 0x48, 0x89, 0xD3, 0x48, 0x89, 0xC5, 0x48,
    0x8B, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE5, 0x49, 0x89, 0xC5, 0x49, 0x01, 0xED,
    0x48, 0x11, 0xD3, 0x4D, 0x01, 0xDD, 0x48, 0x83, 0xD3, 0x00, 0x4C, 0x89, 0xE8, 0x48, 0x21, 0xF0,
    0x49, 0xBB, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE3, 0x4C, 0x03, 0x94,
    0x24, 0x28, 0x01, 0x00, 0x00, 0x4C, 0x13, 0xBC, 0x24, 0xD8, 0x00, 0x00, 0x00] ++ bytes_l118511_10

theorem code_l118511_9 : ∀ x ∈ codeRange 0x11886d bytes_l118511_9, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1886d 93 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l118511_10

def b_l118511_8 : Block Op Label signature Reg.count 401 :=
  .letOp (n := 401) (.out 0x1187fa (andR64R64Effect 0x1187fa 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[394, 364]
    (.letOp (n := 402) (.exec 0x1187fa (fun s => s.RIP = 0x1187fa) (andR64R64Effect 0x1187fa 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[394, 364]
    (.letOp (n := 403) (.out 0x1187fd (movR64Imm64Effect 0x1187fd 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 404) (.exec 0x1187fd (fun s => s.RIP = 0x1187fd) (movR64Imm64Effect 0x1187fd 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 405) (.out 0x118807 (mulR64Effect 0x118807 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[403, 401]
    (.letOp (n := 406) (.out 0x118807 (mulR64Effect 0x118807 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[403, 401]
    (.letOp (n := 407) (.exec 0x118807 (fun s => s.RIP = 0x118807) (mulR64Effect 0x118807 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[403, 401]
    (.letOp (n := 408) (.out 0x11880a (addR64M64Effect 0x11880a 8 (.sib 4 none 0 (.d32 0x158))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 4] []) (.reg (.gpr 8))) #v[353, 4]
    (.letOp (n := 409) (.out 0x11880a (addR64M64Effect 0x11880a 8 (.sib 4 none 0 (.d32 0x158))) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 4] []) (.flag .CF)) #v[353, 4]
    (.letOp (n := 410) (.exec 0x11880a (LoadPre 0x11880a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x158)) s (0x11880a + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x11880a 8 (.sib 4 none 0 (.d32 0x158))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[353, 4]
    (.letOp (n := 411) (.out 0x118812 (atFlags StatusFlags.CF (adcR64M64Effect 0x118812 9 (.sib 4 none 0 (.d32 0x128)))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 9))) #v[351, 4, 409]
    (.letOp (n := 412) (.exec 0x118812 (LoadPre 0x118812 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x118812 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x118812 9 (.sib 4 none 0 (.d32 0x128)))) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[351, 4, 409]
    (.letOp (n := 413) (.out 0x11881a (addR64R64Effect 0x11881a 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[408, 405]
    (.letOp (n := 414) (.out 0x11881a (addR64R64Effect 0x11881a 8 0) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 0] []) (.flag .CF)) #v[408, 405]
    (.letOp (n := 415) (.exec 0x11881a (fun s => s.RIP = 0x11881a) (addR64R64Effect 0x11881a 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[408, 405]
    (.letOp (n := 416) (.out 0x11881d (atFlags StatusFlags.CF (adcR64R64Effect 0x11881d 9 2)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[411, 406, 414]
    (.letOp (n := 417) (.exec 0x11881d (fun s => s.RIP = 0x11881d) (atFlags StatusFlags.CF (adcR64R64Effect 0x11881d 9 2)) (Reg.operands [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[411, 406, 414]
    (.letOp (n := 418) (.out 0x118820 (addR64R64Effect 0x118820 8 3) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 3] []) (.reg (.gpr 8))) #v[413, 337]
    (.letOp (n := 419) (.out 0x118820 (addR64R64Effect 0x118820 8 3) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 3] []) (.flag .CF)) #v[413, 337]
    (.letOp (n := 420) (.exec 0x118820 (fun s => s.RIP = 0x118820) (addR64R64Effect 0x118820 8 3) (Reg.operands [.gpr 8, .gpr 3] [])) #v[413, 337]
    (.letOp (n := 421) (.out 0x118823 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x118823 9 0x0)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[416, 419]
    (.letOp (n := 422) (.exec 0x118823 (fun s => s.RIP = 0x118823) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x118823 9 0x0)) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[416, 419]
    (.letOp (n := 423) (.out 0x118827 (shldR64R64Effect 0x118827 5 9 8 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[421, 418]
    (.letOp (n := 424) (.exec 0x118827 (fun s => s.RIP = 0x118827) (shldR64R64Effect 0x118827 5 9 8 12) (Reg.operands [.gpr 9, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[421, 418]
    (.letOp (n := 425) (.out 0x11882c (movR64R64Effect 0x11882c 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[5]
    (.letOp (n := 426) (.exec 0x11882c (fun s => s.RIP = 0x11882c) (movR64R64Effect 0x11882c 0 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 427) (.out 0x11882f (mulM64Effect 0x11882f 8 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[425, 4]
    (.letOp (n := 428) (.out 0x11882f (mulM64Effect 0x11882f 8 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[425, 4]
    (.letOp (n := 429) (.exec 0x11882f (LoadPre 0x11882f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x11882f + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x11882f 8 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[425, 4]
    (.letOp (n := 430) (.exec 0x118837 (StorePre 0x118837 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x118837 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x118837 2 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[428, 4]
    (.letOp (n := 431) (.exec 0x11883f (StorePre 0x11883f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x11883f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11883f 0 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[427, 4]
    (.letOp (n := 432) (.out 0x118847 (movR64M64Effect 0x118847 0 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 433) (.exec 0x118847 (LoadPre 0x118847 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x118847 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x118847 0 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 434) (.out 0x11884f (mulM64Effect 0x11884f 8 (.sib 4 none 0 (.d32 0x168))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[432, 4]
    (.letOp (n := 435) (.out 0x11884f (mulM64Effect 0x11884f 8 (.sib 4 none 0 (.d32 0x168))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[432, 4]
    (.letOp (n := 436) (.exec 0x11884f (LoadPre 0x11884f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x168)) s (0x11884f + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x11884f 8 (.sib 4 none 0 (.d32 0x168))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[432, 4]
    (.letOp (n := 437) (.out 0x118857 (movR64R64Effect 0x118857 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[435]
    (.letOp (n := 438) (.exec 0x118857 (fun s => s.RIP = 0x118857) (movR64R64Effect 0x118857 15 2) (Reg.operands [.gpr 2] [])) #v[435]
    (.letOp (n := 439) (.out 0x11885a (movR64R64Effect 0x11885a 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[434]
    (.letOp (n := 440) (.exec 0x11885a (fun s => s.RIP = 0x11885a) (movR64R64Effect 0x11885a 10 0) (Reg.operands [.gpr 0] [])) #v[434]
    (.letOp (n := 441) (.out 0x11885d (movR64M64Effect 0x11885d 0 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 442) (.exec 0x11885d (LoadPre 0x11885d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x11885d + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11885d 0 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 443) (.out 0x118865 (mulM64Effect 0x118865 8 (.sib 4 none 0 (.d32 0x118))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[441, 4]
    (.letOp (n := 444) (.out 0x118865 (mulM64Effect 0x118865 8 (.sib 4 none 0 (.d32 0x118))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[441, 4]
    (.letOp (n := 445) (.exec 0x118865 (LoadPre 0x118865 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x118865 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x118865 8 (.sib 4 none 0 (.d32 0x118))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[441, 4]
    (b_l118511_9)))))))))))))))))))))))))))))))))))))))))))))

def bytes_l118511_8 : List UInt8 :=
  [0x48, 0x21, 0xF0, 0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2,
    0x4C, 0x03, 0x84, 0x24, 0x58, 0x01, 0x00, 0x00, 0x4C, 0x13, 0x8C, 0x24, 0x28, 0x01, 0x00, 0x00,
    0x49, 0x01, 0xC0, 0x49, 0x11, 0xD1, 0x49, 0x01, 0xD8, 0x49, 0x83, 0xD1, 0x00, 0x4D, 0x0F, 0xA4,
    0xC1, 0x0C, 0x48, 0x89, 0xE8, 0x48, 0xF7, 0xA4, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x94,
    0x24, 0xD8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0x28, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x84,
    0x24, 0xB8, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xA4, 0x24, 0x68, 0x01, 0x00, 0x00, 0x49, 0x89, 0xD7,
    0x49, 0x89, 0xC2, 0x48, 0x8B, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xA4, 0x24, 0x18,
    0x01, 0x00, 0x00] ++ bytes_l118511_9

theorem code_l118511_8 : ∀ x ∈ codeRange 0x1187fa bytes_l118511_8, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x187fa 115 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l118511_9

def b_l118511_7 : Block Op Label signature Reg.count 355 :=
  .letOp (n := 355) (.out 0x11879b (movR64M64Effect 0x11879b 0 (.sib 4 none 0 (.d32 0xe8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 356) (.exec 0x11879b (LoadPre 0x11879b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x11879b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11879b 0 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 357) (.out 0x1187a3 (mulM64Effect 0x1187a3 8 (.sib 4 none 0 (.d32 0x118))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[355, 4]
    (.letOp (n := 358) (.out 0x1187a3 (mulM64Effect 0x1187a3 8 (.sib 4 none 0 (.d32 0x118))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[355, 4]
    (.letOp (n := 359) (.exec 0x1187a3 (LoadPre 0x1187a3 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x1187a3 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x1187a3 8 (.sib 4 none 0 (.d32 0x118))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[355, 4]
    (.letOp (n := 360) (.out 0x1187ab (movR64R64Effect 0x1187ab 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[357]
    (.letOp (n := 361) (.exec 0x1187ab (fun s => s.RIP = 0x1187ab) (movR64R64Effect 0x1187ab 14 0) (Reg.operands [.gpr 0] [])) #v[357]
    (.letOp (n := 362) (.out 0x1187ae (movR64R64Effect 0x1187ae 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[358]
    (.letOp (n := 363) (.exec 0x1187ae (fun s => s.RIP = 0x1187ae) (movR64R64Effect 0x1187ae 15 2) (Reg.operands [.gpr 2] [])) #v[358]
    (.letOp (n := 364) (.out 0x1187b1 (movR64Imm64Effect 0x1187b1 6 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 365) (.exec 0x1187b1 (fun s => s.RIP = 0x1187b1) (movR64Imm64Effect 0x1187b1 6 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 366) (.out 0x1187bb (andR64R64Effect 0x1187bb 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[332, 364]
    (.letOp (n := 367) (.exec 0x1187bb (fun s => s.RIP = 0x1187bb) (andR64R64Effect 0x1187bb 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[332, 364]
    (.letOp (n := 368) (.out 0x1187be (movR64M64Effect 0x1187be 0 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 369) (.exec 0x1187be (LoadPre 0x1187be (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x1187be + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1187be 0 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 370) (.out 0x1187c6 (mulM64Effect 0x1187c6 8 (.sib 4 none 0 (.d32 0x110))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[368, 4]
    (.letOp (n := 371) (.out 0x1187c6 (mulM64Effect 0x1187c6 8 (.sib 4 none 0 (.d32 0x110))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[368, 4]
    (.letOp (n := 372) (.exec 0x1187c6 (LoadPre 0x1187c6 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x1187c6 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x1187c6 8 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[368, 4]
    (.letOp (n := 373) (.out 0x1187ce (movR64R64Effect 0x1187ce 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[371]
    (.letOp (n := 374) (.exec 0x1187ce (fun s => s.RIP = 0x1187ce) (movR64R64Effect 0x1187ce 11 2) (Reg.operands [.gpr 2] [])) #v[371]
    (.letOp (n := 375) (.out 0x1187d1 (movR64R64Effect 0x1187d1 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[370]
    (.letOp (n := 376) (.exec 0x1187d1 (fun s => s.RIP = 0x1187d1) (movR64R64Effect 0x1187d1 12 0) (Reg.operands [.gpr 0] [])) #v[370]
    (.letOp (n := 377) (.out 0x1187d4 (movR64R64Effect 0x1187d4 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[5]
    (.letOp (n := 378) (.exec 0x1187d4 (fun s => s.RIP = 0x1187d4) (movR64R64Effect 0x1187d4 0 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 379) (.out 0x1187d7 (movR64M64Effect 0x1187d7 13 (.sib 4 none 0 (.d32 0xe0))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 380) (.exec 0x1187d7 (LoadPre 0x1187d7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x1187d7 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1187d7 13 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 381) (.out 0x1187df (mulR64Effect 0x1187df 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[379, 377]
    (.letOp (n := 382) (.out 0x1187df (mulR64Effect 0x1187df 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[379, 377]
    (.letOp (n := 383) (.exec 0x1187df (fun s => s.RIP = 0x1187df) (mulR64Effect 0x1187df 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[379, 377]
    (.letOp (n := 384) (.out 0x1187e2 (addR64R64Effect 0x1187e2 12 14) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 14] []) (.reg (.gpr 12))) #v[375, 360]
    (.letOp (n := 385) (.out 0x1187e2 (addR64R64Effect 0x1187e2 12 14) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 14] []) (.flag .CF)) #v[375, 360]
    (.letOp (n := 386) (.exec 0x1187e2 (fun s => s.RIP = 0x1187e2) (addR64R64Effect 0x1187e2 12 14) (Reg.operands [.gpr 12, .gpr 14] [])) #v[375, 360]
    (.letOp (n := 387) (.out 0x1187e5 (atFlags StatusFlags.CF (adcR64R64Effect 0x1187e5 11 15)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[373, 362, 385]
    (.letOp (n := 388) (.exec 0x1187e5 (fun s => s.RIP = 0x1187e5) (atFlags StatusFlags.CF (adcR64R64Effect 0x1187e5 11 15)) (Reg.operands [.gpr 11, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[373, 362, 385]
    (.letOp (n := 389) (.out 0x1187e8 (addR64R64Effect 0x1187e8 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 12] []) (.reg (.gpr 0))) #v[381, 384]
    (.letOp (n := 390) (.out 0x1187e8 (addR64R64Effect 0x1187e8 0 12) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 12] []) (.flag .CF)) #v[381, 384]
    (.letOp (n := 391) (.exec 0x1187e8 (fun s => s.RIP = 0x1187e8) (addR64R64Effect 0x1187e8 0 12) (Reg.operands [.gpr 0, .gpr 12] [])) #v[381, 384]
    (.letOp (n := 392) (.out 0x1187eb (atFlags StatusFlags.CF (adcR64R64Effect 0x1187eb 11 2)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[387, 382, 390]
    (.letOp (n := 393) (.exec 0x1187eb (fun s => s.RIP = 0x1187eb) (atFlags StatusFlags.CF (adcR64R64Effect 0x1187eb 11 2)) (Reg.operands [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[387, 382, 390]
    (.letOp (n := 394) (.out 0x1187ee (addR64R64Effect 0x1187ee 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[389, 313]
    (.letOp (n := 395) (.out 0x1187ee (addR64R64Effect 0x1187ee 0 10) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 10] []) (.flag .CF)) #v[389, 313]
    (.letOp (n := 396) (.exec 0x1187ee (fun s => s.RIP = 0x1187ee) (addR64R64Effect 0x1187ee 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[389, 313]
    (.letOp (n := 397) (.out 0x1187f1 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1187f1 11 0x0)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[392, 395]
    (.letOp (n := 398) (.exec 0x1187f1 (fun s => s.RIP = 0x1187f1) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1187f1 11 0x0)) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[392, 395]
    (.letOp (n := 399) (.out 0x1187f5 (shldR64R64Effect 0x1187f5 5 11 0 12) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[397, 394]
    (.letOp (n := 400) (.exec 0x1187f5 (fun s => s.RIP = 0x1187f5) (shldR64R64Effect 0x1187f5 5 11 0 12) (Reg.operands [.gpr 11, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[397, 394]
    (b_l118511_8))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l118511_7 : List UInt8 :=
  [0x48, 0x8B, 0x84, 0x24, 0xE8, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xA4, 0x24, 0x18, 0x01, 0x00, 0x00,
    0x49, 0x89, 0xC6, 0x49, 0x89, 0xD7, 0x48, 0xBE, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00,
    0x48, 0x21, 0xF7, 0x48, 0x8B, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xA4, 0x24, 0x10,
    0x01, 0x00, 0x00, 0x49, 0x89, 0xD3, 0x49, 0x89, 0xC4, 0x48, 0x89, 0xE8, 0x4C, 0x8B, 0xAC, 0x24,
    0xE0, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE5, 0x4D, 0x01, 0xF4, 0x4D, 0x11, 0xFB, 0x4C, 0x01, 0xE0,
    0x49, 0x11, 0xD3, 0x4C, 0x01, 0xD0, 0x49, 0x83, 0xD3, 0x00, 0x49, 0x0F, 0xA4, 0xC3, 0x0C] ++ bytes_l118511_8

theorem code_l118511_7 : ∀ x ∈ codeRange 0x11879b bytes_l118511_7, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1879b 95 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l118511_8

def b_l118511_6 : Block Op Label signature Reg.count 313 :=
  .letOp (n := 313) (.out 0x118733 (shldR64R64Effect 0x118733 5 10 0 12) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[311, 308]
    (.letOp (n := 314) (.exec 0x118733 (fun s => s.RIP = 0x118733) (shldR64R64Effect 0x118733 5 10 0 12) (Reg.operands [.gpr 10, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[311, 308]
    (.letOp (n := 315) (.out 0x118738 (shlR64Effect 0x118738 4 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[308]
    (.letOp (n := 316) (.exec 0x118738 (fun s => s.RIP = 0x118738) (shlR64Effect 0x118738 4 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[308]
    (.letOp (n := 317) (.out 0x11873c (movR64Imm64Effect 0x11873c 2 0xfffffffffffff0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 318) (.exec 0x11873c (fun s => s.RIP = 0x11873c) (movR64Imm64Effect 0x11873c 2 0xfffffffffffff0) (Reg.operands [] [])) #v[]
    (.letOp (n := 319) (.out 0x118746 (andR64R64Effect 0x118746 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[315, 317]
    (.letOp (n := 320) (.exec 0x118746 (fun s => s.RIP = 0x118746) (andR64R64Effect 0x118746 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[315, 317]
    (.letOp (n := 321) (.out 0x118749 (orR64R64Effect 0x118749 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[319, 266]
    (.letOp (n := 322) (.exec 0x118749 (fun s => s.RIP = 0x118749) (orR64R64Effect 0x118749 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[319, 266]
    (.letOp (n := 323) (.out 0x11874c (movR64Imm64Effect 0x11874c 2 0x1000003d1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 324) (.exec 0x11874c (fun s => s.RIP = 0x11874c) (movR64Imm64Effect 0x11874c 2 0x1000003d1) (Reg.operands [] [])) #v[]
    (.letOp (n := 325) (.out 0x118756 (mulR64Effect 0x118756 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[323, 321]
    (.letOp (n := 326) (.out 0x118756 (mulR64Effect 0x118756 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[323, 321]
    (.letOp (n := 327) (.exec 0x118756 (fun s => s.RIP = 0x118756) (mulR64Effect 0x118756 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[323, 321]
    (.letOp (n := 328) (.out 0x118759 (movR64R64Effect 0x118759 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[326]
    (.letOp (n := 329) (.exec 0x118759 (fun s => s.RIP = 0x118759) (movR64R64Effect 0x118759 3 2) (Reg.operands [.gpr 2] [])) #v[326]
    (.letOp (n := 330) (.out 0x11875c (movR64R64Effect 0x11875c 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[325]
    (.letOp (n := 331) (.exec 0x11875c (fun s => s.RIP = 0x11875c) (movR64R64Effect 0x11875c 7 0) (Reg.operands [.gpr 0] [])) #v[325]
    (.letOp (n := 332) (.out 0x11875f (addR64M64Effect 0x11875f 7 (.sib 4 none 0 (.d32 0x158))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 4] []) (.reg (.gpr 7))) #v[330, 4]
    (.letOp (n := 333) (.out 0x11875f (addR64M64Effect 0x11875f 7 (.sib 4 none 0 (.d32 0x158))) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 4] []) (.flag .CF)) #v[330, 4]
    (.letOp (n := 334) (.exec 0x11875f (LoadPre 0x11875f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x158)) s (0x11875f + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x11875f 7 (.sib 4 none 0 (.d32 0x158))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[330, 4]
    (.letOp (n := 335) (.out 0x118767 (atFlags StatusFlags.CF (adcR64M64Effect 0x118767 3 (.sib 4 none 0 (.d32 0x128)))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 3))) #v[328, 4, 333]
    (.letOp (n := 336) (.exec 0x118767 (LoadPre 0x118767 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x118767 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x118767 3 (.sib 4 none 0 (.d32 0x128)))) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[328, 4, 333]
    (.letOp (n := 337) (.out 0x11876f (shldR64R64Effect 0x11876f 5 3 7 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[335, 332]
    (.letOp (n := 338) (.exec 0x11876f (fun s => s.RIP = 0x11876f) (shldR64R64Effect 0x11876f 5 3 7 12) (Reg.operands [.gpr 3, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[335, 332]
    (.letOp (n := 339) (.out 0x118774 (movR64R64Effect 0x118774 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[286]
    (.letOp (n := 340) (.exec 0x118774 (fun s => s.RIP = 0x118774) (movR64R64Effect 0x118774 0 13) (Reg.operands [.gpr 13] [])) #v[286]
    (.letOp (n := 341) (.out 0x118777 (mulR64Effect 0x118777 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[248, 339]
    (.letOp (n := 342) (.out 0x118777 (mulR64Effect 0x118777 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[248, 339]
    (.letOp (n := 343) (.exec 0x118777 (fun s => s.RIP = 0x118777) (mulR64Effect 0x118777 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[248, 339]
    (.letOp (n := 344) (.exec 0x11877a (StorePre 0x11877a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x11877a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11877a 2 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[342, 4]
    (.letOp (n := 345) (.exec 0x118782 (StorePre 0x118782 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x158)) s (0x118782 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x118782 0 (.sib 4 none 0 (.d32 0x158))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[341, 4]
    (.letOp (n := 346) (.out 0x11878a (movR64M64Effect 0x11878a 0 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 347) (.exec 0x11878a (LoadPre 0x11878a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x11878a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11878a 0 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 348) (.out 0x118792 (mulR64Effect 0x118792 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[257, 346]
    (.letOp (n := 349) (.out 0x118792 (mulR64Effect 0x118792 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[257, 346]
    (.letOp (n := 350) (.exec 0x118792 (fun s => s.RIP = 0x118792) (mulR64Effect 0x118792 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[257, 346]
    (.letOp (n := 351) (.out 0x118795 (movR64R64Effect 0x118795 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[349]
    (.letOp (n := 352) (.exec 0x118795 (fun s => s.RIP = 0x118795) (movR64R64Effect 0x118795 9 2) (Reg.operands [.gpr 2] [])) #v[349]
    (.letOp (n := 353) (.out 0x118798 (movR64R64Effect 0x118798 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[348]
    (.letOp (n := 354) (.exec 0x118798 (fun s => s.RIP = 0x118798) (movR64R64Effect 0x118798 8 0) (Reg.operands [.gpr 0] [])) #v[348]
    (b_l118511_7))))))))))))))))))))))))))))))))))))))))))

def bytes_l118511_6 : List UInt8 :=
  [0x49, 0x0F, 0xA4, 0xC2, 0x0C, 0x48, 0xC1, 0xE0, 0x04, 0x48, 0xBA, 0xF0, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0xFF, 0x00, 0x48, 0x21, 0xD0, 0x48, 0x09, 0xF0, 0x48, 0xBA, 0xD1, 0x03, 0x00, 0x00, 0x01,
    0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x48, 0x89, 0xD3, 0x48, 0x89, 0xC7, 0x48, 0x03, 0xBC, 0x24,
    0x58, 0x01, 0x00, 0x00, 0x48, 0x13, 0x9C, 0x24, 0x28, 0x01, 0x00, 0x00, 0x48, 0x0F, 0xA4, 0xFB,
    0x0C, 0x4C, 0x89, 0xE8, 0x49, 0xF7, 0xE0, 0x48, 0x89, 0x94, 0x24, 0x28, 0x01, 0x00, 0x00, 0x48,
    0x89, 0x84, 0x24, 0x58, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00, 0x49,
    0xF7, 0xE1, 0x49, 0x89, 0xD1, 0x49, 0x89, 0xC0] ++ bytes_l118511_7

theorem code_l118511_6 : ∀ x ∈ codeRange 0x118733 bytes_l118511_6, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x18733 104 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l118511_7

def b_l118511_5 : Block Op Label signature Reg.count 266 :=
  .letOp (n := 266) (.out 0x1186dd (andR32Imm8Effect 0x1186dd 3 6 0xf) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[244]
    (.letOp (n := 267) (.exec 0x1186dd (fun s => s.RIP = 0x1186dd) (andR32Imm8Effect 0x1186dd 3 6 0xf) (Reg.operands [.gpr 6] [])) #v[244]
    (.letOp (n := 268) (.out 0x1186e0 (movR64M64Effect 0x1186e0 0 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 269) (.exec 0x1186e0 (LoadPre 0x1186e0 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x1186e0 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1186e0 0 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 270) (.out 0x1186e8 (mulM64Effect 0x1186e8 8 (.sib 4 none 0 (.d32 0x118))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[268, 4]
    (.letOp (n := 271) (.out 0x1186e8 (mulM64Effect 0x1186e8 8 (.sib 4 none 0 (.d32 0x118))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[268, 4]
    (.letOp (n := 272) (.exec 0x1186e8 (LoadPre 0x1186e8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x1186e8 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x1186e8 8 (.sib 4 none 0 (.d32 0x118))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[268, 4]
    (.letOp (n := 273) (.out 0x1186f0 (movR64R64Effect 0x1186f0 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[271]
    (.letOp (n := 274) (.exec 0x1186f0 (fun s => s.RIP = 0x1186f0) (movR64R64Effect 0x1186f0 10 2) (Reg.operands [.gpr 2] [])) #v[271]
    (.letOp (n := 275) (.out 0x1186f3 (movR64R64Effect 0x1186f3 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[270]
    (.letOp (n := 276) (.exec 0x1186f3 (fun s => s.RIP = 0x1186f3) (movR64R64Effect 0x1186f3 14 0) (Reg.operands [.gpr 0] [])) #v[270]
    (.letOp (n := 277) (.out 0x1186f6 (movR64R64Effect 0x1186f6 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[5]
    (.letOp (n := 278) (.exec 0x1186f6 (fun s => s.RIP = 0x1186f6) (movR64R64Effect 0x1186f6 0 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 279) (.out 0x1186f9 (mulM64Effect 0x1186f9 8 (.sib 4 none 0 (.d32 0x110))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[277, 4]
    (.letOp (n := 280) (.out 0x1186f9 (mulM64Effect 0x1186f9 8 (.sib 4 none 0 (.d32 0x110))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[277, 4]
    (.letOp (n := 281) (.exec 0x1186f9 (LoadPre 0x1186f9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x1186f9 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x1186f9 8 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[277, 4]
    (.letOp (n := 282) (.out 0x118701 (movR64R64Effect 0x118701 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[280]
    (.letOp (n := 283) (.exec 0x118701 (fun s => s.RIP = 0x118701) (movR64R64Effect 0x118701 15 2) (Reg.operands [.gpr 2] [])) #v[280]
    (.letOp (n := 284) (.out 0x118704 (movR64R64Effect 0x118704 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[279]
    (.letOp (n := 285) (.exec 0x118704 (fun s => s.RIP = 0x118704) (movR64R64Effect 0x118704 12 0) (Reg.operands [.gpr 0] [])) #v[279]
    (.letOp (n := 286) (.out 0x118707 (movR64M64Effect 0x118707 13 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 287) (.exec 0x118707 (LoadPre 0x118707 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x118707 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x118707 13 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 288) (.out 0x11870f (movR64R64Effect 0x11870f 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[286]
    (.letOp (n := 289) (.exec 0x11870f (fun s => s.RIP = 0x11870f) (movR64R64Effect 0x11870f 0 13) (Reg.operands [.gpr 13] [])) #v[286]
    (.letOp (n := 290) (.out 0x118712 (mulM64Effect 0x118712 8 (.sib 4 none 0 (.d32 0xe0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[288, 4]
    (.letOp (n := 291) (.out 0x118712 (mulM64Effect 0x118712 8 (.sib 4 none 0 (.d32 0xe0))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[288, 4]
    (.letOp (n := 292) (.exec 0x118712 (LoadPre 0x118712 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x118712 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x118712 8 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[288, 4]
    (.letOp (n := 293) (.out 0x11871a (addR64R64Effect 0x11871a 14 11) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 11] []) (.reg (.gpr 14))) #v[275, 262]
    (.letOp (n := 294) (.out 0x11871a (addR64R64Effect 0x11871a 14 11) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 11] []) (.flag .CF)) #v[275, 262]
    (.letOp (n := 295) (.exec 0x11871a (fun s => s.RIP = 0x11871a) (addR64R64Effect 0x11871a 14 11) (Reg.operands [.gpr 14, .gpr 11] [])) #v[275, 262]
    (.letOp (n := 296) (.out 0x11871d (atFlags StatusFlags.CF (adcR64R64Effect 0x11871d 10 3)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[273, 264, 294]
    (.letOp (n := 297) (.exec 0x11871d (fun s => s.RIP = 0x11871d) (atFlags StatusFlags.CF (adcR64R64Effect 0x11871d 10 3)) (Reg.operands [.gpr 10, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[273, 264, 294]
    (.letOp (n := 298) (.out 0x118720 (addR64R64Effect 0x118720 14 12) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 12] []) (.reg (.gpr 14))) #v[293, 284]
    (.letOp (n := 299) (.out 0x118720 (addR64R64Effect 0x118720 14 12) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 12] []) (.flag .CF)) #v[293, 284]
    (.letOp (n := 300) (.exec 0x118720 (fun s => s.RIP = 0x118720) (addR64R64Effect 0x118720 14 12) (Reg.operands [.gpr 14, .gpr 12] [])) #v[293, 284]
    (.letOp (n := 301) (.out 0x118723 (atFlags StatusFlags.CF (adcR64R64Effect 0x118723 10 15)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[296, 282, 299]
    (.letOp (n := 302) (.exec 0x118723 (fun s => s.RIP = 0x118723) (atFlags StatusFlags.CF (adcR64R64Effect 0x118723 10 15)) (Reg.operands [.gpr 10, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[296, 282, 299]
    (.letOp (n := 303) (.out 0x118726 (addR64R64Effect 0x118726 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[290, 298]
    (.letOp (n := 304) (.out 0x118726 (addR64R64Effect 0x118726 0 14) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 14] []) (.flag .CF)) #v[290, 298]
    (.letOp (n := 305) (.exec 0x118726 (fun s => s.RIP = 0x118726) (addR64R64Effect 0x118726 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[290, 298]
    (.letOp (n := 306) (.out 0x118729 (atFlags StatusFlags.CF (adcR64R64Effect 0x118729 10 2)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[301, 291, 304]
    (.letOp (n := 307) (.exec 0x118729 (fun s => s.RIP = 0x118729) (atFlags StatusFlags.CF (adcR64R64Effect 0x118729 10 2)) (Reg.operands [.gpr 10, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[301, 291, 304]
    (.letOp (n := 308) (.out 0x11872c (addR64R64Effect 0x11872c 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[303, 240]
    (.letOp (n := 309) (.out 0x11872c (addR64R64Effect 0x11872c 0 7) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 7] []) (.flag .CF)) #v[303, 240]
    (.letOp (n := 310) (.exec 0x11872c (fun s => s.RIP = 0x11872c) (addR64R64Effect 0x11872c 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[303, 240]
    (.letOp (n := 311) (.out 0x11872f (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11872f 10 0x0)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[306, 309]
    (.letOp (n := 312) (.exec 0x11872f (fun s => s.RIP = 0x11872f) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11872f 10 0x0)) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[306, 309]
    (b_l118511_6)))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l118511_5 : List UInt8 :=
  [0x83, 0xE6, 0x0F, 0x48, 0x8B, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xA4, 0x24, 0x18,
    0x01, 0x00, 0x00, 0x49, 0x89, 0xD2, 0x49, 0x89, 0xC6, 0x48, 0x89, 0xE8, 0x48, 0xF7, 0xA4, 0x24,
    0x10, 0x01, 0x00, 0x00, 0x49, 0x89, 0xD7, 0x49, 0x89, 0xC4, 0x4C, 0x8B, 0xAC, 0x24, 0xB8, 0x00,
    0x00, 0x00, 0x4C, 0x89, 0xE8, 0x48, 0xF7, 0xA4, 0x24, 0xE0, 0x00, 0x00, 0x00, 0x4D, 0x01, 0xDE,
    0x49, 0x11, 0xDA, 0x4D, 0x01, 0xE6, 0x4D, 0x11, 0xFA, 0x4C, 0x01, 0xF0, 0x49, 0x11, 0xD2, 0x48,
    0x01, 0xF8, 0x49, 0x83, 0xD2, 0x00] ++ bytes_l118511_6

theorem code_l118511_5 : ∀ x ∈ codeRange 0x1186dd bytes_l118511_5, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x186dd 86 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l118511_6

def b_l118511_4 : Block Op Label signature Reg.count 223 :=
  .letOp (n := 223) (.out 0x118684 (atFlags StatusFlags.CF (adcR64R64Effect 0x118684 7 12)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[218, 182, 221]
    (.letOp (n := 224) (.exec 0x118684 (fun s => s.RIP = 0x118684) (atFlags StatusFlags.CF (adcR64R64Effect 0x118684 7 12)) (Reg.operands [.gpr 7, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[218, 182, 221]
    (.letOp (n := 225) (.out 0x118687 (addR64R64Effect 0x118687 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 14] []) (.reg (.gpr 1))) #v[220, 193]
    (.letOp (n := 226) (.out 0x118687 (addR64R64Effect 0x118687 1 14) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 14] []) (.flag .CF)) #v[220, 193]
    (.letOp (n := 227) (.exec 0x118687 (fun s => s.RIP = 0x118687) (addR64R64Effect 0x118687 1 14) (Reg.operands [.gpr 1, .gpr 14] [])) #v[220, 193]
    (.letOp (n := 228) (.out 0x11868a (atFlags StatusFlags.CF (adcR64R64Effect 0x11868a 7 15)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[223, 195, 226]
    (.letOp (n := 229) (.exec 0x11868a (fun s => s.RIP = 0x11868a) (atFlags StatusFlags.CF (adcR64R64Effect 0x11868a 7 15)) (Reg.operands [.gpr 7, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[223, 195, 226]
    (.letOp (n := 230) (.out 0x11868d (addR64R64Effect 0x11868d 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[225, 205]
    (.letOp (n := 231) (.out 0x11868d (addR64R64Effect 0x11868d 1 0) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 0] []) (.flag .CF)) #v[225, 205]
    (.letOp (n := 232) (.exec 0x11868d (fun s => s.RIP = 0x11868d) (addR64R64Effect 0x11868d 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[225, 205]
    (.letOp (n := 233) (.out 0x118690 (atFlags StatusFlags.CF (adcR64R64Effect 0x118690 7 8)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[228, 208, 231]
    (.letOp (n := 234) (.exec 0x118690 (fun s => s.RIP = 0x118690) (atFlags StatusFlags.CF (adcR64R64Effect 0x118690 7 8)) (Reg.operands [.gpr 7, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[228, 208, 231]
    (.letOp (n := 235) (.out 0x118693 (addR64R64Effect 0x118693 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 9] []) (.reg (.gpr 1))) #v[230, 151]
    (.letOp (n := 236) (.out 0x118693 (addR64R64Effect 0x118693 1 9) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 9] []) (.flag .CF)) #v[230, 151]
    (.letOp (n := 237) (.exec 0x118693 (fun s => s.RIP = 0x118693) (addR64R64Effect 0x118693 1 9) (Reg.operands [.gpr 1, .gpr 9] [])) #v[230, 151]
    (.letOp (n := 238) (.out 0x118696 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x118696 7 0x0)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[233, 236]
    (.letOp (n := 239) (.exec 0x118696 (fun s => s.RIP = 0x118696) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x118696 7 0x0)) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[233, 236]
    (.letOp (n := 240) (.out 0x11869a (shldR64R64Effect 0x11869a 5 7 1 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[238, 235]
    (.letOp (n := 241) (.exec 0x11869a (fun s => s.RIP = 0x11869a) (shldR64R64Effect 0x11869a 5 7 1 12) (Reg.operands [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[238, 235]
    (.letOp (n := 242) (.out 0x11869f (movR64R64Effect 0x11869f 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 1] []) (.reg (.gpr 6))) #v[235]
    (.letOp (n := 243) (.exec 0x11869f (fun s => s.RIP = 0x11869f) (movR64R64Effect 0x11869f 6 1) (Reg.operands [.gpr 1] [])) #v[235]
    (.letOp (n := 244) (.out 0x1186a2 (shrR64Effect 0x1186a2 4 6 48) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[242]
    (.letOp (n := 245) (.exec 0x1186a2 (fun s => s.RIP = 0x1186a2) (shrR64Effect 0x1186a2 4 6 48) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[242]
    (.letOp (n := 246) (.out 0x1186a6 (movR64R64Effect 0x1186a6 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[186]
    (.letOp (n := 247) (.exec 0x1186a6 (fun s => s.RIP = 0x1186a6) (movR64R64Effect 0x1186a6 0 13) (Reg.operands [.gpr 13] [])) #v[186]
    (.letOp (n := 248) (.out 0x1186a9 (movR64M64Effect 0x1186a9 8 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 249) (.exec 0x1186a9 (LoadPre 0x1186a9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x1186a9 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1186a9 8 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 250) (.out 0x1186b1 (mulR64Effect 0x1186b1 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[248, 246]
    (.letOp (n := 251) (.out 0x1186b1 (mulR64Effect 0x1186b1 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[248, 246]
    (.letOp (n := 252) (.exec 0x1186b1 (fun s => s.RIP = 0x1186b1) (mulR64Effect 0x1186b1 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[248, 246]
    (.letOp (n := 253) (.exec 0x1186b4 (StorePre 0x1186b4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x1186b4 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1186b4 2 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[251, 4]
    (.letOp (n := 254) (.exec 0x1186bc (StorePre 0x1186bc 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x158)) s (0x1186bc + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1186bc 0 (.sib 4 none 0 (.d32 0x158))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[250, 4]
    (.letOp (n := 255) (.out 0x1186c4 (movR64M64Effect 0x1186c4 0 (.sib 4 none 0 (.d32 0xe8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 256) (.exec 0x1186c4 (LoadPre 0x1186c4 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x1186c4 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1186c4 0 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 257) (.out 0x1186cc (movR64M64Effect 0x1186cc 9 (.sib 4 none 0 (.d32 0x168))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 258) (.exec 0x1186cc (LoadPre 0x1186cc (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x168)) s (0x1186cc + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1186cc 9 (.sib 4 none 0 (.d32 0x168))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 259) (.out 0x1186d4 (mulR64Effect 0x1186d4 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[257, 255]
    (.letOp (n := 260) (.out 0x1186d4 (mulR64Effect 0x1186d4 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[257, 255]
    (.letOp (n := 261) (.exec 0x1186d4 (fun s => s.RIP = 0x1186d4) (mulR64Effect 0x1186d4 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[257, 255]
    (.letOp (n := 262) (.out 0x1186d7 (movR64R64Effect 0x1186d7 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[259]
    (.letOp (n := 263) (.exec 0x1186d7 (fun s => s.RIP = 0x1186d7) (movR64R64Effect 0x1186d7 11 0) (Reg.operands [.gpr 0] [])) #v[259]
    (.letOp (n := 264) (.out 0x1186da (movR64R64Effect 0x1186da 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[260]
    (.letOp (n := 265) (.exec 0x1186da (fun s => s.RIP = 0x1186da) (movR64R64Effect 0x1186da 3 2) (Reg.operands [.gpr 2] [])) #v[260]
    (b_l118511_5)))))))))))))))))))))))))))))))))))))))))))

def bytes_l118511_4 : List UInt8 :=
  [0x4C, 0x11, 0xE7, 0x4C, 0x01, 0xF1, 0x4C, 0x11, 0xFF, 0x48, 0x01, 0xC1, 0x4C, 0x11, 0xC7, 0x4C,
    0x01, 0xC9, 0x48, 0x83, 0xD7, 0x00, 0x48, 0x0F, 0xA4, 0xCF, 0x0C, 0x48, 0x89, 0xCE, 0x48, 0xC1,
    0xEE, 0x30, 0x4C, 0x89, 0xE8, 0x4C, 0x8B, 0x84, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE0,
    0x48, 0x89, 0x94, 0x24, 0x28, 0x01, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0x58, 0x01, 0x00, 0x00,
    0x48, 0x8B, 0x84, 0x24, 0xE8, 0x00, 0x00, 0x00, 0x4C, 0x8B, 0x8C, 0x24, 0x68, 0x01, 0x00, 0x00,
    0x49, 0xF7, 0xE1, 0x49, 0x89, 0xC3, 0x48, 0x89, 0xD3] ++ bytes_l118511_5

theorem code_l118511_4 : ∀ x ∈ codeRange 0x118684 bytes_l118511_4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x18684 89 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l118511_5

def b_l118511_3 : Block Op Label signature Reg.count 177 :=
  .letOp (n := 177) (.out 0x118626 (movR64M64Effect 0x118626 0 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 178) (.exec 0x118626 (LoadPre 0x118626 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x118626 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x118626 0 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 179) (.out 0x11862e (mulR64Effect 0x11862e 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[59, 177]
    (.letOp (n := 180) (.out 0x11862e (mulR64Effect 0x11862e 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[59, 177]
    (.letOp (n := 181) (.exec 0x11862e (fun s => s.RIP = 0x11862e) (mulR64Effect 0x11862e 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[59, 177]
    (.letOp (n := 182) (.out 0x118631 (movR64R64Effect 0x118631 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 2] []) (.reg (.gpr 12))) #v[180]
    (.letOp (n := 183) (.exec 0x118631 (fun s => s.RIP = 0x118631) (movR64R64Effect 0x118631 12 2) (Reg.operands [.gpr 2] [])) #v[180]
    (.letOp (n := 184) (.out 0x118634 (movR64R64Effect 0x118634 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[179]
    (.letOp (n := 185) (.exec 0x118634 (fun s => s.RIP = 0x118634) (movR64R64Effect 0x118634 3 0) (Reg.operands [.gpr 0] [])) #v[179]
    (.letOp (n := 186) (.out 0x118637 (movR64M64Effect 0x118637 13 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 187) (.exec 0x118637 (LoadPre 0x118637 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x118637 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x118637 13 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 188) (.out 0x11863f (movR64R64Effect 0x11863f 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[186]
    (.letOp (n := 189) (.exec 0x11863f (fun s => s.RIP = 0x11863f) (movR64R64Effect 0x11863f 0 13) (Reg.operands [.gpr 13] [])) #v[186]
    (.letOp (n := 190) (.out 0x118642 (mulR64Effect 0x118642 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6, .gpr 0] []) (.reg (.gpr 0))) #v[122, 188]
    (.letOp (n := 191) (.out 0x118642 (mulR64Effect 0x118642 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6, .gpr 0] []) (.reg (.gpr 2))) #v[122, 188]
    (.letOp (n := 192) (.exec 0x118642 (fun s => s.RIP = 0x118642) (mulR64Effect 0x118642 6) (Reg.operands [.gpr 6, .gpr 0] [])) #v[122, 188]
    (.letOp (n := 193) (.out 0x118645 (movR64R64Effect 0x118645 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[190]
    (.letOp (n := 194) (.exec 0x118645 (fun s => s.RIP = 0x118645) (movR64R64Effect 0x118645 14 0) (Reg.operands [.gpr 0] [])) #v[190]
    (.letOp (n := 195) (.out 0x118648 (movR64R64Effect 0x118648 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[191]
    (.letOp (n := 196) (.exec 0x118648 (fun s => s.RIP = 0x118648) (movR64R64Effect 0x118648 15 2) (Reg.operands [.gpr 2] [])) #v[191]
    (.letOp (n := 197) (.out 0x11864b (shrR64Effect 0x11864b 4 8 52) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[128]
    (.letOp (n := 198) (.exec 0x11864b (fun s => s.RIP = 0x11864b) (shrR64Effect 0x11864b 4 8 52) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[128]
    (.letOp (n := 199) (.out 0x11864f (movR64Imm64Effect 0x11864f 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 200) (.exec 0x11864f (fun s => s.RIP = 0x11864f) (movR64Imm64Effect 0x11864f 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 201) (.out 0x118659 (imulR64R64Effect 0x118659 4 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2] []) (.reg (.gpr 8))) #v[197, 199]
    (.letOp (n := 202) (.exec 0x118659 (fun s => s.RIP = 0x118659) (imulR64R64Effect 0x118659 4 8 2) (Reg.operands [.gpr 8, .gpr 2] [])) #v[197, 199]
    (.letOp (n := 203) (.out 0x11865d (movR64R64Effect 0x11865d 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[132]
    (.letOp (n := 204) (.exec 0x11865d (fun s => s.RIP = 0x11865d) (movR64R64Effect 0x11865d 0 10) (Reg.operands [.gpr 10] [])) #v[132]
    (.letOp (n := 205) (.out 0x118660 (mulR64Effect 0x118660 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[199, 203]
    (.letOp (n := 206) (.out 0x118660 (mulR64Effect 0x118660 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[199, 203]
    (.letOp (n := 207) (.exec 0x118660 (fun s => s.RIP = 0x118660) (mulR64Effect 0x118660 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[199, 203]
    (.letOp (n := 208) (.out 0x118663 (addR64R64Effect 0x118663 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2] []) (.reg (.gpr 8))) #v[201, 206]
    (.letOp (n := 209) (.exec 0x118663 (fun s => s.RIP = 0x118663) (addR64R64Effect 0x118663 8 2) (Reg.operands [.gpr 8, .gpr 2] [])) #v[201, 206]
    (.letOp (n := 210) (.out 0x118666 (addR64M64Effect 0x118666 1 (.sib 4 none 0 (.d32 0x158))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 4] []) (.reg (.gpr 1))) #v[167, 4]
    (.letOp (n := 211) (.out 0x118666 (addR64M64Effect 0x118666 1 (.sib 4 none 0 (.d32 0x158))) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 4] []) (.flag .CF)) #v[167, 4]
    (.letOp (n := 212) (.exec 0x118666 (LoadPre 0x118666 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x158)) s (0x118666 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x118666 1 (.sib 4 none 0 (.d32 0x158))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[167, 4]
    (.letOp (n := 213) (.out 0x11866e (atFlags StatusFlags.CF (adcR64M64Effect 0x11866e 7 (.sib 4 none 0 (.d32 0x128)))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 7))) #v[165, 4, 211]
    (.letOp (n := 214) (.exec 0x11866e (LoadPre 0x11866e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x11866e + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x11866e 7 (.sib 4 none 0 (.d32 0x128)))) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[165, 4, 211]
    (.letOp (n := 215) (.out 0x118676 (addR64R64Effect 0x118676 1 11) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 11] []) (.reg (.gpr 1))) #v[210, 175]
    (.letOp (n := 216) (.out 0x118676 (addR64R64Effect 0x118676 1 11) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 11] []) (.flag .CF)) #v[210, 175]
    (.letOp (n := 217) (.exec 0x118676 (fun s => s.RIP = 0x118676) (addR64R64Effect 0x118676 1 11) (Reg.operands [.gpr 1, .gpr 11] [])) #v[210, 175]
    (.letOp (n := 218) (.out 0x118679 (atFlags StatusFlags.CF (adcR64M64Effect 0x118679 7 (.sib 4 none 0 (.d32 0x170)))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 7))) #v[213, 4, 216]
    (.letOp (n := 219) (.exec 0x118679 (LoadPre 0x118679 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x170)) s (0x118679 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x118679 7 (.sib 4 none 0 (.d32 0x170)))) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[213, 4, 216]
    (.letOp (n := 220) (.out 0x118681 (addR64R64Effect 0x118681 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 3] []) (.reg (.gpr 1))) #v[215, 184]
    (.letOp (n := 221) (.out 0x118681 (addR64R64Effect 0x118681 1 3) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 3] []) (.flag .CF)) #v[215, 184]
    (.letOp (n := 222) (.exec 0x118681 (fun s => s.RIP = 0x118681) (addR64R64Effect 0x118681 1 3) (Reg.operands [.gpr 1, .gpr 3] [])) #v[215, 184]
    (b_l118511_4))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l118511_3 : List UInt8 :=
  [0x48, 0x8B, 0x84, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE5, 0x49, 0x89, 0xD4, 0x48, 0x89,
    0xC3, 0x4C, 0x8B, 0xAC, 0x24, 0x98, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xE8, 0x48, 0xF7, 0xE6, 0x49,
    0x89, 0xC6, 0x49, 0x89, 0xD7, 0x49, 0xC1, 0xE8, 0x34, 0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10,
    0x00, 0x00, 0x00, 0x4C, 0x0F, 0xAF, 0xC2, 0x4C, 0x89, 0xD0, 0x48, 0xF7, 0xE2, 0x49, 0x01, 0xD0,
    0x48, 0x03, 0x8C, 0x24, 0x58, 0x01, 0x00, 0x00, 0x48, 0x13, 0xBC, 0x24, 0x28, 0x01, 0x00, 0x00,
    0x4C, 0x01, 0xD9, 0x48, 0x13, 0xBC, 0x24, 0x70, 0x01, 0x00, 0x00, 0x48, 0x01, 0xD9] ++ bytes_l118511_4

theorem code_l118511_3 : ∀ x ∈ codeRange 0x118626 bytes_l118511_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x18626 94 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l118511_4

def b_l118511_2 : Block Op Label signature Reg.count 136 :=
  .letOp (n := 136) (.out 0x1185c8 (andR64R64Effect 0x1185c8 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[125, 134]
    (.letOp (n := 137) (.exec 0x1185c8 (fun s => s.RIP = 0x1185c8) (andR64R64Effect 0x1185c8 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[125, 134]
    (.letOp (n := 138) (.out 0x1185cb (movR64Imm64Effect 0x1185cb 1 0x1000003d10) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 139) (.exec 0x1185cb (fun s => s.RIP = 0x1185cb) (movR64Imm64Effect 0x1185cb 1 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 140) (.out 0x1185d5 (mulR64Effect 0x1185d5 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[138, 136]
    (.letOp (n := 141) (.out 0x1185d5 (mulR64Effect 0x1185d5 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[138, 136]
    (.letOp (n := 142) (.exec 0x1185d5 (fun s => s.RIP = 0x1185d5) (mulR64Effect 0x1185d5 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[138, 136]
    (.letOp (n := 143) (.out 0x1185d8 (movR64R64Effect 0x1185d8 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[141]
    (.letOp (n := 144) (.exec 0x1185d8 (fun s => s.RIP = 0x1185d8) (movR64R64Effect 0x1185d8 9 2) (Reg.operands [.gpr 2] [])) #v[141]
    (.letOp (n := 145) (.out 0x1185db (addR64R64Effect 0x1185db 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[140, 113]
    (.letOp (n := 146) (.out 0x1185db (addR64R64Effect 0x1185db 0 11) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 11] []) (.flag .CF)) #v[140, 113]
    (.letOp (n := 147) (.exec 0x1185db (fun s => s.RIP = 0x1185db) (addR64R64Effect 0x1185db 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[140, 113]
    (.letOp (n := 148) (.exec 0x1185de (StorePre 0x1185de 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x178)) s (0x1185de + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1185de 0 (.sib 4 none 0 (.d32 0x178))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[145, 4]
    (.letOp (n := 149) (.out 0x1185e6 (atFlags StatusFlags.CF (adcR64R64Effect 0x1185e6 9 7)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[143, 116, 146]
    (.letOp (n := 150) (.exec 0x1185e6 (fun s => s.RIP = 0x1185e6) (atFlags StatusFlags.CF (adcR64R64Effect 0x1185e6 9 7)) (Reg.operands [.gpr 9, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[143, 116, 146]
    (.letOp (n := 151) (.out 0x1185e9 (shldR64R64Effect 0x1185e9 5 9 0 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[149, 145]
    (.letOp (n := 152) (.exec 0x1185e9 (fun s => s.RIP = 0x1185e9) (shldR64R64Effect 0x1185e9 5 9 0 12) (Reg.operands [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[149, 145]
    (.letOp (n := 153) (.out 0x1185ee (movR64R64Effect 0x1185ee 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[118]
    (.letOp (n := 154) (.exec 0x1185ee (fun s => s.RIP = 0x1185ee) (movR64R64Effect 0x1185ee 0 3) (Reg.operands [.gpr 3] [])) #v[118]
    (.letOp (n := 155) (.out 0x1185f1 (mulR64Effect 0x1185f1 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15, .gpr 0] []) (.reg (.gpr 0))) #v[53, 153]
    (.letOp (n := 156) (.out 0x1185f1 (mulR64Effect 0x1185f1 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15, .gpr 0] []) (.reg (.gpr 2))) #v[53, 153]
    (.letOp (n := 157) (.exec 0x1185f1 (fun s => s.RIP = 0x1185f1) (mulR64Effect 0x1185f1 15) (Reg.operands [.gpr 15, .gpr 0] [])) #v[53, 153]
    (.letOp (n := 158) (.exec 0x1185f4 (StorePre 0x1185f4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x1185f4 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1185f4 2 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[156, 4]
    (.letOp (n := 159) (.exec 0x1185fc (StorePre 0x1185fc 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x158)) s (0x1185fc + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1185fc 0 (.sib 4 none 0 (.d32 0x158))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[155, 4]
    (.letOp (n := 160) (.out 0x118604 (movR64M64Effect 0x118604 0 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 161) (.exec 0x118604 (LoadPre 0x118604 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x118604 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x118604 0 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 162) (.out 0x11860c (mulR64Effect 0x11860c 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[55, 160]
    (.letOp (n := 163) (.out 0x11860c (mulR64Effect 0x11860c 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[55, 160]
    (.letOp (n := 164) (.exec 0x11860c (fun s => s.RIP = 0x11860c) (mulR64Effect 0x11860c 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[55, 160]
    (.letOp (n := 165) (.out 0x11860f (movR64R64Effect 0x11860f 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[163]
    (.letOp (n := 166) (.exec 0x11860f (fun s => s.RIP = 0x11860f) (movR64R64Effect 0x11860f 7 2) (Reg.operands [.gpr 2] [])) #v[163]
    (.letOp (n := 167) (.out 0x118612 (movR64R64Effect 0x118612 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[162]
    (.letOp (n := 168) (.exec 0x118612 (fun s => s.RIP = 0x118612) (movR64R64Effect 0x118612 1 0) (Reg.operands [.gpr 0] [])) #v[162]
    (.letOp (n := 169) (.out 0x118615 (movR64R64Effect 0x118615 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[5]
    (.letOp (n := 170) (.exec 0x118615 (fun s => s.RIP = 0x118615) (movR64R64Effect 0x118615 0 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 171) (.out 0x118618 (mulR64Effect 0x118618 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12, .gpr 0] []) (.reg (.gpr 0))) #v[57, 169]
    (.letOp (n := 172) (.out 0x118618 (mulR64Effect 0x118618 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12, .gpr 0] []) (.reg (.gpr 2))) #v[57, 169]
    (.letOp (n := 173) (.exec 0x118618 (fun s => s.RIP = 0x118618) (mulR64Effect 0x118618 12) (Reg.operands [.gpr 12, .gpr 0] [])) #v[57, 169]
    (.letOp (n := 174) (.exec 0x11861b (StorePre 0x11861b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x170)) s (0x11861b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11861b 2 (.sib 4 none 0 (.d32 0x170))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[172, 4]
    (.letOp (n := 175) (.out 0x118623 (movR64R64Effect 0x118623 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[171]
    (.letOp (n := 176) (.exec 0x118623 (fun s => s.RIP = 0x118623) (movR64R64Effect 0x118623 11 0) (Reg.operands [.gpr 0] [])) #v[171]
    (b_l118511_3)))))))))))))))))))))))))))))))))))))))))

def bytes_l118511_2 : List UInt8 :=
  [0x48, 0x21, 0xC8, 0x48, 0xB9, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE1,
    0x49, 0x89, 0xD1, 0x4C, 0x01, 0xD8, 0x48, 0x89, 0x84, 0x24, 0x78, 0x01, 0x00, 0x00, 0x49, 0x11,
    0xF9, 0x49, 0x0F, 0xA4, 0xC1, 0x0C, 0x48, 0x89, 0xD8, 0x49, 0xF7, 0xE7, 0x48, 0x89, 0x94, 0x24,
    0x28, 0x01, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0x58, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x84, 0x24,
    0xC8, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE6, 0x48, 0x89, 0xD7, 0x48, 0x89, 0xC1, 0x48, 0x89, 0xE8,
    0x49, 0xF7, 0xE4, 0x48, 0x89, 0x94, 0x24, 0x70, 0x01, 0x00, 0x00, 0x49, 0x89, 0xC3] ++ bytes_l118511_3

theorem code_l118511_2 : ∀ x ∈ codeRange 0x1185c8 bytes_l118511_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x185c8 94 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l118511_3

def b_l118511_1 : Block Op Label signature Reg.count 94 :=
  .letOp (n := 94) (.out 0x11856f (movR64R64Effect 0x11856f 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[91]
    (.letOp (n := 95) (.exec 0x11856f (fun s => s.RIP = 0x11856f) (movR64R64Effect 0x11856f 1 2) (Reg.operands [.gpr 2] [])) #v[91]
    (.letOp (n := 96) (.out 0x118572 (movR64R64Effect 0x118572 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[90]
    (.letOp (n := 97) (.exec 0x118572 (fun s => s.RIP = 0x118572) (movR64R64Effect 0x118572 6 0) (Reg.operands [.gpr 0] [])) #v[90]
    (.letOp (n := 98) (.out 0x118575 (addR64R64Effect 0x118575 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 8] []) (.reg (.gpr 6))) #v[96, 83]
    (.letOp (n := 99) (.out 0x118575 (addR64R64Effect 0x118575 6 8) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 8] []) (.flag .CF)) #v[96, 83]
    (.letOp (n := 100) (.exec 0x118575 (fun s => s.RIP = 0x118575) (addR64R64Effect 0x118575 6 8) (Reg.operands [.gpr 6, .gpr 8] [])) #v[96, 83]
    (.letOp (n := 101) (.out 0x118578 (atFlags StatusFlags.CF (adcR64R64Effect 0x118578 1 7)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[94, 86, 99]
    (.letOp (n := 102) (.exec 0x118578 (fun s => s.RIP = 0x118578) (atFlags StatusFlags.CF (adcR64R64Effect 0x118578 1 7)) (Reg.operands [.gpr 1, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[94, 86, 99]
    (.letOp (n := 103) (.out 0x11857b (movR64M64Effect 0x11857b 0 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 104) (.exec 0x11857b (LoadPre 0x11857b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x11857b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11857b 0 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 105) (.out 0x118583 (mulR64Effect 0x118583 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[59, 103]
    (.letOp (n := 106) (.out 0x118583 (mulR64Effect 0x118583 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[59, 103]
    (.letOp (n := 107) (.exec 0x118583 (fun s => s.RIP = 0x118583) (mulR64Effect 0x118583 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[59, 103]
    (.letOp (n := 108) (.exec 0x118586 (StorePre 0x118586 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x118586 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x118586 13 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 109) (.out 0x11858e (movR64R64Effect 0x11858e 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[106]
    (.letOp (n := 110) (.exec 0x11858e (fun s => s.RIP = 0x11858e) (movR64R64Effect 0x11858e 7 2) (Reg.operands [.gpr 2] [])) #v[106]
    (.letOp (n := 111) (.out 0x118591 (movR64R64Effect 0x118591 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[105]
    (.letOp (n := 112) (.exec 0x118591 (fun s => s.RIP = 0x118591) (movR64R64Effect 0x118591 11 0) (Reg.operands [.gpr 0] [])) #v[105]
    (.letOp (n := 113) (.out 0x118594 (addR64R64Effect 0x118594 11 6) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 6] []) (.reg (.gpr 11))) #v[111, 98]
    (.letOp (n := 114) (.out 0x118594 (addR64R64Effect 0x118594 11 6) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 6] []) (.flag .CF)) #v[111, 98]
    (.letOp (n := 115) (.exec 0x118594 (fun s => s.RIP = 0x118594) (addR64R64Effect 0x118594 11 6) (Reg.operands [.gpr 11, .gpr 6] [])) #v[111, 98]
    (.letOp (n := 116) (.out 0x118597 (atFlags StatusFlags.CF (adcR64R64Effect 0x118597 7 1)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[109, 101, 114]
    (.letOp (n := 117) (.exec 0x118597 (fun s => s.RIP = 0x118597) (atFlags StatusFlags.CF (adcR64R64Effect 0x118597 7 1)) (Reg.operands [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[109, 101, 114]
    (.letOp (n := 118) (.out 0x11859a (movR64M64Effect 0x11859a 3 (.sib 4 none 0 (.d32 0xe8))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 119) (.exec 0x11859a (LoadPre 0x11859a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x11859a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11859a 3 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 120) (.out 0x1185a2 (movR64R64Effect 0x1185a2 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[118]
    (.letOp (n := 121) (.exec 0x1185a2 (fun s => s.RIP = 0x1185a2) (movR64R64Effect 0x1185a2 0 3) (Reg.operands [.gpr 3] [])) #v[118]
    (.letOp (n := 122) (.out 0x1185a5 (movR64R64Effect 0x1185a5 6 9) (EffectPart.reads (.reg (.gpr 6)) [.gpr 9] []) (.reg (.gpr 6))) #v[61]
    (.letOp (n := 123) (.exec 0x1185a5 (fun s => s.RIP = 0x1185a5) (movR64R64Effect 0x1185a5 6 9) (Reg.operands [.gpr 9] [])) #v[61]
    (.letOp (n := 124) (.exec 0x1185a8 (StorePre 0x1185a8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x1185a8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1185a8 9 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 125) (.out 0x1185b0 (mulR64Effect 0x1185b0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[61, 120]
    (.letOp (n := 126) (.out 0x1185b0 (mulR64Effect 0x1185b0 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[61, 120]
    (.letOp (n := 127) (.exec 0x1185b0 (fun s => s.RIP = 0x1185b0) (mulR64Effect 0x1185b0 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[61, 120]
    (.letOp (n := 128) (.out 0x1185b3 (movR64R64Effect 0x1185b3 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[126]
    (.letOp (n := 129) (.exec 0x1185b3 (fun s => s.RIP = 0x1185b3) (movR64R64Effect 0x1185b3 8 2) (Reg.operands [.gpr 2] [])) #v[126]
    (.letOp (n := 130) (.out 0x1185b6 (movR64R64Effect 0x1185b6 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[126]
    (.letOp (n := 131) (.exec 0x1185b6 (fun s => s.RIP = 0x1185b6) (movR64R64Effect 0x1185b6 10 2) (Reg.operands [.gpr 2] [])) #v[126]
    (.letOp (n := 132) (.out 0x1185b9 (shldR64R64Effect 0x1185b9 5 10 0 12) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[130, 125]
    (.letOp (n := 133) (.exec 0x1185b9 (fun s => s.RIP = 0x1185b9) (shldR64R64Effect 0x1185b9 5 10 0 12) (Reg.operands [.gpr 10, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[130, 125]
    (.letOp (n := 134) (.out 0x1185be (movR64Imm64Effect 0x1185be 1 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 135) (.exec 0x1185be (fun s => s.RIP = 0x1185be) (movR64Imm64Effect 0x1185be 1 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (b_l118511_2))))))))))))))))))))))))))))))))))))))))))

def bytes_l118511_1 : List UInt8 :=
  [0x48, 0x89, 0xD1, 0x48, 0x89, 0xC6, 0x4C, 0x01, 0xC6, 0x48, 0x11, 0xF9, 0x48, 0x8B, 0x84, 0x24,
    0x98, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE5, 0x4C, 0x89, 0xAC, 0x24, 0x10, 0x01, 0x00, 0x00, 0x48,
    0x89, 0xD7, 0x49, 0x89, 0xC3, 0x49, 0x01, 0xF3, 0x48, 0x11, 0xCF, 0x48, 0x8B, 0x9C, 0x24, 0xE8,
    0x00, 0x00, 0x00, 0x48, 0x89, 0xD8, 0x4C, 0x89, 0xCE, 0x4C, 0x89, 0x8C, 0x24, 0xE0, 0x00, 0x00,
    0x00, 0x49, 0xF7, 0xE1, 0x49, 0x89, 0xD0, 0x49, 0x89, 0xD2, 0x49, 0x0F, 0xA4, 0xC2, 0x0C, 0x48,
    0xB9, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00] ++ bytes_l118511_2

theorem code_l118511_1 : ∀ x ∈ codeRange 0x11856f bytes_l118511_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1856f 89 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l118511_2

def b_l118511 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x118511 (movR64M64Effect 0x118511 15 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 54) (.exec 0x118511 (LoadPre 0x118511 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x118511 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x118511 15 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x118515 (movR64M64Effect 0x118515 14 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 56) (.exec 0x118515 (LoadPre 0x118515 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x118515 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x118515 14 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x11851a (movR64M64Effect 0x11851a 12 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 58) (.exec 0x11851a (LoadPre 0x11851a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11851a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11851a 12 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x11851f (movR64M64Effect 0x11851f 13 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 60) (.exec 0x11851f (LoadPre 0x11851f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11851f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11851f 13 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x118524 (movR64M64Effect 0x118524 9 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 62) (.exec 0x118524 (LoadPre 0x118524 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x118524 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x118524 9 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x118529 (movR64M64Effect 0x118529 0 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 64) (.exec 0x118529 (LoadPre 0x118529 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x118529 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x118529 0 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x118531 (mulR64Effect 0x118531 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15, .gpr 0] []) (.reg (.gpr 0))) #v[53, 63]
    (.letOp (n := 66) (.out 0x118531 (mulR64Effect 0x118531 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15, .gpr 0] []) (.reg (.gpr 2))) #v[53, 63]
    (.letOp (n := 67) (.exec 0x118531 (fun s => s.RIP = 0x118531) (mulR64Effect 0x118531 15) (Reg.operands [.gpr 15, .gpr 0] [])) #v[53, 63]
    (.letOp (n := 68) (.exec 0x118534 (StorePre 0x118534 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x118534 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x118534 15 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 69) (.out 0x11853c (movR64R64Effect 0x11853c 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[66]
    (.letOp (n := 70) (.exec 0x11853c (fun s => s.RIP = 0x11853c) (movR64R64Effect 0x11853c 1 2) (Reg.operands [.gpr 2] [])) #v[66]
    (.letOp (n := 71) (.out 0x11853f (movR64R64Effect 0x11853f 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[65]
    (.letOp (n := 72) (.exec 0x11853f (fun s => s.RIP = 0x11853f) (movR64R64Effect 0x11853f 6 0) (Reg.operands [.gpr 0] [])) #v[65]
    (.letOp (n := 73) (.out 0x118542 (movR64R64Effect 0x118542 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[5]
    (.letOp (n := 74) (.exec 0x118542 (fun s => s.RIP = 0x118542) (movR64R64Effect 0x118542 0 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 75) (.out 0x118545 (mulR64Effect 0x118545 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[55, 73]
    (.letOp (n := 76) (.out 0x118545 (mulR64Effect 0x118545 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[55, 73]
    (.letOp (n := 77) (.exec 0x118545 (fun s => s.RIP = 0x118545) (mulR64Effect 0x118545 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[55, 73]
    (.letOp (n := 78) (.exec 0x118548 (StorePre 0x118548 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x168)) s (0x118548 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x118548 14 (.sib 4 none 0 (.d32 0x168))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 79) (.out 0x118550 (movR64R64Effect 0x118550 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[76]
    (.letOp (n := 80) (.exec 0x118550 (fun s => s.RIP = 0x118550) (movR64R64Effect 0x118550 7 2) (Reg.operands [.gpr 2] [])) #v[76]
    (.letOp (n := 81) (.out 0x118553 (movR64R64Effect 0x118553 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[75]
    (.letOp (n := 82) (.exec 0x118553 (fun s => s.RIP = 0x118553) (movR64R64Effect 0x118553 8 0) (Reg.operands [.gpr 0] [])) #v[75]
    (.letOp (n := 83) (.out 0x118556 (addR64R64Effect 0x118556 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6] []) (.reg (.gpr 8))) #v[81, 71]
    (.letOp (n := 84) (.out 0x118556 (addR64R64Effect 0x118556 8 6) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 6] []) (.flag .CF)) #v[81, 71]
    (.letOp (n := 85) (.exec 0x118556 (fun s => s.RIP = 0x118556) (addR64R64Effect 0x118556 8 6) (Reg.operands [.gpr 8, .gpr 6] [])) #v[81, 71]
    (.letOp (n := 86) (.out 0x118559 (atFlags StatusFlags.CF (adcR64R64Effect 0x118559 7 1)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[79, 69, 84]
    (.letOp (n := 87) (.exec 0x118559 (fun s => s.RIP = 0x118559) (atFlags StatusFlags.CF (adcR64R64Effect 0x118559 7 1)) (Reg.operands [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[79, 69, 84]
    (.letOp (n := 88) (.out 0x11855c (movR64M64Effect 0x11855c 0 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 89) (.exec 0x11855c (LoadPre 0x11855c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x11855c + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11855c 0 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 90) (.out 0x118564 (mulR64Effect 0x118564 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12, .gpr 0] []) (.reg (.gpr 0))) #v[57, 88]
    (.letOp (n := 91) (.out 0x118564 (mulR64Effect 0x118564 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12, .gpr 0] []) (.reg (.gpr 2))) #v[57, 88]
    (.letOp (n := 92) (.exec 0x118564 (fun s => s.RIP = 0x118564) (mulR64Effect 0x118564 12) (Reg.operands [.gpr 12, .gpr 0] [])) #v[57, 88]
    (.letOp (n := 93) (.exec 0x118567 (StorePre 0x118567 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x118567 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x118567 12 (.sib 4 none 0 (.d32 0x118))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[57, 4]
    (b_l118511_1)))))))))))))))))))))))))))))))))))))))))

def bytes_l118511 : List UInt8 :=
  [0x4C, 0x8B, 0x3C, 0x24, 0x4C, 0x8B, 0x74, 0x24, 0x08, 0x4C, 0x8B, 0x64, 0x24, 0x10, 0x4C, 0x8B,
    0x6C, 0x24, 0x18, 0x4C, 0x8B, 0x4C, 0x24, 0x20, 0x48, 0x8B, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00,
    0x49, 0xF7, 0xE7, 0x4C, 0x89, 0xBC, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x48, 0x89, 0xD1, 0x48, 0x89,
    0xC6, 0x48, 0x89, 0xE8, 0x49, 0xF7, 0xE6, 0x4C, 0x89, 0xB4, 0x24, 0x68, 0x01, 0x00, 0x00, 0x48,
    0x89, 0xD7, 0x49, 0x89, 0xC0, 0x49, 0x01, 0xF0, 0x48, 0x11, 0xCF, 0x48, 0x8B, 0x84, 0x24, 0xB8,
    0x00, 0x00, 0x00, 0x49, 0xF7, 0xE4, 0x4C, 0x89, 0xA4, 0x24, 0x18, 0x01, 0x00, 0x00] ++ bytes_l118511_1

theorem code_l118511 : ∀ x ∈ codeRange 0x118511 bytes_l118511, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x18511 94 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l118511_1

@[cfg_block] def b_l118950 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x118950 (movR64R64Effect 0x118950 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 54) (.exec 0x118950 (fun s => s.RIP = 0x118950) (movR64R64Effect 0x118950 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x118953 (movR64R64Effect 0x118953 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 56) (.exec 0x118953 (fun s => s.RIP = 0x118953) (movR64R64Effect 0x118953 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x118956 (callEffect (fun _ => 0x1145f0) 0x11895b) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x118956 (PushPre 0x118956 5) (callEffect (fun _ => 0x1145f0) 0x11895b) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x11895b⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ { target := .l11895b, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l118950 : List UInt8 :=
  [0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x95, 0xBC, 0xFF, 0xFF]

theorem code_l118950 : ∀ x ∈ codeRange 0x118950 bytes_l118950, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x18950 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11895b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11895b (movR64M64Effect 0x11895b 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x11895b (LoadPre 0x11895b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x11895b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11895b 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x118960 (StorePre 0x118960 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x118960 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x118960 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x118965 (movR64M64Effect 0x118965 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x118965 (LoadPre 0x118965 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x118965 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x118965 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x11896a (StorePre 0x11896a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11896a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11896a 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x11896f (movR64M64Effect 0x11896f 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x11896f (LoadPre 0x11896f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11896f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11896f 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x118974 (StorePre 0x118974 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x118974 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x118974 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x118979 (movR64M64Effect 0x118979 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x118979 (LoadPre 0x118979 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x118979 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x118979 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x11897e (movR64M64Effect 0x11897e 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x11897e (LoadPre 0x11897e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11897e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11897e 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x118983 (StorePre 0x118983 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x118983 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x118983 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x118988 (StorePre 0x118988 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x118988 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x118988 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x11898c (decR64Effect 0x11898c 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[15]
    (.letOp (n := 69) (.out 0x11898c (decR64Effect 0x11898c 15) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.flag .ZF)) #v[15]
    (.letOp (n := 70) (.exec 0x11898c (fun s => s.RIP = 0x11898c) (decR64Effect 0x11898c 15) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[15]
    (.letOp (n := 71) (.pure (condOp 5)) #v[69]
    (.terminate (.condBr (Fin.last 71) ⟨.l118950, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 68), (19, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩ ⟨.l118991, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 68), (19, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩))))))))))))))))))))

def bytes_l11895b : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x49, 0xFF, 0xCF, 0x75, 0xBF]

theorem code_l11895b : ∀ x ∈ codeRange 0x11895b bytes_l11895b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1895b 54 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

def b_l118991_11 : Block Op Label signature Reg.count 539 :=
  .letOp (n := 539) (.out 0x118d57 (shldR64R64Effect 0x118d57 5 2 1 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[537, 534]
    (.letOp (n := 540) (.exec 0x118d57 (fun s => s.RIP = 0x118d57) (shldR64R64Effect 0x118d57 5 2 1 12) (Reg.operands [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[537, 534]
    (.letOp (n := 541) (.out 0x118d5c (movR64Imm64Effect 0x118d5c 0 0xffffffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 542) (.exec 0x118d5c (fun s => s.RIP = 0x118d5c) (movR64Imm64Effect 0x118d5c 0 0xffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 543) (.out 0x118d66 (andR64R64Effect 0x118d66 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[236, 541]
    (.letOp (n := 544) (.exec 0x118d66 (fun s => s.RIP = 0x118d66) (andR64R64Effect 0x118d66 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[236, 541]
    (.letOp (n := 545) (.out 0x118d69 (addR64R64Effect 0x118d69 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[543, 539]
    (.letOp (n := 546) (.exec 0x118d69 (fun s => s.RIP = 0x118d69) (addR64R64Effect 0x118d69 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[543, 539]
    (.letOp (n := 547) (.out 0x118d6c (movR64M64Effect 0x118d6c 0 (.sib 4 none 0 (.d32 0xe0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 548) (.exec 0x118d6c (LoadPre 0x118d6c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x118d6c + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x118d6c 0 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 549) (.exec 0x118d74 (StorePre 0x118d74 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x118d74 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x118d74 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[547, 4]
    (.letOp (n := 550) (.exec 0x118d78 (StorePre 0x118d78 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x118d78 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x118d78 8 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[457, 4]
    (.letOp (n := 551) (.exec 0x118d7d (StorePre 0x118d7d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x118d7d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x118d7d 10 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[523, 4]
    (.letOp (n := 552) (.out 0x118d82 (andR64R64Effect 0x118d82 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[534, 368]
    (.letOp (n := 553) (.exec 0x118d82 (fun s => s.RIP = 0x118d82) (andR64R64Effect 0x118d82 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[534, 368]
    (.letOp (n := 554) (.exec 0x118d85 (StorePre 0x118d85 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x118d85 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x118d85 1 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[552, 4]
    (.letOp (n := 555) (.exec 0x118d8a (StorePre 0x118d8a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x118d8a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x118d8a 6 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[545, 4]
    (.letOp (n := 556) (.out 0x118d8f (leaR64Effect 0x118d8f 3 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 557) (.exec 0x118d8f (fun s => s.RIP = 0x118d8f) (leaR64Effect 0x118d8f 3 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 558) (.out 0x118d94 (movR64R64Effect 0x118d94 14 4) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 559) (.exec 0x118d94 (fun s => s.RIP = 0x118d94) (movR64R64Effect 0x118d94 14 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 560) (.out 0x118d97 (movR64R64Effect 0x118d97 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[556]
    (.letOp (n := 561) (.exec 0x118d97 (fun s => s.RIP = 0x118d97) (movR64R64Effect 0x118d97 7 3) (Reg.operands [.gpr 3] [])) #v[556]
    (.letOp (n := 562) (.out 0x118d9a (movR64R64Effect 0x118d9a 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[558]
    (.letOp (n := 563) (.exec 0x118d9a (fun s => s.RIP = 0x118d9a) (movR64R64Effect 0x118d9a 6 14) (Reg.operands [.gpr 14] [])) #v[558]
    (.letOp (n := 564) (.out 0x118d9d (callEffect (fun _ => 0x1145f0) 0x118da2) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 565) (.exec 0x118d9d (PushPre 0x118d9d 5) (callEffect (fun _ => 0x1145f0) 0x118da2) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 566) (.const ⟨64, 0x118da2⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 547), (1, 552), (2, 539), (3, 556), (4, 564), (5, 453), (6, 562), (7, 560), (8, 457), (9, 430), (10, 523), (11, 406), (12, 466), (13, 455), (14, 558), (15, 480), (22, 22), (39, 39), (50, 50), (51, 51)] 567⟩ { target := .l118da2, kept := #v[], arity := rfl, guard := some (Fin.last 566) })))))))))))))))))))))))))))))

def bytes_l118991_11 : List UInt8 :=
  [0x48, 0x0F, 0xA4, 0xCA, 0x0C, 0x48, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x48,
    0x21, 0xC6, 0x48, 0x01, 0xD6, 0x48, 0x8B, 0x84, 0x24, 0xE0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x04,
    0x24, 0x4C, 0x89, 0x44, 0x24, 0x08, 0x4C, 0x89, 0x54, 0x24, 0x10, 0x48, 0x21, 0xF9, 0x48, 0x89,
    0x4C, 0x24, 0x18, 0x48, 0x89, 0x74, 0x24, 0x20, 0x48, 0x8D, 0x5C, 0x24, 0x28, 0x49, 0x89, 0xE6,
    0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x4E, 0xB8, 0xFF, 0xFF]

theorem code_l118991_11 : ∀ x ∈ codeRange 0x118d57 bytes_l118991_11, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x18d57 75 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

def b_l118991_10 : Block Op Label signature Reg.count 491 :=
  .letOp (n := 491) (.out 0x118d05 (mulR64Effect 0x118d05 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[489, 487]
    (.letOp (n := 492) (.out 0x118d05 (mulR64Effect 0x118d05 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[489, 487]
    (.letOp (n := 493) (.exec 0x118d05 (fun s => s.RIP = 0x118d05) (mulR64Effect 0x118d05 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[489, 487]
    (.letOp (n := 494) (.out 0x118d08 (addR64M64Effect 0x118d08 10 (.sib 4 none 0 (.d32 0x110))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 4] []) (.reg (.gpr 10))) #v[446, 4]
    (.letOp (n := 495) (.out 0x118d08 (addR64M64Effect 0x118d08 10 (.sib 4 none 0 (.d32 0x110))) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 4] []) (.flag .CF)) #v[446, 4]
    (.letOp (n := 496) (.exec 0x118d08 (LoadPre 0x118d08 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x118d08 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x118d08 10 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[446, 4]
    (.letOp (n := 497) (.out 0x118d10 (atFlags StatusFlags.CF (adcR64M64Effect 0x118d10 14 (.sib 4 none 0 (.d32 0x80)))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 14))) #v[444, 4, 495]
    (.letOp (n := 498) (.exec 0x118d10 (LoadPre 0x118d10 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x118d10 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x118d10 14 (.sib 4 none 0 (.d32 0x80)))) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[444, 4, 495]
    (.letOp (n := 499) (.out 0x118d18 (addR64R64Effect 0x118d18 10 5) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 5] []) (.reg (.gpr 10))) #v[494, 453]
    (.letOp (n := 500) (.out 0x118d18 (addR64R64Effect 0x118d18 10 5) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 5] []) (.flag .CF)) #v[494, 453]
    (.letOp (n := 501) (.exec 0x118d18 (fun s => s.RIP = 0x118d18) (addR64R64Effect 0x118d18 10 5) (Reg.operands [.gpr 10, .gpr 5] [])) #v[494, 453]
    (.letOp (n := 502) (.out 0x118d1b (atFlags StatusFlags.CF (adcR64R64Effect 0x118d1b 14 13)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[497, 455, 500]
    (.letOp (n := 503) (.exec 0x118d1b (fun s => s.RIP = 0x118d1b) (atFlags StatusFlags.CF (adcR64R64Effect 0x118d1b 14 13)) (Reg.operands [.gpr 14, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[497, 455, 500]
    (.letOp (n := 504) (.out 0x118d1e (addR64R64Effect 0x118d1e 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0] []) (.reg (.gpr 10))) #v[499, 491]
    (.letOp (n := 505) (.out 0x118d1e (addR64R64Effect 0x118d1e 10 0) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 0] []) (.flag .CF)) #v[499, 491]
    (.letOp (n := 506) (.exec 0x118d1e (fun s => s.RIP = 0x118d1e) (addR64R64Effect 0x118d1e 10 0) (Reg.operands [.gpr 10, .gpr 0] [])) #v[499, 491]
    (.letOp (n := 507) (.out 0x118d21 (atFlags StatusFlags.CF (adcR64R64Effect 0x118d21 14 2)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[502, 492, 505]
    (.letOp (n := 508) (.exec 0x118d21 (fun s => s.RIP = 0x118d21) (atFlags StatusFlags.CF (adcR64R64Effect 0x118d21 14 2)) (Reg.operands [.gpr 14, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[502, 492, 505]
    (.letOp (n := 509) (.out 0x118d24 (addR64R64Effect 0x118d24 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9] []) (.reg (.gpr 10))) #v[504, 430]
    (.letOp (n := 510) (.out 0x118d24 (addR64R64Effect 0x118d24 10 9) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 9] []) (.flag .CF)) #v[504, 430]
    (.letOp (n := 511) (.exec 0x118d24 (fun s => s.RIP = 0x118d24) (addR64R64Effect 0x118d24 10 9) (Reg.operands [.gpr 10, .gpr 9] [])) #v[504, 430]
    (.letOp (n := 512) (.out 0x118d27 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x118d27 14 0x0)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[507, 510]
    (.letOp (n := 513) (.exec 0x118d27 (fun s => s.RIP = 0x118d27) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x118d27 14 0x0)) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[507, 510]
    (.letOp (n := 514) (.out 0x118d2b (shldR64R64Effect 0x118d2b 5 3 15 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[483, 480]
    (.letOp (n := 515) (.exec 0x118d2b (fun s => s.RIP = 0x118d2b) (shldR64R64Effect 0x118d2b 5 3 15 12) (Reg.operands [.gpr 3, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[483, 480]
    (.letOp (n := 516) (.out 0x118d30 (shldR64R64Effect 0x118d30 5 14 10 12) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[512, 509]
    (.letOp (n := 517) (.exec 0x118d30 (fun s => s.RIP = 0x118d30) (shldR64R64Effect 0x118d30 5 14 10 12) (Reg.operands [.gpr 14, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[512, 509]
    (.letOp (n := 518) (.out 0x118d35 (movR64R64Effect 0x118d35 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[514]
    (.letOp (n := 519) (.exec 0x118d35 (fun s => s.RIP = 0x118d35) (movR64R64Effect 0x118d35 0 3) (Reg.operands [.gpr 3] [])) #v[514]
    (.letOp (n := 520) (.out 0x118d38 (mulR64Effect 0x118d38 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[489, 518]
    (.letOp (n := 521) (.out 0x118d38 (mulR64Effect 0x118d38 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[489, 518]
    (.letOp (n := 522) (.exec 0x118d38 (fun s => s.RIP = 0x118d38) (mulR64Effect 0x118d38 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[489, 518]
    (.letOp (n := 523) (.out 0x118d3b (andR64R64Effect 0x118d3b 10 7) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 7] []) (.reg (.gpr 10))) #v[509, 368]
    (.letOp (n := 524) (.exec 0x118d3b (fun s => s.RIP = 0x118d3b) (andR64R64Effect 0x118d3b 10 7) (Reg.operands [.gpr 10, .gpr 7] [])) #v[509, 368]
    (.letOp (n := 525) (.out 0x118d3e (movR64M64Effect 0x118d3e 1 (.sib 4 none 0 (.d32 0x118))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 526) (.exec 0x118d3e (LoadPre 0x118d3e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x118d3e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x118d3e 1 (.sib 4 none 0 (.d32 0x118))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 527) (.out 0x118d46 (andR64R64Effect 0x118d46 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[525, 368]
    (.letOp (n := 528) (.exec 0x118d46 (fun s => s.RIP = 0x118d46) (andR64R64Effect 0x118d46 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[525, 368]
    (.letOp (n := 529) (.out 0x118d49 (addR64R64Effect 0x118d49 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[527, 520]
    (.letOp (n := 530) (.out 0x118d49 (addR64R64Effect 0x118d49 1 0) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 0] []) (.flag .CF)) #v[527, 520]
    (.letOp (n := 531) (.exec 0x118d49 (fun s => s.RIP = 0x118d49) (addR64R64Effect 0x118d49 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[527, 520]
    (.letOp (n := 532) (.out 0x118d4c (atFlags StatusFlags.CF (adcR64Imm8Effect 0x118d4c 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[521, 530]
    (.letOp (n := 533) (.exec 0x118d4c (fun s => s.RIP = 0x118d4c) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x118d4c 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[521, 530]
    (.letOp (n := 534) (.out 0x118d50 (addR64R64Effect 0x118d50 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 14] []) (.reg (.gpr 1))) #v[529, 516]
    (.letOp (n := 535) (.out 0x118d50 (addR64R64Effect 0x118d50 1 14) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 14] []) (.flag .CF)) #v[529, 516]
    (.letOp (n := 536) (.exec 0x118d50 (fun s => s.RIP = 0x118d50) (addR64R64Effect 0x118d50 1 14) (Reg.operands [.gpr 1, .gpr 14] [])) #v[529, 516]
    (.letOp (n := 537) (.out 0x118d53 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x118d53 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[532, 535]
    (.letOp (n := 538) (.exec 0x118d53 (fun s => s.RIP = 0x118d53) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x118d53 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[532, 535]
    (b_l118991_11))))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l118991_10 : List UInt8 :=
  [0x48, 0xF7, 0xE1, 0x4C, 0x03, 0x94, 0x24, 0x10, 0x01, 0x00, 0x00, 0x4C, 0x13, 0xB4, 0x24, 0x80,
    0x00, 0x00, 0x00, 0x49, 0x01, 0xEA, 0x4D, 0x11, 0xEE, 0x49, 0x01, 0xC2, 0x49, 0x11, 0xD6, 0x4D,
    0x01, 0xCA, 0x49, 0x83, 0xD6, 0x00, 0x4C, 0x0F, 0xA4, 0xFB, 0x0C, 0x4D, 0x0F, 0xA4, 0xD6, 0x0C,
    0x48, 0x89, 0xD8, 0x48, 0xF7, 0xE1, 0x49, 0x21, 0xFA, 0x48, 0x8B, 0x8C, 0x24, 0x18, 0x01, 0x00,
    0x00, 0x48, 0x21, 0xF9, 0x48, 0x01, 0xC1, 0x48, 0x83, 0xD2, 0x00, 0x4C, 0x01, 0xF1, 0x48, 0x83,
    0xD2, 0x00] ++ bytes_l118991_11

theorem code_l118991_10 : ∀ x ∈ codeRange 0x118d05 bytes_l118991_10, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x18d05 82 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l118991_11

def b_l118991_9 : Block Op Label signature Reg.count 446 :=
  .letOp (n := 446) (.out 0x118cb1 (movR64R64Effect 0x118cb1 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[441]
    (.letOp (n := 447) (.exec 0x118cb1 (fun s => s.RIP = 0x118cb1) (movR64R64Effect 0x118cb1 10 0) (Reg.operands [.gpr 0] [])) #v[441]
    (.letOp (n := 448) (.out 0x118cb4 (movR64M64Effect 0x118cb4 0 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 449) (.exec 0x118cb4 (LoadPre 0x118cb4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x118cb4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x118cb4 0 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 450) (.out 0x118cb9 (mulM64Effect 0x118cb9 8 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[448, 4]
    (.letOp (n := 451) (.out 0x118cb9 (mulM64Effect 0x118cb9 8 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[448, 4]
    (.letOp (n := 452) (.exec 0x118cb9 (LoadPre 0x118cb9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x118cb9 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x118cb9 8 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[448, 4]
    (.letOp (n := 453) (.out 0x118cc1 (movR64R64Effect 0x118cc1 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[450]
    (.letOp (n := 454) (.exec 0x118cc1 (fun s => s.RIP = 0x118cc1) (movR64R64Effect 0x118cc1 5 0) (Reg.operands [.gpr 0] [])) #v[450]
    (.letOp (n := 455) (.out 0x118cc4 (movR64R64Effect 0x118cc4 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[451]
    (.letOp (n := 456) (.exec 0x118cc4 (fun s => s.RIP = 0x118cc4) (movR64R64Effect 0x118cc4 13 2) (Reg.operands [.gpr 2] [])) #v[451]
    (.letOp (n := 457) (.out 0x118cc7 (andR64R64Effect 0x118cc7 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 7] []) (.reg (.gpr 8))) #v[425, 368]
    (.letOp (n := 458) (.exec 0x118cc7 (fun s => s.RIP = 0x118cc7) (andR64R64Effect 0x118cc7 8 7) (Reg.operands [.gpr 8, .gpr 7] [])) #v[425, 368]
    (.letOp (n := 459) (.out 0x118cca (movR64M64Effect 0x118cca 0 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 460) (.exec 0x118cca (LoadPre 0x118cca (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x118cca + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x118cca 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 461) (.out 0x118ccf (mulM64Effect 0x118ccf 8 (.sib 4 none 0 (.d32 0xe8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[459, 4]
    (.letOp (n := 462) (.out 0x118ccf (mulM64Effect 0x118ccf 8 (.sib 4 none 0 (.d32 0xe8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[459, 4]
    (.letOp (n := 463) (.exec 0x118ccf (LoadPre 0x118ccf (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x118ccf + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x118ccf 8 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[459, 4]
    (.letOp (n := 464) (.out 0x118cd7 (movR64R64Effect 0x118cd7 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[462]
    (.letOp (n := 465) (.exec 0x118cd7 (fun s => s.RIP = 0x118cd7) (movR64R64Effect 0x118cd7 3 2) (Reg.operands [.gpr 2] [])) #v[462]
    (.letOp (n := 466) (.out 0x118cda (movR64R64Effect 0x118cda 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[461]
    (.letOp (n := 467) (.exec 0x118cda (fun s => s.RIP = 0x118cda) (movR64R64Effect 0x118cda 12 0) (Reg.operands [.gpr 0] [])) #v[461]
    (.letOp (n := 468) (.out 0x118cdd (movR64M64Effect 0x118cdd 0 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 469) (.exec 0x118cdd (LoadPre 0x118cdd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x118cdd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x118cdd 0 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 470) (.out 0x118ce2 (mulR64Effect 0x118ce2 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15, .gpr 0] []) (.reg (.gpr 0))) #v[386, 468]
    (.letOp (n := 471) (.out 0x118ce2 (mulR64Effect 0x118ce2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15, .gpr 0] []) (.reg (.gpr 2))) #v[386, 468]
    (.letOp (n := 472) (.exec 0x118ce2 (fun s => s.RIP = 0x118ce2) (mulR64Effect 0x118ce2 15) (Reg.operands [.gpr 15, .gpr 0] [])) #v[386, 468]
    (.letOp (n := 473) (.out 0x118ce5 (movR64R64Effect 0x118ce5 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[470]
    (.letOp (n := 474) (.exec 0x118ce5 (fun s => s.RIP = 0x118ce5) (movR64R64Effect 0x118ce5 15 0) (Reg.operands [.gpr 0] [])) #v[470]
    (.letOp (n := 475) (.out 0x118ce8 (addR64R64Effect 0x118ce8 15 12) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 12] []) (.reg (.gpr 15))) #v[473, 466]
    (.letOp (n := 476) (.out 0x118ce8 (addR64R64Effect 0x118ce8 15 12) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 12] []) (.flag .CF)) #v[473, 466]
    (.letOp (n := 477) (.exec 0x118ce8 (fun s => s.RIP = 0x118ce8) (addR64R64Effect 0x118ce8 15 12) (Reg.operands [.gpr 15, .gpr 12] [])) #v[473, 466]
    (.letOp (n := 478) (.out 0x118ceb (atFlags StatusFlags.CF (adcR64R64Effect 0x118ceb 3 2)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[464, 471, 476]
    (.letOp (n := 479) (.exec 0x118ceb (fun s => s.RIP = 0x118ceb) (atFlags StatusFlags.CF (adcR64R64Effect 0x118ceb 3 2)) (Reg.operands [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[464, 471, 476]
    (.letOp (n := 480) (.out 0x118cee (addR64R64Effect 0x118cee 15 11) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 11] []) (.reg (.gpr 15))) #v[475, 406]
    (.letOp (n := 481) (.out 0x118cee (addR64R64Effect 0x118cee 15 11) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 11] []) (.flag .CF)) #v[475, 406]
    (.letOp (n := 482) (.exec 0x118cee (fun s => s.RIP = 0x118cee) (addR64R64Effect 0x118cee 15 11) (Reg.operands [.gpr 15, .gpr 11] [])) #v[475, 406]
    (.letOp (n := 483) (.out 0x118cf1 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x118cf1 3 0x0)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[478, 481]
    (.letOp (n := 484) (.exec 0x118cf1 (fun s => s.RIP = 0x118cf1) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x118cf1 3 0x0)) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[478, 481]
    (.letOp (n := 485) (.out 0x118cf5 (movR64R64Effect 0x118cf5 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[480]
    (.letOp (n := 486) (.exec 0x118cf5 (fun s => s.RIP = 0x118cf5) (movR64R64Effect 0x118cf5 0 15) (Reg.operands [.gpr 15] [])) #v[480]
    (.letOp (n := 487) (.out 0x118cf8 (andR64R64Effect 0x118cf8 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[485, 368]
    (.letOp (n := 488) (.exec 0x118cf8 (fun s => s.RIP = 0x118cf8) (andR64R64Effect 0x118cf8 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[485, 368]
    (.letOp (n := 489) (.out 0x118cfb (movR64Imm64Effect 0x118cfb 1 0x1000003d10) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 490) (.exec 0x118cfb (fun s => s.RIP = 0x118cfb) (movR64Imm64Effect 0x118cfb 1 0x1000003d10) (Reg.operands [] [])) #v[]
    (b_l118991_10)))))))))))))))))))))))))))))))))))))))))))))

def bytes_l118991_9 : List UInt8 :=
  [0x49, 0x89, 0xC2, 0x48, 0x8B, 0x44, 0x24, 0x78, 0x48, 0xF7, 0xA4, 0x24, 0xC8, 0x00, 0x00, 0x00,
    0x48, 0x89, 0xC5, 0x49, 0x89, 0xD5, 0x49, 0x21, 0xF8, 0x48, 0x8B, 0x44, 0x24, 0x58, 0x48, 0xF7,
    0xA4, 0x24, 0xE8, 0x00, 0x00, 0x00, 0x48, 0x89, 0xD3, 0x49, 0x89, 0xC4, 0x48, 0x8B, 0x44, 0x24,
    0x50, 0x49, 0xF7, 0xE7, 0x49, 0x89, 0xC7, 0x4D, 0x01, 0xE7, 0x48, 0x11, 0xD3, 0x4D, 0x01, 0xDF,
    0x48, 0x83, 0xD3, 0x00, 0x4C, 0x89, 0xF8, 0x48, 0x21, 0xF8, 0x48, 0xB9, 0x10, 0x3D, 0x00, 0x00,
    0x10, 0x00, 0x00, 0x00] ++ bytes_l118991_10

theorem code_l118991_9 : ∀ x ∈ codeRange 0x118cb1 bytes_l118991_9, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x18cb1 84 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l118991_10

def b_l118991_8 : Block Op Label signature Reg.count 401 :=
  .letOp (n := 401) (.out 0x118c4d (addR64R64Effect 0x118c4d 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[396, 316]
    (.letOp (n := 402) (.out 0x118c4d (addR64R64Effect 0x118c4d 0 10) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 10] []) (.flag .CF)) #v[396, 316]
    (.letOp (n := 403) (.exec 0x118c4d (fun s => s.RIP = 0x118c4d) (addR64R64Effect 0x118c4d 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[396, 316]
    (.letOp (n := 404) (.out 0x118c50 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x118c50 11 0x0)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[399, 402]
    (.letOp (n := 405) (.exec 0x118c50 (fun s => s.RIP = 0x118c50) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x118c50 11 0x0)) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[399, 402]
    (.letOp (n := 406) (.out 0x118c54 (shldR64R64Effect 0x118c54 5 11 0 12) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[404, 401]
    (.letOp (n := 407) (.exec 0x118c54 (fun s => s.RIP = 0x118c54) (shldR64R64Effect 0x118c54 5 11 0 12) (Reg.operands [.gpr 11, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[404, 401]
    (.letOp (n := 408) (.out 0x118c59 (andR64R64Effect 0x118c59 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[401, 368]
    (.letOp (n := 409) (.exec 0x118c59 (fun s => s.RIP = 0x118c59) (andR64R64Effect 0x118c59 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[401, 368]
    (.letOp (n := 410) (.out 0x118c5c (movR64Imm64Effect 0x118c5c 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 411) (.exec 0x118c5c (fun s => s.RIP = 0x118c5c) (movR64Imm64Effect 0x118c5c 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 412) (.out 0x118c66 (mulR64Effect 0x118c66 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[410, 408]
    (.letOp (n := 413) (.out 0x118c66 (mulR64Effect 0x118c66 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[410, 408]
    (.letOp (n := 414) (.exec 0x118c66 (fun s => s.RIP = 0x118c66) (mulR64Effect 0x118c66 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[410, 408]
    (.letOp (n := 415) (.out 0x118c69 (addR64R64Effect 0x118c69 8 14) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 14] []) (.reg (.gpr 8))) #v[357, 348]
    (.letOp (n := 416) (.out 0x118c69 (addR64R64Effect 0x118c69 8 14) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 14] []) (.flag .CF)) #v[357, 348]
    (.letOp (n := 417) (.exec 0x118c69 (fun s => s.RIP = 0x118c69) (addR64R64Effect 0x118c69 8 14) (Reg.operands [.gpr 8, .gpr 14] [])) #v[357, 348]
    (.letOp (n := 418) (.out 0x118c6c (atFlags StatusFlags.CF (adcR64M64Effect 0x118c6c 9 (.sib 4 none 0 (.d32 0xd8)))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 9))) #v[355, 4, 416]
    (.letOp (n := 419) (.exec 0x118c6c (LoadPre 0x118c6c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x118c6c + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x118c6c 9 (.sib 4 none 0 (.d32 0xd8)))) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[355, 4, 416]
    (.letOp (n := 420) (.out 0x118c74 (addR64R64Effect 0x118c74 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[415, 412]
    (.letOp (n := 421) (.out 0x118c74 (addR64R64Effect 0x118c74 8 0) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 0] []) (.flag .CF)) #v[415, 412]
    (.letOp (n := 422) (.exec 0x118c74 (fun s => s.RIP = 0x118c74) (addR64R64Effect 0x118c74 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[415, 412]
    (.letOp (n := 423) (.out 0x118c77 (atFlags StatusFlags.CF (adcR64R64Effect 0x118c77 9 2)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[418, 413, 421]
    (.letOp (n := 424) (.exec 0x118c77 (fun s => s.RIP = 0x118c77) (atFlags StatusFlags.CF (adcR64R64Effect 0x118c77 9 2)) (Reg.operands [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[418, 413, 421]
    (.letOp (n := 425) (.out 0x118c7a (addR64R64Effect 0x118c7a 8 3) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 3] []) (.reg (.gpr 8))) #v[420, 338]
    (.letOp (n := 426) (.out 0x118c7a (addR64R64Effect 0x118c7a 8 3) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 3] []) (.flag .CF)) #v[420, 338]
    (.letOp (n := 427) (.exec 0x118c7a (fun s => s.RIP = 0x118c7a) (addR64R64Effect 0x118c7a 8 3) (Reg.operands [.gpr 8, .gpr 3] [])) #v[420, 338]
    (.letOp (n := 428) (.out 0x118c7d (atFlags StatusFlags.CF (adcR64Imm8Effect 0x118c7d 9 0x0)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[423, 426]
    (.letOp (n := 429) (.exec 0x118c7d (fun s => s.RIP = 0x118c7d) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x118c7d 9 0x0)) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[423, 426]
    (.letOp (n := 430) (.out 0x118c81 (shldR64R64Effect 0x118c81 5 9 8 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[428, 425]
    (.letOp (n := 431) (.exec 0x118c81 (fun s => s.RIP = 0x118c81) (shldR64R64Effect 0x118c81 5 9 8 12) (Reg.operands [.gpr 9, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[428, 425]
    (.letOp (n := 432) (.out 0x118c86 (movR64R64Effect 0x118c86 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[382]
    (.letOp (n := 433) (.exec 0x118c86 (fun s => s.RIP = 0x118c86) (movR64R64Effect 0x118c86 0 1) (Reg.operands [.gpr 1] [])) #v[382]
    (.letOp (n := 434) (.out 0x118c89 (mulM64Effect 0x118c89 8 (.sib 4 none 0 (.d32 0x110))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[432, 4]
    (.letOp (n := 435) (.out 0x118c89 (mulM64Effect 0x118c89 8 (.sib 4 none 0 (.d32 0x110))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[432, 4]
    (.letOp (n := 436) (.exec 0x118c89 (LoadPre 0x118c89 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x118c89 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x118c89 8 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[432, 4]
    (.letOp (n := 437) (.exec 0x118c91 (StorePre 0x118c91 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x118c91 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x118c91 2 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[435, 4]
    (.letOp (n := 438) (.exec 0x118c99 (StorePre 0x118c99 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x118c99 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x118c99 0 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[434, 4]
    (.letOp (n := 439) (.out 0x118ca1 (movR64M64Effect 0x118ca1 0 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 440) (.exec 0x118ca1 (LoadPre 0x118ca1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x118ca1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x118ca1 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 441) (.out 0x118ca6 (mulM64Effect 0x118ca6 8 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[439, 4]
    (.letOp (n := 442) (.out 0x118ca6 (mulM64Effect 0x118ca6 8 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[439, 4]
    (.letOp (n := 443) (.exec 0x118ca6 (LoadPre 0x118ca6 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x118ca6 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x118ca6 8 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[439, 4]
    (.letOp (n := 444) (.out 0x118cae (movR64R64Effect 0x118cae 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[442]
    (.letOp (n := 445) (.exec 0x118cae (fun s => s.RIP = 0x118cae) (movR64R64Effect 0x118cae 14 2) (Reg.operands [.gpr 2] [])) #v[442]
    (b_l118991_9)))))))))))))))))))))))))))))))))))))))))))))

def bytes_l118991_8 : List UInt8 :=
  [0x4C, 0x01, 0xD0, 0x49, 0x83, 0xD3, 0x00, 0x49, 0x0F, 0xA4, 0xC3, 0x0C, 0x48, 0x21, 0xF8, 0x48,
    0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x4D, 0x01, 0xF0, 0x4C,
    0x13, 0x8C, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x49, 0x01, 0xC0, 0x49, 0x11, 0xD1, 0x49, 0x01, 0xD8,
    0x49, 0x83, 0xD1, 0x00, 0x4D, 0x0F, 0xA4, 0xC1, 0x0C, 0x48, 0x89, 0xC8, 0x48, 0xF7, 0xA4, 0x24,
    0x10, 0x01, 0x00, 0x00, 0x48, 0x89, 0x94, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24,
    0x10, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x60, 0x48, 0xF7, 0xA4, 0x24, 0x98, 0x00, 0x00,
    0x00, 0x49, 0x89, 0xD6] ++ bytes_l118991_9

theorem code_l118991_8 : ∀ x ∈ codeRange 0x118c4d bytes_l118991_8, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x18c4d 100 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l118991_9

def b_l118991_7 : Block Op Label signature Reg.count 357 :=
  .letOp (n := 357) (.out 0x118bf2 (movR64R64Effect 0x118bf2 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[352]
    (.letOp (n := 358) (.exec 0x118bf2 (fun s => s.RIP = 0x118bf2) (movR64R64Effect 0x118bf2 8 0) (Reg.operands [.gpr 0] [])) #v[352]
    (.letOp (n := 359) (.out 0x118bf5 (movR64M64Effect 0x118bf5 0 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 360) (.exec 0x118bf5 (LoadPre 0x118bf5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x118bf5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x118bf5 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 361) (.out 0x118bfa (mulM64Effect 0x118bfa 8 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[359, 4]
    (.letOp (n := 362) (.out 0x118bfa (mulM64Effect 0x118bfa 8 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[359, 4]
    (.letOp (n := 363) (.exec 0x118bfa (LoadPre 0x118bfa (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x118bfa + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x118bfa 8 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[359, 4]
    (.letOp (n := 364) (.out 0x118c02 (movR64R64Effect 0x118c02 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[361]
    (.letOp (n := 365) (.exec 0x118c02 (fun s => s.RIP = 0x118c02) (movR64R64Effect 0x118c02 12 0) (Reg.operands [.gpr 0] [])) #v[361]
    (.letOp (n := 366) (.out 0x118c05 (movR64R64Effect 0x118c05 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[362]
    (.letOp (n := 367) (.exec 0x118c05 (fun s => s.RIP = 0x118c05) (movR64R64Effect 0x118c05 13 2) (Reg.operands [.gpr 2] [])) #v[362]
    (.letOp (n := 368) (.out 0x118c08 (movR64Imm64Effect 0x118c08 7 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 369) (.exec 0x118c08 (fun s => s.RIP = 0x118c08) (movR64Imm64Effect 0x118c08 7 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 370) (.out 0x118c12 (andR64R64Effect 0x118c12 11 7) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 7] []) (.reg (.gpr 11))) #v[340, 368]
    (.letOp (n := 371) (.exec 0x118c12 (fun s => s.RIP = 0x118c12) (andR64R64Effect 0x118c12 11 7) (Reg.operands [.gpr 11, .gpr 7] [])) #v[340, 368]
    (.letOp (n := 372) (.exec 0x118c15 (StorePre 0x118c15 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x118c15 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x118c15 11 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[370, 4]
    (.letOp (n := 373) (.out 0x118c1d (movR64M64Effect 0x118c1d 0 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 374) (.exec 0x118c1d (LoadPre 0x118c1d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x118c1d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x118c1d 0 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 375) (.out 0x118c22 (mulR64Effect 0x118c22 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[280, 373]
    (.letOp (n := 376) (.out 0x118c22 (mulR64Effect 0x118c22 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[280, 373]
    (.letOp (n := 377) (.exec 0x118c22 (fun s => s.RIP = 0x118c22) (mulR64Effect 0x118c22 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[280, 373]
    (.letOp (n := 378) (.out 0x118c25 (movR64R64Effect 0x118c25 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[376]
    (.letOp (n := 379) (.exec 0x118c25 (fun s => s.RIP = 0x118c25) (movR64R64Effect 0x118c25 11 2) (Reg.operands [.gpr 2] [])) #v[376]
    (.letOp (n := 380) (.out 0x118c28 (movR64R64Effect 0x118c28 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[375]
    (.letOp (n := 381) (.exec 0x118c28 (fun s => s.RIP = 0x118c28) (movR64R64Effect 0x118c28 5 0) (Reg.operands [.gpr 0] [])) #v[375]
    (.letOp (n := 382) (.out 0x118c2b (movR64M64Effect 0x118c2b 1 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 383) (.exec 0x118c2b (LoadPre 0x118c2b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x118c2b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x118c2b 1 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 384) (.out 0x118c33 (movR64R64Effect 0x118c33 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[382]
    (.letOp (n := 385) (.exec 0x118c33 (fun s => s.RIP = 0x118c33) (movR64R64Effect 0x118c33 0 1) (Reg.operands [.gpr 1] [])) #v[382]
    (.letOp (n := 386) (.out 0x118c36 (movR64M64Effect 0x118c36 15 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 387) (.exec 0x118c36 (LoadPre 0x118c36 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x118c36 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x118c36 15 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 388) (.out 0x118c3e (mulR64Effect 0x118c3e 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15, .gpr 0] []) (.reg (.gpr 0))) #v[386, 384]
    (.letOp (n := 389) (.out 0x118c3e (mulR64Effect 0x118c3e 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15, .gpr 0] []) (.reg (.gpr 2))) #v[386, 384]
    (.letOp (n := 390) (.exec 0x118c3e (fun s => s.RIP = 0x118c3e) (mulR64Effect 0x118c3e 15) (Reg.operands [.gpr 15, .gpr 0] [])) #v[386, 384]
    (.letOp (n := 391) (.out 0x118c41 (addR64R64Effect 0x118c41 5 12) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 12] []) (.reg (.gpr 5))) #v[380, 364]
    (.letOp (n := 392) (.out 0x118c41 (addR64R64Effect 0x118c41 5 12) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 12] []) (.flag .CF)) #v[380, 364]
    (.letOp (n := 393) (.exec 0x118c41 (fun s => s.RIP = 0x118c41) (addR64R64Effect 0x118c41 5 12) (Reg.operands [.gpr 5, .gpr 12] [])) #v[380, 364]
    (.letOp (n := 394) (.out 0x118c44 (atFlags StatusFlags.CF (adcR64R64Effect 0x118c44 11 13)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[378, 366, 392]
    (.letOp (n := 395) (.exec 0x118c44 (fun s => s.RIP = 0x118c44) (atFlags StatusFlags.CF (adcR64R64Effect 0x118c44 11 13)) (Reg.operands [.gpr 11, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[378, 366, 392]
    (.letOp (n := 396) (.out 0x118c47 (addR64R64Effect 0x118c47 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[388, 391]
    (.letOp (n := 397) (.out 0x118c47 (addR64R64Effect 0x118c47 0 5) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 5] []) (.flag .CF)) #v[388, 391]
    (.letOp (n := 398) (.exec 0x118c47 (fun s => s.RIP = 0x118c47) (addR64R64Effect 0x118c47 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[388, 391]
    (.letOp (n := 399) (.out 0x118c4a (atFlags StatusFlags.CF (adcR64R64Effect 0x118c4a 11 2)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[394, 389, 397]
    (.letOp (n := 400) (.exec 0x118c4a (fun s => s.RIP = 0x118c4a) (atFlags StatusFlags.CF (adcR64R64Effect 0x118c4a 11 2)) (Reg.operands [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[394, 389, 397]
    (b_l118991_8))))))))))))))))))))))))))))))))))))))))))))

def bytes_l118991_7 : List UInt8 :=
  [0x49, 0x89, 0xC0, 0x48, 0x8B, 0x44, 0x24, 0x58, 0x48, 0xF7, 0xA4, 0x24, 0xC8, 0x00, 0x00, 0x00,
    0x49, 0x89, 0xC4, 0x49, 0x89, 0xD5, 0x48, 0xBF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00,
    0x49, 0x21, 0xFB, 0x4C, 0x89, 0x9C, 0x24, 0xE0, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x50,
    0x48, 0xF7, 0xE5, 0x49, 0x89, 0xD3, 0x48, 0x89, 0xC5, 0x48, 0x8B, 0x8C, 0x24, 0x80, 0x00, 0x00,
    0x00, 0x48, 0x89, 0xC8, 0x4C, 0x8B, 0xBC, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE7, 0x4C,
    0x01, 0xE5, 0x4D, 0x11, 0xEB, 0x48, 0x01, 0xE8, 0x49, 0x11, 0xD3] ++ bytes_l118991_8

theorem code_l118991_7 : ∀ x ∈ codeRange 0x118bf2 bytes_l118991_7, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x18bf2 91 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l118991_8

def b_l118991_6 : Block Op Label signature Reg.count 314 :=
  .letOp (n := 314) (.out 0x118b91 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x118b91 10 0x0)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[309, 312]
    (.letOp (n := 315) (.exec 0x118b91 (fun s => s.RIP = 0x118b91) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x118b91 10 0x0)) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[309, 312]
    (.letOp (n := 316) (.out 0x118b95 (shldR64R64Effect 0x118b95 5 10 0 12) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[314, 311]
    (.letOp (n := 317) (.exec 0x118b95 (fun s => s.RIP = 0x118b95) (shldR64R64Effect 0x118b95 5 10 0 12) (Reg.operands [.gpr 10, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[314, 311]
    (.letOp (n := 318) (.out 0x118b9a (shlR64Effect 0x118b9a 4 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[311]
    (.letOp (n := 319) (.exec 0x118b9a (fun s => s.RIP = 0x118b9a) (shlR64Effect 0x118b9a 4 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[311]
    (.letOp (n := 320) (.out 0x118b9e (movR64Imm64Effect 0x118b9e 2 0xfffffffffffff0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 321) (.exec 0x118b9e (fun s => s.RIP = 0x118b9e) (movR64Imm64Effect 0x118b9e 2 0xfffffffffffff0) (Reg.operands [] [])) #v[]
    (.letOp (n := 322) (.out 0x118ba8 (andR64R64Effect 0x118ba8 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[318, 320]
    (.letOp (n := 323) (.exec 0x118ba8 (fun s => s.RIP = 0x118ba8) (andR64R64Effect 0x118ba8 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[318, 320]
    (.letOp (n := 324) (.out 0x118bab (orR64R64Effect 0x118bab 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 13] []) (.reg (.gpr 0))) #v[322, 267]
    (.letOp (n := 325) (.exec 0x118bab (fun s => s.RIP = 0x118bab) (orR64R64Effect 0x118bab 0 13) (Reg.operands [.gpr 0, .gpr 13] [])) #v[322, 267]
    (.letOp (n := 326) (.out 0x118bae (movR64Imm64Effect 0x118bae 2 0x1000003d1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 327) (.exec 0x118bae (fun s => s.RIP = 0x118bae) (movR64Imm64Effect 0x118bae 2 0x1000003d1) (Reg.operands [] [])) #v[]
    (.letOp (n := 328) (.out 0x118bb8 (mulR64Effect 0x118bb8 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[326, 324]
    (.letOp (n := 329) (.out 0x118bb8 (mulR64Effect 0x118bb8 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[326, 324]
    (.letOp (n := 330) (.exec 0x118bb8 (fun s => s.RIP = 0x118bb8) (mulR64Effect 0x118bb8 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[326, 324]
    (.letOp (n := 331) (.out 0x118bbb (movR64R64Effect 0x118bbb 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[329]
    (.letOp (n := 332) (.exec 0x118bbb (fun s => s.RIP = 0x118bbb) (movR64R64Effect 0x118bbb 3 2) (Reg.operands [.gpr 2] [])) #v[329]
    (.letOp (n := 333) (.out 0x118bbe (addR64M64Effect 0x118bbe 0 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[328, 4]
    (.letOp (n := 334) (.out 0x118bbe (addR64M64Effect 0x118bbe 0 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 4] []) (.flag .CF)) #v[328, 4]
    (.letOp (n := 335) (.exec 0x118bbe (LoadPre 0x118bbe (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x118bbe + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x118bbe 0 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[328, 4]
    (.letOp (n := 336) (.out 0x118bc6 (atFlags StatusFlags.CF (adcR64M64Effect 0x118bc6 3 (.sib 4 none 0 (.d32 0xe0)))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 3))) #v[331, 4, 334]
    (.letOp (n := 337) (.exec 0x118bc6 (LoadPre 0x118bc6 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x118bc6 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x118bc6 3 (.sib 4 none 0 (.d32 0xe0)))) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[331, 4, 334]
    (.letOp (n := 338) (.out 0x118bce (shldR64R64Effect 0x118bce 5 3 0 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[336, 333]
    (.letOp (n := 339) (.exec 0x118bce (fun s => s.RIP = 0x118bce) (shldR64R64Effect 0x118bce 5 3 0 12) (Reg.operands [.gpr 3, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[336, 333]
    (.letOp (n := 340) (.out 0x118bd3 (movR64R64Effect 0x118bd3 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[333]
    (.letOp (n := 341) (.exec 0x118bd3 (fun s => s.RIP = 0x118bd3) (movR64R64Effect 0x118bd3 11 0) (Reg.operands [.gpr 0] [])) #v[333]
    (.letOp (n := 342) (.out 0x118bd6 (movR64R64Effect 0x118bd6 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[289]
    (.letOp (n := 343) (.exec 0x118bd6 (fun s => s.RIP = 0x118bd6) (movR64R64Effect 0x118bd6 0 1) (Reg.operands [.gpr 1] [])) #v[289]
    (.letOp (n := 344) (.out 0x118bd9 (mulR64Effect 0x118bd9 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[249, 342]
    (.letOp (n := 345) (.out 0x118bd9 (mulR64Effect 0x118bd9 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[249, 342]
    (.letOp (n := 346) (.exec 0x118bd9 (fun s => s.RIP = 0x118bd9) (mulR64Effect 0x118bd9 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[249, 342]
    (.letOp (n := 347) (.exec 0x118bdc (StorePre 0x118bdc 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x118bdc + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x118bdc 2 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[345, 4]
    (.letOp (n := 348) (.out 0x118be4 (movR64R64Effect 0x118be4 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[344]
    (.letOp (n := 349) (.exec 0x118be4 (fun s => s.RIP = 0x118be4) (movR64R64Effect 0x118be4 14 0) (Reg.operands [.gpr 0] [])) #v[344]
    (.letOp (n := 350) (.out 0x118be7 (movR64M64Effect 0x118be7 0 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 351) (.exec 0x118be7 (LoadPre 0x118be7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x118be7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x118be7 0 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 352) (.out 0x118bec (mulR64Effect 0x118bec 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[258, 350]
    (.letOp (n := 353) (.out 0x118bec (mulR64Effect 0x118bec 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[258, 350]
    (.letOp (n := 354) (.exec 0x118bec (fun s => s.RIP = 0x118bec) (mulR64Effect 0x118bec 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[258, 350]
    (.letOp (n := 355) (.out 0x118bef (movR64R64Effect 0x118bef 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[353]
    (.letOp (n := 356) (.exec 0x118bef (fun s => s.RIP = 0x118bef) (movR64R64Effect 0x118bef 9 2) (Reg.operands [.gpr 2] [])) #v[353]
    (b_l118991_7)))))))))))))))))))))))))))))))))))))))))))

def bytes_l118991_6 : List UInt8 :=
  [0x49, 0x83, 0xD2, 0x00, 0x49, 0x0F, 0xA4, 0xC2, 0x0C, 0x48, 0xC1, 0xE0, 0x04, 0x48, 0xBA, 0xF0,
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x48, 0x21, 0xD0, 0x4C, 0x09, 0xE8, 0x48, 0xBA, 0xD1,
    0x03, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x48, 0x89, 0xD3, 0x48, 0x03, 0x84,
    0x24, 0xD8, 0x00, 0x00, 0x00, 0x48, 0x13, 0x9C, 0x24, 0xE0, 0x00, 0x00, 0x00, 0x48, 0x0F, 0xA4,
    0xC3, 0x0C, 0x49, 0x89, 0xC3, 0x48, 0x89, 0xC8, 0x49, 0xF7, 0xE0, 0x48, 0x89, 0x94, 0x24, 0xD8,
    0x00, 0x00, 0x00, 0x49, 0x89, 0xC6, 0x48, 0x8B, 0x44, 0x24, 0x78, 0x49, 0xF7, 0xE1, 0x49, 0x89,
    0xD1] ++ bytes_l118991_7

theorem code_l118991_6 : ∀ x ∈ codeRange 0x118b91 bytes_l118991_6, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x18b91 97 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l118991_7

def b_l118991_5 : Block Op Label signature Reg.count 267 :=
  .letOp (n := 267) (.out 0x118b3c (andR32Imm8Effect 0x118b3c 4 13 0xf) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[245]
    (.letOp (n := 268) (.exec 0x118b3c (fun s => s.RIP = 0x118b3c) (andR32Imm8Effect 0x118b3c 4 13 0xf) (Reg.operands [.gpr 13] [])) #v[245]
    (.letOp (n := 269) (.out 0x118b40 (movR64M64Effect 0x118b40 0 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 270) (.exec 0x118b40 (LoadPre 0x118b40 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x118b40 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x118b40 0 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 271) (.out 0x118b45 (mulM64Effect 0x118b45 8 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[269, 4]
    (.letOp (n := 272) (.out 0x118b45 (mulM64Effect 0x118b45 8 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[269, 4]
    (.letOp (n := 273) (.exec 0x118b45 (LoadPre 0x118b45 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x118b45 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x118b45 8 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[269, 4]
    (.letOp (n := 274) (.out 0x118b4d (movR64R64Effect 0x118b4d 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[272]
    (.letOp (n := 275) (.exec 0x118b4d (fun s => s.RIP = 0x118b4d) (movR64R64Effect 0x118b4d 10 2) (Reg.operands [.gpr 2] [])) #v[272]
    (.letOp (n := 276) (.out 0x118b50 (movR64R64Effect 0x118b50 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[271]
    (.letOp (n := 277) (.exec 0x118b50 (fun s => s.RIP = 0x118b50) (movR64R64Effect 0x118b50 14 0) (Reg.operands [.gpr 0] [])) #v[271]
    (.letOp (n := 278) (.out 0x118b53 (movR64M64Effect 0x118b53 0 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 279) (.exec 0x118b53 (LoadPre 0x118b53 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x118b53 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x118b53 0 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 280) (.out 0x118b5b (movR64M64Effect 0x118b5b 5 (.sib 4 none 0 (.d32 0xe8))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 281) (.exec 0x118b5b (LoadPre 0x118b5b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x118b5b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x118b5b 5 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 282) (.out 0x118b63 (mulR64Effect 0x118b63 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[280, 278]
    (.letOp (n := 283) (.out 0x118b63 (mulR64Effect 0x118b63 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[280, 278]
    (.letOp (n := 284) (.exec 0x118b63 (fun s => s.RIP = 0x118b63) (mulR64Effect 0x118b63 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[280, 278]
    (.letOp (n := 285) (.out 0x118b66 (movR64R64Effect 0x118b66 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[283]
    (.letOp (n := 286) (.exec 0x118b66 (fun s => s.RIP = 0x118b66) (movR64R64Effect 0x118b66 15 2) (Reg.operands [.gpr 2] [])) #v[283]
    (.letOp (n := 287) (.out 0x118b69 (movR64R64Effect 0x118b69 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[282]
    (.letOp (n := 288) (.exec 0x118b69 (fun s => s.RIP = 0x118b69) (movR64R64Effect 0x118b69 12 0) (Reg.operands [.gpr 0] [])) #v[282]
    (.letOp (n := 289) (.out 0x118b6c (movR64M64Effect 0x118b6c 1 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 290) (.exec 0x118b6c (LoadPre 0x118b6c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x118b6c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x118b6c 1 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 291) (.out 0x118b71 (movR64R64Effect 0x118b71 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[289]
    (.letOp (n := 292) (.exec 0x118b71 (fun s => s.RIP = 0x118b71) (movR64R64Effect 0x118b71 0 1) (Reg.operands [.gpr 1] [])) #v[289]
    (.letOp (n := 293) (.out 0x118b74 (mulM64Effect 0x118b74 8 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[291, 4]
    (.letOp (n := 294) (.out 0x118b74 (mulM64Effect 0x118b74 8 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[291, 4]
    (.letOp (n := 295) (.exec 0x118b74 (LoadPre 0x118b74 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x118b74 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x118b74 8 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[291, 4]
    (.letOp (n := 296) (.out 0x118b7c (addR64R64Effect 0x118b7c 14 11) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 11] []) (.reg (.gpr 14))) #v[276, 263]
    (.letOp (n := 297) (.out 0x118b7c (addR64R64Effect 0x118b7c 14 11) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 11] []) (.flag .CF)) #v[276, 263]
    (.letOp (n := 298) (.exec 0x118b7c (fun s => s.RIP = 0x118b7c) (addR64R64Effect 0x118b7c 14 11) (Reg.operands [.gpr 14, .gpr 11] [])) #v[276, 263]
    (.letOp (n := 299) (.out 0x118b7f (atFlags StatusFlags.CF (adcR64R64Effect 0x118b7f 10 3)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[274, 265, 297]
    (.letOp (n := 300) (.exec 0x118b7f (fun s => s.RIP = 0x118b7f) (atFlags StatusFlags.CF (adcR64R64Effect 0x118b7f 10 3)) (Reg.operands [.gpr 10, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[274, 265, 297]
    (.letOp (n := 301) (.out 0x118b82 (addR64R64Effect 0x118b82 14 12) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 12] []) (.reg (.gpr 14))) #v[296, 287]
    (.letOp (n := 302) (.out 0x118b82 (addR64R64Effect 0x118b82 14 12) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 12] []) (.flag .CF)) #v[296, 287]
    (.letOp (n := 303) (.exec 0x118b82 (fun s => s.RIP = 0x118b82) (addR64R64Effect 0x118b82 14 12) (Reg.operands [.gpr 14, .gpr 12] [])) #v[296, 287]
    (.letOp (n := 304) (.out 0x118b85 (atFlags StatusFlags.CF (adcR64R64Effect 0x118b85 10 15)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[299, 285, 302]
    (.letOp (n := 305) (.exec 0x118b85 (fun s => s.RIP = 0x118b85) (atFlags StatusFlags.CF (adcR64R64Effect 0x118b85 10 15)) (Reg.operands [.gpr 10, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[299, 285, 302]
    (.letOp (n := 306) (.out 0x118b88 (addR64R64Effect 0x118b88 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[293, 301]
    (.letOp (n := 307) (.out 0x118b88 (addR64R64Effect 0x118b88 0 14) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 14] []) (.flag .CF)) #v[293, 301]
    (.letOp (n := 308) (.exec 0x118b88 (fun s => s.RIP = 0x118b88) (addR64R64Effect 0x118b88 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[293, 301]
    (.letOp (n := 309) (.out 0x118b8b (atFlags StatusFlags.CF (adcR64R64Effect 0x118b8b 10 2)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[304, 294, 307]
    (.letOp (n := 310) (.exec 0x118b8b (fun s => s.RIP = 0x118b8b) (atFlags StatusFlags.CF (adcR64R64Effect 0x118b8b 10 2)) (Reg.operands [.gpr 10, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[304, 294, 307]
    (.letOp (n := 311) (.out 0x118b8e (addR64R64Effect 0x118b8e 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[306, 241]
    (.letOp (n := 312) (.out 0x118b8e (addR64R64Effect 0x118b8e 0 7) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 7] []) (.flag .CF)) #v[306, 241]
    (.letOp (n := 313) (.exec 0x118b8e (fun s => s.RIP = 0x118b8e) (addR64R64Effect 0x118b8e 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[306, 241]
    (b_l118991_6)))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l118991_5 : List UInt8 :=
  [0x41, 0x83, 0xE5, 0x0F, 0x48, 0x8B, 0x44, 0x24, 0x50, 0x48, 0xF7, 0xA4, 0x24, 0xC8, 0x00, 0x00,
    0x00, 0x49, 0x89, 0xD2, 0x49, 0x89, 0xC6, 0x48, 0x8B, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48,
    0x8B, 0xAC, 0x24, 0xE8, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE5, 0x49, 0x89, 0xD7, 0x49, 0x89, 0xC4,
    0x48, 0x8B, 0x4C, 0x24, 0x60, 0x48, 0x89, 0xC8, 0x48, 0xF7, 0xA4, 0x24, 0xB8, 0x00, 0x00, 0x00,
    0x4D, 0x01, 0xDE, 0x49, 0x11, 0xDA, 0x4D, 0x01, 0xE6, 0x4D, 0x11, 0xFA, 0x4C, 0x01, 0xF0, 0x49,
    0x11, 0xD2, 0x48, 0x01, 0xF8] ++ bytes_l118991_6

theorem code_l118991_5 : ∀ x ∈ codeRange 0x118b3c bytes_l118991_5, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x18b3c 85 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l118991_6

def b_l118991_4 : Block Op Label signature Reg.count 224 :=
  .letOp (n := 224) (.out 0x118ae6 (atFlags StatusFlags.CF (adcR64R64Effect 0x118ae6 7 15)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[219, 185, 222]
    (.letOp (n := 225) (.exec 0x118ae6 (fun s => s.RIP = 0x118ae6) (atFlags StatusFlags.CF (adcR64R64Effect 0x118ae6 7 15)) (Reg.operands [.gpr 7, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[219, 185, 222]
    (.letOp (n := 226) (.out 0x118ae9 (addR64R64Effect 0x118ae9 6 11) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 11] []) (.reg (.gpr 6))) #v[221, 196]
    (.letOp (n := 227) (.out 0x118ae9 (addR64R64Effect 0x118ae9 6 11) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 11] []) (.flag .CF)) #v[221, 196]
    (.letOp (n := 228) (.exec 0x118ae9 (fun s => s.RIP = 0x118ae9) (addR64R64Effect 0x118ae9 6 11) (Reg.operands [.gpr 6, .gpr 11] [])) #v[221, 196]
    (.letOp (n := 229) (.out 0x118aec (atFlags StatusFlags.CF (adcR64R64Effect 0x118aec 7 5)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[224, 198, 227]
    (.letOp (n := 230) (.exec 0x118aec (fun s => s.RIP = 0x118aec) (atFlags StatusFlags.CF (adcR64R64Effect 0x118aec 7 5)) (Reg.operands [.gpr 7, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[224, 198, 227]
    (.letOp (n := 231) (.out 0x118aef (addR64R64Effect 0x118aef 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[226, 206]
    (.letOp (n := 232) (.out 0x118aef (addR64R64Effect 0x118aef 6 0) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 0] []) (.flag .CF)) #v[226, 206]
    (.letOp (n := 233) (.exec 0x118aef (fun s => s.RIP = 0x118aef) (addR64R64Effect 0x118aef 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[226, 206]
    (.letOp (n := 234) (.out 0x118af2 (atFlags StatusFlags.CF (adcR64R64Effect 0x118af2 7 8)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[229, 209, 232]
    (.letOp (n := 235) (.exec 0x118af2 (fun s => s.RIP = 0x118af2) (atFlags StatusFlags.CF (adcR64R64Effect 0x118af2 7 8)) (Reg.operands [.gpr 7, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[229, 209, 232]
    (.letOp (n := 236) (.out 0x118af5 (addR64R64Effect 0x118af5 6 9) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 9] []) (.reg (.gpr 6))) #v[231, 153]
    (.letOp (n := 237) (.out 0x118af5 (addR64R64Effect 0x118af5 6 9) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 9] []) (.flag .CF)) #v[231, 153]
    (.letOp (n := 238) (.exec 0x118af5 (fun s => s.RIP = 0x118af5) (addR64R64Effect 0x118af5 6 9) (Reg.operands [.gpr 6, .gpr 9] [])) #v[231, 153]
    (.letOp (n := 239) (.out 0x118af8 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x118af8 7 0x0)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[234, 237]
    (.letOp (n := 240) (.exec 0x118af8 (fun s => s.RIP = 0x118af8) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x118af8 7 0x0)) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[234, 237]
    (.letOp (n := 241) (.out 0x118afc (shldR64R64Effect 0x118afc 5 7 6 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[239, 236]
    (.letOp (n := 242) (.exec 0x118afc (fun s => s.RIP = 0x118afc) (shldR64R64Effect 0x118afc 5 7 6 12) (Reg.operands [.gpr 7, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[239, 236]
    (.letOp (n := 243) (.out 0x118b01 (movR64R64Effect 0x118b01 13 6) (EffectPart.reads (.reg (.gpr 13)) [.gpr 6] []) (.reg (.gpr 13))) #v[236]
    (.letOp (n := 244) (.exec 0x118b01 (fun s => s.RIP = 0x118b01) (movR64R64Effect 0x118b01 13 6) (Reg.operands [.gpr 6] [])) #v[236]
    (.letOp (n := 245) (.out 0x118b04 (shrR64Effect 0x118b04 4 13 48) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[243]
    (.letOp (n := 246) (.exec 0x118b04 (fun s => s.RIP = 0x118b04) (shrR64Effect 0x118b04 4 13 48) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[243]
    (.letOp (n := 247) (.out 0x118b08 (movR64R64Effect 0x118b08 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[189]
    (.letOp (n := 248) (.exec 0x118b08 (fun s => s.RIP = 0x118b08) (movR64R64Effect 0x118b08 0 10) (Reg.operands [.gpr 10] [])) #v[189]
    (.letOp (n := 249) (.out 0x118b0b (movR64M64Effect 0x118b0b 8 (.sib 4 none 0 (.d32 0x110))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 250) (.exec 0x118b0b (LoadPre 0x118b0b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x118b0b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x118b0b 8 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 251) (.out 0x118b13 (mulR64Effect 0x118b13 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[249, 247]
    (.letOp (n := 252) (.out 0x118b13 (mulR64Effect 0x118b13 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[249, 247]
    (.letOp (n := 253) (.exec 0x118b13 (fun s => s.RIP = 0x118b13) (mulR64Effect 0x118b13 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[249, 247]
    (.letOp (n := 254) (.exec 0x118b16 (StorePre 0x118b16 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x118b16 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x118b16 2 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[252, 4]
    (.letOp (n := 255) (.exec 0x118b1e (StorePre 0x118b1e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x118b1e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x118b1e 0 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[251, 4]
    (.letOp (n := 256) (.out 0x118b26 (movR64M64Effect 0x118b26 0 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 257) (.exec 0x118b26 (LoadPre 0x118b26 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x118b26 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x118b26 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 258) (.out 0x118b2b (movR64M64Effect 0x118b2b 9 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 259) (.exec 0x118b2b (LoadPre 0x118b2b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x118b2b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x118b2b 9 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 260) (.out 0x118b33 (mulR64Effect 0x118b33 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[258, 256]
    (.letOp (n := 261) (.out 0x118b33 (mulR64Effect 0x118b33 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[258, 256]
    (.letOp (n := 262) (.exec 0x118b33 (fun s => s.RIP = 0x118b33) (mulR64Effect 0x118b33 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[258, 256]
    (.letOp (n := 263) (.out 0x118b36 (movR64R64Effect 0x118b36 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[260]
    (.letOp (n := 264) (.exec 0x118b36 (fun s => s.RIP = 0x118b36) (movR64R64Effect 0x118b36 11 0) (Reg.operands [.gpr 0] [])) #v[260]
    (.letOp (n := 265) (.out 0x118b39 (movR64R64Effect 0x118b39 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[261]
    (.letOp (n := 266) (.exec 0x118b39 (fun s => s.RIP = 0x118b39) (movR64R64Effect 0x118b39 3 2) (Reg.operands [.gpr 2] [])) #v[261]
    (b_l118991_5)))))))))))))))))))))))))))))))))))))))))))

def bytes_l118991_4 : List UInt8 :=
  [0x4C, 0x11, 0xFF, 0x4C, 0x01, 0xDE, 0x48, 0x11, 0xEF, 0x48, 0x01, 0xC6, 0x4C, 0x11, 0xC7, 0x4C,
    0x01, 0xCE, 0x48, 0x83, 0xD7, 0x00, 0x48, 0x0F, 0xA4, 0xF7, 0x0C, 0x49, 0x89, 0xF5, 0x49, 0xC1,
    0xED, 0x30, 0x4C, 0x89, 0xD0, 0x4C, 0x8B, 0x84, 0x24, 0x10, 0x01, 0x00, 0x00, 0x49, 0xF7, 0xE0,
    0x48, 0x89, 0x94, 0x24, 0xE0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0xD8, 0x00, 0x00, 0x00,
    0x48, 0x8B, 0x44, 0x24, 0x58, 0x4C, 0x8B, 0x8C, 0x24, 0x98, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE1,
    0x49, 0x89, 0xC3, 0x48, 0x89, 0xD3] ++ bytes_l118991_5

theorem code_l118991_4 : ∀ x ∈ codeRange 0x118ae6 bytes_l118991_4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x18ae6 86 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l118991_5

def b_l118991_3 : Block Op Label signature Reg.count 178 :=
  .letOp (n := 178) (.out 0x118a9c (movR64R64Effect 0x118a9c 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[173]
    (.letOp (n := 179) (.exec 0x118a9c (fun s => s.RIP = 0x118a9c) (movR64R64Effect 0x118a9c 12 0) (Reg.operands [.gpr 0] [])) #v[173]
    (.letOp (n := 180) (.out 0x118a9f (movR64R64Effect 0x118a9f 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[90]
    (.letOp (n := 181) (.exec 0x118a9f (fun s => s.RIP = 0x118a9f) (movR64R64Effect 0x118a9f 0 15) (Reg.operands [.gpr 15] [])) #v[90]
    (.letOp (n := 182) (.out 0x118aa2 (mulR64Effect 0x118aa2 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[60, 180]
    (.letOp (n := 183) (.out 0x118aa2 (mulR64Effect 0x118aa2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[60, 180]
    (.letOp (n := 184) (.exec 0x118aa2 (fun s => s.RIP = 0x118aa2) (mulR64Effect 0x118aa2 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[60, 180]
    (.letOp (n := 185) (.out 0x118aa5 (movR64R64Effect 0x118aa5 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[183]
    (.letOp (n := 186) (.exec 0x118aa5 (fun s => s.RIP = 0x118aa5) (movR64R64Effect 0x118aa5 15 2) (Reg.operands [.gpr 2] [])) #v[183]
    (.letOp (n := 187) (.out 0x118aa8 (movR64R64Effect 0x118aa8 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[182]
    (.letOp (n := 188) (.exec 0x118aa8 (fun s => s.RIP = 0x118aa8) (movR64R64Effect 0x118aa8 13 0) (Reg.operands [.gpr 0] [])) #v[182]
    (.letOp (n := 189) (.out 0x118aab (movR64M64Effect 0x118aab 10 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 190) (.exec 0x118aab (LoadPre 0x118aab (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x118aab + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x118aab 10 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 191) (.out 0x118ab0 (movR64R64Effect 0x118ab0 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[189]
    (.letOp (n := 192) (.exec 0x118ab0 (fun s => s.RIP = 0x118ab0) (movR64R64Effect 0x118ab0 0 10) (Reg.operands [.gpr 10] [])) #v[189]
    (.letOp (n := 193) (.out 0x118ab3 (mulR64Effect 0x118ab3 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[62, 191]
    (.letOp (n := 194) (.out 0x118ab3 (mulR64Effect 0x118ab3 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[62, 191]
    (.letOp (n := 195) (.exec 0x118ab3 (fun s => s.RIP = 0x118ab3) (mulR64Effect 0x118ab3 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[62, 191]
    (.letOp (n := 196) (.out 0x118ab6 (movR64R64Effect 0x118ab6 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[193]
    (.letOp (n := 197) (.exec 0x118ab6 (fun s => s.RIP = 0x118ab6) (movR64R64Effect 0x118ab6 11 0) (Reg.operands [.gpr 0] [])) #v[193]
    (.letOp (n := 198) (.out 0x118ab9 (movR64R64Effect 0x118ab9 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[194]
    (.letOp (n := 199) (.exec 0x118ab9 (fun s => s.RIP = 0x118ab9) (movR64R64Effect 0x118ab9 5 2) (Reg.operands [.gpr 2] [])) #v[194]
    (.letOp (n := 200) (.out 0x118abc (shrR64Effect 0x118abc 4 8 52) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[130]
    (.letOp (n := 201) (.exec 0x118abc (fun s => s.RIP = 0x118abc) (shrR64Effect 0x118abc 4 8 52) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[130]
    (.letOp (n := 202) (.out 0x118ac0 (imulR64R64Effect 0x118ac0 4 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[200, 140]
    (.letOp (n := 203) (.exec 0x118ac0 (fun s => s.RIP = 0x118ac0) (imulR64R64Effect 0x118ac0 4 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[200, 140]
    (.letOp (n := 204) (.out 0x118ac4 (movR64R64Effect 0x118ac4 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[134]
    (.letOp (n := 205) (.exec 0x118ac4 (fun s => s.RIP = 0x118ac4) (movR64R64Effect 0x118ac4 0 3) (Reg.operands [.gpr 3] [])) #v[134]
    (.letOp (n := 206) (.out 0x118ac7 (mulR64Effect 0x118ac7 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[140, 204]
    (.letOp (n := 207) (.out 0x118ac7 (mulR64Effect 0x118ac7 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[140, 204]
    (.letOp (n := 208) (.exec 0x118ac7 (fun s => s.RIP = 0x118ac7) (mulR64Effect 0x118ac7 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[140, 204]
    (.letOp (n := 209) (.out 0x118aca (addR64R64Effect 0x118aca 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2] []) (.reg (.gpr 8))) #v[202, 207]
    (.letOp (n := 210) (.exec 0x118aca (fun s => s.RIP = 0x118aca) (addR64R64Effect 0x118aca 8 2) (Reg.operands [.gpr 8, .gpr 2] [])) #v[202, 207]
    (.letOp (n := 211) (.out 0x118acd (addR64M64Effect 0x118acd 6 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 4] []) (.reg (.gpr 6))) #v[169, 4]
    (.letOp (n := 212) (.out 0x118acd (addR64M64Effect 0x118acd 6 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 4] []) (.flag .CF)) #v[169, 4]
    (.letOp (n := 213) (.exec 0x118acd (LoadPre 0x118acd (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x118acd + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x118acd 6 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[169, 4]
    (.letOp (n := 214) (.out 0x118ad5 (atFlags StatusFlags.CF (adcR64M64Effect 0x118ad5 7 (.sib 4 none 0 (.d32 0xe0)))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 7))) #v[167, 4, 212]
    (.letOp (n := 215) (.exec 0x118ad5 (LoadPre 0x118ad5 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x118ad5 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x118ad5 7 (.sib 4 none 0 (.d32 0xe0)))) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[167, 4, 212]
    (.letOp (n := 216) (.out 0x118add (addR64R64Effect 0x118add 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 12] []) (.reg (.gpr 6))) #v[211, 178]
    (.letOp (n := 217) (.out 0x118add (addR64R64Effect 0x118add 6 12) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 12] []) (.flag .CF)) #v[211, 178]
    (.letOp (n := 218) (.exec 0x118add (fun s => s.RIP = 0x118add) (addR64R64Effect 0x118add 6 12) (Reg.operands [.gpr 6, .gpr 12] [])) #v[211, 178]
    (.letOp (n := 219) (.out 0x118ae0 (atFlags StatusFlags.CF (adcR64R64Effect 0x118ae0 7 14)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[214, 176, 217]
    (.letOp (n := 220) (.exec 0x118ae0 (fun s => s.RIP = 0x118ae0) (atFlags StatusFlags.CF (adcR64R64Effect 0x118ae0 7 14)) (Reg.operands [.gpr 7, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[214, 176, 217]
    (.letOp (n := 221) (.out 0x118ae3 (addR64R64Effect 0x118ae3 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 13] []) (.reg (.gpr 6))) #v[216, 187]
    (.letOp (n := 222) (.out 0x118ae3 (addR64R64Effect 0x118ae3 6 13) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 13] []) (.flag .CF)) #v[216, 187]
    (.letOp (n := 223) (.exec 0x118ae3 (fun s => s.RIP = 0x118ae3) (addR64R64Effect 0x118ae3 6 13) (Reg.operands [.gpr 6, .gpr 13] [])) #v[216, 187]
    (b_l118991_4))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l118991_3 : List UInt8 :=
  [0x49, 0x89, 0xC4, 0x4C, 0x89, 0xF8, 0x49, 0xF7, 0xE2, 0x49, 0x89, 0xD7, 0x49, 0x89, 0xC5, 0x4C,
    0x8B, 0x54, 0x24, 0x78, 0x4C, 0x89, 0xD0, 0x48, 0xF7, 0xE5, 0x49, 0x89, 0xC3, 0x48, 0x89, 0xD5,
    0x49, 0xC1, 0xE8, 0x34, 0x4C, 0x0F, 0xAF, 0xC1, 0x48, 0x89, 0xD8, 0x48, 0xF7, 0xE1, 0x49, 0x01,
    0xD0, 0x48, 0x03, 0xB4, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x48, 0x13, 0xBC, 0x24, 0xE0, 0x00, 0x00,
    0x00, 0x4C, 0x01, 0xE6, 0x4C, 0x11, 0xF7, 0x4C, 0x01, 0xEE] ++ bytes_l118991_4

theorem code_l118991_3 : ∀ x ∈ codeRange 0x118a9c bytes_l118991_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x18a9c 74 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l118991_4

def b_l118991_2 : Block Op Label signature Reg.count 136 :=
  .letOp (n := 136) (.out 0x118a3a (movR64Imm64Effect 0x118a3a 1 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 137) (.exec 0x118a3a (fun s => s.RIP = 0x118a3a) (movR64Imm64Effect 0x118a3a 1 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 138) (.out 0x118a44 (andR64R64Effect 0x118a44 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[126, 136]
    (.letOp (n := 139) (.exec 0x118a44 (fun s => s.RIP = 0x118a44) (andR64R64Effect 0x118a44 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[126, 136]
    (.letOp (n := 140) (.out 0x118a47 (movR64Imm64Effect 0x118a47 1 0x1000003d10) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 141) (.exec 0x118a47 (fun s => s.RIP = 0x118a47) (movR64Imm64Effect 0x118a47 1 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 142) (.out 0x118a51 (mulR64Effect 0x118a51 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[140, 138]
    (.letOp (n := 143) (.out 0x118a51 (mulR64Effect 0x118a51 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[140, 138]
    (.letOp (n := 144) (.exec 0x118a51 (fun s => s.RIP = 0x118a51) (mulR64Effect 0x118a51 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[140, 138]
    (.letOp (n := 145) (.out 0x118a54 (movR64R64Effect 0x118a54 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[143]
    (.letOp (n := 146) (.exec 0x118a54 (fun s => s.RIP = 0x118a54) (movR64R64Effect 0x118a54 9 2) (Reg.operands [.gpr 2] [])) #v[143]
    (.letOp (n := 147) (.out 0x118a57 (addR64R64Effect 0x118a57 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[142, 117]
    (.letOp (n := 148) (.out 0x118a57 (addR64R64Effect 0x118a57 0 11) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 11] []) (.flag .CF)) #v[142, 117]
    (.letOp (n := 149) (.exec 0x118a57 (fun s => s.RIP = 0x118a57) (addR64R64Effect 0x118a57 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[142, 117]
    (.letOp (n := 150) (.exec 0x118a5a (StorePre 0x118a5a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x118a5a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x118a5a 0 (.sib 4 none 0 (.d32 0x118))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[147, 4]
    (.letOp (n := 151) (.out 0x118a62 (atFlags StatusFlags.CF (adcR64R64Effect 0x118a62 9 7)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[145, 120, 148]
    (.letOp (n := 152) (.exec 0x118a62 (fun s => s.RIP = 0x118a62) (atFlags StatusFlags.CF (adcR64R64Effect 0x118a62 9 7)) (Reg.operands [.gpr 9, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[145, 120, 148]
    (.letOp (n := 153) (.out 0x118a65 (shldR64R64Effect 0x118a65 5 9 0 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[151, 147]
    (.letOp (n := 154) (.exec 0x118a65 (fun s => s.RIP = 0x118a65) (shldR64R64Effect 0x118a65 5 9 0 12) (Reg.operands [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[151, 147]
    (.letOp (n := 155) (.out 0x118a6a (movR64R64Effect 0x118a6a 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[122]
    (.letOp (n := 156) (.exec 0x118a6a (fun s => s.RIP = 0x118a6a) (movR64R64Effect 0x118a6a 0 6) (Reg.operands [.gpr 6] [])) #v[122]
    (.letOp (n := 157) (.out 0x118a6d (mulR64Effect 0x118a6d 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12, .gpr 0] []) (.reg (.gpr 0))) #v[53, 155]
    (.letOp (n := 158) (.out 0x118a6d (mulR64Effect 0x118a6d 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12, .gpr 0] []) (.reg (.gpr 2))) #v[53, 155]
    (.letOp (n := 159) (.exec 0x118a6d (fun s => s.RIP = 0x118a6d) (mulR64Effect 0x118a6d 12) (Reg.operands [.gpr 12, .gpr 0] [])) #v[53, 155]
    (.letOp (n := 160) (.exec 0x118a70 (StorePre 0x118a70 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x118a70 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x118a70 2 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[158, 4]
    (.letOp (n := 161) (.exec 0x118a78 (StorePre 0x118a78 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x118a78 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x118a78 0 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[157, 4]
    (.letOp (n := 162) (.out 0x118a80 (movR64M64Effect 0x118a80 0 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 163) (.exec 0x118a80 (LoadPre 0x118a80 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x118a80 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x118a80 0 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 164) (.out 0x118a85 (mulM64Effect 0x118a85 8 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[162, 4]
    (.letOp (n := 165) (.out 0x118a85 (mulM64Effect 0x118a85 8 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[162, 4]
    (.letOp (n := 166) (.exec 0x118a85 (LoadPre 0x118a85 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x118a85 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x118a85 8 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[162, 4]
    (.letOp (n := 167) (.out 0x118a8d (movR64R64Effect 0x118a8d 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[165]
    (.letOp (n := 168) (.exec 0x118a8d (fun s => s.RIP = 0x118a8d) (movR64R64Effect 0x118a8d 7 2) (Reg.operands [.gpr 2] [])) #v[165]
    (.letOp (n := 169) (.out 0x118a90 (movR64R64Effect 0x118a90 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[164]
    (.letOp (n := 170) (.exec 0x118a90 (fun s => s.RIP = 0x118a90) (movR64R64Effect 0x118a90 6 0) (Reg.operands [.gpr 0] [])) #v[164]
    (.letOp (n := 171) (.out 0x118a93 (movR64R64Effect 0x118a93 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[74]
    (.letOp (n := 172) (.exec 0x118a93 (fun s => s.RIP = 0x118a93) (movR64R64Effect 0x118a93 0 13) (Reg.operands [.gpr 13] [])) #v[74]
    (.letOp (n := 173) (.out 0x118a96 (mulR64Effect 0x118a96 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[58, 171]
    (.letOp (n := 174) (.out 0x118a96 (mulR64Effect 0x118a96 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[58, 171]
    (.letOp (n := 175) (.exec 0x118a96 (fun s => s.RIP = 0x118a96) (mulR64Effect 0x118a96 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[58, 171]
    (.letOp (n := 176) (.out 0x118a99 (movR64R64Effect 0x118a99 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[174]
    (.letOp (n := 177) (.exec 0x118a99 (fun s => s.RIP = 0x118a99) (movR64R64Effect 0x118a99 14 2) (Reg.operands [.gpr 2] [])) #v[174]
    (b_l118991_3))))))))))))))))))))))))))))))))))))))))))

def bytes_l118991_2 : List UInt8 :=
  [0x48, 0xB9, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48, 0x21, 0xC8, 0x48, 0xB9, 0x10,
    0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE1, 0x49, 0x89, 0xD1, 0x4C, 0x01, 0xD8,
    0x48, 0x89, 0x84, 0x24, 0x18, 0x01, 0x00, 0x00, 0x49, 0x11, 0xF9, 0x49, 0x0F, 0xA4, 0xC1, 0x0C,
    0x48, 0x89, 0xF0, 0x49, 0xF7, 0xE4, 0x48, 0x89, 0x94, 0x24, 0xE0, 0x00, 0x00, 0x00, 0x48, 0x89,
    0x84, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x50, 0x48, 0xF7, 0xA4, 0x24, 0x98,
    0x00, 0x00, 0x00, 0x48, 0x89, 0xD7, 0x48, 0x89, 0xC6, 0x4C, 0x89, 0xE8, 0x49, 0xF7, 0xE6, 0x49,
    0x89, 0xD6] ++ bytes_l118991_3

theorem code_l118991_2 : ∀ x ∈ codeRange 0x118a3a bytes_l118991_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x18a3a 98 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l118991_3

def b_l118991_1 : Block Op Label signature Reg.count 94 :=
  .letOp (n := 94) (.out 0x1189e9 (mulR64Effect 0x1189e9 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[58, 92]
    (.letOp (n := 95) (.out 0x1189e9 (mulR64Effect 0x1189e9 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[58, 92]
    (.letOp (n := 96) (.exec 0x1189e9 (fun s => s.RIP = 0x1189e9) (mulR64Effect 0x1189e9 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[58, 92]
    (.letOp (n := 97) (.exec 0x1189ec (StorePre 0x1189ec 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x1189ec + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1189ec 14 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[58, 4]
    (.letOp (n := 98) (.out 0x1189f4 (movR64R64Effect 0x1189f4 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[95]
    (.letOp (n := 99) (.exec 0x1189f4 (fun s => s.RIP = 0x1189f4) (movR64R64Effect 0x1189f4 1 2) (Reg.operands [.gpr 2] [])) #v[95]
    (.letOp (n := 100) (.out 0x1189f7 (movR64R64Effect 0x1189f7 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[94]
    (.letOp (n := 101) (.exec 0x1189f7 (fun s => s.RIP = 0x1189f7) (movR64R64Effect 0x1189f7 6 0) (Reg.operands [.gpr 0] [])) #v[94]
    (.letOp (n := 102) (.out 0x1189fa (addR64R64Effect 0x1189fa 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 8] []) (.reg (.gpr 6))) #v[100, 85]
    (.letOp (n := 103) (.out 0x1189fa (addR64R64Effect 0x1189fa 6 8) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 8] []) (.flag .CF)) #v[100, 85]
    (.letOp (n := 104) (.exec 0x1189fa (fun s => s.RIP = 0x1189fa) (addR64R64Effect 0x1189fa 6 8) (Reg.operands [.gpr 6, .gpr 8] [])) #v[100, 85]
    (.letOp (n := 105) (.out 0x1189fd (atFlags StatusFlags.CF (adcR64R64Effect 0x1189fd 1 7)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[98, 88, 103]
    (.letOp (n := 106) (.exec 0x1189fd (fun s => s.RIP = 0x1189fd) (atFlags StatusFlags.CF (adcR64R64Effect 0x1189fd 1 7)) (Reg.operands [.gpr 1, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[98, 88, 103]
    (.letOp (n := 107) (.out 0x118a00 (movR64M64Effect 0x118a00 0 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 108) (.exec 0x118a00 (LoadPre 0x118a00 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x118a00 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x118a00 0 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 109) (.out 0x118a05 (mulR64Effect 0x118a05 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[60, 107]
    (.letOp (n := 110) (.out 0x118a05 (mulR64Effect 0x118a05 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[60, 107]
    (.letOp (n := 111) (.exec 0x118a05 (fun s => s.RIP = 0x118a05) (mulR64Effect 0x118a05 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[60, 107]
    (.letOp (n := 112) (.exec 0x118a08 (StorePre 0x118a08 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x118a08 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x118a08 10 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[60, 4]
    (.letOp (n := 113) (.out 0x118a10 (movR64R64Effect 0x118a10 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[110]
    (.letOp (n := 114) (.exec 0x118a10 (fun s => s.RIP = 0x118a10) (movR64R64Effect 0x118a10 7 2) (Reg.operands [.gpr 2] [])) #v[110]
    (.letOp (n := 115) (.out 0x118a13 (movR64R64Effect 0x118a13 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[109]
    (.letOp (n := 116) (.exec 0x118a13 (fun s => s.RIP = 0x118a13) (movR64R64Effect 0x118a13 11 0) (Reg.operands [.gpr 0] [])) #v[109]
    (.letOp (n := 117) (.out 0x118a16 (addR64R64Effect 0x118a16 11 6) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 6] []) (.reg (.gpr 11))) #v[115, 102]
    (.letOp (n := 118) (.out 0x118a16 (addR64R64Effect 0x118a16 11 6) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 6] []) (.flag .CF)) #v[115, 102]
    (.letOp (n := 119) (.exec 0x118a16 (fun s => s.RIP = 0x118a16) (addR64R64Effect 0x118a16 11 6) (Reg.operands [.gpr 11, .gpr 6] [])) #v[115, 102]
    (.letOp (n := 120) (.out 0x118a19 (atFlags StatusFlags.CF (adcR64R64Effect 0x118a19 7 1)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[113, 105, 118]
    (.letOp (n := 121) (.exec 0x118a19 (fun s => s.RIP = 0x118a19) (atFlags StatusFlags.CF (adcR64R64Effect 0x118a19 7 1)) (Reg.operands [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[113, 105, 118]
    (.letOp (n := 122) (.out 0x118a1c (movR64M64Effect 0x118a1c 6 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 123) (.exec 0x118a1c (LoadPre 0x118a1c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x118a1c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x118a1c 6 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 124) (.out 0x118a21 (movR64R64Effect 0x118a21 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[122]
    (.letOp (n := 125) (.exec 0x118a21 (fun s => s.RIP = 0x118a21) (movR64R64Effect 0x118a21 0 6) (Reg.operands [.gpr 6] [])) #v[122]
    (.letOp (n := 126) (.out 0x118a24 (mulR64Effect 0x118a24 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[62, 124]
    (.letOp (n := 127) (.out 0x118a24 (mulR64Effect 0x118a24 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[62, 124]
    (.letOp (n := 128) (.exec 0x118a24 (fun s => s.RIP = 0x118a24) (mulR64Effect 0x118a24 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[62, 124]
    (.letOp (n := 129) (.exec 0x118a27 (StorePre 0x118a27 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x118a27 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x118a27 5 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 130) (.out 0x118a2f (movR64R64Effect 0x118a2f 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[127]
    (.letOp (n := 131) (.exec 0x118a2f (fun s => s.RIP = 0x118a2f) (movR64R64Effect 0x118a2f 8 2) (Reg.operands [.gpr 2] [])) #v[127]
    (.letOp (n := 132) (.out 0x118a32 (movR64R64Effect 0x118a32 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[127]
    (.letOp (n := 133) (.exec 0x118a32 (fun s => s.RIP = 0x118a32) (movR64R64Effect 0x118a32 3 2) (Reg.operands [.gpr 2] [])) #v[127]
    (.letOp (n := 134) (.out 0x118a35 (shldR64R64Effect 0x118a35 5 3 0 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[132, 126]
    (.letOp (n := 135) (.exec 0x118a35 (fun s => s.RIP = 0x118a35) (shldR64R64Effect 0x118a35 5 3 0 12) (Reg.operands [.gpr 3, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[132, 126]
    (b_l118991_2))))))))))))))))))))))))))))))))))))))))))

def bytes_l118991_1 : List UInt8 :=
  [0x49, 0xF7, 0xE6, 0x4C, 0x89, 0xB4, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x48, 0x89, 0xD1, 0x48, 0x89,
    0xC6, 0x4C, 0x01, 0xC6, 0x48, 0x11, 0xF9, 0x48, 0x8B, 0x44, 0x24, 0x78, 0x49, 0xF7, 0xE2, 0x4C,
    0x89, 0x94, 0x24, 0xE8, 0x00, 0x00, 0x00, 0x48, 0x89, 0xD7, 0x49, 0x89, 0xC3, 0x49, 0x01, 0xF3,
    0x48, 0x11, 0xCF, 0x48, 0x8B, 0x74, 0x24, 0x58, 0x48, 0x89, 0xF0, 0x48, 0xF7, 0xE5, 0x48, 0x89,
    0xAC, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x49, 0x89, 0xD0, 0x48, 0x89, 0xD3, 0x48, 0x0F, 0xA4, 0xC3,
    0x0C] ++ bytes_l118991_2

theorem code_l118991_1 : ∀ x ∈ codeRange 0x1189e9 bytes_l118991_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x189e9 81 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l118991_2

def b_l118991 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x118991 (movR64M64Effect 0x118991 12 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 54) (.exec 0x118991 (LoadPre 0x118991 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x118991 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x118991 12 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x118995 (movR64M64Effect 0x118995 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 56) (.exec 0x118995 (LoadPre 0x118995 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x118995 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x118995 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x11899a (StorePre 0x11899a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x11899a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11899a 7 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 58) (.out 0x1189a2 (movR64M64Effect 0x1189a2 14 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 59) (.exec 0x1189a2 (LoadPre 0x1189a2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1189a2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1189a2 14 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.out 0x1189a7 (movR64M64Effect 0x1189a7 10 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 61) (.exec 0x1189a7 (LoadPre 0x1189a7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1189a7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1189a7 10 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.out 0x1189ac (movR64M64Effect 0x1189ac 5 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 63) (.exec 0x1189ac (LoadPre 0x1189ac (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1189ac + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1189ac 5 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x1189b1 (movR64M64Effect 0x1189b1 0 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 65) (.exec 0x1189b1 (LoadPre 0x1189b1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1189b1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1189b1 0 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.out 0x1189b6 (mulR64Effect 0x1189b6 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12, .gpr 0] []) (.reg (.gpr 0))) #v[53, 64]
    (.letOp (n := 67) (.out 0x1189b6 (mulR64Effect 0x1189b6 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12, .gpr 0] []) (.reg (.gpr 2))) #v[53, 64]
    (.letOp (n := 68) (.exec 0x1189b6 (fun s => s.RIP = 0x1189b6) (mulR64Effect 0x1189b6 12) (Reg.operands [.gpr 12, .gpr 0] [])) #v[53, 64]
    (.letOp (n := 69) (.exec 0x1189b9 (StorePre 0x1189b9 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x1189b9 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1189b9 12 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 70) (.out 0x1189c1 (movR64R64Effect 0x1189c1 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[67]
    (.letOp (n := 71) (.exec 0x1189c1 (fun s => s.RIP = 0x1189c1) (movR64R64Effect 0x1189c1 1 2) (Reg.operands [.gpr 2] [])) #v[67]
    (.letOp (n := 72) (.out 0x1189c4 (movR64R64Effect 0x1189c4 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[66]
    (.letOp (n := 73) (.exec 0x1189c4 (fun s => s.RIP = 0x1189c4) (movR64R64Effect 0x1189c4 6 0) (Reg.operands [.gpr 0] [])) #v[66]
    (.letOp (n := 74) (.out 0x1189c7 (movR64M64Effect 0x1189c7 13 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 75) (.exec 0x1189c7 (LoadPre 0x1189c7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1189c7 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1189c7 13 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 76) (.out 0x1189cf (movR64R64Effect 0x1189cf 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[74]
    (.letOp (n := 77) (.exec 0x1189cf (fun s => s.RIP = 0x1189cf) (movR64R64Effect 0x1189cf 0 13) (Reg.operands [.gpr 13] [])) #v[74]
    (.letOp (n := 78) (.out 0x1189d2 (mulR64Effect 0x1189d2 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[55, 76]
    (.letOp (n := 79) (.out 0x1189d2 (mulR64Effect 0x1189d2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[55, 76]
    (.letOp (n := 80) (.exec 0x1189d2 (fun s => s.RIP = 0x1189d2) (mulR64Effect 0x1189d2 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[55, 76]
    (.letOp (n := 81) (.out 0x1189d5 (movR64R64Effect 0x1189d5 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[79]
    (.letOp (n := 82) (.exec 0x1189d5 (fun s => s.RIP = 0x1189d5) (movR64R64Effect 0x1189d5 7 2) (Reg.operands [.gpr 2] [])) #v[79]
    (.letOp (n := 83) (.out 0x1189d8 (movR64R64Effect 0x1189d8 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[78]
    (.letOp (n := 84) (.exec 0x1189d8 (fun s => s.RIP = 0x1189d8) (movR64R64Effect 0x1189d8 8 0) (Reg.operands [.gpr 0] [])) #v[78]
    (.letOp (n := 85) (.out 0x1189db (addR64R64Effect 0x1189db 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6] []) (.reg (.gpr 8))) #v[83, 72]
    (.letOp (n := 86) (.out 0x1189db (addR64R64Effect 0x1189db 8 6) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 6] []) (.flag .CF)) #v[83, 72]
    (.letOp (n := 87) (.exec 0x1189db (fun s => s.RIP = 0x1189db) (addR64R64Effect 0x1189db 8 6) (Reg.operands [.gpr 8, .gpr 6] [])) #v[83, 72]
    (.letOp (n := 88) (.out 0x1189de (atFlags StatusFlags.CF (adcR64R64Effect 0x1189de 7 1)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[81, 70, 86]
    (.letOp (n := 89) (.exec 0x1189de (fun s => s.RIP = 0x1189de) (atFlags StatusFlags.CF (adcR64R64Effect 0x1189de 7 1)) (Reg.operands [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[81, 70, 86]
    (.letOp (n := 90) (.out 0x1189e1 (movR64M64Effect 0x1189e1 15 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 91) (.exec 0x1189e1 (LoadPre 0x1189e1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1189e1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1189e1 15 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 92) (.out 0x1189e6 (movR64R64Effect 0x1189e6 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[90]
    (.letOp (n := 93) (.exec 0x1189e6 (fun s => s.RIP = 0x1189e6) (movR64R64Effect 0x1189e6 0 15) (Reg.operands [.gpr 15] [])) #v[90]
    (b_l118991_1)))))))))))))))))))))))))))))))))))))))))

def bytes_l118991 : List UInt8 :=
  [0x4C, 0x8B, 0x24, 0x24, 0x48, 0x8B, 0x7C, 0x24, 0x08, 0x48, 0x89, 0xBC, 0x24, 0x98, 0x00, 0x00,
    0x00, 0x4C, 0x8B, 0x74, 0x24, 0x10, 0x4C, 0x8B, 0x54, 0x24, 0x18, 0x48, 0x8B, 0x6C, 0x24, 0x20,
    0x48, 0x8B, 0x44, 0x24, 0x50, 0x49, 0xF7, 0xE4, 0x4C, 0x89, 0xA4, 0x24, 0x10, 0x01, 0x00, 0x00,
    0x48, 0x89, 0xD1, 0x48, 0x89, 0xC6, 0x4C, 0x8B, 0xAC, 0x24, 0x80, 0x00, 0x00, 0x00, 0x4C, 0x89,
    0xE8, 0x48, 0xF7, 0xE7, 0x48, 0x89, 0xD7, 0x49, 0x89, 0xC0, 0x49, 0x01, 0xF0, 0x48, 0x11, 0xCF,
    0x4C, 0x8B, 0x7C, 0x24, 0x60, 0x4C, 0x89, 0xF8] ++ bytes_l118991_1

theorem code_l118991 : ∀ x ∈ codeRange 0x118991 bytes_l118991, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x18991 88 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l118991_1

@[cfg_block] def b_l118da2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x118da2 (movR64M64Effect 0x118da2 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x118da2 (LoadPre 0x118da2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x118da2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x118da2 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x118da7 (StorePre 0x118da7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x118da7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x118da7 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x118dac (movR64M64Effect 0x118dac 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x118dac (LoadPre 0x118dac (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x118dac + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x118dac 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x118db1 (StorePre 0x118db1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x118db1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x118db1 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x118db6 (movR64M64Effect 0x118db6 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x118db6 (LoadPre 0x118db6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x118db6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x118db6 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x118dbb (StorePre 0x118dbb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x118dbb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x118dbb 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x118dc0 (movR64M64Effect 0x118dc0 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x118dc0 (LoadPre 0x118dc0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x118dc0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x118dc0 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x118dc5 (movR64M64Effect 0x118dc5 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x118dc5 (LoadPre 0x118dc5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x118dc5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x118dc5 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x118dca (StorePre 0x118dca 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x118dca + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x118dca 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x118dcf (StorePre 0x118dcf 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x118dcf + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x118dcf 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x118dd3 (movR64R64Effect 0x118dd3 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x118dd3 (fun s => s.RIP = 0x118dd3) (movR64R64Effect 0x118dd3 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x118dd6 (movR64R64Effect 0x118dd6 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x118dd6 (fun s => s.RIP = 0x118dd6) (movR64R64Effect 0x118dd6 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x118dd9 (callEffect (fun _ => 0x1145f0) 0x118dde) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x118dd9 (PushPre 0x118dd9 5) (callEffect (fun _ => 0x1145f0) 0x118dde) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x118dde⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l118dde, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l118da2 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x12, 0xB8, 0xFF, 0xFF]

theorem code_l118da2 : ∀ x ∈ codeRange 0x118da2 bytes_l118da2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x18da2 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l118dde : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x118dde (movR64M64Effect 0x118dde 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x118dde (LoadPre 0x118dde (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x118dde + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x118dde 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x118de3 (StorePre 0x118de3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x118de3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x118de3 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x118de8 (movR64M64Effect 0x118de8 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x118de8 (LoadPre 0x118de8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x118de8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x118de8 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x118ded (StorePre 0x118ded 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x118ded + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x118ded 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x118df2 (movR64M64Effect 0x118df2 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x118df2 (LoadPre 0x118df2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x118df2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x118df2 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x118df7 (StorePre 0x118df7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x118df7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x118df7 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x118dfc (movR64M64Effect 0x118dfc 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x118dfc (LoadPre 0x118dfc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x118dfc + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x118dfc 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x118e01 (movR64M64Effect 0x118e01 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x118e01 (LoadPre 0x118e01 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x118e01 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x118e01 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x118e06 (StorePre 0x118e06 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x118e06 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x118e06 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x118e0b (StorePre 0x118e0b 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x118e0b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x118e0b 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x118e0f (movR64R64Effect 0x118e0f 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x118e0f (fun s => s.RIP = 0x118e0f) (movR64R64Effect 0x118e0f 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x118e12 (movR64R64Effect 0x118e12 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x118e12 (fun s => s.RIP = 0x118e12) (movR64R64Effect 0x118e12 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x118e15 (callEffect (fun _ => 0x1145f0) 0x118e1a) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x118e15 (PushPre 0x118e15 5) (callEffect (fun _ => 0x1145f0) 0x118e1a) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x118e1a⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l118e1a, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l118dde : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0xD6, 0xB7, 0xFF, 0xFF]

theorem code_l118dde : ∀ x ∈ codeRange 0x118dde bytes_l118dde, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x18dde 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

def b_l118e1a_12 : Block Op Label signature Reg.count 571 :=
  .letOp (n := 571) (.out 0x119250 (movR64R64Effect 0x119250 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[567]
    (.letOp (n := 572) (.exec 0x119250 (fun s => s.RIP = 0x119250) (movR64R64Effect 0x119250 6 14) (Reg.operands [.gpr 14] [])) #v[567]
    (.letOp (n := 573) (.out 0x119253 (callEffect (fun _ => 0x1145f0) 0x119258) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 574) (.exec 0x119253 (PushPre 0x119253 5) (callEffect (fun _ => 0x1145f0) 0x119258) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 575) (.const ⟨64, 0x119258⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 552), (1, 561), (2, 550), (3, 565), (4, 573), (5, 487), (6, 571), (7, 569), (8, 460), (9, 434), (10, 534), (11, 498), (12, 494), (13, 457), (14, 567), (15, 375), (22, 22), (39, 39), (50, 50), (51, 51)] 576⟩ { target := .l119258, kept := #v[], arity := rfl, guard := some (Fin.last 575) }))))))

def bytes_l118e1a_12 : List UInt8 :=
  [0x4C, 0x89, 0xF6, 0xE8, 0x98, 0xB3, 0xFF, 0xFF]

theorem code_l118e1a_12 : ∀ x ∈ codeRange 0x119250 bytes_l118e1a_12, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x19250 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

def b_l118e1a_11 : Block Op Label signature Reg.count 534 :=
  .letOp (n := 534) (.out 0x1191f9 (andR64R64Effect 0x1191f9 10 12) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 12] []) (.reg (.gpr 10))) #v[519, 494]
    (.letOp (n := 535) (.exec 0x1191f9 (fun s => s.RIP = 0x1191f9) (andR64R64Effect 0x1191f9 10 12) (Reg.operands [.gpr 10, .gpr 12] [])) #v[519, 494]
    (.letOp (n := 536) (.out 0x1191fc (movR64M64Effect 0x1191fc 1 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 537) (.exec 0x1191fc (LoadPre 0x1191fc (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x1191fc + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1191fc 1 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 538) (.out 0x119204 (andR64R64Effect 0x119204 1 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 12] []) (.reg (.gpr 1))) #v[536, 494]
    (.letOp (n := 539) (.exec 0x119204 (fun s => s.RIP = 0x119204) (andR64R64Effect 0x119204 1 12) (Reg.operands [.gpr 1, .gpr 12] [])) #v[536, 494]
    (.letOp (n := 540) (.out 0x119207 (addR64R64Effect 0x119207 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[538, 531]
    (.letOp (n := 541) (.out 0x119207 (addR64R64Effect 0x119207 1 0) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 0] []) (.flag .CF)) #v[538, 531]
    (.letOp (n := 542) (.exec 0x119207 (fun s => s.RIP = 0x119207) (addR64R64Effect 0x119207 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[538, 531]
    (.letOp (n := 543) (.out 0x11920a (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11920a 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[532, 541]
    (.letOp (n := 544) (.exec 0x11920a (fun s => s.RIP = 0x11920a) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11920a 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[532, 541]
    (.letOp (n := 545) (.out 0x11920e (addR64R64Effect 0x11920e 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 3] []) (.reg (.gpr 1))) #v[540, 526]
    (.letOp (n := 546) (.out 0x11920e (addR64R64Effect 0x11920e 1 3) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 3] []) (.flag .CF)) #v[540, 526]
    (.letOp (n := 547) (.exec 0x11920e (fun s => s.RIP = 0x11920e) (addR64R64Effect 0x11920e 1 3) (Reg.operands [.gpr 1, .gpr 3] [])) #v[540, 526]
    (.letOp (n := 548) (.out 0x119211 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x119211 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[543, 546]
    (.letOp (n := 549) (.exec 0x119211 (fun s => s.RIP = 0x119211) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x119211 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[543, 546]
    (.letOp (n := 550) (.out 0x119215 (shldR64R64Effect 0x119215 5 2 1 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[548, 545]
    (.letOp (n := 551) (.exec 0x119215 (fun s => s.RIP = 0x119215) (shldR64R64Effect 0x119215 5 2 1 12) (Reg.operands [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[548, 545]
    (.letOp (n := 552) (.out 0x11921a (movR64Imm64Effect 0x11921a 0 0xffffffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 553) (.exec 0x11921a (fun s => s.RIP = 0x11921a) (movR64Imm64Effect 0x11921a 0 0xffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 554) (.out 0x119224 (andR64R64Effect 0x119224 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[240, 552]
    (.letOp (n := 555) (.exec 0x119224 (fun s => s.RIP = 0x119224) (andR64R64Effect 0x119224 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[240, 552]
    (.letOp (n := 556) (.out 0x119227 (addR64R64Effect 0x119227 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[554, 550]
    (.letOp (n := 557) (.exec 0x119227 (fun s => s.RIP = 0x119227) (addR64R64Effect 0x119227 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[554, 550]
    (.letOp (n := 558) (.exec 0x11922a (StorePre 0x11922a 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x11922a + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11922a 15 (.sib 4 none 0 .none)) (Reg.operands [.gpr 15, .gpr 4] [])) #v[375, 4]
    (.letOp (n := 559) (.exec 0x11922e (StorePre 0x11922e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11922e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11922e 8 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[460, 4]
    (.letOp (n := 560) (.exec 0x119233 (StorePre 0x119233 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x119233 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119233 10 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[534, 4]
    (.letOp (n := 561) (.out 0x119238 (andR64R64Effect 0x119238 1 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 12] []) (.reg (.gpr 1))) #v[545, 494]
    (.letOp (n := 562) (.exec 0x119238 (fun s => s.RIP = 0x119238) (andR64R64Effect 0x119238 1 12) (Reg.operands [.gpr 1, .gpr 12] [])) #v[545, 494]
    (.letOp (n := 563) (.exec 0x11923b (StorePre 0x11923b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11923b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11923b 1 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[561, 4]
    (.letOp (n := 564) (.exec 0x119240 (StorePre 0x119240 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x119240 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119240 6 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[556, 4]
    (.letOp (n := 565) (.out 0x119245 (leaR64Effect 0x119245 3 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 566) (.exec 0x119245 (fun s => s.RIP = 0x119245) (leaR64Effect 0x119245 3 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 567) (.out 0x11924a (movR64R64Effect 0x11924a 14 4) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 568) (.exec 0x11924a (fun s => s.RIP = 0x11924a) (movR64R64Effect 0x11924a 14 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 569) (.out 0x11924d (movR64R64Effect 0x11924d 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[565]
    (.letOp (n := 570) (.exec 0x11924d (fun s => s.RIP = 0x11924d) (movR64R64Effect 0x11924d 7 3) (Reg.operands [.gpr 3] [])) #v[565]
    (b_l118e1a_12)))))))))))))))))))))))))))))))))))))

def bytes_l118e1a_11 : List UInt8 :=
  [0x4D, 0x21, 0xE2, 0x48, 0x8B, 0x8C, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x4C, 0x21, 0xE1, 0x48, 0x01,
    0xC1, 0x48, 0x83, 0xD2, 0x00, 0x48, 0x01, 0xD9, 0x48, 0x83, 0xD2, 0x00, 0x48, 0x0F, 0xA4, 0xCA,
    0x0C, 0x48, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x48, 0x21, 0xC6, 0x48, 0x01,
    0xD6, 0x4C, 0x89, 0x3C, 0x24, 0x4C, 0x89, 0x44, 0x24, 0x08, 0x4C, 0x89, 0x54, 0x24, 0x10, 0x4C,
    0x21, 0xE1, 0x48, 0x89, 0x4C, 0x24, 0x18, 0x48, 0x89, 0x74, 0x24, 0x20, 0x48, 0x8D, 0x5C, 0x24,
    0x28, 0x49, 0x89, 0xE6, 0x48, 0x89, 0xDF] ++ bytes_l118e1a_12

theorem code_l118e1a_11 : ∀ x ∈ codeRange 0x1191f9 bytes_l118e1a_11, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x191f9 87 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l118e1a_12

def b_l118e1a_10 : Block Op Label signature Reg.count 490 :=
  .letOp (n := 490) (.out 0x119199 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x119199 14 0x0)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[485, 488]
    (.letOp (n := 491) (.exec 0x119199 (fun s => s.RIP = 0x119199) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x119199 14 0x0)) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[485, 488]
    (.letOp (n := 492) (.out 0x11919d (movR64R64Effect 0x11919d 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[487]
    (.letOp (n := 493) (.exec 0x11919d (fun s => s.RIP = 0x11919d) (movR64R64Effect 0x11919d 0 5) (Reg.operands [.gpr 5] [])) #v[487]
    (.letOp (n := 494) (.out 0x1191a0 (movR64Imm64Effect 0x1191a0 12 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 12)) [] []) (.reg (.gpr 12))) #v[]
    (.letOp (n := 495) (.exec 0x1191a0 (fun s => s.RIP = 0x1191a0) (movR64Imm64Effect 0x1191a0 12 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 496) (.out 0x1191aa (andR64R64Effect 0x1191aa 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 12] []) (.reg (.gpr 0))) #v[492, 494]
    (.letOp (n := 497) (.exec 0x1191aa (fun s => s.RIP = 0x1191aa) (andR64R64Effect 0x1191aa 0 12) (Reg.operands [.gpr 0, .gpr 12] [])) #v[492, 494]
    (.letOp (n := 498) (.out 0x1191ad (movR64Imm64Effect 0x1191ad 11 0x1000003d10) (EffectPart.reads (.reg (.gpr 11)) [] []) (.reg (.gpr 11))) #v[]
    (.letOp (n := 499) (.exec 0x1191ad (fun s => s.RIP = 0x1191ad) (movR64Imm64Effect 0x1191ad 11 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 500) (.out 0x1191b7 (mulR64Effect 0x1191b7 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[498, 496]
    (.letOp (n := 501) (.out 0x1191b7 (mulR64Effect 0x1191b7 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[498, 496]
    (.letOp (n := 502) (.exec 0x1191b7 (fun s => s.RIP = 0x1191b7) (mulR64Effect 0x1191b7 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[498, 496]
    (.letOp (n := 503) (.out 0x1191ba (addR64M64Effect 0x1191ba 10 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 4] []) (.reg (.gpr 10))) #v[450, 4]
    (.letOp (n := 504) (.out 0x1191ba (addR64M64Effect 0x1191ba 10 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 4] []) (.flag .CF)) #v[450, 4]
    (.letOp (n := 505) (.exec 0x1191ba (LoadPre 0x1191ba (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1191ba + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x1191ba 10 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[450, 4]
    (.letOp (n := 506) (.out 0x1191bf (atFlags StatusFlags.CF (adcR64M64Effect 0x1191bf 3 (.sib 4 none 0 (.d32 0xd0)))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 3))) #v[448, 4, 504]
    (.letOp (n := 507) (.exec 0x1191bf (LoadPre 0x1191bf (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x1191bf + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x1191bf 3 (.sib 4 none 0 (.d32 0xd0)))) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[448, 4, 504]
    (.letOp (n := 508) (.out 0x1191c7 (addR64R64Effect 0x1191c7 10 13) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 13] []) (.reg (.gpr 10))) #v[503, 457]
    (.letOp (n := 509) (.out 0x1191c7 (addR64R64Effect 0x1191c7 10 13) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 13] []) (.flag .CF)) #v[503, 457]
    (.letOp (n := 510) (.exec 0x1191c7 (fun s => s.RIP = 0x1191c7) (addR64R64Effect 0x1191c7 10 13) (Reg.operands [.gpr 10, .gpr 13] [])) #v[503, 457]
    (.letOp (n := 511) (.out 0x1191ca (atFlags StatusFlags.CF (adcR64M64Effect 0x1191ca 3 (.sib 4 none 0 (.d32 0xa0)))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 3))) #v[506, 4, 509]
    (.letOp (n := 512) (.exec 0x1191ca (LoadPre 0x1191ca (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x1191ca + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x1191ca 3 (.sib 4 none 0 (.d32 0xa0)))) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[506, 4, 509]
    (.letOp (n := 513) (.out 0x1191d2 (addR64R64Effect 0x1191d2 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0] []) (.reg (.gpr 10))) #v[508, 500]
    (.letOp (n := 514) (.out 0x1191d2 (addR64R64Effect 0x1191d2 10 0) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 0] []) (.flag .CF)) #v[508, 500]
    (.letOp (n := 515) (.exec 0x1191d2 (fun s => s.RIP = 0x1191d2) (addR64R64Effect 0x1191d2 10 0) (Reg.operands [.gpr 10, .gpr 0] [])) #v[508, 500]
    (.letOp (n := 516) (.out 0x1191d5 (atFlags StatusFlags.CF (adcR64R64Effect 0x1191d5 3 2)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[511, 501, 514]
    (.letOp (n := 517) (.exec 0x1191d5 (fun s => s.RIP = 0x1191d5) (atFlags StatusFlags.CF (adcR64R64Effect 0x1191d5 3 2)) (Reg.operands [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[511, 501, 514]
    (.letOp (n := 518) (.exec 0x1191d8 (StorePre 0x1191d8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1191d8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1191d8 1 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[475, 4]
    (.letOp (n := 519) (.out 0x1191dd (addR64R64Effect 0x1191dd 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9] []) (.reg (.gpr 10))) #v[513, 434]
    (.letOp (n := 520) (.out 0x1191dd (addR64R64Effect 0x1191dd 10 9) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 9] []) (.flag .CF)) #v[513, 434]
    (.letOp (n := 521) (.exec 0x1191dd (fun s => s.RIP = 0x1191dd) (addR64R64Effect 0x1191dd 10 9) (Reg.operands [.gpr 10, .gpr 9] [])) #v[513, 434]
    (.letOp (n := 522) (.out 0x1191e0 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1191e0 3 0x0)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[516, 520]
    (.letOp (n := 523) (.exec 0x1191e0 (fun s => s.RIP = 0x1191e0) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1191e0 3 0x0)) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[516, 520]
    (.letOp (n := 524) (.out 0x1191e4 (shldR64R64Effect 0x1191e4 5 14 5 12) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[490, 487]
    (.letOp (n := 525) (.exec 0x1191e4 (fun s => s.RIP = 0x1191e4) (shldR64R64Effect 0x1191e4 5 14 5 12) (Reg.operands [.gpr 14, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[490, 487]
    (.letOp (n := 526) (.out 0x1191e9 (shldR64R64Effect 0x1191e9 5 3 10 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[522, 519]
    (.letOp (n := 527) (.exec 0x1191e9 (fun s => s.RIP = 0x1191e9) (shldR64R64Effect 0x1191e9 5 3 10 12) (Reg.operands [.gpr 3, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[522, 519]
    (.letOp (n := 528) (.exec 0x1191ee (StorePre 0x1191ee 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1191ee + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1191ee 7 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[464, 4]
    (.letOp (n := 529) (.out 0x1191f3 (movR64R64Effect 0x1191f3 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[524]
    (.letOp (n := 530) (.exec 0x1191f3 (fun s => s.RIP = 0x1191f3) (movR64R64Effect 0x1191f3 0 14) (Reg.operands [.gpr 14] [])) #v[524]
    (.letOp (n := 531) (.out 0x1191f6 (mulR64Effect 0x1191f6 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[498, 529]
    (.letOp (n := 532) (.out 0x1191f6 (mulR64Effect 0x1191f6 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[498, 529]
    (.letOp (n := 533) (.exec 0x1191f6 (fun s => s.RIP = 0x1191f6) (mulR64Effect 0x1191f6 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[498, 529]
    (b_l118e1a_11))))))))))))))))))))))))))))))))))))))))))))

def bytes_l118e1a_10 : List UInt8 :=
  [0x49, 0x83, 0xD6, 0x00, 0x48, 0x89, 0xE8, 0x49, 0xBC, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F,
    0x00, 0x4C, 0x21, 0xE0, 0x49, 0xBB, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x49, 0xF7,
    0xE3, 0x4C, 0x03, 0x54, 0x24, 0x60, 0x48, 0x13, 0x9C, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x4D, 0x01,
    0xEA, 0x48, 0x13, 0x9C, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x49, 0x01, 0xC2, 0x48, 0x11, 0xD3, 0x48,
    0x89, 0x4C, 0x24, 0x20, 0x4D, 0x01, 0xCA, 0x48, 0x83, 0xD3, 0x00, 0x49, 0x0F, 0xA4, 0xEE, 0x0C,
    0x4C, 0x0F, 0xA4, 0xD3, 0x0C, 0x48, 0x89, 0x7C, 0x24, 0x18, 0x4C, 0x89, 0xF0, 0x49, 0xF7, 0xE3] ++ bytes_l118e1a_11

theorem code_l118e1a_10 : ∀ x ∈ codeRange 0x119199 bytes_l118e1a_10, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x19199 96 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l118e1a_11

def b_l118e1a_9 : Block Op Label signature Reg.count 445 :=
  .letOp (n := 445) (.out 0x119140 (mulM64Effect 0x119140 8 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[443, 4]
    (.letOp (n := 446) (.out 0x119140 (mulM64Effect 0x119140 8 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[443, 4]
    (.letOp (n := 447) (.exec 0x119140 (LoadPre 0x119140 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x119140 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x119140 8 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[443, 4]
    (.letOp (n := 448) (.out 0x119148 (movR64R64Effect 0x119148 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[446]
    (.letOp (n := 449) (.exec 0x119148 (fun s => s.RIP = 0x119148) (movR64R64Effect 0x119148 3 2) (Reg.operands [.gpr 2] [])) #v[446]
    (.letOp (n := 450) (.out 0x11914b (movR64R64Effect 0x11914b 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[445]
    (.letOp (n := 451) (.exec 0x11914b (fun s => s.RIP = 0x11914b) (movR64R64Effect 0x11914b 10 0) (Reg.operands [.gpr 0] [])) #v[445]
    (.letOp (n := 452) (.out 0x11914e (movR64M64Effect 0x11914e 0 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 453) (.exec 0x11914e (LoadPre 0x11914e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x11914e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11914e 0 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 454) (.out 0x119156 (mulR64Effect 0x119156 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[364, 452]
    (.letOp (n := 455) (.out 0x119156 (mulR64Effect 0x119156 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[364, 452]
    (.letOp (n := 456) (.exec 0x119156 (fun s => s.RIP = 0x119156) (mulR64Effect 0x119156 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[364, 452]
    (.letOp (n := 457) (.out 0x119159 (movR64R64Effect 0x119159 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[454]
    (.letOp (n := 458) (.exec 0x119159 (fun s => s.RIP = 0x119159) (movR64R64Effect 0x119159 13 0) (Reg.operands [.gpr 0] [])) #v[454]
    (.letOp (n := 459) (.exec 0x11915c (StorePre 0x11915c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x11915c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11915c 2 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[455, 4]
    (.letOp (n := 460) (.out 0x119164 (andR64R64Effect 0x119164 8 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 12] []) (.reg (.gpr 8))) #v[429, 412]
    (.letOp (n := 461) (.exec 0x119164 (fun s => s.RIP = 0x119164) (andR64R64Effect 0x119164 8 12) (Reg.operands [.gpr 8, .gpr 12] [])) #v[429, 412]
    (.letOp (n := 462) (.out 0x119167 (movR64M64Effect 0x119167 0 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 463) (.exec 0x119167 (LoadPre 0x119167 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x119167 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x119167 0 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 464) (.out 0x11916f (movR64M64Effect 0x11916f 7 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 465) (.exec 0x11916f (LoadPre 0x11916f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x11916f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11916f 7 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 466) (.out 0x119174 (mulR64Effect 0x119174 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[464, 462]
    (.letOp (n := 467) (.out 0x119174 (mulR64Effect 0x119174 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 0] []) (.reg (.gpr 2))) #v[464, 462]
    (.letOp (n := 468) (.exec 0x119174 (fun s => s.RIP = 0x119174) (mulR64Effect 0x119174 7) (Reg.operands [.gpr 7, .gpr 0] [])) #v[464, 462]
    (.letOp (n := 469) (.out 0x119177 (movR64R64Effect 0x119177 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[467]
    (.letOp (n := 470) (.exec 0x119177 (fun s => s.RIP = 0x119177) (movR64R64Effect 0x119177 14 2) (Reg.operands [.gpr 2] [])) #v[467]
    (.letOp (n := 471) (.out 0x11917a (movR64R64Effect 0x11917a 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[466]
    (.letOp (n := 472) (.exec 0x11917a (fun s => s.RIP = 0x11917a) (movR64R64Effect 0x11917a 12 0) (Reg.operands [.gpr 0] [])) #v[466]
    (.letOp (n := 473) (.out 0x11917d (movR64M64Effect 0x11917d 0 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 474) (.exec 0x11917d (LoadPre 0x11917d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x11917d + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11917d 0 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 475) (.out 0x119185 (movR64M64Effect 0x119185 1 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 476) (.exec 0x119185 (LoadPre 0x119185 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x119185 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119185 1 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 477) (.out 0x11918a (mulR64Effect 0x11918a 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[475, 473]
    (.letOp (n := 478) (.out 0x11918a (mulR64Effect 0x11918a 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[475, 473]
    (.letOp (n := 479) (.exec 0x11918a (fun s => s.RIP = 0x11918a) (mulR64Effect 0x11918a 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[475, 473]
    (.letOp (n := 480) (.out 0x11918d (movR64R64Effect 0x11918d 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[477]
    (.letOp (n := 481) (.exec 0x11918d (fun s => s.RIP = 0x11918d) (movR64R64Effect 0x11918d 5 0) (Reg.operands [.gpr 0] [])) #v[477]
    (.letOp (n := 482) (.out 0x119190 (addR64R64Effect 0x119190 5 12) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 12] []) (.reg (.gpr 5))) #v[480, 471]
    (.letOp (n := 483) (.out 0x119190 (addR64R64Effect 0x119190 5 12) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 12] []) (.flag .CF)) #v[480, 471]
    (.letOp (n := 484) (.exec 0x119190 (fun s => s.RIP = 0x119190) (addR64R64Effect 0x119190 5 12) (Reg.operands [.gpr 5, .gpr 12] [])) #v[480, 471]
    (.letOp (n := 485) (.out 0x119193 (atFlags StatusFlags.CF (adcR64R64Effect 0x119193 14 2)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[469, 478, 483]
    (.letOp (n := 486) (.exec 0x119193 (fun s => s.RIP = 0x119193) (atFlags StatusFlags.CF (adcR64R64Effect 0x119193 14 2)) (Reg.operands [.gpr 14, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[469, 478, 483]
    (.letOp (n := 487) (.out 0x119196 (addR64R64Effect 0x119196 5 11) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 11] []) (.reg (.gpr 5))) #v[482, 408]
    (.letOp (n := 488) (.out 0x119196 (addR64R64Effect 0x119196 5 11) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 11] []) (.flag .CF)) #v[482, 408]
    (.letOp (n := 489) (.exec 0x119196 (fun s => s.RIP = 0x119196) (addR64R64Effect 0x119196 5 11) (Reg.operands [.gpr 5, .gpr 11] [])) #v[482, 408]
    (b_l118e1a_10)))))))))))))))))))))))))))))))))))))))))))))

def bytes_l118e1a_9 : List UInt8 :=
  [0x48, 0xF7, 0xA4, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0x89, 0xD3, 0x49, 0x89, 0xC2, 0x48, 0x8B,
    0x84, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE6, 0x49, 0x89, 0xC5, 0x48, 0x89, 0x94, 0x24,
    0xA0, 0x00, 0x00, 0x00, 0x4D, 0x21, 0xE0, 0x48, 0x8B, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00, 0x48,
    0x8B, 0x7C, 0x24, 0x78, 0x48, 0xF7, 0xE7, 0x49, 0x89, 0xD6, 0x49, 0x89, 0xC4, 0x48, 0x8B, 0x84,
    0x24, 0xA8, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x4C, 0x24, 0x50, 0x48, 0xF7, 0xE1, 0x48, 0x89, 0xC5,
    0x4C, 0x01, 0xE5, 0x49, 0x11, 0xD6, 0x4C, 0x01, 0xDD] ++ bytes_l118e1a_10

theorem code_l118e1a_9 : ∀ x ∈ codeRange 0x119140 bytes_l118e1a_9, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x19140 89 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l118e1a_10

def b_l118e1a_8 : Block Op Label signature Reg.count 401 :=
  .letOp (n := 401) (.out 0x1190df (atFlags StatusFlags.CF (adcR64R64Effect 0x1190df 11 2)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[396, 391, 399]
    (.letOp (n := 402) (.exec 0x1190df (fun s => s.RIP = 0x1190df) (atFlags StatusFlags.CF (adcR64R64Effect 0x1190df 11 2)) (Reg.operands [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[396, 391, 399]
    (.letOp (n := 403) (.out 0x1190e2 (addR64R64Effect 0x1190e2 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[398, 320]
    (.letOp (n := 404) (.out 0x1190e2 (addR64R64Effect 0x1190e2 0 10) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 10] []) (.flag .CF)) #v[398, 320]
    (.letOp (n := 405) (.exec 0x1190e2 (fun s => s.RIP = 0x1190e2) (addR64R64Effect 0x1190e2 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[398, 320]
    (.letOp (n := 406) (.out 0x1190e5 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1190e5 11 0x0)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[401, 404]
    (.letOp (n := 407) (.exec 0x1190e5 (fun s => s.RIP = 0x1190e5) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1190e5 11 0x0)) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[401, 404]
    (.letOp (n := 408) (.out 0x1190e9 (shldR64R64Effect 0x1190e9 5 11 0 12) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[406, 403]
    (.letOp (n := 409) (.exec 0x1190e9 (fun s => s.RIP = 0x1190e9) (shldR64R64Effect 0x1190e9 5 11 0 12) (Reg.operands [.gpr 11, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[406, 403]
    (.letOp (n := 410) (.out 0x1190ee (andR64R64Effect 0x1190ee 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[403, 373]
    (.letOp (n := 411) (.exec 0x1190ee (fun s => s.RIP = 0x1190ee) (andR64R64Effect 0x1190ee 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[403, 373]
    (.letOp (n := 412) (.out 0x1190f1 (movR64R64Effect 0x1190f1 12 1) (EffectPart.reads (.reg (.gpr 12)) [.gpr 1] []) (.reg (.gpr 12))) #v[373]
    (.letOp (n := 413) (.exec 0x1190f1 (fun s => s.RIP = 0x1190f1) (movR64R64Effect 0x1190f1 12 1) (Reg.operands [.gpr 1] [])) #v[373]
    (.letOp (n := 414) (.out 0x1190f4 (movR64Imm64Effect 0x1190f4 1 0x1000003d10) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 415) (.exec 0x1190f4 (fun s => s.RIP = 0x1190f4) (movR64Imm64Effect 0x1190f4 1 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 416) (.out 0x1190fe (mulR64Effect 0x1190fe 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[414, 410]
    (.letOp (n := 417) (.out 0x1190fe (mulR64Effect 0x1190fe 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[414, 410]
    (.letOp (n := 418) (.exec 0x1190fe (fun s => s.RIP = 0x1190fe) (mulR64Effect 0x1190fe 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[414, 410]
    (.letOp (n := 419) (.out 0x119101 (addR64M64Effect 0x119101 8 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 4] []) (.reg (.gpr 8))) #v[360, 4]
    (.letOp (n := 420) (.out 0x119101 (addR64M64Effect 0x119101 8 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 4] []) (.flag .CF)) #v[360, 4]
    (.letOp (n := 421) (.exec 0x119101 (LoadPre 0x119101 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x119101 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x119101 8 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[360, 4]
    (.letOp (n := 422) (.out 0x119109 (atFlags StatusFlags.CF (adcR64M64Effect 0x119109 9 (.sib 4 none 0 (.d32 0x98)))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 9))) #v[358, 4, 420]
    (.letOp (n := 423) (.exec 0x119109 (LoadPre 0x119109 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x119109 + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x119109 9 (.sib 4 none 0 (.d32 0x98)))) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[358, 4, 420]
    (.letOp (n := 424) (.out 0x119111 (addR64R64Effect 0x119111 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[419, 416]
    (.letOp (n := 425) (.out 0x119111 (addR64R64Effect 0x119111 8 0) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 0] []) (.flag .CF)) #v[419, 416]
    (.letOp (n := 426) (.exec 0x119111 (fun s => s.RIP = 0x119111) (addR64R64Effect 0x119111 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[419, 416]
    (.letOp (n := 427) (.out 0x119114 (atFlags StatusFlags.CF (adcR64R64Effect 0x119114 9 2)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[422, 417, 425]
    (.letOp (n := 428) (.exec 0x119114 (fun s => s.RIP = 0x119114) (atFlags StatusFlags.CF (adcR64R64Effect 0x119114 9 2)) (Reg.operands [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[422, 417, 425]
    (.letOp (n := 429) (.out 0x119117 (addR64R64Effect 0x119117 8 3) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 3] []) (.reg (.gpr 8))) #v[424, 344]
    (.letOp (n := 430) (.out 0x119117 (addR64R64Effect 0x119117 8 3) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 3] []) (.flag .CF)) #v[424, 344]
    (.letOp (n := 431) (.exec 0x119117 (fun s => s.RIP = 0x119117) (addR64R64Effect 0x119117 8 3) (Reg.operands [.gpr 8, .gpr 3] [])) #v[424, 344]
    (.letOp (n := 432) (.out 0x11911a (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11911a 9 0x0)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[427, 430]
    (.letOp (n := 433) (.exec 0x11911a (fun s => s.RIP = 0x11911a) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11911a 9 0x0)) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[427, 430]
    (.letOp (n := 434) (.out 0x11911e (shldR64R64Effect 0x11911e 5 9 8 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[432, 429]
    (.letOp (n := 435) (.exec 0x11911e (fun s => s.RIP = 0x11911e) (shldR64R64Effect 0x11911e 5 9 8 12) (Reg.operands [.gpr 9, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[432, 429]
    (.letOp (n := 436) (.out 0x119123 (movR64R64Effect 0x119123 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[386]
    (.letOp (n := 437) (.exec 0x119123 (fun s => s.RIP = 0x119123) (movR64R64Effect 0x119123 0 7) (Reg.operands [.gpr 7] [])) #v[386]
    (.letOp (n := 438) (.out 0x119126 (mulM64Effect 0x119126 5 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[436, 4]
    (.letOp (n := 439) (.out 0x119126 (mulM64Effect 0x119126 5 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[436, 4]
    (.letOp (n := 440) (.exec 0x119126 (LoadPre 0x119126 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x119126 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x119126 5 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[436, 4]
    (.letOp (n := 441) (.exec 0x11912b (StorePre 0x11912b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x11912b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11912b 2 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[439, 4]
    (.letOp (n := 442) (.exec 0x119133 (StorePre 0x119133 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x119133 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119133 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[438, 4]
    (.letOp (n := 443) (.out 0x119138 (movR64M64Effect 0x119138 0 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 444) (.exec 0x119138 (LoadPre 0x119138 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x119138 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x119138 0 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l118e1a_9))))))))))))))))))))))))))))))))))))))))))))

def bytes_l118e1a_8 : List UInt8 :=
  [0x49, 0x11, 0xD3, 0x4C, 0x01, 0xD0, 0x49, 0x83, 0xD3, 0x00, 0x49, 0x0F, 0xA4, 0xC3, 0x0C, 0x48,
    0x21, 0xC8, 0x49, 0x89, 0xCC, 0x48, 0xB9, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48,
    0xF7, 0xE1, 0x4C, 0x03, 0x84, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x4C, 0x13, 0x8C, 0x24, 0x98, 0x00,
    0x00, 0x00, 0x49, 0x01, 0xC0, 0x49, 0x11, 0xD1, 0x49, 0x01, 0xD8, 0x49, 0x83, 0xD1, 0x00, 0x4D,
    0x0F, 0xA4, 0xC1, 0x0C, 0x48, 0x89, 0xF8, 0x48, 0xF7, 0x64, 0x24, 0x60, 0x48, 0x89, 0x94, 0x24,
    0xD0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x60, 0x48, 0x8B, 0x84, 0x24, 0xB0, 0x00, 0x00,
    0x00] ++ bytes_l118e1a_9

theorem code_l118e1a_8 : ∀ x ∈ codeRange 0x1190df bytes_l118e1a_8, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x190df 97 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l118e1a_9

def b_l118e1a_7 : Block Op Label signature Reg.count 355 :=
  .letOp (n := 355) (.out 0x119089 (mulR64Effect 0x119089 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[262, 353]
    (.letOp (n := 356) (.out 0x119089 (mulR64Effect 0x119089 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[262, 353]
    (.letOp (n := 357) (.exec 0x119089 (fun s => s.RIP = 0x119089) (mulR64Effect 0x119089 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[262, 353]
    (.letOp (n := 358) (.out 0x11908c (movR64R64Effect 0x11908c 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[356]
    (.letOp (n := 359) (.exec 0x11908c (fun s => s.RIP = 0x11908c) (movR64R64Effect 0x11908c 9 2) (Reg.operands [.gpr 2] [])) #v[356]
    (.letOp (n := 360) (.out 0x11908f (movR64R64Effect 0x11908f 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[355]
    (.letOp (n := 361) (.exec 0x11908f (fun s => s.RIP = 0x11908f) (movR64R64Effect 0x11908f 8 0) (Reg.operands [.gpr 0] [])) #v[355]
    (.letOp (n := 362) (.out 0x119092 (movR64M64Effect 0x119092 0 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 363) (.exec 0x119092 (LoadPre 0x119092 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x119092 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x119092 0 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 364) (.out 0x11909a (movR64M64Effect 0x11909a 14 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 365) (.exec 0x11909a (LoadPre 0x11909a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x11909a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11909a 14 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 366) (.out 0x11909f (mulR64Effect 0x11909f 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[364, 362]
    (.letOp (n := 367) (.out 0x11909f (mulR64Effect 0x11909f 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[364, 362]
    (.letOp (n := 368) (.exec 0x11909f (fun s => s.RIP = 0x11909f) (mulR64Effect 0x11909f 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[364, 362]
    (.letOp (n := 369) (.out 0x1190a2 (movR64R64Effect 0x1190a2 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[366]
    (.letOp (n := 370) (.exec 0x1190a2 (fun s => s.RIP = 0x1190a2) (movR64R64Effect 0x1190a2 12 0) (Reg.operands [.gpr 0] [])) #v[366]
    (.letOp (n := 371) (.out 0x1190a5 (movR64R64Effect 0x1190a5 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[367]
    (.letOp (n := 372) (.exec 0x1190a5 (fun s => s.RIP = 0x1190a5) (movR64R64Effect 0x1190a5 13 2) (Reg.operands [.gpr 2] [])) #v[367]
    (.letOp (n := 373) (.out 0x1190a8 (movR64Imm64Effect 0x1190a8 1 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 374) (.exec 0x1190a8 (fun s => s.RIP = 0x1190a8) (movR64Imm64Effect 0x1190a8 1 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 375) (.out 0x1190b2 (andR64R64Effect 0x1190b2 15 1) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 1] []) (.reg (.gpr 15))) #v[339, 373]
    (.letOp (n := 376) (.exec 0x1190b2 (fun s => s.RIP = 0x1190b2) (andR64R64Effect 0x1190b2 15 1) (Reg.operands [.gpr 15, .gpr 1] [])) #v[339, 373]
    (.letOp (n := 377) (.out 0x1190b5 (movR64M64Effect 0x1190b5 0 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 378) (.exec 0x1190b5 (LoadPre 0x1190b5 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x1190b5 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1190b5 0 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 379) (.out 0x1190bd (mulR64Effect 0x1190bd 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[284, 377]
    (.letOp (n := 380) (.out 0x1190bd (mulR64Effect 0x1190bd 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[284, 377]
    (.letOp (n := 381) (.exec 0x1190bd (fun s => s.RIP = 0x1190bd) (mulR64Effect 0x1190bd 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[284, 377]
    (.letOp (n := 382) (.out 0x1190c0 (movR64R64Effect 0x1190c0 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[380]
    (.letOp (n := 383) (.exec 0x1190c0 (fun s => s.RIP = 0x1190c0) (movR64R64Effect 0x1190c0 11 2) (Reg.operands [.gpr 2] [])) #v[380]
    (.letOp (n := 384) (.out 0x1190c3 (movR64R64Effect 0x1190c3 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[379]
    (.letOp (n := 385) (.exec 0x1190c3 (fun s => s.RIP = 0x1190c3) (movR64R64Effect 0x1190c3 5 0) (Reg.operands [.gpr 0] [])) #v[379]
    (.letOp (n := 386) (.out 0x1190c6 (movR64M64Effect 0x1190c6 7 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 387) (.exec 0x1190c6 (LoadPre 0x1190c6 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x1190c6 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1190c6 7 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 388) (.out 0x1190ce (movR64R64Effect 0x1190ce 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[386]
    (.letOp (n := 389) (.exec 0x1190ce (fun s => s.RIP = 0x1190ce) (movR64R64Effect 0x1190ce 0 7) (Reg.operands [.gpr 7] [])) #v[386]
    (.letOp (n := 390) (.out 0x1190d1 (mulM64Effect 0x1190d1 5 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[388, 4]
    (.letOp (n := 391) (.out 0x1190d1 (mulM64Effect 0x1190d1 5 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[388, 4]
    (.letOp (n := 392) (.exec 0x1190d1 (LoadPre 0x1190d1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1190d1 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x1190d1 5 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[388, 4]
    (.letOp (n := 393) (.out 0x1190d6 (addR64R64Effect 0x1190d6 5 12) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 12] []) (.reg (.gpr 5))) #v[384, 369]
    (.letOp (n := 394) (.out 0x1190d6 (addR64R64Effect 0x1190d6 5 12) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 12] []) (.flag .CF)) #v[384, 369]
    (.letOp (n := 395) (.exec 0x1190d6 (fun s => s.RIP = 0x1190d6) (addR64R64Effect 0x1190d6 5 12) (Reg.operands [.gpr 5, .gpr 12] [])) #v[384, 369]
    (.letOp (n := 396) (.out 0x1190d9 (atFlags StatusFlags.CF (adcR64R64Effect 0x1190d9 11 13)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[382, 371, 394]
    (.letOp (n := 397) (.exec 0x1190d9 (fun s => s.RIP = 0x1190d9) (atFlags StatusFlags.CF (adcR64R64Effect 0x1190d9 11 13)) (Reg.operands [.gpr 11, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[382, 371, 394]
    (.letOp (n := 398) (.out 0x1190dc (addR64R64Effect 0x1190dc 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[390, 393]
    (.letOp (n := 399) (.out 0x1190dc (addR64R64Effect 0x1190dc 0 5) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 5] []) (.flag .CF)) #v[390, 393]
    (.letOp (n := 400) (.exec 0x1190dc (fun s => s.RIP = 0x1190dc) (addR64R64Effect 0x1190dc 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[390, 393]
    (b_l118e1a_8))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l118e1a_7 : List UInt8 :=
  [0x49, 0xF7, 0xE1, 0x49, 0x89, 0xD1, 0x49, 0x89, 0xC0, 0x48, 0x8B, 0x84, 0x24, 0x90, 0x00, 0x00,
    0x00, 0x4C, 0x8B, 0x74, 0x24, 0x58, 0x49, 0xF7, 0xE6, 0x49, 0x89, 0xC4, 0x49, 0x89, 0xD5, 0x48,
    0xB9, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x49, 0x21, 0xCF, 0x48, 0x8B, 0x84, 0x24,
    0xA8, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE5, 0x49, 0x89, 0xD3, 0x48, 0x89, 0xC5, 0x48, 0x8B, 0xBC,
    0x24, 0xD0, 0x00, 0x00, 0x00, 0x48, 0x89, 0xF8, 0x48, 0xF7, 0x64, 0x24, 0x50, 0x4C, 0x01, 0xE5,
    0x4D, 0x11, 0xEB, 0x48, 0x01, 0xE8] ++ bytes_l118e1a_8

theorem code_l118e1a_7 : ∀ x ∈ codeRange 0x119089 bytes_l118e1a_7, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x19089 86 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l118e1a_8

def b_l118e1a_6 : Block Op Label signature Reg.count 313 :=
  .letOp (n := 313) (.out 0x119020 (atFlags StatusFlags.CF (adcR64R64Effect 0x119020 10 2)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[308, 298, 311]
    (.letOp (n := 314) (.exec 0x119020 (fun s => s.RIP = 0x119020) (atFlags StatusFlags.CF (adcR64R64Effect 0x119020 10 2)) (Reg.operands [.gpr 10, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[308, 298, 311]
    (.letOp (n := 315) (.out 0x119023 (addR64R64Effect 0x119023 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[310, 245]
    (.letOp (n := 316) (.out 0x119023 (addR64R64Effect 0x119023 0 7) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 7] []) (.flag .CF)) #v[310, 245]
    (.letOp (n := 317) (.exec 0x119023 (fun s => s.RIP = 0x119023) (addR64R64Effect 0x119023 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[310, 245]
    (.letOp (n := 318) (.out 0x119026 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x119026 10 0x0)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[313, 316]
    (.letOp (n := 319) (.exec 0x119026 (fun s => s.RIP = 0x119026) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x119026 10 0x0)) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[313, 316]
    (.letOp (n := 320) (.out 0x11902a (shldR64R64Effect 0x11902a 5 10 0 12) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[318, 315]
    (.letOp (n := 321) (.exec 0x11902a (fun s => s.RIP = 0x11902a) (shldR64R64Effect 0x11902a 5 10 0 12) (Reg.operands [.gpr 10, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[318, 315]
    (.letOp (n := 322) (.out 0x11902f (shlR64Effect 0x11902f 4 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[315]
    (.letOp (n := 323) (.exec 0x11902f (fun s => s.RIP = 0x11902f) (shlR64Effect 0x11902f 4 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[315]
    (.letOp (n := 324) (.out 0x119033 (movR64Imm64Effect 0x119033 2 0xfffffffffffff0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 325) (.exec 0x119033 (fun s => s.RIP = 0x119033) (movR64Imm64Effect 0x119033 2 0xfffffffffffff0) (Reg.operands [] [])) #v[]
    (.letOp (n := 326) (.out 0x11903d (andR64R64Effect 0x11903d 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[322, 324]
    (.letOp (n := 327) (.exec 0x11903d (fun s => s.RIP = 0x11903d) (andR64R64Effect 0x11903d 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[322, 324]
    (.letOp (n := 328) (.out 0x119040 (orR64R64Effect 0x119040 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 13] []) (.reg (.gpr 0))) #v[326, 271]
    (.letOp (n := 329) (.exec 0x119040 (fun s => s.RIP = 0x119040) (orR64R64Effect 0x119040 0 13) (Reg.operands [.gpr 0, .gpr 13] [])) #v[326, 271]
    (.letOp (n := 330) (.out 0x119043 (movR64Imm64Effect 0x119043 2 0x1000003d1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 331) (.exec 0x119043 (fun s => s.RIP = 0x119043) (movR64Imm64Effect 0x119043 2 0x1000003d1) (Reg.operands [] [])) #v[]
    (.letOp (n := 332) (.out 0x11904d (mulR64Effect 0x11904d 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[330, 328]
    (.letOp (n := 333) (.out 0x11904d (mulR64Effect 0x11904d 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[330, 328]
    (.letOp (n := 334) (.exec 0x11904d (fun s => s.RIP = 0x11904d) (mulR64Effect 0x11904d 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[330, 328]
    (.letOp (n := 335) (.out 0x119050 (movR64R64Effect 0x119050 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[333]
    (.letOp (n := 336) (.exec 0x119050 (fun s => s.RIP = 0x119050) (movR64R64Effect 0x119050 3 2) (Reg.operands [.gpr 2] [])) #v[333]
    (.letOp (n := 337) (.out 0x119053 (movR64R64Effect 0x119053 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[332]
    (.letOp (n := 338) (.exec 0x119053 (fun s => s.RIP = 0x119053) (movR64R64Effect 0x119053 15 0) (Reg.operands [.gpr 0] [])) #v[332]
    (.letOp (n := 339) (.out 0x119056 (addR64M64Effect 0x119056 15 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 4] []) (.reg (.gpr 15))) #v[337, 4]
    (.letOp (n := 340) (.out 0x119056 (addR64M64Effect 0x119056 15 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 4] []) (.flag .CF)) #v[337, 4]
    (.letOp (n := 341) (.exec 0x119056 (LoadPre 0x119056 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x119056 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x119056 15 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[337, 4]
    (.letOp (n := 342) (.out 0x11905e (atFlags StatusFlags.CF (adcR64M64Effect 0x11905e 3 (.sib 4 none 0 (.d32 0x98)))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 3))) #v[335, 4, 340]
    (.letOp (n := 343) (.exec 0x11905e (LoadPre 0x11905e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x11905e + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x11905e 3 (.sib 4 none 0 (.d32 0x98)))) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[335, 4, 340]
    (.letOp (n := 344) (.out 0x119066 (shldR64R64Effect 0x119066 5 3 15 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[342, 339]
    (.letOp (n := 345) (.exec 0x119066 (fun s => s.RIP = 0x119066) (shldR64R64Effect 0x119066 5 3 15 12) (Reg.operands [.gpr 3, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[342, 339]
    (.letOp (n := 346) (.out 0x11906b (movR64R64Effect 0x11906b 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[293]
    (.letOp (n := 347) (.exec 0x11906b (fun s => s.RIP = 0x11906b) (movR64R64Effect 0x11906b 0 1) (Reg.operands [.gpr 1] [])) #v[293]
    (.letOp (n := 348) (.out 0x11906e (mulR64Effect 0x11906e 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[253, 346]
    (.letOp (n := 349) (.out 0x11906e (mulR64Effect 0x11906e 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[253, 346]
    (.letOp (n := 350) (.exec 0x11906e (fun s => s.RIP = 0x11906e) (mulR64Effect 0x11906e 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[253, 346]
    (.letOp (n := 351) (.exec 0x119071 (StorePre 0x119071 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x119071 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x119071 2 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[349, 4]
    (.letOp (n := 352) (.exec 0x119079 (StorePre 0x119079 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x119079 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x119079 0 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[348, 4]
    (.letOp (n := 353) (.out 0x119081 (movR64M64Effect 0x119081 0 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 354) (.exec 0x119081 (LoadPre 0x119081 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x119081 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x119081 0 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l118e1a_7))))))))))))))))))))))))))))))))))))))))))

def bytes_l118e1a_6 : List UInt8 :=
  [0x49, 0x11, 0xD2, 0x48, 0x01, 0xF8, 0x49, 0x83, 0xD2, 0x00, 0x49, 0x0F, 0xA4, 0xC2, 0x0C, 0x48,
    0xC1, 0xE0, 0x04, 0x48, 0xBA, 0xF0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x48, 0x21, 0xD0,
    0x4C, 0x09, 0xE8, 0x48, 0xBA, 0xD1, 0x03, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2,
    0x48, 0x89, 0xD3, 0x49, 0x89, 0xC7, 0x4C, 0x03, 0xBC, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x48, 0x13,
    0x9C, 0x24, 0x98, 0x00, 0x00, 0x00, 0x4C, 0x0F, 0xA4, 0xFB, 0x0C, 0x48, 0x89, 0xC8, 0x49, 0xF7,
    0xE0, 0x48, 0x89, 0x94, 0x24, 0x98, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0xB8, 0x00, 0x00,
    0x00, 0x48, 0x8B, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00] ++ bytes_l118e1a_7

theorem code_l118e1a_6 : ∀ x ∈ codeRange 0x119020 bytes_l118e1a_6, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x19020 105 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l118e1a_7

def b_l118e1a_5 : Block Op Label signature Reg.count 267 :=
  .letOp (n := 267) (.out 0x118fce (movR64R64Effect 0x118fce 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[264]
    (.letOp (n := 268) (.exec 0x118fce (fun s => s.RIP = 0x118fce) (movR64R64Effect 0x118fce 11 0) (Reg.operands [.gpr 0] [])) #v[264]
    (.letOp (n := 269) (.out 0x118fd1 (movR64R64Effect 0x118fd1 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[265]
    (.letOp (n := 270) (.exec 0x118fd1 (fun s => s.RIP = 0x118fd1) (movR64R64Effect 0x118fd1 3 2) (Reg.operands [.gpr 2] [])) #v[265]
    (.letOp (n := 271) (.out 0x118fd4 (andR32Imm8Effect 0x118fd4 4 13 0xf) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[249]
    (.letOp (n := 272) (.exec 0x118fd4 (fun s => s.RIP = 0x118fd4) (andR32Imm8Effect 0x118fd4 4 13 0xf) (Reg.operands [.gpr 13] [])) #v[249]
    (.letOp (n := 273) (.out 0x118fd8 (movR64M64Effect 0x118fd8 0 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 274) (.exec 0x118fd8 (LoadPre 0x118fd8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x118fd8 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x118fd8 0 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 275) (.out 0x118fe0 (mulM64Effect 0x118fe0 5 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[273, 4]
    (.letOp (n := 276) (.out 0x118fe0 (mulM64Effect 0x118fe0 5 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[273, 4]
    (.letOp (n := 277) (.exec 0x118fe0 (LoadPre 0x118fe0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x118fe0 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x118fe0 5 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[273, 4]
    (.letOp (n := 278) (.out 0x118fe5 (movR64R64Effect 0x118fe5 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[276]
    (.letOp (n := 279) (.exec 0x118fe5 (fun s => s.RIP = 0x118fe5) (movR64R64Effect 0x118fe5 10 2) (Reg.operands [.gpr 2] [])) #v[276]
    (.letOp (n := 280) (.out 0x118fe8 (movR64R64Effect 0x118fe8 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[275]
    (.letOp (n := 281) (.exec 0x118fe8 (fun s => s.RIP = 0x118fe8) (movR64R64Effect 0x118fe8 14 0) (Reg.operands [.gpr 0] [])) #v[275]
    (.letOp (n := 282) (.out 0x118feb (movR64M64Effect 0x118feb 0 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 283) (.exec 0x118feb (LoadPre 0x118feb (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x118feb + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x118feb 0 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 284) (.out 0x118ff3 (movR64M64Effect 0x118ff3 5 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 285) (.exec 0x118ff3 (LoadPre 0x118ff3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x118ff3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x118ff3 5 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 286) (.out 0x118ff8 (mulR64Effect 0x118ff8 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[284, 282]
    (.letOp (n := 287) (.out 0x118ff8 (mulR64Effect 0x118ff8 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[284, 282]
    (.letOp (n := 288) (.exec 0x118ff8 (fun s => s.RIP = 0x118ff8) (mulR64Effect 0x118ff8 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[284, 282]
    (.letOp (n := 289) (.out 0x118ffb (movR64R64Effect 0x118ffb 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[287]
    (.letOp (n := 290) (.exec 0x118ffb (fun s => s.RIP = 0x118ffb) (movR64R64Effect 0x118ffb 15 2) (Reg.operands [.gpr 2] [])) #v[287]
    (.letOp (n := 291) (.out 0x118ffe (movR64R64Effect 0x118ffe 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[286]
    (.letOp (n := 292) (.exec 0x118ffe (fun s => s.RIP = 0x118ffe) (movR64R64Effect 0x118ffe 12 0) (Reg.operands [.gpr 0] [])) #v[286]
    (.letOp (n := 293) (.out 0x119001 (movR64M64Effect 0x119001 1 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 294) (.exec 0x119001 (LoadPre 0x119001 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x119001 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x119001 1 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 295) (.out 0x119009 (movR64R64Effect 0x119009 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[293]
    (.letOp (n := 296) (.exec 0x119009 (fun s => s.RIP = 0x119009) (movR64R64Effect 0x119009 0 1) (Reg.operands [.gpr 1] [])) #v[293]
    (.letOp (n := 297) (.out 0x11900c (mulM64Effect 0x11900c 5 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[295, 4]
    (.letOp (n := 298) (.out 0x11900c (mulM64Effect 0x11900c 5 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[295, 4]
    (.letOp (n := 299) (.exec 0x11900c (LoadPre 0x11900c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x11900c + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x11900c 5 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[295, 4]
    (.letOp (n := 300) (.out 0x119011 (addR64R64Effect 0x119011 14 11) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 11] []) (.reg (.gpr 14))) #v[280, 267]
    (.letOp (n := 301) (.out 0x119011 (addR64R64Effect 0x119011 14 11) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 11] []) (.flag .CF)) #v[280, 267]
    (.letOp (n := 302) (.exec 0x119011 (fun s => s.RIP = 0x119011) (addR64R64Effect 0x119011 14 11) (Reg.operands [.gpr 14, .gpr 11] [])) #v[280, 267]
    (.letOp (n := 303) (.out 0x119014 (atFlags StatusFlags.CF (adcR64R64Effect 0x119014 10 3)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[278, 269, 301]
    (.letOp (n := 304) (.exec 0x119014 (fun s => s.RIP = 0x119014) (atFlags StatusFlags.CF (adcR64R64Effect 0x119014 10 3)) (Reg.operands [.gpr 10, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[278, 269, 301]
    (.letOp (n := 305) (.out 0x119017 (addR64R64Effect 0x119017 14 12) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 12] []) (.reg (.gpr 14))) #v[300, 291]
    (.letOp (n := 306) (.out 0x119017 (addR64R64Effect 0x119017 14 12) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 12] []) (.flag .CF)) #v[300, 291]
    (.letOp (n := 307) (.exec 0x119017 (fun s => s.RIP = 0x119017) (addR64R64Effect 0x119017 14 12) (Reg.operands [.gpr 14, .gpr 12] [])) #v[300, 291]
    (.letOp (n := 308) (.out 0x11901a (atFlags StatusFlags.CF (adcR64R64Effect 0x11901a 10 15)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[303, 289, 306]
    (.letOp (n := 309) (.exec 0x11901a (fun s => s.RIP = 0x11901a) (atFlags StatusFlags.CF (adcR64R64Effect 0x11901a 10 15)) (Reg.operands [.gpr 10, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[303, 289, 306]
    (.letOp (n := 310) (.out 0x11901d (addR64R64Effect 0x11901d 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[297, 305]
    (.letOp (n := 311) (.out 0x11901d (addR64R64Effect 0x11901d 0 14) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 14] []) (.flag .CF)) #v[297, 305]
    (.letOp (n := 312) (.exec 0x11901d (fun s => s.RIP = 0x11901d) (addR64R64Effect 0x11901d 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[297, 305]
    (b_l118e1a_6))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l118e1a_5 : List UInt8 :=
  [0x49, 0x89, 0xC3, 0x48, 0x89, 0xD3, 0x41, 0x83, 0xE5, 0x0F, 0x48, 0x8B, 0x84, 0x24, 0xA8, 0x00,
    0x00, 0x00, 0x48, 0xF7, 0x64, 0x24, 0x58, 0x49, 0x89, 0xD2, 0x49, 0x89, 0xC6, 0x48, 0x8B, 0x84,
    0x24, 0xD0, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x6C, 0x24, 0x78, 0x48, 0xF7, 0xE5, 0x49, 0x89, 0xD7,
    0x49, 0x89, 0xC4, 0x48, 0x8B, 0x8C, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x48, 0x89, 0xC8, 0x48, 0xF7,
    0x64, 0x24, 0x50, 0x4D, 0x01, 0xDE, 0x49, 0x11, 0xDA, 0x4D, 0x01, 0xE6, 0x4D, 0x11, 0xFA, 0x4C,
    0x01, 0xF0] ++ bytes_l118e1a_6

theorem code_l118e1a_5 : ∀ x ∈ codeRange 0x118fce bytes_l118e1a_5, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x18fce 82 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l118e1a_6

def b_l118e1a_4 : Block Op Label signature Reg.count 223 :=
  .letOp (n := 223) (.out 0x118f78 (atFlags StatusFlags.CF (adcR64R64Effect 0x118f78 7 14)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[218, 178, 221]
    (.letOp (n := 224) (.exec 0x118f78 (fun s => s.RIP = 0x118f78) (atFlags StatusFlags.CF (adcR64R64Effect 0x118f78 7 14)) (Reg.operands [.gpr 7, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[218, 178, 221]
    (.letOp (n := 225) (.out 0x118f7b (addR64R64Effect 0x118f7b 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 13] []) (.reg (.gpr 6))) #v[220, 189]
    (.letOp (n := 226) (.out 0x118f7b (addR64R64Effect 0x118f7b 6 13) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 13] []) (.flag .CF)) #v[220, 189]
    (.letOp (n := 227) (.exec 0x118f7b (fun s => s.RIP = 0x118f7b) (addR64R64Effect 0x118f7b 6 13) (Reg.operands [.gpr 6, .gpr 13] [])) #v[220, 189]
    (.letOp (n := 228) (.out 0x118f7e (atFlags StatusFlags.CF (adcR64R64Effect 0x118f7e 7 15)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[223, 187, 226]
    (.letOp (n := 229) (.exec 0x118f7e (fun s => s.RIP = 0x118f7e) (atFlags StatusFlags.CF (adcR64R64Effect 0x118f7e 7 15)) (Reg.operands [.gpr 7, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[223, 187, 226]
    (.letOp (n := 230) (.out 0x118f81 (addR64R64Effect 0x118f81 6 11) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 11] []) (.reg (.gpr 6))) #v[225, 198]
    (.letOp (n := 231) (.out 0x118f81 (addR64R64Effect 0x118f81 6 11) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 11] []) (.flag .CF)) #v[225, 198]
    (.letOp (n := 232) (.exec 0x118f81 (fun s => s.RIP = 0x118f81) (addR64R64Effect 0x118f81 6 11) (Reg.operands [.gpr 6, .gpr 11] [])) #v[225, 198]
    (.letOp (n := 233) (.out 0x118f84 (atFlags StatusFlags.CF (adcR64R64Effect 0x118f84 7 5)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[228, 200, 231]
    (.letOp (n := 234) (.exec 0x118f84 (fun s => s.RIP = 0x118f84) (atFlags StatusFlags.CF (adcR64R64Effect 0x118f84 7 5)) (Reg.operands [.gpr 7, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[228, 200, 231]
    (.letOp (n := 235) (.out 0x118f87 (addR64R64Effect 0x118f87 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[230, 210]
    (.letOp (n := 236) (.out 0x118f87 (addR64R64Effect 0x118f87 6 0) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 0] []) (.flag .CF)) #v[230, 210]
    (.letOp (n := 237) (.exec 0x118f87 (fun s => s.RIP = 0x118f87) (addR64R64Effect 0x118f87 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[230, 210]
    (.letOp (n := 238) (.out 0x118f8a (atFlags StatusFlags.CF (adcR64R64Effect 0x118f8a 7 8)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[233, 213, 236]
    (.letOp (n := 239) (.exec 0x118f8a (fun s => s.RIP = 0x118f8a) (atFlags StatusFlags.CF (adcR64R64Effect 0x118f8a 7 8)) (Reg.operands [.gpr 7, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[233, 213, 236]
    (.letOp (n := 240) (.out 0x118f8d (addR64R64Effect 0x118f8d 6 9) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 9] []) (.reg (.gpr 6))) #v[235, 155]
    (.letOp (n := 241) (.out 0x118f8d (addR64R64Effect 0x118f8d 6 9) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 9] []) (.flag .CF)) #v[235, 155]
    (.letOp (n := 242) (.exec 0x118f8d (fun s => s.RIP = 0x118f8d) (addR64R64Effect 0x118f8d 6 9) (Reg.operands [.gpr 6, .gpr 9] [])) #v[235, 155]
    (.letOp (n := 243) (.out 0x118f90 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x118f90 7 0x0)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[238, 241]
    (.letOp (n := 244) (.exec 0x118f90 (fun s => s.RIP = 0x118f90) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x118f90 7 0x0)) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[238, 241]
    (.letOp (n := 245) (.out 0x118f94 (shldR64R64Effect 0x118f94 5 7 6 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[243, 240]
    (.letOp (n := 246) (.exec 0x118f94 (fun s => s.RIP = 0x118f94) (shldR64R64Effect 0x118f94 5 7 6 12) (Reg.operands [.gpr 7, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[243, 240]
    (.letOp (n := 247) (.out 0x118f99 (movR64R64Effect 0x118f99 13 6) (EffectPart.reads (.reg (.gpr 13)) [.gpr 6] []) (.reg (.gpr 13))) #v[240]
    (.letOp (n := 248) (.exec 0x118f99 (fun s => s.RIP = 0x118f99) (movR64R64Effect 0x118f99 13 6) (Reg.operands [.gpr 6] [])) #v[240]
    (.letOp (n := 249) (.out 0x118f9c (shrR64Effect 0x118f9c 4 13 48) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[247]
    (.letOp (n := 250) (.exec 0x118f9c (fun s => s.RIP = 0x118f9c) (shrR64Effect 0x118f9c 4 13 48) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[247]
    (.letOp (n := 251) (.out 0x118fa0 (movR64R64Effect 0x118fa0 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[191]
    (.letOp (n := 252) (.exec 0x118fa0 (fun s => s.RIP = 0x118fa0) (movR64R64Effect 0x118fa0 0 10) (Reg.operands [.gpr 10] [])) #v[191]
    (.letOp (n := 253) (.out 0x118fa3 (movR64M64Effect 0x118fa3 8 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 254) (.exec 0x118fa3 (LoadPre 0x118fa3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x118fa3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x118fa3 8 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 255) (.out 0x118fa8 (mulR64Effect 0x118fa8 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[253, 251]
    (.letOp (n := 256) (.out 0x118fa8 (mulR64Effect 0x118fa8 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[253, 251]
    (.letOp (n := 257) (.exec 0x118fa8 (fun s => s.RIP = 0x118fa8) (mulR64Effect 0x118fa8 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[253, 251]
    (.letOp (n := 258) (.exec 0x118fab (StorePre 0x118fab 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x118fab + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x118fab 2 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[256, 4]
    (.letOp (n := 259) (.exec 0x118fb3 (StorePre 0x118fb3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x118fb3 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x118fb3 0 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[255, 4]
    (.letOp (n := 260) (.out 0x118fbb (movR64M64Effect 0x118fbb 0 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 261) (.exec 0x118fbb (LoadPre 0x118fbb (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x118fbb + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x118fbb 0 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 262) (.out 0x118fc3 (movR64M64Effect 0x118fc3 9 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 263) (.exec 0x118fc3 (LoadPre 0x118fc3 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x118fc3 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x118fc3 9 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 264) (.out 0x118fcb (mulR64Effect 0x118fcb 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[262, 260]
    (.letOp (n := 265) (.out 0x118fcb (mulR64Effect 0x118fcb 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[262, 260]
    (.letOp (n := 266) (.exec 0x118fcb (fun s => s.RIP = 0x118fcb) (mulR64Effect 0x118fcb 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[262, 260]
    (b_l118e1a_5))))))))))))))))))))))))))))))))))))))))))))

def bytes_l118e1a_4 : List UInt8 :=
  [0x4C, 0x11, 0xF7, 0x4C, 0x01, 0xEE, 0x4C, 0x11, 0xFF, 0x4C, 0x01, 0xDE, 0x48, 0x11, 0xEF, 0x48,
    0x01, 0xC6, 0x4C, 0x11, 0xC7, 0x4C, 0x01, 0xCE, 0x48, 0x83, 0xD7, 0x00, 0x48, 0x0F, 0xA4, 0xF7,
    0x0C, 0x49, 0x89, 0xF5, 0x49, 0xC1, 0xED, 0x30, 0x4C, 0x89, 0xD0, 0x4C, 0x8B, 0x44, 0x24, 0x60,
    0x49, 0xF7, 0xE0, 0x48, 0x89, 0x94, 0x24, 0x98, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0xB8,
    0x00, 0x00, 0x00, 0x48, 0x8B, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00, 0x4C, 0x8B, 0x8C, 0x24, 0x80,
    0x00, 0x00, 0x00, 0x49, 0xF7, 0xE1] ++ bytes_l118e1a_5

theorem code_l118e1a_4 : ∀ x ∈ codeRange 0x118f78 bytes_l118e1a_4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x18f78 86 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l118e1a_5

def b_l118e1a_3 : Block Op Label signature Reg.count 178 :=
  .letOp (n := 178) (.out 0x118f24 (movR64R64Effect 0x118f24 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[176]
    (.letOp (n := 179) (.exec 0x118f24 (fun s => s.RIP = 0x118f24) (movR64R64Effect 0x118f24 14 2) (Reg.operands [.gpr 2] [])) #v[176]
    (.letOp (n := 180) (.out 0x118f27 (movR64R64Effect 0x118f27 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[175]
    (.letOp (n := 181) (.exec 0x118f27 (fun s => s.RIP = 0x118f27) (movR64R64Effect 0x118f27 12 0) (Reg.operands [.gpr 0] [])) #v[175]
    (.letOp (n := 182) (.out 0x118f2a (movR64R64Effect 0x118f2a 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[90]
    (.letOp (n := 183) (.exec 0x118f2a (fun s => s.RIP = 0x118f2a) (movR64R64Effect 0x118f2a 0 5) (Reg.operands [.gpr 5] [])) #v[90]
    (.letOp (n := 184) (.out 0x118f2d (mulR64Effect 0x118f2d 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[55, 182]
    (.letOp (n := 185) (.out 0x118f2d (mulR64Effect 0x118f2d 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[55, 182]
    (.letOp (n := 186) (.exec 0x118f2d (fun s => s.RIP = 0x118f2d) (mulR64Effect 0x118f2d 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[55, 182]
    (.letOp (n := 187) (.out 0x118f30 (movR64R64Effect 0x118f30 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[185]
    (.letOp (n := 188) (.exec 0x118f30 (fun s => s.RIP = 0x118f30) (movR64R64Effect 0x118f30 15 2) (Reg.operands [.gpr 2] [])) #v[185]
    (.letOp (n := 189) (.out 0x118f33 (movR64R64Effect 0x118f33 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[184]
    (.letOp (n := 190) (.exec 0x118f33 (fun s => s.RIP = 0x118f33) (movR64R64Effect 0x118f33 13 0) (Reg.operands [.gpr 0] [])) #v[184]
    (.letOp (n := 191) (.out 0x118f36 (movR64M64Effect 0x118f36 10 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 192) (.exec 0x118f36 (LoadPre 0x118f36 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x118f36 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x118f36 10 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 193) (.out 0x118f3e (movR64R64Effect 0x118f3e 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[191]
    (.letOp (n := 194) (.exec 0x118f3e (fun s => s.RIP = 0x118f3e) (movR64R64Effect 0x118f3e 0 10) (Reg.operands [.gpr 10] [])) #v[191]
    (.letOp (n := 195) (.out 0x118f41 (mulR64Effect 0x118f41 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[126, 193]
    (.letOp (n := 196) (.out 0x118f41 (mulR64Effect 0x118f41 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[126, 193]
    (.letOp (n := 197) (.exec 0x118f41 (fun s => s.RIP = 0x118f41) (mulR64Effect 0x118f41 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[126, 193]
    (.letOp (n := 198) (.out 0x118f44 (movR64R64Effect 0x118f44 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[195]
    (.letOp (n := 199) (.exec 0x118f44 (fun s => s.RIP = 0x118f44) (movR64R64Effect 0x118f44 11 0) (Reg.operands [.gpr 0] [])) #v[195]
    (.letOp (n := 200) (.out 0x118f47 (movR64R64Effect 0x118f47 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[196]
    (.letOp (n := 201) (.exec 0x118f47 (fun s => s.RIP = 0x118f47) (movR64R64Effect 0x118f47 5 2) (Reg.operands [.gpr 2] [])) #v[196]
    (.letOp (n := 202) (.out 0x118f4a (shrR64Effect 0x118f4a 4 8 52) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[132]
    (.letOp (n := 203) (.exec 0x118f4a (fun s => s.RIP = 0x118f4a) (shrR64Effect 0x118f4a 4 8 52) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[132]
    (.letOp (n := 204) (.out 0x118f4e (movR64Imm64Effect 0x118f4e 1 0x1000003d10) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 205) (.exec 0x118f4e (fun s => s.RIP = 0x118f4e) (movR64Imm64Effect 0x118f4e 1 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 206) (.out 0x118f58 (imulR64R64Effect 0x118f58 4 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[202, 204]
    (.letOp (n := 207) (.exec 0x118f58 (fun s => s.RIP = 0x118f58) (imulR64R64Effect 0x118f58 4 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[202, 204]
    (.letOp (n := 208) (.out 0x118f5c (movR64R64Effect 0x118f5c 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[136]
    (.letOp (n := 209) (.exec 0x118f5c (fun s => s.RIP = 0x118f5c) (movR64R64Effect 0x118f5c 0 3) (Reg.operands [.gpr 3] [])) #v[136]
    (.letOp (n := 210) (.out 0x118f5f (mulR64Effect 0x118f5f 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[204, 208]
    (.letOp (n := 211) (.out 0x118f5f (mulR64Effect 0x118f5f 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[204, 208]
    (.letOp (n := 212) (.exec 0x118f5f (fun s => s.RIP = 0x118f5f) (mulR64Effect 0x118f5f 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[204, 208]
    (.letOp (n := 213) (.out 0x118f62 (addR64R64Effect 0x118f62 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2] []) (.reg (.gpr 8))) #v[206, 211]
    (.letOp (n := 214) (.exec 0x118f62 (fun s => s.RIP = 0x118f62) (addR64R64Effect 0x118f62 8 2) (Reg.operands [.gpr 8, .gpr 2] [])) #v[206, 211]
    (.letOp (n := 215) (.out 0x118f65 (addR64M64Effect 0x118f65 6 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 4] []) (.reg (.gpr 6))) #v[171, 4]
    (.letOp (n := 216) (.out 0x118f65 (addR64M64Effect 0x118f65 6 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 4] []) (.flag .CF)) #v[171, 4]
    (.letOp (n := 217) (.exec 0x118f65 (LoadPre 0x118f65 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x118f65 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x118f65 6 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[171, 4]
    (.letOp (n := 218) (.out 0x118f6d (atFlags StatusFlags.CF (adcR64M64Effect 0x118f6d 7 (.sib 4 none 0 (.d32 0x98)))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 7))) #v[169, 4, 216]
    (.letOp (n := 219) (.exec 0x118f6d (LoadPre 0x118f6d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x118f6d + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x118f6d 7 (.sib 4 none 0 (.d32 0x98)))) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[169, 4, 216]
    (.letOp (n := 220) (.out 0x118f75 (addR64R64Effect 0x118f75 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 12] []) (.reg (.gpr 6))) #v[215, 180]
    (.letOp (n := 221) (.out 0x118f75 (addR64R64Effect 0x118f75 6 12) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 12] []) (.flag .CF)) #v[215, 180]
    (.letOp (n := 222) (.exec 0x118f75 (fun s => s.RIP = 0x118f75) (addR64R64Effect 0x118f75 6 12) (Reg.operands [.gpr 6, .gpr 12] [])) #v[215, 180]
    (b_l118e1a_4)))))))))))))))))))))))))))))))))))))))))))))

def bytes_l118e1a_3 : List UInt8 :=
  [0x49, 0x89, 0xD6, 0x49, 0x89, 0xC4, 0x48, 0x89, 0xE8, 0x49, 0xF7, 0xE2, 0x49, 0x89, 0xD7, 0x49,
    0x89, 0xC5, 0x4C, 0x8B, 0x94, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xD0, 0x48, 0xF7, 0xE1,
    0x49, 0x89, 0xC3, 0x48, 0x89, 0xD5, 0x49, 0xC1, 0xE8, 0x34, 0x48, 0xB9, 0x10, 0x3D, 0x00, 0x00,
    0x10, 0x00, 0x00, 0x00, 0x4C, 0x0F, 0xAF, 0xC1, 0x48, 0x89, 0xD8, 0x48, 0xF7, 0xE1, 0x49, 0x01,
    0xD0, 0x48, 0x03, 0xB4, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x48, 0x13, 0xBC, 0x24, 0x98, 0x00, 0x00,
    0x00, 0x4C, 0x01, 0xE6] ++ bytes_l118e1a_4

theorem code_l118e1a_3 : ∀ x ∈ codeRange 0x118f24 bytes_l118e1a_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x18f24 84 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l118e1a_4

def b_l118e1a_2 : Block Op Label signature Reg.count 136 :=
  .letOp (n := 136) (.out 0x118ec2 (shldR64R64Effect 0x118ec2 5 3 0 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[134, 129]
    (.letOp (n := 137) (.exec 0x118ec2 (fun s => s.RIP = 0x118ec2) (shldR64R64Effect 0x118ec2 5 3 0 12) (Reg.operands [.gpr 3, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[134, 129]
    (.letOp (n := 138) (.out 0x118ec7 (movR64Imm64Effect 0x118ec7 2 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 139) (.exec 0x118ec7 (fun s => s.RIP = 0x118ec7) (movR64Imm64Effect 0x118ec7 2 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 140) (.out 0x118ed1 (andR64R64Effect 0x118ed1 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[129, 138]
    (.letOp (n := 141) (.exec 0x118ed1 (fun s => s.RIP = 0x118ed1) (andR64R64Effect 0x118ed1 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[129, 138]
    (.letOp (n := 142) (.out 0x118ed4 (movR64Imm64Effect 0x118ed4 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 143) (.exec 0x118ed4 (fun s => s.RIP = 0x118ed4) (movR64Imm64Effect 0x118ed4 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 144) (.out 0x118ede (mulR64Effect 0x118ede 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[142, 140]
    (.letOp (n := 145) (.out 0x118ede (mulR64Effect 0x118ede 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[142, 140]
    (.letOp (n := 146) (.exec 0x118ede (fun s => s.RIP = 0x118ede) (mulR64Effect 0x118ede 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[142, 140]
    (.letOp (n := 147) (.out 0x118ee1 (movR64R64Effect 0x118ee1 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[145]
    (.letOp (n := 148) (.exec 0x118ee1 (fun s => s.RIP = 0x118ee1) (movR64R64Effect 0x118ee1 9 2) (Reg.operands [.gpr 2] [])) #v[145]
    (.letOp (n := 149) (.out 0x118ee4 (addR64R64Effect 0x118ee4 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[144, 117]
    (.letOp (n := 150) (.out 0x118ee4 (addR64R64Effect 0x118ee4 0 11) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 11] []) (.flag .CF)) #v[144, 117]
    (.letOp (n := 151) (.exec 0x118ee4 (fun s => s.RIP = 0x118ee4) (addR64R64Effect 0x118ee4 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[144, 117]
    (.letOp (n := 152) (.exec 0x118ee7 (StorePre 0x118ee7 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x118ee7 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x118ee7 0 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[149, 4]
    (.letOp (n := 153) (.out 0x118eef (atFlags StatusFlags.CF (adcR64R64Effect 0x118eef 9 7)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[147, 120, 150]
    (.letOp (n := 154) (.exec 0x118eef (fun s => s.RIP = 0x118eef) (atFlags StatusFlags.CF (adcR64R64Effect 0x118eef 9 7)) (Reg.operands [.gpr 9, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[147, 120, 150]
    (.letOp (n := 155) (.out 0x118ef2 (shldR64R64Effect 0x118ef2 5 9 0 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[153, 149]
    (.letOp (n := 156) (.exec 0x118ef2 (fun s => s.RIP = 0x118ef2) (shldR64R64Effect 0x118ef2 5 9 0 12) (Reg.operands [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[153, 149]
    (.letOp (n := 157) (.out 0x118ef7 (movR64R64Effect 0x118ef7 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[122]
    (.letOp (n := 158) (.exec 0x118ef7 (fun s => s.RIP = 0x118ef7) (movR64R64Effect 0x118ef7 0 6) (Reg.operands [.gpr 6] [])) #v[122]
    (.letOp (n := 159) (.out 0x118efa (mulR64Effect 0x118efa 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[59, 157]
    (.letOp (n := 160) (.out 0x118efa (mulR64Effect 0x118efa 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[59, 157]
    (.letOp (n := 161) (.exec 0x118efa (fun s => s.RIP = 0x118efa) (mulR64Effect 0x118efa 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[59, 157]
    (.letOp (n := 162) (.exec 0x118efd (StorePre 0x118efd 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x118efd + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x118efd 2 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[160, 4]
    (.letOp (n := 163) (.exec 0x118f05 (StorePre 0x118f05 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x118f05 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x118f05 0 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[159, 4]
    (.letOp (n := 164) (.out 0x118f0d (movR64M64Effect 0x118f0d 0 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 165) (.exec 0x118f0d (LoadPre 0x118f0d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x118f0d + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x118f0d 0 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 166) (.out 0x118f15 (mulR64Effect 0x118f15 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[61, 164]
    (.letOp (n := 167) (.out 0x118f15 (mulR64Effect 0x118f15 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[61, 164]
    (.letOp (n := 168) (.exec 0x118f15 (fun s => s.RIP = 0x118f15) (mulR64Effect 0x118f15 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[61, 164]
    (.letOp (n := 169) (.out 0x118f18 (movR64R64Effect 0x118f18 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[167]
    (.letOp (n := 170) (.exec 0x118f18 (fun s => s.RIP = 0x118f18) (movR64R64Effect 0x118f18 7 2) (Reg.operands [.gpr 2] [])) #v[167]
    (.letOp (n := 171) (.out 0x118f1b (movR64R64Effect 0x118f1b 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[166]
    (.letOp (n := 172) (.exec 0x118f1b (fun s => s.RIP = 0x118f1b) (movR64R64Effect 0x118f1b 6 0) (Reg.operands [.gpr 0] [])) #v[166]
    (.letOp (n := 173) (.out 0x118f1e (movR64R64Effect 0x118f1e 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[73]
    (.letOp (n := 174) (.exec 0x118f1e (fun s => s.RIP = 0x118f1e) (movR64R64Effect 0x118f1e 0 12) (Reg.operands [.gpr 12] [])) #v[73]
    (.letOp (n := 175) (.out 0x118f21 (mulR64Effect 0x118f21 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15, .gpr 0] []) (.reg (.gpr 0))) #v[57, 173]
    (.letOp (n := 176) (.out 0x118f21 (mulR64Effect 0x118f21 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15, .gpr 0] []) (.reg (.gpr 2))) #v[57, 173]
    (.letOp (n := 177) (.exec 0x118f21 (fun s => s.RIP = 0x118f21) (mulR64Effect 0x118f21 15) (Reg.operands [.gpr 15, .gpr 0] [])) #v[57, 173]
    (b_l118e1a_3))))))))))))))))))))))))))))))))))))))))))

def bytes_l118e1a_2 : List UInt8 :=
  [0x48, 0x0F, 0xA4, 0xC3, 0x0C, 0x48, 0xBA, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48,
    0x21, 0xD0, 0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x49,
    0x89, 0xD1, 0x4C, 0x01, 0xD8, 0x48, 0x89, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x49, 0x11, 0xF9,
    0x49, 0x0F, 0xA4, 0xC1, 0x0C, 0x48, 0x89, 0xF0, 0x49, 0xF7, 0xE5, 0x48, 0x89, 0x94, 0x24, 0x98,
    0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x84, 0x24, 0xA8,
    0x00, 0x00, 0x00, 0x49, 0xF7, 0xE6, 0x48, 0x89, 0xD7, 0x48, 0x89, 0xC6, 0x4C, 0x89, 0xE0, 0x49,
    0xF7, 0xE7] ++ bytes_l118e1a_3

theorem code_l118e1a_2 : ∀ x ∈ codeRange 0x118ec2 bytes_l118e1a_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x18ec2 98 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l118e1a_3

def b_l118e1a_1 : Block Op Label signature Reg.count 94 :=
  .letOp (n := 94) (.out 0x118e76 (mulR64Effect 0x118e76 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15, .gpr 0] []) (.reg (.gpr 0))) #v[57, 92]
    (.letOp (n := 95) (.out 0x118e76 (mulR64Effect 0x118e76 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15, .gpr 0] []) (.reg (.gpr 2))) #v[57, 92]
    (.letOp (n := 96) (.exec 0x118e76 (fun s => s.RIP = 0x118e76) (mulR64Effect 0x118e76 15) (Reg.operands [.gpr 15, .gpr 0] [])) #v[57, 92]
    (.letOp (n := 97) (.exec 0x118e79 (StorePre 0x118e79 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x118e79 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x118e79 15 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 98) (.out 0x118e7e (movR64R64Effect 0x118e7e 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[95]
    (.letOp (n := 99) (.exec 0x118e7e (fun s => s.RIP = 0x118e7e) (movR64R64Effect 0x118e7e 1 2) (Reg.operands [.gpr 2] [])) #v[95]
    (.letOp (n := 100) (.out 0x118e81 (movR64R64Effect 0x118e81 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[94]
    (.letOp (n := 101) (.exec 0x118e81 (fun s => s.RIP = 0x118e81) (movR64R64Effect 0x118e81 6 0) (Reg.operands [.gpr 0] [])) #v[94]
    (.letOp (n := 102) (.out 0x118e84 (addR64R64Effect 0x118e84 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 8] []) (.reg (.gpr 6))) #v[100, 85]
    (.letOp (n := 103) (.out 0x118e84 (addR64R64Effect 0x118e84 6 8) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 8] []) (.flag .CF)) #v[100, 85]
    (.letOp (n := 104) (.exec 0x118e84 (fun s => s.RIP = 0x118e84) (addR64R64Effect 0x118e84 6 8) (Reg.operands [.gpr 6, .gpr 8] [])) #v[100, 85]
    (.letOp (n := 105) (.out 0x118e87 (atFlags StatusFlags.CF (adcR64R64Effect 0x118e87 1 7)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[98, 88, 103]
    (.letOp (n := 106) (.exec 0x118e87 (fun s => s.RIP = 0x118e87) (atFlags StatusFlags.CF (adcR64R64Effect 0x118e87 1 7)) (Reg.operands [.gpr 1, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[98, 88, 103]
    (.letOp (n := 107) (.out 0x118e8a (movR64M64Effect 0x118e8a 0 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 108) (.exec 0x118e8a (LoadPre 0x118e8a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x118e8a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x118e8a 0 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 109) (.out 0x118e92 (mulR64Effect 0x118e92 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[55, 107]
    (.letOp (n := 110) (.out 0x118e92 (mulR64Effect 0x118e92 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[55, 107]
    (.letOp (n := 111) (.exec 0x118e92 (fun s => s.RIP = 0x118e92) (mulR64Effect 0x118e92 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[55, 107]
    (.letOp (n := 112) (.exec 0x118e95 (StorePre 0x118e95 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x118e95 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x118e95 10 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 113) (.out 0x118e9a (movR64R64Effect 0x118e9a 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[110]
    (.letOp (n := 114) (.exec 0x118e9a (fun s => s.RIP = 0x118e9a) (movR64R64Effect 0x118e9a 7 2) (Reg.operands [.gpr 2] [])) #v[110]
    (.letOp (n := 115) (.out 0x118e9d (movR64R64Effect 0x118e9d 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[109]
    (.letOp (n := 116) (.exec 0x118e9d (fun s => s.RIP = 0x118e9d) (movR64R64Effect 0x118e9d 11 0) (Reg.operands [.gpr 0] [])) #v[109]
    (.letOp (n := 117) (.out 0x118ea0 (addR64R64Effect 0x118ea0 11 6) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 6] []) (.reg (.gpr 11))) #v[115, 102]
    (.letOp (n := 118) (.out 0x118ea0 (addR64R64Effect 0x118ea0 11 6) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 6] []) (.flag .CF)) #v[115, 102]
    (.letOp (n := 119) (.exec 0x118ea0 (fun s => s.RIP = 0x118ea0) (addR64R64Effect 0x118ea0 11 6) (Reg.operands [.gpr 11, .gpr 6] [])) #v[115, 102]
    (.letOp (n := 120) (.out 0x118ea3 (atFlags StatusFlags.CF (adcR64R64Effect 0x118ea3 7 1)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[113, 105, 118]
    (.letOp (n := 121) (.exec 0x118ea3 (fun s => s.RIP = 0x118ea3) (atFlags StatusFlags.CF (adcR64R64Effect 0x118ea3 7 1)) (Reg.operands [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[113, 105, 118]
    (.letOp (n := 122) (.out 0x118ea6 (movR64M64Effect 0x118ea6 6 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 123) (.exec 0x118ea6 (LoadPre 0x118ea6 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x118ea6 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x118ea6 6 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 124) (.out 0x118eae (movR64R64Effect 0x118eae 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[122]
    (.letOp (n := 125) (.exec 0x118eae (fun s => s.RIP = 0x118eae) (movR64R64Effect 0x118eae 0 6) (Reg.operands [.gpr 6] [])) #v[122]
    (.letOp (n := 126) (.out 0x118eb1 (movR64R64Effect 0x118eb1 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 3] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 127) (.exec 0x118eb1 (fun s => s.RIP = 0x118eb1) (movR64R64Effect 0x118eb1 1 3) (Reg.operands [.gpr 3] [])) #v[53]
    (.letOp (n := 128) (.exec 0x118eb4 (StorePre 0x118eb4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x118eb4 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x118eb4 3 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 129) (.out 0x118eb9 (mulR64Effect 0x118eb9 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 0] []) (.reg (.gpr 0))) #v[53, 124]
    (.letOp (n := 130) (.out 0x118eb9 (mulR64Effect 0x118eb9 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3, .gpr 0] []) (.reg (.gpr 2))) #v[53, 124]
    (.letOp (n := 131) (.exec 0x118eb9 (fun s => s.RIP = 0x118eb9) (mulR64Effect 0x118eb9 3) (Reg.operands [.gpr 3, .gpr 0] [])) #v[53, 124]
    (.letOp (n := 132) (.out 0x118ebc (movR64R64Effect 0x118ebc 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[130]
    (.letOp (n := 133) (.exec 0x118ebc (fun s => s.RIP = 0x118ebc) (movR64R64Effect 0x118ebc 8 2) (Reg.operands [.gpr 2] [])) #v[130]
    (.letOp (n := 134) (.out 0x118ebf (movR64R64Effect 0x118ebf 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[130]
    (.letOp (n := 135) (.exec 0x118ebf (fun s => s.RIP = 0x118ebf) (movR64R64Effect 0x118ebf 3 2) (Reg.operands [.gpr 2] [])) #v[130]
    (b_l118e1a_2))))))))))))))))))))))))))))))))))))))))))

def bytes_l118e1a_1 : List UInt8 :=
  [0x49, 0xF7, 0xE7, 0x4C, 0x89, 0x7C, 0x24, 0x58, 0x48, 0x89, 0xD1, 0x48, 0x89, 0xC6, 0x4C, 0x01,
    0xC6, 0x48, 0x11, 0xF9, 0x48, 0x8B, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE2, 0x4C,
    0x89, 0x54, 0x24, 0x78, 0x48, 0x89, 0xD7, 0x49, 0x89, 0xC3, 0x49, 0x01, 0xF3, 0x48, 0x11, 0xCF,
    0x48, 0x8B, 0xB4, 0x24, 0x90, 0x00, 0x00, 0x00, 0x48, 0x89, 0xF0, 0x48, 0x89, 0xD9, 0x48, 0x89,
    0x5C, 0x24, 0x50, 0x48, 0xF7, 0xE3, 0x49, 0x89, 0xD0, 0x48, 0x89, 0xD3] ++ bytes_l118e1a_2

theorem code_l118e1a_1 : ∀ x ∈ codeRange 0x118e76 bytes_l118e1a_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x18e76 76 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l118e1a_2

def b_l118e1a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x118e1a (movR64M64Effect 0x118e1a 3 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 54) (.exec 0x118e1a (LoadPre 0x118e1a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x118e1a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x118e1a 3 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x118e1f (movR64M64Effect 0x118e1f 10 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 56) (.exec 0x118e1f (LoadPre 0x118e1f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x118e1f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x118e1f 10 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x118e24 (movR64M64Effect 0x118e24 15 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 58) (.exec 0x118e24 (LoadPre 0x118e24 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x118e24 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x118e24 15 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x118e29 (movR64M64Effect 0x118e29 13 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 60) (.exec 0x118e29 (LoadPre 0x118e29 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x118e29 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x118e29 13 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x118e2e (movR64M64Effect 0x118e2e 14 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 62) (.exec 0x118e2e (LoadPre 0x118e2e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x118e2e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x118e2e 14 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x118e33 (movR64M64Effect 0x118e33 0 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 64) (.exec 0x118e33 (LoadPre 0x118e33 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x118e33 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x118e33 0 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x118e3b (mulR64Effect 0x118e3b 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[59, 63]
    (.letOp (n := 66) (.out 0x118e3b (mulR64Effect 0x118e3b 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[59, 63]
    (.letOp (n := 67) (.exec 0x118e3b (fun s => s.RIP = 0x118e3b) (mulR64Effect 0x118e3b 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[59, 63]
    (.letOp (n := 68) (.exec 0x118e3e (StorePre 0x118e3e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x118e3e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x118e3e 13 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 69) (.out 0x118e43 (movR64R64Effect 0x118e43 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[66]
    (.letOp (n := 70) (.exec 0x118e43 (fun s => s.RIP = 0x118e43) (movR64R64Effect 0x118e43 1 2) (Reg.operands [.gpr 2] [])) #v[66]
    (.letOp (n := 71) (.out 0x118e46 (movR64R64Effect 0x118e46 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[65]
    (.letOp (n := 72) (.exec 0x118e46 (fun s => s.RIP = 0x118e46) (movR64R64Effect 0x118e46 6 0) (Reg.operands [.gpr 0] [])) #v[65]
    (.letOp (n := 73) (.out 0x118e49 (movR64M64Effect 0x118e49 12 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 74) (.exec 0x118e49 (LoadPre 0x118e49 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x118e49 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x118e49 12 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.out 0x118e51 (movR64R64Effect 0x118e51 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[73]
    (.letOp (n := 76) (.exec 0x118e51 (fun s => s.RIP = 0x118e51) (movR64R64Effect 0x118e51 0 12) (Reg.operands [.gpr 12] [])) #v[73]
    (.letOp (n := 77) (.out 0x118e54 (mulR64Effect 0x118e54 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[61, 75]
    (.letOp (n := 78) (.out 0x118e54 (mulR64Effect 0x118e54 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[61, 75]
    (.letOp (n := 79) (.exec 0x118e54 (fun s => s.RIP = 0x118e54) (mulR64Effect 0x118e54 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[61, 75]
    (.letOp (n := 80) (.exec 0x118e57 (StorePre 0x118e57 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x118e57 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x118e57 14 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 81) (.out 0x118e5f (movR64R64Effect 0x118e5f 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[78]
    (.letOp (n := 82) (.exec 0x118e5f (fun s => s.RIP = 0x118e5f) (movR64R64Effect 0x118e5f 7 2) (Reg.operands [.gpr 2] [])) #v[78]
    (.letOp (n := 83) (.out 0x118e62 (movR64R64Effect 0x118e62 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[77]
    (.letOp (n := 84) (.exec 0x118e62 (fun s => s.RIP = 0x118e62) (movR64R64Effect 0x118e62 8 0) (Reg.operands [.gpr 0] [])) #v[77]
    (.letOp (n := 85) (.out 0x118e65 (addR64R64Effect 0x118e65 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6] []) (.reg (.gpr 8))) #v[83, 71]
    (.letOp (n := 86) (.out 0x118e65 (addR64R64Effect 0x118e65 8 6) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 6] []) (.flag .CF)) #v[83, 71]
    (.letOp (n := 87) (.exec 0x118e65 (fun s => s.RIP = 0x118e65) (addR64R64Effect 0x118e65 8 6) (Reg.operands [.gpr 8, .gpr 6] [])) #v[83, 71]
    (.letOp (n := 88) (.out 0x118e68 (atFlags StatusFlags.CF (adcR64R64Effect 0x118e68 7 1)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[81, 69, 86]
    (.letOp (n := 89) (.exec 0x118e68 (fun s => s.RIP = 0x118e68) (atFlags StatusFlags.CF (adcR64R64Effect 0x118e68 7 1)) (Reg.operands [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[81, 69, 86]
    (.letOp (n := 90) (.out 0x118e6b (movR64M64Effect 0x118e6b 5 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 91) (.exec 0x118e6b (LoadPre 0x118e6b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x118e6b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x118e6b 5 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 92) (.out 0x118e73 (movR64R64Effect 0x118e73 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[90]
    (.letOp (n := 93) (.exec 0x118e73 (fun s => s.RIP = 0x118e73) (movR64R64Effect 0x118e73 0 5) (Reg.operands [.gpr 5] [])) #v[90]
    (b_l118e1a_1)))))))))))))))))))))))))))))))))))))))))

def bytes_l118e1a : List UInt8 :=
  [0x48, 0x8B, 0x5C, 0x24, 0x48, 0x4C, 0x8B, 0x54, 0x24, 0x40, 0x4C, 0x8B, 0x7C, 0x24, 0x38, 0x4C,
    0x8B, 0x6C, 0x24, 0x28, 0x4C, 0x8B, 0x74, 0x24, 0x30, 0x48, 0x8B, 0x84, 0x24, 0xA8, 0x00, 0x00,
    0x00, 0x49, 0xF7, 0xE5, 0x4C, 0x89, 0x6C, 0x24, 0x60, 0x48, 0x89, 0xD1, 0x48, 0x89, 0xC6, 0x4C,
    0x8B, 0xA4, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xE0, 0x49, 0xF7, 0xE6, 0x4C, 0x89, 0xB4,
    0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0x89, 0xD7, 0x49, 0x89, 0xC0, 0x49, 0x01, 0xF0, 0x48, 0x11,
    0xCF, 0x48, 0x8B, 0xAC, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x48, 0x89, 0xE8] ++ bytes_l118e1a_1

theorem code_l118e1a : ∀ x ∈ codeRange 0x118e1a bytes_l118e1a, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x18e1a 92 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l118e1a_1

@[cfg_block] def b_l119258 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x119258 (movR64M64Effect 0x119258 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x119258 (LoadPre 0x119258 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x119258 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119258 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x11925d (StorePre 0x11925d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11925d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11925d 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x119262 (movR64M64Effect 0x119262 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x119262 (LoadPre 0x119262 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x119262 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119262 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x119267 (StorePre 0x119267 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x119267 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119267 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x11926c (movR64M64Effect 0x11926c 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x11926c (LoadPre 0x11926c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11926c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11926c 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x119271 (StorePre 0x119271 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x119271 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119271 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x119276 (movR64M64Effect 0x119276 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x119276 (LoadPre 0x119276 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x119276 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119276 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x11927b (movR64M64Effect 0x11927b 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x11927b (LoadPre 0x11927b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11927b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11927b 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x119280 (StorePre 0x119280 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x119280 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119280 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x119285 (StorePre 0x119285 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x119285 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x119285 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x119289 (movR64R64Effect 0x119289 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x119289 (fun s => s.RIP = 0x119289) (movR64R64Effect 0x119289 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x11928c (movR64R64Effect 0x11928c 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x11928c (fun s => s.RIP = 0x11928c) (movR64R64Effect 0x11928c 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x11928f (callEffect (fun _ => 0x1145f0) 0x119294) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x11928f (PushPre 0x11928f 5) (callEffect (fun _ => 0x1145f0) 0x119294) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x119294⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l119294, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l119258 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x5C, 0xB3, 0xFF, 0xFF]

theorem code_l119258 : ∀ x ∈ codeRange 0x119258 bytes_l119258, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x19258 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l119294 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x119294 (movR64M64Effect 0x119294 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x119294 (LoadPre 0x119294 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x119294 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119294 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x119299 (StorePre 0x119299 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x119299 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119299 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x11929e (movR64M64Effect 0x11929e 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x11929e (LoadPre 0x11929e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x11929e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11929e 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x1192a3 (StorePre 0x1192a3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1192a3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1192a3 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x1192a8 (movR64M64Effect 0x1192a8 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x1192a8 (LoadPre 0x1192a8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1192a8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1192a8 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x1192ad (StorePre 0x1192ad 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1192ad + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1192ad 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x1192b2 (movR64M64Effect 0x1192b2 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x1192b2 (LoadPre 0x1192b2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1192b2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1192b2 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x1192b7 (movR64M64Effect 0x1192b7 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x1192b7 (LoadPre 0x1192b7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1192b7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1192b7 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x1192bc (StorePre 0x1192bc 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1192bc + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1192bc 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x1192c1 (StorePre 0x1192c1 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1192c1 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1192c1 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x1192c5 (movR64R64Effect 0x1192c5 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x1192c5 (fun s => s.RIP = 0x1192c5) (movR64R64Effect 0x1192c5 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x1192c8 (movR64R64Effect 0x1192c8 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x1192c8 (fun s => s.RIP = 0x1192c8) (movR64R64Effect 0x1192c8 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x1192cb (callEffect (fun _ => 0x1145f0) 0x1192d0) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x1192cb (PushPre 0x1192cb 5) (callEffect (fun _ => 0x1145f0) 0x1192d0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x1192d0⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l1192d0, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l119294 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x20, 0xB3, 0xFF, 0xFF]

theorem code_l119294 : ∀ x ∈ codeRange 0x119294 bytes_l119294, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x19294 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1192d0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1192d0 (movR64M64Effect 0x1192d0 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1192d0 (LoadPre 0x1192d0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1192d0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1192d0 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x1192d5 (StorePre 0x1192d5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1192d5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1192d5 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x1192da (movR64M64Effect 0x1192da 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x1192da (LoadPre 0x1192da (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1192da + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1192da 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x1192df (StorePre 0x1192df 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1192df + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1192df 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x1192e4 (movR64M64Effect 0x1192e4 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x1192e4 (LoadPre 0x1192e4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1192e4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1192e4 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x1192e9 (StorePre 0x1192e9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1192e9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1192e9 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x1192ee (movR64M64Effect 0x1192ee 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x1192ee (LoadPre 0x1192ee (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1192ee + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1192ee 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x1192f3 (movR64M64Effect 0x1192f3 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x1192f3 (LoadPre 0x1192f3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1192f3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1192f3 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x1192f8 (StorePre 0x1192f8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1192f8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1192f8 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x1192fd (StorePre 0x1192fd 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1192fd + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1192fd 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x119301 (movR64R64Effect 0x119301 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x119301 (fun s => s.RIP = 0x119301) (movR64R64Effect 0x119301 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x119304 (movR64R64Effect 0x119304 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x119304 (fun s => s.RIP = 0x119304) (movR64R64Effect 0x119304 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x119307 (callEffect (fun _ => 0x1145f0) 0x11930c) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x119307 (PushPre 0x119307 5) (callEffect (fun _ => 0x1145f0) 0x11930c) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x11930c⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l11930c, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l1192d0 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0xE4, 0xB2, 0xFF, 0xFF]

theorem code_l1192d0 : ∀ x ∈ codeRange 0x1192d0 bytes_l1192d0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x192d0 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11930c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11930c (movR64M64Effect 0x11930c 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x11930c (LoadPre 0x11930c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x11930c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11930c 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x119311 (StorePre 0x119311 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x119311 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119311 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x119316 (movR64M64Effect 0x119316 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x119316 (LoadPre 0x119316 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x119316 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119316 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x11931b (StorePre 0x11931b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11931b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11931b 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x119320 (movR64M64Effect 0x119320 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x119320 (LoadPre 0x119320 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x119320 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119320 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x119325 (StorePre 0x119325 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x119325 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119325 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x11932a (movR64M64Effect 0x11932a 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x11932a (LoadPre 0x11932a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11932a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11932a 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x11932f (movR64M64Effect 0x11932f 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x11932f (LoadPre 0x11932f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11932f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11932f 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x119334 (StorePre 0x119334 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x119334 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119334 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x119339 (StorePre 0x119339 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x119339 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x119339 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x11933d (movR64R64Effect 0x11933d 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x11933d (fun s => s.RIP = 0x11933d) (movR64R64Effect 0x11933d 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x119340 (movR64R64Effect 0x119340 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x119340 (fun s => s.RIP = 0x119340) (movR64R64Effect 0x119340 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x119343 (callEffect (fun _ => 0x1145f0) 0x119348) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x119343 (PushPre 0x119343 5) (callEffect (fun _ => 0x1145f0) 0x119348) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x119348⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l119348, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l11930c : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0xA8, 0xB2, 0xFF, 0xFF]

theorem code_l11930c : ∀ x ∈ codeRange 0x11930c bytes_l11930c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1930c 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l119348 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x119348 (movR64M64Effect 0x119348 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x119348 (LoadPre 0x119348 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x119348 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119348 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x11934d (StorePre 0x11934d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11934d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11934d 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x119352 (movR64M64Effect 0x119352 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x119352 (LoadPre 0x119352 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x119352 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119352 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x119357 (StorePre 0x119357 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x119357 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119357 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x11935c (movR64M64Effect 0x11935c 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x11935c (LoadPre 0x11935c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11935c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11935c 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x119361 (StorePre 0x119361 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x119361 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119361 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x119366 (movR64M64Effect 0x119366 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x119366 (LoadPre 0x119366 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x119366 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119366 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x11936b (movR64M64Effect 0x11936b 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x11936b (LoadPre 0x11936b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11936b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11936b 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x119370 (StorePre 0x119370 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x119370 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119370 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x119375 (StorePre 0x119375 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x119375 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x119375 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x119379 (movR64R64Effect 0x119379 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x119379 (fun s => s.RIP = 0x119379) (movR64R64Effect 0x119379 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x11937c (movR64R64Effect 0x11937c 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x11937c (fun s => s.RIP = 0x11937c) (movR64R64Effect 0x11937c 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x11937f (callEffect (fun _ => 0x1145f0) 0x119384) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x11937f (PushPre 0x11937f 5) (callEffect (fun _ => 0x1145f0) 0x119384) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x119384⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l119384, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l119348 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x6C, 0xB2, 0xFF, 0xFF]

theorem code_l119348 : ∀ x ∈ codeRange 0x119348 bytes_l119348, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x19348 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l119384 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x119384 (movR64M64Effect 0x119384 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x119384 (LoadPre 0x119384 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x119384 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119384 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x119389 (StorePre 0x119389 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x119389 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119389 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x11938e (movR64M64Effect 0x11938e 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x11938e (LoadPre 0x11938e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x11938e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11938e 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x119393 (StorePre 0x119393 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x119393 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119393 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x119398 (movR64M64Effect 0x119398 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x119398 (LoadPre 0x119398 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x119398 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119398 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x11939d (StorePre 0x11939d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11939d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11939d 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x1193a2 (movR64M64Effect 0x1193a2 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x1193a2 (LoadPre 0x1193a2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1193a2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1193a2 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x1193a7 (movR64M64Effect 0x1193a7 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x1193a7 (LoadPre 0x1193a7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1193a7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1193a7 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x1193ac (StorePre 0x1193ac 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1193ac + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1193ac 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x1193b1 (StorePre 0x1193b1 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1193b1 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1193b1 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x1193b5 (movR64R64Effect 0x1193b5 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x1193b5 (fun s => s.RIP = 0x1193b5) (movR64R64Effect 0x1193b5 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x1193b8 (movR64R64Effect 0x1193b8 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x1193b8 (fun s => s.RIP = 0x1193b8) (movR64R64Effect 0x1193b8 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x1193bb (callEffect (fun _ => 0x1145f0) 0x1193c0) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x1193bb (PushPre 0x1193bb 5) (callEffect (fun _ => 0x1145f0) 0x1193c0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x1193c0⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l1193c0, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l119384 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x30, 0xB2, 0xFF, 0xFF]

theorem code_l119384 : ∀ x ∈ codeRange 0x119384 bytes_l119384, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x19384 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1193c0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1193c0 (movR64M64Effect 0x1193c0 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1193c0 (LoadPre 0x1193c0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1193c0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1193c0 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x1193c5 (StorePre 0x1193c5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1193c5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1193c5 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x1193ca (movR64M64Effect 0x1193ca 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x1193ca (LoadPre 0x1193ca (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1193ca + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1193ca 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x1193cf (StorePre 0x1193cf 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1193cf + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1193cf 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x1193d4 (movR64M64Effect 0x1193d4 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x1193d4 (LoadPre 0x1193d4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1193d4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1193d4 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x1193d9 (StorePre 0x1193d9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1193d9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1193d9 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x1193de (movR64M64Effect 0x1193de 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x1193de (LoadPre 0x1193de (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1193de + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1193de 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x1193e3 (movR64M64Effect 0x1193e3 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x1193e3 (LoadPre 0x1193e3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1193e3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1193e3 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x1193e8 (StorePre 0x1193e8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1193e8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1193e8 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x1193ed (StorePre 0x1193ed 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1193ed + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1193ed 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x1193f1 (movR64R64Effect 0x1193f1 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x1193f1 (fun s => s.RIP = 0x1193f1) (movR64R64Effect 0x1193f1 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x1193f4 (movR64R64Effect 0x1193f4 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x1193f4 (fun s => s.RIP = 0x1193f4) (movR64R64Effect 0x1193f4 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x1193f7 (callEffect (fun _ => 0x1145f0) 0x1193fc) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x1193f7 (PushPre 0x1193f7 5) (callEffect (fun _ => 0x1145f0) 0x1193fc) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x1193fc⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l1193fc, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l1193c0 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0xF4, 0xB1, 0xFF, 0xFF]

theorem code_l1193c0 : ∀ x ∈ codeRange 0x1193c0 bytes_l1193c0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x193c0 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1193fc : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1193fc (movR64M64Effect 0x1193fc 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1193fc (LoadPre 0x1193fc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1193fc + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1193fc 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x119401 (StorePre 0x119401 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x119401 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119401 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x119406 (movR64M64Effect 0x119406 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x119406 (LoadPre 0x119406 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x119406 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119406 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x11940b (StorePre 0x11940b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11940b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11940b 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x119410 (movR64M64Effect 0x119410 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x119410 (LoadPre 0x119410 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x119410 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119410 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x119415 (StorePre 0x119415 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x119415 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119415 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x11941a (movR64M64Effect 0x11941a 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x11941a (LoadPre 0x11941a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11941a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11941a 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x11941f (movR64M64Effect 0x11941f 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x11941f (LoadPre 0x11941f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11941f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11941f 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x119424 (StorePre 0x119424 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x119424 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119424 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x119429 (StorePre 0x119429 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x119429 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x119429 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x11942d (movR64R64Effect 0x11942d 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x11942d (fun s => s.RIP = 0x11942d) (movR64R64Effect 0x11942d 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x119430 (movR64R64Effect 0x119430 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x119430 (fun s => s.RIP = 0x119430) (movR64R64Effect 0x119430 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x119433 (callEffect (fun _ => 0x1145f0) 0x119438) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x119433 (PushPre 0x119433 5) (callEffect (fun _ => 0x1145f0) 0x119438) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x119438⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l119438, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l1193fc : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0xB8, 0xB1, 0xFF, 0xFF]

theorem code_l1193fc : ∀ x ∈ codeRange 0x1193fc bytes_l1193fc, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x193fc 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l119438 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x119438 (movR64M64Effect 0x119438 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x119438 (LoadPre 0x119438 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x119438 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119438 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x11943d (StorePre 0x11943d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11943d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11943d 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x119442 (movR64M64Effect 0x119442 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x119442 (LoadPre 0x119442 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x119442 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119442 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x119447 (StorePre 0x119447 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x119447 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119447 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x11944c (movR64M64Effect 0x11944c 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x11944c (LoadPre 0x11944c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11944c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11944c 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x119451 (StorePre 0x119451 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x119451 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119451 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x119456 (movR64M64Effect 0x119456 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x119456 (LoadPre 0x119456 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x119456 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119456 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x11945b (movR64M64Effect 0x11945b 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x11945b (LoadPre 0x11945b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11945b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11945b 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x119460 (StorePre 0x119460 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x119460 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119460 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x119465 (StorePre 0x119465 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x119465 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x119465 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x119469 (movR64R64Effect 0x119469 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x119469 (fun s => s.RIP = 0x119469) (movR64R64Effect 0x119469 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x11946c (movR64R64Effect 0x11946c 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x11946c (fun s => s.RIP = 0x11946c) (movR64R64Effect 0x11946c 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x11946f (callEffect (fun _ => 0x1145f0) 0x119474) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x11946f (PushPre 0x11946f 5) (callEffect (fun _ => 0x1145f0) 0x119474) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x119474⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l119474, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l119438 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x7C, 0xB1, 0xFF, 0xFF]

theorem code_l119438 : ∀ x ∈ codeRange 0x119438 bytes_l119438, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x19438 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l119474 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x119474 (movR64M64Effect 0x119474 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x119474 (LoadPre 0x119474 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x119474 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119474 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x119479 (StorePre 0x119479 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x119479 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119479 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x11947e (movR64M64Effect 0x11947e 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x11947e (LoadPre 0x11947e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x11947e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11947e 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x119483 (StorePre 0x119483 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x119483 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119483 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x119488 (movR64M64Effect 0x119488 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x119488 (LoadPre 0x119488 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x119488 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119488 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x11948d (StorePre 0x11948d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11948d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11948d 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x119492 (movR64M64Effect 0x119492 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x119492 (LoadPre 0x119492 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x119492 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119492 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x119497 (movR64M64Effect 0x119497 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x119497 (LoadPre 0x119497 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x119497 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119497 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x11949c (StorePre 0x11949c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11949c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11949c 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x1194a1 (StorePre 0x1194a1 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1194a1 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1194a1 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x1194a5 (movR64R64Effect 0x1194a5 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x1194a5 (fun s => s.RIP = 0x1194a5) (movR64R64Effect 0x1194a5 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x1194a8 (movR64R64Effect 0x1194a8 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x1194a8 (fun s => s.RIP = 0x1194a8) (movR64R64Effect 0x1194a8 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x1194ab (callEffect (fun _ => 0x1145f0) 0x1194b0) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x1194ab (PushPre 0x1194ab 5) (callEffect (fun _ => 0x1145f0) 0x1194b0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x1194b0⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l1194b0, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l119474 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x40, 0xB1, 0xFF, 0xFF]

theorem code_l119474 : ∀ x ∈ codeRange 0x119474 bytes_l119474, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x19474 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1194b0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1194b0 (movR64M64Effect 0x1194b0 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1194b0 (LoadPre 0x1194b0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1194b0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1194b0 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x1194b5 (StorePre 0x1194b5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1194b5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1194b5 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x1194ba (movR64M64Effect 0x1194ba 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x1194ba (LoadPre 0x1194ba (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1194ba + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1194ba 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x1194bf (StorePre 0x1194bf 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1194bf + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1194bf 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x1194c4 (movR64M64Effect 0x1194c4 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x1194c4 (LoadPre 0x1194c4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1194c4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1194c4 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x1194c9 (StorePre 0x1194c9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1194c9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1194c9 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x1194ce (movR64M64Effect 0x1194ce 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x1194ce (LoadPre 0x1194ce (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1194ce + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1194ce 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x1194d3 (movR64M64Effect 0x1194d3 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x1194d3 (LoadPre 0x1194d3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1194d3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1194d3 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x1194d8 (StorePre 0x1194d8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1194d8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1194d8 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x1194dd (StorePre 0x1194dd 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1194dd + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1194dd 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x1194e1 (movR64R64Effect 0x1194e1 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x1194e1 (fun s => s.RIP = 0x1194e1) (movR64R64Effect 0x1194e1 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x1194e4 (movR64R64Effect 0x1194e4 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x1194e4 (fun s => s.RIP = 0x1194e4) (movR64R64Effect 0x1194e4 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x1194e7 (callEffect (fun _ => 0x1145f0) 0x1194ec) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x1194e7 (PushPre 0x1194e7 5) (callEffect (fun _ => 0x1145f0) 0x1194ec) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x1194ec⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l1194ec, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l1194b0 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x04, 0xB1, 0xFF, 0xFF]

theorem code_l1194b0 : ∀ x ∈ codeRange 0x1194b0 bytes_l1194b0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x194b0 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1194ec : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1194ec (movR64M64Effect 0x1194ec 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1194ec (LoadPre 0x1194ec (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1194ec + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1194ec 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x1194f1 (StorePre 0x1194f1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1194f1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1194f1 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x1194f6 (movR64M64Effect 0x1194f6 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x1194f6 (LoadPre 0x1194f6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1194f6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1194f6 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x1194fb (StorePre 0x1194fb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1194fb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1194fb 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x119500 (movR64M64Effect 0x119500 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x119500 (LoadPre 0x119500 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x119500 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119500 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x119505 (StorePre 0x119505 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x119505 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119505 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x11950a (movR64M64Effect 0x11950a 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x11950a (LoadPre 0x11950a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11950a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11950a 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x11950f (movR64M64Effect 0x11950f 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x11950f (LoadPre 0x11950f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11950f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11950f 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x119514 (StorePre 0x119514 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x119514 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119514 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x119519 (StorePre 0x119519 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x119519 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x119519 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x11951d (movR64R64Effect 0x11951d 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x11951d (fun s => s.RIP = 0x11951d) (movR64R64Effect 0x11951d 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x119520 (movR64R64Effect 0x119520 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x119520 (fun s => s.RIP = 0x119520) (movR64R64Effect 0x119520 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x119523 (callEffect (fun _ => 0x1145f0) 0x119528) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x119523 (PushPre 0x119523 5) (callEffect (fun _ => 0x1145f0) 0x119528) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x119528⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l119528, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l1194ec : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0xC8, 0xB0, 0xFF, 0xFF]

theorem code_l1194ec : ∀ x ∈ codeRange 0x1194ec bytes_l1194ec, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x194ec 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l119528 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x119528 (movR64M64Effect 0x119528 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x119528 (LoadPre 0x119528 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x119528 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119528 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x11952d (StorePre 0x11952d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11952d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11952d 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x119532 (movR64M64Effect 0x119532 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x119532 (LoadPre 0x119532 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x119532 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119532 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x119537 (StorePre 0x119537 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x119537 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119537 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x11953c (movR64M64Effect 0x11953c 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x11953c (LoadPre 0x11953c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11953c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11953c 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x119541 (StorePre 0x119541 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x119541 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119541 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x119546 (movR64M64Effect 0x119546 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x119546 (LoadPre 0x119546 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x119546 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119546 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x11954b (movR64M64Effect 0x11954b 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x11954b (LoadPre 0x11954b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11954b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11954b 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x119550 (StorePre 0x119550 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x119550 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119550 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x119555 (StorePre 0x119555 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x119555 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x119555 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x119559 (movR64R64Effect 0x119559 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x119559 (fun s => s.RIP = 0x119559) (movR64R64Effect 0x119559 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x11955c (movR64R64Effect 0x11955c 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x11955c (fun s => s.RIP = 0x11955c) (movR64R64Effect 0x11955c 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x11955f (callEffect (fun _ => 0x1145f0) 0x119564) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x11955f (PushPre 0x11955f 5) (callEffect (fun _ => 0x1145f0) 0x119564) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x119564⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l119564, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l119528 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x8C, 0xB0, 0xFF, 0xFF]

theorem code_l119528 : ∀ x ∈ codeRange 0x119528 bytes_l119528, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x19528 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l119564 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x119564 (movR64M64Effect 0x119564 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x119564 (LoadPre 0x119564 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x119564 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119564 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x119569 (StorePre 0x119569 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x119569 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119569 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x11956e (movR64M64Effect 0x11956e 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x11956e (LoadPre 0x11956e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x11956e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11956e 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x119573 (StorePre 0x119573 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x119573 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119573 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x119578 (movR64M64Effect 0x119578 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x119578 (LoadPre 0x119578 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x119578 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119578 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x11957d (StorePre 0x11957d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11957d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11957d 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x119582 (movR64M64Effect 0x119582 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x119582 (LoadPre 0x119582 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x119582 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119582 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x119587 (movR64M64Effect 0x119587 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x119587 (LoadPre 0x119587 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x119587 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119587 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x11958c (StorePre 0x11958c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11958c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11958c 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x119591 (StorePre 0x119591 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x119591 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x119591 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x119595 (movR64R64Effect 0x119595 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x119595 (fun s => s.RIP = 0x119595) (movR64R64Effect 0x119595 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x119598 (movR64R64Effect 0x119598 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x119598 (fun s => s.RIP = 0x119598) (movR64R64Effect 0x119598 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x11959b (callEffect (fun _ => 0x1145f0) 0x1195a0) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x11959b (PushPre 0x11959b 5) (callEffect (fun _ => 0x1145f0) 0x1195a0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x1195a0⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l1195a0, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l119564 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x50, 0xB0, 0xFF, 0xFF]

theorem code_l119564 : ∀ x ∈ codeRange 0x119564 bytes_l119564, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x19564 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1195a0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1195a0 (movR64M64Effect 0x1195a0 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1195a0 (LoadPre 0x1195a0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1195a0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1195a0 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x1195a5 (StorePre 0x1195a5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1195a5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1195a5 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x1195aa (movR64M64Effect 0x1195aa 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x1195aa (LoadPre 0x1195aa (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1195aa + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1195aa 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x1195af (StorePre 0x1195af 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1195af + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1195af 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x1195b4 (movR64M64Effect 0x1195b4 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x1195b4 (LoadPre 0x1195b4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1195b4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1195b4 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x1195b9 (StorePre 0x1195b9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1195b9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1195b9 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x1195be (movR64M64Effect 0x1195be 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x1195be (LoadPre 0x1195be (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1195be + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1195be 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x1195c3 (movR64M64Effect 0x1195c3 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x1195c3 (LoadPre 0x1195c3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1195c3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1195c3 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x1195c8 (StorePre 0x1195c8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1195c8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1195c8 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x1195cd (StorePre 0x1195cd 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1195cd + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1195cd 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x1195d1 (movR64R64Effect 0x1195d1 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x1195d1 (fun s => s.RIP = 0x1195d1) (movR64R64Effect 0x1195d1 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x1195d4 (movR64R64Effect 0x1195d4 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x1195d4 (fun s => s.RIP = 0x1195d4) (movR64R64Effect 0x1195d4 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x1195d7 (callEffect (fun _ => 0x1145f0) 0x1195dc) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x1195d7 (PushPre 0x1195d7 5) (callEffect (fun _ => 0x1145f0) 0x1195dc) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x1195dc⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l1195dc, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l1195a0 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x14, 0xB0, 0xFF, 0xFF]

theorem code_l1195a0 : ∀ x ∈ codeRange 0x1195a0 bytes_l1195a0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x195a0 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1195dc : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1195dc (movR64M64Effect 0x1195dc 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1195dc (LoadPre 0x1195dc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1195dc + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1195dc 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x1195e1 (StorePre 0x1195e1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1195e1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1195e1 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x1195e6 (movR64M64Effect 0x1195e6 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x1195e6 (LoadPre 0x1195e6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1195e6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1195e6 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x1195eb (StorePre 0x1195eb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1195eb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1195eb 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x1195f0 (movR64M64Effect 0x1195f0 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x1195f0 (LoadPre 0x1195f0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1195f0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1195f0 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x1195f5 (StorePre 0x1195f5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1195f5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1195f5 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x1195fa (movR64M64Effect 0x1195fa 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x1195fa (LoadPre 0x1195fa (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1195fa + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1195fa 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x1195ff (movR64M64Effect 0x1195ff 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x1195ff (LoadPre 0x1195ff (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1195ff + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1195ff 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x119604 (StorePre 0x119604 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x119604 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119604 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x119609 (StorePre 0x119609 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x119609 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x119609 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x11960d (movR64R64Effect 0x11960d 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x11960d (fun s => s.RIP = 0x11960d) (movR64R64Effect 0x11960d 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x119610 (movR64R64Effect 0x119610 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x119610 (fun s => s.RIP = 0x119610) (movR64R64Effect 0x119610 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x119613 (callEffect (fun _ => 0x1145f0) 0x119618) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x119613 (PushPre 0x119613 5) (callEffect (fun _ => 0x1145f0) 0x119618) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x119618⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l119618, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l1195dc : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0xD8, 0xAF, 0xFF, 0xFF]

theorem code_l1195dc : ∀ x ∈ codeRange 0x1195dc bytes_l1195dc, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x195dc 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l119618 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x119618 (movR64M64Effect 0x119618 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x119618 (LoadPre 0x119618 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x119618 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119618 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x11961d (StorePre 0x11961d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11961d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11961d 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x119622 (movR64M64Effect 0x119622 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x119622 (LoadPre 0x119622 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x119622 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119622 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x119627 (StorePre 0x119627 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x119627 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119627 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x11962c (movR64M64Effect 0x11962c 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x11962c (LoadPre 0x11962c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11962c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11962c 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x119631 (StorePre 0x119631 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x119631 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119631 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x119636 (movR64M64Effect 0x119636 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x119636 (LoadPre 0x119636 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x119636 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119636 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x11963b (movR64M64Effect 0x11963b 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x11963b (LoadPre 0x11963b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11963b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11963b 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x119640 (StorePre 0x119640 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x119640 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119640 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x119645 (StorePre 0x119645 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x119645 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x119645 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x119649 (movR64R64Effect 0x119649 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x119649 (fun s => s.RIP = 0x119649) (movR64R64Effect 0x119649 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x11964c (movR64R64Effect 0x11964c 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x11964c (fun s => s.RIP = 0x11964c) (movR64R64Effect 0x11964c 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x11964f (callEffect (fun _ => 0x1145f0) 0x119654) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x11964f (PushPre 0x11964f 5) (callEffect (fun _ => 0x1145f0) 0x119654) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x119654⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l119654, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l119618 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x9C, 0xAF, 0xFF, 0xFF]

theorem code_l119618 : ∀ x ∈ codeRange 0x119618 bytes_l119618, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x19618 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l119654 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x119654 (movR64M64Effect 0x119654 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x119654 (LoadPre 0x119654 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x119654 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119654 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x119659 (StorePre 0x119659 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x119659 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119659 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x11965e (movR64M64Effect 0x11965e 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x11965e (LoadPre 0x11965e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x11965e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11965e 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x119663 (StorePre 0x119663 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x119663 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119663 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x119668 (movR64M64Effect 0x119668 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x119668 (LoadPre 0x119668 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x119668 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119668 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x11966d (StorePre 0x11966d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11966d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11966d 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x119672 (movR64M64Effect 0x119672 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x119672 (LoadPre 0x119672 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x119672 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119672 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x119677 (movR64M64Effect 0x119677 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x119677 (LoadPre 0x119677 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x119677 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119677 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x11967c (StorePre 0x11967c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11967c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11967c 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x119681 (StorePre 0x119681 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x119681 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x119681 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x119685 (movR64R64Effect 0x119685 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x119685 (fun s => s.RIP = 0x119685) (movR64R64Effect 0x119685 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x119688 (movR64R64Effect 0x119688 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x119688 (fun s => s.RIP = 0x119688) (movR64R64Effect 0x119688 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x11968b (callEffect (fun _ => 0x1145f0) 0x119690) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x11968b (PushPre 0x11968b 5) (callEffect (fun _ => 0x1145f0) 0x119690) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x119690⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l119690, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l119654 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x60, 0xAF, 0xFF, 0xFF]

theorem code_l119654 : ∀ x ∈ codeRange 0x119654 bytes_l119654, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x19654 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l119690 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x119690 (movR64M64Effect 0x119690 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x119690 (LoadPre 0x119690 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x119690 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119690 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x119695 (StorePre 0x119695 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x119695 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119695 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x11969a (movR64M64Effect 0x11969a 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x11969a (LoadPre 0x11969a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x11969a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11969a 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x11969f (StorePre 0x11969f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11969f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11969f 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x1196a4 (movR64M64Effect 0x1196a4 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x1196a4 (LoadPre 0x1196a4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1196a4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1196a4 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x1196a9 (StorePre 0x1196a9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1196a9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1196a9 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x1196ae (movR64M64Effect 0x1196ae 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x1196ae (LoadPre 0x1196ae (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1196ae + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1196ae 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x1196b3 (movR64M64Effect 0x1196b3 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x1196b3 (LoadPre 0x1196b3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1196b3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1196b3 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x1196b8 (StorePre 0x1196b8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1196b8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1196b8 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x1196bd (StorePre 0x1196bd 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1196bd + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1196bd 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x1196c1 (movR64R64Effect 0x1196c1 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x1196c1 (fun s => s.RIP = 0x1196c1) (movR64R64Effect 0x1196c1 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x1196c4 (movR64R64Effect 0x1196c4 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x1196c4 (fun s => s.RIP = 0x1196c4) (movR64R64Effect 0x1196c4 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x1196c7 (callEffect (fun _ => 0x1145f0) 0x1196cc) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x1196c7 (PushPre 0x1196c7 5) (callEffect (fun _ => 0x1145f0) 0x1196cc) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x1196cc⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l1196cc, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l119690 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x24, 0xAF, 0xFF, 0xFF]

theorem code_l119690 : ∀ x ∈ codeRange 0x119690 bytes_l119690, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x19690 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1196cc : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1196cc (movR64M64Effect 0x1196cc 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1196cc (LoadPre 0x1196cc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1196cc + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1196cc 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x1196d1 (StorePre 0x1196d1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1196d1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1196d1 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x1196d6 (movR64M64Effect 0x1196d6 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x1196d6 (LoadPre 0x1196d6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1196d6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1196d6 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x1196db (StorePre 0x1196db 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1196db + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1196db 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x1196e0 (movR64M64Effect 0x1196e0 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x1196e0 (LoadPre 0x1196e0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1196e0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1196e0 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x1196e5 (StorePre 0x1196e5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1196e5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1196e5 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x1196ea (movR64M64Effect 0x1196ea 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x1196ea (LoadPre 0x1196ea (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1196ea + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1196ea 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x1196ef (movR64M64Effect 0x1196ef 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x1196ef (LoadPre 0x1196ef (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1196ef + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1196ef 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x1196f4 (StorePre 0x1196f4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1196f4 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1196f4 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x1196f9 (StorePre 0x1196f9 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1196f9 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1196f9 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x1196fd (movR64R64Effect 0x1196fd 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x1196fd (fun s => s.RIP = 0x1196fd) (movR64R64Effect 0x1196fd 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x119700 (movR64R64Effect 0x119700 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x119700 (fun s => s.RIP = 0x119700) (movR64R64Effect 0x119700 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x119703 (callEffect (fun _ => 0x1145f0) 0x119708) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x119703 (PushPre 0x119703 5) (callEffect (fun _ => 0x1145f0) 0x119708) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x119708⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l119708, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l1196cc : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0xE8, 0xAE, 0xFF, 0xFF]

theorem code_l1196cc : ∀ x ∈ codeRange 0x1196cc bytes_l1196cc, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x196cc 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l119708 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x119708 (movR64M64Effect 0x119708 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x119708 (LoadPre 0x119708 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x119708 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119708 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x11970d (StorePre 0x11970d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11970d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11970d 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x119712 (movR64M64Effect 0x119712 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x119712 (LoadPre 0x119712 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x119712 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119712 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x119717 (StorePre 0x119717 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x119717 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119717 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x11971c (movR64M64Effect 0x11971c 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x11971c (LoadPre 0x11971c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11971c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11971c 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x119721 (StorePre 0x119721 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x119721 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119721 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x119726 (movR64M64Effect 0x119726 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x119726 (LoadPre 0x119726 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x119726 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119726 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x11972b (movR64M64Effect 0x11972b 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x11972b (LoadPre 0x11972b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11972b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11972b 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x119730 (StorePre 0x119730 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x119730 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119730 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x119735 (StorePre 0x119735 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x119735 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x119735 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x119739 (movR64R64Effect 0x119739 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x119739 (fun s => s.RIP = 0x119739) (movR64R64Effect 0x119739 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x11973c (movR64R64Effect 0x11973c 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x11973c (fun s => s.RIP = 0x11973c) (movR64R64Effect 0x11973c 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x11973f (callEffect (fun _ => 0x1145f0) 0x119744) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x11973f (PushPre 0x11973f 5) (callEffect (fun _ => 0x1145f0) 0x119744) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x119744⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l119744, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l119708 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0xAC, 0xAE, 0xFF, 0xFF]

theorem code_l119708 : ∀ x ∈ codeRange 0x119708 bytes_l119708, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x19708 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l119744 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x119744 (movR64M64Effect 0x119744 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x119744 (LoadPre 0x119744 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x119744 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119744 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x119749 (StorePre 0x119749 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x119749 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119749 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x11974e (movR64M64Effect 0x11974e 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x11974e (LoadPre 0x11974e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x11974e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11974e 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x119753 (StorePre 0x119753 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x119753 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x119753 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x119758 (movR64M64Effect 0x119758 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x119758 (LoadPre 0x119758 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x119758 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119758 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x11975d (StorePre 0x11975d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11975d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11975d 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x119762 (movR64M64Effect 0x119762 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x119762 (LoadPre 0x119762 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x119762 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119762 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x119767 (movR64M64Effect 0x119767 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x119767 (LoadPre 0x119767 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x119767 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x119767 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x11976c (StorePre 0x11976c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11976c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11976c 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x119771 (StorePre 0x119771 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x119771 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x119771 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x119775 (movR64R64Effect 0x119775 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 69) (.exec 0x119775 (fun s => s.RIP = 0x119775) (movR64R64Effect 0x119775 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.out 0x119778 (movR64R64Effect 0x119778 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 71) (.exec 0x119778 (fun s => s.RIP = 0x119778) (movR64R64Effect 0x119778 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x11977b (callEffect (fun _ => 0x1145f0) 0x119780) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x11977b (PushPre 0x11977b 5) (callEffect (fun _ => 0x1145f0) 0x119780) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x119780⟩) #v[]
    (.terminate (.call ⟨.l1145f0, RegMap.args [(0, 62), (1, 64), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l119780, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l119744 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48,
    0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B,
    0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x04,
    0x24, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0xE8, 0x70, 0xAE, 0xFF, 0xFF]

theorem code_l119744 : ∀ x ∈ codeRange 0x119744 bytes_l119744, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x19744 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

end K256.Proofs.Signing.LIR
