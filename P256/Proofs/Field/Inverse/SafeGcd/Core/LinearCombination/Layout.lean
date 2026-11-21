import P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic.LinearCombination.Model
import P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine
import P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine.LinearCombination.Frame
import P256.Proofs.Field.Inverse.SafeGcd.Core.Support

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

inductive Label where
  | entry | stage0 | stage1 | stage2 | stage3 | stage4 | stage5 | stage6 | stage7 | stage8 | stage9 | stage10 | stage11 | stage12 | stage13 | stage14 | stage15 | stage16 | stage17

@[refine_layout] def start : Label → Machine.Label
  | .entry => .l116d00
  | .stage0 => .l116d0e
  | .stage1 => .l116d4e
  | .stage2 => .l116d95
  | .stage3 => .l116de3
  | .stage4 => .l116e0f
  | .stage5 => .l116e59
  | .stage6 => .l116e9d
  | .stage7 => .l116eb9
  | .stage8 => .l116ede
  | .stage9 => .l116f0b
  | .stage10 => .l116f39
  | .stage11 => .l116f67
  | .stage12 => .l116fbb
  | .stage13 => .l116fd8
  | .stage14 => .l11700a
  | .stage15 => .l117033
  | .stage16 => .l117072
  | .stage17 => .l117080

def program : Program Support.Op Label (fun _ => 0) 0 where
  blocks
  | .entry => .terminate (.br ⟨.stage0, #v[]⟩)
  | .stage0 => .terminate (.br ⟨.stage1, #v[]⟩)
  | .stage1 => .terminate (.br ⟨.stage2, #v[]⟩)
  | .stage2 => .terminate (.br ⟨.stage3, #v[]⟩)
  | .stage3 => .terminate (.br ⟨.stage4, #v[]⟩)
  | .stage4 => .terminate (.br ⟨.stage5, #v[]⟩)
  | .stage5 => .terminate (.br ⟨.stage6, #v[]⟩)
  | .stage6 => .terminate (.br ⟨.stage7, #v[]⟩)
  | .stage7 => .terminate (.br ⟨.stage8, #v[]⟩)
  | .stage8 => .terminate (.br ⟨.stage9, #v[]⟩)
  | .stage9 => .terminate (.br ⟨.stage10, #v[]⟩)
  | .stage10 => .terminate (.br ⟨.stage11, #v[]⟩)
  | .stage11 => .terminate (.br ⟨.stage12, #v[]⟩)
  | .stage12 => .terminate (.br ⟨.stage13, #v[]⟩)
  | .stage13 => .terminate (.br ⟨.stage14, #v[]⟩)
  | .stage14 => .terminate (.br ⟨.stage15, #v[]⟩)
  | .stage15 => .terminate (.br ⟨.stage16, #v[]⟩)
  | .stage16 => .terminate (.br ⟨.stage17, #v[]⟩)
  | .stage17 => .terminate (.ret #v[])

@[refine_layout] def commonAtoms (fr : Activation) (controls : RamState) (p : Inputs) : List Atom :=
  [.reg 39 ⟨32, controls.MXCSR⟩, .reg 51 ⟨16, controls.FP87_Control⟩,
   .writable fr.rdi 41,
   .fact (fr.rdi.toNat + 41 ≤ fr.low.toNat ∨ fr.rsp.toNat + 8 ≤ fr.rdi.toNat),
   .words fr.rsi 64 p.a, .words fr.rdx 64 p.b,
   .mem (fr.rsi + 32) 8 p.aSign, .mem (fr.rdx + 32) 8 p.bSign,
   .readable fr.rsi 33, .readable fr.rdx 33,
   .fact (fr.rsi.toNat + 33 ≤ fr.low.toNat ∨ fr.rsp.toNat ≤ fr.rsi.toNat),
   .fact (fr.rdx.toNat + 33 ≤ fr.low.toNat ∨ fr.rsp.toNat ≤ fr.rdx.toNat),
   .fact (fr.rcx = p.u), .fact (fr.r8 = p.v)]

@[refine_layout] def coreAtoms (l : Label) (fr : Activation) (p : Inputs) : List Atom :=
  match l with
  | .entry | .stage0 => []
  | .stage1 =>
      [.gpr 8 (p.v),
       .gpr 11 (fr.rdx),
       .gpr 0 (v1b1106 p),
       .gpr 3 (v1b1106 p),
       .mem (fr.rsp - 0x50) 64 (v1b10e4 p),
       .mem (fr.rsp - 0x58) 64 (v1b110c p),
       .mem (fr.rsp - 0x70) 8 ((v1b110c p).setWidth 8)]
  | .stage2 =>
      [.gpr 1 ((v1b1158 p).2),
       .gpr 11 (fr.rdx),
       .gpr 3 ((v1b1158 p).1),
       .gpr 10 ((v1b111e p).1),
       .gpr 14 ((v1b111e p).2),
       .gpr 9 ((v1b1130 p).1),
       .gpr 15 ((v1b1130 p).2),
       .gpr 13 (v1b1162 p),
       .gpr 12 ((v1b1145 p).1),
       .gpr 5 ((v1b1145 p).2),
       .mem (fr.rsp - 0x50) 64 (v1b10e4 p),
       .mem (fr.rsp - 0x58) 64 (v1b110c p),
       .mem (fr.rsp - 0x70) 8 ((v1b110c p).setWidth 8)]
  | .stage3 =>
      [.gpr 2 ((v1b11af p).2),
       .gpr 1 ((v1b116e p).1),
       .gpr 8 (mergeGPR 8 (v1b11a3 p) (v1b10e4 p)),
       .gpr 11 (fr.rdx),
       .gpr 0 ((v1b11af p).1),
       .gpr 3 ((v1b116b p).1),
       .gpr 10 ((v1b111e p).1),
       .gpr 14 ((v1b1194 p).1),
       .gpr 9 ((v1b1165 p).1),
       .gpr 15 ((v1b1185 p).1),
       .gpr 12 ((v1b1168 p).1),
       .gpr 5 ((v1b1194 p).2),
       .mem (fr.rsp - 0x58) 64 (v1b110c p),
       .mem (fr.rsp - 0x70) 8 ((v1b110c p).setWidth 8),
       .mem (fr.rsp - 0x60) 64 ((v1b1175 p).2),
       .mem (fr.rsp - 0x48) 64 ((v1b1175 p).1),
       .mem (fr.rsp - 0x68) 64 ((v1b1185 p).2),
       .mem (fr.rsp - 0x50) 64 (mergeGPR 8 (v1b11a3 p) (v1b10e4 p))]
  | .stage4 =>
      [.gpr 6 ((v1b11b8 p).1),
       .gpr 2 (mergeGPR 8 (v1b11d6 p) (v1b110c p)),
       .gpr 1 ((v1b116e p).1),
       .gpr 8 (mergeGPR 8 (v1b11a3 p) (v1b10e4 p)),
       .gpr 0 ((v1b11c5 p).1),
       .gpr 3 ((v1b116b p).1),
       .gpr 10 ((v1b111e p).1),
       .gpr 9 ((v1b1165 p).1),
       .gpr 15 ((v1b11b3 p).1),
       .gpr 12 ((v1b1168 p).1),
       .mem (fr.rsp - 0x70) 8 ((v1b110c p).setWidth 8),
       .mem (fr.rsp - 0x60) 64 ((v1b1175 p).2),
       .mem (fr.rsp - 0x48) 64 ((v1b1175 p).1),
       .mem (fr.rsp - 0x50) 64 (mergeGPR 8 (v1b11a3 p) (v1b10e4 p)),
       .mem (fr.rsp - 0x40) 64 ((v1b11b8 p).1),
       .mem (fr.rsp - 0x68) 64 ((v1b11c8 p).1),
       .mem (fr.rsp - 0x58) 64 (mergeGPR 8 (v1b11d6 p) (v1b110c p))]
  | .stage5 =>
      [.gpr 2 ((v1b120f p).1),
       .gpr 1 ((v1b116e p).1),
       .gpr 8 ((v1b1207 p).1),
       .gpr 11 (mergeGPR 8 (v1b11ea p) (mergeGPR 8 (v1b11e2 p) (((mergeGPR 8 (v1b11d6 p) (v1b110c p)).setWidth 32 : BitVec 32).setWidth 64))),
       .gpr 0 ((v1b11c5 p).1),
       .gpr 3 ((v1b116b p).1),
       .gpr 10 ((v1b111e p).1),
       .gpr 14 ((v1b1175 p).1),
       .gpr 9 ((v1b1165 p).1),
       .gpr 15 ((v1b11b3 p).1),
       .gpr 13 (v1b11f6 p),
       .gpr 12 ((v1b1168 p).1),
       .gpr 5 ((v1b11fe p).1),
       .mem (fr.rsp - 0x48) 64 ((v1b1175 p).1),
       .mem (fr.rsp - 0x50) 64 (mergeGPR 8 (v1b11a3 p) (v1b10e4 p)),
       .mem (fr.rsp - 0x40) 64 ((v1b11b8 p).1),
       .mem (fr.rsp - 0x68) 64 ((v1b11c8 p).1),
       .mem (fr.rsp - 0x58) 64 (mergeGPR 8 (v1b11d6 p) (v1b110c p)),
       .mem (fr.rsp - 0x60) 8 ((mergeGPR 8 (v1b11e2 p) (((mergeGPR 8 (v1b11d6 p) (v1b110c p)).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8),
       .mem (fr.rsp - 0x38) 64 ((((if !((v1b120f p).2.CF) then 1 else 0 : BitVec 8)).setWidth 32 : BitVec 32).setWidth 64),
       .mem (fr.rsp - 0x70) 8 ((mergeGPR 8 (v1b11ea p) (mergeGPR 8 (v1b11e2 p) (((mergeGPR 8 (v1b11d6 p) (v1b110c p)).setWidth 32 : BitVec 32).setWidth 64))).setWidth 8)]
  | .stage6 =>
      [.gpr 6 (v1b1236 p),
       .gpr 2 ((v1b120f p).1),
       .gpr 1 ((v1b116e p).1),
       .gpr 8 (v1b125d p),
       .gpr 11 (mergeGPR 8 (v1b11ea p) (mergeGPR 8 (v1b11e2 p) (((mergeGPR 8 (v1b11d6 p) (v1b110c p)).setWidth 32 : BitVec 32).setWidth 64))),
       .gpr 0 ((v1b11c5 p).1),
       .gpr 3 ((v1b116b p).1),
       .gpr 10 ((v1b111e p).1),
       .gpr 9 ((v1b1165 p).1),
       .gpr 13 (v1b124e p),
       .gpr 12 ((v1b1168 p).1),
       .gpr 5 (v1b126a p),
       .mem (fr.rsp - 0x48) 64 ((v1b1175 p).1),
       .mem (fr.rsp - 0x50) 64 (mergeGPR 8 (v1b11a3 p) (v1b10e4 p)),
       .mem (fr.rsp - 0x40) 64 ((v1b11b8 p).1),
       .mem (fr.rsp - 0x68) 64 ((v1b11c8 p).1),
       .mem (fr.rsp - 0x58) 64 (mergeGPR 8 (v1b11d6 p) (v1b110c p)),
       .mem (fr.rsp - 0x60) 8 ((mergeGPR 8 (v1b11e2 p) (((mergeGPR 8 (v1b11d6 p) (v1b110c p)).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8),
       .mem (fr.rsp - 0x38) 64 ((((if !((v1b120f p).2.CF) then 1 else 0 : BitVec 8)).setWidth 32 : BitVec 32).setWidth 64),
       .mem (fr.rsp - 0x70) 8 ((mergeGPR 8 (v1b11ea p) (mergeGPR 8 (v1b11e2 p) (((mergeGPR 8 (v1b11d6 p) (v1b110c p)).setWidth 32 : BitVec 32).setWidth 64))).setWidth 8)]
  | .stage7 =>
      [.gpr 6 (v1b1236 p),
       .gpr 1 ((v1b116e p).1),
       .gpr 8 (v1b125d p),
       .gpr 3 ((v1b116b p).1),
       .gpr 10 ((v1b111e p).1),
       .gpr 9 ((v1b1165 p).1),
       .gpr 15 (v1b127f p),
       .gpr 13 (v1b124e p),
       .gpr 12 ((v1b1168 p).1),
       .gpr 5 (v1b126a p),
       .mem (fr.rsp - 0x48) 64 ((v1b1175 p).1),
       .mem (fr.rsp - 0x50) 64 (mergeGPR 8 (v1b11a3 p) (v1b10e4 p)),
       .mem (fr.rsp - 0x40) 64 ((v1b11b8 p).1),
       .mem (fr.rsp - 0x68) 64 ((v1b11c8 p).1),
       .mem (fr.rsp - 0x58) 64 (mergeGPR 8 (v1b11d6 p) (v1b110c p)),
       .mem (fr.rsp - 0x60) 8 ((mergeGPR 8 (v1b11e2 p) (((mergeGPR 8 (v1b11d6 p) (v1b110c p)).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8),
       .mem (fr.rsp - 0x38) 64 ((((if !((v1b120f p).2.CF) then 1 else 0 : BitVec 8)).setWidth 32 : BitVec 32).setWidth 64),
       .mem (fr.rsp - 0x70) 8 ((mergeGPR 8 (v1b11ea p) (mergeGPR 8 (v1b11e2 p) (((mergeGPR 8 (v1b11d6 p) (v1b110c p)).setWidth 32 : BitVec 32).setWidth 64))).setWidth 8)]
  | .stage8 =>
      [.gpr 1 ((v1b116e p).1),
       .gpr 8 (v1b125d p),
       .gpr 0 (v1b128c p),
       .gpr 3 ((v1b116b p).1),
       .gpr 10 (v1b12a1 p),
       .gpr 14 ((((mergeGPR 8 (v1b11ea p) (mergeGPR 8 (v1b11e2 p) (((mergeGPR 8 (v1b11d6 p) (v1b110c p)).setWidth 32 : BitVec 32).setWidth 64))).setWidth 8).setWidth 32 : BitVec 32).setWidth 64),
       .gpr 9 ((v1b1165 p).1),
       .gpr 15 (v1b127f p),
       .gpr 13 (v1b124e p),
       .gpr 12 ((v1b1168 p).1),
       .gpr 5 (v1b126a p),
       .mem (fr.rsp - 0x48) 64 ((v1b1175 p).1),
       .mem (fr.rsp - 0x50) 64 (mergeGPR 8 (v1b11a3 p) (v1b10e4 p)),
       .mem (fr.rsp - 0x40) 64 ((v1b11b8 p).1),
       .mem (fr.rsp - 0x68) 64 ((v1b11c8 p).1),
       .mem (fr.rsp - 0x58) 64 (mergeGPR 8 (v1b11d6 p) (v1b110c p)),
       .mem (fr.rsp - 0x60) 8 ((mergeGPR 8 (v1b11e2 p) (((mergeGPR 8 (v1b11d6 p) (v1b110c p)).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8),
       .mem (fr.rsp - 0x38) 64 ((((if !((v1b120f p).2.CF) then 1 else 0 : BitVec 8)).setWidth 32 : BitVec 32).setWidth 64),
       .mem (fr.rsp - 0x70) 64 (v1b12a1 p)]
  | .stage9 =>
      [.gpr 1 ((v1b116e p).1),
       .gpr 8 ((v1b12c2 p).1),
       .gpr 0 (v1b128c p),
       .gpr 3 ((v1b116b p).1),
       .gpr 10 (v1b12a1 p),
       .gpr 14 ((((mergeGPR 8 (v1b11ea p) (mergeGPR 8 (v1b11e2 p) (((mergeGPR 8 (v1b11d6 p) (v1b110c p)).setWidth 32 : BitVec 32).setWidth 64))).setWidth 8).setWidth 32 : BitVec 32).setWidth 64),
       .gpr 9 (v1b12d7 p),
       .gpr 15 (v1b127f p),
       .gpr 12 ((v1b1168 p).1),
       .gpr 5 (v1b126a p),
       .mem (fr.rsp - 0x48) 64 ((v1b1175 p).1),
       .mem (fr.rsp - 0x50) 64 (mergeGPR 8 (v1b11a3 p) (v1b10e4 p)),
       .mem (fr.rsp - 0x40) 64 ((v1b11b8 p).1),
       .mem (fr.rsp - 0x68) 64 ((v1b11c8 p).1),
       .mem (fr.rsp - 0x58) 64 (mergeGPR 8 (v1b11d6 p) (v1b110c p)),
       .mem (fr.rsp - 0x60) 8 ((mergeGPR 8 (v1b11e2 p) (((mergeGPR 8 (v1b11d6 p) (v1b110c p)).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8),
       .mem (fr.rsp - 0x38) 64 ((((if !((v1b120f p).2.CF) then 1 else 0 : BitVec 8)).setWidth 32 : BitVec 32).setWidth 64),
       .mem (fr.rsp - 0x70) 64 (v1b12a1 p)]
  | .stage10 =>
      [.gpr 1 ((v1b116e p).1),
       .gpr 8 ((v1b12c2 p).1),
       .gpr 0 (v1b128c p),
       .gpr 3 ((v1b116b p).1),
       .gpr 10 (v1b12a1 p),
       .gpr 14 ((((mergeGPR 8 (v1b11ea p) (mergeGPR 8 (v1b11e2 p) (((mergeGPR 8 (v1b11d6 p) (v1b110c p)).setWidth 32 : BitVec 32).setWidth 64))).setWidth 8).setWidth 32 : BitVec 32).setWidth 64),
       .gpr 9 ((v1b12f0 p).1),
       .gpr 15 (v1b127f p),
       .gpr 12 (v1b1305 p),
       .mem (fr.rsp - 0x48) 64 ((v1b1175 p).1),
       .mem (fr.rsp - 0x50) 64 (mergeGPR 8 (v1b11a3 p) (v1b10e4 p)),
       .mem (fr.rsp - 0x40) 64 ((v1b11b8 p).1),
       .mem (fr.rsp - 0x68) 64 ((v1b11c8 p).1),
       .mem (fr.rsp - 0x58) 64 (mergeGPR 8 (v1b11d6 p) (v1b110c p)),
       .mem (fr.rsp - 0x60) 8 ((mergeGPR 8 (v1b11e2 p) (((mergeGPR 8 (v1b11d6 p) (v1b110c p)).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8),
       .mem (fr.rsp - 0x38) 64 ((((if !((v1b120f p).2.CF) then 1 else 0 : BitVec 8)).setWidth 32 : BitVec 32).setWidth 64),
       .mem (fr.rsp - 0x70) 64 (v1b12d7 p)]
  | .stage11 =>
      [.gpr 1 ((v1b116e p).1),
       .gpr 8 ((v1b12c2 p).1),
       .gpr 0 (v1b128c p),
       .gpr 3 (v1b1333 p),
       .gpr 10 ((v1b131e p).1),
       .gpr 14 ((((mergeGPR 8 (v1b11ea p) (mergeGPR 8 (v1b11e2 p) (((mergeGPR 8 (v1b11d6 p) (v1b110c p)).setWidth 32 : BitVec 32).setWidth 64))).setWidth 8).setWidth 32 : BitVec 32).setWidth 64),
       .gpr 9 ((v1b12f0 p).1),
       .mem (fr.rsp - 0x48) 64 ((v1b1175 p).1),
       .mem (fr.rsp - 0x50) 64 (mergeGPR 8 (v1b11a3 p) (v1b10e4 p)),
       .mem (fr.rsp - 0x40) 64 ((v1b11b8 p).1),
       .mem (fr.rsp - 0x68) 64 ((v1b11c8 p).1),
       .mem (fr.rsp - 0x58) 64 (mergeGPR 8 (v1b11d6 p) (v1b110c p)),
       .mem (fr.rsp - 0x60) 8 ((mergeGPR 8 (v1b11e2 p) (((mergeGPR 8 (v1b11d6 p) (v1b110c p)).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8),
       .mem (fr.rsp - 0x38) 64 ((((if !((v1b120f p).2.CF) then 1 else 0 : BitVec 8)).setWidth 32 : BitVec 32).setWidth 64),
       .mem (fr.rsp - 0x70) 64 (v1b1305 p)]
  | .stage12 =>
      [.gpr 8 ((v1b12c2 p).1),
       .gpr 0 (v1b128c p),
       .gpr 3 ((v1b137a p).1),
       .gpr 10 ((v1b131e p).1),
       .gpr 9 ((v1b12f0 p).1),
       .mem (fr.rsp - 0x48) 64 ((v1b1175 p).1),
       .mem (fr.rsp - 0x50) 64 (mergeGPR 8 (v1b11a3 p) (v1b10e4 p)),
       .mem (fr.rsp - 0x40) 64 ((v1b11b8 p).1),
       .mem (fr.rsp - 0x68) 64 ((v1b11c8 p).1),
       .mem (fr.rsp - 0x58) 64 (mergeGPR 8 (v1b11d6 p) (v1b110c p)),
       .mem (fr.rsp - 0x60) 8 ((mergeGPR 8 (v1b11e2 p) (((mergeGPR 8 (v1b11d6 p) (v1b110c p)).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8),
       .mem (fr.rsp - 0x38) 64 ((((if !((v1b120f p).2.CF) then 1 else 0 : BitVec 8)).setWidth 32 : BitVec 32).setWidth 64),
       .mem (fr.rsp - 0x70) 64 (v1b1383 p)]
  | .stage13 =>
      [.gpr 1 (((if decide ((v1b1383 p : BitVec 64) = (0)) then (((0 : BitVec 32).setWidth 64).setWidth 32) else (((((mergeGPR 8 (v1b1393 p) ((((mergeGPR 8 (v1b11e2 p) (((mergeGPR 8 (v1b11d6 p) (v1b110c p)).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8).setWidth 32 : BitVec 32).setWidth 64).setWidth 32)) : BitVec 32).setWidth 64),
       .gpr 8 ((v1b12c2 p).1),
       .gpr 0 (v1b128c p),
       .gpr 3 ((v1b137a p).1),
       .gpr 10 ((v1b131e p).1),
       .gpr 9 ((v1b12f0 p).1),
       .gpr 13 ((0 : BitVec 32).setWidth 64),
       .mem (fr.rsp - 0x48) 64 ((v1b1175 p).1),
       .mem (fr.rsp - 0x50) 64 (mergeGPR 8 (v1b11a3 p) (v1b10e4 p)),
       .mem (fr.rsp - 0x40) 64 ((v1b11b8 p).1),
       .mem (fr.rsp - 0x68) 64 ((v1b11c8 p).1),
       .mem (fr.rsp - 0x58) 64 (mergeGPR 8 (v1b11d6 p) (v1b110c p)),
       .mem (fr.rsp - 0x60) 8 ((mergeGPR 8 (v1b11e2 p) (((mergeGPR 8 (v1b11d6 p) (v1b110c p)).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8),
       .mem (fr.rsp - 0x38) 64 ((((if !((v1b120f p).2.CF) then 1 else 0 : BitVec 8)).setWidth 32 : BitVec 32).setWidth 64),
       .mem (fr.rsp - 0x70) 64 (v1b1383 p)]
  | .stage14 =>
      [.gpr 2 ((v1b13d7 p).1),
       .gpr 1 (((if decide ((v1b1383 p : BitVec 64) = (0)) then (((0 : BitVec 32).setWidth 64).setWidth 32) else (((((mergeGPR 8 (v1b1393 p) ((((mergeGPR 8 (v1b11e2 p) (((mergeGPR 8 (v1b11d6 p) (v1b110c p)).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8).setWidth 32 : BitVec 32).setWidth 64).setWidth 32)) : BitVec 32).setWidth 64),
       .gpr 8 ((v1b12c2 p).1),
       .gpr 11 ((v1b13bd p).1),
       .gpr 0 (v1b128c p),
       .gpr 3 ((v1b137a p).1),
       .gpr 10 ((v1b131e p).1),
       .gpr 14 ((v1b13b4 p).1),
       .gpr 9 ((v1b12f0 p).1),
       .gpr 13 ((v1b13c0 p).1),
       .gpr 12 (v1b13ab p),
       .mem (fr.rsp - 0x48) 64 ((v1b1175 p).1),
       .mem (fr.rsp - 0x50) 64 (mergeGPR 8 (v1b11a3 p) (v1b10e4 p)),
       .mem (fr.rsp - 0x40) 64 ((v1b11b8 p).1),
       .mem (fr.rsp - 0x68) 64 ((v1b11c8 p).1),
       .mem (fr.rsp - 0x58) 64 (mergeGPR 8 (v1b11d6 p) (v1b110c p)),
       .mem (fr.rsp - 0x60) 8 ((mergeGPR 8 (v1b11e2 p) (((mergeGPR 8 (v1b11d6 p) (v1b110c p)).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8),
       .mem (fr.rsp - 0x38) 64 ((((if !((v1b120f p).2.CF) then 1 else 0 : BitVec 8)).setWidth 32 : BitVec 32).setWidth 64),
       .mem (fr.rsp - 0x70) 8 ((if !((v1b13c0 p).2.CF) then 1 else 0 : BitVec 8))]
  | .stage15 =>
      [.gpr 6 (v1b13ed p),
       .gpr 2 ((v1b13d7 p).1),
       .gpr 1 (((if decide ((v1b1383 p : BitVec 64) = (0)) then (((0 : BitVec 32).setWidth 64).setWidth 32) else (((((mergeGPR 8 (v1b1393 p) ((((mergeGPR 8 (v1b11e2 p) (((mergeGPR 8 (v1b11d6 p) (v1b110c p)).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8).setWidth 32 : BitVec 32).setWidth 64).setWidth 32)) : BitVec 32).setWidth 64),
       .gpr 11 ((v1b13bd p).1),
       .gpr 0 (v1b1400 p),
       .gpr 3 ((v1b137a p).1),
       .gpr 10 ((v1b131e p).1),
       .gpr 9 ((v1b12f0 p).1),
       .gpr 13 ((v1b13c0 p).1),
       .mem (fr.rsp - 0x48) 64 ((v1b1175 p).1),
       .mem (fr.rsp - 0x50) 64 (mergeGPR 8 (v1b11a3 p) (v1b10e4 p)),
       .mem (fr.rsp - 0x40) 64 ((v1b11b8 p).1),
       .mem (fr.rsp - 0x68) 64 ((v1b11c8 p).1),
       .mem (fr.rsp - 0x58) 64 (mergeGPR 8 (v1b11d6 p) (v1b110c p)),
       .mem (fr.rsp - 0x60) 8 ((mergeGPR 8 (v1b11e2 p) (((mergeGPR 8 (v1b11d6 p) (v1b110c p)).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8),
       .mem (fr.rsp - 0x38) 64 ((((if !((v1b120f p).2.CF) then 1 else 0 : BitVec 8)).setWidth 32 : BitVec 32).setWidth 64),
       .mem (fr.rsp - 0x70) 8 ((((if decide ((v1b1383 p : BitVec 64) = (0)) then (((0 : BitVec 32).setWidth 64).setWidth 32) else (((((mergeGPR 8 (v1b1393 p) ((((mergeGPR 8 (v1b11e2 p) (((mergeGPR 8 (v1b11d6 p) (v1b110c p)).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8).setWidth 32 : BitVec 32).setWidth 64).setWidth 32)) : BitVec 32).setWidth 64).setWidth 8)]
  | .stage16 =>
      [.gpr 6 (v1b13ed p),
       .gpr 1 (((if decide ((v1b1383 p : BitVec 64) = (0)) then (((0 : BitVec 32).setWidth 64).setWidth 32) else (((((mergeGPR 8 (v1b1393 p) ((((mergeGPR 8 (v1b11e2 p) (((mergeGPR 8 (v1b11d6 p) (v1b110c p)).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8).setWidth 32 : BitVec 32).setWidth 64).setWidth 32)) : BitVec 32).setWidth 64),
       .gpr 8 (v1b1414 p),
       .gpr 0 (v1b1400 p),
       .gpr 10 (v1b143f p),
       .gpr 9 (v1b1428 p),
       .mem (fr.rsp - 0x48) 64 ((v1b1175 p).1),
       .mem (fr.rsp - 0x50) 64 (mergeGPR 8 (v1b11a3 p) (v1b10e4 p)),
       .mem (fr.rsp - 0x40) 64 ((v1b11b8 p).1),
       .mem (fr.rsp - 0x68) 64 ((v1b11c8 p).1),
       .mem (fr.rsp - 0x58) 64 (mergeGPR 8 (v1b11d6 p) (v1b110c p)),
       .mem (fr.rsp - 0x60) 8 ((mergeGPR 8 (v1b11e2 p) (((mergeGPR 8 (v1b11d6 p) (v1b110c p)).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8),
       .mem (fr.rsp - 0x38) 64 ((((if !((v1b120f p).2.CF) then 1 else 0 : BitVec 8)).setWidth 32 : BitVec 32).setWidth 64),
       .mem (fr.rsp - 0x70) 8 ((((if decide ((v1b1383 p : BitVec 64) = (0)) then (((0 : BitVec 32).setWidth 64).setWidth 32) else (((((mergeGPR 8 (v1b1393 p) ((((mergeGPR 8 (v1b11e2 p) (((mergeGPR 8 (v1b11d6 p) (v1b110c p)).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8).setWidth 32 : BitVec 32).setWidth 64).setWidth 32)) : BitVec 32).setWidth 64).setWidth 8)]
  | .stage17 =>
      [.gpr 6 (v1b13ed p),
       .gpr 2 (mergeGPR 8 (v1b1447 p) (mergeGPR 8 (v1b11d6 p) (v1b110c p))),
       .gpr 1 (mergeGPR 8 (v1b144c p) (mergeGPR 8 (v1b1449 p) (((if decide ((v1b1383 p : BitVec 64) = (0)) then (((0 : BitVec 32).setWidth 64).setWidth 32) else (((((mergeGPR 8 (v1b1393 p) ((((mergeGPR 8 (v1b11e2 p) (((mergeGPR 8 (v1b11d6 p) (v1b110c p)).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8).setWidth 32 : BitVec 32).setWidth 64).setWidth 32)) : BitVec 32).setWidth 64))),
       .gpr 8 (v1b1414 p),
       .gpr 0 (v1b1400 p),
       .gpr 10 (v1b143f p),
       .gpr 9 (v1b1428 p),
       .mem (fr.rsp - 0x48) 64 ((v1b1175 p).1),
       .mem (fr.rsp - 0x50) 64 (mergeGPR 8 (v1b11a3 p) (v1b10e4 p)),
       .mem (fr.rsp - 0x40) 64 ((v1b11b8 p).1),
       .mem (fr.rsp - 0x68) 64 ((v1b11c8 p).1),
       .mem (fr.rsp - 0x58) 64 (mergeGPR 8 (v1b11d6 p) (v1b110c p)),
       .mem (fr.rsp - 0x60) 8 ((mergeGPR 8 (v1b11e2 p) (((mergeGPR 8 (v1b11d6 p) (v1b110c p)).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8),
       .mem (fr.rsp - 0x38) 64 ((((if !((v1b120f p).2.CF) then 1 else 0 : BitVec 8)).setWidth 32 : BitVec 32).setWidth 64),
       .mem (fr.rsp - 0x70) 8 ((((if decide ((v1b1383 p : BitVec 64) = (0)) then (((0 : BitVec 32).setWidth 64).setWidth 32) else (((((mergeGPR 8 (v1b1393 p) ((((mergeGPR 8 (v1b11e2 p) (((mergeGPR 8 (v1b11d6 p) (v1b110c p)).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8).setWidth 32 : BitVec 32).setWidth 64).setWidth 32)) : BitVec 32).setWidth 64).setWidth 8)]

def dialect : Dialect Support.Op Unit Inputs where
  eval op := nomatch op
  truth _ := false

@[refine_layout] def outputRegion (fr : Activation) : MemoryRegion := ⟨fr.rdi.toNat, 41⟩

def layout (fr : Activation) (controls : RamState) : Layout program dialect Machine.lifted Unit where
  start := start
  Params _ := Inputs
  args _ _ := #v[]
  store _ p := p
  atoms l _ p := Machine.LinearCombination.frameAt (start l) fr ++ commonAtoms fr controls p ++ coreAtoms l fr p
  Result := Inputs
  output p := ⟨#v[], none, p⟩
  done _ p := Machine.LinearCombination.doneAt fr ++
    [.words fr.rdi 64 (resultWords p), .mem (fr.rdi + 40) 8 (resultSign p), .readable fr.rdi 41,
      .reg 39 ⟨32, controls.MXCSR⟩, .reg 51 ⟨16, controls.FP87_Control⟩]
  retAddr _ := fr.ret
  original _ := fr.original
  regions _ := [fr.region, outputRegion fr]

end P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination
