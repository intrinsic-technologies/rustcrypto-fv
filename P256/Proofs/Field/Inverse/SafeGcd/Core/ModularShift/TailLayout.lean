import P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Defs
import P256.Proofs.Field.Inverse.SafeGcd.Core.LinearShift.Tail

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Tail

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

inductive Label where
  | stage0 | stage1 | stage2 | stage3 | stage4 | stage5 | stage6 | stage7 | stage8 | stage9 | stage10 | stage11 | stage12 | stage13 | stage14 | stage15 | stage16 | stage17 | stage18 | stage19 | stage20 | stage21 | stage22 | stage23

@[refine_layout] def start : Label → Machine.Label
  | .stage0 => .l1171be
  | .stage1 => .l1171d2
  | .stage2 => .l117200
  | .stage3 => .l117244
  | .stage4 => .l117256
  | .stage5 => .l117287
  | .stage6 => .l1172b7
  | .stage7 => .l1172e7
  | .stage8 => .l11731a
  | .stage9 => .l11734e
  | .stage10 => .l117393
  | .stage11 => .l1173d1
  | .stage12 => .l1173e1
  | .stage13 => .l117405
  | .stage14 => .l117423
  | .stage15 => .l117457
  | .stage16 => .l117477
  | .stage17 => .l1174a0
  | .stage18 => .l1174d8
  | .stage19 => .l11750f
  | .stage20 => .l11754e
  | .stage21 => .l11758e
  | .stage22 => .l1175c8
  | .stage23 => .l1175f2

def program : Program Support.Op Label (fun _ => 0) 0 where
  blocks
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
  | .stage17 => .terminate (.br ⟨.stage18, #v[]⟩)
  | .stage18 => .terminate (.br ⟨.stage19, #v[]⟩)
  | .stage19 => .terminate (.br ⟨.stage20, #v[]⟩)
  | .stage20 => .terminate (.br ⟨.stage21, #v[]⟩)
  | .stage21 => .terminate (.br ⟨.stage22, #v[]⟩)
  | .stage22 => .terminate (.br ⟨.stage23, #v[]⟩)
  | .stage23 => .terminate (.ret #v[])

@[refine_layout] def frame (fr : Activation) (controls : RamState) (p : Inputs) : List Atom :=
  [.gpr 4 (fr.rsp - 0xa8), .reg 22 ⟨1, 0⟩,
   .mem (fr.rsp - 8) 64 fr.rbp, .mem (fr.rsp - 16) 64 fr.r15,
   .mem (fr.rsp - 24) 64 fr.r14, .mem (fr.rsp - 32) 64 fr.r13,
   .mem (fr.rsp - 40) 64 fr.r12, .mem (fr.rsp - 48) 64 fr.rbx,
   .mem fr.rsp 64 fr.ret, .readable fr.rsp 8, .fact (fr.ret.toNat < 2^32),
   .writable (fr.rsp - 0x120) 0x120, .fact (fr.low.toNat + 0x120 ≤ fr.rsp.toNat),
   .fact (fr.rsp.toNat % 16 = 8)] ++ bounds p ++ outputAtoms fr controls ++ modulusAtoms fr p

set_option maxHeartbeats 2000000 in
@[refine_layout] def coreAtoms (l : Label) (fr : Activation) (p : Inputs) : List Atom :=
  match l with
  | .stage0 =>
      [.gpr 5 (p.shift.setWidth 64),
       .gpr 3 (fr.rdi),
       .mem (fr.rsp - 0x98) 64 ((LinearCombination.resultWords p.linear)[0]),
       .mem (fr.rsp - 0x90) 64 ((LinearCombination.resultWords p.linear)[1]),
       .mem (fr.rsp - 0x88) 64 ((LinearCombination.resultWords p.linear)[2]),
       .mem (fr.rsp - 0x80) 64 ((LinearCombination.resultWords p.linear)[3]),
       .mem (fr.rsp - 0x78) 64 ((LinearCombination.resultWords p.linear)[4]),
       .mem (fr.rsp - 0x70) 8 (LinearCombination.resultSign p.linear)]
  | .stage1 =>
      [.gpr 3 (fr.rdi),
       .gpr 1 ((v1b1597 p : BitVec 32).setWidth 64),
       .mem (fr.rsp - 0x98) 64 ((LinearCombination.resultWords p.linear)[0]),
       .mem (fr.rsp - 0x90) 64 ((LinearCombination.resultWords p.linear)[1]),
       .mem (fr.rsp - 0x88) 64 ((LinearCombination.resultWords p.linear)[2]),
       .mem (fr.rsp - 0x80) 64 ((LinearCombination.resultWords p.linear)[3]),
       .mem (fr.rsp - 0x78) 64 ((LinearCombination.resultWords p.linear)[4]),
       .mem (fr.rsp - 0x70) 8 (LinearCombination.resultSign p.linear),
       .mem (fr.rsp - 0x64) 32 ((p.shift.setWidth 64).setWidth 32)]
  | .stage2 =>
      [.gpr 3 ((LinearCombination.resultWords p.linear)[2]),
       .gpr 1 ((v1b1597 p : BitVec 32).setWidth 64),
       .gpr 7 (p.modulusPtr),
       .gpr 6 ((LinearCombination.resultWords p.linear)[0]),
       .gpr 9 (v1b15c3 p),
       .gpr 8 ((LinearCombination.resultWords p.linear)[1]),
       .mem (fr.rsp - 0x98) 64 ((LinearCombination.resultWords p.linear)[0]),
       .mem (fr.rsp - 0x90) 64 ((LinearCombination.resultWords p.linear)[1]),
       .mem (fr.rsp - 0x88) 64 ((LinearCombination.resultWords p.linear)[2]),
       .mem (fr.rsp - 0x80) 64 ((LinearCombination.resultWords p.linear)[3]),
       .mem (fr.rsp - 0x78) 64 ((LinearCombination.resultWords p.linear)[4]),
       .mem (fr.rsp - 0x70) 8 (LinearCombination.resultSign p.linear),
       .mem (fr.rsp - 0x64) 32 ((p.shift.setWidth 64).setWidth 32),
       .mem (fr.rsp - 0x38) 64 (fr.rdi)]
  | .stage3 =>
      [.gpr 3 ((LinearCombination.resultWords p.linear)[2]),
       .gpr 12 ((v1b15ed p).2),
       .gpr 13 ((v1b15ff p).2),
       .gpr 14 ((v1b15dc p).1),
       .gpr 15 ((v1b15dc p).2),
       .gpr 1 ((v1b1597 p : BitVec 32).setWidth 64),
       .gpr 6 ((LinearCombination.resultWords p.linear)[0]),
       .gpr 8 ((LinearCombination.resultWords p.linear)[1]),
       .gpr 0 ((v1b1611 p).1),
       .gpr 10 ((v1b15ff p).1),
       .gpr 2 ((v1b1611 p).2),
       .gpr 11 ((v1b15ed p).1),
       .mem (fr.rsp - 0x98) 64 ((LinearCombination.resultWords p.linear)[0]),
       .mem (fr.rsp - 0x90) 64 ((LinearCombination.resultWords p.linear)[1]),
       .mem (fr.rsp - 0x88) 64 ((LinearCombination.resultWords p.linear)[2]),
       .mem (fr.rsp - 0x80) 64 ((LinearCombination.resultWords p.linear)[3]),
       .mem (fr.rsp - 0x78) 64 ((LinearCombination.resultWords p.linear)[4]),
       .mem (fr.rsp - 0x70) 8 (LinearCombination.resultSign p.linear),
       .mem (fr.rsp - 0x64) 32 ((p.shift.setWidth 64).setWidth 32),
       .mem (fr.rsp - 0x38) 64 (fr.rdi),
       .mem (fr.rsp - 0x58) 64 (p.modulus[0]),
       .mem (fr.rsp - 0x50) 64 (p.modulus[1]),
       .mem (fr.rsp - 0x48) 64 (p.modulus[2]),
       .mem (fr.rsp - 0x40) 64 (p.modulus[3])]
  | .stage4 =>
      [.gpr 3 ((LinearCombination.resultWords p.linear)[2]),
       .gpr 12 ((v1b15ed p).2),
       .gpr 13 ((v1b15ff p).2),
       .gpr 14 ((v1b15dc p).1),
       .gpr 1 ((v1b1597 p : BitVec 32).setWidth 64),
       .gpr 7 ((LinearCombination.resultWords p.linear)[3]),
       .gpr 6 ((LinearCombination.resultWords p.linear)[0]),
       .gpr 8 ((LinearCombination.resultWords p.linear)[1]),
       .gpr 0 ((v1b161f p).1),
       .gpr 10 ((v1b161c p).1),
       .gpr 2 ((v1b1622 p).1),
       .gpr 11 ((v1b1614 p).1),
       .mem (fr.rsp - 0x98) 64 ((LinearCombination.resultWords p.linear)[0]),
       .mem (fr.rsp - 0x90) 64 ((LinearCombination.resultWords p.linear)[1]),
       .mem (fr.rsp - 0x88) 64 ((LinearCombination.resultWords p.linear)[2]),
       .mem (fr.rsp - 0x80) 64 ((LinearCombination.resultWords p.linear)[3]),
       .mem (fr.rsp - 0x78) 64 ((LinearCombination.resultWords p.linear)[4]),
       .mem (fr.rsp - 0x70) 8 (LinearCombination.resultSign p.linear),
       .mem (fr.rsp - 0x64) 32 ((p.shift.setWidth 64).setWidth 32),
       .mem (fr.rsp - 0x38) 64 (fr.rdi),
       .mem (fr.rsp - 0x58) 64 (p.modulus[0]),
       .mem (fr.rsp - 0x50) 64 (p.modulus[1]),
       .mem (fr.rsp - 0x48) 64 (p.modulus[2]),
       .mem (fr.rsp - 0x40) 64 (p.modulus[3])]
  | .stage5 =>
      [.gpr 5 (v1b1629 p),
       .gpr 3 ((LinearCombination.resultWords p.linear)[2]),
       .gpr 12 ((v1b15ed p).2),
       .gpr 13 ((v1b15ff p).2),
       .gpr 14 ((LinearCombination.resultWords p.linear)[4]),
       .gpr 1 ((v1b1597 p : BitVec 32).setWidth 64),
       .gpr 7 ((LinearCombination.resultWords p.linear)[3]),
       .gpr 8 ((LinearCombination.resultWords p.linear)[1]),
       .gpr 0 ((v1b161f p).1),
       .gpr 10 ((v1b161c p).1),
       .gpr 2 ((v1b1622 p).1),
       .gpr 11 ((v1b1614 p).1),
       .mem (fr.rsp - 0x90) 64 ((LinearCombination.resultWords p.linear)[1]),
       .mem (fr.rsp - 0x88) 64 ((LinearCombination.resultWords p.linear)[2]),
       .mem (fr.rsp - 0x80) 64 ((LinearCombination.resultWords p.linear)[3]),
       .mem (fr.rsp - 0x78) 64 ((LinearCombination.resultWords p.linear)[4]),
       .mem (fr.rsp - 0x70) 8 (LinearCombination.resultSign p.linear),
       .mem (fr.rsp - 0x64) 32 ((p.shift.setWidth 64).setWidth 32),
       .mem (fr.rsp - 0x38) 64 (fr.rdi),
       .mem (fr.rsp - 0x58) 64 (p.modulus[0]),
       .mem (fr.rsp - 0x50) 64 (p.modulus[1]),
       .mem (fr.rsp - 0x48) 64 (p.modulus[2]),
       .mem (fr.rsp - 0x40) 64 (p.modulus[3]),
       .mem (fr.rsp - 0x99) 8 ((((LinearCombination.resultSign p.linear).setWidth 32 : BitVec 32).setWidth 64).setWidth 8),
       .mem (fr.rsp - 0x98) 64 (v1b164e p)]
  | .stage6 =>
      [.gpr 5 (v1b1629 p),
       .gpr 3 ((LinearCombination.resultWords p.linear)[2]),
       .gpr 12 ((v1b166e p).1),
       .gpr 13 ((v1b15ff p).2),
       .gpr 14 ((LinearCombination.resultWords p.linear)[4]),
       .gpr 1 ((v1b1597 p : BitVec 32).setWidth 64),
       .gpr 7 ((LinearCombination.resultWords p.linear)[3]),
       .gpr 8 (v1b1683 p),
       .gpr 0 ((v1b161f p).1),
       .gpr 10 ((v1b161c p).1),
       .gpr 2 ((v1b1622 p).1),
       .gpr 11 ((v1b1614 p).1),
       .mem (fr.rsp - 0x90) 64 ((LinearCombination.resultWords p.linear)[1]),
       .mem (fr.rsp - 0x88) 64 ((LinearCombination.resultWords p.linear)[2]),
       .mem (fr.rsp - 0x80) 64 ((LinearCombination.resultWords p.linear)[3]),
       .mem (fr.rsp - 0x78) 64 ((LinearCombination.resultWords p.linear)[4]),
       .mem (fr.rsp - 0x70) 8 (LinearCombination.resultSign p.linear),
       .mem (fr.rsp - 0x64) 32 ((p.shift.setWidth 64).setWidth 32),
       .mem (fr.rsp - 0x38) 64 (fr.rdi),
       .mem (fr.rsp - 0x58) 64 (p.modulus[0]),
       .mem (fr.rsp - 0x50) 64 (p.modulus[1]),
       .mem (fr.rsp - 0x48) 64 (p.modulus[2]),
       .mem (fr.rsp - 0x40) 64 (p.modulus[3]),
       .mem (fr.rsp - 0x99) 8 ((((LinearCombination.resultSign p.linear).setWidth 32 : BitVec 32).setWidth 64).setWidth 8),
       .mem (fr.rsp - 0x98) 64 (v1b164e p)]
  | .stage7 =>
      [.gpr 5 (v1b1629 p),
       .gpr 3 (v1b16b3 p),
       .gpr 12 ((v1b166e p).1),
       .gpr 13 ((v1b15ff p).2),
       .gpr 14 ((LinearCombination.resultWords p.linear)[4]),
       .gpr 1 ((v1b1597 p : BitVec 32).setWidth 64),
       .gpr 7 ((LinearCombination.resultWords p.linear)[3]),
       .gpr 0 ((v1b161f p).1),
       .gpr 10 ((v1b161c p).1),
       .gpr 2 ((v1b1622 p).1),
       .gpr 11 ((v1b169e p).1),
       .mem (fr.rsp - 0x90) 64 ((LinearCombination.resultWords p.linear)[1]),
       .mem (fr.rsp - 0x88) 64 ((LinearCombination.resultWords p.linear)[2]),
       .mem (fr.rsp - 0x80) 64 ((LinearCombination.resultWords p.linear)[3]),
       .mem (fr.rsp - 0x78) 64 ((LinearCombination.resultWords p.linear)[4]),
       .mem (fr.rsp - 0x70) 8 (LinearCombination.resultSign p.linear),
       .mem (fr.rsp - 0x64) 32 ((p.shift.setWidth 64).setWidth 32),
       .mem (fr.rsp - 0x38) 64 (fr.rdi),
       .mem (fr.rsp - 0x58) 64 (p.modulus[0]),
       .mem (fr.rsp - 0x50) 64 (p.modulus[1]),
       .mem (fr.rsp - 0x48) 64 (p.modulus[2]),
       .mem (fr.rsp - 0x40) 64 (p.modulus[3]),
       .mem (fr.rsp - 0x99) 8 ((((LinearCombination.resultSign p.linear).setWidth 32 : BitVec 32).setWidth 64).setWidth 8),
       .mem (fr.rsp - 0x98) 64 (v1b1683 p)]
  | .stage8 =>
      [.gpr 5 (v1b1629 p),
       .gpr 12 ((v1b166e p).1),
       .gpr 13 ((v1b16ce p).1),
       .gpr 14 ((LinearCombination.resultWords p.linear)[4]),
       .gpr 1 ((v1b1597 p : BitVec 32).setWidth 64),
       .gpr 7 (v1b16e6 p),
       .gpr 0 ((v1b161f p).1),
       .gpr 10 (((0 : BitVec 32) : BitVec 32).setWidth 64),
       .gpr 2 ((v1b1622 p).1),
       .gpr 11 ((v1b169e p).1),
       .mem (fr.rsp - 0x90) 64 ((LinearCombination.resultWords p.linear)[1]),
       .mem (fr.rsp - 0x88) 64 ((LinearCombination.resultWords p.linear)[2]),
       .mem (fr.rsp - 0x80) 64 ((LinearCombination.resultWords p.linear)[3]),
       .mem (fr.rsp - 0x78) 64 ((LinearCombination.resultWords p.linear)[4]),
       .mem (fr.rsp - 0x70) 8 (LinearCombination.resultSign p.linear),
       .mem (fr.rsp - 0x64) 32 ((p.shift.setWidth 64).setWidth 32),
       .mem (fr.rsp - 0x38) 64 (fr.rdi),
       .mem (fr.rsp - 0x58) 64 (p.modulus[0]),
       .mem (fr.rsp - 0x50) 64 (p.modulus[1]),
       .mem (fr.rsp - 0x48) 64 (p.modulus[2]),
       .mem (fr.rsp - 0x40) 64 (p.modulus[3]),
       .mem (fr.rsp - 0x99) 8 ((((LinearCombination.resultSign p.linear).setWidth 32 : BitVec 32).setWidth 64).setWidth 8),
       .mem (fr.rsp - 0x98) 64 (v1b16b3 p)]
  | .stage9 =>
      [.gpr 5 (v1b1629 p),
       .gpr 12 ((v1b166e p).1),
       .gpr 13 ((v1b16ce p).1),
       .gpr 1 ((v1b1597 p : BitVec 32).setWidth 64),
       .gpr 0 ((v1b170c p).1),
       .gpr 10 (((0 : BitVec 32) : BitVec 32).setWidth 64),
       .gpr 11 ((v1b169e p).1),
       .mem (fr.rsp - 0x90) 64 ((LinearCombination.resultWords p.linear)[1]),
       .mem (fr.rsp - 0x88) 64 ((LinearCombination.resultWords p.linear)[2]),
       .mem (fr.rsp - 0x80) 64 ((LinearCombination.resultWords p.linear)[3]),
       .mem (fr.rsp - 0x78) 64 ((LinearCombination.resultWords p.linear)[4]),
       .mem (fr.rsp - 0x70) 8 (LinearCombination.resultSign p.linear),
       .mem (fr.rsp - 0x64) 32 ((p.shift.setWidth 64).setWidth 32),
       .mem (fr.rsp - 0x38) 64 (fr.rdi),
       .mem (fr.rsp - 0x58) 64 (p.modulus[0]),
       .mem (fr.rsp - 0x50) 64 (p.modulus[1]),
       .mem (fr.rsp - 0x48) 64 (p.modulus[2]),
       .mem (fr.rsp - 0x40) 64 (p.modulus[3]),
       .mem (fr.rsp - 0x99) 8 ((((LinearCombination.resultSign p.linear).setWidth 32 : BitVec 32).setWidth 64).setWidth 8),
       .mem (fr.rsp - 0x98) 64 (v1b1715 p)]
  | .stage10 =>
      [.gpr 5 ((v1b173c p).1),
       .gpr 3 (v1b172b p),
       .gpr 12 ((v1b166e p).1),
       .gpr 13 ((v1b16ce p).1),
       .gpr 1 ((v1b1597 p : BitVec 32).setWidth 64),
       .gpr 6 ((((if !((v1b173f p).2.CF) then 1 else 0 : BitVec 8)).setWidth 32 : BitVec 32).setWidth 64),
       .gpr 8 ((v1b1734 p).1),
       .gpr 0 ((v1b170c p).1),
       .gpr 10 ((v1b173f p).1),
       .gpr 11 ((v1b169e p).1),
       .mem (fr.rsp - 0x90) 64 ((LinearCombination.resultWords p.linear)[1]),
       .mem (fr.rsp - 0x88) 64 ((LinearCombination.resultWords p.linear)[2]),
       .mem (fr.rsp - 0x80) 64 ((LinearCombination.resultWords p.linear)[3]),
       .mem (fr.rsp - 0x78) 64 ((LinearCombination.resultWords p.linear)[4]),
       .mem (fr.rsp - 0x70) 8 (LinearCombination.resultSign p.linear),
       .mem (fr.rsp - 0x64) 32 ((p.shift.setWidth 64).setWidth 32),
       .mem (fr.rsp - 0x38) 64 (fr.rdi),
       .mem (fr.rsp - 0x58) 64 (p.modulus[0]),
       .mem (fr.rsp - 0x50) 64 (p.modulus[1]),
       .mem (fr.rsp - 0x48) 64 (p.modulus[2]),
       .mem (fr.rsp - 0x40) 64 (p.modulus[3]),
       .mem (fr.rsp - 0x99) 8 ((((LinearCombination.resultSign p.linear).setWidth 32 : BitVec 32).setWidth 64).setWidth 8),
       .mem (fr.rsp - 0x60) 64 (v1b1629 p),
       .mem (fr.rsp - 0x98) 8 ((if !(decide ((v1b1715 p : BitVec 64) = 0)) then 1 else 0 : BitVec 8)),
       .reg 19 (Value.ofBool (decide ((v1b1715 p : BitVec 64) = 0)))]
  | .stage11 =>
      [.gpr 5 ((v1b173c p).1),
       .gpr 3 (v1b172b p),
       .gpr 12 ((v1b166e p).1),
       .gpr 13 ((v1b16ce p).1),
       .gpr 14 ((((if !(decide ((v1b1715 p : BitVec 64) = 0)) then 1 else 0 : BitVec 8)).setWidth 32 : BitVec 32).setWidth 64),
       .gpr 15 ((((if !(decide ((v1b1715 p : BitVec 64) = 0)) then 1 else 0 : BitVec 8)).setWidth 32 : BitVec 32).setWidth 64),
       .gpr 1 ((v1b1597 p : BitVec 32).setWidth 64),
       .gpr 7 ((((if !(decide ((v1b1715 p : BitVec 64) = 0)) then 1 else 0 : BitVec 8)).setWidth 32 : BitVec 32).setWidth 64),
       .gpr 6 ((((if !((v1b173f p).2.CF) then 1 else 0 : BitVec 8)).setWidth 32 : BitVec 32).setWidth 64),
       .low 9 8 ((mergeGPR 8 ((if !(decide ((v1b1715 p : BitVec 64) = 0)) then 1 else 0 : BitVec 8)) ((0 : BitVec 64))).setWidth 8),
       .gpr 8 ((v1b1734 p).1),
       .gpr 0 ((v1b170c p).1),
       .gpr 10 ((v1b173f p).1),
       .gpr 2 ((((if !(decide ((v1b1715 p : BitVec 64) = 0)) then 1 else 0 : BitVec 8)).setWidth 32 : BitVec 32).setWidth 64),
       .gpr 11 ((v1b169e p).1),
       .mem (fr.rsp - 0x90) 64 ((LinearCombination.resultWords p.linear)[1]),
       .mem (fr.rsp - 0x88) 64 ((LinearCombination.resultWords p.linear)[2]),
       .mem (fr.rsp - 0x80) 64 ((LinearCombination.resultWords p.linear)[3]),
       .mem (fr.rsp - 0x78) 64 ((LinearCombination.resultWords p.linear)[4]),
       .mem (fr.rsp - 0x70) 8 (LinearCombination.resultSign p.linear),
       .mem (fr.rsp - 0x64) 32 ((p.shift.setWidth 64).setWidth 32),
       .mem (fr.rsp - 0x38) 64 (fr.rdi),
       .mem (fr.rsp - 0x58) 64 (p.modulus[0]),
       .mem (fr.rsp - 0x50) 64 (p.modulus[1]),
       .mem (fr.rsp - 0x48) 64 (p.modulus[2]),
       .mem (fr.rsp - 0x40) 64 (p.modulus[3]),
       .mem (fr.rsp - 0x99) 8 ((((LinearCombination.resultSign p.linear).setWidth 32 : BitVec 32).setWidth 64).setWidth 8),
       .mem (fr.rsp - 0x60) 64 (v1b1629 p),
       .mem (fr.rsp - 0x98) 8 ((if !(decide ((v1b1715 p : BitVec 64) = 0)) then 1 else 0 : BitVec 8))]
  | .stage12 =>
      [.gpr 5 ((v1b173c p).1),
       .gpr 3 (v1b172b p),
       .gpr 12 ((v1b166e p).1),
       .gpr 13 ((v1b16ce p).1),
       .gpr 14 ((((if !(decide ((v1b1715 p : BitVec 64) = 0)) then 1 else 0 : BitVec 8)).setWidth 32 : BitVec 32).setWidth 64),
       .gpr 15 ((((if !(decide ((v1b1715 p : BitVec 64) = 0)) then 1 else 0 : BitVec 8)).setWidth 32 : BitVec 32).setWidth 64),
       .gpr 1 ((v1b1597 p : BitVec 32).setWidth 64),
       .gpr 7 ((((if !(decide ((v1b1715 p : BitVec 64) = 0)) then 1 else 0 : BitVec 8)).setWidth 32 : BitVec 32).setWidth 64),
       .gpr 6 ((((if !((v1b173f p).2.CF) then 1 else 0 : BitVec 8)).setWidth 32 : BitVec 32).setWidth 64),
       .low 9 8 ((mergeGPR 8 ((if !(decide ((v1b1715 p : BitVec 64) = 0)) then 1 else 0 : BitVec 8)) ((0 : BitVec 64))).setWidth 8),
       .gpr 8 ((v1b1734 p).1),
       .gpr 0 ((v1b170c p).1),
       .gpr 10 ((v1b173f p).1),
       .gpr 2 ((((if !(decide ((v1b1715 p : BitVec 64) = 0)) then 1 else 0 : BitVec 8)).setWidth 32 : BitVec 32).setWidth 64),
       .gpr 11 ((v1b169e p).1),
       .mem (fr.rsp - 0x90) 64 ((LinearCombination.resultWords p.linear)[1]),
       .mem (fr.rsp - 0x88) 64 ((LinearCombination.resultWords p.linear)[2]),
       .mem (fr.rsp - 0x80) 64 ((LinearCombination.resultWords p.linear)[3]),
       .mem (fr.rsp - 0x78) 64 ((LinearCombination.resultWords p.linear)[4]),
       .mem (fr.rsp - 0x70) 8 (LinearCombination.resultSign p.linear),
       .mem (fr.rsp - 0x64) 32 ((p.shift.setWidth 64).setWidth 32),
       .mem (fr.rsp - 0x38) 64 (fr.rdi),
       .mem (fr.rsp - 0x58) 64 (p.modulus[0]),
       .mem (fr.rsp - 0x50) 64 (p.modulus[1]),
       .mem (fr.rsp - 0x48) 64 (p.modulus[2]),
       .mem (fr.rsp - 0x40) 64 (p.modulus[3]),
       .mem (fr.rsp - 0x99) 8 ((((LinearCombination.resultSign p.linear).setWidth 32 : BitVec 32).setWidth 64).setWidth 8),
       .mem (fr.rsp - 0x60) 64 (v1b1629 p),
       .mem (fr.rsp - 0x98) 8 ((if !(decide ((v1b1715 p : BitVec 64) = 0)) then 1 else 0 : BitVec 8)),
       .mem (fr.rsp - 0x9a) 8 ((mergeGPR 8 ((if !(decide ((v1b1715 p : BitVec 64) = 0)) then 1 else 0 : BitVec 8)) ((0 : BitVec 64))).setWidth 8)]
  | .stage13 =>
      [.gpr 3 (v1b172b p),
       .gpr 14 (v1b17c6 p),
       .gpr 15 (v1b17d2 p),
       .gpr 1 ((v1b1597 p : BitVec 32).setWidth 64),
       .gpr 7 (v1b17ba p),
       .gpr 6 ((((if !((v1b173f p).2.CF) then 1 else 0 : BitVec 8)).setWidth 32 : BitVec 32).setWidth 64),
       .low 9 8 ((mergeGPR 8 ((if !(decide ((v1b1715 p : BitVec 64) = 0)) then 1 else 0 : BitVec 8)) ((0 : BitVec 64))).setWidth 8),
       .gpr 0 ((v1b170c p).1),
       .gpr 2 ((((if !(decide ((v1b1715 p : BitVec 64) = 0)) then 1 else 0 : BitVec 8)).setWidth 32 : BitVec 32).setWidth 64),
       .mem (fr.rsp - 0x90) 64 ((LinearCombination.resultWords p.linear)[1]),
       .mem (fr.rsp - 0x88) 64 ((LinearCombination.resultWords p.linear)[2]),
       .mem (fr.rsp - 0x80) 64 ((LinearCombination.resultWords p.linear)[3]),
       .mem (fr.rsp - 0x78) 64 ((LinearCombination.resultWords p.linear)[4]),
       .mem (fr.rsp - 0x70) 8 (LinearCombination.resultSign p.linear),
       .mem (fr.rsp - 0x64) 32 ((p.shift.setWidth 64).setWidth 32),
       .mem (fr.rsp - 0x38) 64 (fr.rdi),
       .mem (fr.rsp - 0x58) 64 (p.modulus[0]),
       .mem (fr.rsp - 0x50) 64 (p.modulus[1]),
       .mem (fr.rsp - 0x48) 64 (p.modulus[2]),
       .mem (fr.rsp - 0x40) 64 (p.modulus[3]),
       .mem (fr.rsp - 0x99) 8 ((((LinearCombination.resultSign p.linear).setWidth 32 : BitVec 32).setWidth 64).setWidth 8),
       .mem (fr.rsp - 0x60) 64 (v1b1629 p),
       .mem (fr.rsp - 0x98) 8 ((if !(decide ((v1b1715 p : BitVec 64) = 0)) then 1 else 0 : BitVec 8)),
       .mem (fr.rsp - 0x9a) 8 ((mergeGPR 8 ((if !(decide ((v1b1715 p : BitVec 64) = 0)) then 1 else 0 : BitVec 8)) ((0 : BitVec 64))).setWidth 8)]
  | .stage14 =>
      [.gpr 3 (v1b172b p),
       .gpr 13 (v1b17f0 p),
       .gpr 14 (v1b17c6 p),
       .gpr 15 (v1b17d2 p),
       .gpr 1 ((v1b1597 p : BitVec 32).setWidth 64),
       .gpr 7 (v1b17ba p),
       .low 9 8 ((mergeGPR 8 ((if !(decide ((v1b1715 p : BitVec 64) = 0)) then 1 else 0 : BitVec 8)) ((0 : BitVec 64))).setWidth 8),
       .gpr 2 ((((if !(decide ((v1b1715 p : BitVec 64) = 0)) then 1 else 0 : BitVec 8)).setWidth 32 : BitVec 32).setWidth 64),
       .mem (fr.rsp - 0x90) 64 ((LinearCombination.resultWords p.linear)[1]),
       .mem (fr.rsp - 0x88) 64 ((LinearCombination.resultWords p.linear)[2]),
       .mem (fr.rsp - 0x80) 64 ((LinearCombination.resultWords p.linear)[3]),
       .mem (fr.rsp - 0x78) 64 ((LinearCombination.resultWords p.linear)[4]),
       .mem (fr.rsp - 0x70) 8 (LinearCombination.resultSign p.linear),
       .mem (fr.rsp - 0x64) 32 ((p.shift.setWidth 64).setWidth 32),
       .mem (fr.rsp - 0x38) 64 (fr.rdi),
       .mem (fr.rsp - 0x58) 64 (p.modulus[0]),
       .mem (fr.rsp - 0x50) 64 (p.modulus[1]),
       .mem (fr.rsp - 0x48) 64 (p.modulus[2]),
       .mem (fr.rsp - 0x40) 64 (p.modulus[3]),
       .mem (fr.rsp - 0x99) 8 ((((LinearCombination.resultSign p.linear).setWidth 32 : BitVec 32).setWidth 64).setWidth 8),
       .mem (fr.rsp - 0x60) 64 (v1b1629 p),
       .mem (fr.rsp - 0x98) 8 ((if !(decide ((v1b1715 p : BitVec 64) = 0)) then 1 else 0 : BitVec 8)),
       .mem (fr.rsp - 0x9a) 8 ((mergeGPR 8 ((if !(decide ((v1b1715 p : BitVec 64) = 0)) then 1 else 0 : BitVec 8)) ((0 : BitVec 64))).setWidth 8)]
  | .stage15 =>
      [.gpr 5 (((p.shift.setWidth 64).setWidth 32 : BitVec 32).setWidth 64),
       .gpr 12 (v1b181e p),
       .gpr 13 (v1b17f0 p),
       .gpr 14 (v1b17c6 p),
       .gpr 15 (v1b17d2 p),
       .gpr 7 (v1b1816 p),
       .low 9 8 ((mergeGPR 8 ((if !(decide ((v1b1715 p : BitVec 64) = 0)) then 1 else 0 : BitVec 8)) ((0 : BitVec 64))).setWidth 8),
       .gpr 0 ((((v1b1597 p : BitVec 32).setWidth 64).setWidth 32 : BitVec 32).setWidth 64),
       .gpr 10 (v1b17fa p),
       .gpr 2 (v1b1824 p),
       .gpr 11 (v1b1811 p),
       .mem (fr.rsp - 0x90) 64 ((LinearCombination.resultWords p.linear)[1]),
       .mem (fr.rsp - 0x88) 64 ((LinearCombination.resultWords p.linear)[2]),
       .mem (fr.rsp - 0x80) 64 ((LinearCombination.resultWords p.linear)[3]),
       .mem (fr.rsp - 0x78) 64 ((LinearCombination.resultWords p.linear)[4]),
       .mem (fr.rsp - 0x70) 8 (LinearCombination.resultSign p.linear),
       .mem (fr.rsp - 0x64) 32 ((p.shift.setWidth 64).setWidth 32),
       .mem (fr.rsp - 0x38) 64 (fr.rdi),
       .mem (fr.rsp - 0x58) 64 (p.modulus[0]),
       .mem (fr.rsp - 0x50) 64 (p.modulus[1]),
       .mem (fr.rsp - 0x48) 64 (p.modulus[2]),
       .mem (fr.rsp - 0x40) 64 (p.modulus[3]),
       .mem (fr.rsp - 0x99) 8 ((((LinearCombination.resultSign p.linear).setWidth 32 : BitVec 32).setWidth 64).setWidth 8),
       .mem (fr.rsp - 0x60) 64 (v1b1629 p),
       .mem (fr.rsp - 0x98) 8 ((if !(decide ((v1b1715 p : BitVec 64) = 0)) then 1 else 0 : BitVec 8)),
       .mem (fr.rsp - 0x9a) 8 ((mergeGPR 8 ((if !(decide ((v1b1715 p : BitVec 64) = 0)) then 1 else 0 : BitVec 8)) ((0 : BitVec 64))).setWidth 8)]
  | .stage16 =>
      [.gpr 5 (((p.shift.setWidth 64).setWidth 32 : BitVec 32).setWidth 64),
       .gpr 3 (v1b1841 p),
       .gpr 12 (v1b1827 p),
       .gpr 13 (v1b17f0 p),
       .low 9 8 ((mergeGPR 8 ((if !(decide ((v1b1715 p : BitVec 64) = 0)) then 1 else 0 : BitVec 8)) ((0 : BitVec 64))).setWidth 8),
       .gpr 10 (v1b17fa p),
       .gpr 2 (v1b1844 p),
       .gpr 11 (v1b1811 p),
       .mem (fr.rsp - 0x90) 64 ((LinearCombination.resultWords p.linear)[1]),
       .mem (fr.rsp - 0x88) 64 ((LinearCombination.resultWords p.linear)[2]),
       .mem (fr.rsp - 0x80) 64 ((LinearCombination.resultWords p.linear)[3]),
       .mem (fr.rsp - 0x78) 64 ((LinearCombination.resultWords p.linear)[4]),
       .mem (fr.rsp - 0x70) 8 (LinearCombination.resultSign p.linear),
       .mem (fr.rsp - 0x64) 32 ((p.shift.setWidth 64).setWidth 32),
       .mem (fr.rsp - 0x38) 64 (fr.rdi),
       .mem (fr.rsp - 0x58) 64 (p.modulus[0]),
       .mem (fr.rsp - 0x50) 64 (p.modulus[1]),
       .mem (fr.rsp - 0x48) 64 (p.modulus[2]),
       .mem (fr.rsp - 0x40) 64 (p.modulus[3]),
       .mem (fr.rsp - 0x99) 8 ((((LinearCombination.resultSign p.linear).setWidth 32 : BitVec 32).setWidth 64).setWidth 8),
       .mem (fr.rsp - 0x60) 64 (v1b1629 p),
       .mem (fr.rsp - 0x98) 8 ((if !(decide ((v1b1715 p : BitVec 64) = 0)) then 1 else 0 : BitVec 8)),
       .mem (fr.rsp - 0x9a) 8 ((mergeGPR 8 ((if !(decide ((v1b1715 p : BitVec 64) = 0)) then 1 else 0 : BitVec 8)) ((0 : BitVec 64))).setWidth 8)]
  | .stage17 =>
      [.gpr 5 (((p.shift.setWidth 64).setWidth 32 : BitVec 32).setWidth 64),
       .gpr 3 (v1b1841 p),
       .gpr 12 (v1b1827 p),
       .gpr 13 (v1b17f0 p),
       .low 9 8 ((mergeGPR 8 ((if !(decide ((v1b1715 p : BitVec 64) = 0)) then 1 else 0 : BitVec 8)) ((0 : BitVec 64))).setWidth 8),
       .gpr 0 (v1b184f p),
       .gpr 10 (v1b17fa p),
       .gpr 2 (v1b1844 p),
       .gpr 11 (v1b1811 p),
       .mem (fr.rsp - 0x90) 64 ((LinearCombination.resultWords p.linear)[1]),
       .mem (fr.rsp - 0x88) 64 ((LinearCombination.resultWords p.linear)[2]),
       .mem (fr.rsp - 0x80) 64 ((LinearCombination.resultWords p.linear)[3]),
       .mem (fr.rsp - 0x78) 64 ((LinearCombination.resultWords p.linear)[4]),
       .mem (fr.rsp - 0x70) 8 (LinearCombination.resultSign p.linear),
       .mem (fr.rsp - 0x64) 32 ((p.shift.setWidth 64).setWidth 32),
       .mem (fr.rsp - 0x38) 64 (fr.rdi),
       .mem (fr.rsp - 0x58) 64 (p.modulus[0]),
       .mem (fr.rsp - 0x50) 64 (p.modulus[1]),
       .mem (fr.rsp - 0x48) 64 (p.modulus[2]),
       .mem (fr.rsp - 0x40) 64 (p.modulus[3]),
       .mem (fr.rsp - 0x99) 8 ((((LinearCombination.resultSign p.linear).setWidth 32 : BitVec 32).setWidth 64).setWidth 8),
       .mem (fr.rsp - 0x60) 64 (v1b1629 p),
       .mem (fr.rsp - 0x9a) 8 ((mergeGPR 8 ((if !(decide ((v1b1715 p : BitVec 64) = 0)) then 1 else 0 : BitVec 8)) ((0 : BitVec 64))).setWidth 8),
       .mem (fr.rsp - 0x98) 64 (v1b1867 p)]
  | .stage18 =>
      [.gpr 5 (((p.shift.setWidth 64).setWidth 32 : BitVec 32).setWidth 64),
       .gpr 3 (v1b1841 p),
       .gpr 12 (v1b1827 p),
       .gpr 13 (v1b17f0 p),
       .gpr 6 (v1b18a4 p),
       .gpr 9 ((v1b188c p).1),
       .gpr 0 (v1b184f p),
       .gpr 10 (v1b17fa p),
       .gpr 2 (v1b1844 p),
       .gpr 11 (v1b1811 p),
       .mem (fr.rsp - 0x90) 64 ((LinearCombination.resultWords p.linear)[1]),
       .mem (fr.rsp - 0x88) 64 ((LinearCombination.resultWords p.linear)[2]),
       .mem (fr.rsp - 0x80) 64 ((LinearCombination.resultWords p.linear)[3]),
       .mem (fr.rsp - 0x78) 64 ((LinearCombination.resultWords p.linear)[4]),
       .mem (fr.rsp - 0x70) 8 (LinearCombination.resultSign p.linear),
       .mem (fr.rsp - 0x64) 32 ((p.shift.setWidth 64).setWidth 32),
       .mem (fr.rsp - 0x38) 64 (fr.rdi),
       .mem (fr.rsp - 0x58) 64 (p.modulus[0]),
       .mem (fr.rsp - 0x50) 64 (p.modulus[1]),
       .mem (fr.rsp - 0x48) 64 (p.modulus[2]),
       .mem (fr.rsp - 0x40) 64 (p.modulus[3]),
       .mem (fr.rsp - 0x99) 8 ((((LinearCombination.resultSign p.linear).setWidth 32 : BitVec 32).setWidth 64).setWidth 8),
       .mem (fr.rsp - 0x60) 64 (v1b1629 p),
       .mem (fr.rsp - 0x9a) 8 ((mergeGPR 8 ((if !(decide ((v1b1715 p : BitVec 64) = 0)) then 1 else 0 : BitVec 8)) ((0 : BitVec 64))).setWidth 8),
       .mem (fr.rsp - 0x98) 64 (v1b1867 p)]
  | .stage19 =>
      [.gpr 5 (((p.shift.setWidth 64).setWidth 32 : BitVec 32).setWidth 64),
       .gpr 3 (v1b1841 p),
       .gpr 12 (v1b1827 p),
       .gpr 13 (v1b17f0 p),
       .gpr 7 (v1b18db p),
       .gpr 6 ((v1b18c3 p).1),
       .gpr 9 ((v1b188c p).1),
       .gpr 0 (v1b184f p),
       .gpr 10 (v1b17fa p),
       .gpr 2 (v1b1844 p),
       .gpr 11 (v1b1811 p),
       .mem (fr.rsp - 0x90) 64 ((LinearCombination.resultWords p.linear)[1]),
       .mem (fr.rsp - 0x88) 64 ((LinearCombination.resultWords p.linear)[2]),
       .mem (fr.rsp - 0x80) 64 ((LinearCombination.resultWords p.linear)[3]),
       .mem (fr.rsp - 0x78) 64 ((LinearCombination.resultWords p.linear)[4]),
       .mem (fr.rsp - 0x70) 8 (LinearCombination.resultSign p.linear),
       .mem (fr.rsp - 0x64) 32 ((p.shift.setWidth 64).setWidth 32),
       .mem (fr.rsp - 0x38) 64 (fr.rdi),
       .mem (fr.rsp - 0x58) 64 (p.modulus[0]),
       .mem (fr.rsp - 0x50) 64 (p.modulus[1]),
       .mem (fr.rsp - 0x48) 64 (p.modulus[2]),
       .mem (fr.rsp - 0x40) 64 (p.modulus[3]),
       .mem (fr.rsp - 0x99) 8 ((((LinearCombination.resultSign p.linear).setWidth 32 : BitVec 32).setWidth 64).setWidth 8),
       .mem (fr.rsp - 0x60) 64 (v1b1629 p),
       .mem (fr.rsp - 0x9a) 8 ((mergeGPR 8 ((if !(decide ((v1b1715 p : BitVec 64) = 0)) then 1 else 0 : BitVec 8)) ((0 : BitVec 64))).setWidth 8),
       .mem (fr.rsp - 0x98) 64 (v1b18a4 p)]
  | .stage20 =>
      [.gpr 5 (((p.shift.setWidth 64).setWidth 32 : BitVec 32).setWidth 64),
       .gpr 3 (v1b1841 p),
       .gpr 12 (v1b1827 p),
       .gpr 13 (v1b17f0 p),
       .gpr 7 ((v1b18fd p).1),
       .gpr 6 ((v1b18c3 p).1),
       .gpr 9 ((v1b188c p).1),
       .gpr 8 (v1b1915 p),
       .gpr 0 (v1b184f p),
       .gpr 2 (v1b1844 p),
       .gpr 11 (v1b18eb p),
       .mem (fr.rsp - 0x90) 64 ((LinearCombination.resultWords p.linear)[1]),
       .mem (fr.rsp - 0x88) 64 ((LinearCombination.resultWords p.linear)[2]),
       .mem (fr.rsp - 0x80) 64 ((LinearCombination.resultWords p.linear)[3]),
       .mem (fr.rsp - 0x78) 64 ((LinearCombination.resultWords p.linear)[4]),
       .mem (fr.rsp - 0x70) 8 (LinearCombination.resultSign p.linear),
       .mem (fr.rsp - 0x64) 32 ((p.shift.setWidth 64).setWidth 32),
       .mem (fr.rsp - 0x38) 64 (fr.rdi),
       .mem (fr.rsp - 0x58) 64 (p.modulus[0]),
       .mem (fr.rsp - 0x50) 64 (p.modulus[1]),
       .mem (fr.rsp - 0x48) 64 (p.modulus[2]),
       .mem (fr.rsp - 0x40) 64 (p.modulus[3]),
       .mem (fr.rsp - 0x99) 8 ((((LinearCombination.resultSign p.linear).setWidth 32 : BitVec 32).setWidth 64).setWidth 8),
       .mem (fr.rsp - 0x60) 64 (v1b1629 p),
       .mem (fr.rsp - 0x9a) 8 ((mergeGPR 8 ((if !(decide ((v1b1715 p : BitVec 64) = 0)) then 1 else 0 : BitVec 8)) ((0 : BitVec 64))).setWidth 8),
       .mem (fr.rsp - 0x98) 64 (v1b1915 p)]
  | .stage21 =>
      [.gpr 5 (mergeGPR 8 (v1b1930 p) ((((((LinearCombination.resultSign p.linear).setWidth 32 : BitVec 32).setWidth 64).setWidth 8).setWidth 32 : BitVec 32).setWidth 64)),
       .gpr 3 (v1b1841 p),
       .gpr 12 (v1b1827 p),
       .gpr 1 (mergeGPR 8 (v1b193b p) (mergeGPR 8 ((if decide ((v1b1923 p : BitVec 64) = 0) then 1 else 0 : BitVec 8)) (((((p.shift.setWidth 64).setWidth 32 : BitVec 32).setWidth 64).setWidth 32 : BitVec 32).setWidth 64))),
       .gpr 7 ((v1b18fd p).1),
       .gpr 6 ((v1b18c3 p).1),
       .gpr 9 ((v1b188c p).1),
       .gpr 0 (v1b184f p),
       .gpr 10 (v1b195a p),
       .gpr 2 (v1b1844 p),
       .gpr 11 (v1b18eb p),
       .mem (fr.rsp - 0x90) 64 ((LinearCombination.resultWords p.linear)[1]),
       .mem (fr.rsp - 0x88) 64 ((LinearCombination.resultWords p.linear)[2]),
       .mem (fr.rsp - 0x80) 64 ((LinearCombination.resultWords p.linear)[3]),
       .mem (fr.rsp - 0x78) 64 ((LinearCombination.resultWords p.linear)[4]),
       .mem (fr.rsp - 0x70) 8 (LinearCombination.resultSign p.linear),
       .mem (fr.rsp - 0x64) 32 ((p.shift.setWidth 64).setWidth 32),
       .mem (fr.rsp - 0x38) 64 (fr.rdi),
       .mem (fr.rsp - 0x58) 64 (p.modulus[0]),
       .mem (fr.rsp - 0x50) 64 (p.modulus[1]),
       .mem (fr.rsp - 0x48) 64 (p.modulus[2]),
       .mem (fr.rsp - 0x40) 64 (p.modulus[3]),
       .mem (fr.rsp - 0x99) 8 ((((LinearCombination.resultSign p.linear).setWidth 32 : BitVec 32).setWidth 64).setWidth 8),
       .mem (fr.rsp - 0x60) 64 (v1b1629 p),
       .mem (fr.rsp - 0x9a) 8 ((mergeGPR 8 ((if !(decide ((v1b1715 p : BitVec 64) = 0)) then 1 else 0 : BitVec 8)) ((0 : BitVec 64))).setWidth 8),
       .mem (fr.rsp - 0x98) 8 ((mergeGPR 8 (v1b193b p) (mergeGPR 8 ((if decide ((v1b1923 p : BitVec 64) = 0) then 1 else 0 : BitVec 8)) (((((p.shift.setWidth 64).setWidth 32 : BitVec 32).setWidth 64).setWidth 32 : BitVec 32).setWidth 64))).setWidth 8)]
  | .stage22 =>
      [.gpr 5 (mergeGPR 8 (v1b1930 p) ((((((LinearCombination.resultSign p.linear).setWidth 32 : BitVec 32).setWidth 64).setWidth 8).setWidth 32 : BitVec 32).setWidth 64)),
       .gpr 12 (v1b1827 p),
       .gpr 1 (mergeGPR 8 (v1b193b p) (mergeGPR 8 ((if decide ((v1b1923 p : BitVec 64) = 0) then 1 else 0 : BitVec 8)) (((((p.shift.setWidth 64).setWidth 32 : BitVec 32).setWidth 64).setWidth 32 : BitVec 32).setWidth 64))),
       .gpr 7 ((v1b18fd p).1),
       .gpr 6 ((v1b18c3 p).1),
       .gpr 8 (v1b1980 p),
       .gpr 0 (v1b1995 p),
       .gpr 11 (v1b18eb p),
       .mem (fr.rsp - 0x90) 64 ((LinearCombination.resultWords p.linear)[1]),
       .mem (fr.rsp - 0x88) 64 ((LinearCombination.resultWords p.linear)[2]),
       .mem (fr.rsp - 0x80) 64 ((LinearCombination.resultWords p.linear)[3]),
       .mem (fr.rsp - 0x78) 64 ((LinearCombination.resultWords p.linear)[4]),
       .mem (fr.rsp - 0x70) 8 (LinearCombination.resultSign p.linear),
       .mem (fr.rsp - 0x64) 32 ((p.shift.setWidth 64).setWidth 32),
       .mem (fr.rsp - 0x38) 64 (fr.rdi),
       .mem (fr.rsp - 0x58) 64 (p.modulus[0]),
       .mem (fr.rsp - 0x50) 64 (p.modulus[1]),
       .mem (fr.rsp - 0x48) 64 (p.modulus[2]),
       .mem (fr.rsp - 0x40) 64 (p.modulus[3]),
       .mem (fr.rsp - 0x99) 8 ((((LinearCombination.resultSign p.linear).setWidth 32 : BitVec 32).setWidth 64).setWidth 8),
       .mem (fr.rsp - 0x60) 64 (v1b1629 p),
       .mem (fr.rsp - 0x9a) 8 ((mergeGPR 8 ((if !(decide ((v1b1715 p : BitVec 64) = 0)) then 1 else 0 : BitVec 8)) ((0 : BitVec 64))).setWidth 8),
       .mem (fr.rsp - 0x98) 8 ((mergeGPR 8 (v1b193b p) (mergeGPR 8 ((if decide ((v1b1923 p : BitVec 64) = 0) then 1 else 0 : BitVec 8)) (((((p.shift.setWidth 64).setWidth 32 : BitVec 32).setWidth 64).setWidth 32 : BitVec 32).setWidth 64))).setWidth 8)]
  | .stage23 =>
      [.gpr 5 (mergeGPR 8 (v1b1930 p) ((((((LinearCombination.resultSign p.linear).setWidth 32 : BitVec 32).setWidth 64).setWidth 8).setWidth 32 : BitVec 32).setWidth 64)),
       .gpr 1 (v1b19bf p),
       .gpr 8 (v1b1980 p),
       .gpr 0 (v1b1995 p),
       .gpr 2 (v1b19aa p),
       .mem (fr.rsp - 0x90) 64 ((LinearCombination.resultWords p.linear)[1]),
       .mem (fr.rsp - 0x88) 64 ((LinearCombination.resultWords p.linear)[2]),
       .mem (fr.rsp - 0x80) 64 ((LinearCombination.resultWords p.linear)[3]),
       .mem (fr.rsp - 0x78) 64 ((LinearCombination.resultWords p.linear)[4]),
       .mem (fr.rsp - 0x70) 8 (LinearCombination.resultSign p.linear),
       .mem (fr.rsp - 0x64) 32 ((p.shift.setWidth 64).setWidth 32),
       .mem (fr.rsp - 0x38) 64 (fr.rdi),
       .mem (fr.rsp - 0x58) 64 (p.modulus[0]),
       .mem (fr.rsp - 0x50) 64 (p.modulus[1]),
       .mem (fr.rsp - 0x48) 64 (p.modulus[2]),
       .mem (fr.rsp - 0x40) 64 (p.modulus[3]),
       .mem (fr.rsp - 0x99) 8 ((((LinearCombination.resultSign p.linear).setWidth 32 : BitVec 32).setWidth 64).setWidth 8),
       .mem (fr.rsp - 0x60) 64 (v1b1629 p),
       .mem (fr.rsp - 0x9a) 8 ((mergeGPR 8 ((if !(decide ((v1b1715 p : BitVec 64) = 0)) then 1 else 0 : BitVec 8)) ((0 : BitVec 64))).setWidth 8),
       .mem (fr.rsp - 0x98) 8 ((mergeGPR 8 (v1b193b p) (mergeGPR 8 ((if decide ((v1b1923 p : BitVec 64) = 0) then 1 else 0 : BitVec 8)) (((((p.shift.setWidth 64).setWidth 32 : BitVec 32).setWidth 64).setWidth 32 : BitVec 32).setWidth 64))).setWidth 8)]

def dialect : Dialect Support.Op Unit Inputs where
  eval op := nomatch op
  truth _ := false

def layout (fr : Activation) (controls : RamState) : Layout program dialect Machine.lifted Unit where
  start := start
  Params _ := Inputs
  args _ _ := #v[]
  store _ p := p
  atoms l _ p := frame fr controls p ++ coreAtoms l fr p
  Result := Inputs
  output p := ⟨#v[], none, p⟩
  done _ p := Machine.Modular.doneAt fr ++
    [.words fr.rdi 64 (resultWords p), .mem (fr.rdi + 32) 8 (resultSign p), .readable fr.rdi 33,
      .reg 39 ⟨32, controls.MXCSR⟩, .reg 51 ⟨16, controls.FP87_Control⟩]
  retAddr _ := fr.ret
  original _ := fr.original
  regions _ := [fr.region, outputRegion fr]

end P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Tail
