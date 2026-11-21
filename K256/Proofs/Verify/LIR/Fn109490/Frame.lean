import K256.Proofs.Verify.LIR.Program
import K256.Proofs.Common.Refine.Contract
import K256.Proofs.Common.Refine.Lemma.SysVEntry

namespace K256.Proofs.Verify.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Sec1.LIR K256.Proofs.Generate.LIR K256.Proofs.Ecdh.LIR

namespace Fn109490

def frameInfo : Refine.FrameInfo where
  entry := 0x109490
  frameBytes := 0x198
  stackBytes := some 0x2d0
  slots := [(3, 0x30), (5, 0x8), (12, 0x28), (13, 0x20), (14, 0x18), (15, 0x10)]
  preserved := [3, 5, 12, 13, 14, 15]
  fpPreserved := [39, 50, 51]
  clobbers := [0, 1, 2, 6, 7, 8, 9, 10, 11]
  callSlots := [(0x203de0, 0x129770), (0x203e20, 0x100a20)]

def labelFrameG11 : Label.G11 → Option Refine.LabelFrame
  | .l109490 => some ⟨0x0, [(1, 1), (2, 2), (3, 3), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9),
      (12, 12), (13, 13), (14, 14), (15, 15), (39, 39), (50, 50),
      (51, 51)], [], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l1095b0 => some ⟨0x188, [(39, 39), (50, 50), (51, 51)], [(0x130, 2), (0x68, 7), (0x60, 1),
      (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770),
      (0x203e20, 0x100a20)]⟩
  | .l1095c1 => some ⟨0x188, [(39, 39), (50, 50), (51, 51)], [(0x130, 2), (0x68, 7), (0x60, 1),
      (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770),
      (0x203e20, 0x100a20)]⟩
  | .l10960c => some ⟨0x188, [(39, 39), (50, 50), (51, 51)], [(0x130, 2), (0x68, 7), (0x60, 1),
      (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770),
      (0x203e20, 0x100a20)]⟩
  | .l109657 => some ⟨0x188, [(39, 39), (50, 50), (51, 51)], [(0x130, 2), (0x68, 7), (0x60, 1),
      (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770),
      (0x203e20, 0x100a20)]⟩
  | .l10971c => some ⟨0x198, [(3, 2), (15, 1), (39, 39), (50, 50), (51, 51)], [(0x198, 2),
      (0x190, 1), (0x130, 2), (0x68, 7), (0x60, 1), (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14),
      (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l109763 => some ⟨0x198, [(3, 2), (15, 1), (39, 39), (50, 50), (51, 51)], [(0x198, 2),
      (0x190, 1), (0x130, 2), (0x68, 7), (0x60, 1), (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14),
      (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l1097fe => some ⟨0x188, [(39, 39), (50, 50), (51, 51)], [(0x130, 2), (0x68, 7), (0x60, 1),
      (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770),
      (0x203e20, 0x100a20)]⟩
  | .l109808 => some ⟨0x188, [(39, 39), (50, 50), (51, 51)], [(0x130, 2), (0x68, 7), (0x60, 1),
      (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770),
      (0x203e20, 0x100a20)]⟩
  | .l109810 => some ⟨0x188, [(39, 39), (50, 50), (51, 51)], [(0x130, 2), (0x68, 7), (0x60, 1),
      (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770),
      (0x203e20, 0x100a20)]⟩
  | .l109818 => some ⟨0x188, [(39, 39), (50, 50), (51, 51)], [(0x130, 2), (0x68, 7), (0x60, 1),
      (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770),
      (0x203e20, 0x100a20)]⟩
  | .l109824 => some ⟨0x188, [(39, 39), (50, 50), (51, 51)], [(0x130, 2), (0x68, 7), (0x60, 1),
      (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770),
      (0x203e20, 0x100a20)]⟩
  | .l10988a => some ⟨0x188, [(39, 39), (50, 50), (51, 51)], [(0x130, 2), (0x68, 7), (0x60, 1),
      (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770),
      (0x203e20, 0x100a20)]⟩
  | .l1098e0 => some ⟨0x188, [(39, 39), (50, 50), (51, 51)], [(0x130, 2), (0x68, 7), (0x60, 1),
      (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770),
      (0x203e20, 0x100a20)]⟩
  | .l1098e5 => some ⟨0x188, [(39, 39), (50, 50), (51, 51)], [(0x130, 2), (0x68, 7), (0x60, 1),
      (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770),
      (0x203e20, 0x100a20)]⟩
  | .l10990b => some ⟨0x188, [(39, 39), (50, 50), (51, 51)], [(0x130, 2), (0x68, 7), (0x60, 1),
      (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770),
      (0x203e20, 0x100a20)]⟩
  | .l109925 => some ⟨0x188, [(39, 39), (50, 50), (51, 51)], [(0x130, 2), (0x68, 7), (0x60, 1),
      (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770),
      (0x203e20, 0x100a20)]⟩
  | .l10992a => some ⟨0x188, [(39, 39), (50, 50), (51, 51)], [(0x130, 2), (0x68, 7), (0x60, 1),
      (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770),
      (0x203e20, 0x100a20)]⟩
  | .l109930 => some ⟨0x188, [(39, 39), (50, 50), (51, 51)], [(0x130, 2), (0x68, 7), (0x60, 1),
      (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770),
      (0x203e20, 0x100a20)]⟩
  | .l10993d => some ⟨0x188, [(39, 39), (50, 50), (51, 51)], [(0x130, 2), (0x68, 7), (0x60, 1),
      (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770),
      (0x203e20, 0x100a20)]⟩
  | .l109948 => some ⟨0x188, [(39, 39), (50, 50), (51, 51)], [(0x130, 2), (0x68, 7), (0x60, 1),
      (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15), (0x8, 5)], []⟩
  | .l109989 => some ⟨0x188, [(14, 7), (39, 39), (50, 50), (51, 51)], [(0x130, 2), (0x68, 7),
      (0x60, 1), (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15), (0x8, 5)], []⟩
  | _ => none

@[refine_layout] def frameAtG11 : Label.G11 → Refine.Activation → List Refine.Atom
  | .l109490 => fun fr =>
      [.gpr 4 fr.rsp, .reg 22 ⟨1, 0⟩, .gpr 1 fr.rcx, .gpr 2 fr.rdx, .gpr 3 fr.rbx, .gpr 5 fr.rbp,
       .gpr 6 fr.rsi, .gpr 7 fr.rdi, .gpr 8 fr.r8, .gpr 9 fr.r9, .gpr 12 fr.r12, .gpr 13 fr.r13,
       .gpr 14 fr.r14, .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x2d0) 0x2d0,
       .fact (fr.low.toNat + 0x2d0 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x203de0 8, .mem 0x203de0 64 0x129770, .readable 0x203e20 8,
       .mem 0x203e20 64 0x100a20, .fact (0x2040f8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l1095b0 => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x130) 64 fr.rdx, .mem (fr.rsp - 0x68) 64 fr.rdi,
       .mem (fr.rsp - 0x60) 64 fr.rcx, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x2d0) 0x2d0,
       .fact (fr.low.toNat + 0x2d0 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x203de0 8, .mem 0x203de0 64 0x129770, .readable 0x203e20 8,
       .mem 0x203e20 64 0x100a20, .fact (0x2040f8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l1095c1 => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x130) 64 fr.rdx, .mem (fr.rsp - 0x68) 64 fr.rdi,
       .mem (fr.rsp - 0x60) 64 fr.rcx, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x2d0) 0x2d0,
       .fact (fr.low.toNat + 0x2d0 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x203de0 8, .mem 0x203de0 64 0x129770, .readable 0x203e20 8,
       .mem 0x203e20 64 0x100a20, .fact (0x2040f8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l10960c => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x130) 64 fr.rdx, .mem (fr.rsp - 0x68) 64 fr.rdi,
       .mem (fr.rsp - 0x60) 64 fr.rcx, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x2d0) 0x2d0,
       .fact (fr.low.toNat + 0x2d0 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x203de0 8, .mem 0x203de0 64 0x129770, .readable 0x203e20 8,
       .mem 0x203e20 64 0x100a20, .fact (0x2040f8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l109657 => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x130) 64 fr.rdx, .mem (fr.rsp - 0x68) 64 fr.rdi,
       .mem (fr.rsp - 0x60) 64 fr.rcx, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x2d0) 0x2d0,
       .fact (fr.low.toNat + 0x2d0 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x203de0 8, .mem 0x203de0 64 0x129770, .readable 0x203e20 8,
       .mem 0x203e20 64 0x100a20, .fact (0x2040f8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l10971c => fun fr =>
      [.gpr 4 (fr.rsp - 0x198), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rdx, .gpr 15 fr.rcx,
       .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩,
       .mem (fr.rsp - 0x198) 64 fr.rdx, .mem (fr.rsp - 0x190) 64 fr.rcx,
       .mem (fr.rsp - 0x130) 64 fr.rdx, .mem (fr.rsp - 0x68) 64 fr.rdi,
       .mem (fr.rsp - 0x60) 64 fr.rcx, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x2d0) 0x2d0,
       .fact (fr.low.toNat + 0x2d0 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x203de0 8, .mem 0x203de0 64 0x129770, .readable 0x203e20 8,
       .mem 0x203e20 64 0x100a20, .fact (0x2040f8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l109763 => fun fr =>
      [.gpr 4 (fr.rsp - 0x198), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rdx, .gpr 15 fr.rcx,
       .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩,
       .mem (fr.rsp - 0x198) 64 fr.rdx, .mem (fr.rsp - 0x190) 64 fr.rcx,
       .mem (fr.rsp - 0x130) 64 fr.rdx, .mem (fr.rsp - 0x68) 64 fr.rdi,
       .mem (fr.rsp - 0x60) 64 fr.rcx, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x2d0) 0x2d0,
       .fact (fr.low.toNat + 0x2d0 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x203de0 8, .mem 0x203de0 64 0x129770, .readable 0x203e20 8,
       .mem 0x203e20 64 0x100a20, .fact (0x2040f8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l1097fe => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x130) 64 fr.rdx, .mem (fr.rsp - 0x68) 64 fr.rdi,
       .mem (fr.rsp - 0x60) 64 fr.rcx, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x2d0) 0x2d0,
       .fact (fr.low.toNat + 0x2d0 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x203de0 8, .mem 0x203de0 64 0x129770, .readable 0x203e20 8,
       .mem 0x203e20 64 0x100a20, .fact (0x2040f8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l109808 => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x130) 64 fr.rdx, .mem (fr.rsp - 0x68) 64 fr.rdi,
       .mem (fr.rsp - 0x60) 64 fr.rcx, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x2d0) 0x2d0,
       .fact (fr.low.toNat + 0x2d0 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x203de0 8, .mem 0x203de0 64 0x129770, .readable 0x203e20 8,
       .mem 0x203e20 64 0x100a20, .fact (0x2040f8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l109810 => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x130) 64 fr.rdx, .mem (fr.rsp - 0x68) 64 fr.rdi,
       .mem (fr.rsp - 0x60) 64 fr.rcx, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x2d0) 0x2d0,
       .fact (fr.low.toNat + 0x2d0 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x203de0 8, .mem 0x203de0 64 0x129770, .readable 0x203e20 8,
       .mem 0x203e20 64 0x100a20, .fact (0x2040f8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l109818 => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x130) 64 fr.rdx, .mem (fr.rsp - 0x68) 64 fr.rdi,
       .mem (fr.rsp - 0x60) 64 fr.rcx, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x2d0) 0x2d0,
       .fact (fr.low.toNat + 0x2d0 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x203de0 8, .mem 0x203de0 64 0x129770, .readable 0x203e20 8,
       .mem 0x203e20 64 0x100a20, .fact (0x2040f8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l109824 => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x130) 64 fr.rdx, .mem (fr.rsp - 0x68) 64 fr.rdi,
       .mem (fr.rsp - 0x60) 64 fr.rcx, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x2d0) 0x2d0,
       .fact (fr.low.toNat + 0x2d0 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x203de0 8, .mem 0x203de0 64 0x129770, .readable 0x203e20 8,
       .mem 0x203e20 64 0x100a20, .fact (0x2040f8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l10988a => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x130) 64 fr.rdx, .mem (fr.rsp - 0x68) 64 fr.rdi,
       .mem (fr.rsp - 0x60) 64 fr.rcx, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x2d0) 0x2d0,
       .fact (fr.low.toNat + 0x2d0 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x203de0 8, .mem 0x203de0 64 0x129770, .readable 0x203e20 8,
       .mem 0x203e20 64 0x100a20, .fact (0x2040f8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l1098e0 => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x130) 64 fr.rdx, .mem (fr.rsp - 0x68) 64 fr.rdi,
       .mem (fr.rsp - 0x60) 64 fr.rcx, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x2d0) 0x2d0,
       .fact (fr.low.toNat + 0x2d0 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x203de0 8, .mem 0x203de0 64 0x129770, .readable 0x203e20 8,
       .mem 0x203e20 64 0x100a20, .fact (0x2040f8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l1098e5 => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x130) 64 fr.rdx, .mem (fr.rsp - 0x68) 64 fr.rdi,
       .mem (fr.rsp - 0x60) 64 fr.rcx, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x2d0) 0x2d0,
       .fact (fr.low.toNat + 0x2d0 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x203de0 8, .mem 0x203de0 64 0x129770, .readable 0x203e20 8,
       .mem 0x203e20 64 0x100a20, .fact (0x2040f8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l10990b => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x130) 64 fr.rdx, .mem (fr.rsp - 0x68) 64 fr.rdi,
       .mem (fr.rsp - 0x60) 64 fr.rcx, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x2d0) 0x2d0,
       .fact (fr.low.toNat + 0x2d0 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x203de0 8, .mem 0x203de0 64 0x129770, .readable 0x203e20 8,
       .mem 0x203e20 64 0x100a20, .fact (0x2040f8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l109925 => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x130) 64 fr.rdx, .mem (fr.rsp - 0x68) 64 fr.rdi,
       .mem (fr.rsp - 0x60) 64 fr.rcx, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x2d0) 0x2d0,
       .fact (fr.low.toNat + 0x2d0 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x203de0 8, .mem 0x203de0 64 0x129770, .readable 0x203e20 8,
       .mem 0x203e20 64 0x100a20, .fact (0x2040f8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l10992a => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x130) 64 fr.rdx, .mem (fr.rsp - 0x68) 64 fr.rdi,
       .mem (fr.rsp - 0x60) 64 fr.rcx, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x2d0) 0x2d0,
       .fact (fr.low.toNat + 0x2d0 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x203de0 8, .mem 0x203de0 64 0x129770, .readable 0x203e20 8,
       .mem 0x203e20 64 0x100a20, .fact (0x2040f8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l109930 => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x130) 64 fr.rdx, .mem (fr.rsp - 0x68) 64 fr.rdi,
       .mem (fr.rsp - 0x60) 64 fr.rcx, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x2d0) 0x2d0,
       .fact (fr.low.toNat + 0x2d0 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x203de0 8, .mem 0x203de0 64 0x129770, .readable 0x203e20 8,
       .mem 0x203e20 64 0x100a20, .fact (0x2040f8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l10993d => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x130) 64 fr.rdx, .mem (fr.rsp - 0x68) 64 fr.rdi,
       .mem (fr.rsp - 0x60) 64 fr.rcx, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x2d0) 0x2d0,
       .fact (fr.low.toNat + 0x2d0 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x203de0 8, .mem 0x203de0 64 0x129770, .readable 0x203e20 8,
       .mem 0x203e20 64 0x100a20, .fact (0x2040f8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l109948 => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x130) 64 fr.rdx, .mem (fr.rsp - 0x68) 64 fr.rdi,
       .mem (fr.rsp - 0x60) 64 fr.rcx, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x2d0) 0x2d0,
       .fact (fr.low.toNat + 0x2d0 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l109989 => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .gpr 14 fr.rdi, .reg 39 ⟨32, fr.mxcsr⟩,
       .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x130) 64 fr.rdx,
       .mem (fr.rsp - 0x68) 64 fr.rdi, .mem (fr.rsp - 0x60) 64 fr.rcx,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x2d0) 0x2d0, .fact (fr.low.toNat + 0x2d0 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8)]
  | _ => fun _ => []

def labelFrame : Label → Option Refine.LabelFrame
  | .g11 l => labelFrameG11 l
  | _ => none

@[refine_layout] def frameAt : Label → Refine.Activation → List Refine.Atom
  | .g11 l => frameAtG11 l
  | _ => fun _ => []

@[refine_layout] def doneAt (fr : Refine.Activation) : List Refine.Atom :=
  [.gpr 4 (fr.rsp + 8), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rbx, .gpr 5 fr.rbp, .gpr 12 fr.r12,
   .gpr 13 fr.r13, .gpr 14 fr.r14, .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
   .reg 51 ⟨16, fr.fcw⟩]

theorem frameAt_canonical (l : Label) (fr : Refine.Activation) :
    frameAt l fr = frameInfo.atomsAt (labelFrame l) fr := by
  cases l <;> rename_i l <;> first | rfl | (cases l <;> rfl)

theorem doneAt_canonical (fr : Refine.Activation) : doneAt fr = frameInfo.doneAtoms fr := rfl

abbrev Pre (code : CodeMap) (fr : Refine.Activation) (s : RamState) : Prop :=
  frameInfo.Pre code fr s

abbrev Post (fr : Refine.Activation) (footprint : List Prelude.MemoryRegion)
    (t : RamState) : Prop :=
  frameInfo.Post fr footprint t

def closureCode : CodeMap := sectionCode textSection [(0xa20, 0x2), (0x84e0, 0x3aa),
    (0x8890, 0x597), (0x9490, 0x11c), (0x95b0, 0x32a), (0x98e0, 0xdf), (0x9c00, 0x175),
    (0x29560, 0x34), (0x295f2, 0x3d), (0x29770, 0x2c)]

theorem closure_code : ∀ x ∈ closureCode, x ∈ fnCode :=
  sectionCode_sub (.head _) (by decide)

theorem callSlots_loaded {sections : Prelude.ImageSections}
    (hs : rodataSection ∈ sections) {mem : Ram}
    (h : ∀ x ∈ sections.toCodeMap, mem[x.1]? = some x.2) :
    ∀ c ∈ frameInfo.callSlots, Refine.Readable mem c.1 8 ∧ memLoad mem c.1 64 = c.2 :=
  Refine.FrameInfo.callSlots_of_section hs (by decide +kernel) h

theorem callSlots_span {sections : Prelude.ImageSections}
    (hs : rodataSection ∈ sections) :
    ∀ a : BitVec 64, Refine.FrameInfo.slotsLow frameInfo.callSlots ≤ a.toNat →
      a.toNat < Refine.FrameInfo.slotsHigh frameInfo.callSlots →
        ∃ b, (a, b) ∈ sections.toCodeMap :=
  Refine.FrameInfo.callSlotSpan_of_section hs (by decide +kernel)

section Contract

variable {UOp : Nat → Type} {ULabel UValue UStore : Type} {usig : ULabel → Nat} {results : Nat}
  {P : Program UOp ULabel usig results} {D : Dialect UOp UValue UStore} {Ctx : Type}

theorem routine [inst : Bindings] {atoms : Label → Refine.Activation → List Refine.Atom}
    {retAtoms : Refine.Activation → List Refine.Atom} (core : Refine.LayoutCore P D lifted Ctx)
    {code : CodeMap} (liftedBlocks : ∀ l, LiftedBlock code lifted l)
    (blocks : ∀ label, (Refine.Layout.withFrame atoms retAtoms core).BlockSimulation code label)
    {initial : RamState} {fr : Refine.Activation} {c : Ctx} {n : Nat}
    {regions : Vector Prelude.MemoryRegion n} (hready : EntryReady code initial)
    (hpre : Pre code fr initial)
    (hregions : ∀ x, (∀ r ∈ regions, ¬ r.Contains x) →
      ∀ r ∈ fr.region :: core.footprint c fr, ¬ r.Contains x)
    {lab : ULabel} {p : core.Params lab} {o : Output UValue UStore results}
    (hexec : P.Exec D ⟨⟨lab, core.args lab p, core.store lab p⟩, []⟩ o)
    (hcore : Refine.Atom.All code (lifted.locationOf .l109490 initial).arguments initial.external
      (core.atoms lab c fr p))
    (hstart : core.start lab = .l109490 := by rfl)
    (hentry : ∀ fr, atoms .l109490 fr = frameInfo.entryAtoms fr := by intro _; rfl)
    (hdone : ∀ fr, retAtoms fr = frameInfo.doneAtoms fr := by intro _; rfl) :
    RoutineResult inst initial regions fun t =>
      Prelude.Execution.CallingConvention.SysVCalleeReturn initial t fr.ret ∧
        Post fr (core.footprint c fr) t ∧ ∃ r, o = core.output r ∧ ∃ lo,
          RetRel code lifted lo t ∧
            Refine.Atom.All code lo.values lo.store (core.done c fr r) :=
  Refine.Layout.withFrame_routine core hready hpre liftedBlocks blocks hregions hexec hcore hstart hentry
    hdone rfl rfl (by decide) (by decide)

theorem call {atoms : Label → Refine.Activation → List Refine.Atom}
    {retAtoms : Refine.Activation → List Refine.Atom} {core : Refine.LayoutCore P D lifted Ctx}
    {code : CodeMap}
    (blocks : ∀ label, (Refine.Layout.withFrame atoms retAtoms core).BlockSimulation code label)
    {u : Location UValue UStore ULabel usig} {o : Output UValue UStore results}
    (hexec : P.Exec D ⟨u, []⟩ o) (fr : Refine.Activation) (c : Ctx) {l : lifted.Location}
    (hrel : (Refine.Layout.withFrame atoms retAtoms core).Rel code (fr, c) u l)
    (hdone : ∀ fr, retAtoms fr = frameInfo.doneAtoms fr := by intro _; rfl) :
    ∃ lo, lifted.program.Exec (dialect code) ⟨l, []⟩ lo ∧
      (Refine.Layout.withFrame atoms retAtoms core).RetRel code (fr, c) o lo ∧
        Refine.Atom.All code lo.values lo.store (frameInfo.doneAtoms fr) :=
  Refine.Layout.withFrame_call blocks hexec fr c hrel hdone

end Contract

end Fn109490

end K256.Proofs.Verify.LIR
