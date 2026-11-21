import K256.Proofs.Sec1.LIR.Program
import K256.Proofs.Common.Refine.Contract
import K256.Proofs.Common.Refine.Lemma.SysVEntry

namespace K256.Proofs.Sec1.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift

namespace Fn106390

def frameInfo : Refine.FrameInfo where
  entry := 0x106390
  frameBytes := 0x158
  stackBytes := some 0x608
  slots := [(3, 0x20), (12, 0x18), (14, 0x10), (15, 0x8)]
  preserved := [3, 5, 12, 13, 14, 15]
  fpPreserved := [39, 50, 51]
  clobbers := [0, 1, 2, 6, 8, 9, 10, 11]
  callSlots := [(0x203dd0, 0x12a820), (0x203de0, 0x129770), (0x203e10, 0x12a700), (0x203e20, 0x100a20)]

def labelFrameG0 : Label.G0 → Option Refine.LabelFrame
  | .l106390 => some ⟨0x0, [(1, 1), (2, 2), (3, 3), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9),
      (12, 12), (13, 13), (14, 14), (15, 15), (39, 39), (50, 50),
      (51, 51)], [], [(0x203dd0, 0x12a820), (0x203de0, 0x129770), (0x203e10, 0x12a700),
      (0x203e20, 0x100a20)]⟩
  | .l1063a7 => some ⟨0x158, [(1, 1), (2, 2), (3, 3), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9),
      (12, 12), (13, 13), (14, 14), (15, 15), (39, 39), (50, 50), (51, 51)], [(0x20, 3), (0x18, 12),
      (0x10, 14), (0x8, 15)], [(0x203dd0, 0x12a820), (0x203de0, 0x129770), (0x203e10, 0x12a700),
      (0x203e20, 0x100a20)]⟩
  | .l1063c4 => some ⟨0x158, [(2, 2), (3, 3), (5, 5), (6, 6), (7, 7), (9, 9), (12, 12), (13, 13),
      (14, 14), (15, 15), (39, 39), (50, 50), (51, 51)], [(0x20, 3), (0x18, 12), (0x10, 14),
      (0x8, 15)], [(0x203dd0, 0x12a820), (0x203de0, 0x129770), (0x203e10, 0x12a700),
      (0x203e20, 0x100a20)]⟩
  | .l1063d2 => some ⟨0x158, [(2, 2), (3, 3), (5, 5), (6, 6), (7, 7), (9, 9), (12, 12), (13, 13),
      (14, 14), (15, 15), (39, 39), (50, 50), (51, 51)], [(0x20, 3), (0x18, 12), (0x10, 14),
      (0x8, 15)], [(0x203dd0, 0x12a820), (0x203de0, 0x129770), (0x203e10, 0x12a700),
      (0x203e20, 0x100a20)]⟩
  | .l106409 => some ⟨0x158, [(3, 6), (5, 5), (13, 13), (14, 2), (15, 7), (39, 39), (50, 50),
      (51, 51)], [(0x20, 3), (0x18, 12), (0x10, 14), (0x8, 15)], [(0x203dd0, 0x12a820),
      (0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l10641d => some ⟨0x158, [(3, 6), (5, 5), (13, 13), (14, 2), (15, 7), (39, 39), (50, 50),
      (51, 51)], [(0x20, 3), (0x18, 12), (0x10, 14), (0x8, 15)], [(0x203de0, 0x129770),
      (0x203e20, 0x100a20)]⟩
  | .l1064f4 => some ⟨0x158, [(5, 5), (13, 13), (14, 2), (15, 7), (39, 39), (50, 50),
      (51, 51)], [(0x20, 3), (0x18, 12), (0x10, 14), (0x8, 15)], [(0x203de0, 0x129770),
      (0x203e20, 0x100a20)]⟩
  | .l106514 => some ⟨0x158, [(5, 5), (13, 13), (14, 2), (15, 7), (39, 39), (50, 50),
      (51, 51)], [(0x20, 3), (0x18, 12), (0x10, 14), (0x8, 15)], [(0x203de0, 0x129770),
      (0x203e20, 0x100a20)]⟩
  | .l106518 => some ⟨0x158, [(5, 5), (13, 13), (14, 2), (15, 7), (39, 39), (50, 50),
      (51, 51)], [(0x20, 3), (0x18, 12), (0x10, 14), (0x8, 15)], []⟩
  | .l106548 => some ⟨0x158, [(5, 5), (7, 7), (13, 13), (14, 2), (15, 7), (39, 39), (50, 50),
      (51, 51)], [(0x20, 3), (0x18, 12), (0x10, 14), (0x8, 15)], []⟩
  | .l106560 => some ⟨0x158, [(5, 5), (7, 7), (13, 13), (39, 39), (50, 50), (51, 51)], [(0x20, 3),
      (0x18, 12), (0x10, 14), (0x8, 15)], []⟩
  | .l106565 => some ⟨0x158, [(5, 5), (7, 7), (13, 13), (39, 39), (50, 50), (51, 51)], [(0x20, 3),
      (0x18, 12), (0x10, 14), (0x8, 15)], []⟩
  | .l10657a => some ⟨0x158, [(5, 5), (13, 13), (14, 2), (15, 7), (39, 39), (50, 50),
      (51, 51)], [(0x20, 3), (0x18, 12), (0x10, 14), (0x8, 15)], [(0x203de0, 0x129770),
      (0x203e20, 0x100a20)]⟩
  | _ => none

@[refine_layout] def frameAtG0 : Label.G0 → Refine.Activation → List Refine.Atom
  | .l106390 => fun fr =>
      [.gpr 4 fr.rsp, .reg 22 ⟨1, 0⟩, .gpr 1 fr.rcx, .gpr 2 fr.rdx, .gpr 3 fr.rbx, .gpr 5 fr.rbp,
       .gpr 6 fr.rsi, .gpr 7 fr.rdi, .gpr 8 fr.r8, .gpr 9 fr.r9, .gpr 12 fr.r12, .gpr 13 fr.r13,
       .gpr 14 fr.r14, .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x608) 0x608,
       .fact (fr.low.toNat + 0x608 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x203dd0 8, .mem 0x203dd0 64 0x12a820, .readable 0x203de0 8,
       .mem 0x203de0 64 0x129770, .readable 0x203e10 8, .mem 0x203e10 64 0x12a700,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204430 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203dd0)]
  | .l1063a7 => fun fr =>
      [.gpr 4 (fr.rsp - 0x158), .reg 22 ⟨1, 0⟩, .gpr 1 fr.rcx, .gpr 2 fr.rdx, .gpr 3 fr.rbx,
       .gpr 5 fr.rbp, .gpr 6 fr.rsi, .gpr 7 fr.rdi, .gpr 8 fr.r8, .gpr 9 fr.r9, .gpr 12 fr.r12,
       .gpr 13 fr.r13, .gpr 14 fr.r14, .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x20) 64 fr.rbx, .mem (fr.rsp - 0x18) 64 fr.r12,
       .mem (fr.rsp - 0x10) 64 fr.r14, .mem (fr.rsp - 0x8) 64 fr.r15, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x608) 0x608, .fact (fr.low.toNat + 0x608 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203dd0 8, .mem 0x203dd0 64 0x12a820,
       .readable 0x203de0 8, .mem 0x203de0 64 0x129770, .readable 0x203e10 8,
       .mem 0x203e10 64 0x12a700, .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204430 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203dd0)]
  | .l1063c4 => fun fr =>
      [.gpr 4 (fr.rsp - 0x158), .reg 22 ⟨1, 0⟩, .gpr 2 fr.rdx, .gpr 3 fr.rbx, .gpr 5 fr.rbp,
       .gpr 6 fr.rsi, .gpr 7 fr.rdi, .gpr 9 fr.r9, .gpr 12 fr.r12, .gpr 13 fr.r13, .gpr 14 fr.r14,
       .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩,
       .mem (fr.rsp - 0x20) 64 fr.rbx, .mem (fr.rsp - 0x18) 64 fr.r12,
       .mem (fr.rsp - 0x10) 64 fr.r14, .mem (fr.rsp - 0x8) 64 fr.r15, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x608) 0x608, .fact (fr.low.toNat + 0x608 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203dd0 8, .mem 0x203dd0 64 0x12a820,
       .readable 0x203de0 8, .mem 0x203de0 64 0x129770, .readable 0x203e10 8,
       .mem 0x203e10 64 0x12a700, .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204430 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203dd0)]
  | .l1063d2 => fun fr =>
      [.gpr 4 (fr.rsp - 0x158), .reg 22 ⟨1, 0⟩, .gpr 2 fr.rdx, .gpr 3 fr.rbx, .gpr 5 fr.rbp,
       .gpr 6 fr.rsi, .gpr 7 fr.rdi, .gpr 9 fr.r9, .gpr 12 fr.r12, .gpr 13 fr.r13, .gpr 14 fr.r14,
       .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩,
       .mem (fr.rsp - 0x20) 64 fr.rbx, .mem (fr.rsp - 0x18) 64 fr.r12,
       .mem (fr.rsp - 0x10) 64 fr.r14, .mem (fr.rsp - 0x8) 64 fr.r15, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x608) 0x608, .fact (fr.low.toNat + 0x608 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203dd0 8, .mem 0x203dd0 64 0x12a820,
       .readable 0x203de0 8, .mem 0x203de0 64 0x129770, .readable 0x203e10 8,
       .mem 0x203e10 64 0x12a700, .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204430 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203dd0)]
  | .l106409 => fun fr =>
      [.gpr 4 (fr.rsp - 0x158), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rsi, .gpr 5 fr.rbp, .gpr 13 fr.r13,
       .gpr 14 fr.rdx, .gpr 15 fr.rdi, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x20) 64 fr.rbx, .mem (fr.rsp - 0x18) 64 fr.r12,
       .mem (fr.rsp - 0x10) 64 fr.r14, .mem (fr.rsp - 0x8) 64 fr.r15, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x608) 0x608, .fact (fr.low.toNat + 0x608 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203dd0 8, .mem 0x203dd0 64 0x12a820,
       .readable 0x203de0 8, .mem 0x203de0 64 0x129770, .readable 0x203e20 8,
       .mem 0x203e20 64 0x100a20, .fact (0x204430 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203dd0)]
  | .l10641d => fun fr =>
      [.gpr 4 (fr.rsp - 0x158), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rsi, .gpr 5 fr.rbp, .gpr 13 fr.r13,
       .gpr 14 fr.rdx, .gpr 15 fr.rdi, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x20) 64 fr.rbx, .mem (fr.rsp - 0x18) 64 fr.r12,
       .mem (fr.rsp - 0x10) 64 fr.r14, .mem (fr.rsp - 0x8) 64 fr.r15, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x608) 0x608, .fact (fr.low.toNat + 0x608 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204430 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l1064f4 => fun fr =>
      [.gpr 4 (fr.rsp - 0x158), .reg 22 ⟨1, 0⟩, .gpr 5 fr.rbp, .gpr 13 fr.r13, .gpr 14 fr.rdx,
       .gpr 15 fr.rdi, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩,
       .mem (fr.rsp - 0x20) 64 fr.rbx, .mem (fr.rsp - 0x18) 64 fr.r12,
       .mem (fr.rsp - 0x10) 64 fr.r14, .mem (fr.rsp - 0x8) 64 fr.r15, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x608) 0x608, .fact (fr.low.toNat + 0x608 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204430 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l106514 => fun fr =>
      [.gpr 4 (fr.rsp - 0x158), .reg 22 ⟨1, 0⟩, .gpr 5 fr.rbp, .gpr 13 fr.r13, .gpr 14 fr.rdx,
       .gpr 15 fr.rdi, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩,
       .mem (fr.rsp - 0x20) 64 fr.rbx, .mem (fr.rsp - 0x18) 64 fr.r12,
       .mem (fr.rsp - 0x10) 64 fr.r14, .mem (fr.rsp - 0x8) 64 fr.r15, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x608) 0x608, .fact (fr.low.toNat + 0x608 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204430 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l106518 => fun fr =>
      [.gpr 4 (fr.rsp - 0x158), .reg 22 ⟨1, 0⟩, .gpr 5 fr.rbp, .gpr 13 fr.r13, .gpr 14 fr.rdx,
       .gpr 15 fr.rdi, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩,
       .mem (fr.rsp - 0x20) 64 fr.rbx, .mem (fr.rsp - 0x18) 64 fr.r12,
       .mem (fr.rsp - 0x10) 64 fr.r14, .mem (fr.rsp - 0x8) 64 fr.r15, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x608) 0x608, .fact (fr.low.toNat + 0x608 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8)]
  | .l106548 => fun fr =>
      [.gpr 4 (fr.rsp - 0x158), .reg 22 ⟨1, 0⟩, .gpr 5 fr.rbp, .gpr 7 fr.rdi, .gpr 13 fr.r13,
       .gpr 14 fr.rdx, .gpr 15 fr.rdi, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x20) 64 fr.rbx, .mem (fr.rsp - 0x18) 64 fr.r12,
       .mem (fr.rsp - 0x10) 64 fr.r14, .mem (fr.rsp - 0x8) 64 fr.r15, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x608) 0x608, .fact (fr.low.toNat + 0x608 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8)]
  | .l106560 => fun fr =>
      [.gpr 4 (fr.rsp - 0x158), .reg 22 ⟨1, 0⟩, .gpr 5 fr.rbp, .gpr 7 fr.rdi, .gpr 13 fr.r13,
       .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩,
       .mem (fr.rsp - 0x20) 64 fr.rbx, .mem (fr.rsp - 0x18) 64 fr.r12,
       .mem (fr.rsp - 0x10) 64 fr.r14, .mem (fr.rsp - 0x8) 64 fr.r15, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x608) 0x608, .fact (fr.low.toNat + 0x608 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8)]
  | .l106565 => fun fr =>
      [.gpr 4 (fr.rsp - 0x158), .reg 22 ⟨1, 0⟩, .gpr 5 fr.rbp, .gpr 7 fr.rdi, .gpr 13 fr.r13,
       .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩,
       .mem (fr.rsp - 0x20) 64 fr.rbx, .mem (fr.rsp - 0x18) 64 fr.r12,
       .mem (fr.rsp - 0x10) 64 fr.r14, .mem (fr.rsp - 0x8) 64 fr.r15, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x608) 0x608, .fact (fr.low.toNat + 0x608 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8)]
  | .l10657a => fun fr =>
      [.gpr 4 (fr.rsp - 0x158), .reg 22 ⟨1, 0⟩, .gpr 5 fr.rbp, .gpr 13 fr.r13, .gpr 14 fr.rdx,
       .gpr 15 fr.rdi, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩,
       .mem (fr.rsp - 0x20) 64 fr.rbx, .mem (fr.rsp - 0x18) 64 fr.r12,
       .mem (fr.rsp - 0x10) 64 fr.r14, .mem (fr.rsp - 0x8) 64 fr.r15, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x608) 0x608, .fact (fr.low.toNat + 0x608 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204430 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | _ => fun _ => []

def labelFrame : Label → Option Refine.LabelFrame
  | .g0 l => labelFrameG0 l
  | _ => none

@[refine_layout] def frameAt : Label → Refine.Activation → List Refine.Atom
  | .g0 l => frameAtG0 l
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

def closureCode : CodeMap := sectionCode textSection [(0xa20, 0x2), (0x6390, 0x21c),
    (0x145f0, 0x2d4), (0x14930, 0x18a), (0x15950, 0x1000), (0x16950, 0x1000), (0x17950, 0x1000),
    (0x18950, 0x1000), (0x19950, 0xc17), (0x1f780, 0xbc8), (0x205b0, 0x97b), (0x21480, 0x152),
    (0x27d50, 0x11), (0x295a0, 0x52), (0x29770, 0x2c), (0x2a700, 0x45), (0x2a820, 0x2f)]

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
    (hcore : Refine.Atom.All code (lifted.locationOf .l106390 initial).arguments initial.external
      (core.atoms lab c fr p))
    (hstart : core.start lab = .l106390 := by rfl)
    (hentry : ∀ fr, atoms .l106390 fr = frameInfo.entryAtoms fr := by intro _; rfl)
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

end Fn106390

end K256.Proofs.Sec1.LIR
