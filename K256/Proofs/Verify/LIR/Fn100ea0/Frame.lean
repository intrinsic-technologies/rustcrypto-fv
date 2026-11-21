import K256.Proofs.Verify.LIR.Program
import K256.Proofs.Common.Refine.Contract
import K256.Proofs.Common.Refine.Lemma.SysVEntry

namespace K256.Proofs.Verify.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Sec1.LIR K256.Proofs.Generate.LIR K256.Proofs.Ecdh.LIR

namespace Fn100ea0

def frameInfo : Refine.FrameInfo where
  entry := 0x100ea0
  frameBytes := 0x118
  stackBytes := some 0x8a0
  slots := [(3, 0x30), (5, 0x8), (12, 0x28), (13, 0x20), (14, 0x18), (15, 0x10)]
  preserved := [3, 5, 12, 13, 14, 15]
  fpPreserved := [39, 50, 51]
  clobbers := [0, 1, 2, 6, 7, 8, 9, 10, 11]
  callSlots := [(0x203dc8, 0x12965d), (0x203dd0, 0x12a820), (0x203de0, 0x129770), (0x203e10, 0x12a700), (0x203e20, 0x100a20)]

def labelFrameG1 : Label.G1 → Option Refine.LabelFrame
  | .l100ea0 => some ⟨0x0, [(1, 1), (2, 2), (3, 3), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9),
      (12, 12), (13, 13), (14, 14), (15, 15), (39, 39), (50, 50),
      (51, 51)], [], [(0x203dc8, 0x12965d), (0x203dd0, 0x12a820), (0x203de0, 0x129770),
      (0x203e10, 0x12a700), (0x203e20, 0x100a20)]⟩
  | .l100f18 => some ⟨0x118, [(0, 1), (3, 3), (6, 6), (8, 8), (9, 9), (11, 2), (12, 12), (39, 39),
      (50, 50), (51, 51)], [(0x58, 7), (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15),
      (0x8, 5)], [(0x203dc8, 0x12965d), (0x203dd0, 0x12a820), (0x203de0, 0x129770),
      (0x203e10, 0x12a700), (0x203e20, 0x100a20)]⟩
  | .l100f75 => some ⟨0x118, [(0, 1), (8, 8), (9, 9), (11, 2), (12, 12), (39, 39), (50, 50),
      (51, 51)], [(0x60, 6), (0x58, 7), (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15),
      (0x8, 5)], [(0x203dc8, 0x12965d), (0x203dd0, 0x12a820), (0x203de0, 0x129770),
      (0x203e10, 0x12a700), (0x203e20, 0x100a20)]⟩
  | .l100f82 => some ⟨0x118, [(0, 1), (8, 8), (9, 9), (11, 2), (12, 12), (39, 39), (50, 50),
      (51, 51)], [(0x60, 6), (0x58, 7), (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15),
      (0x8, 5)], [(0x203dc8, 0x12965d), (0x203dd0, 0x12a820), (0x203de0, 0x129770),
      (0x203e10, 0x12a700), (0x203e20, 0x100a20)]⟩
  | .l101003 => some ⟨0x118, [(0, 1), (8, 8), (11, 2), (12, 12), (39, 39), (50, 50),
      (51, 51)], [(0x70, 9), (0x68, 2), (0x60, 6), (0x58, 7), (0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203dc8, 0x12965d), (0x203dd0, 0x12a820),
      (0x203de0, 0x129770), (0x203e10, 0x12a700), (0x203e20, 0x100a20)]⟩
  | .l101011 => some ⟨0x118, [(0, 1), (8, 8), (11, 2), (12, 12), (39, 39), (50, 50),
      (51, 51)], [(0x70, 9), (0x68, 2), (0x60, 6), (0x58, 7), (0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203dc8, 0x12965d), (0x203dd0, 0x12a820),
      (0x203de0, 0x129770), (0x203e10, 0x12a700), (0x203e20, 0x100a20)]⟩
  | .l101023 => some ⟨0x118, [(0, 1), (8, 8), (11, 2), (12, 12), (39, 39), (50, 50),
      (51, 51)], [(0x70, 9), (0x68, 2), (0x60, 6), (0x58, 7), (0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203dc8, 0x12965d), (0x203dd0, 0x12a820),
      (0x203de0, 0x129770), (0x203e10, 0x12a700), (0x203e20, 0x100a20)]⟩
  | .l101026 => some ⟨0x118, [(0, 1), (8, 8), (11, 2), (12, 12), (39, 39), (50, 50),
      (51, 51)], [(0x70, 9), (0x68, 2), (0x60, 6), (0x58, 7), (0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203dc8, 0x12965d), (0x203dd0, 0x12a820),
      (0x203de0, 0x129770), (0x203e10, 0x12a700), (0x203e20, 0x100a20)]⟩
  | .l10106a => some ⟨0x118, [(12, 12), (39, 39), (50, 50), (51, 51)], [(0x70, 9), (0x68, 2),
      (0x60, 6), (0x58, 7), (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15),
      (0x8, 5)], [(0x203dc8, 0x12965d), (0x203dd0, 0x12a820), (0x203de0, 0x129770),
      (0x203e10, 0x12a700), (0x203e20, 0x100a20)]⟩
  | .l101072 => some ⟨0x118, [(12, 12), (39, 39), (50, 50), (51, 51)], [(0x70, 9), (0x68, 2),
      (0x60, 6), (0x58, 7), (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15),
      (0x8, 5)], [(0x203dc8, 0x12965d), (0x203dd0, 0x12a820), (0x203de0, 0x129770),
      (0x203e10, 0x12a700), (0x203e20, 0x100a20)]⟩
  | .l1010ae => some ⟨0x118, [(12, 12), (39, 39), (50, 50), (51, 51)], [(0x70, 9), (0x68, 2),
      (0x60, 6), (0x58, 7), (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15),
      (0x8, 5)], [(0x203dc8, 0x12965d), (0x203dd0, 0x12a820), (0x203de0, 0x129770),
      (0x203e10, 0x12a700), (0x203e20, 0x100a20)]⟩
  | .l10126c => some ⟨0x118, [(14, 7), (39, 39), (50, 50), (51, 51)], [(0x70, 9), (0x68, 2),
      (0x60, 6), (0x58, 7), (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15),
      (0x8, 5)], [(0x203dd0, 0x12a820), (0x203de0, 0x129770), (0x203e10, 0x12a700),
      (0x203e20, 0x100a20)]⟩
  | .l101295 => some ⟨0x118, [(3, 2), (14, 7), (39, 39), (50, 50), (51, 51)], [(0x70, 9), (0x68, 2),
      (0x60, 6), (0x58, 7), (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15),
      (0x8, 5)], [(0x203dd0, 0x12a820), (0x203e10, 0x12a700)]⟩
  | .l10132a => some ⟨0x118, [(3, 2), (14, 7), (39, 39), (50, 50), (51, 51)], [(0xb0, 6), (0xa8, 2),
      (0x98, 2), (0x90, 9), (0x70, 9), (0x68, 2), (0x60, 6), (0x58, 7), (0x30, 3), (0x28, 12),
      (0x20, 13), (0x18, 14), (0x10, 15), (0x8, 5)], []⟩
  | .l10138a => some ⟨0x118, [(0, 1), (3, 3), (6, 6), (8, 8), (9, 9), (11, 2), (12, 12), (39, 39),
      (50, 50), (51, 51)], [(0x58, 7), (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15),
      (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l1013a0 => some ⟨0x118, [(0, 1), (8, 8), (9, 9), (11, 2), (12, 12), (39, 39), (50, 50),
      (51, 51)], [(0x60, 6), (0x58, 7), (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15),
      (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | _ => none

@[refine_layout] def frameAtG1 : Label.G1 → Refine.Activation → List Refine.Atom
  | .l100ea0 => fun fr =>
      [.gpr 4 fr.rsp, .reg 22 ⟨1, 0⟩, .gpr 1 fr.rcx, .gpr 2 fr.rdx, .gpr 3 fr.rbx, .gpr 5 fr.rbp,
       .gpr 6 fr.rsi, .gpr 7 fr.rdi, .gpr 8 fr.r8, .gpr 9 fr.r9, .gpr 12 fr.r12, .gpr 13 fr.r13,
       .gpr 14 fr.r14, .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x8a0) 0x8a0,
       .fact (fr.low.toNat + 0x8a0 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x203dc8 8, .mem 0x203dc8 64 0x12965d, .readable 0x203dd0 8,
       .mem 0x203dd0 64 0x12a820, .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e10 8, .mem 0x203e10 64 0x12a700, .readable 0x203e20 8,
       .mem 0x203e20 64 0x100a20, .fact (0x2046c8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203dc8)]
  | .l100f18 => fun fr =>
      [.gpr 4 (fr.rsp - 0x118), .reg 22 ⟨1, 0⟩, .gpr 0 fr.rcx, .gpr 3 fr.rbx, .gpr 6 fr.rsi,
       .gpr 8 fr.r8, .gpr 9 fr.r9, .gpr 11 fr.rdx, .gpr 12 fr.r12, .reg 39 ⟨32, fr.mxcsr⟩,
       .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x58) 64 fr.rdi,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x8a0) 0x8a0, .fact (fr.low.toNat + 0x8a0 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203dc8 8, .mem 0x203dc8 64 0x12965d,
       .readable 0x203dd0 8, .mem 0x203dd0 64 0x12a820, .readable 0x203de0 8,
       .mem 0x203de0 64 0x129770, .readable 0x203e10 8, .mem 0x203e10 64 0x12a700,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x2046c8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203dc8)]
  | .l100f75 => fun fr =>
      [.gpr 4 (fr.rsp - 0x118), .reg 22 ⟨1, 0⟩, .gpr 0 fr.rcx, .gpr 8 fr.r8, .gpr 9 fr.r9,
       .gpr 11 fr.rdx, .gpr 12 fr.r12, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x60) 64 fr.rsi, .mem (fr.rsp - 0x58) 64 fr.rdi,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x8a0) 0x8a0, .fact (fr.low.toNat + 0x8a0 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203dc8 8, .mem 0x203dc8 64 0x12965d,
       .readable 0x203dd0 8, .mem 0x203dd0 64 0x12a820, .readable 0x203de0 8,
       .mem 0x203de0 64 0x129770, .readable 0x203e10 8, .mem 0x203e10 64 0x12a700,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x2046c8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203dc8)]
  | .l100f82 => fun fr =>
      [.gpr 4 (fr.rsp - 0x118), .reg 22 ⟨1, 0⟩, .gpr 0 fr.rcx, .gpr 8 fr.r8, .gpr 9 fr.r9,
       .gpr 11 fr.rdx, .gpr 12 fr.r12, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x60) 64 fr.rsi, .mem (fr.rsp - 0x58) 64 fr.rdi,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x8a0) 0x8a0, .fact (fr.low.toNat + 0x8a0 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203dc8 8, .mem 0x203dc8 64 0x12965d,
       .readable 0x203dd0 8, .mem 0x203dd0 64 0x12a820, .readable 0x203de0 8,
       .mem 0x203de0 64 0x129770, .readable 0x203e10 8, .mem 0x203e10 64 0x12a700,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x2046c8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203dc8)]
  | .l101003 => fun fr =>
      [.gpr 4 (fr.rsp - 0x118), .reg 22 ⟨1, 0⟩, .gpr 0 fr.rcx, .gpr 8 fr.r8, .gpr 11 fr.rdx,
       .gpr 12 fr.r12, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩,
       .mem (fr.rsp - 0x70) 64 fr.r9, .mem (fr.rsp - 0x68) 64 fr.rdx,
       .mem (fr.rsp - 0x60) 64 fr.rsi, .mem (fr.rsp - 0x58) 64 fr.rdi,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x8a0) 0x8a0, .fact (fr.low.toNat + 0x8a0 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203dc8 8, .mem 0x203dc8 64 0x12965d,
       .readable 0x203dd0 8, .mem 0x203dd0 64 0x12a820, .readable 0x203de0 8,
       .mem 0x203de0 64 0x129770, .readable 0x203e10 8, .mem 0x203e10 64 0x12a700,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x2046c8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203dc8)]
  | .l101011 => fun fr =>
      [.gpr 4 (fr.rsp - 0x118), .reg 22 ⟨1, 0⟩, .gpr 0 fr.rcx, .gpr 8 fr.r8, .gpr 11 fr.rdx,
       .gpr 12 fr.r12, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩,
       .mem (fr.rsp - 0x70) 64 fr.r9, .mem (fr.rsp - 0x68) 64 fr.rdx,
       .mem (fr.rsp - 0x60) 64 fr.rsi, .mem (fr.rsp - 0x58) 64 fr.rdi,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x8a0) 0x8a0, .fact (fr.low.toNat + 0x8a0 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203dc8 8, .mem 0x203dc8 64 0x12965d,
       .readable 0x203dd0 8, .mem 0x203dd0 64 0x12a820, .readable 0x203de0 8,
       .mem 0x203de0 64 0x129770, .readable 0x203e10 8, .mem 0x203e10 64 0x12a700,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x2046c8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203dc8)]
  | .l101023 => fun fr =>
      [.gpr 4 (fr.rsp - 0x118), .reg 22 ⟨1, 0⟩, .gpr 0 fr.rcx, .gpr 8 fr.r8, .gpr 11 fr.rdx,
       .gpr 12 fr.r12, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩,
       .mem (fr.rsp - 0x70) 64 fr.r9, .mem (fr.rsp - 0x68) 64 fr.rdx,
       .mem (fr.rsp - 0x60) 64 fr.rsi, .mem (fr.rsp - 0x58) 64 fr.rdi,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x8a0) 0x8a0, .fact (fr.low.toNat + 0x8a0 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203dc8 8, .mem 0x203dc8 64 0x12965d,
       .readable 0x203dd0 8, .mem 0x203dd0 64 0x12a820, .readable 0x203de0 8,
       .mem 0x203de0 64 0x129770, .readable 0x203e10 8, .mem 0x203e10 64 0x12a700,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x2046c8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203dc8)]
  | .l101026 => fun fr =>
      [.gpr 4 (fr.rsp - 0x118), .reg 22 ⟨1, 0⟩, .gpr 0 fr.rcx, .gpr 8 fr.r8, .gpr 11 fr.rdx,
       .gpr 12 fr.r12, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩,
       .mem (fr.rsp - 0x70) 64 fr.r9, .mem (fr.rsp - 0x68) 64 fr.rdx,
       .mem (fr.rsp - 0x60) 64 fr.rsi, .mem (fr.rsp - 0x58) 64 fr.rdi,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x8a0) 0x8a0, .fact (fr.low.toNat + 0x8a0 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203dc8 8, .mem 0x203dc8 64 0x12965d,
       .readable 0x203dd0 8, .mem 0x203dd0 64 0x12a820, .readable 0x203de0 8,
       .mem 0x203de0 64 0x129770, .readable 0x203e10 8, .mem 0x203e10 64 0x12a700,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x2046c8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203dc8)]
  | .l10106a => fun fr =>
      [.gpr 4 (fr.rsp - 0x118), .reg 22 ⟨1, 0⟩, .gpr 12 fr.r12, .reg 39 ⟨32, fr.mxcsr⟩,
       .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x70) 64 fr.r9,
       .mem (fr.rsp - 0x68) 64 fr.rdx, .mem (fr.rsp - 0x60) 64 fr.rsi,
       .mem (fr.rsp - 0x58) 64 fr.rdi, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x8a0) 0x8a0,
       .fact (fr.low.toNat + 0x8a0 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x203dc8 8, .mem 0x203dc8 64 0x12965d, .readable 0x203dd0 8,
       .mem 0x203dd0 64 0x12a820, .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e10 8, .mem 0x203e10 64 0x12a700, .readable 0x203e20 8,
       .mem 0x203e20 64 0x100a20, .fact (0x2046c8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203dc8)]
  | .l101072 => fun fr =>
      [.gpr 4 (fr.rsp - 0x118), .reg 22 ⟨1, 0⟩, .gpr 12 fr.r12, .reg 39 ⟨32, fr.mxcsr⟩,
       .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x70) 64 fr.r9,
       .mem (fr.rsp - 0x68) 64 fr.rdx, .mem (fr.rsp - 0x60) 64 fr.rsi,
       .mem (fr.rsp - 0x58) 64 fr.rdi, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x8a0) 0x8a0,
       .fact (fr.low.toNat + 0x8a0 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x203dc8 8, .mem 0x203dc8 64 0x12965d, .readable 0x203dd0 8,
       .mem 0x203dd0 64 0x12a820, .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e10 8, .mem 0x203e10 64 0x12a700, .readable 0x203e20 8,
       .mem 0x203e20 64 0x100a20, .fact (0x2046c8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203dc8)]
  | .l1010ae => fun fr =>
      [.gpr 4 (fr.rsp - 0x118), .reg 22 ⟨1, 0⟩, .gpr 12 fr.r12, .reg 39 ⟨32, fr.mxcsr⟩,
       .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x70) 64 fr.r9,
       .mem (fr.rsp - 0x68) 64 fr.rdx, .mem (fr.rsp - 0x60) 64 fr.rsi,
       .mem (fr.rsp - 0x58) 64 fr.rdi, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x8a0) 0x8a0,
       .fact (fr.low.toNat + 0x8a0 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x203dc8 8, .mem 0x203dc8 64 0x12965d, .readable 0x203dd0 8,
       .mem 0x203dd0 64 0x12a820, .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e10 8, .mem 0x203e10 64 0x12a700, .readable 0x203e20 8,
       .mem 0x203e20 64 0x100a20, .fact (0x2046c8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203dc8)]
  | .l10126c => fun fr =>
      [.gpr 4 (fr.rsp - 0x118), .reg 22 ⟨1, 0⟩, .gpr 14 fr.rdi, .reg 39 ⟨32, fr.mxcsr⟩,
       .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x70) 64 fr.r9,
       .mem (fr.rsp - 0x68) 64 fr.rdx, .mem (fr.rsp - 0x60) 64 fr.rsi,
       .mem (fr.rsp - 0x58) 64 fr.rdi, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x8a0) 0x8a0,
       .fact (fr.low.toNat + 0x8a0 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x203dd0 8, .mem 0x203dd0 64 0x12a820, .readable 0x203de0 8,
       .mem 0x203de0 64 0x129770, .readable 0x203e10 8, .mem 0x203e10 64 0x12a700,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x2046c8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203dd0)]
  | .l101295 => fun fr =>
      [.gpr 4 (fr.rsp - 0x118), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rdx, .gpr 14 fr.rdi,
       .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩,
       .mem (fr.rsp - 0x70) 64 fr.r9, .mem (fr.rsp - 0x68) 64 fr.rdx,
       .mem (fr.rsp - 0x60) 64 fr.rsi, .mem (fr.rsp - 0x58) 64 fr.rdi,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x8a0) 0x8a0, .fact (fr.low.toNat + 0x8a0 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203dd0 8, .mem 0x203dd0 64 0x12a820,
       .readable 0x203e10 8, .mem 0x203e10 64 0x12a700,
       .fact (0x2046b8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203dd0)]
  | .l10132a => fun fr =>
      [.gpr 4 (fr.rsp - 0x118), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rdx, .gpr 14 fr.rdi,
       .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩,
       .mem (fr.rsp - 0xb0) 64 fr.rsi, .mem (fr.rsp - 0xa8) 64 fr.rdx,
       .mem (fr.rsp - 0x98) 64 fr.rdx, .mem (fr.rsp - 0x90) 64 fr.r9, .mem (fr.rsp - 0x70) 64 fr.r9,
       .mem (fr.rsp - 0x68) 64 fr.rdx, .mem (fr.rsp - 0x60) 64 fr.rsi,
       .mem (fr.rsp - 0x58) 64 fr.rdi, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x8a0) 0x8a0,
       .fact (fr.low.toNat + 0x8a0 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l10138a => fun fr =>
      [.gpr 4 (fr.rsp - 0x118), .reg 22 ⟨1, 0⟩, .gpr 0 fr.rcx, .gpr 3 fr.rbx, .gpr 6 fr.rsi,
       .gpr 8 fr.r8, .gpr 9 fr.r9, .gpr 11 fr.rdx, .gpr 12 fr.r12, .reg 39 ⟨32, fr.mxcsr⟩,
       .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x58) 64 fr.rdi,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x8a0) 0x8a0, .fact (fr.low.toNat + 0x8a0 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x2046c8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l1013a0 => fun fr =>
      [.gpr 4 (fr.rsp - 0x118), .reg 22 ⟨1, 0⟩, .gpr 0 fr.rcx, .gpr 8 fr.r8, .gpr 9 fr.r9,
       .gpr 11 fr.rdx, .gpr 12 fr.r12, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x60) 64 fr.rsi, .mem (fr.rsp - 0x58) 64 fr.rdi,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x8a0) 0x8a0, .fact (fr.low.toNat + 0x8a0 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x2046c8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | _ => fun _ => []

def labelFrameG2 : Label.G2 → Option Refine.LabelFrame
  | .l1013b8 => some ⟨0x118, [(0, 1), (8, 8), (11, 2), (12, 12), (39, 39), (50, 50),
      (51, 51)], [(0x70, 9), (0x68, 2), (0x60, 6), (0x58, 7), (0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l1013c9 => some ⟨0x118, [(12, 12), (39, 39), (50, 50), (51, 51)], [(0x70, 9), (0x68, 2),
      (0x60, 6), (0x58, 7), (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15),
      (0x8, 5)], [(0x203e20, 0x100a20)]⟩
  | _ => none

@[refine_layout] def frameAtG2 : Label.G2 → Refine.Activation → List Refine.Atom
  | .l1013b8 => fun fr =>
      [.gpr 4 (fr.rsp - 0x118), .reg 22 ⟨1, 0⟩, .gpr 0 fr.rcx, .gpr 8 fr.r8, .gpr 11 fr.rdx,
       .gpr 12 fr.r12, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩,
       .mem (fr.rsp - 0x70) 64 fr.r9, .mem (fr.rsp - 0x68) 64 fr.rdx,
       .mem (fr.rsp - 0x60) 64 fr.rsi, .mem (fr.rsp - 0x58) 64 fr.rdi,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x8a0) 0x8a0, .fact (fr.low.toNat + 0x8a0 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x2046c8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l1013c9 => fun fr =>
      [.gpr 4 (fr.rsp - 0x118), .reg 22 ⟨1, 0⟩, .gpr 12 fr.r12, .reg 39 ⟨32, fr.mxcsr⟩,
       .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x70) 64 fr.r9,
       .mem (fr.rsp - 0x68) 64 fr.rdx, .mem (fr.rsp - 0x60) 64 fr.rsi,
       .mem (fr.rsp - 0x58) 64 fr.rdi, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x8a0) 0x8a0,
       .fact (fr.low.toNat + 0x8a0 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x2046c8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203e20)]
  | _ => fun _ => []

def labelFrame : Label → Option Refine.LabelFrame
  | .g1 l => labelFrameG1 l
  | .g2 l => labelFrameG2 l
  | _ => none

@[refine_layout] def frameAt : Label → Refine.Activation → List Refine.Atom
  | .g1 l => frameAtG1 l
  | .g2 l => frameAtG2 l
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

def closureCode : CodeMap := sectionCode textSection [(0x0, 0x176), (0xa20, 0x2), (0xea0, 0x569),
    (0x3f30, 0x2c9), (0x4200, 0x5cd), (0x47d0, 0x193), (0x4970, 0x317), (0x65b0, 0x1e4),
    (0x7a50, 0x53d), (0x218e0, 0x1000), (0x228e0, 0x1000), (0x238e0, 0x819), (0x27d70, 0x79),
    (0x27df0, 0xa4), (0x27ea0, 0xa3), (0x2873d, 0x35), (0x29560, 0x34), (0x295f2, 0x3d),
    (0x2965d, 0xee), (0x29770, 0x2c), (0x29b60, 0xc8), (0x2a700, 0x45), (0x2a820, 0x2f)]

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
    (hcore : Refine.Atom.All code (lifted.locationOf .l100ea0 initial).arguments initial.external
      (core.atoms lab c fr p))
    (hstart : core.start lab = .l100ea0 := by rfl)
    (hentry : ∀ fr, atoms .l100ea0 fr = frameInfo.entryAtoms fr := by intro _; rfl)
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

end Fn100ea0

end K256.Proofs.Verify.LIR
