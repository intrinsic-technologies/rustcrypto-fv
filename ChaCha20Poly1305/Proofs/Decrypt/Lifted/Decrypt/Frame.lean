import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Program
import ChaCha20Poly1305.Proofs.Common.Refine.Contract
import ChaCha20Poly1305.Proofs.Common.Refine.Lemma.SysVEntry

namespace ChaCha20Poly1305.Proofs.Decrypt.Lifted

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift

namespace Decrypt

def frameInfo : Refine.FrameInfo where
  entry := 0x1014c0
  frameBytes := 0x88
  stackBytes := some 0x3f0
  slots := [(3, 0x30), (5, 0x8), (12, 0x28), (13, 0x20), (14, 0x18), (15, 0x10)]
  preserved := [3, 5, 12, 13, 14, 15]
  fpPreserved := [39, 50, 51]
  clobbers := [0, 1, 2, 6, 7, 8, 9, 10, 11]
  callSlots := [(0x2013a8, 0x102dc0), (0x2013e0, 0x102d70)]

def labelFrameG1 : Label.G1 → Option Refine.LabelFrame
  | .l1014c0 => some ⟨0x0, [(1, 1), (2, 2), (3, 3), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9),
      (12, 12), (13, 13), (14, 14), (15, 15), (39, 39), (50, 50),
      (51, 51)], [], [(0x2013a8, 0x102dc0), (0x2013e0, 0x102d70)]⟩
  | .l101526 => some ⟨0x88, [(2, 2), (3, 3), (5, 5), (6, 6), (7, 7), (9, 9), (12, 12), (13, 1),
      (15, 15), (39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14),
      (0x10, 15), (0x8, 5)], [(0x2013a8, 0x102dc0), (0x2013e0, 0x102d70)]⟩
  | .l10152c => some ⟨0x88, [(2, 2), (3, 3), (5, 5), (6, 6), (7, 7), (9, 9), (12, 12), (13, 1),
      (15, 15), (39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14),
      (0x10, 15), (0x8, 5)], [(0x2013a8, 0x102dc0), (0x2013e0, 0x102d70)]⟩
  | .l10153a => some ⟨0x88, [(3, 9), (5, 5), (12, 6), (13, 1), (15, 2), (39, 39), (50, 50),
      (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15),
      (0x8, 5)], [(0x2013a8, 0x102dc0), (0x2013e0, 0x102d70)]⟩
  | .l101552 => some ⟨0x88, [(3, 9), (12, 6), (13, 1), (15, 2), (39, 39), (50, 50),
      (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15),
      (0x8, 5)], [(0x2013a8, 0x102dc0), (0x2013e0, 0x102d70)]⟩
  | .l101562 => some ⟨0x88, [(3, 9), (12, 6), (13, 1), (15, 2), (39, 39), (50, 50),
      (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15),
      (0x8, 5)], [(0x2013a8, 0x102dc0), (0x2013e0, 0x102d70)]⟩
  | .l101572 => some ⟨0x88, [(3, 9), (12, 6), (13, 1), (15, 2), (39, 39), (50, 50),
      (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15),
      (0x8, 5)], [(0x2013a8, 0x102dc0), (0x2013e0, 0x102d70)]⟩
  | .l10158b => some ⟨0x88, [(3, 9), (12, 6), (13, 1), (15, 2), (39, 39), (50, 50),
      (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15),
      (0x8, 5)], [(0x2013a8, 0x102dc0), (0x2013e0, 0x102d70)]⟩
  | .l101596 => some ⟨0x88, [(3, 9), (12, 6), (13, 1), (15, 2), (39, 39), (50, 50),
      (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15),
      (0x8, 5)], [(0x2013a8, 0x102dc0), (0x2013e0, 0x102d70)]⟩
  | .l1015d4 => some ⟨0x88, [(3, 9), (12, 6), (15, 2), (39, 39), (50, 50), (51, 51)], [(0x30, 3),
      (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15), (0x8, 5)], [(0x2013a8, 0x102dc0)]⟩
  | .l1015d8 => some ⟨0x88, [(3, 9), (12, 6), (15, 2), (39, 39), (50, 50), (51, 51)], [(0x30, 3),
      (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15), (0x8, 5)], [(0x2013a8, 0x102dc0)]⟩
  | .l1015e5 => some ⟨0x88, [(3, 9), (12, 6), (15, 2), (39, 39), (50, 50), (51, 51)], [(0x30, 3),
      (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15), (0x8, 5)], [(0x2013a8, 0x102dc0)]⟩
  | .l1015ed => some ⟨0x88, [(3, 9), (12, 6), (15, 2), (39, 39), (50, 50), (51, 51)], [(0x30, 3),
      (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15), (0x8, 5)], [(0x2013a8, 0x102dc0)]⟩
  | .l1015ff => some ⟨0x88, [(3, 9), (12, 6), (15, 2), (39, 39), (50, 50), (51, 51)], [(0x30, 3),
      (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15), (0x8, 5)], [(0x2013a8, 0x102dc0)]⟩
  | .l10160d => some ⟨0x88, [(3, 9), (12, 6), (15, 2), (39, 39), (50, 50), (51, 51)], [(0x30, 3),
      (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15), (0x8, 5)], []⟩
  | .l101611 => some ⟨0x88, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], []⟩
  | .l101616 => some ⟨0x88, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], []⟩
  | .l101625 => some ⟨0x88, [(3, 9), (12, 6), (15, 2), (39, 39), (50, 50), (51, 51)], [(0x30, 3),
      (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15), (0x8, 5)], []⟩
  | .l101639 => some ⟨0x88, [(2, 2), (3, 3), (5, 5), (6, 6), (7, 7), (9, 9), (12, 12), (13, 1),
      (15, 15), (39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14),
      (0x10, 15), (0x8, 5)], []⟩
  | .l10163b => some ⟨0x88, [(3, 9), (12, 6), (13, 1), (15, 2), (39, 39), (50, 50),
      (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15), (0x8, 5)], []⟩
  | _ => none

@[refine_layout] def frameAtG1 : Label.G1 → Refine.Activation → List Refine.Atom
  | .l1014c0 => fun fr =>
      [.gpr 4 fr.rsp, .reg 22 ⟨1, 0⟩, .gpr 1 fr.rcx, .gpr 2 fr.rdx, .gpr 3 fr.rbx, .gpr 5 fr.rbp,
       .gpr 6 fr.rsi, .gpr 7 fr.rdi, .gpr 8 fr.r8, .gpr 9 fr.r9, .gpr 12 fr.r12, .gpr 13 fr.r13,
       .gpr 14 fr.r14, .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x3f0) 0x3f0,
       .fact (fr.low.toNat + 0x3f0 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x2013a8 8, .mem 0x2013a8 64 0x102dc0, .readable 0x2013e0 8,
       .mem 0x2013e0 64 0x102d70, .fact (0x2017d8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x2013a8)]
  | .l101526 => fun fr =>
      [.gpr 4 (fr.rsp - 0x88), .reg 22 ⟨1, 0⟩, .gpr 2 fr.rdx, .gpr 3 fr.rbx, .gpr 5 fr.rbp,
       .gpr 6 fr.rsi, .gpr 7 fr.rdi, .gpr 9 fr.r9, .gpr 12 fr.r12, .gpr 13 fr.rcx, .gpr 15 fr.r15,
       .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x3f0) 0x3f0, .fact (fr.low.toNat + 0x3f0 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x2013a8 8, .mem 0x2013a8 64 0x102dc0,
       .readable 0x2013e0 8, .mem 0x2013e0 64 0x102d70,
       .fact (0x2017d8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x2013a8)]
  | .l10152c => fun fr =>
      [.gpr 4 (fr.rsp - 0x88), .reg 22 ⟨1, 0⟩, .gpr 2 fr.rdx, .gpr 3 fr.rbx, .gpr 5 fr.rbp,
       .gpr 6 fr.rsi, .gpr 7 fr.rdi, .gpr 9 fr.r9, .gpr 12 fr.r12, .gpr 13 fr.rcx, .gpr 15 fr.r15,
       .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x3f0) 0x3f0, .fact (fr.low.toNat + 0x3f0 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x2013a8 8, .mem 0x2013a8 64 0x102dc0,
       .readable 0x2013e0 8, .mem 0x2013e0 64 0x102d70,
       .fact (0x2017d8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x2013a8)]
  | .l10153a => fun fr =>
      [.gpr 4 (fr.rsp - 0x88), .reg 22 ⟨1, 0⟩, .gpr 3 fr.r9, .gpr 5 fr.rbp, .gpr 12 fr.rsi,
       .gpr 13 fr.rcx, .gpr 15 fr.rdx, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x3f0) 0x3f0, .fact (fr.low.toNat + 0x3f0 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x2013a8 8, .mem 0x2013a8 64 0x102dc0,
       .readable 0x2013e0 8, .mem 0x2013e0 64 0x102d70,
       .fact (0x2017d8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x2013a8)]
  | .l101552 => fun fr =>
      [.gpr 4 (fr.rsp - 0x88), .reg 22 ⟨1, 0⟩, .gpr 3 fr.r9, .gpr 12 fr.rsi, .gpr 13 fr.rcx,
       .gpr 15 fr.rdx, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x3f0) 0x3f0, .fact (fr.low.toNat + 0x3f0 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x2013a8 8, .mem 0x2013a8 64 0x102dc0,
       .readable 0x2013e0 8, .mem 0x2013e0 64 0x102d70,
       .fact (0x2017d8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x2013a8)]
  | .l101562 => fun fr =>
      [.gpr 4 (fr.rsp - 0x88), .reg 22 ⟨1, 0⟩, .gpr 3 fr.r9, .gpr 12 fr.rsi, .gpr 13 fr.rcx,
       .gpr 15 fr.rdx, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x3f0) 0x3f0, .fact (fr.low.toNat + 0x3f0 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x2013a8 8, .mem 0x2013a8 64 0x102dc0,
       .readable 0x2013e0 8, .mem 0x2013e0 64 0x102d70,
       .fact (0x2017d8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x2013a8)]
  | .l101572 => fun fr =>
      [.gpr 4 (fr.rsp - 0x88), .reg 22 ⟨1, 0⟩, .gpr 3 fr.r9, .gpr 12 fr.rsi, .gpr 13 fr.rcx,
       .gpr 15 fr.rdx, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x3f0) 0x3f0, .fact (fr.low.toNat + 0x3f0 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x2013a8 8, .mem 0x2013a8 64 0x102dc0,
       .readable 0x2013e0 8, .mem 0x2013e0 64 0x102d70,
       .fact (0x2017d8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x2013a8)]
  | .l10158b => fun fr =>
      [.gpr 4 (fr.rsp - 0x88), .reg 22 ⟨1, 0⟩, .gpr 3 fr.r9, .gpr 12 fr.rsi, .gpr 13 fr.rcx,
       .gpr 15 fr.rdx, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x3f0) 0x3f0, .fact (fr.low.toNat + 0x3f0 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x2013a8 8, .mem 0x2013a8 64 0x102dc0,
       .readable 0x2013e0 8, .mem 0x2013e0 64 0x102d70,
       .fact (0x2017d8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x2013a8)]
  | .l101596 => fun fr =>
      [.gpr 4 (fr.rsp - 0x88), .reg 22 ⟨1, 0⟩, .gpr 3 fr.r9, .gpr 12 fr.rsi, .gpr 13 fr.rcx,
       .gpr 15 fr.rdx, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x3f0) 0x3f0, .fact (fr.low.toNat + 0x3f0 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x2013a8 8, .mem 0x2013a8 64 0x102dc0,
       .readable 0x2013e0 8, .mem 0x2013e0 64 0x102d70,
       .fact (0x2017d8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x2013a8)]
  | .l1015d4 => fun fr =>
      [.gpr 4 (fr.rsp - 0x88), .reg 22 ⟨1, 0⟩, .gpr 3 fr.r9, .gpr 12 fr.rsi, .gpr 15 fr.rdx,
       .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x3f0) 0x3f0, .fact (fr.low.toNat + 0x3f0 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x2013a8 8, .mem 0x2013a8 64 0x102dc0,
       .fact (0x2017a0 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x2013a8)]
  | .l1015d8 => fun fr =>
      [.gpr 4 (fr.rsp - 0x88), .reg 22 ⟨1, 0⟩, .gpr 3 fr.r9, .gpr 12 fr.rsi, .gpr 15 fr.rdx,
       .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x3f0) 0x3f0, .fact (fr.low.toNat + 0x3f0 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x2013a8 8, .mem 0x2013a8 64 0x102dc0,
       .fact (0x2017a0 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x2013a8)]
  | .l1015e5 => fun fr =>
      [.gpr 4 (fr.rsp - 0x88), .reg 22 ⟨1, 0⟩, .gpr 3 fr.r9, .gpr 12 fr.rsi, .gpr 15 fr.rdx,
       .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x3f0) 0x3f0, .fact (fr.low.toNat + 0x3f0 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x2013a8 8, .mem 0x2013a8 64 0x102dc0,
       .fact (0x2017a0 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x2013a8)]
  | .l1015ed => fun fr =>
      [.gpr 4 (fr.rsp - 0x88), .reg 22 ⟨1, 0⟩, .gpr 3 fr.r9, .gpr 12 fr.rsi, .gpr 15 fr.rdx,
       .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x3f0) 0x3f0, .fact (fr.low.toNat + 0x3f0 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x2013a8 8, .mem 0x2013a8 64 0x102dc0,
       .fact (0x2017a0 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x2013a8)]
  | .l1015ff => fun fr =>
      [.gpr 4 (fr.rsp - 0x88), .reg 22 ⟨1, 0⟩, .gpr 3 fr.r9, .gpr 12 fr.rsi, .gpr 15 fr.rdx,
       .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x3f0) 0x3f0, .fact (fr.low.toNat + 0x3f0 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x2013a8 8, .mem 0x2013a8 64 0x102dc0,
       .fact (0x2017a0 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x2013a8)]
  | .l10160d => fun fr =>
      [.gpr 4 (fr.rsp - 0x88), .reg 22 ⟨1, 0⟩, .gpr 3 fr.r9, .gpr 12 fr.rsi, .gpr 15 fr.rdx,
       .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x3f0) 0x3f0, .fact (fr.low.toNat + 0x3f0 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8)]
  | .l101611 => fun fr =>
      [.gpr 4 (fr.rsp - 0x88), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x3f0) 0x3f0, .fact (fr.low.toNat + 0x3f0 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8)]
  | .l101616 => fun fr =>
      [.gpr 4 (fr.rsp - 0x88), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x3f0) 0x3f0, .fact (fr.low.toNat + 0x3f0 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8)]
  | .l101625 => fun fr =>
      [.gpr 4 (fr.rsp - 0x88), .reg 22 ⟨1, 0⟩, .gpr 3 fr.r9, .gpr 12 fr.rsi, .gpr 15 fr.rdx,
       .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x3f0) 0x3f0, .fact (fr.low.toNat + 0x3f0 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8)]
  | .l101639 => fun fr =>
      [.gpr 4 (fr.rsp - 0x88), .reg 22 ⟨1, 0⟩, .gpr 2 fr.rdx, .gpr 3 fr.rbx, .gpr 5 fr.rbp,
       .gpr 6 fr.rsi, .gpr 7 fr.rdi, .gpr 9 fr.r9, .gpr 12 fr.r12, .gpr 13 fr.rcx, .gpr 15 fr.r15,
       .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x3f0) 0x3f0, .fact (fr.low.toNat + 0x3f0 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8)]
  | .l10163b => fun fr =>
      [.gpr 4 (fr.rsp - 0x88), .reg 22 ⟨1, 0⟩, .gpr 3 fr.r9, .gpr 12 fr.rsi, .gpr 13 fr.rcx,
       .gpr 15 fr.rdx, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x3f0) 0x3f0, .fact (fr.low.toNat + 0x3f0 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8)]
  | _ => fun _ => []

def labelFrame : Label → Option Refine.LabelFrame
  | .g1 l => labelFrameG1 l
  | _ => none

@[refine_layout] def frameAt : Label → Refine.Activation → List Refine.Atom
  | .g1 l => frameAtG1 l
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

def closureCode : CodeMap := sectionCode textSection [(0x1f0, 0x40d), (0x620, 0x1), (0xa80, 0xa3c),
    (0x14c0, 0x166), (0x1639, 0x1), (0x163b, 0x1), (0x1aa0, 0x1), (0x1ab0, 0x222), (0x1ce0, 0x148),
    (0x1e30, 0x7), (0x1e40, 0x78), (0x2020, 0xb), (0x2d70, 0x45), (0x2dc0, 0x2f)]

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
    (hcore : Refine.Atom.All code (lifted.locationOf .l1014c0 initial).arguments initial.external
      (core.atoms lab c fr p))
    (hstart : core.start lab = .l1014c0 := by rfl)
    (hentry : ∀ fr, atoms .l1014c0 fr = frameInfo.entryAtoms fr := by intro _; rfl)
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

end Decrypt

end ChaCha20Poly1305.Proofs.Decrypt.Lifted
