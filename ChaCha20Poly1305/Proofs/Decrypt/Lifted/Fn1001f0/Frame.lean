import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Program
import ChaCha20Poly1305.Proofs.Common.Refine.Contract
import ChaCha20Poly1305.Proofs.Common.Refine.Lemma.SysVEntry

namespace ChaCha20Poly1305.Proofs.Decrypt.Lifted

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift

namespace Fn1001f0

def frameInfo : Refine.FrameInfo where
  entry := 0x1001f0
  frameBytes := 0x1b8
  stackBytes := some 0x360
  slots := [(3, 0x30), (5, 0x8), (12, 0x28), (13, 0x20), (14, 0x18), (15, 0x10)]
  preserved := [3, 5, 12, 13, 14, 15]
  fpPreserved := [39, 50, 51]
  clobbers := [0, 1, 2, 6, 7, 8, 9, 10, 11]
  callSlots := [(0x2013a8, 0x102dc0), (0x2013e0, 0x102d70)]

def labelFrameG0 : Label.G0 → Option Refine.LabelFrame
  | .l1001f0 => some ⟨0x0, [(1, 1), (2, 2), (3, 3), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9),
      (12, 12), (13, 13), (14, 14), (15, 15), (39, 39), (50, 50),
      (51, 51)], [], [(0x2013a8, 0x102dc0), (0x2013e0, 0x102d70)]⟩
  | .l10024c => some ⟨0x1b8, [(2, 2), (3, 8), (5, 1), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12),
      (13, 2), (14, 9), (15, 15), (39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x2013a8, 0x102dc0), (0x2013e0, 0x102d70)]⟩
  | .l1002e5 => some ⟨0x1b8, [(2, 2), (3, 8), (5, 1), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12),
      (13, 2), (14, 9), (15, 15), (39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x2013a8, 0x102dc0), (0x2013e0, 0x102d70)]⟩
  | .l100384 => some ⟨0x1b8, [(3, 8), (5, 1), (12, 12), (13, 2), (14, 9), (15, 15), (39, 39),
      (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15),
      (0x8, 5)], [(0x2013a8, 0x102dc0), (0x2013e0, 0x102d70)]⟩
  | .l10038c => some ⟨0x1b8, [(3, 8), (5, 1), (12, 12), (13, 2), (14, 9), (15, 15), (39, 39),
      (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15),
      (0x8, 5)], [(0x2013a8, 0x102dc0), (0x2013e0, 0x102d70)]⟩
  | .l1003ae => some ⟨0x1b8, [(3, 8), (5, 1), (13, 2), (14, 9), (39, 39), (50, 50),
      (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15),
      (0x8, 5)], [(0x2013a8, 0x102dc0), (0x2013e0, 0x102d70)]⟩
  | .l1003e3 => some ⟨0x1b8, [(3, 8), (5, 1), (13, 2), (14, 9), (39, 39), (50, 50),
      (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15),
      (0x8, 5)], [(0x2013a8, 0x102dc0), (0x2013e0, 0x102d70)]⟩
  | .l100417 => some ⟨0x1b8, [(3, 8), (5, 1), (39, 39), (50, 50), (51, 51)], [(0x1b0, 2),
      (0x1a8, 8), (0xf8, 1), (0xf0, 9), (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15),
      (0x8, 5)], [(0x2013a8, 0x102dc0), (0x2013e0, 0x102d70)]⟩
  | .l100420 => some ⟨0x1b8, [(39, 39), (50, 50), (51, 51)], [(0x1b0, 2), (0x1a8, 8), (0xf8, 1),
      (0xf0, 9), (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15),
      (0x8, 5)], [(0x2013a8, 0x102dc0), (0x2013e0, 0x102d70)]⟩
  | .l10042c => some ⟨0x1b8, [(39, 39), (50, 50), (51, 51)], [(0x1b0, 2), (0x1a8, 8), (0xf8, 1),
      (0xf0, 9), (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15),
      (0x8, 5)], [(0x2013a8, 0x102dc0), (0x2013e0, 0x102d70)]⟩
  | .l100435 => some ⟨0x1b8, [(39, 39), (50, 50), (51, 51)], [(0x1b0, 2), (0x1a8, 8), (0xf8, 1),
      (0xf0, 9), (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15),
      (0x8, 5)], [(0x2013a8, 0x102dc0), (0x2013e0, 0x102d70)]⟩
  | .l10043a => some ⟨0x1b8, [(39, 39), (50, 50), (51, 51)], [(0x1b0, 2), (0x1a8, 8), (0xf8, 1),
      (0xf0, 9), (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15),
      (0x8, 5)], [(0x2013a8, 0x102dc0), (0x2013e0, 0x102d70)]⟩
  | .l10045a => some ⟨0x1b8, [(39, 39), (50, 50), (51, 51)], [(0x1b0, 2), (0x1a8, 8), (0xf8, 1),
      (0xf0, 9), (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15),
      (0x8, 5)], [(0x2013a8, 0x102dc0), (0x2013e0, 0x102d70)]⟩
  | .l10046e => some ⟨0x1b8, [(39, 39), (50, 50), (51, 51)], [(0x1b0, 2), (0x1a8, 8), (0xf8, 1),
      (0xf0, 9), (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15),
      (0x8, 5)], [(0x2013a8, 0x102dc0), (0x2013e0, 0x102d70)]⟩
  | .l100479 => some ⟨0x1b8, [(39, 39), (50, 50), (51, 51)], [(0x1b0, 2), (0x1a8, 8), (0xf8, 1),
      (0xf0, 9), (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15),
      (0x8, 5)], [(0x2013a8, 0x102dc0), (0x2013e0, 0x102d70)]⟩
  | .l10049a => some ⟨0x1b8, [(39, 39), (50, 50), (51, 51)], [(0x1b0, 2), (0x1a8, 8), (0xf8, 1),
      (0xf0, 9), (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15),
      (0x8, 5)], [(0x2013a8, 0x102dc0), (0x2013e0, 0x102d70)]⟩
  | .l1004a0 => some ⟨0x1b8, [(39, 39), (50, 50), (51, 51)], [(0x1b0, 2), (0x1a8, 8), (0xf8, 1),
      (0xf0, 9), (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15),
      (0x8, 5)], [(0x2013a8, 0x102dc0), (0x2013e0, 0x102d70)]⟩
  | .l1004ac => some ⟨0x1b8, [(39, 39), (50, 50), (51, 51)], [(0x1b0, 2), (0x1a8, 8), (0xf8, 1),
      (0xf0, 9), (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15),
      (0x8, 5)], [(0x2013a8, 0x102dc0), (0x2013e0, 0x102d70)]⟩
  | .l1004b5 => some ⟨0x1b8, [(39, 39), (50, 50), (51, 51)], [(0x1b0, 2), (0x1a8, 8), (0xf8, 1),
      (0xf0, 9), (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15),
      (0x8, 5)], [(0x2013a8, 0x102dc0), (0x2013e0, 0x102d70)]⟩
  | .l1004c2 => some ⟨0x1b8, [(39, 39), (50, 50), (51, 51)], [(0x1b0, 2), (0x1a8, 8), (0xf8, 1),
      (0xf0, 9), (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15),
      (0x8, 5)], [(0x2013a8, 0x102dc0), (0x2013e0, 0x102d70)]⟩
  | .l1004dd => some ⟨0x1b8, [(39, 39), (50, 50), (51, 51)], [(0x1b0, 2), (0x1a8, 8), (0xf8, 1),
      (0xf0, 9), (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15),
      (0x8, 5)], [(0x2013a8, 0x102dc0)]⟩
  | .l1004f1 => some ⟨0x1b8, [(39, 39), (50, 50), (51, 51)], [(0x1b0, 2), (0x1a8, 8), (0xf8, 1),
      (0xf0, 9), (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15), (0x8, 5)], []⟩
  | .l1004fc => some ⟨0x1b8, [(39, 39), (50, 50), (51, 51)], [(0x1b0, 2), (0x1a8, 8), (0xf8, 1),
      (0xf0, 9), (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15), (0x8, 5)], []⟩
  | .l100520 => some ⟨0x1b8, [(39, 39), (50, 50), (51, 51)], [(0x1b0, 2), (0x1a8, 8), (0x198, 1),
      (0xf8, 1), (0xf0, 9), (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15),
      (0x8, 5)], []⟩
  | .l100577 => some ⟨0x1b8, [(39, 39), (50, 50), (51, 51)], [(0x1b0, 2), (0x1a8, 8), (0xf8, 1),
      (0xf0, 9), (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15), (0x8, 5)], []⟩
  | .l1005d2 => some ⟨0x1b8, [(8, 9), (39, 39), (50, 50), (51, 51)], [(0x1b0, 2), (0x1a8, 8),
      (0xf8, 1), (0xf0, 9), (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15),
      (0x8, 5)], []⟩
  | .l1005e4 => some ⟨0x1b8, [(39, 39), (50, 50), (51, 51)], [(0x1b0, 2), (0x1a8, 8), (0xf8, 1),
      (0xf0, 9), (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15), (0x8, 5)], []⟩
  | .l1005e8 => some ⟨0x1b8, [(39, 39), (50, 50), (51, 51)], [(0x1b0, 2), (0x1a8, 8), (0xf8, 1),
      (0xf0, 9), (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15), (0x8, 5)], []⟩
  | .l1005ea => some ⟨0x1b8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], []⟩
  | .l1005fc => some ⟨0x1b8, [(3, 8), (5, 1), (12, 12), (13, 2), (14, 9), (15, 15), (39, 39),
      (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15),
      (0x8, 5)], []⟩
  | .l100620 => some ⟨0x1b8, [(39, 39), (50, 50), (51, 51)], [(0x1b0, 2), (0x1a8, 8), (0xf8, 1),
      (0xf0, 9), (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15), (0x8, 5)], []⟩
  | _ => none

@[refine_layout] def frameAtG0 : Label.G0 → Refine.Activation → List Refine.Atom
  | .l1001f0 => fun fr =>
      [.gpr 4 fr.rsp, .reg 22 ⟨1, 0⟩, .gpr 1 fr.rcx, .gpr 2 fr.rdx, .gpr 3 fr.rbx, .gpr 5 fr.rbp,
       .gpr 6 fr.rsi, .gpr 7 fr.rdi, .gpr 8 fr.r8, .gpr 9 fr.r9, .gpr 12 fr.r12, .gpr 13 fr.r13,
       .gpr 14 fr.r14, .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x360) 0x360,
       .fact (fr.low.toNat + 0x360 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x2013a8 8, .mem 0x2013a8 64 0x102dc0, .readable 0x2013e0 8,
       .mem 0x2013e0 64 0x102d70, .fact (0x201748 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x2013a8)]
  | .l10024c => fun fr =>
      [.gpr 4 (fr.rsp - 0x1b8), .reg 22 ⟨1, 0⟩, .gpr 2 fr.rdx, .gpr 3 fr.r8, .gpr 5 fr.rcx,
       .gpr 6 fr.rsi, .gpr 7 fr.rdi, .gpr 8 fr.r8, .gpr 9 fr.r9, .gpr 12 fr.r12, .gpr 13 fr.rdx,
       .gpr 14 fr.r9, .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x360) 0x360, .fact (fr.low.toNat + 0x360 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x2013a8 8, .mem 0x2013a8 64 0x102dc0,
       .readable 0x2013e0 8, .mem 0x2013e0 64 0x102d70,
       .fact (0x201748 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x2013a8)]
  | .l1002e5 => fun fr =>
      [.gpr 4 (fr.rsp - 0x1b8), .reg 22 ⟨1, 0⟩, .gpr 2 fr.rdx, .gpr 3 fr.r8, .gpr 5 fr.rcx,
       .gpr 6 fr.rsi, .gpr 7 fr.rdi, .gpr 8 fr.r8, .gpr 9 fr.r9, .gpr 12 fr.r12, .gpr 13 fr.rdx,
       .gpr 14 fr.r9, .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x360) 0x360, .fact (fr.low.toNat + 0x360 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x2013a8 8, .mem 0x2013a8 64 0x102dc0,
       .readable 0x2013e0 8, .mem 0x2013e0 64 0x102d70,
       .fact (0x201748 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x2013a8)]
  | .l100384 => fun fr =>
      [.gpr 4 (fr.rsp - 0x1b8), .reg 22 ⟨1, 0⟩, .gpr 3 fr.r8, .gpr 5 fr.rcx, .gpr 12 fr.r12,
       .gpr 13 fr.rdx, .gpr 14 fr.r9, .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x360) 0x360, .fact (fr.low.toNat + 0x360 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x2013a8 8, .mem 0x2013a8 64 0x102dc0,
       .readable 0x2013e0 8, .mem 0x2013e0 64 0x102d70,
       .fact (0x201748 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x2013a8)]
  | .l10038c => fun fr =>
      [.gpr 4 (fr.rsp - 0x1b8), .reg 22 ⟨1, 0⟩, .gpr 3 fr.r8, .gpr 5 fr.rcx, .gpr 12 fr.r12,
       .gpr 13 fr.rdx, .gpr 14 fr.r9, .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x360) 0x360, .fact (fr.low.toNat + 0x360 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x2013a8 8, .mem 0x2013a8 64 0x102dc0,
       .readable 0x2013e0 8, .mem 0x2013e0 64 0x102d70,
       .fact (0x201748 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x2013a8)]
  | .l1003ae => fun fr =>
      [.gpr 4 (fr.rsp - 0x1b8), .reg 22 ⟨1, 0⟩, .gpr 3 fr.r8, .gpr 5 fr.rcx, .gpr 13 fr.rdx,
       .gpr 14 fr.r9, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x360) 0x360, .fact (fr.low.toNat + 0x360 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x2013a8 8, .mem 0x2013a8 64 0x102dc0,
       .readable 0x2013e0 8, .mem 0x2013e0 64 0x102d70,
       .fact (0x201748 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x2013a8)]
  | .l1003e3 => fun fr =>
      [.gpr 4 (fr.rsp - 0x1b8), .reg 22 ⟨1, 0⟩, .gpr 3 fr.r8, .gpr 5 fr.rcx, .gpr 13 fr.rdx,
       .gpr 14 fr.r9, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x360) 0x360, .fact (fr.low.toNat + 0x360 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x2013a8 8, .mem 0x2013a8 64 0x102dc0,
       .readable 0x2013e0 8, .mem 0x2013e0 64 0x102d70,
       .fact (0x201748 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x2013a8)]
  | .l100417 => fun fr =>
      [.gpr 4 (fr.rsp - 0x1b8), .reg 22 ⟨1, 0⟩, .gpr 3 fr.r8, .gpr 5 fr.rcx, .reg 39 ⟨32, fr.mxcsr⟩,
       .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x1b0) 64 fr.rdx,
       .mem (fr.rsp - 0x1a8) 64 fr.r8, .mem (fr.rsp - 0xf8) 64 fr.rcx,
       .mem (fr.rsp - 0xf0) 64 fr.r9, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x360) 0x360,
       .fact (fr.low.toNat + 0x360 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x2013a8 8, .mem 0x2013a8 64 0x102dc0, .readable 0x2013e0 8,
       .mem 0x2013e0 64 0x102d70, .fact (0x201748 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x2013a8)]
  | .l100420 => fun fr =>
      [.gpr 4 (fr.rsp - 0x1b8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x1b0) 64 fr.rdx, .mem (fr.rsp - 0x1a8) 64 fr.r8,
       .mem (fr.rsp - 0xf8) 64 fr.rcx, .mem (fr.rsp - 0xf0) 64 fr.r9,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x360) 0x360, .fact (fr.low.toNat + 0x360 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x2013a8 8, .mem 0x2013a8 64 0x102dc0,
       .readable 0x2013e0 8, .mem 0x2013e0 64 0x102d70,
       .fact (0x201748 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x2013a8)]
  | .l10042c => fun fr =>
      [.gpr 4 (fr.rsp - 0x1b8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x1b0) 64 fr.rdx, .mem (fr.rsp - 0x1a8) 64 fr.r8,
       .mem (fr.rsp - 0xf8) 64 fr.rcx, .mem (fr.rsp - 0xf0) 64 fr.r9,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x360) 0x360, .fact (fr.low.toNat + 0x360 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x2013a8 8, .mem 0x2013a8 64 0x102dc0,
       .readable 0x2013e0 8, .mem 0x2013e0 64 0x102d70,
       .fact (0x201748 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x2013a8)]
  | .l100435 => fun fr =>
      [.gpr 4 (fr.rsp - 0x1b8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x1b0) 64 fr.rdx, .mem (fr.rsp - 0x1a8) 64 fr.r8,
       .mem (fr.rsp - 0xf8) 64 fr.rcx, .mem (fr.rsp - 0xf0) 64 fr.r9,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x360) 0x360, .fact (fr.low.toNat + 0x360 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x2013a8 8, .mem 0x2013a8 64 0x102dc0,
       .readable 0x2013e0 8, .mem 0x2013e0 64 0x102d70,
       .fact (0x201748 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x2013a8)]
  | .l10043a => fun fr =>
      [.gpr 4 (fr.rsp - 0x1b8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x1b0) 64 fr.rdx, .mem (fr.rsp - 0x1a8) 64 fr.r8,
       .mem (fr.rsp - 0xf8) 64 fr.rcx, .mem (fr.rsp - 0xf0) 64 fr.r9,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x360) 0x360, .fact (fr.low.toNat + 0x360 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x2013a8 8, .mem 0x2013a8 64 0x102dc0,
       .readable 0x2013e0 8, .mem 0x2013e0 64 0x102d70,
       .fact (0x201748 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x2013a8)]
  | .l10045a => fun fr =>
      [.gpr 4 (fr.rsp - 0x1b8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x1b0) 64 fr.rdx, .mem (fr.rsp - 0x1a8) 64 fr.r8,
       .mem (fr.rsp - 0xf8) 64 fr.rcx, .mem (fr.rsp - 0xf0) 64 fr.r9,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x360) 0x360, .fact (fr.low.toNat + 0x360 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x2013a8 8, .mem 0x2013a8 64 0x102dc0,
       .readable 0x2013e0 8, .mem 0x2013e0 64 0x102d70,
       .fact (0x201748 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x2013a8)]
  | .l10046e => fun fr =>
      [.gpr 4 (fr.rsp - 0x1b8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x1b0) 64 fr.rdx, .mem (fr.rsp - 0x1a8) 64 fr.r8,
       .mem (fr.rsp - 0xf8) 64 fr.rcx, .mem (fr.rsp - 0xf0) 64 fr.r9,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x360) 0x360, .fact (fr.low.toNat + 0x360 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x2013a8 8, .mem 0x2013a8 64 0x102dc0,
       .readable 0x2013e0 8, .mem 0x2013e0 64 0x102d70,
       .fact (0x201748 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x2013a8)]
  | .l100479 => fun fr =>
      [.gpr 4 (fr.rsp - 0x1b8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x1b0) 64 fr.rdx, .mem (fr.rsp - 0x1a8) 64 fr.r8,
       .mem (fr.rsp - 0xf8) 64 fr.rcx, .mem (fr.rsp - 0xf0) 64 fr.r9,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x360) 0x360, .fact (fr.low.toNat + 0x360 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x2013a8 8, .mem 0x2013a8 64 0x102dc0,
       .readable 0x2013e0 8, .mem 0x2013e0 64 0x102d70,
       .fact (0x201748 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x2013a8)]
  | .l10049a => fun fr =>
      [.gpr 4 (fr.rsp - 0x1b8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x1b0) 64 fr.rdx, .mem (fr.rsp - 0x1a8) 64 fr.r8,
       .mem (fr.rsp - 0xf8) 64 fr.rcx, .mem (fr.rsp - 0xf0) 64 fr.r9,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x360) 0x360, .fact (fr.low.toNat + 0x360 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x2013a8 8, .mem 0x2013a8 64 0x102dc0,
       .readable 0x2013e0 8, .mem 0x2013e0 64 0x102d70,
       .fact (0x201748 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x2013a8)]
  | .l1004a0 => fun fr =>
      [.gpr 4 (fr.rsp - 0x1b8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x1b0) 64 fr.rdx, .mem (fr.rsp - 0x1a8) 64 fr.r8,
       .mem (fr.rsp - 0xf8) 64 fr.rcx, .mem (fr.rsp - 0xf0) 64 fr.r9,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x360) 0x360, .fact (fr.low.toNat + 0x360 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x2013a8 8, .mem 0x2013a8 64 0x102dc0,
       .readable 0x2013e0 8, .mem 0x2013e0 64 0x102d70,
       .fact (0x201748 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x2013a8)]
  | .l1004ac => fun fr =>
      [.gpr 4 (fr.rsp - 0x1b8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x1b0) 64 fr.rdx, .mem (fr.rsp - 0x1a8) 64 fr.r8,
       .mem (fr.rsp - 0xf8) 64 fr.rcx, .mem (fr.rsp - 0xf0) 64 fr.r9,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x360) 0x360, .fact (fr.low.toNat + 0x360 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x2013a8 8, .mem 0x2013a8 64 0x102dc0,
       .readable 0x2013e0 8, .mem 0x2013e0 64 0x102d70,
       .fact (0x201748 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x2013a8)]
  | .l1004b5 => fun fr =>
      [.gpr 4 (fr.rsp - 0x1b8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x1b0) 64 fr.rdx, .mem (fr.rsp - 0x1a8) 64 fr.r8,
       .mem (fr.rsp - 0xf8) 64 fr.rcx, .mem (fr.rsp - 0xf0) 64 fr.r9,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x360) 0x360, .fact (fr.low.toNat + 0x360 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x2013a8 8, .mem 0x2013a8 64 0x102dc0,
       .readable 0x2013e0 8, .mem 0x2013e0 64 0x102d70,
       .fact (0x201748 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x2013a8)]
  | .l1004c2 => fun fr =>
      [.gpr 4 (fr.rsp - 0x1b8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x1b0) 64 fr.rdx, .mem (fr.rsp - 0x1a8) 64 fr.r8,
       .mem (fr.rsp - 0xf8) 64 fr.rcx, .mem (fr.rsp - 0xf0) 64 fr.r9,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x360) 0x360, .fact (fr.low.toNat + 0x360 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x2013a8 8, .mem 0x2013a8 64 0x102dc0,
       .readable 0x2013e0 8, .mem 0x2013e0 64 0x102d70,
       .fact (0x201748 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x2013a8)]
  | .l1004dd => fun fr =>
      [.gpr 4 (fr.rsp - 0x1b8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x1b0) 64 fr.rdx, .mem (fr.rsp - 0x1a8) 64 fr.r8,
       .mem (fr.rsp - 0xf8) 64 fr.rcx, .mem (fr.rsp - 0xf0) 64 fr.r9,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x360) 0x360, .fact (fr.low.toNat + 0x360 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x2013a8 8, .mem 0x2013a8 64 0x102dc0,
       .fact (0x201710 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x2013a8)]
  | .l1004f1 => fun fr =>
      [.gpr 4 (fr.rsp - 0x1b8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x1b0) 64 fr.rdx, .mem (fr.rsp - 0x1a8) 64 fr.r8,
       .mem (fr.rsp - 0xf8) 64 fr.rcx, .mem (fr.rsp - 0xf0) 64 fr.r9,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x360) 0x360, .fact (fr.low.toNat + 0x360 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8)]
  | .l1004fc => fun fr =>
      [.gpr 4 (fr.rsp - 0x1b8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x1b0) 64 fr.rdx, .mem (fr.rsp - 0x1a8) 64 fr.r8,
       .mem (fr.rsp - 0xf8) 64 fr.rcx, .mem (fr.rsp - 0xf0) 64 fr.r9,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x360) 0x360, .fact (fr.low.toNat + 0x360 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8)]
  | .l100520 => fun fr =>
      [.gpr 4 (fr.rsp - 0x1b8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x1b0) 64 fr.rdx, .mem (fr.rsp - 0x1a8) 64 fr.r8,
       .mem (fr.rsp - 0x198) 64 fr.rcx, .mem (fr.rsp - 0xf8) 64 fr.rcx,
       .mem (fr.rsp - 0xf0) 64 fr.r9, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x360) 0x360,
       .fact (fr.low.toNat + 0x360 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l100577 => fun fr =>
      [.gpr 4 (fr.rsp - 0x1b8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x1b0) 64 fr.rdx, .mem (fr.rsp - 0x1a8) 64 fr.r8,
       .mem (fr.rsp - 0xf8) 64 fr.rcx, .mem (fr.rsp - 0xf0) 64 fr.r9,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x360) 0x360, .fact (fr.low.toNat + 0x360 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8)]
  | .l1005d2 => fun fr =>
      [.gpr 4 (fr.rsp - 0x1b8), .reg 22 ⟨1, 0⟩, .gpr 8 fr.r9, .reg 39 ⟨32, fr.mxcsr⟩,
       .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x1b0) 64 fr.rdx,
       .mem (fr.rsp - 0x1a8) 64 fr.r8, .mem (fr.rsp - 0xf8) 64 fr.rcx,
       .mem (fr.rsp - 0xf0) 64 fr.r9, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x360) 0x360,
       .fact (fr.low.toNat + 0x360 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l1005e4 => fun fr =>
      [.gpr 4 (fr.rsp - 0x1b8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x1b0) 64 fr.rdx, .mem (fr.rsp - 0x1a8) 64 fr.r8,
       .mem (fr.rsp - 0xf8) 64 fr.rcx, .mem (fr.rsp - 0xf0) 64 fr.r9,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x360) 0x360, .fact (fr.low.toNat + 0x360 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8)]
  | .l1005e8 => fun fr =>
      [.gpr 4 (fr.rsp - 0x1b8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x1b0) 64 fr.rdx, .mem (fr.rsp - 0x1a8) 64 fr.r8,
       .mem (fr.rsp - 0xf8) 64 fr.rcx, .mem (fr.rsp - 0xf0) 64 fr.r9,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x360) 0x360, .fact (fr.low.toNat + 0x360 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8)]
  | .l1005ea => fun fr =>
      [.gpr 4 (fr.rsp - 0x1b8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x360) 0x360, .fact (fr.low.toNat + 0x360 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8)]
  | .l1005fc => fun fr =>
      [.gpr 4 (fr.rsp - 0x1b8), .reg 22 ⟨1, 0⟩, .gpr 3 fr.r8, .gpr 5 fr.rcx, .gpr 12 fr.r12,
       .gpr 13 fr.rdx, .gpr 14 fr.r9, .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x360) 0x360, .fact (fr.low.toNat + 0x360 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8)]
  | .l100620 => fun fr =>
      [.gpr 4 (fr.rsp - 0x1b8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x1b0) 64 fr.rdx, .mem (fr.rsp - 0x1a8) 64 fr.r8,
       .mem (fr.rsp - 0xf8) 64 fr.rcx, .mem (fr.rsp - 0xf0) 64 fr.r9,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x360) 0x360, .fact (fr.low.toNat + 0x360 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8)]
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

def closureCode : CodeMap := sectionCode textSection [(0x1f0, 0x40d), (0x620, 0x1), (0xa80, 0xa3c),
    (0x1ab0, 0x222), (0x1ce0, 0x148), (0x1e30, 0x7), (0x1e40, 0x78), (0x2d70, 0x45), (0x2dc0, 0x2f)]

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
    (hcore : Refine.Atom.All code (lifted.locationOf .l1001f0 initial).arguments initial.external
      (core.atoms lab c fr p))
    (hstart : core.start lab = .l1001f0 := by rfl)
    (hentry : ∀ fr, atoms .l1001f0 fr = frameInfo.entryAtoms fr := by intro _; rfl)
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

end Fn1001f0

end ChaCha20Poly1305.Proofs.Decrypt.Lifted
