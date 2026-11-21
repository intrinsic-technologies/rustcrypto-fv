import K256.Proofs.Generate.LIR.Program
import K256.Proofs.Common.Refine.Contract
import K256.Proofs.Common.Refine.Lemma.SysVEntry

namespace K256.Proofs.Generate.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Sec1.LIR

namespace Fn11c880

def frameInfo : Refine.FrameInfo where
  entry := 0x11c880
  frameBytes := 0xcb8
  stackBytes := some 0xed8
  slots := [(3, 0x30), (5, 0x8), (12, 0x28), (13, 0x20), (14, 0x18), (15, 0x10)]
  preserved := [3, 5, 12, 13, 14, 15]
  fpPreserved := [39, 50, 51]
  clobbers := [0, 1, 2, 6, 7, 8, 9, 10, 11]
  callSlots := [(0x203de0, 0x129770), (0x203e20, 0x100a20)]

def labelFrameG1 : Label.G1 → Option Refine.LabelFrame
  | .l11c880 => some ⟨0x0, [(1, 1), (2, 2), (3, 3), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9),
      (12, 12), (13, 13), (14, 14), (15, 15), (39, 39), (50, 50),
      (51, 51)], [], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11c8d2 => some ⟨0xcb8, [(1, 1), (2, 2), (3, 3), (5, 5), (7, 7), (8, 8), (9, 9), (12, 12),
      (13, 13), (14, 14), (15, 15), (39, 39), (50, 50), (51, 51)], [(0xc08, 6), (0xbc8, 9),
      (0xbb8, 8), (0xb18, 2), (0xaf8, 1), (0xa70, 7), (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14),
      (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11c920 => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11c95d => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11c977 => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11c989 => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11c9a3 => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11c9c0 => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11c9d2 => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11c9e7 => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | _ => none

@[refine_layout] def frameAtG1 : Label.G1 → Refine.Activation → List Refine.Atom
  | .l11c880 => fun fr =>
      [.gpr 4 fr.rsp, .reg 22 ⟨1, 0⟩, .gpr 1 fr.rcx, .gpr 2 fr.rdx, .gpr 3 fr.rbx, .gpr 5 fr.rbp,
       .gpr 6 fr.rsi, .gpr 7 fr.rdi, .gpr 8 fr.r8, .gpr 9 fr.r9, .gpr 12 fr.r12, .gpr 13 fr.r13,
       .gpr 14 fr.r14, .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0xed8) 0xed8,
       .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x203de0 8, .mem 0x203de0 64 0x129770, .readable 0x203e20 8,
       .mem 0x203e20 64 0x100a20, .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11c8d2 => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .gpr 1 fr.rcx, .gpr 2 fr.rdx, .gpr 3 fr.rbx,
       .gpr 5 fr.rbp, .gpr 7 fr.rdi, .gpr 8 fr.r8, .gpr 9 fr.r9, .gpr 12 fr.r12, .gpr 13 fr.r13,
       .gpr 14 fr.r14, .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0xc08) 64 fr.rsi, .mem (fr.rsp - 0xbc8) 64 fr.r9,
       .mem (fr.rsp - 0xbb8) 64 fr.r8, .mem (fr.rsp - 0xb18) 64 fr.rdx,
       .mem (fr.rsp - 0xaf8) 64 fr.rcx, .mem (fr.rsp - 0xa70) 64 fr.rdi,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11c920 => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11c95d => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11c977 => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11c989 => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11c9a3 => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11c9c0 => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11c9d2 => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11c9e7 => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | _ => fun _ => []

def labelFrameG2 : Label.G2 → Option Refine.LabelFrame
  | .l11ca7f => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11cb3c => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11cbf4 => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11cc3e => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11ccfd => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11cf0d => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11cf51 => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11cfae => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11d003 => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11d058 => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11d0ad => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11d102 => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11d157 => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11d2e1 => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11d31e => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11d371 => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11d3bc => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11d407 => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11d452 => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11d49d => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11d4e8 => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11d514 => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11d535 => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11d546 => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11d556 => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11d566 => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11d579 => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11d620 => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11d690 => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11d69b => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11d6a6 => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11d6c2 => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11d6d3 => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11d6eb => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11d6fe => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11d70e => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11d719 => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11d72f => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11d731 => some ⟨0xcb8, [(1, 1), (2, 2), (3, 3), (5, 5), (7, 7), (8, 8), (9, 9), (12, 12),
      (13, 13), (14, 14), (15, 15), (39, 39), (50, 50), (51, 51)], [(0xc08, 6), (0xbc8, 9),
      (0xbb8, 8), (0xb18, 2), (0xaf8, 1), (0xa70, 7), (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14),
      (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11d748 => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11d7d0 => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11d7ef => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11d810 => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11d82c => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11d880 => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11f5e5 => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11f5f4 => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11f600 => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11f60e => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11f61c => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11f638 => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11f64e => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11f677 => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11f68a => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11f69b => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11f6a6 => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11f6bf => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11f6c4 => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], []⟩
  | .l11f6f1 => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11f708 => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11f71f => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11f736 => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11f74d => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l11f764 => some ⟨0xcb8, [(39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩

@[refine_layout] def frameAtG2 : Label.G2 → Refine.Activation → List Refine.Atom
  | .l11ca7f => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11cb3c => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11cbf4 => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11cc3e => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11ccfd => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11cf0d => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11cf51 => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11cfae => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11d003 => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11d058 => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11d0ad => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11d102 => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11d157 => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11d2e1 => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11d31e => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11d371 => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11d3bc => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11d407 => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11d452 => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11d49d => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11d4e8 => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11d514 => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11d535 => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11d546 => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11d556 => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11d566 => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11d579 => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11d620 => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11d690 => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11d69b => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11d6a6 => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11d6c2 => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11d6d3 => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11d6eb => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11d6fe => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11d70e => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11d719 => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11d72f => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11d731 => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .gpr 1 fr.rcx, .gpr 2 fr.rdx, .gpr 3 fr.rbx,
       .gpr 5 fr.rbp, .gpr 7 fr.rdi, .gpr 8 fr.r8, .gpr 9 fr.r9, .gpr 12 fr.r12, .gpr 13 fr.r13,
       .gpr 14 fr.r14, .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0xc08) 64 fr.rsi, .mem (fr.rsp - 0xbc8) 64 fr.r9,
       .mem (fr.rsp - 0xbb8) 64 fr.r8, .mem (fr.rsp - 0xb18) 64 fr.rdx,
       .mem (fr.rsp - 0xaf8) 64 fr.rcx, .mem (fr.rsp - 0xa70) 64 fr.rdi,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11d748 => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11d7d0 => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11d7ef => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11d810 => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11d82c => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11d880 => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11f5e5 => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11f5f4 => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11f600 => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11f60e => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11f61c => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11f638 => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11f64e => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11f677 => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11f68a => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11f69b => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11f6a6 => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11f6bf => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11f6c4 => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8)]
  | .l11f6f1 => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11f708 => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11f71f => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11f736 => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11f74d => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l11f764 => fun fr =>
      [.gpr 4 (fr.rsp - 0xcb8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0xed8) 0xed8, .fact (fr.low.toNat + 0xed8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204d00 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]

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

def closureCode : CodeMap := sectionCode textSection [(0xa20, 0x2), (0x99c0, 0x23c),
    (0xa410, 0x1000), (0xb410, 0x1000), (0xc410, 0x1000), (0xd410, 0xbf6), (0xe010, 0x4a4),
    (0xfcc0, 0x18a), (0x109b0, 0x1c2), (0x10b80, 0x14b), (0x145f0, 0x2d4), (0x1aa40, 0x22c),
    (0x1b510, 0x3d4), (0x1b8f0, 0x253), (0x1c510, 0x363), (0x1c880, 0xf4a), (0x1d7d0, 0x1000),
    (0x1e7d0, 0xfab), (0x27d50, 0x11), (0x295f2, 0x3d), (0x29770, 0x2c), (0x2a820, 0x2f)]

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
    (hcore : Refine.Atom.All code (lifted.locationOf .l11c880 initial).arguments initial.external
      (core.atoms lab c fr p))
    (hstart : core.start lab = .l11c880 := by rfl)
    (hentry : ∀ fr, atoms .l11c880 fr = frameInfo.entryAtoms fr := by intro _; rfl)
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

end Fn11c880

end K256.Proofs.Generate.LIR
