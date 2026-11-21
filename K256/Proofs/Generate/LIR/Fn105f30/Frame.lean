import K256.Proofs.Generate.LIR.Program
import K256.Proofs.Common.Refine.Contract
import K256.Proofs.Common.Refine.Lemma.SysVEntry

namespace K256.Proofs.Generate.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Sec1.LIR

namespace Fn105f30

def frameInfo : Refine.FrameInfo where
  entry := 0x105f30
  frameBytes := 0x188
  stackBytes := some 0x27b8
  slots := [(3, 0x30), (5, 0x8), (12, 0x28), (13, 0x20), (14, 0x18), (15, 0x10)]
  preserved := [3, 5, 12, 13, 14, 15]
  fpPreserved := [39, 50, 51]
  clobbers := [0, 1, 2, 6, 7, 8, 9, 10, 11]
  callSlots := [(0x203de0, 0x129770), (0x203e20, 0x100a20)]

def labelFrameG0 : Label.G0 → Option Refine.LabelFrame
  | .l105f30 => some ⟨0x0, [(1, 1), (2, 2), (3, 3), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9),
      (12, 12), (13, 13), (14, 14), (15, 15), (39, 39), (50, 50),
      (51, 51)], [], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l105f70 => some ⟨0x188, [(14, 6), (39, 39), (50, 50), (51, 51)], [(0x168, 7), (0x30, 3),
      (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770),
      (0x203e20, 0x100a20)]⟩
  | .l105ff5 => some ⟨0x188, [(14, 6), (39, 39), (50, 50), (51, 51)], [(0x168, 7), (0x30, 3),
      (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770),
      (0x203e20, 0x100a20)]⟩
  | .l106001 => some ⟨0x188, [(14, 6), (39, 39), (50, 50), (51, 51)], [(0x168, 7), (0x30, 3),
      (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770),
      (0x203e20, 0x100a20)]⟩
  | .l106009 => some ⟨0x188, [(14, 6), (39, 39), (50, 50), (51, 51)], [(0x168, 7), (0x30, 3),
      (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770),
      (0x203e20, 0x100a20)]⟩
  | .l10600f => some ⟨0x188, [(14, 6), (39, 39), (50, 50), (51, 51)], [(0x168, 7), (0x30, 3),
      (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770),
      (0x203e20, 0x100a20)]⟩
  | .l106020 => some ⟨0x188, [(14, 6), (39, 39), (50, 50), (51, 51)], [(0x168, 7), (0x30, 3),
      (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770),
      (0x203e20, 0x100a20)]⟩
  | .l10605d => some ⟨0x188, [(14, 6), (39, 39), (50, 50), (51, 51)], [(0x168, 7), (0x30, 3),
      (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770),
      (0x203e20, 0x100a20)]⟩
  | .l10606b => some ⟨0x188, [(14, 6), (39, 39), (50, 50), (51, 51)], [(0x168, 7), (0x30, 3),
      (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770),
      (0x203e20, 0x100a20)]⟩
  | .l106078 => some ⟨0x188, [(14, 6), (39, 39), (50, 50), (51, 51)], [(0x168, 7), (0x30, 3),
      (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15), (0x8, 5)], []⟩
  | .l10607d => some ⟨0x188, [(14, 6), (39, 39), (50, 50), (51, 51)], [(0x168, 7), (0x30, 3),
      (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770),
      (0x203e20, 0x100a20)]⟩
  | .l1060b7 => some ⟨0x188, [(39, 39), (50, 50), (51, 51)], [(0x168, 7), (0x30, 3), (0x28, 12),
      (0x20, 13), (0x18, 14), (0x10, 15), (0x8, 5)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l1060c7 => some ⟨0x188, [(39, 39), (50, 50), (51, 51)], [(0x168, 7), (0x30, 3), (0x28, 12),
      (0x20, 13), (0x18, 14), (0x10, 15), (0x8, 5)], []⟩
  | _ => none

@[refine_layout] def frameAtG0 : Label.G0 → Refine.Activation → List Refine.Atom
  | .l105f30 => fun fr =>
      [.gpr 4 fr.rsp, .reg 22 ⟨1, 0⟩, .gpr 1 fr.rcx, .gpr 2 fr.rdx, .gpr 3 fr.rbx, .gpr 5 fr.rbp,
       .gpr 6 fr.rsi, .gpr 7 fr.rdi, .gpr 8 fr.r8, .gpr 9 fr.r9, .gpr 12 fr.r12, .gpr 13 fr.r13,
       .gpr 14 fr.r14, .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x27b8) 0x27b8,
       .fact (fr.low.toNat + 0x27b8 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x203de0 8, .mem 0x203de0 64 0x129770, .readable 0x203e20 8,
       .mem 0x203e20 64 0x100a20, .fact (0x2065e0 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l105f70 => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .gpr 14 fr.rsi, .reg 39 ⟨32, fr.mxcsr⟩,
       .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x168) 64 fr.rdi,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x27b8) 0x27b8, .fact (fr.low.toNat + 0x27b8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x2065e0 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l105ff5 => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .gpr 14 fr.rsi, .reg 39 ⟨32, fr.mxcsr⟩,
       .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x168) 64 fr.rdi,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x27b8) 0x27b8, .fact (fr.low.toNat + 0x27b8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x2065e0 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l106001 => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .gpr 14 fr.rsi, .reg 39 ⟨32, fr.mxcsr⟩,
       .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x168) 64 fr.rdi,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x27b8) 0x27b8, .fact (fr.low.toNat + 0x27b8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x2065e0 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l106009 => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .gpr 14 fr.rsi, .reg 39 ⟨32, fr.mxcsr⟩,
       .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x168) 64 fr.rdi,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x27b8) 0x27b8, .fact (fr.low.toNat + 0x27b8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x2065e0 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l10600f => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .gpr 14 fr.rsi, .reg 39 ⟨32, fr.mxcsr⟩,
       .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x168) 64 fr.rdi,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x27b8) 0x27b8, .fact (fr.low.toNat + 0x27b8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x2065e0 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l106020 => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .gpr 14 fr.rsi, .reg 39 ⟨32, fr.mxcsr⟩,
       .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x168) 64 fr.rdi,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x27b8) 0x27b8, .fact (fr.low.toNat + 0x27b8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x2065e0 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l10605d => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .gpr 14 fr.rsi, .reg 39 ⟨32, fr.mxcsr⟩,
       .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x168) 64 fr.rdi,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x27b8) 0x27b8, .fact (fr.low.toNat + 0x27b8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x2065e0 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l10606b => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .gpr 14 fr.rsi, .reg 39 ⟨32, fr.mxcsr⟩,
       .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x168) 64 fr.rdi,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x27b8) 0x27b8, .fact (fr.low.toNat + 0x27b8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x2065e0 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l106078 => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .gpr 14 fr.rsi, .reg 39 ⟨32, fr.mxcsr⟩,
       .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x168) 64 fr.rdi,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x27b8) 0x27b8, .fact (fr.low.toNat + 0x27b8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8)]
  | .l10607d => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .gpr 14 fr.rsi, .reg 39 ⟨32, fr.mxcsr⟩,
       .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x168) 64 fr.rdi,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x27b8) 0x27b8, .fact (fr.low.toNat + 0x27b8 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203de0 8, .mem 0x203de0 64 0x129770,
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x2065e0 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l1060b7 => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x168) 64 fr.rdi, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x27b8) 0x27b8,
       .fact (fr.low.toNat + 0x27b8 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x203de0 8, .mem 0x203de0 64 0x129770, .readable 0x203e20 8,
       .mem 0x203e20 64 0x100a20, .fact (0x2065e0 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l1060c7 => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x168) 64 fr.rdi, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x27b8) 0x27b8,
       .fact (fr.low.toNat + 0x27b8 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
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

def closureCode : CodeMap := sectionCode textSection [(0xa20, 0x2), (0xa30, 0x2), (0x5f30, 0x32),
    (0x5f70, 0x1a8), (0x84e0, 0x3aa), (0x8890, 0x597), (0x8e30, 0x14a), (0x8f80, 0x507),
    (0x99c0, 0x23c), (0x9c00, 0x175), (0x9e60, 0xf5), (0xa280, 0x1e), (0xa410, 0x1000),
    (0xb410, 0x1000), (0xc410, 0x1000), (0xd410, 0xbf6), (0xe010, 0x4a4), (0xe4c0, 0x819),
    (0xece0, 0x19a), (0xee80, 0x2c3), (0xfcc0, 0x18a), (0xfe50, 0x5), (0x109b0, 0x1c2),
    (0x10b80, 0x14b), (0x145f0, 0x2d4), (0x14930, 0x18a), (0x1aa40, 0x22c), (0x1b510, 0x3d4),
    (0x1b8f0, 0x253), (0x1c510, 0x363), (0x1c880, 0xf4a), (0x1d7d0, 0x1000), (0x1e7d0, 0xfab),
    (0x20470, 0x112), (0x27d50, 0x11), (0x27f50, 0x6a), (0x29560, 0x34), (0x295f2, 0x3d),
    (0x29770, 0x2c), (0x2a820, 0x2f)]

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
    (hcore : Refine.Atom.All code (lifted.locationOf .l105f30 initial).arguments initial.external
      (core.atoms lab c fr p))
    (hstart : core.start lab = .l105f30 := by rfl)
    (hentry : ∀ fr, atoms .l105f30 fr = frameInfo.entryAtoms fr := by intro _; rfl)
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

end Fn105f30

end K256.Proofs.Generate.LIR
