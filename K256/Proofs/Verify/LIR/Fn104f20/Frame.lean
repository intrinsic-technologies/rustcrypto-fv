import K256.Proofs.Verify.LIR.Program
import K256.Proofs.Common.Refine.Contract
import K256.Proofs.Common.Refine.Lemma.SysVEntry

namespace K256.Proofs.Verify.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Sec1.LIR K256.Proofs.Generate.LIR K256.Proofs.Ecdh.LIR

namespace Fn104f20

def frameInfo : Refine.FrameInfo where
  entry := 0x104f20
  frameBytes := 0x1e8
  stackBytes := some 0x2ed1
  slots := [(3, 0x28), (12, 0x20), (13, 0x18), (14, 0x10), (15, 0x8)]
  preserved := [3, 5, 12, 13, 14, 15]
  fpPreserved := [39, 50, 51]
  clobbers := [0, 1, 2, 6, 7, 8, 9, 10, 11]
  callSlots := [(0x203dd0, 0x12a820), (0x203de0, 0x129770), (0x203e20, 0x100a20)]

def labelFrameG6 : Label.G6 → Option Refine.LabelFrame
  | .l104f20 => some ⟨0x0, [(1, 1), (2, 2), (3, 3), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9),
      (12, 12), (13, 13), (14, 14), (15, 15), (39, 39), (50, 50),
      (51, 51)], [], [(0x203dd0, 0x12a820), (0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l104fa4 => some ⟨0x1e8, [(3, 7), (5, 5), (12, 2), (13, 1), (14, 6), (15, 8), (39, 39),
      (50, 50), (51, 51)], [(0x28, 3), (0x20, 12), (0x18, 13), (0x10, 14),
      (0x8, 15)], [(0x203dd0, 0x12a820), (0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l104fb0 => some ⟨0x1e8, [(3, 7), (5, 5), (12, 2), (13, 1), (14, 6), (15, 8), (39, 39),
      (50, 50), (51, 51)], [(0x28, 3), (0x20, 12), (0x18, 13), (0x10, 14),
      (0x8, 15)], [(0x203dd0, 0x12a820), (0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l104fbc => some ⟨0x1e8, [(3, 7), (5, 5), (12, 2), (13, 1), (14, 6), (15, 8), (39, 39),
      (50, 50), (51, 51)], [(0x28, 3), (0x20, 12), (0x18, 13), (0x10, 14),
      (0x8, 15)], [(0x203dd0, 0x12a820), (0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l105051 => some ⟨0x1e8, [(3, 7), (5, 5), (12, 2), (13, 1), (14, 6), (15, 8), (39, 39),
      (50, 50), (51, 51)], [(0x28, 3), (0x20, 12), (0x18, 13), (0x10, 14),
      (0x8, 15)], [(0x203dd0, 0x12a820), (0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l10505d => some ⟨0x1e8, [(3, 7), (5, 5), (12, 2), (13, 1), (14, 6), (15, 8), (39, 39),
      (50, 50), (51, 51)], [(0x28, 3), (0x20, 12), (0x18, 13), (0x10, 14),
      (0x8, 15)], [(0x203dd0, 0x12a820), (0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l105069 => some ⟨0x1e8, [(3, 7), (5, 5), (12, 2), (13, 1), (14, 6), (15, 8), (39, 39),
      (50, 50), (51, 51)], [(0x28, 3), (0x20, 12), (0x18, 13), (0x10, 14),
      (0x8, 15)], [(0x203dd0, 0x12a820), (0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l1050a9 => some ⟨0x1e8, [(3, 7), (5, 5), (12, 2), (13, 1), (14, 6), (15, 8), (39, 39),
      (50, 50), (51, 51)], [(0x28, 3), (0x20, 12), (0x18, 13), (0x10, 14),
      (0x8, 15)], [(0x203dd0, 0x12a820), (0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l1050ad => some ⟨0x1e8, [(3, 7), (5, 5), (12, 2), (13, 1), (14, 6), (15, 8), (39, 39),
      (50, 50), (51, 51)], [(0x28, 3), (0x20, 12), (0x18, 13), (0x10, 14), (0x8, 15)], []⟩
  | .l1050c1 => some ⟨0x1e8, [(3, 7), (5, 5), (12, 2), (13, 1), (14, 6), (15, 8), (39, 39),
      (50, 50), (51, 51)], [(0x28, 3), (0x20, 12), (0x18, 13), (0x10, 14),
      (0x8, 15)], [(0x203dd0, 0x12a820), (0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l10513d => some ⟨0x1e8, [(3, 7), (5, 5), (12, 2), (13, 1), (14, 6), (15, 8), (39, 39),
      (50, 50), (51, 51)], [(0x28, 3), (0x20, 12), (0x18, 13), (0x10, 14),
      (0x8, 15)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l105145 => some ⟨0x1e8, [(3, 7), (5, 5), (12, 2), (13, 1), (14, 6), (15, 8), (39, 39),
      (50, 50), (51, 51)], [(0x28, 3), (0x20, 12), (0x18, 13), (0x10, 14),
      (0x8, 15)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l10518b => some ⟨0x1e8, [(3, 7), (5, 5), (12, 2), (13, 1), (14, 6), (15, 8), (39, 39),
      (50, 50), (51, 51)], [(0x28, 3), (0x20, 12), (0x18, 13), (0x10, 14),
      (0x8, 15)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l10519d => some ⟨0x1e8, [(3, 7), (5, 5), (12, 2), (13, 1), (14, 6), (15, 8), (39, 39),
      (50, 50), (51, 51)], [(0x28, 3), (0x20, 12), (0x18, 13), (0x10, 14),
      (0x8, 15)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l1051b1 => some ⟨0x1e8, [(3, 7), (5, 5), (12, 2), (13, 1), (14, 6), (15, 8), (39, 39),
      (50, 50), (51, 51)], [(0x28, 3), (0x20, 12), (0x18, 13), (0x10, 14), (0x8, 15)], []⟩
  | .l105216 => some ⟨0x1e8, [(3, 7), (5, 5), (13, 1), (14, 6), (15, 8), (39, 39), (50, 50),
      (51, 51)], [(0x28, 3), (0x20, 12), (0x18, 13), (0x10, 14), (0x8, 15)], []⟩
  | .l105256 => some ⟨0x1e8, [(3, 7), (5, 5), (13, 1), (14, 6), (39, 39), (50, 50),
      (51, 51)], [(0x28, 3), (0x20, 12), (0x18, 13), (0x10, 14), (0x8, 15)], []⟩
  | .l10537f => some ⟨0x1e8, [(3, 7), (5, 5), (12, 2), (13, 1), (14, 6), (15, 8), (39, 39),
      (50, 50), (51, 51)], [(0x28, 3), (0x20, 12), (0x18, 13), (0x10, 14), (0x8, 15)], []⟩
  | .l105393 => some ⟨0x1e8, [(3, 7), (5, 5), (12, 2), (13, 1), (14, 6), (15, 8), (39, 39),
      (50, 50), (51, 51)], [(0x28, 3), (0x20, 12), (0x18, 13), (0x10, 14),
      (0x8, 15)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l105398 => some ⟨0x1e8, [(3, 7), (5, 5), (12, 2), (13, 1), (14, 6), (15, 8), (39, 39),
      (50, 50), (51, 51)], [(0x28, 3), (0x20, 12), (0x18, 13), (0x10, 14),
      (0x8, 15)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l1053af => some ⟨0x1e8, [(3, 7), (5, 5), (12, 2), (13, 1), (14, 6), (15, 8), (39, 39),
      (50, 50), (51, 51)], [(0x28, 3), (0x20, 12), (0x18, 13), (0x10, 14),
      (0x8, 15)], [(0x203e20, 0x100a20)]⟩
  | .l1053cb => some ⟨0x1e8, [(3, 7), (5, 5), (12, 2), (13, 1), (14, 6), (15, 8), (39, 39),
      (50, 50), (51, 51)], [(0x28, 3), (0x20, 12), (0x18, 13), (0x10, 14),
      (0x8, 15)], [(0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l1053ef => some ⟨0x1e8, [(3, 7), (5, 5), (12, 2), (13, 1), (14, 6), (15, 8), (39, 39),
      (50, 50), (51, 51)], [(0x28, 3), (0x20, 12), (0x18, 13), (0x10, 14),
      (0x8, 15)], [(0x203e20, 0x100a20)]⟩
  | _ => none

@[refine_layout] def frameAtG6 : Label.G6 → Refine.Activation → List Refine.Atom
  | .l104f20 => fun fr =>
      [.gpr 4 fr.rsp, .reg 22 ⟨1, 0⟩, .gpr 1 fr.rcx, .gpr 2 fr.rdx, .gpr 3 fr.rbx, .gpr 5 fr.rbp,
       .gpr 6 fr.rsi, .gpr 7 fr.rdi, .gpr 8 fr.r8, .gpr 9 fr.r9, .gpr 12 fr.r12, .gpr 13 fr.r13,
       .gpr 14 fr.r14, .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x2ed1) 0x2ed1,
       .fact (fr.low.toNat + 0x2ed1 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x203dd0 8, .mem 0x203dd0 64 0x12a820, .readable 0x203de0 8,
       .mem 0x203de0 64 0x129770, .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x206cf9 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203dd0)]
  | .l104fa4 => fun fr =>
      [.gpr 4 (fr.rsp - 0x1e8), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rdi, .gpr 5 fr.rbp, .gpr 12 fr.rdx,
       .gpr 13 fr.rcx, .gpr 14 fr.rsi, .gpr 15 fr.r8, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x28) 64 fr.rbx, .mem (fr.rsp - 0x20) 64 fr.r12,
       .mem (fr.rsp - 0x18) 64 fr.r13, .mem (fr.rsp - 0x10) 64 fr.r14,
       .mem (fr.rsp - 0x8) 64 fr.r15, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x2ed1) 0x2ed1,
       .fact (fr.low.toNat + 0x2ed1 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x203dd0 8, .mem 0x203dd0 64 0x12a820, .readable 0x203de0 8,
       .mem 0x203de0 64 0x129770, .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x206cf9 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203dd0)]
  | .l104fb0 => fun fr =>
      [.gpr 4 (fr.rsp - 0x1e8), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rdi, .gpr 5 fr.rbp, .gpr 12 fr.rdx,
       .gpr 13 fr.rcx, .gpr 14 fr.rsi, .gpr 15 fr.r8, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x28) 64 fr.rbx, .mem (fr.rsp - 0x20) 64 fr.r12,
       .mem (fr.rsp - 0x18) 64 fr.r13, .mem (fr.rsp - 0x10) 64 fr.r14,
       .mem (fr.rsp - 0x8) 64 fr.r15, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x2ed1) 0x2ed1,
       .fact (fr.low.toNat + 0x2ed1 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x203dd0 8, .mem 0x203dd0 64 0x12a820, .readable 0x203de0 8,
       .mem 0x203de0 64 0x129770, .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x206cf9 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203dd0)]
  | .l104fbc => fun fr =>
      [.gpr 4 (fr.rsp - 0x1e8), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rdi, .gpr 5 fr.rbp, .gpr 12 fr.rdx,
       .gpr 13 fr.rcx, .gpr 14 fr.rsi, .gpr 15 fr.r8, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x28) 64 fr.rbx, .mem (fr.rsp - 0x20) 64 fr.r12,
       .mem (fr.rsp - 0x18) 64 fr.r13, .mem (fr.rsp - 0x10) 64 fr.r14,
       .mem (fr.rsp - 0x8) 64 fr.r15, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x2ed1) 0x2ed1,
       .fact (fr.low.toNat + 0x2ed1 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x203dd0 8, .mem 0x203dd0 64 0x12a820, .readable 0x203de0 8,
       .mem 0x203de0 64 0x129770, .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x206cf9 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203dd0)]
  | .l105051 => fun fr =>
      [.gpr 4 (fr.rsp - 0x1e8), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rdi, .gpr 5 fr.rbp, .gpr 12 fr.rdx,
       .gpr 13 fr.rcx, .gpr 14 fr.rsi, .gpr 15 fr.r8, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x28) 64 fr.rbx, .mem (fr.rsp - 0x20) 64 fr.r12,
       .mem (fr.rsp - 0x18) 64 fr.r13, .mem (fr.rsp - 0x10) 64 fr.r14,
       .mem (fr.rsp - 0x8) 64 fr.r15, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x2ed1) 0x2ed1,
       .fact (fr.low.toNat + 0x2ed1 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x203dd0 8, .mem 0x203dd0 64 0x12a820, .readable 0x203de0 8,
       .mem 0x203de0 64 0x129770, .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x206cf9 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203dd0)]
  | .l10505d => fun fr =>
      [.gpr 4 (fr.rsp - 0x1e8), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rdi, .gpr 5 fr.rbp, .gpr 12 fr.rdx,
       .gpr 13 fr.rcx, .gpr 14 fr.rsi, .gpr 15 fr.r8, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x28) 64 fr.rbx, .mem (fr.rsp - 0x20) 64 fr.r12,
       .mem (fr.rsp - 0x18) 64 fr.r13, .mem (fr.rsp - 0x10) 64 fr.r14,
       .mem (fr.rsp - 0x8) 64 fr.r15, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x2ed1) 0x2ed1,
       .fact (fr.low.toNat + 0x2ed1 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x203dd0 8, .mem 0x203dd0 64 0x12a820, .readable 0x203de0 8,
       .mem 0x203de0 64 0x129770, .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x206cf9 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203dd0)]
  | .l105069 => fun fr =>
      [.gpr 4 (fr.rsp - 0x1e8), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rdi, .gpr 5 fr.rbp, .gpr 12 fr.rdx,
       .gpr 13 fr.rcx, .gpr 14 fr.rsi, .gpr 15 fr.r8, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x28) 64 fr.rbx, .mem (fr.rsp - 0x20) 64 fr.r12,
       .mem (fr.rsp - 0x18) 64 fr.r13, .mem (fr.rsp - 0x10) 64 fr.r14,
       .mem (fr.rsp - 0x8) 64 fr.r15, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x2ed1) 0x2ed1,
       .fact (fr.low.toNat + 0x2ed1 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x203dd0 8, .mem 0x203dd0 64 0x12a820, .readable 0x203de0 8,
       .mem 0x203de0 64 0x129770, .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x206cf9 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203dd0)]
  | .l1050a9 => fun fr =>
      [.gpr 4 (fr.rsp - 0x1e8), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rdi, .gpr 5 fr.rbp, .gpr 12 fr.rdx,
       .gpr 13 fr.rcx, .gpr 14 fr.rsi, .gpr 15 fr.r8, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x28) 64 fr.rbx, .mem (fr.rsp - 0x20) 64 fr.r12,
       .mem (fr.rsp - 0x18) 64 fr.r13, .mem (fr.rsp - 0x10) 64 fr.r14,
       .mem (fr.rsp - 0x8) 64 fr.r15, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x2ed1) 0x2ed1,
       .fact (fr.low.toNat + 0x2ed1 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x203dd0 8, .mem 0x203dd0 64 0x12a820, .readable 0x203de0 8,
       .mem 0x203de0 64 0x129770, .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x206cf9 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203dd0)]
  | .l1050ad => fun fr =>
      [.gpr 4 (fr.rsp - 0x1e8), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rdi, .gpr 5 fr.rbp, .gpr 12 fr.rdx,
       .gpr 13 fr.rcx, .gpr 14 fr.rsi, .gpr 15 fr.r8, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x28) 64 fr.rbx, .mem (fr.rsp - 0x20) 64 fr.r12,
       .mem (fr.rsp - 0x18) 64 fr.r13, .mem (fr.rsp - 0x10) 64 fr.r14,
       .mem (fr.rsp - 0x8) 64 fr.r15, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x2ed1) 0x2ed1,
       .fact (fr.low.toNat + 0x2ed1 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l1050c1 => fun fr =>
      [.gpr 4 (fr.rsp - 0x1e8), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rdi, .gpr 5 fr.rbp, .gpr 12 fr.rdx,
       .gpr 13 fr.rcx, .gpr 14 fr.rsi, .gpr 15 fr.r8, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x28) 64 fr.rbx, .mem (fr.rsp - 0x20) 64 fr.r12,
       .mem (fr.rsp - 0x18) 64 fr.r13, .mem (fr.rsp - 0x10) 64 fr.r14,
       .mem (fr.rsp - 0x8) 64 fr.r15, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x2ed1) 0x2ed1,
       .fact (fr.low.toNat + 0x2ed1 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x203dd0 8, .mem 0x203dd0 64 0x12a820, .readable 0x203de0 8,
       .mem 0x203de0 64 0x129770, .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x206cf9 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203dd0)]
  | .l10513d => fun fr =>
      [.gpr 4 (fr.rsp - 0x1e8), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rdi, .gpr 5 fr.rbp, .gpr 12 fr.rdx,
       .gpr 13 fr.rcx, .gpr 14 fr.rsi, .gpr 15 fr.r8, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x28) 64 fr.rbx, .mem (fr.rsp - 0x20) 64 fr.r12,
       .mem (fr.rsp - 0x18) 64 fr.r13, .mem (fr.rsp - 0x10) 64 fr.r14,
       .mem (fr.rsp - 0x8) 64 fr.r15, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x2ed1) 0x2ed1,
       .fact (fr.low.toNat + 0x2ed1 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x203de0 8, .mem 0x203de0 64 0x129770, .readable 0x203e20 8,
       .mem 0x203e20 64 0x100a20, .fact (0x206cf9 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l105145 => fun fr =>
      [.gpr 4 (fr.rsp - 0x1e8), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rdi, .gpr 5 fr.rbp, .gpr 12 fr.rdx,
       .gpr 13 fr.rcx, .gpr 14 fr.rsi, .gpr 15 fr.r8, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x28) 64 fr.rbx, .mem (fr.rsp - 0x20) 64 fr.r12,
       .mem (fr.rsp - 0x18) 64 fr.r13, .mem (fr.rsp - 0x10) 64 fr.r14,
       .mem (fr.rsp - 0x8) 64 fr.r15, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x2ed1) 0x2ed1,
       .fact (fr.low.toNat + 0x2ed1 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x203de0 8, .mem 0x203de0 64 0x129770, .readable 0x203e20 8,
       .mem 0x203e20 64 0x100a20, .fact (0x206cf9 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l10518b => fun fr =>
      [.gpr 4 (fr.rsp - 0x1e8), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rdi, .gpr 5 fr.rbp, .gpr 12 fr.rdx,
       .gpr 13 fr.rcx, .gpr 14 fr.rsi, .gpr 15 fr.r8, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x28) 64 fr.rbx, .mem (fr.rsp - 0x20) 64 fr.r12,
       .mem (fr.rsp - 0x18) 64 fr.r13, .mem (fr.rsp - 0x10) 64 fr.r14,
       .mem (fr.rsp - 0x8) 64 fr.r15, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x2ed1) 0x2ed1,
       .fact (fr.low.toNat + 0x2ed1 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x203de0 8, .mem 0x203de0 64 0x129770, .readable 0x203e20 8,
       .mem 0x203e20 64 0x100a20, .fact (0x206cf9 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l10519d => fun fr =>
      [.gpr 4 (fr.rsp - 0x1e8), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rdi, .gpr 5 fr.rbp, .gpr 12 fr.rdx,
       .gpr 13 fr.rcx, .gpr 14 fr.rsi, .gpr 15 fr.r8, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x28) 64 fr.rbx, .mem (fr.rsp - 0x20) 64 fr.r12,
       .mem (fr.rsp - 0x18) 64 fr.r13, .mem (fr.rsp - 0x10) 64 fr.r14,
       .mem (fr.rsp - 0x8) 64 fr.r15, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x2ed1) 0x2ed1,
       .fact (fr.low.toNat + 0x2ed1 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x203de0 8, .mem 0x203de0 64 0x129770, .readable 0x203e20 8,
       .mem 0x203e20 64 0x100a20, .fact (0x206cf9 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l1051b1 => fun fr =>
      [.gpr 4 (fr.rsp - 0x1e8), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rdi, .gpr 5 fr.rbp, .gpr 12 fr.rdx,
       .gpr 13 fr.rcx, .gpr 14 fr.rsi, .gpr 15 fr.r8, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x28) 64 fr.rbx, .mem (fr.rsp - 0x20) 64 fr.r12,
       .mem (fr.rsp - 0x18) 64 fr.r13, .mem (fr.rsp - 0x10) 64 fr.r14,
       .mem (fr.rsp - 0x8) 64 fr.r15, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x2ed1) 0x2ed1,
       .fact (fr.low.toNat + 0x2ed1 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l105216 => fun fr =>
      [.gpr 4 (fr.rsp - 0x1e8), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rdi, .gpr 5 fr.rbp, .gpr 13 fr.rcx,
       .gpr 14 fr.rsi, .gpr 15 fr.r8, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x28) 64 fr.rbx, .mem (fr.rsp - 0x20) 64 fr.r12,
       .mem (fr.rsp - 0x18) 64 fr.r13, .mem (fr.rsp - 0x10) 64 fr.r14,
       .mem (fr.rsp - 0x8) 64 fr.r15, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x2ed1) 0x2ed1,
       .fact (fr.low.toNat + 0x2ed1 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l105256 => fun fr =>
      [.gpr 4 (fr.rsp - 0x1e8), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rdi, .gpr 5 fr.rbp, .gpr 13 fr.rcx,
       .gpr 14 fr.rsi, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩,
       .mem (fr.rsp - 0x28) 64 fr.rbx, .mem (fr.rsp - 0x20) 64 fr.r12,
       .mem (fr.rsp - 0x18) 64 fr.r13, .mem (fr.rsp - 0x10) 64 fr.r14,
       .mem (fr.rsp - 0x8) 64 fr.r15, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x2ed1) 0x2ed1,
       .fact (fr.low.toNat + 0x2ed1 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l10537f => fun fr =>
      [.gpr 4 (fr.rsp - 0x1e8), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rdi, .gpr 5 fr.rbp, .gpr 12 fr.rdx,
       .gpr 13 fr.rcx, .gpr 14 fr.rsi, .gpr 15 fr.r8, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x28) 64 fr.rbx, .mem (fr.rsp - 0x20) 64 fr.r12,
       .mem (fr.rsp - 0x18) 64 fr.r13, .mem (fr.rsp - 0x10) 64 fr.r14,
       .mem (fr.rsp - 0x8) 64 fr.r15, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x2ed1) 0x2ed1,
       .fact (fr.low.toNat + 0x2ed1 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l105393 => fun fr =>
      [.gpr 4 (fr.rsp - 0x1e8), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rdi, .gpr 5 fr.rbp, .gpr 12 fr.rdx,
       .gpr 13 fr.rcx, .gpr 14 fr.rsi, .gpr 15 fr.r8, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x28) 64 fr.rbx, .mem (fr.rsp - 0x20) 64 fr.r12,
       .mem (fr.rsp - 0x18) 64 fr.r13, .mem (fr.rsp - 0x10) 64 fr.r14,
       .mem (fr.rsp - 0x8) 64 fr.r15, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x2ed1) 0x2ed1,
       .fact (fr.low.toNat + 0x2ed1 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x203de0 8, .mem 0x203de0 64 0x129770, .readable 0x203e20 8,
       .mem 0x203e20 64 0x100a20, .fact (0x206cf9 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l105398 => fun fr =>
      [.gpr 4 (fr.rsp - 0x1e8), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rdi, .gpr 5 fr.rbp, .gpr 12 fr.rdx,
       .gpr 13 fr.rcx, .gpr 14 fr.rsi, .gpr 15 fr.r8, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x28) 64 fr.rbx, .mem (fr.rsp - 0x20) 64 fr.r12,
       .mem (fr.rsp - 0x18) 64 fr.r13, .mem (fr.rsp - 0x10) 64 fr.r14,
       .mem (fr.rsp - 0x8) 64 fr.r15, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x2ed1) 0x2ed1,
       .fact (fr.low.toNat + 0x2ed1 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x203de0 8, .mem 0x203de0 64 0x129770, .readable 0x203e20 8,
       .mem 0x203e20 64 0x100a20, .fact (0x206cf9 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l1053af => fun fr =>
      [.gpr 4 (fr.rsp - 0x1e8), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rdi, .gpr 5 fr.rbp, .gpr 12 fr.rdx,
       .gpr 13 fr.rcx, .gpr 14 fr.rsi, .gpr 15 fr.r8, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x28) 64 fr.rbx, .mem (fr.rsp - 0x20) 64 fr.r12,
       .mem (fr.rsp - 0x18) 64 fr.r13, .mem (fr.rsp - 0x10) 64 fr.r14,
       .mem (fr.rsp - 0x8) 64 fr.r15, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x2ed1) 0x2ed1,
       .fact (fr.low.toNat + 0x2ed1 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x206cf9 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203e20)]
  | .l1053cb => fun fr =>
      [.gpr 4 (fr.rsp - 0x1e8), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rdi, .gpr 5 fr.rbp, .gpr 12 fr.rdx,
       .gpr 13 fr.rcx, .gpr 14 fr.rsi, .gpr 15 fr.r8, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x28) 64 fr.rbx, .mem (fr.rsp - 0x20) 64 fr.r12,
       .mem (fr.rsp - 0x18) 64 fr.r13, .mem (fr.rsp - 0x10) 64 fr.r14,
       .mem (fr.rsp - 0x8) 64 fr.r15, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x2ed1) 0x2ed1,
       .fact (fr.low.toNat + 0x2ed1 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x203de0 8, .mem 0x203de0 64 0x129770, .readable 0x203e20 8,
       .mem 0x203e20 64 0x100a20, .fact (0x206cf9 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203de0)]
  | .l1053ef => fun fr =>
      [.gpr 4 (fr.rsp - 0x1e8), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rdi, .gpr 5 fr.rbp, .gpr 12 fr.rdx,
       .gpr 13 fr.rcx, .gpr 14 fr.rsi, .gpr 15 fr.r8, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x28) 64 fr.rbx, .mem (fr.rsp - 0x20) 64 fr.r12,
       .mem (fr.rsp - 0x18) 64 fr.r13, .mem (fr.rsp - 0x10) 64 fr.r14,
       .mem (fr.rsp - 0x8) 64 fr.r15, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x2ed1) 0x2ed1,
       .fact (fr.low.toNat + 0x2ed1 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x206cf9 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203e20)]
  | _ => fun _ => []

def labelFrame : Label → Option Refine.LabelFrame
  | .g6 l => labelFrameG6 l
  | _ => none

@[refine_layout] def frameAt : Label → Refine.Activation → List Refine.Atom
  | .g6 l => frameAtG6 l
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

def closureCode : CodeMap := sectionCode textSection [(0xa20, 0x2), (0x4f20, 0x34c), (0x537f, 0x56),
    (0x53ef, 0x26), (0x84e0, 0x3aa), (0x8890, 0x597), (0x9490, 0x11c), (0x95b0, 0x32a),
    (0x98e0, 0xdf), (0x99c0, 0x23c), (0x9c00, 0x175), (0x9f60, 0x5), (0x9f80, 0x132),
    (0xa0c0, 0xa1), (0xa170, 0xa3), (0xa280, 0x1e), (0xa2f0, 0x116), (0xf150, 0x374), (0xfb20, 0x88),
    (0x109b0, 0x1c2), (0x10b80, 0x14b), (0x15408, 0x36), (0x1b510, 0x3d4), (0x1b8f0, 0x253),
    (0x27d50, 0x11), (0x27d70, 0x79), (0x27df0, 0xa4), (0x27f50, 0x6a), (0x29560, 0x34),
    (0x295f2, 0x3d), (0x2965d, 0xee), (0x29770, 0x2c), (0x2a700, 0x45), (0x2a820, 0x2f)]

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
    (hcore : Refine.Atom.All code (lifted.locationOf .l104f20 initial).arguments initial.external
      (core.atoms lab c fr p))
    (hstart : core.start lab = .l104f20 := by rfl)
    (hentry : ∀ fr, atoms .l104f20 fr = frameInfo.entryAtoms fr := by intro _; rfl)
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

end Fn104f20

end K256.Proofs.Verify.LIR
