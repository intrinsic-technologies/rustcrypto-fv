import AesGcm.Proofs.Machine.Instructions.Memory16
import AesGcm.Proofs.Machine.Instructions.HighByteStore
import AesGcm.Proofs.Machine.LIR.Program
import AesGcm.Proofs.Copied.X86Proofs.Refine.Contract
import AesGcm.Proofs.Copied.X86Proofs.Refine.Lemma.SysVEntry

namespace AesGcm.Proofs.Machine.LIR

open AesGcm.Proofs.Machine.Instructions
open X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift

namespace Fn104010

def frameInfo : Refine.FrameInfo where
  entry := 0x104010
  frameBytes := 0x8
  stackBytes := some 0x90
  slots := []
  preserved := [3, 5, 12, 13, 14, 15]
  fpPreserved := [39, 50, 51]
  clobbers := [1, 6, 9, 10]
  callSlots := [(0x201210, 0x103880), (0x201230, 0x101230)]

def labelFrameG4 : Label.G4 → Option Refine.LabelFrame
  | .l104010 => some ⟨0x0, [(1, 1), (2, 2), (3, 3), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9),
      (12, 12), (13, 13), (14, 14), (15, 15), (39, 39), (50, 50),
      (51, 51)], [], [(0x201210, 0x103880), (0x201230, 0x101230)]⟩
  | .l104020 => some ⟨0x8, [(1, 1), (2, 2), (3, 3), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12),
      (13, 13), (14, 14), (15, 15), (39, 39), (50, 50), (51, 51)], [], [(0x201210, 0x103880),
      (0x201230, 0x101230)]⟩
  | .l104029 => some ⟨0x8, [(1, 1), (2, 2), (3, 3), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12),
      (13, 13), (14, 14), (15, 15), (39, 39), (50, 50), (51, 51)], [], [(0x201210, 0x103880),
      (0x201230, 0x101230)]⟩
  | .l10408b => some ⟨0x8, [(0, 1), (2, 2), (3, 3), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12),
      (13, 13), (14, 14), (15, 15), (39, 39), (50, 50), (51, 51)], [], [(0x201210, 0x103880),
      (0x201230, 0x101230)]⟩
  | .l104094 => some ⟨0x8, [(0, 1), (2, 2), (3, 3), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12),
      (13, 13), (14, 14), (15, 15), (39, 39), (50, 50), (51, 51)], [], [(0x201210, 0x103880),
      (0x201230, 0x101230)]⟩
  | .l1040f5 => some ⟨0x8, [(0, 1), (2, 2), (3, 3), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12),
      (13, 13), (14, 14), (15, 15), (39, 39), (50, 50), (51, 51)], [], [(0x201210, 0x103880),
      (0x201230, 0x101230)]⟩
  | .l1040fe => some ⟨0x8, [(0, 1), (2, 2), (3, 3), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12),
      (13, 13), (14, 14), (15, 15), (39, 39), (50, 50), (51, 51)], [], [(0x201210, 0x103880),
      (0x201230, 0x101230)]⟩
  | .l10415f => some ⟨0x8, [(0, 1), (2, 2), (3, 3), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12),
      (13, 13), (14, 14), (15, 15), (39, 39), (50, 50), (51, 51)], [], [(0x201210, 0x103880),
      (0x201230, 0x101230)]⟩
  | .l104168 => some ⟨0x8, [(0, 1), (2, 2), (3, 3), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12),
      (13, 13), (14, 14), (15, 15), (39, 39), (50, 50), (51, 51)], [], [(0x201210, 0x103880),
      (0x201230, 0x101230)]⟩
  | .l1041c9 => some ⟨0x8, [(0, 1), (2, 2), (3, 3), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12),
      (13, 13), (14, 14), (15, 15), (39, 39), (50, 50), (51, 51)], [], [(0x201210, 0x103880),
      (0x201230, 0x101230)]⟩
  | _ => none

@[refine_layout] def frameAtG4 : Label.G4 → Refine.Activation → List Refine.Atom
  | .l104010 => fun fr =>
      [.gpr 4 fr.rsp, .reg 22 ⟨1, 0⟩, .gpr 1 fr.rcx, .gpr 2 fr.rdx, .gpr 3 fr.rbx, .gpr 5 fr.rbp,
       .gpr 6 fr.rsi, .gpr 7 fr.rdi, .gpr 8 fr.r8, .gpr 9 fr.r9, .gpr 12 fr.r12, .gpr 13 fr.r13,
       .gpr 14 fr.r14, .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x90) 0x90,
       .fact (fr.low.toNat + 0x90 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x201210 8, .mem 0x201210 64 0x103880, .readable 0x201230 8,
       .mem 0x201230 64 0x101230, .fact (0x2012c8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201210)]
  | .l104020 => fun fr =>
      [.gpr 4 (fr.rsp - 0x8), .reg 22 ⟨1, 0⟩, .gpr 1 fr.rcx, .gpr 2 fr.rdx, .gpr 3 fr.rbx,
       .gpr 5 fr.rbp, .gpr 6 fr.rsi, .gpr 7 fr.rdi, .gpr 8 fr.r8, .gpr 12 fr.r12, .gpr 13 fr.r13,
       .gpr 14 fr.r14, .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x90) 0x90,
       .fact (fr.low.toNat + 0x90 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x201210 8, .mem 0x201210 64 0x103880, .readable 0x201230 8,
       .mem 0x201230 64 0x101230, .fact (0x2012c8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201210)]
  | .l104029 => fun fr =>
      [.gpr 4 (fr.rsp - 0x8), .reg 22 ⟨1, 0⟩, .gpr 1 fr.rcx, .gpr 2 fr.rdx, .gpr 3 fr.rbx,
       .gpr 5 fr.rbp, .gpr 6 fr.rsi, .gpr 7 fr.rdi, .gpr 8 fr.r8, .gpr 12 fr.r12, .gpr 13 fr.r13,
       .gpr 14 fr.r14, .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x90) 0x90,
       .fact (fr.low.toNat + 0x90 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x201210 8, .mem 0x201210 64 0x103880, .readable 0x201230 8,
       .mem 0x201230 64 0x101230, .fact (0x2012c8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201210)]
  | .l10408b => fun fr =>
      [.gpr 4 (fr.rsp - 0x8), .reg 22 ⟨1, 0⟩, .gpr 0 fr.rcx, .gpr 2 fr.rdx, .gpr 3 fr.rbx,
       .gpr 5 fr.rbp, .gpr 6 fr.rsi, .gpr 7 fr.rdi, .gpr 8 fr.r8, .gpr 12 fr.r12, .gpr 13 fr.r13,
       .gpr 14 fr.r14, .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x90) 0x90,
       .fact (fr.low.toNat + 0x90 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x201210 8, .mem 0x201210 64 0x103880, .readable 0x201230 8,
       .mem 0x201230 64 0x101230, .fact (0x2012c8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201210)]
  | .l104094 => fun fr =>
      [.gpr 4 (fr.rsp - 0x8), .reg 22 ⟨1, 0⟩, .gpr 0 fr.rcx, .gpr 2 fr.rdx, .gpr 3 fr.rbx,
       .gpr 5 fr.rbp, .gpr 6 fr.rsi, .gpr 7 fr.rdi, .gpr 8 fr.r8, .gpr 12 fr.r12, .gpr 13 fr.r13,
       .gpr 14 fr.r14, .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x90) 0x90,
       .fact (fr.low.toNat + 0x90 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x201210 8, .mem 0x201210 64 0x103880, .readable 0x201230 8,
       .mem 0x201230 64 0x101230, .fact (0x2012c8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201210)]
  | .l1040f5 => fun fr =>
      [.gpr 4 (fr.rsp - 0x8), .reg 22 ⟨1, 0⟩, .gpr 0 fr.rcx, .gpr 2 fr.rdx, .gpr 3 fr.rbx,
       .gpr 5 fr.rbp, .gpr 6 fr.rsi, .gpr 7 fr.rdi, .gpr 8 fr.r8, .gpr 12 fr.r12, .gpr 13 fr.r13,
       .gpr 14 fr.r14, .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x90) 0x90,
       .fact (fr.low.toNat + 0x90 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x201210 8, .mem 0x201210 64 0x103880, .readable 0x201230 8,
       .mem 0x201230 64 0x101230, .fact (0x2012c8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201210)]
  | .l1040fe => fun fr =>
      [.gpr 4 (fr.rsp - 0x8), .reg 22 ⟨1, 0⟩, .gpr 0 fr.rcx, .gpr 2 fr.rdx, .gpr 3 fr.rbx,
       .gpr 5 fr.rbp, .gpr 6 fr.rsi, .gpr 7 fr.rdi, .gpr 8 fr.r8, .gpr 12 fr.r12, .gpr 13 fr.r13,
       .gpr 14 fr.r14, .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x90) 0x90,
       .fact (fr.low.toNat + 0x90 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x201210 8, .mem 0x201210 64 0x103880, .readable 0x201230 8,
       .mem 0x201230 64 0x101230, .fact (0x2012c8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201210)]
  | .l10415f => fun fr =>
      [.gpr 4 (fr.rsp - 0x8), .reg 22 ⟨1, 0⟩, .gpr 0 fr.rcx, .gpr 2 fr.rdx, .gpr 3 fr.rbx,
       .gpr 5 fr.rbp, .gpr 6 fr.rsi, .gpr 7 fr.rdi, .gpr 8 fr.r8, .gpr 12 fr.r12, .gpr 13 fr.r13,
       .gpr 14 fr.r14, .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x90) 0x90,
       .fact (fr.low.toNat + 0x90 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x201210 8, .mem 0x201210 64 0x103880, .readable 0x201230 8,
       .mem 0x201230 64 0x101230, .fact (0x2012c8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201210)]
  | .l104168 => fun fr =>
      [.gpr 4 (fr.rsp - 0x8), .reg 22 ⟨1, 0⟩, .gpr 0 fr.rcx, .gpr 2 fr.rdx, .gpr 3 fr.rbx,
       .gpr 5 fr.rbp, .gpr 6 fr.rsi, .gpr 7 fr.rdi, .gpr 8 fr.r8, .gpr 12 fr.r12, .gpr 13 fr.r13,
       .gpr 14 fr.r14, .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x90) 0x90,
       .fact (fr.low.toNat + 0x90 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x201210 8, .mem 0x201210 64 0x103880, .readable 0x201230 8,
       .mem 0x201230 64 0x101230, .fact (0x2012c8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201210)]
  | .l1041c9 => fun fr =>
      [.gpr 4 (fr.rsp - 0x8), .reg 22 ⟨1, 0⟩, .gpr 0 fr.rcx, .gpr 2 fr.rdx, .gpr 3 fr.rbx,
       .gpr 5 fr.rbp, .gpr 6 fr.rsi, .gpr 7 fr.rdi, .gpr 8 fr.r8, .gpr 12 fr.r12, .gpr 13 fr.r13,
       .gpr 14 fr.r14, .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x90) 0x90,
       .fact (fr.low.toNat + 0x90 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x201210 8, .mem 0x201210 64 0x103880, .readable 0x201230 8,
       .mem 0x201230 64 0x101230, .fact (0x2012c8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201210)]
  | _ => fun _ => []

def labelFrameG5 : Label.G5 → Option Refine.LabelFrame
  | .l1041d2 => some ⟨0x8, [(0, 1), (2, 2), (3, 3), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12),
      (13, 13), (14, 14), (15, 15), (39, 39), (50, 50), (51, 51)], [], [(0x201210, 0x103880),
      (0x201230, 0x101230)]⟩
  | .l104233 => some ⟨0x8, [(0, 1), (2, 2), (3, 3), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12),
      (13, 13), (14, 14), (15, 15), (39, 39), (50, 50), (51, 51)], [], [(0x201210, 0x103880),
      (0x201230, 0x101230)]⟩
  | .l10423c => some ⟨0x8, [(0, 1), (2, 2), (3, 3), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12),
      (13, 13), (14, 14), (15, 15), (39, 39), (50, 50), (51, 51)], [], [(0x201210, 0x103880),
      (0x201230, 0x101230)]⟩
  | .l10429d => some ⟨0x8, [(0, 1), (2, 2), (3, 3), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12),
      (13, 13), (14, 14), (15, 15), (39, 39), (50, 50), (51, 51)], [], [(0x201210, 0x103880),
      (0x201230, 0x101230)]⟩
  | .l1042a6 => some ⟨0x8, [(0, 1), (2, 2), (3, 3), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12),
      (13, 13), (14, 14), (15, 15), (39, 39), (50, 50), (51, 51)], [], [(0x201210, 0x103880),
      (0x201230, 0x101230)]⟩
  | .l104303 => some ⟨0x8, [(0, 1), (2, 2), (3, 3), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12),
      (13, 13), (14, 14), (15, 15), (39, 39), (50, 50), (51, 51)], [], [(0x201210, 0x103880),
      (0x201230, 0x101230)]⟩
  | .l104308 => some ⟨0x8, [(0, 1), (2, 2), (3, 3), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12),
      (13, 13), (14, 14), (15, 15), (39, 39), (50, 50), (51, 51)], [], []⟩
  | .l10434d => some ⟨0x8, [(2, 2), (3, 3), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13),
      (14, 14), (15, 15), (39, 39), (50, 50), (51, 51)], [], [(0x201210, 0x103880),
      (0x201230, 0x101230)]⟩
  | .l10435c => some ⟨0x8, [(1, 1), (2, 2), (3, 3), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12),
      (13, 13), (14, 14), (15, 15), (39, 39), (50, 50), (51, 51)], [], [(0x201210, 0x103880),
      (0x201230, 0x101230)]⟩
  | .l10435f => some ⟨0x8, [(2, 2), (3, 3), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13),
      (14, 14), (15, 15), (39, 39), (50, 50), (51, 51)], [], [(0x201210, 0x103880),
      (0x201230, 0x101230)]⟩
  | _ => none

@[refine_layout] def frameAtG5 : Label.G5 → Refine.Activation → List Refine.Atom
  | .l1041d2 => fun fr =>
      [.gpr 4 (fr.rsp - 0x8), .reg 22 ⟨1, 0⟩, .gpr 0 fr.rcx, .gpr 2 fr.rdx, .gpr 3 fr.rbx,
       .gpr 5 fr.rbp, .gpr 6 fr.rsi, .gpr 7 fr.rdi, .gpr 8 fr.r8, .gpr 12 fr.r12, .gpr 13 fr.r13,
       .gpr 14 fr.r14, .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x90) 0x90,
       .fact (fr.low.toNat + 0x90 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x201210 8, .mem 0x201210 64 0x103880, .readable 0x201230 8,
       .mem 0x201230 64 0x101230, .fact (0x2012c8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201210)]
  | .l104233 => fun fr =>
      [.gpr 4 (fr.rsp - 0x8), .reg 22 ⟨1, 0⟩, .gpr 0 fr.rcx, .gpr 2 fr.rdx, .gpr 3 fr.rbx,
       .gpr 5 fr.rbp, .gpr 6 fr.rsi, .gpr 7 fr.rdi, .gpr 8 fr.r8, .gpr 12 fr.r12, .gpr 13 fr.r13,
       .gpr 14 fr.r14, .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x90) 0x90,
       .fact (fr.low.toNat + 0x90 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x201210 8, .mem 0x201210 64 0x103880, .readable 0x201230 8,
       .mem 0x201230 64 0x101230, .fact (0x2012c8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201210)]
  | .l10423c => fun fr =>
      [.gpr 4 (fr.rsp - 0x8), .reg 22 ⟨1, 0⟩, .gpr 0 fr.rcx, .gpr 2 fr.rdx, .gpr 3 fr.rbx,
       .gpr 5 fr.rbp, .gpr 6 fr.rsi, .gpr 7 fr.rdi, .gpr 8 fr.r8, .gpr 12 fr.r12, .gpr 13 fr.r13,
       .gpr 14 fr.r14, .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x90) 0x90,
       .fact (fr.low.toNat + 0x90 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x201210 8, .mem 0x201210 64 0x103880, .readable 0x201230 8,
       .mem 0x201230 64 0x101230, .fact (0x2012c8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201210)]
  | .l10429d => fun fr =>
      [.gpr 4 (fr.rsp - 0x8), .reg 22 ⟨1, 0⟩, .gpr 0 fr.rcx, .gpr 2 fr.rdx, .gpr 3 fr.rbx,
       .gpr 5 fr.rbp, .gpr 6 fr.rsi, .gpr 7 fr.rdi, .gpr 8 fr.r8, .gpr 12 fr.r12, .gpr 13 fr.r13,
       .gpr 14 fr.r14, .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x90) 0x90,
       .fact (fr.low.toNat + 0x90 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x201210 8, .mem 0x201210 64 0x103880, .readable 0x201230 8,
       .mem 0x201230 64 0x101230, .fact (0x2012c8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201210)]
  | .l1042a6 => fun fr =>
      [.gpr 4 (fr.rsp - 0x8), .reg 22 ⟨1, 0⟩, .gpr 0 fr.rcx, .gpr 2 fr.rdx, .gpr 3 fr.rbx,
       .gpr 5 fr.rbp, .gpr 6 fr.rsi, .gpr 7 fr.rdi, .gpr 8 fr.r8, .gpr 12 fr.r12, .gpr 13 fr.r13,
       .gpr 14 fr.r14, .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x90) 0x90,
       .fact (fr.low.toNat + 0x90 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x201210 8, .mem 0x201210 64 0x103880, .readable 0x201230 8,
       .mem 0x201230 64 0x101230, .fact (0x2012c8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201210)]
  | .l104303 => fun fr =>
      [.gpr 4 (fr.rsp - 0x8), .reg 22 ⟨1, 0⟩, .gpr 0 fr.rcx, .gpr 2 fr.rdx, .gpr 3 fr.rbx,
       .gpr 5 fr.rbp, .gpr 6 fr.rsi, .gpr 7 fr.rdi, .gpr 8 fr.r8, .gpr 12 fr.r12, .gpr 13 fr.r13,
       .gpr 14 fr.r14, .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x90) 0x90,
       .fact (fr.low.toNat + 0x90 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x201210 8, .mem 0x201210 64 0x103880, .readable 0x201230 8,
       .mem 0x201230 64 0x101230, .fact (0x2012c8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201210)]
  | .l104308 => fun fr =>
      [.gpr 4 (fr.rsp - 0x8), .reg 22 ⟨1, 0⟩, .gpr 0 fr.rcx, .gpr 2 fr.rdx, .gpr 3 fr.rbx,
       .gpr 5 fr.rbp, .gpr 6 fr.rsi, .gpr 7 fr.rdi, .gpr 8 fr.r8, .gpr 12 fr.r12, .gpr 13 fr.r13,
       .gpr 14 fr.r14, .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x90) 0x90,
       .fact (fr.low.toNat + 0x90 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l10434d => fun fr =>
      [.gpr 4 (fr.rsp - 0x8), .reg 22 ⟨1, 0⟩, .gpr 2 fr.rdx, .gpr 3 fr.rbx, .gpr 5 fr.rbp,
       .gpr 6 fr.rsi, .gpr 7 fr.rdi, .gpr 8 fr.r8, .gpr 12 fr.r12, .gpr 13 fr.r13, .gpr 14 fr.r14,
       .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩,
       .readable fr.rsp 8, .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x90) 0x90, .fact (fr.low.toNat + 0x90 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x201210 8, .mem 0x201210 64 0x103880,
       .readable 0x201230 8, .mem 0x201230 64 0x101230,
       .fact (0x2012c8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201210)]
  | .l10435c => fun fr =>
      [.gpr 4 (fr.rsp - 0x8), .reg 22 ⟨1, 0⟩, .gpr 1 fr.rcx, .gpr 2 fr.rdx, .gpr 3 fr.rbx,
       .gpr 5 fr.rbp, .gpr 6 fr.rsi, .gpr 7 fr.rdi, .gpr 8 fr.r8, .gpr 12 fr.r12, .gpr 13 fr.r13,
       .gpr 14 fr.r14, .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x90) 0x90,
       .fact (fr.low.toNat + 0x90 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x201210 8, .mem 0x201210 64 0x103880, .readable 0x201230 8,
       .mem 0x201230 64 0x101230, .fact (0x2012c8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201210)]
  | .l10435f => fun fr =>
      [.gpr 4 (fr.rsp - 0x8), .reg 22 ⟨1, 0⟩, .gpr 2 fr.rdx, .gpr 3 fr.rbx, .gpr 5 fr.rbp,
       .gpr 6 fr.rsi, .gpr 7 fr.rdi, .gpr 8 fr.r8, .gpr 12 fr.r12, .gpr 13 fr.r13, .gpr 14 fr.r14,
       .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩,
       .readable fr.rsp 8, .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x90) 0x90, .fact (fr.low.toNat + 0x90 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x201210 8, .mem 0x201210 64 0x103880,
       .readable 0x201230 8, .mem 0x201230 64 0x101230,
       .fact (0x2012c8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201210)]
  | _ => fun _ => []

def labelFrame : Label → Option Refine.LabelFrame
  | .g4 l => labelFrameG4 l
  | .g5 l => labelFrameG5 l
  | _ => none

@[refine_layout] def frameAt : Label → Refine.Activation → List Refine.Atom
  | .g4 l => frameAtG4 l
  | .g5 l => frameAtG5 l
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

def closureCode : CodeMap := sectionCode textSection [(0x1230, 0x2), (0x3837, 0x3d), (0x3880, 0x2c),
    (0x4010, 0x35e)]

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
    (hcore : Refine.Atom.All code (lifted.locationOf .l104010 initial).arguments initial.external
      (core.atoms lab c fr p))
    (hstart : core.start lab = .l104010 := by rfl)
    (hentry : ∀ fr, atoms .l104010 fr = frameInfo.entryAtoms fr := by intro _; rfl)
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

end Fn104010

end AesGcm.Proofs.Machine.LIR
