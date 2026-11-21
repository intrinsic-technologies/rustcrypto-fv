import AesGcm.Proofs.Machine.Instructions.Memory16
import AesGcm.Proofs.Machine.Instructions.HighByteStore
import AesGcm.Proofs.Machine.LIR.Program
import AesGcm.Proofs.Copied.X86Proofs.Refine.Contract
import AesGcm.Proofs.Copied.X86Proofs.Refine.Lemma.SysVEntry

namespace AesGcm.Proofs.Machine.LIR

open AesGcm.Proofs.Machine.Instructions
open X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift

namespace Fn102520

def frameInfo : Refine.FrameInfo where
  entry := 0x102520
  frameBytes := 0xc8
  stackBytes := some 0x940
  slots := [(3, 0x30), (5, 0x8), (12, 0x28), (13, 0x20), (14, 0x18), (15, 0x10)]
  preserved := [3, 5, 12, 13, 14, 15]
  fpPreserved := [39, 50, 51]
  clobbers := [0, 1, 2, 6, 7, 8, 9, 10, 11]
  callSlots := [(0x201208, 0x103f00), (0x201210, 0x103880), (0x201228, 0x103eb0), (0x201230, 0x101230)]

def labelFrameG2 : Label.G2 → Option Refine.LabelFrame
  | .l102520 => some ⟨0x0, [(1, 1), (2, 2), (3, 3), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9),
      (12, 12), (13, 13), (14, 14), (15, 15), (39, 39), (50, 50),
      (51, 51)], [], [(0x201208, 0x103f00), (0x201210, 0x103880), (0x201228, 0x103eb0),
      (0x201230, 0x101230)]⟩
  | .l102558 => some ⟨0xc8, [(1, 1), (2, 2), (3, 7), (5, 5), (6, 6), (8, 8), (9, 9), (13, 13),
      (14, 14), (15, 15), (39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], []⟩
  | .l102560 => some ⟨0xc8, [(1, 1), (2, 2), (3, 7), (5, 5), (6, 6), (8, 8), (9, 9), (13, 13),
      (14, 14), (15, 15), (39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], [(0x201208, 0x103f00), (0x201210, 0x103880),
      (0x201228, 0x103eb0), (0x201230, 0x101230)]⟩
  | .l1025c2 => some ⟨0xc8, [(14, 9), (39, 39), (50, 50), (51, 51)], [(0x70, 7), (0x68, 6),
      (0x60, 1), (0x58, 8), (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15),
      (0x8, 5)], [(0x201208, 0x103f00), (0x201210, 0x103880), (0x201228, 0x103eb0),
      (0x201230, 0x101230)]⟩
  | .l1025f9 => some ⟨0xc8, [(14, 9), (39, 39), (50, 50), (51, 51)], [(0x70, 7), (0x68, 6),
      (0x60, 1), (0x58, 8), (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15),
      (0x8, 5)], [(0x201208, 0x103f00), (0x201210, 0x103880), (0x201228, 0x103eb0),
      (0x201230, 0x101230)]⟩
  | .l102642 => some ⟨0xc8, [(39, 39), (50, 50), (51, 51)], [(0x70, 7), (0x68, 6), (0x60, 1),
      (0x58, 8), (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15),
      (0x8, 5)], [(0x201208, 0x103f00), (0x201210, 0x103880), (0x201228, 0x103eb0),
      (0x201230, 0x101230)]⟩
  | .l10264a => some ⟨0xc8, [(39, 39), (50, 50), (51, 51)], [(0x70, 7), (0x68, 6), (0x60, 1),
      (0x58, 8), (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15),
      (0x8, 5)], [(0x201208, 0x103f00), (0x201228, 0x103eb0)]⟩
  | .l10264f => some ⟨0xc8, [(14, 9), (39, 39), (50, 50), (51, 51)], [(0x70, 7), (0x68, 6),
      (0x60, 1), (0x58, 8), (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15),
      (0x8, 5)], [(0x201208, 0x103f00), (0x201210, 0x103880), (0x201228, 0x103eb0),
      (0x201230, 0x101230)]⟩
  | .l10265e => some ⟨0xc8, [(39, 39), (50, 50), (51, 51)], [(0x70, 7), (0x68, 6), (0x60, 1),
      (0x58, 8), (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15),
      (0x8, 5)], [(0x201208, 0x103f00), (0x201210, 0x103880), (0x201228, 0x103eb0),
      (0x201230, 0x101230)]⟩
  | .l102683 => some ⟨0xc8, [(39, 39), (50, 50), (51, 51)], [(0x70, 7), (0x68, 6), (0x60, 1),
      (0x58, 8), (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15),
      (0x8, 5)], [(0x201208, 0x103f00), (0x201210, 0x103880), (0x201228, 0x103eb0),
      (0x201230, 0x101230)]⟩
  | .l1026a2 => some ⟨0xc8, [(39, 39), (50, 50), (51, 51)], [(0x70, 7), (0x68, 6), (0x60, 1),
      (0x58, 8), (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15),
      (0x8, 5)], [(0x201208, 0x103f00), (0x201210, 0x103880), (0x201228, 0x103eb0),
      (0x201230, 0x101230)]⟩
  | .l1026ce => some ⟨0xc8, [(39, 39), (50, 50), (51, 51)], [(0x70, 7), (0x68, 6), (0x60, 1),
      (0x58, 8), (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15),
      (0x8, 5)], [(0x201208, 0x103f00), (0x201228, 0x103eb0)]⟩
  | .l1026de => some ⟨0xc8, [(39, 39), (50, 50), (51, 51)], [(0x70, 7), (0x68, 6), (0x60, 1),
      (0x58, 8), (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15),
      (0x8, 5)], [(0x201208, 0x103f00), (0x201228, 0x103eb0)]⟩
  | .l102707 => some ⟨0xc8, [(3, 7), (39, 39), (50, 50), (51, 51)], [(0x70, 7), (0x68, 6),
      (0x60, 1), (0x58, 8), (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15),
      (0x8, 5)], []⟩
  | .l10270a => some ⟨0xc8, [(3, 7), (39, 39), (50, 50), (51, 51)], [(0x30, 3), (0x28, 12),
      (0x20, 13), (0x18, 14), (0x10, 15), (0x8, 5)], []⟩
  | _ => none

@[refine_layout] def frameAtG2 : Label.G2 → Refine.Activation → List Refine.Atom
  | .l102520 => fun fr =>
      [.gpr 4 fr.rsp, .reg 22 ⟨1, 0⟩, .gpr 1 fr.rcx, .gpr 2 fr.rdx, .gpr 3 fr.rbx, .gpr 5 fr.rbp,
       .gpr 6 fr.rsi, .gpr 7 fr.rdi, .gpr 8 fr.r8, .gpr 9 fr.r9, .gpr 12 fr.r12, .gpr 13 fr.r13,
       .gpr 14 fr.r14, .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x940) 0x940,
       .fact (fr.low.toNat + 0x940 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x201208 8, .mem 0x201208 64 0x103f00, .readable 0x201210 8,
       .mem 0x201210 64 0x103880, .readable 0x201228 8, .mem 0x201228 64 0x103eb0,
       .readable 0x201230 8, .mem 0x201230 64 0x101230,
       .fact (0x201b78 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201208)]
  | .l102558 => fun fr =>
      [.gpr 4 (fr.rsp - 0xc8), .reg 22 ⟨1, 0⟩, .gpr 1 fr.rcx, .gpr 2 fr.rdx, .gpr 3 fr.rdi,
       .gpr 5 fr.rbp, .gpr 6 fr.rsi, .gpr 8 fr.r8, .gpr 9 fr.r9, .gpr 13 fr.r13, .gpr 14 fr.r14,
       .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x940) 0x940, .fact (fr.low.toNat + 0x940 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8)]
  | .l102560 => fun fr =>
      [.gpr 4 (fr.rsp - 0xc8), .reg 22 ⟨1, 0⟩, .gpr 1 fr.rcx, .gpr 2 fr.rdx, .gpr 3 fr.rdi,
       .gpr 5 fr.rbp, .gpr 6 fr.rsi, .gpr 8 fr.r8, .gpr 9 fr.r9, .gpr 13 fr.r13, .gpr 14 fr.r14,
       .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x940) 0x940, .fact (fr.low.toNat + 0x940 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x201208 8, .mem 0x201208 64 0x103f00,
       .readable 0x201210 8, .mem 0x201210 64 0x103880, .readable 0x201228 8,
       .mem 0x201228 64 0x103eb0, .readable 0x201230 8, .mem 0x201230 64 0x101230,
       .fact (0x201b78 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201208)]
  | .l1025c2 => fun fr =>
      [.gpr 4 (fr.rsp - 0xc8), .reg 22 ⟨1, 0⟩, .gpr 14 fr.r9, .reg 39 ⟨32, fr.mxcsr⟩,
       .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x70) 64 fr.rdi,
       .mem (fr.rsp - 0x68) 64 fr.rsi, .mem (fr.rsp - 0x60) 64 fr.rcx,
       .mem (fr.rsp - 0x58) 64 fr.r8, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x940) 0x940,
       .fact (fr.low.toNat + 0x940 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x201208 8, .mem 0x201208 64 0x103f00, .readable 0x201210 8,
       .mem 0x201210 64 0x103880, .readable 0x201228 8, .mem 0x201228 64 0x103eb0,
       .readable 0x201230 8, .mem 0x201230 64 0x101230,
       .fact (0x201b78 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201208)]
  | .l1025f9 => fun fr =>
      [.gpr 4 (fr.rsp - 0xc8), .reg 22 ⟨1, 0⟩, .gpr 14 fr.r9, .reg 39 ⟨32, fr.mxcsr⟩,
       .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x70) 64 fr.rdi,
       .mem (fr.rsp - 0x68) 64 fr.rsi, .mem (fr.rsp - 0x60) 64 fr.rcx,
       .mem (fr.rsp - 0x58) 64 fr.r8, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x940) 0x940,
       .fact (fr.low.toNat + 0x940 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x201208 8, .mem 0x201208 64 0x103f00, .readable 0x201210 8,
       .mem 0x201210 64 0x103880, .readable 0x201228 8, .mem 0x201228 64 0x103eb0,
       .readable 0x201230 8, .mem 0x201230 64 0x101230,
       .fact (0x201b78 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201208)]
  | .l102642 => fun fr =>
      [.gpr 4 (fr.rsp - 0xc8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x70) 64 fr.rdi, .mem (fr.rsp - 0x68) 64 fr.rsi,
       .mem (fr.rsp - 0x60) 64 fr.rcx, .mem (fr.rsp - 0x58) 64 fr.r8,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x940) 0x940, .fact (fr.low.toNat + 0x940 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x201208 8, .mem 0x201208 64 0x103f00,
       .readable 0x201210 8, .mem 0x201210 64 0x103880, .readable 0x201228 8,
       .mem 0x201228 64 0x103eb0, .readable 0x201230 8, .mem 0x201230 64 0x101230,
       .fact (0x201b78 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201208)]
  | .l10264a => fun fr =>
      [.gpr 4 (fr.rsp - 0xc8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x70) 64 fr.rdi, .mem (fr.rsp - 0x68) 64 fr.rsi,
       .mem (fr.rsp - 0x60) 64 fr.rcx, .mem (fr.rsp - 0x58) 64 fr.r8,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x940) 0x940, .fact (fr.low.toNat + 0x940 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x201208 8, .mem 0x201208 64 0x103f00,
       .readable 0x201228 8, .mem 0x201228 64 0x103eb0,
       .fact (0x201b70 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201208)]
  | .l10264f => fun fr =>
      [.gpr 4 (fr.rsp - 0xc8), .reg 22 ⟨1, 0⟩, .gpr 14 fr.r9, .reg 39 ⟨32, fr.mxcsr⟩,
       .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x70) 64 fr.rdi,
       .mem (fr.rsp - 0x68) 64 fr.rsi, .mem (fr.rsp - 0x60) 64 fr.rcx,
       .mem (fr.rsp - 0x58) 64 fr.r8, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x940) 0x940,
       .fact (fr.low.toNat + 0x940 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x201208 8, .mem 0x201208 64 0x103f00, .readable 0x201210 8,
       .mem 0x201210 64 0x103880, .readable 0x201228 8, .mem 0x201228 64 0x103eb0,
       .readable 0x201230 8, .mem 0x201230 64 0x101230,
       .fact (0x201b78 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201208)]
  | .l10265e => fun fr =>
      [.gpr 4 (fr.rsp - 0xc8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x70) 64 fr.rdi, .mem (fr.rsp - 0x68) 64 fr.rsi,
       .mem (fr.rsp - 0x60) 64 fr.rcx, .mem (fr.rsp - 0x58) 64 fr.r8,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x940) 0x940, .fact (fr.low.toNat + 0x940 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x201208 8, .mem 0x201208 64 0x103f00,
       .readable 0x201210 8, .mem 0x201210 64 0x103880, .readable 0x201228 8,
       .mem 0x201228 64 0x103eb0, .readable 0x201230 8, .mem 0x201230 64 0x101230,
       .fact (0x201b78 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201208)]
  | .l102683 => fun fr =>
      [.gpr 4 (fr.rsp - 0xc8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x70) 64 fr.rdi, .mem (fr.rsp - 0x68) 64 fr.rsi,
       .mem (fr.rsp - 0x60) 64 fr.rcx, .mem (fr.rsp - 0x58) 64 fr.r8,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x940) 0x940, .fact (fr.low.toNat + 0x940 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x201208 8, .mem 0x201208 64 0x103f00,
       .readable 0x201210 8, .mem 0x201210 64 0x103880, .readable 0x201228 8,
       .mem 0x201228 64 0x103eb0, .readable 0x201230 8, .mem 0x201230 64 0x101230,
       .fact (0x201b78 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201208)]
  | .l1026a2 => fun fr =>
      [.gpr 4 (fr.rsp - 0xc8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x70) 64 fr.rdi, .mem (fr.rsp - 0x68) 64 fr.rsi,
       .mem (fr.rsp - 0x60) 64 fr.rcx, .mem (fr.rsp - 0x58) 64 fr.r8,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x940) 0x940, .fact (fr.low.toNat + 0x940 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x201208 8, .mem 0x201208 64 0x103f00,
       .readable 0x201210 8, .mem 0x201210 64 0x103880, .readable 0x201228 8,
       .mem 0x201228 64 0x103eb0, .readable 0x201230 8, .mem 0x201230 64 0x101230,
       .fact (0x201b78 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201208)]
  | .l1026ce => fun fr =>
      [.gpr 4 (fr.rsp - 0xc8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x70) 64 fr.rdi, .mem (fr.rsp - 0x68) 64 fr.rsi,
       .mem (fr.rsp - 0x60) 64 fr.rcx, .mem (fr.rsp - 0x58) 64 fr.r8,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x940) 0x940, .fact (fr.low.toNat + 0x940 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x201208 8, .mem 0x201208 64 0x103f00,
       .readable 0x201228 8, .mem 0x201228 64 0x103eb0,
       .fact (0x201b70 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201208)]
  | .l1026de => fun fr =>
      [.gpr 4 (fr.rsp - 0xc8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x70) 64 fr.rdi, .mem (fr.rsp - 0x68) 64 fr.rsi,
       .mem (fr.rsp - 0x60) 64 fr.rcx, .mem (fr.rsp - 0x58) 64 fr.r8,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x940) 0x940, .fact (fr.low.toNat + 0x940 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x201208 8, .mem 0x201208 64 0x103f00,
       .readable 0x201228 8, .mem 0x201228 64 0x103eb0,
       .fact (0x201b70 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201208)]
  | .l102707 => fun fr =>
      [.gpr 4 (fr.rsp - 0xc8), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rdi, .reg 39 ⟨32, fr.mxcsr⟩,
       .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x70) 64 fr.rdi,
       .mem (fr.rsp - 0x68) 64 fr.rsi, .mem (fr.rsp - 0x60) 64 fr.rcx,
       .mem (fr.rsp - 0x58) 64 fr.r8, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x940) 0x940,
       .fact (fr.low.toNat + 0x940 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l10270a => fun fr =>
      [.gpr 4 (fr.rsp - 0xc8), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rdi, .reg 39 ⟨32, fr.mxcsr⟩,
       .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x940) 0x940,
       .fact (fr.low.toNat + 0x940 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | _ => fun _ => []

def labelFrame : Label → Option Refine.LabelFrame
  | .g2 l => labelFrameG2 l
  | _ => none

@[refine_layout] def frameAt : Label → Refine.Activation → List Refine.Atom
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

def closureCode : CodeMap := sectionCode textSection [(0x0, 0x29a), (0x2a0, 0x2d4), (0x580, 0x2a2),
    (0x830, 0x2d4), (0xb10, 0x711), (0x1230, 0x2), (0x1800, 0x412), (0x2520, 0x1ff),
    (0x2bd0, 0x8ca), (0x34a0, 0x13), (0x34c0, 0xf), (0x34d0, 0x4d), (0x3837, 0x3d), (0x3880, 0x2c),
    (0x3c70, 0xc8), (0x3eb0, 0x45), (0x3f00, 0x2f), (0x5100, 0x6c0), (0x7050, 0x113),
    (0x7170, 0x1000), (0x8170, 0x363), (0x9980, 0x139), (0x9ac0, 0x2c9), (0x9d90, 0x25b),
    (0x9ff0, 0x217), (0xa210, 0x471), (0xa690, 0x41f)]

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
    (hcore : Refine.Atom.All code (lifted.locationOf .l102520 initial).arguments initial.external
      (core.atoms lab c fr p))
    (hstart : core.start lab = .l102520 := by rfl)
    (hentry : ∀ fr, atoms .l102520 fr = frameInfo.entryAtoms fr := by intro _; rfl)
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

end Fn102520

end AesGcm.Proofs.Machine.LIR
