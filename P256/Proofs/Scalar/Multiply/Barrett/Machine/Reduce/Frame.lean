import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Scalar.Multiply.Barrett.Machine.Program
import P256.Proofs.Field.Inverse.SafeGcd.Frame

namespace P256.Proofs.Scalar.Multiply.Barrett.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

namespace Reduce

def frameInfo : Refine.FrameInfo where
  entry := 0x112840
  frameBytes := 0x70
  stackBytes := some 0x70
  slots := [(3, 0x30), (5, 0x8), (12, 0x28), (13, 0x20), (14, 0x18), (15, 0x10)]
  preserved := [3, 5, 12, 13, 14, 15]
  fpPreserved := [39, 51]
  clobbers := [0, 1, 2, 6, 8, 9, 10, 11]
  callSlots := []

def labelFrameG0 : Label.G0 → Option Refine.LabelFrame
  | .l118320 => some ⟨0x0, [(1, 1), (2, 2), (3, 3), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9),
      (12, 12), (13, 13), (14, 14), (15, 15)], [], []⟩
  | .l11832e => some ⟨0x70, [(1, 1), (2, 2), (3, 3), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9),
      (12, 12), (13, 13), (14, 14), (15, 15)], [(0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14),
      (0x10, 15), (0x8, 5)], []⟩
  | .l11839b => some ⟨0x70, [(7, 7), (12, 2)], [(0x48, 6), (0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], []⟩
  | .l118420 => some ⟨0x70, [(7, 7), (8, 2)], [(0x60, 2), (0x48, 6), (0x30, 3), (0x28, 12),
      (0x20, 13), (0x18, 14), (0x10, 15), (0x8, 5)], []⟩
  | .l1184ac => some ⟨0x70, [(7, 7), (8, 2)], [(0x60, 2), (0x48, 6), (0x30, 3), (0x28, 12),
      (0x20, 13), (0x18, 14), (0x10, 15), (0x8, 5)], []⟩
  | .l118544 => some ⟨0x70, [(7, 7)], [(0x60, 2), (0x48, 6), (0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], []⟩
  | .l1185d2 => some ⟨0x70, [(7, 7)], [(0x60, 2), (0x48, 6), (0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], []⟩
  | .l118654 => some ⟨0x70, [(7, 7)], [(0x48, 6), (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14),
      (0x10, 15), (0x8, 5)], []⟩
  | .l1186f3 => some ⟨0x70, [(1, 6), (7, 7)], [(0x48, 6), (0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], []⟩
  | .l118722 => some ⟨0x70, [(7, 7)], [(0x48, 6), (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14),
      (0x10, 15), (0x8, 5)], []⟩
  | .l118752 => some ⟨0x70, [(7, 7)], [(0x48, 6), (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14),
      (0x10, 15), (0x8, 5)], []⟩
  | .l118782 => some ⟨0x70, [(7, 7)], [(0x48, 6), (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14),
      (0x10, 15), (0x8, 5)], []⟩
  | .l1187b8 => some ⟨0x70, [(7, 7)], [(0x48, 6), (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14),
      (0x10, 15), (0x8, 5)], []⟩
  | .l1187ed => some ⟨0x70, [(7, 7)], [(0x48, 6), (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14),
      (0x10, 15), (0x8, 5)], []⟩
  | .l11880b => some ⟨0x70, [(7, 7)], [(0x48, 6), (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14),
      (0x10, 15), (0x8, 5)], []⟩
  | .l118837 => some ⟨0x70, [(7, 7)], [(0x48, 6), (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14),
      (0x10, 15), (0x8, 5)], []⟩
  | .l118856 => some ⟨0x70, [(7, 7)], [(0x48, 6), (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14),
      (0x10, 15), (0x8, 5)], []⟩
  | .l118882 => some ⟨0x70, [(7, 7)], [(0x48, 6), (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14),
      (0x10, 15), (0x8, 5)], []⟩
  | .l1188a1 => some ⟨0x70, [(7, 7)], [(0x48, 6), (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14),
      (0x10, 15), (0x8, 5)], []⟩
  | .l1188c5 => some ⟨0x70, [(7, 7)], [(0x48, 6), (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14),
      (0x10, 15), (0x8, 5)], []⟩
  | .l1188e7 => some ⟨0x70, [(7, 7)], [(0x48, 6), (0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14),
      (0x10, 15), (0x8, 5)], []⟩

@[refine_layout] def frameAtG0 : Label.G0 → Refine.Activation → List Refine.Atom
  | .l118320 => fun fr =>
      [.gpr 4 fr.rsp, .reg 22 ⟨1, 0⟩, .gpr 1 fr.rcx, .gpr 2 fr.rdx, .gpr 3 fr.rbx, .gpr 5 fr.rbp,
       .gpr 6 fr.rsi, .gpr 7 fr.rdi, .gpr 8 fr.r8, .gpr 9 fr.r9, .gpr 12 fr.r12, .gpr 13 fr.r13,
       .gpr 14 fr.r14, .gpr 15 fr.r15, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x70) 0x70,
       .fact (fr.low.toNat + 0x70 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l11832e => fun fr =>
      [.gpr 4 (fr.rsp - 0x70), .reg 22 ⟨1, 0⟩, .gpr 1 fr.rcx, .gpr 2 fr.rdx, .gpr 3 fr.rbx,
       .gpr 5 fr.rbp, .gpr 6 fr.rsi, .gpr 7 fr.rdi, .gpr 8 fr.r8, .gpr 9 fr.r9, .gpr 12 fr.r12,
       .gpr 13 fr.r13, .gpr 14 fr.r14, .gpr 15 fr.r15, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x70) 0x70,
       .fact (fr.low.toNat + 0x70 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l11839b => fun fr =>
      [.gpr 4 (fr.rsp - 0x70), .reg 22 ⟨1, 0⟩, .gpr 7 fr.rdi, .gpr 12 fr.rdx,
       .mem (fr.rsp - 0x48) 64 fr.rsi, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x70) 0x70,
       .fact (fr.low.toNat + 0x70 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l118420 => fun fr =>
      [.gpr 4 (fr.rsp - 0x70), .reg 22 ⟨1, 0⟩, .gpr 7 fr.rdi, .gpr 8 fr.rdx,
       .mem (fr.rsp - 0x60) 64 fr.rdx, .mem (fr.rsp - 0x48) 64 fr.rsi,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x70) 0x70,
       .fact (fr.low.toNat + 0x70 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l1184ac => fun fr =>
      [.gpr 4 (fr.rsp - 0x70), .reg 22 ⟨1, 0⟩, .gpr 7 fr.rdi, .gpr 8 fr.rdx,
       .mem (fr.rsp - 0x60) 64 fr.rdx, .mem (fr.rsp - 0x48) 64 fr.rsi,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x70) 0x70,
       .fact (fr.low.toNat + 0x70 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l118544 => fun fr =>
      [.gpr 4 (fr.rsp - 0x70), .reg 22 ⟨1, 0⟩, .gpr 7 fr.rdi, .mem (fr.rsp - 0x60) 64 fr.rdx,
       .mem (fr.rsp - 0x48) 64 fr.rsi, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x70) 0x70,
       .fact (fr.low.toNat + 0x70 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l1185d2 => fun fr =>
      [.gpr 4 (fr.rsp - 0x70), .reg 22 ⟨1, 0⟩, .gpr 7 fr.rdi, .mem (fr.rsp - 0x60) 64 fr.rdx,
       .mem (fr.rsp - 0x48) 64 fr.rsi, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x70) 0x70,
       .fact (fr.low.toNat + 0x70 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l118654 => fun fr =>
      [.gpr 4 (fr.rsp - 0x70), .reg 22 ⟨1, 0⟩, .gpr 7 fr.rdi, .mem (fr.rsp - 0x48) 64 fr.rsi,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x70) 0x70,
       .fact (fr.low.toNat + 0x70 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l1186f3 => fun fr =>
      [.gpr 4 (fr.rsp - 0x70), .reg 22 ⟨1, 0⟩, .gpr 1 fr.rsi, .gpr 7 fr.rdi,
       .mem (fr.rsp - 0x48) 64 fr.rsi, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x70) 0x70,
       .fact (fr.low.toNat + 0x70 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l118722 => fun fr =>
      [.gpr 4 (fr.rsp - 0x70), .reg 22 ⟨1, 0⟩, .gpr 7 fr.rdi, .mem (fr.rsp - 0x48) 64 fr.rsi,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x70) 0x70,
       .fact (fr.low.toNat + 0x70 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l118752 => fun fr =>
      [.gpr 4 (fr.rsp - 0x70), .reg 22 ⟨1, 0⟩, .gpr 7 fr.rdi, .mem (fr.rsp - 0x48) 64 fr.rsi,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x70) 0x70,
       .fact (fr.low.toNat + 0x70 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l118782 => fun fr =>
      [.gpr 4 (fr.rsp - 0x70), .reg 22 ⟨1, 0⟩, .gpr 7 fr.rdi, .mem (fr.rsp - 0x48) 64 fr.rsi,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x70) 0x70,
       .fact (fr.low.toNat + 0x70 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l1187b8 => fun fr =>
      [.gpr 4 (fr.rsp - 0x70), .reg 22 ⟨1, 0⟩, .gpr 7 fr.rdi, .mem (fr.rsp - 0x48) 64 fr.rsi,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x70) 0x70,
       .fact (fr.low.toNat + 0x70 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l1187ed => fun fr =>
      [.gpr 4 (fr.rsp - 0x70), .reg 22 ⟨1, 0⟩, .gpr 7 fr.rdi, .mem (fr.rsp - 0x48) 64 fr.rsi,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x70) 0x70,
       .fact (fr.low.toNat + 0x70 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l11880b => fun fr =>
      [.gpr 4 (fr.rsp - 0x70), .reg 22 ⟨1, 0⟩, .gpr 7 fr.rdi, .mem (fr.rsp - 0x48) 64 fr.rsi,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x70) 0x70,
       .fact (fr.low.toNat + 0x70 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l118837 => fun fr =>
      [.gpr 4 (fr.rsp - 0x70), .reg 22 ⟨1, 0⟩, .gpr 7 fr.rdi, .mem (fr.rsp - 0x48) 64 fr.rsi,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x70) 0x70,
       .fact (fr.low.toNat + 0x70 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l118856 => fun fr =>
      [.gpr 4 (fr.rsp - 0x70), .reg 22 ⟨1, 0⟩, .gpr 7 fr.rdi, .mem (fr.rsp - 0x48) 64 fr.rsi,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x70) 0x70,
       .fact (fr.low.toNat + 0x70 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l118882 => fun fr =>
      [.gpr 4 (fr.rsp - 0x70), .reg 22 ⟨1, 0⟩, .gpr 7 fr.rdi, .mem (fr.rsp - 0x48) 64 fr.rsi,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x70) 0x70,
       .fact (fr.low.toNat + 0x70 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l1188a1 => fun fr =>
      [.gpr 4 (fr.rsp - 0x70), .reg 22 ⟨1, 0⟩, .gpr 7 fr.rdi, .mem (fr.rsp - 0x48) 64 fr.rsi,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x70) 0x70,
       .fact (fr.low.toNat + 0x70 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l1188c5 => fun fr =>
      [.gpr 4 (fr.rsp - 0x70), .reg 22 ⟨1, 0⟩, .gpr 7 fr.rdi, .mem (fr.rsp - 0x48) 64 fr.rsi,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x70) 0x70,
       .fact (fr.low.toNat + 0x70 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l1188e7 => fun fr =>
      [.gpr 4 (fr.rsp - 0x70), .reg 22 ⟨1, 0⟩, .gpr 7 fr.rdi, .mem (fr.rsp - 0x48) 64 fr.rsi,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x70) 0x70,
       .fact (fr.low.toNat + 0x70 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]

def labelFrame : Label → Option Refine.LabelFrame
  | .g0 l => labelFrameG0 l

@[refine_layout] def frameAt : Label → Refine.Activation → List Refine.Atom
  | .g0 l => frameAtG0 l

@[refine_layout] def doneAt (fr : Refine.Activation) : List Refine.Atom :=
  [.gpr 4 (fr.rsp + 8), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rbx, .gpr 5 fr.rbp, .gpr 12 fr.r12,
   .gpr 13 fr.r13, .gpr 14 fr.r14, .gpr 15 fr.r15]

theorem frameAt_canonical (l : Label) (fr : Refine.Activation) :
    frameAt l fr = frameInfo.atomsAt (labelFrame l) fr := by
  cases l <;> rename_i l <;> first | rfl | (cases l <;> rfl)

theorem doneAt_canonical (fr : Refine.Activation) : doneAt fr = P256.Proofs.Field.Inverse.SafeGcd.FrameCompat.doneAtoms frameInfo fr := rfl

abbrev Pre (code : CodeMap) (fr : Refine.Activation) (s : RamState) : Prop :=
  P256.Proofs.Field.Inverse.SafeGcd.FrameCompat.Pre frameInfo code fr s

abbrev Post (fr : Refine.Activation) (footprint : List Prelude.MemoryRegion)
    (t : RamState) : Prop :=
  P256.Proofs.Field.Inverse.SafeGcd.FrameCompat.Post frameInfo fr footprint t

end Reduce

end P256.Proofs.Scalar.Multiply.Barrett.Machine
