import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine.Program
import P256.Proofs.Field.Inverse.SafeGcd.Frame

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

namespace LinearCombination

def frameInfo : Refine.FrameInfo where
  entry := 0x111220
  frameBytes := 0x70
  stackBytes := some 0x70
  slots := [(3, 0x30), (5, 0x8), (12, 0x28), (13, 0x20), (14, 0x18), (15, 0x10)]
  preserved := [3, 5, 12, 13, 14, 15]
  fpPreserved := [39, 51]
  clobbers := [0, 1, 2, 6, 8, 9, 10, 11]
  callSlots := []

def labelFrameG0 : Label.G0 → Option Refine.LabelFrame
  | .l116d00 => some ⟨0x0, [(1, 1), (2, 2), (3, 3), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9),
      (12, 12), (13, 13), (14, 14), (15, 15)], [], []⟩
  | .l116d0e => some ⟨0x70, [(1, 1), (2, 2), (3, 3), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9),
      (12, 12), (13, 13), (14, 14), (15, 15)], [(0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14),
      (0x10, 15), (0x8, 5)], []⟩
  | .l116d4e => some ⟨0x70, [(1, 1), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 2), (12, 12),
      (13, 13), (14, 14), (15, 15)], [(0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15),
      (0x8, 5)], []⟩
  | .l116d95 => some ⟨0x70, [(6, 6), (7, 7), (8, 8), (11, 2)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], []⟩
  | .l116de3 => some ⟨0x70, [(6, 6), (7, 7), (11, 2)], [(0x30, 3), (0x28, 12), (0x20, 13),
      (0x18, 14), (0x10, 15), (0x8, 5)], []⟩
  | .l116e0f => some ⟨0x70, [(7, 7), (11, 2)], [(0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14),
      (0x10, 15), (0x8, 5)], []⟩
  | .l116e59 => some ⟨0x70, [(7, 7)], [(0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15),
      (0x8, 5)], []⟩
  | .l116e9d => some ⟨0x70, [(7, 7)], [(0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15),
      (0x8, 5)], []⟩
  | .l116eb9 => some ⟨0x70, [(7, 7)], [(0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15),
      (0x8, 5)], []⟩
  | .l116ede => some ⟨0x70, [(7, 7)], [(0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15),
      (0x8, 5)], []⟩
  | .l116f0b => some ⟨0x70, [(7, 7)], [(0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15),
      (0x8, 5)], []⟩
  | .l116f39 => some ⟨0x70, [(7, 7)], [(0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15),
      (0x8, 5)], []⟩
  | .l116f67 => some ⟨0x70, [(7, 7)], [(0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15),
      (0x8, 5)], []⟩
  | .l116fbb => some ⟨0x70, [(7, 7)], [(0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15),
      (0x8, 5)], []⟩
  | .l116fd8 => some ⟨0x70, [(7, 7)], [(0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15),
      (0x8, 5)], []⟩
  | .l11700a => some ⟨0x70, [(7, 7)], [(0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15),
      (0x8, 5)], []⟩
  | .l117033 => some ⟨0x70, [(7, 7)], [(0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15),
      (0x8, 5)], []⟩
  | .l117072 => some ⟨0x70, [(7, 7)], [(0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15),
      (0x8, 5)], []⟩
  | .l117080 => some ⟨0x70, [(7, 7)], [(0x30, 3), (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15),
      (0x8, 5)], []⟩

@[refine_layout] def frameAtG0 : Label.G0 → Refine.Activation → List Refine.Atom
  | .l116d00 => fun fr =>
      [.gpr 4 fr.rsp, .reg 22 ⟨1, 0⟩, .gpr 1 fr.rcx, .gpr 2 fr.rdx, .gpr 3 fr.rbx, .gpr 5 fr.rbp,
       .gpr 6 fr.rsi, .gpr 7 fr.rdi, .gpr 8 fr.r8, .gpr 9 fr.r9, .gpr 12 fr.r12, .gpr 13 fr.r13,
       .gpr 14 fr.r14, .gpr 15 fr.r15, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x70) 0x70,
       .fact (fr.low.toNat + 0x70 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l116d0e => fun fr =>
      [.gpr 4 (fr.rsp - 0x70), .reg 22 ⟨1, 0⟩, .gpr 1 fr.rcx, .gpr 2 fr.rdx, .gpr 3 fr.rbx,
       .gpr 5 fr.rbp, .gpr 6 fr.rsi, .gpr 7 fr.rdi, .gpr 8 fr.r8, .gpr 9 fr.r9, .gpr 12 fr.r12,
       .gpr 13 fr.r13, .gpr 14 fr.r14, .gpr 15 fr.r15, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x70) 0x70,
       .fact (fr.low.toNat + 0x70 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l116d4e => fun fr =>
      [.gpr 4 (fr.rsp - 0x70), .reg 22 ⟨1, 0⟩, .gpr 1 fr.rcx, .gpr 5 fr.rbp, .gpr 6 fr.rsi,
       .gpr 7 fr.rdi, .gpr 8 fr.r8, .gpr 9 fr.r9, .gpr 11 fr.rdx, .gpr 12 fr.r12, .gpr 13 fr.r13,
       .gpr 14 fr.r14, .gpr 15 fr.r15, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x70) 0x70,
       .fact (fr.low.toNat + 0x70 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l116d95 => fun fr =>
      [.gpr 4 (fr.rsp - 0x70), .reg 22 ⟨1, 0⟩, .gpr 6 fr.rsi, .gpr 7 fr.rdi, .gpr 8 fr.r8,
       .gpr 11 fr.rdx, .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x70) 0x70,
       .fact (fr.low.toNat + 0x70 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l116de3 => fun fr =>
      [.gpr 4 (fr.rsp - 0x70), .reg 22 ⟨1, 0⟩, .gpr 6 fr.rsi, .gpr 7 fr.rdi, .gpr 11 fr.rdx,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x70) 0x70,
       .fact (fr.low.toNat + 0x70 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l116e0f => fun fr =>
      [.gpr 4 (fr.rsp - 0x70), .reg 22 ⟨1, 0⟩, .gpr 7 fr.rdi, .gpr 11 fr.rdx,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x70) 0x70,
       .fact (fr.low.toNat + 0x70 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l116e59 => fun fr =>
      [.gpr 4 (fr.rsp - 0x70), .reg 22 ⟨1, 0⟩, .gpr 7 fr.rdi, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x70) 0x70,
       .fact (fr.low.toNat + 0x70 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l116e9d => fun fr =>
      [.gpr 4 (fr.rsp - 0x70), .reg 22 ⟨1, 0⟩, .gpr 7 fr.rdi, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x70) 0x70,
       .fact (fr.low.toNat + 0x70 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l116eb9 => fun fr =>
      [.gpr 4 (fr.rsp - 0x70), .reg 22 ⟨1, 0⟩, .gpr 7 fr.rdi, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x70) 0x70,
       .fact (fr.low.toNat + 0x70 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l116ede => fun fr =>
      [.gpr 4 (fr.rsp - 0x70), .reg 22 ⟨1, 0⟩, .gpr 7 fr.rdi, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x70) 0x70,
       .fact (fr.low.toNat + 0x70 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l116f0b => fun fr =>
      [.gpr 4 (fr.rsp - 0x70), .reg 22 ⟨1, 0⟩, .gpr 7 fr.rdi, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x70) 0x70,
       .fact (fr.low.toNat + 0x70 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l116f39 => fun fr =>
      [.gpr 4 (fr.rsp - 0x70), .reg 22 ⟨1, 0⟩, .gpr 7 fr.rdi, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x70) 0x70,
       .fact (fr.low.toNat + 0x70 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l116f67 => fun fr =>
      [.gpr 4 (fr.rsp - 0x70), .reg 22 ⟨1, 0⟩, .gpr 7 fr.rdi, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x70) 0x70,
       .fact (fr.low.toNat + 0x70 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l116fbb => fun fr =>
      [.gpr 4 (fr.rsp - 0x70), .reg 22 ⟨1, 0⟩, .gpr 7 fr.rdi, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x70) 0x70,
       .fact (fr.low.toNat + 0x70 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l116fd8 => fun fr =>
      [.gpr 4 (fr.rsp - 0x70), .reg 22 ⟨1, 0⟩, .gpr 7 fr.rdi, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x70) 0x70,
       .fact (fr.low.toNat + 0x70 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l11700a => fun fr =>
      [.gpr 4 (fr.rsp - 0x70), .reg 22 ⟨1, 0⟩, .gpr 7 fr.rdi, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x70) 0x70,
       .fact (fr.low.toNat + 0x70 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l117033 => fun fr =>
      [.gpr 4 (fr.rsp - 0x70), .reg 22 ⟨1, 0⟩, .gpr 7 fr.rdi, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x70) 0x70,
       .fact (fr.low.toNat + 0x70 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l117072 => fun fr =>
      [.gpr 4 (fr.rsp - 0x70), .reg 22 ⟨1, 0⟩, .gpr 7 fr.rdi, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x70) 0x70,
       .fact (fr.low.toNat + 0x70 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l117080 => fun fr =>
      [.gpr 4 (fr.rsp - 0x70), .reg 22 ⟨1, 0⟩, .gpr 7 fr.rdi, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x70) 0x70,
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

theorem doneAt_canonical (fr : Refine.Activation) : doneAt fr = FrameCompat.doneAtoms frameInfo fr := rfl

abbrev Pre (code : CodeMap) (fr : Refine.Activation) (s : RamState) : Prop :=
  FrameCompat.Pre frameInfo code fr s

abbrev Post (fr : Refine.Activation) (footprint : List Prelude.MemoryRegion)
    (t : RamState) : Prop :=
  FrameCompat.Post frameInfo fr footprint t

def closureCode : CodeMap := sectionCode textSection [(0x11220, 0x3aa)]

theorem closure_code : ∀ x ∈ closureCode, x ∈ fnCode :=
  sectionCode_sub (.head _) (by decide)

section Contract

variable {UOp : Nat → Type} {ULabel UValue UStore : Type} {usig : ULabel → Nat} {results : Nat}
  {P : Program UOp ULabel usig results} {D : Dialect UOp UValue UStore} {Ctx : Type}

theorem routine [inst : Bindings] {atoms : Label → Refine.Activation → List Refine.Atom}
    {retAtoms : Refine.Activation → List Refine.Atom} (core : Refine.LayoutCore P D lifted Ctx)
    {code : CodeMap} (sim : ∀ {boundary : ReturnBoundary}, ReturnOutside boundary code →
      Simulation (machineAnyReturn boundary) (lifted.program.sem (dialect code)) (Rel code lifted)
        (RetRel code lifted))
    (blocks : ∀ label, (Refine.Layout.withFrame atoms retAtoms core).BlockSimulation code label)
    {initial : RamState} {fr : Refine.Activation} {c : Ctx} {n : Nat}
    {regions : Vector Prelude.MemoryRegion n} (hready : EntryReady code initial)
    (hpre : Pre code fr initial)
    (hregions : ∀ x, (∀ r ∈ regions, ¬ r.Contains x) →
      ∀ r ∈ fr.region :: core.footprint c fr, ¬ r.Contains x)
    {lab : ULabel} {p : core.Params lab} {o : Output UValue UStore results}
    (hexec : P.Exec D ⟨⟨lab, core.args lab p, core.store lab p⟩, []⟩ o)
    (hcore : Refine.Atom.All code (lifted.locationOf .l116d00 initial).arguments initial.external
      (core.atoms lab c fr p))
    (hstart : core.start lab = .l116d00 := by rfl)
    (hentry : ∀ fr, atoms .l116d00 fr = FrameCompat.entryAtoms frameInfo fr := by intro _; rfl)
    (hdone : ∀ fr, retAtoms fr = FrameCompat.doneAtoms frameInfo fr := by intro _; rfl) :
    RoutineResult inst initial regions fun t => Post fr (core.footprint c fr) t ∧
      ∃ r, o = core.output r ∧ ∃ lo, RetRel code lifted lo t ∧
        Refine.Atom.All code lo.values lo.store (core.done c fr r) :=
  FrameCompat.withFrame_routine core hready hpre sim blocks hregions hexec hcore hstart hentry
    hdone rfl (by decide)

theorem call {atoms : Label → Refine.Activation → List Refine.Atom}
    {retAtoms : Refine.Activation → List Refine.Atom} {core : Refine.LayoutCore P D lifted Ctx}
    {code : CodeMap}
    (blocks : ∀ label, (Refine.Layout.withFrame atoms retAtoms core).BlockSimulation code label)
    {u : Location UValue UStore ULabel usig} {o : Output UValue UStore results}
    (hexec : P.Exec D ⟨u, []⟩ o) (fr : Refine.Activation) (c : Ctx) {l : lifted.Location}
    (hrel : (Refine.Layout.withFrame atoms retAtoms core).Rel code (fr, c) u l)
    (hdone : ∀ fr, retAtoms fr = FrameCompat.doneAtoms frameInfo fr := by intro _; rfl) :
    ∃ lo, lifted.program.Exec (dialect code) ⟨l, []⟩ lo ∧
      (Refine.Layout.withFrame atoms retAtoms core).RetRel code (fr, c) o lo ∧
        Refine.Atom.All code lo.values lo.store (FrameCompat.doneAtoms frameInfo fr) :=
  FrameCompat.withFrame_call blocks hexec fr c hrel hdone

end Contract

end LinearCombination

end P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Machine
