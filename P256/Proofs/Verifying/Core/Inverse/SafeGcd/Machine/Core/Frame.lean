import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Verifying.Core.Inverse.SafeGcd.Machine.Program
import P256.Proofs.Field.Inverse.SafeGcd.Frame

namespace P256.Proofs.Verifying.Core.Inverse.SafeGcd.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

namespace Core

def frameInfo : Refine.FrameInfo where
  entry := 0x112190
  frameBytes := 0x188
  stackBytes := some 0x2c0
  slots := [(3, 0x30), (5, 0x8), (12, 0x28), (13, 0x20), (14, 0x18), (15, 0x10)]
  preserved := [3, 5, 12, 13, 14, 15]
  fpPreserved := [39, 51]
  clobbers := []
  callSlots := []

@[refine_layout] def frameAtG0 : Label.G0 → Refine.Activation → List Refine.Atom
  | .l1141e0 => fun fr =>
      [.gpr 4 fr.rsp, .reg 22 ⟨1, 0⟩, .gpr 1 fr.rcx, .gpr 2 fr.rdx, .gpr 3 fr.rbx, .gpr 5 fr.rbp,
       .gpr 6 fr.rsi, .gpr 7 fr.rdi, .gpr 8 fr.r8, .gpr 9 fr.r9, .gpr 12 fr.r12, .gpr 13 fr.r13,
       .gpr 14 fr.r14, .gpr 15 fr.r15, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x2c0) 0x2c0,
       .fact (fr.low.toNat + 0x2c0 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l114201 => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .gpr 1 fr.rcx, .gpr 2 fr.rdx, .gpr 3 fr.rbx,
       .gpr 5 fr.rbp, .gpr 6 fr.rsi, .gpr 7 fr.rdi, .gpr 8 fr.r8, .gpr 9 fr.r9, .gpr 12 fr.r12,
       .gpr 13 fr.r13, .gpr 14 fr.r14, .gpr 15 fr.r15, .mem (fr.rsp - 0x68) 64 fr.rdi,
       .mem (fr.rsp - 0x60) 64 fr.rcx, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x2c0) 0x2c0,
       .fact (fr.low.toNat + 0x2c0 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l114285 => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .gpr 2 fr.rdx, .gpr 3 fr.rbx, .gpr 5 fr.rbp,
       .gpr 6 fr.rsi, .gpr 7 fr.rdi, .gpr 8 fr.r8, .gpr 9 fr.r9, .gpr 12 fr.r12, .gpr 13 fr.r13,
       .gpr 14 fr.r14, .gpr 15 fr.r15, .mem (fr.rsp - 0x130) 64 fr.rdx,
       .mem (fr.rsp - 0x68) 64 fr.rdi, .mem (fr.rsp - 0x60) 64 fr.rcx,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x2c0) 0x2c0, .fact (fr.low.toNat + 0x2c0 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8)]
  | .l1142ec => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .gpr 2 fr.rdx, .gpr 3 fr.rbx, .gpr 5 fr.rbp,
       .gpr 6 fr.rsi, .gpr 7 fr.rdi, .gpr 8 fr.r8, .gpr 9 fr.r9, .gpr 12 fr.r12, .gpr 13 fr.r13,
       .gpr 14 fr.r14, .gpr 15 fr.r15, .mem (fr.rsp - 0x130) 64 fr.rdx,
       .mem (fr.rsp - 0x68) 64 fr.rdi, .mem (fr.rsp - 0x60) 64 fr.rcx,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x2c0) 0x2c0, .fact (fr.low.toNat + 0x2c0 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8)]
  | .l114300 => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rbx, .gpr 5 fr.rbp, .gpr 8 fr.r8,
       .gpr 13 fr.r13, .gpr 14 fr.r14, .gpr 15 fr.r15, .mem (fr.rsp - 0x130) 64 fr.rdx,
       .mem (fr.rsp - 0x68) 64 fr.rdi, .mem (fr.rsp - 0x60) 64 fr.rcx,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x2c0) 0x2c0, .fact (fr.low.toNat + 0x2c0 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8)]
  | .l114311 => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .gpr 5 fr.rbp, .mem (fr.rsp - 0x130) 64 fr.rdx,
       .mem (fr.rsp - 0x68) 64 fr.rdi, .mem (fr.rsp - 0x60) 64 fr.rcx,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x2c0) 0x2c0, .fact (fr.low.toNat + 0x2c0 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8)]
  | .l11454e => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .gpr 2 fr.rdx, .gpr 3 fr.rbx, .gpr 5 fr.rbp,
       .gpr 7 fr.rdi, .gpr 8 fr.r8, .gpr 9 fr.r9, .gpr 13 fr.r13, .gpr 14 fr.r14, .gpr 15 fr.r15,
       .mem (fr.rsp - 0x130) 64 fr.rdx, .mem (fr.rsp - 0x68) 64 fr.rdi,
       .mem (fr.rsp - 0x60) 64 fr.rcx, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x2c0) 0x2c0,
       .fact (fr.low.toNat + 0x2c0 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l114558 => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rbx, .gpr 5 fr.rbp, .gpr 7 fr.rdi,
       .gpr 8 fr.r8, .gpr 9 fr.r9, .gpr 13 fr.r13, .gpr 14 fr.r14, .gpr 15 fr.r15,
       .mem (fr.rsp - 0x130) 64 fr.rdx, .mem (fr.rsp - 0x68) 64 fr.rdi,
       .mem (fr.rsp - 0x60) 64 fr.rcx, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x2c0) 0x2c0,
       .fact (fr.low.toNat + 0x2c0 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l114560 => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rbx, .gpr 5 fr.rbp, .gpr 7 fr.rdi,
       .gpr 8 fr.r8, .gpr 9 fr.r9, .gpr 13 fr.r13, .gpr 14 fr.r14, .gpr 15 fr.r15,
       .mem (fr.rsp - 0x130) 64 fr.rdx, .mem (fr.rsp - 0x68) 64 fr.rdi,
       .mem (fr.rsp - 0x60) 64 fr.rcx, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x2c0) 0x2c0,
       .fact (fr.low.toNat + 0x2c0 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l114568 => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rbx, .gpr 5 fr.rbp, .gpr 7 fr.rdi,
       .gpr 8 fr.r8, .gpr 9 fr.r9, .gpr 13 fr.r13, .gpr 14 fr.r14, .gpr 15 fr.r15,
       .mem (fr.rsp - 0x130) 64 fr.rdx, .mem (fr.rsp - 0x68) 64 fr.rdi,
       .mem (fr.rsp - 0x60) 64 fr.rcx, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x2c0) 0x2c0,
       .fact (fr.low.toNat + 0x2c0 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l114574 => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rbx, .gpr 5 fr.rbp, .gpr 7 fr.rdi,
       .gpr 8 fr.r8, .gpr 9 fr.r9, .gpr 13 fr.r13, .gpr 14 fr.r14, .gpr 15 fr.r15,
       .mem (fr.rsp - 0x130) 64 fr.rdx, .mem (fr.rsp - 0x68) 64 fr.rdi,
       .mem (fr.rsp - 0x60) 64 fr.rcx, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x2c0) 0x2c0,
       .fact (fr.low.toNat + 0x2c0 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l1145af => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rbx, .gpr 5 fr.rbp, .gpr 8 fr.r8,
       .gpr 13 fr.r13, .gpr 14 fr.r14, .gpr 15 fr.r15, .mem (fr.rsp - 0x130) 64 fr.rdx,
       .mem (fr.rsp - 0x68) 64 fr.rdi, .mem (fr.rsp - 0x60) 64 fr.rcx,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x2c0) 0x2c0, .fact (fr.low.toNat + 0x2c0 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8)]
  | .l1145da => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rbx, .gpr 5 fr.rbp, .gpr 8 fr.r8,
       .gpr 13 fr.r13, .gpr 14 fr.r14, .gpr 15 fr.r15, .mem (fr.rsp - 0x130) 64 fr.rdx,
       .mem (fr.rsp - 0x68) 64 fr.rdi, .mem (fr.rsp - 0x60) 64 fr.rcx,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x2c0) 0x2c0, .fact (fr.low.toNat + 0x2c0 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8)]
  | .l1145e2 => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rbx, .gpr 5 fr.rbp, .gpr 8 fr.r8,
       .gpr 13 fr.r13, .gpr 14 fr.r14, .gpr 15 fr.r15, .mem (fr.rsp - 0x130) 64 fr.rdx,
       .mem (fr.rsp - 0x68) 64 fr.rdi, .mem (fr.rsp - 0x60) 64 fr.rcx,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x2c0) 0x2c0, .fact (fr.low.toNat + 0x2c0 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8)]
  | .l114616 => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rbx, .gpr 5 fr.rbp, .gpr 13 fr.r13,
       .gpr 14 fr.r14, .gpr 15 fr.r15, .mem (fr.rsp - 0x130) 64 fr.rdx,
       .mem (fr.rsp - 0x68) 64 fr.rdi, .mem (fr.rsp - 0x60) 64 fr.rcx,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x2c0) 0x2c0, .fact (fr.low.toNat + 0x2c0 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8)]
  | .l114630 => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .gpr 5 fr.rbp, .mem (fr.rsp - 0x130) 64 fr.rdx,
       .mem (fr.rsp - 0x68) 64 fr.rdi, .mem (fr.rsp - 0x60) 64 fr.rcx,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x2c0) 0x2c0, .fact (fr.low.toNat + 0x2c0 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8)]
  | .l114635 => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .gpr 5 fr.rbp, .mem (fr.rsp - 0x130) 64 fr.rdx,
       .mem (fr.rsp - 0x68) 64 fr.rdi, .mem (fr.rsp - 0x60) 64 fr.rcx,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x2c0) 0x2c0, .fact (fr.low.toNat + 0x2c0 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8)]
  | .l11465b => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .gpr 5 fr.rbp, .mem (fr.rsp - 0x130) 64 fr.rdx,
       .mem (fr.rsp - 0x68) 64 fr.rdi, .mem (fr.rsp - 0x60) 64 fr.rcx,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x2c0) 0x2c0, .fact (fr.low.toNat + 0x2c0 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8)]
  | .l114675 => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .gpr 5 fr.rbp, .mem (fr.rsp - 0x130) 64 fr.rdx,
       .mem (fr.rsp - 0x68) 64 fr.rdi, .mem (fr.rsp - 0x60) 64 fr.rcx,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x2c0) 0x2c0, .fact (fr.low.toNat + 0x2c0 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8)]
  | .l11467a => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .gpr 5 fr.rbp, .mem (fr.rsp - 0x130) 64 fr.rdx,
       .mem (fr.rsp - 0x68) 64 fr.rdi, .mem (fr.rsp - 0x60) 64 fr.rcx,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x2c0) 0x2c0, .fact (fr.low.toNat + 0x2c0 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8)]
  | .l114680 => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .gpr 5 fr.rbp, .mem (fr.rsp - 0x130) 64 fr.rdx,
       .mem (fr.rsp - 0x68) 64 fr.rdi, .mem (fr.rsp - 0x60) 64 fr.rcx,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x2c0) 0x2c0, .fact (fr.low.toNat + 0x2c0 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8)]
  | .l11468d => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .gpr 5 fr.rbp, .mem (fr.rsp - 0x130) 64 fr.rdx,
       .mem (fr.rsp - 0x68) 64 fr.rdi, .mem (fr.rsp - 0x60) 64 fr.rcx,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x2c0) 0x2c0, .fact (fr.low.toNat + 0x2c0 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8)]
  | .l114698 => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rbx, .gpr 5 fr.rbp, .gpr 7 fr.rdi,
       .gpr 8 fr.r8, .gpr 9 fr.r9, .gpr 13 fr.r13, .gpr 14 fr.r14, .gpr 15 fr.r15,
       .mem (fr.rsp - 0x130) 64 fr.rdx, .mem (fr.rsp - 0x68) 64 fr.rdi,
       .mem (fr.rsp - 0x60) 64 fr.rcx, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x2c0) 0x2c0,
       .fact (fr.low.toNat + 0x2c0 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | _ => fun _ => []

@[refine_layout] def frameAt : Label → Refine.Activation → List Refine.Atom
  | .g0 l => frameAtG0 l

@[refine_layout] def doneAt (fr : Refine.Activation) : List Refine.Atom :=
  [.gpr 4 (fr.rsp + 8), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rbx, .gpr 5 fr.rbp, .gpr 12 fr.r12,
   .gpr 13 fr.r13, .gpr 14 fr.r14, .gpr 15 fr.r15]

abbrev Post := P256.Proofs.Field.Inverse.SafeGcd.FrameCompat.Post frameInfo

end Core

end P256.Proofs.Verifying.Core.Inverse.SafeGcd.Machine
