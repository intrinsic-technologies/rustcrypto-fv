import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.Machine.Program
import P256.Proofs.Field.Inverse.SafeGcd.Frame

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

namespace Core

def frameInfo : Refine.FrameInfo where
  entry := 0x111b70
  frameBytes := 0x188
  stackBytes := some 0x2c0
  slots := [(3, 0x30), (5, 0x8), (12, 0x28), (13, 0x20), (14, 0x18), (15, 0x10)]
  preserved := [3, 5, 12, 13, 14, 15]
  fpPreserved := [39, 51]
  clobbers := []
  callSlots := []

@[refine_layout] def frameAtG0 : Label.G0 → Refine.Activation → List Refine.Atom
  | .l117650 => fun fr =>
      [.gpr 4 fr.rsp, .reg 22 ⟨1, 0⟩, .gpr 1 fr.rcx, .gpr 2 fr.rdx, .gpr 3 fr.rbx, .gpr 5 fr.rbp,
       .gpr 6 fr.rsi, .gpr 7 fr.rdi, .gpr 8 fr.r8, .gpr 9 fr.r9, .gpr 12 fr.r12, .gpr 13 fr.r13,
       .gpr 14 fr.r14, .gpr 15 fr.r15, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x2c0) 0x2c0,
       .fact (fr.low.toNat + 0x2c0 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l117671 => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .gpr 1 fr.rcx, .gpr 2 fr.rdx, .gpr 3 fr.rbx,
       .gpr 5 fr.rbp, .gpr 6 fr.rsi, .gpr 7 fr.rdi, .gpr 8 fr.r8, .gpr 9 fr.r9, .gpr 12 fr.r12,
       .gpr 13 fr.r13, .gpr 14 fr.r14, .gpr 15 fr.r15, .mem (fr.rsp - 0x68) 64 fr.rdi,
       .mem (fr.rsp - 0x60) 64 fr.rcx, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x2c0) 0x2c0,
       .fact (fr.low.toNat + 0x2c0 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l1176da => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .gpr 2 fr.rdx, .gpr 3 fr.rbx, .gpr 5 fr.rbp,
       .gpr 6 fr.rsi, .gpr 7 fr.rdi, .gpr 8 fr.r8, .gpr 12 fr.r12, .gpr 13 fr.r13, .gpr 14 fr.r14,
       .gpr 15 fr.r15, .mem (fr.rsp - 0x108) 64 fr.rdx, .mem (fr.rsp - 0x68) 64 fr.rdi,
       .mem (fr.rsp - 0x60) 64 fr.rcx, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x2c0) 0x2c0,
       .fact (fr.low.toNat + 0x2c0 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l11774d => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .gpr 2 fr.rdx, .gpr 3 fr.rbx, .gpr 5 fr.rbp,
       .gpr 6 fr.rsi, .gpr 7 fr.rdi, .gpr 8 fr.r8, .gpr 12 fr.r12, .gpr 13 fr.r13, .gpr 14 fr.r14,
       .gpr 15 fr.r15, .mem (fr.rsp - 0x108) 64 fr.rdx, .mem (fr.rsp - 0x68) 64 fr.rdi,
       .mem (fr.rsp - 0x60) 64 fr.rcx, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x2c0) 0x2c0,
       .fact (fr.low.toNat + 0x2c0 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l117784 => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .gpr 2 fr.rdx, .gpr 3 fr.rbx, .gpr 5 fr.rbp,
       .gpr 6 fr.rsi, .gpr 7 fr.rdi, .gpr 8 fr.r8, .gpr 12 fr.r12, .gpr 13 fr.r13, .gpr 14 fr.r14,
       .gpr 15 fr.r15, .mem (fr.rsp - 0x108) 64 fr.rdx, .mem (fr.rsp - 0x68) 64 fr.rdi,
       .mem (fr.rsp - 0x60) 64 fr.rcx, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x2c0) 0x2c0,
       .fact (fr.low.toNat + 0x2c0 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l1177a0 => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rbx, .gpr 7 fr.rdi, .gpr 12 fr.r12,
       .gpr 14 fr.r14, .gpr 15 fr.r15, .mem (fr.rsp - 0x108) 64 fr.rdx,
       .mem (fr.rsp - 0x68) 64 fr.rdi, .mem (fr.rsp - 0x60) 64 fr.rcx,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x2c0) 0x2c0, .fact (fr.low.toNat + 0x2c0 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8)]
  | .l1177b1 => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .mem (fr.rsp - 0x108) 64 fr.rdx,
       .mem (fr.rsp - 0x68) 64 fr.rdi, .mem (fr.rsp - 0x60) 64 fr.rcx,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x2c0) 0x2c0, .fact (fr.low.toNat + 0x2c0 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8)]
  | .l1179fa => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rbx, .gpr 6 fr.rsi, .gpr 7 fr.rdi,
       .gpr 8 fr.r8, .gpr 12 fr.r12, .gpr 14 fr.r14, .gpr 15 fr.r15,
       .mem (fr.rsp - 0x108) 64 fr.rdx, .mem (fr.rsp - 0x68) 64 fr.rdi,
       .mem (fr.rsp - 0x60) 64 fr.rcx, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x2c0) 0x2c0,
       .fact (fr.low.toNat + 0x2c0 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l117a59 => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rbx, .gpr 7 fr.rdi, .gpr 12 fr.r12,
       .gpr 14 fr.r14, .gpr 15 fr.r15, .mem (fr.rsp - 0x108) 64 fr.rdx,
       .mem (fr.rsp - 0x68) 64 fr.rdi, .mem (fr.rsp - 0x60) 64 fr.rcx,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x2c0) 0x2c0, .fact (fr.low.toNat + 0x2c0 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8)]
  | .l117aa0 => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .mem (fr.rsp - 0x108) 64 fr.rdx,
       .mem (fr.rsp - 0x68) 64 fr.rdi, .mem (fr.rsp - 0x60) 64 fr.rcx,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x2c0) 0x2c0, .fact (fr.low.toNat + 0x2c0 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8)]
  | .l117b01 => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .mem (fr.rsp - 0x108) 64 fr.rdx,
       .mem (fr.rsp - 0x68) 64 fr.rdi, .mem (fr.rsp - 0x60) 64 fr.rcx,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x2c0) 0x2c0, .fact (fr.low.toNat + 0x2c0 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8)]
  | .l117b46 => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .mem (fr.rsp - 0x108) 64 fr.rdx,
       .mem (fr.rsp - 0x68) 64 fr.rdi, .mem (fr.rsp - 0x60) 64 fr.rcx,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x2c0) 0x2c0, .fact (fr.low.toNat + 0x2c0 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8)]
  | .l117b83 => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .mem (fr.rsp - 0x108) 64 fr.rdx,
       .mem (fr.rsp - 0x68) 64 fr.rdi, .mem (fr.rsp - 0x60) 64 fr.rcx,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x2c0) 0x2c0, .fact (fr.low.toNat + 0x2c0 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8)]
  | .l117bc2 => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .mem (fr.rsp - 0x108) 64 fr.rdx,
       .mem (fr.rsp - 0x68) 64 fr.rdi, .mem (fr.rsp - 0x60) 64 fr.rcx,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x2c0) 0x2c0, .fact (fr.low.toNat + 0x2c0 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8)]
  | .l117bdb => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .mem (fr.rsp - 0x108) 64 fr.rdx,
       .mem (fr.rsp - 0x68) 64 fr.rdi, .mem (fr.rsp - 0x60) 64 fr.rcx,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x2c0) 0x2c0, .fact (fr.low.toNat + 0x2c0 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8)]
  | .l117be3 => fun fr =>
      [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩, .mem (fr.rsp - 0x108) 64 fr.rdx,
       .mem (fr.rsp - 0x68) 64 fr.rdi, .mem (fr.rsp - 0x60) 64 fr.rcx,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x2c0) 0x2c0, .fact (fr.low.toNat + 0x2c0 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8)]
  | _ => fun _ => []

@[refine_layout] def frameAt : Label → Refine.Activation → List Refine.Atom
  | .g0 l => frameAtG0 l

@[refine_layout] def doneAt (fr : Refine.Activation) : List Refine.Atom :=
  [.gpr 4 (fr.rsp + 8), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rbx, .gpr 5 fr.rbp, .gpr 12 fr.r12,
   .gpr 13 fr.r13, .gpr 14 fr.r14, .gpr 15 fr.r15]

abbrev Post := FrameCompat.Post frameInfo

end Core

end P256.Proofs.Field.Inverse.SafeGcd.Core.Machine
