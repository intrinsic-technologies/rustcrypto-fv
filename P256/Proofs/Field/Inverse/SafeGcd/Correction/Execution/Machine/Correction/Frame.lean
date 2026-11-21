import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.Machine.Program
import P256.Proofs.Field.Inverse.SafeGcd.Frame

namespace P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

namespace Correction

def frameInfo : Refine.FrameInfo where
  entry := 0x1126c0
  frameBytes := 0x38
  stackBytes := some 0x38
  slots := [(3, 0x28), (12, 0x20), (13, 0x18), (14, 0x10), (15, 0x8)]
  preserved := [3, 5, 12, 13, 14, 15]
  fpPreserved := [39, 51]
  clobbers := [0, 1, 2, 6, 8, 9, 10, 11]
  callSlots := []

@[refine_layout] def frameAtG0 : Label.G0 → Refine.Activation → List Refine.Atom
  | .l1181a0 => fun fr =>
      [.gpr 4 fr.rsp, .reg 22 ⟨1, 0⟩, .gpr 1 fr.rcx, .gpr 2 fr.rdx, .gpr 3 fr.rbx, .gpr 5 fr.rbp,
       .gpr 6 fr.rsi, .gpr 7 fr.rdi, .gpr 8 fr.r8, .gpr 9 fr.r9, .gpr 12 fr.r12, .gpr 13 fr.r13,
       .gpr 14 fr.r14, .gpr 15 fr.r15, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x38) 0x38,
       .fact (fr.low.toNat + 0x38 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l1181ad => fun fr =>
      [.gpr 4 (fr.rsp - 0x38), .reg 22 ⟨1, 0⟩, .gpr 1 fr.rcx, .gpr 2 fr.rdx, .gpr 3 fr.rbx,
       .gpr 5 fr.rbp, .gpr 6 fr.rsi, .gpr 7 fr.rdi, .gpr 8 fr.r8, .gpr 9 fr.r9, .gpr 12 fr.r12,
       .gpr 13 fr.r13, .gpr 14 fr.r14, .gpr 15 fr.r15, .mem (fr.rsp - 0x28) 64 fr.rbx,
       .mem (fr.rsp - 0x20) 64 fr.r12, .mem (fr.rsp - 0x18) 64 fr.r13,
       .mem (fr.rsp - 0x10) 64 fr.r14, .mem (fr.rsp - 0x8) 64 fr.r15, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x38) 0x38,
       .fact (fr.low.toNat + 0x38 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l1181e3 => fun fr =>
      [.gpr 4 (fr.rsp - 0x38), .reg 22 ⟨1, 0⟩, .gpr 1 fr.rcx, .gpr 5 fr.rbp, .gpr 6 fr.rsi,
       .gpr 7 fr.rdi, .gpr 12 fr.r12, .gpr 13 fr.r13, .gpr 15 fr.r15,
       .mem (fr.rsp - 0x28) 64 fr.rbx, .mem (fr.rsp - 0x20) 64 fr.r12,
       .mem (fr.rsp - 0x18) 64 fr.r13, .mem (fr.rsp - 0x10) 64 fr.r14,
       .mem (fr.rsp - 0x8) 64 fr.r15, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x38) 0x38,
       .fact (fr.low.toNat + 0x38 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l11821e => fun fr =>
      [.gpr 4 (fr.rsp - 0x38), .reg 22 ⟨1, 0⟩, .gpr 1 fr.rcx, .gpr 5 fr.rbp, .gpr 7 fr.rdi,
       .gpr 13 fr.r13, .mem (fr.rsp - 0x28) 64 fr.rbx, .mem (fr.rsp - 0x20) 64 fr.r12,
       .mem (fr.rsp - 0x18) 64 fr.r13, .mem (fr.rsp - 0x10) 64 fr.r14,
       .mem (fr.rsp - 0x8) 64 fr.r15, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x38) 0x38,
       .fact (fr.low.toNat + 0x38 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l118251 => fun fr =>
      [.gpr 4 (fr.rsp - 0x38), .reg 22 ⟨1, 0⟩, .gpr 1 fr.rcx, .gpr 5 fr.rbp, .gpr 7 fr.rdi,
       .mem (fr.rsp - 0x28) 64 fr.rbx, .mem (fr.rsp - 0x20) 64 fr.r12,
       .mem (fr.rsp - 0x18) 64 fr.r13, .mem (fr.rsp - 0x10) 64 fr.r14,
       .mem (fr.rsp - 0x8) 64 fr.r15, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x38) 0x38,
       .fact (fr.low.toNat + 0x38 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l118288 => fun fr =>
      [.gpr 4 (fr.rsp - 0x38), .reg 22 ⟨1, 0⟩, .gpr 5 fr.rbp, .gpr 7 fr.rdi,
       .mem (fr.rsp - 0x28) 64 fr.rbx, .mem (fr.rsp - 0x20) 64 fr.r12,
       .mem (fr.rsp - 0x18) 64 fr.r13, .mem (fr.rsp - 0x10) 64 fr.r14,
       .mem (fr.rsp - 0x8) 64 fr.r15, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x38) 0x38,
       .fact (fr.low.toNat + 0x38 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l1182a7 => fun fr =>
      [.gpr 4 (fr.rsp - 0x38), .reg 22 ⟨1, 0⟩, .gpr 5 fr.rbp, .gpr 7 fr.rdi,
       .mem (fr.rsp - 0x28) 64 fr.rbx, .mem (fr.rsp - 0x20) 64 fr.r12,
       .mem (fr.rsp - 0x18) 64 fr.r13, .mem (fr.rsp - 0x10) 64 fr.r14,
       .mem (fr.rsp - 0x8) 64 fr.r15, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x38) 0x38,
       .fact (fr.low.toNat + 0x38 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l1182f8 => fun fr =>
      [.gpr 4 (fr.rsp - 0x38), .reg 22 ⟨1, 0⟩, .gpr 5 fr.rbp, .gpr 7 fr.rdi,
       .mem (fr.rsp - 0x28) 64 fr.rbx, .mem (fr.rsp - 0x20) 64 fr.r12,
       .mem (fr.rsp - 0x18) 64 fr.r13, .mem (fr.rsp - 0x10) 64 fr.r14,
       .mem (fr.rsp - 0x8) 64 fr.r15, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x38) 0x38,
       .fact (fr.low.toNat + 0x38 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]

@[refine_layout] def frameAt : Label → Refine.Activation → List Refine.Atom
  | .g0 l => frameAtG0 l

@[refine_layout] def doneAt (fr : Refine.Activation) : List Refine.Atom :=
  [.gpr 4 (fr.rsp + 8), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rbx, .gpr 5 fr.rbp, .gpr 12 fr.r12,
   .gpr 13 fr.r13, .gpr 14 fr.r14, .gpr 15 fr.r15]

abbrev Post (fr : Refine.Activation) (footprint : List Prelude.MemoryRegion)
    (t : RamState) : Prop :=
  FrameCompat.Post frameInfo fr footprint t


end Correction

end P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.Machine
