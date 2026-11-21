import P256.Proofs.Field.Inverse.SafeGcd.Core.Prepare
import P256.Proofs.Field.Inverse.SafeGcd.Core.LinearShift
import P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.Update

open Shared (batchCount batchResult fInput linearInput)

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

@[refine_layout] def memoryAtoms (fr : Activation) (p : Inputs) (s : LoopState) : List Atom :=
  [.mem (fr.rsp - 8) 64 fr.rbp, .mem (fr.rsp - 16) 64 fr.r15,
   .mem (fr.rsp - 24) 64 fr.r14, .mem (fr.rsp - 32) 64 fr.r13,
   .mem (fr.rsp - 40) 64 fr.r12, .mem (fr.rsp - 48) 64 fr.rbx,
   .mem fr.rsp 64 fr.ret, .readable fr.rsp 8, .fact (fr.ret.toNat < 2^32),
   .writable (fr.rsp - 0x2c0) 0x2c0, .fact (fr.low.toNat + 0x2c0 ≤ fr.rsp.toNat),
   .fact (fr.rsp.toNat % 16 = 8),
   .mem (fr.rsp - 0x108) 64 fr.rdx, .mem (fr.rsp - 0x68) 64 fr.rdi,
   .mem (fr.rsp - 0x60) 64 fr.rcx] ++ commonAtoms fr p ++ savedInputAtoms fr p ++
   stateAtoms fr s ++ [.mem (fr.rsp - 0x38) 64 (BitVec.ofNat 64 s.remaining),
     .mem (fr.rsp - 0x184) 32 (BitVec.ofNat 32 (batchCount s))]

@[refine_layout] def preservedAtoms (fr : Activation) (controls : RamState) (s : LoopState) (sp : BitVec 64) : List Atom :=
  [.gpr 4 sp, .reg 22 ⟨1, 0⟩,
   .gpr 3 (batchResult s).v, .gpr 5 (batchResult s).delta,
   .gpr 12 (batchResult s).r, .gpr 13 (fr.rsp - 0x180),
   .gpr 14 (batchResult s).q, .gpr 15 (batchResult s).u,
   .reg 39 ⟨32, controls.MXCSR⟩, .reg 51 ⟨16, controls.FP87_Control⟩]


@[refine_layout] def bounds (s : LoopState) : List Atom :=
  [.fact (1 ≤ s.remaining), .fact (s.remaining ≤ 591)]

@[refine_layout] def firstCall (fr : Activation) (controls : RamState) (p : Inputs) (s : LoopState) : List Atom :=
  memoryAtoms fr p s ++ bounds s ++ preservedAtoms fr controls s (fr.rsp - 0x190) ++
  [.gpr 7 (fr.rsp - 0x180), .gpr 6 (fr.rsp - 0x130), .gpr 2 (fr.rsp - 0x100),
   .gpr 1 (batchResult s).u, .gpr 8 (batchResult s).v,
   .gpr 9 ((BitVec.ofNat 32 (batchCount s)).setWidth 64),
   .mem (fr.rsp - 0x190) 64 0x111d1c, .readable (fr.rsp - 0x190) 8]

@[refine_layout] def firstResult (fr : Activation) (s : LoopState) : List Atom :=
  [.words (fr.rsp - 0x180) 64 (LinearShift.shiftedWords (fInput s)),
   .mem (fr.rsp - 0x160) 8 (LinearShift.resultSign (fInput s)),
   .readable (fr.rsp - 0x180) 33]

@[refine_layout] def firstReturned (fr : Activation) (controls : RamState) (p : Inputs) (s : LoopState) : List Atom :=
  memoryAtoms fr p s ++ bounds s ++ preservedAtoms fr controls s (fr.rsp - 0x188) ++ firstResult fr s

end P256.Proofs.Field.Inverse.SafeGcd.Core.Update
