import P256.Proofs.Field.Inverse.SafeGcd.Core.Update.CopyFG

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.Update

open Shared (batchCount batchResult fInput gInput dInput eInput linearInput nextState)
open Support (MemoryStable atoms_of_frame)

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

def dCallInput (fr : Activation) (p : Inputs) (s : LoopState) : ModularShift.Inputs :=
  { dInput p s with modulusPtr := fr.rdx }

def eCallInput (fr : Activation) (p : Inputs) (s : LoopState) : ModularShift.Inputs :=
  { eInput p s with modulusPtr := fr.rdx }

@[refine_layout] def modularPreserved (last : Bool) (fr : Activation) (controls : RamState) (s : LoopState) (sp : BitVec 64) : List Atom :=
  [.gpr 4 sp, .reg 22 ⟨1, 0⟩,
   .gpr 3 fr.rdx, .gpr 5 (batchResult s).delta,
   .gpr 12 (batchResult s).r, .gpr 13 (fr.rsp - 0x180),
   .gpr 14 (if last then (BitVec.ofNat 32 (batchCount s)).setWidth 64 else (batchResult s).q),
   .gpr 15 fr.rcx,
   .reg 39 ⟨32, controls.MXCSR⟩, .reg 51 ⟨16, controls.FP87_Control⟩]


@[refine_layout] def thirdCall (fr : Activation) (controls : RamState) (p : Inputs) (s : LoopState) : List Atom :=
  memoryAtoms fr p (CopyFG.fgState s) ++ bounds s ++ modularPreserved false fr controls s (fr.rsp - 0x1a0) ++
  [.gpr 7 (fr.rsp - 0x180), .gpr 6 (fr.rsp - 0xd8), .gpr 2 (fr.rsp - 0xb0),
   .gpr 1 (batchResult s).u, .gpr 8 (batchResult s).v,
   .gpr 9 ((BitVec.ofNat 32 (batchCount s)).setWidth 64),
   .mem (fr.rsp - 0x1a0) 64 0x111e2e, .readable (fr.rsp - 0x1a0) 24,
   .mem (fr.rsp - 0x198) 64 fr.rdx, .mem (fr.rsp - 0x190) 64 fr.rcx]

@[refine_layout] def thirdResult (fr : Activation) (p : Inputs) (s : LoopState) : List Atom :=
  [.words (fr.rsp - 0x180) 64 (ModularShift.resultWords (dInput p s)),
   .mem (fr.rsp - 0x160) 8 (ModularShift.resultSign (dInput p s)),
   .readable (fr.rsp - 0x180) 33]

@[refine_layout] def thirdReturned (fr : Activation) (controls : RamState) (p : Inputs) (s : LoopState) : List Atom :=
  memoryAtoms fr p (CopyFG.fgState s) ++ bounds s ++
  modularPreserved false fr controls s (fr.rsp - 0x198) ++ thirdResult fr p s

@[refine_layout] def fourthCall (fr : Activation) (controls : RamState) (p : Inputs) (s : LoopState) : List Atom :=
  memoryAtoms fr p (CopyFG.fgState s) ++ bounds s ++ modularPreserved true fr controls s (fr.rsp - 0x1a0) ++
  thirdResult fr p s ++
  [.gpr 7 (fr.rsp - 0x158), .gpr 6 (fr.rsp - 0xd8), .gpr 2 (fr.rsp - 0xb0),
   .gpr 1 (batchResult s).q, .gpr 8 (batchResult s).r,
   .gpr 9 ((BitVec.ofNat 32 (batchCount s)).setWidth 64),
   .mem (fr.rsp - 0x1a0) 64 0x111e7a, .readable (fr.rsp - 0x1a0) 24,
   .mem (fr.rsp - 0x198) 64 fr.rdx, .mem (fr.rsp - 0x190) 64 fr.rcx]

@[refine_layout] def fourthResult (fr : Activation) (p : Inputs) (s : LoopState) : List Atom :=
  [.words (fr.rsp - 0x158) 64 (ModularShift.resultWords (eInput p s)),
   .mem (fr.rsp - 0x138) 8 (ModularShift.resultSign (eInput p s)),
   .readable (fr.rsp - 0x158) 33]

@[refine_layout] def fourthReturned (fr : Activation) (controls : RamState) (p : Inputs) (s : LoopState) : List Atom :=
  memoryAtoms fr p (CopyFG.fgState s) ++ bounds s ++ modularPreserved true fr controls s (fr.rsp - 0x198) ++
  thirdResult fr p s ++ fourthResult fr p s

end P256.Proofs.Field.Inverse.SafeGcd.Core.Update
