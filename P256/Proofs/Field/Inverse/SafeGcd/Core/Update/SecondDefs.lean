import P256.Proofs.Field.Inverse.SafeGcd.Core.Update.Defs

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.Update

open Shared (batchCount batchResult fInput gInput linearInput)
open Support (MemoryStable atoms_of_frame)

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

@[refine_layout] def secondCall (fr : Activation) (controls : RamState) (p : Inputs) (s : LoopState) : List Atom :=
  memoryAtoms fr p s ++ bounds s ++ preservedAtoms fr controls s (fr.rsp - 0x190) ++ firstResult fr s ++
  [.gpr 7 (fr.rsp - 0x158), .gpr 6 (fr.rsp - 0x130), .gpr 2 (fr.rsp - 0x100),
   .gpr 1 (batchResult s).q, .gpr 8 (batchResult s).r,
   .gpr 9 ((BitVec.ofNat 32 (batchCount s)).setWidth 64),
   .mem (fr.rsp - 0x190) 64 0x111d69, .readable (fr.rsp - 0x190) 8]

@[refine_layout] def secondResult (fr : Activation) (s : LoopState) : List Atom :=
  [.words (fr.rsp - 0x158) 64 (LinearShift.shiftedWords (gInput s)),
   .mem (fr.rsp - 0x138) 8 (LinearShift.resultSign (gInput s)),
   .readable (fr.rsp - 0x158) 33]

@[refine_layout] def secondReturned (fr : Activation) (controls : RamState) (p : Inputs) (s : LoopState) : List Atom :=
  memoryAtoms fr p s ++ bounds s ++ preservedAtoms fr controls s (fr.rsp - 0x188) ++
  firstResult fr s ++ secondResult fr s

end P256.Proofs.Field.Inverse.SafeGcd.Core.Update
