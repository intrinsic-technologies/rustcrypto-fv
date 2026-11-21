import P256.Proofs.Verifying.Core.Inverse.SafeGcd.Defs
import P256.Proofs.Field.Inverse.SafeGcd.Correction
import P256.Proofs.Field.Inverse.SafeGcd.Core.Prepare.Frame

namespace P256.Proofs.Verifying.Core.Inverse.SafeGcd.Tail

open P256.Proofs.Field.Inverse.SafeGcd.Core.Shared (zeroWords correctionInput)

open P256.Proofs.Field.Inverse.SafeGcd

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

def nonzeroByte (p : Inputs) : BitVec 8 := if zeroWords p.a then 0 else 1

def choiceByte (p : Inputs) (s : LoopState) : BitVec 8 :=
  BitVec.ofNat 8 (if !zeroWords p.a && zeroWords (s.f.words.set 0
    (s.f.words[0] ^^^ 1)) then 1 else 0)

@[refine_layout] def savedAtoms (fr : Activation) : List Atom :=
  [.mem (fr.rsp - 8) 64 fr.rbp, .mem (fr.rsp - 16) 64 fr.r15,
   .mem (fr.rsp - 24) 64 fr.r14, .mem (fr.rsp - 32) 64 fr.r13,
   .mem (fr.rsp - 40) 64 fr.r12, .mem (fr.rsp - 48) 64 fr.rbx,
   .mem fr.rsp 64 fr.ret, .readable fr.rsp 8, .fact (fr.ret.toNat < 2^32),
   .writable (fr.rsp - 0x2c0) 0x2c0, .fact (fr.low.toNat + 0x2c0 ≤ fr.rsp.toNat),
   .fact (fr.rsp.toNat % 16 = 8)]

@[refine_layout] def residentAtoms (fr : Activation) (s : LoopState) : List Atom :=
  savedAtoms fr ++ outputAtoms fr ++ signedAtoms (fr.rsp - 0x180) s.f

@[refine_layout] def callAtoms (fr : Activation) (controls : RamState) (p : Inputs) (s : LoopState) : List Atom :=
  residentAtoms fr s ++
  [.words (fr.rsp - 0x128) 64 s.d.words, .mem (fr.rsp - 0x108) 8 s.d.sign,
   .words fr.rdx 64 p.modulus, .readable fr.rdx 32,
   .fact (fr.rdx.toNat + 32 ≤ fr.low.toNat ∨ fr.rsp.toNat ≤ fr.rdx.toNat),
   .gpr 4 (fr.rsp - 0x190), .reg 22 ⟨1, 0⟩,
   .low 3 8 (nonzeroByte p), .gpr 14 fr.rdi,
   .gpr 7 fr.rdi, .gpr 6 (fr.rsp - 0x128), .gpr 1 fr.rdx, .low 2 8 s.f.sign,
   .mem (fr.rsp - 0x190) 64 0x112689, .readable (fr.rsp - 0x190) 8,
   .reg 39 ⟨32, controls.MXCSR⟩, .reg 51 ⟨16, controls.FP87_Control⟩]

@[refine_layout] def returnedAtoms (fr : Activation) (controls : RamState) (p : Inputs) (s : LoopState) : List Atom :=
  residentAtoms fr s ++
  [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩,
   .low 3 8 (nonzeroByte p), .gpr 14 fr.rdi,
   .words fr.rdi 64 (Correction.correctedWords (correctionInput p s)),
   .readable fr.rdi 32,
   .reg 39 ⟨32, controls.MXCSR⟩, .reg 51 ⟨16, controls.FP87_Control⟩]

end P256.Proofs.Verifying.Core.Inverse.SafeGcd.Tail
