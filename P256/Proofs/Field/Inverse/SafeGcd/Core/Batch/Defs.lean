import P256.Proofs.Field.Inverse.SafeGcd.Core.Batch.Model
import P256.Proofs.Field.Inverse.SafeGcd.Core.Machine
import P256.Proofs.Field.Inverse.SafeGcd.Core.Support

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.Batch

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

inductive Label where | entry | selectedDelta | selectedFG | selectedUV | selectedQR | shift | finish

@[refine_layout] def exitLabel (last : Bool) : Machine.Label :=
  match last with | true => .l1177b1 | false => .l117aa0

@[refine_layout] def start (last : Bool) : Label → Machine.Label
  | .entry => .l117aa0 | .selectedDelta => .l117b01
  | .selectedFG => .l117b46 | .selectedUV => .l117b83
  | .selectedQR => .l117bc2 | .shift => .l117bdb | .finish => exitLabel last

def program : Program Support.Op Label (fun _ => 0) 0 where
  blocks
  | .entry => .terminate (.br ⟨.selectedDelta, #v[]⟩)
  | .selectedDelta => .terminate (.br ⟨.selectedFG, #v[]⟩)
  | .selectedFG => .terminate (.br ⟨.selectedUV, #v[]⟩)
  | .selectedUV => .terminate (.br ⟨.selectedQR, #v[]⟩)
  | .selectedQR => .terminate (.br ⟨.shift, #v[]⟩)
  | .shift => .terminate (.br ⟨.finish, #v[]⟩)
  | .finish => .terminate (.ret #v[])

def dialect : Dialect Support.Op Unit (Words × Nat) where
  eval op := nomatch op
  truth _ := false

def scratchRegion (fr : Activation) : MemoryRegion := ⟨(fr.rsp + 8).toNat, 1⟩

@[refine_layout] def frameAtoms (fr : Activation) (controls : RamState) : List Atom :=
  [.gpr 4 fr.rsp, .gpr 13 fr.r13, .reg 22 ⟨1, 0⟩,
   .writable (fr.rsp + 8) 1, .fact (fr.rsp.toNat + 9 < 2^64),
   .reg 39 ⟨32, controls.MXCSR⟩, .reg 51 ⟨16, controls.FP87_Control⟩]

@[refine_layout] def wordAtoms (p : Words) (remaining : Nat) : List Atom :=
  [.gpr 0 p.g, .gpr 2 p.f, .gpr 5 p.delta, .gpr 7 p.u, .gpr 6 p.v,
   .gpr 14 p.q, .gpr 12 p.r, .gpr 1 ((BitVec.ofNat 32 remaining).setWidth 64)]

@[refine_layout] def loopAtoms (fr : Activation) (controls : RamState) (p : Words) (remaining : Nat) : List Atom :=
  frameAtoms fr controls ++ wordAtoms p remaining

@[refine_layout] def finishAtoms (last : Bool) (fr : Activation) (controls : RamState) (p : Words) (remaining : Nat) : List Atom :=
  match last with
  | true => frameAtoms fr controls ++ [.gpr 5 p.delta, .gpr 15 p.u, .gpr 3 p.v, .gpr 14 p.q, .gpr 12 p.r]
  | false => loopAtoms fr controls p remaining

@[refine_layout] def stageAtoms (l : Label) (p : Words) (remaining : Nat) : List Atom :=
  match l with
  | .finish => []
  | .entry => wordAtoms p remaining
  | .selectedDelta =>
        [.gpr 0 p.g, .gpr 11 p.f, .gpr 5 (next p).delta, .gpr 7 p.u, .gpr 6 p.v,
         .gpr 14 p.q, .gpr 12 p.r, .gpr 1 ((BitVec.ofNat 32 remaining).setWidth 64),
         .gpr 3 (maskedF p), .gpr 9 (positiveBit p.delta), .low 8 8 (oddByte p),
         .low 10 8 (swapByte p)]
  | .selectedFG =>
        [.gpr 0 (select (swapByte p) (p.g + maskedF p) (p.g - maskedF p)),
         .gpr 2 (next p).f, .gpr 5 (next p).delta, .gpr 7 p.u, .gpr 6 p.v,
         .gpr 14 p.q, .gpr 12 p.r, .gpr 1 ((BitVec.ofNat 32 remaining).setWidth 64),
         .gpr 11 (-(swapByte p).setWidth 64), .gpr 9 (positiveBit p.delta),
         .low 8 8 (oddByte p), .low 10 8 (swapByte p)]
  | .selectedUV =>
        [.gpr 0 (select (swapByte p) (p.g + maskedF p) (p.g - maskedF p)),
         .gpr 2 (next p).f, .gpr 5 (next p).delta, .gpr 7 p.u, .gpr 6 p.v,
         .gpr 14 p.q, .gpr 12 p.r, .gpr 1 ((BitVec.ofNat 32 remaining).setWidth 64),
         .gpr 15 (select (swapByte p) p.u p.q),
         .gpr 10 ((-((positiveBit p.delta).setWidth 8).setWidth 64) &&& (-p.u ^^^ p.u)),
         .gpr 3 ((-(swapByte p).setWidth 64) &&& (p.r ^^^ p.v)),
         .gpr 9 (positiveBit p.delta), .low 8 8 (oddByte p)]
  | .selectedQR =>
        [.gpr 0 (next p).g, .gpr 2 (next p).f, .gpr 5 (next p).delta,
         .gpr 15 (next p).u, .gpr 3 (next p).v, .gpr 14 (next p).q, .gpr 12 p.r,
         .gpr 1 ((BitVec.ofNat 32 remaining).setWidth 64), .low 8 8 (oddByte p),
         .gpr 7 (select ((positiveBit p.delta).setWidth 8) p.v (-p.v))]
  | .shift => wordAtoms (next p) remaining ++ [.gpr 15 (next p).u, .gpr 3 (next p).v]

@[refine_layout] def atoms (last : Bool) (l : Label) (fr : Activation) (controls : RamState) (p : Words) (remaining : Nat) : List Atom :=
  match l with
  | .finish => finishAtoms last fr controls (next p) (remaining - 1)
  | l => frameAtoms fr controls ++ [.fact (1 ≤ remaining), .fact (remaining ≤ 62),
      .fact (if last then remaining = 1 else 1 < remaining)] ++ stageAtoms l p remaining

def layout (last : Bool) (fr : Activation) (controls : RamState) : Layout program dialect Machine.lifted Unit where
  start := start last
  Params _ := Words × Nat
  args _ _ := #v[]
  store _ p := p
  atoms l _ p := atoms last l fr controls p.1 p.2
  Result := Empty
  output r := nomatch r
  done _ r := nomatch r
  retAddr _ := fr.ret
  original _ := fr.original
  regions _ := [scratchRegion fr]

end P256.Proofs.Field.Inverse.SafeGcd.Core.Batch
