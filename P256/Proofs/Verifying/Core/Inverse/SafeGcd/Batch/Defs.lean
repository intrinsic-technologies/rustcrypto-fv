import P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic.Shared.Batch.Model
import P256.Proofs.Verifying.Core.Inverse.SafeGcd.Machine
import P256.Proofs.Field.Inverse.SafeGcd.Core.Support

namespace P256.Proofs.Verifying.Core.Inverse.SafeGcd.Batch

open P256.Proofs.Field.Inverse.SafeGcd
open P256.Proofs.Field.Inverse.SafeGcd.Core.Shared
open P256.Proofs.Field.Inverse.SafeGcd.Core.Shared.Batch
open P256.Proofs.Field.Inverse.SafeGcd.Core

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

inductive Path where | even | swap | add

inductive Label where | entry | odd | even | swap | add | join | shift | finish

@[refine_layout] def exitLabel (last : Bool) : Machine.Label :=
  match last with | true => .l114311 | false => .l114675

@[refine_layout] def start (last : Bool) : Label → Machine.Label
  | .entry => .l114675 | .odd => .l114630 | .even => .l11467a
  | .swap => .l114635 | .add => .l114680 | .join => .l11468d
  | .shift => .l11465b | .finish => exitLabel last

def program (path : Path) : Program Core.Support.Op Label (fun _ => 0) 0 where
  blocks
  | .entry => .terminate (.br ⟨match path with | .even => .even | _ => .odd, #v[]⟩)
  | .odd => .terminate (.br ⟨match path with | .swap => .swap | _ => .add, #v[]⟩)
  | .even | .add => .terminate (.br ⟨.join, #v[]⟩)
  | .swap | .join => .terminate (.br ⟨.shift, #v[]⟩)
  | .shift => .terminate (.br ⟨.finish, #v[]⟩)
  | .finish => .terminate (.ret #v[])

def dialect : Dialect Core.Support.Op Unit (Words × Nat) where
  eval op := nomatch op
  truth _ := false

@[refine_layout] def pathFacts (path : Path) (p : Words) : List Atom :=
  match path with
  | .even => [.fact (even p = true)]
  | .swap => [.fact (even p = false), .fact (positive p = true)]
  | .add => [.fact (even p = false), .fact (positive p = false)]

@[refine_layout] def frameAtoms (fr : Activation) (controls : RamState) : List Atom :=
  [.gpr 4 fr.rsp, .gpr 9 fr.r9, .reg 22 ⟨1, 0⟩,
   .reg 39 ⟨32, controls.MXCSR⟩, .reg 51 ⟨16, controls.FP87_Control⟩]

@[refine_layout] def wordAtoms (p : Words) (remaining : Nat) : List Atom :=
  [.gpr 0 p.f, .gpr 1 p.g, .gpr 3 p.u, .gpr 15 p.v,
   .gpr 6 p.q, .gpr 7 p.r, .gpr 12 p.delta,
   .gpr 2 ((BitVec.ofNat 32 remaining).setWidth 64)]

@[refine_layout] def loopAtoms (fr : Activation) (controls : RamState) (p : Words) (remaining : Nat) : List Atom :=
  frameAtoms fr controls ++ wordAtoms p remaining

@[refine_layout] def finishAtoms (last : Bool) (fr : Activation) (controls : RamState) (p : Words) (remaining : Nat) : List Atom :=
  match last with
  | true => frameAtoms fr controls ++
    [.gpr 3 p.u, .gpr 15 p.v, .gpr 13 p.q, .gpr 14 p.r, .gpr 12 p.delta]
  | false => loopAtoms fr controls p remaining

@[refine_layout] def shiftAtoms (p : Words) (remaining : Nat) : List Atom :=
  [.gpr 0 (next p).f, .gpr 12 (next p).delta,
   .gpr 8 (numerator p),
   .gpr 3 (if swap p then p.q else p.u), .gpr 15 (if swap p then p.r else p.v),
   .gpr 13 (next p).q, .gpr 14 (next p).r,
   .gpr 2 ((BitVec.ofNat 32 remaining).setWidth 64)]

@[refine_layout] def joinAtoms (p : Words) (remaining : Nat) : List Atom :=
  [.gpr 0 p.f, .gpr 1 (numerator p), .gpr 12 (p.delta + 2),
   .gpr 3 p.u, .gpr 15 p.v, .gpr 6 (next p).q, .gpr 7 (next p).r,
   .gpr 2 ((BitVec.ofNat 32 remaining).setWidth 64)]

@[refine_layout] def atoms (path : Path) (last : Bool) (l : Label)
    (fr : Activation) (controls : RamState) (p : Words) (remaining : Nat) : List Atom :=
  match l with
  | .finish => finishAtoms last fr controls (next p) (remaining - 1)
  | l => frameAtoms fr controls ++ pathFacts path p ++
      [.fact (1 ≤ remaining), .fact (remaining ≤ 62),
       .fact (if last then remaining = 1 else 1 < remaining)] ++
      match l with
      | .join => joinAtoms p remaining
      | .shift => shiftAtoms p remaining
      | _ => wordAtoms p remaining

def layout (path : Path) (last : Bool) (fr : Activation) (controls : RamState) :
    Layout (program path) dialect Machine.lifted Unit where
  start := start last
  Params _ := Words × Nat
  args _ _ := #v[]
  store _ p := p
  atoms l _ p := atoms path last l fr controls p.1 p.2
  Result := Empty
  output r := nomatch r
  done _ r := nomatch r
  retAddr _ := fr.ret
  original _ := fr.original
  regions _ := []

end P256.Proofs.Verifying.Core.Inverse.SafeGcd.Batch
