import P256.Proofs.Verifying.Core.Inverse.SafeGcd.Defs

namespace P256.Proofs.Verifying.Core.Inverse.SafeGcd.Prefix

open P256.Proofs.Field.Inverse.SafeGcd
open P256.Proofs.Field.Inverse.SafeGcd.Core.Shared
open P256.Proofs.Field.Inverse.SafeGcd.Core.Shared.Batch
open P256.Proofs.Field.Inverse.SafeGcd.Core

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

inductive Label where | entry | loads | coefficients | initialize | finish

@[refine_layout] def start : Label → Machine.Label
  | .entry => .l1141e0 | .loads => .l114201 | .coefficients => .l114285
  | .initialize => .l1142ec | .finish => .l11454e

def program : Program Core.Support.Op Label (fun _ => 0) 0 where
  blocks
  | .entry => .terminate (.br ⟨.loads, #v[]⟩)
  | .loads => .terminate (.br ⟨.coefficients, #v[]⟩)
  | .coefficients => .terminate (.br ⟨.initialize, #v[]⟩)
  | .initialize => .terminate (.br ⟨.finish, #v[]⟩)
  | .finish => .terminate (.ret #v[])

def dialect : Dialect Core.Support.Op Unit Inputs where
  eval op := nomatch op
  truth _ := false

@[refine_layout] def atoms (l : Label) (fr : Activation) (controls : RamState) (p : Inputs) : List Atom :=
  match l with
  | .entry | .loads => Machine.Core.frameAt (start l) fr ++
      [.reg 39 ⟨32, controls.MXCSR⟩, .reg 51 ⟨16, controls.FP87_Control⟩] ++ commonAtoms fr p
  | .coefficients => Machine.Core.frameAt .l114285 fr ++
      [.reg 39 ⟨32, controls.MXCSR⟩, .reg 51 ⟨16, controls.FP87_Control⟩] ++ commonAtoms fr p ++
    savedInputAtoms fr p ++ signedAtoms (fr.rsp - 0x180) (initialState p).f ++
    signedAtoms (fr.rsp - 0x158) (initialState p).g
  | .initialize => Machine.Core.frameAt .l1142ec fr ++
      [.reg 39 ⟨32, controls.MXCSR⟩, .reg 51 ⟨16, controls.FP87_Control⟩] ++ commonAtoms fr p ++
    savedInputAtoms fr p ++ stateAtoms fr (initialState p)
  | .finish => loopAtoms fr controls p (initialState p)

def layout (fr : Activation) (controls : RamState) : Layout program dialect Machine.lifted Unit where
  start := start
  Params _ := Inputs
  args _ _ := #v[]
  store _ p := p
  atoms l _ p := atoms l fr controls p
  Result := Empty
  output r := nomatch r
  done _ r := nomatch r
  retAddr _ := fr.ret
  original _ := fr.original
  regions _ := [fr.region, outputRegion fr]

end P256.Proofs.Verifying.Core.Inverse.SafeGcd.Prefix
