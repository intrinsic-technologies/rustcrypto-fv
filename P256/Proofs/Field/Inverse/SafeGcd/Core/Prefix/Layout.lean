import P256.Proofs.Field.Inverse.SafeGcd.Core.Defs

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.Prefix

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

inductive Label where | entry | loads | coefficients | scale | initialize | finish

@[refine_layout] def start : Label → Machine.Label
  | .entry => .l117650 | .loads => .l117671 | .coefficients => .l1176da
  | .scale => .l11774d | .initialize => .l117784 | .finish => .l1179fa

def program : Program Support.Op Label (fun _ => 0) 0 where
  blocks
  | .entry => .terminate (.br ⟨.loads, #v[]⟩)
  | .loads => .terminate (.br ⟨.coefficients, #v[]⟩)
  | .coefficients => .terminate (.br ⟨.scale, #v[]⟩)
  | .scale => .terminate (.br ⟨.initialize, #v[]⟩)
  | .initialize => .terminate (.br ⟨.finish, #v[]⟩)
  | .finish => .terminate (.ret #v[])

def dialect : Dialect Support.Op Unit Inputs where
  eval op := nomatch op
  truth _ := false

@[refine_layout] def atoms (l : Label) (fr : Activation) (controls : RamState) (p : Inputs) : List Atom :=
  match l with
  | .entry | .loads => Machine.Core.frameAt (start l) fr ++
      [.reg 39 ⟨32, controls.MXCSR⟩, .reg 51 ⟨16, controls.FP87_Control⟩] ++ commonAtoms fr p
  | .coefficients => Machine.Core.frameAt (start l) fr ++
      [.reg 39 ⟨32, controls.MXCSR⟩, .reg 51 ⟨16, controls.FP87_Control⟩] ++ commonAtoms fr p ++
      savedInputAtoms fr p ++ signedAtoms (fr.rsp - 0x130) (Shared.initialState p).f ++
      [.gpr 9 0x7fffffffffffffff]
  | .scale => Machine.Core.frameAt (start l) fr ++
      [.reg 39 ⟨32, controls.MXCSR⟩, .reg 51 ⟨16, controls.FP87_Control⟩] ++ commonAtoms fr p ++
      savedInputAtoms fr p ++ signedAtoms (fr.rsp - 0x130) (Shared.initialState p).f ++
      signedAtoms (fr.rsp - 0x100) (Shared.initialState p).g ++
      signedAtoms (fr.rsp - 0xd8) (Shared.initialState p).d ++ [.gpr 9 0x7fffffffffffffff]
  | .initialize => frameAtoms fr controls ++ commonAtoms fr p ++ savedInputAtoms fr p ++
      stateAtoms fr (Shared.initialState p) ++ [.gpr 9 0x7fffffffffffffff]
  | .finish => loopAtoms fr controls p (Shared.initialState p)

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

end P256.Proofs.Field.Inverse.SafeGcd.Core.Prefix
