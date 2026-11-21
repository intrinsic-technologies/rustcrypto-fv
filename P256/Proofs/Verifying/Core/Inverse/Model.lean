import P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic.Shared.Model

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Inverse.SafeGcd

open P256.Proofs.Field.Inverse.SafeGcd
open P256.Proofs.Field.Inverse.SafeGcd.Core.Shared

abbrev Inputs := Core.Shared.Inputs
abbrev LoopState := Core.Shared.LoopState

def runBatches : Nat → Inputs → LoopState → LoopState
  | 0, _, s => s
  | fuel+1, p, s =>
    if s.remaining = 0 ∨ zeroWords s.g.words then s
    else runBatches fuel p (nextState p s)

def finalState (p : Inputs) : LoopState := runBatches 10 p (initialState p)

def resultWords (p : Inputs) : Vector (BitVec 64) 4 :=
  Correction.correctedWords (correctionInput p (finalState p))

def resultChoice (p : Inputs) : BitVec 8 :=
  BitVec.ofNat 8 (if !zeroWords p.a && zeroWords ((finalState p).f.words.set 0
    ((finalState p).f.words[0] ^^^ 1)) then 1 else 0)

end P256.Proofs.Verifying.Core.Inverse.SafeGcd
