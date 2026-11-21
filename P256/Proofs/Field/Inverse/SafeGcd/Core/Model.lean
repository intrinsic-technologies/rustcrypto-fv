import P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic.Shared.Model

set_option autoImplicit false

namespace P256.Proofs.Field.Inverse.SafeGcd.Core

abbrev Inputs := Shared.Inputs
abbrev LoopState := Shared.LoopState

def runBatches : Nat → Inputs → LoopState → LoopState
  | 0, _, s => s
  | fuel+1, p, s =>
    if s.remaining = 0 then s else runBatches fuel p (Shared.nextState p s)

def finalState (p : Inputs) : LoopState := runBatches 10 p (Shared.initialState p)

def resultWords (p : Inputs) : Vector (BitVec 64) 4 :=
  Correction.correctedWords (Shared.correctionInput p (finalState p))

def resultChoice (p : Inputs) : BitVec 8 :=
  BitVec.ofNat 8 (if !Shared.zeroWords p.a && Shared.zeroWords ((finalState p).f.words.set 0
    ((finalState p).f.words[0] ^^^ 1)) then 1 else 0)

end P256.Proofs.Field.Inverse.SafeGcd.Core
