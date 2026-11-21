import Sha3.Proofs.Variant

namespace Sha3.Proofs.Finalize

def entryAddress (v : Variant) (reset : Bool := false) (keccak : Bool := false) (fullState : Bool := false) : BitVec 64 :=
  if reset then v.finalizeResetAddress keccak fullState else v.finalizeAddress keccak fullState

def callAddress (v : Variant) (reset : Bool := false) (keccak : Bool := false) (fullState : Bool := false) : BitVec 64 :=
  entryAddress v reset keccak fullState + (if fullState || (v = .sha224 ∨ v = .sha256) then 46 else 43)

def outputAddress (v : Variant) (reset : Bool := false) (keccak : Bool := false) (fullState : Bool := false) : BitVec 64 :=
  callAddress v reset keccak fullState + 5

def outputBytes (v : Variant) (fullState : Bool := false) (reset : Bool := false) : Nat :=
  if fullState then (if reset then 17 else 11) else
    match v with
    | .sha224 => 29 | .sha256 => 30 | .sha384 => 46 | .sha512 => 62

def epilogueAddress (v : Variant) (reset : Bool := false) (keccak : Bool := false) (fullState : Bool := false) : BitVec 64 :=
  outputAddress v reset keccak fullState + BitVec.ofNat 64 (outputBytes v fullState reset)

def frameBytes : Nat := 296

end Sha3.Proofs.Finalize
