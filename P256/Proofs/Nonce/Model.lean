import P256.Proofs.HMAC.Mathematics

set_option autoImplicit false

namespace P256.Proofs.Nonce

open P256.Spec

abbrev State := Standards.RFC.DeterministicSigning.Nonce.State

def updateValue (state : State) : State :=
  ⟨state.key, Standards.RFC.HMAC.hmac Operations.hash 64 state.key state.value⟩

def updateRound (tag : UInt8) (seed : ByteArray) (state : State) : State :=
  let key := Standards.RFC.HMAC.hmac Operations.hash 64 state.key
    (state.value ++ ⟨#[tag]⟩ ++ seed)
  updateValue ⟨key, state.value⟩

def updateState (nonempty : Bool) (seed : ByteArray) (state : State) : State :=
  let state := updateRound 0 seed state
  if nonempty then updateRound 1 seed state else state

end P256.Proofs.Nonce
