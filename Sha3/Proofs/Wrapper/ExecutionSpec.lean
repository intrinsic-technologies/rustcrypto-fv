import Sha3.Proofs.Wrapper.Invariant
import Sha3.Proofs.Absorption

namespace Sha3.Proofs.Wrapper

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

def afterInputs (mode : Mode) (inputs : Array Input) (split : Nat) : Array Input :=
  match mode with
  | .plain | .digest => inputs
  | _ => inputs.extract split inputs.size

def expectedDigest (v : Variant) (mode : Mode) (inputs : Array Input) (split : Nat)
    (keccak : Bool := false) (fullState : Bool := false) :
    Standards.NIST.SHA3.Digest (mode.entry v keccak fullState).outputBytes :=
  Absorption.digestLanes
    (Absorption.absorbSha3 Keccak.keccakLanes v.rate (message (afterInputs mode inputs split))
      (Variant.suffix keccak))
    (mode.entry v keccak fullState).outputBytes (by
      rw [Mode.entry_digestBytes mode v keccak fullState]
      exact v.digestBytes_le_state fullState)

def expectedBeforeDigest (v : Variant) (inputs : Array Input) (split : Nat)
    (mode : Mode := .finalizeReset) (keccak : Bool := false) (fullState : Bool := false) :
    Standards.NIST.SHA3.Digest (mode.entry v keccak fullState).outputBytes :=
  Absorption.digestLanes
    (Absorption.absorbSha3 Keccak.keccakLanes v.rate (message (inputs.extract 0 split))
      (Variant.suffix keccak))
    (mode.entry v keccak fullState).outputBytes (by
      rw [Mode.entry_digestBytes mode v keccak fullState]
      exact v.digestBytes_le_state fullState)

structure ExecutionResult [Bindings] (v : Variant) (mode : Mode) (initial : RamState)
    (inputs : Array Input) (split : Nat) (final : RamState)
    (keccak : Bool := false) (fullState : Bool := false) : Prop where
  invariant : Invariant initial v mode final keccak fullState
  output : readBytes (mode.output (mode.entry v keccak fullState) initial)
      (mode.entry v keccak fullState).outputBytes final =
    .ok (expectedDigest v mode inputs split keccak fullState)
  before : mode.hasBeforeOutput = true →
    readOutput (mode.entry v keccak fullState) initial final =
      .ok (expectedBeforeDigest v inputs split mode keccak fullState)
  saved : CalleeSavedRegistersUnchanged initial final

end Sha3.Proofs.Wrapper
