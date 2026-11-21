import P256.Proofs.Signing.Wrapper.Hash.Call.Correct

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Hash.Output

open P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem correct [Bindings] {initial start s : RamState} {signature : Nat × Nat}
    (state : Call.Result initial start s signature) :
    ∃ t, HashResult initial start t signature :=
  ⟨s, {
    toSerializedInput := {
      toState := state.toState
      rip := state.rip
      status := state.status
      first := state.first
      second := state.second
      output := state.savedOutput
      capacity := state.savedCapacity }
    run := state.run }⟩

end P256.Proofs.Signing.Wrapper.Hash.Output
