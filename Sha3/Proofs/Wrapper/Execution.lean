import Sha3.Proofs.Wrapper.Execution.Plain
import Sha3.Proofs.Wrapper.Execution.Reset
import Sha3.Proofs.Wrapper.Execution.FinalizeReset
import Sha3.Proofs.Update
import Sha3.Proofs.Wrapper.Setup

namespace Sha3.Proofs.Wrapper

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

theorem execution_with_options [bindings : Bindings] (v : Variant) (mode : Mode)
    (keccak fullState : Bool)
    {initial : RamState} {inputs : Array Input} {split : Nat}
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hEnvironment : MachineRamUnitStrideDecodable bindings initial)
    (hCall : ValidInvocation bindings v mode initial inputs split keccak fullState) :
    ∃ fuel final, Returns (returnBoundary initial) fuel initial final ∧
      ExecutionResult v mode initial inputs split final keccak fullState := by
  have hInitial := (Invariant.initial hMachine hEnvironment hCall).ready
  have hBoundary := (validInvocation_returnBoundary_bounds hInitial hCall).2
  have hUpdate : Loop.UpdateCorrect v (returnBoundary initial) := by
    intro called bytes state hc
    exact Update.call_advance hc (returnBoundary initial) hBoundary
  cases mode with
  | plain | digest => exact plain_execution_with_update hMachine hEnvironment hCall hUpdate
  | reset =>
    obtain ⟨_, n, s, hRun, hFirst⟩ := Setup.through_first_loop hMachine hEnvironment hCall hUpdate
    obtain ⟨fuel, final, hReturn, hResult⟩ := reset_after_first_with_update
      hEnvironment.stringStride hInitial hCall hUpdate hFirst
    exact ⟨n + fuel, final, hRun.returns hReturn, hResult⟩
  | finalizeReset | finalizeFixedReset | digestFinalizeIntoReset | digestFinalizeReset =>
    obtain ⟨_, n, s, hRun, hFirst⟩ := Setup.through_first_loop hMachine hEnvironment hCall hUpdate
    obtain ⟨fuel, final, hReturn, hResult⟩ := finalize_reset_after_first_with_update
      hEnvironment.stringStride hInitial hCall hUpdate hFirst
    exact ⟨n + fuel, final, hRun.returns hReturn, hResult⟩

theorem execution [bindings : Bindings] (v : Variant) (mode : Mode)
    {initial : RamState} {inputs : Array Input} {split : Nat}
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hEnvironment : MachineRamUnitStrideDecodable bindings initial)
    (hCall : ValidInvocation bindings v mode initial inputs split) :
    ∃ fuel final, Returns (returnBoundary initial) fuel initial final ∧
      ExecutionResult v mode initial inputs split final := by
  exact execution_with_options v mode false false hMachine hEnvironment hCall

end Sha3.Proofs.Wrapper
