import P256.Proofs.Signing.Interface
import P256.Proofs.Signing.Mathematics

set_option autoImplicit false

namespace P256.Proofs.Signing

open P256.Spec Prelude X86 P256.Spec.Program.Routines

open Classical in
theorem correct_of_contracts (core : CoreContract) (wrapper : WrapperContract)
    [bindings : Machine.Bindings] {initial : Machine.RamState}
    {signingKey msg : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall signingKeyTrySign initial [signingKey, msg]) :
    if Ecdsa.NeverSigns #[signingKey, msg] then NeverReturns initial else
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[outputRegion signingKeyTrySign initial [signingKey, msg], allocatorStateRegion,
          randomSourceRegion, callStack signingKeyTrySign initial] ∧
      readOutput signingKeyTrySign initial final = .ok (Ecdsa.signMessage #[signingKey, msg]) := by
  have execution := wrapper core hBindings hMachine hCall
  by_cases exhausted : Ecdsa.NeverSigns #[signingKey, msg]
  · rw [ite_eq_left exhausted]
    exact execution.2 exhausted
  · rw [ite_eq_right exhausted]
    obtain ⟨attempts, found⟩ := signMessage_found exhausted
    exact execution.1 attempts _ found

end P256.Proofs.Signing
