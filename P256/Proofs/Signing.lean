import P256.Proofs.Signing.Correctness
import P256.Proofs.Signing.Core.Correct
import P256.Proofs.Signing.Wrapper

set_option autoImplicit false

namespace P256.Proofs.Signing

open P256.Spec Prelude X86 P256.Spec.Program.Routines

open Classical in
theorem signing_correct
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
  exact correct_of_contracts core_correct Wrapper.correct hBindings hMachine hCall

end P256.Proofs.Signing
