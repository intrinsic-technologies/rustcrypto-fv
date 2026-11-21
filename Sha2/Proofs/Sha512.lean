import Sha2.Spec
import Sha2.Proofs.Wrapper512.Correctness

namespace Sha2.Statements

open Sha2.Spec Sha2.Spec.Program Standards.NIST.SHA2 Prelude X86

theorem sha512_digest_slices_writes_sha512_of_message
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {inputs : Array Input}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall sha512DigestSlices initial inputs) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[outputRegion sha512DigestSlices initial,
          Stack.region initial sha512DigestSlices.minStackBytes] ∧
      readOutput sha512DigestSlices initial final =
        .ok (SHA512 (bytesToBits (message inputs))).bytes := by
  exact Sha2.Proofs.Wrapper512.sha512_of_wrapper_contract
    (Sha2.Proofs.Wrapper512.wrapper_contract .sha512) hBindings hMachine hCall

end Sha2.Statements
