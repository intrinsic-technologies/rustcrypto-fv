import Sha2.Proofs.Wrapper.Absorb.Correctness
import Sha2.Proofs.Wrapper.Dispatch
import Sha2.Proofs.Wrapper.Finish


namespace Sha2.Statements

open Sha2.Spec Sha2.Spec.Program Standards.NIST Prelude X86

theorem sha256_digest_slices_writes_sha256_of_message
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {inputs : Array Input}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall sha256DigestSlices initial inputs) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[outputRegion sha256DigestSlices initial, Stack.region initial sha256DigestSlices.minStackBytes] ∧
      readOutput sha256DigestSlices initial final =
        .ok (SHA2.SHA256 (SHA2.bytesToBits (message inputs))).bytes := by
  have ctx : Sha2.Proofs.Wrapper.Context initial inputs :=
    ⟨hBindings.stringStride,
      Sha2.Proofs.Program.SupportedMachine.of_root bindings initial hMachine hBindings, hCall⟩
  obtain ⟨s, finalized | loop⟩ := Sha2.Proofs.Wrapper.Dispatch.run ctx
  · exact Sha2.Proofs.Wrapper.finish ctx finalized.1 finalized.2
  · obtain ⟨t, buffered, rip⟩ := Sha2.Proofs.Wrapper.Absorb.absorb_all ctx loop
    exact Sha2.Proofs.Wrapper.finish ctx buffered rip

end Sha2.Statements
