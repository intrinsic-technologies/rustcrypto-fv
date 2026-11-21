import Sha2.Proofs.Wrapper.Absorb.Correctness
import Sha2.Proofs.Wrapper.Dispatch
import Sha2.Proofs.Wrapper.Finish

namespace Sha2.Statements

open Sha2.Spec Sha2.Spec.Program Standards.NIST Prelude X86
open Standards.NIST.SHA2

theorem sha224_digest_slices_writes_sha224_of_message
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {inputs : Array Input}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall sha224DigestSlices initial inputs) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[outputRegion sha224DigestSlices initial,
          Stack.region initial sha224DigestSlices.minStackBytes] ∧
      readOutput sha224DigestSlices initial final =
        .ok (SHA224 (bytesToBits (message inputs))).bytes := by
  have ctx : Sha2.Proofs.Wrapper.Context initial inputs .sha224 :=
    ⟨hBindings.stringStride,
      Sha2.Proofs.Program.SupportedMachine.of_root bindings initial hMachine hBindings, hCall⟩
  obtain ⟨s, finalized | loop⟩ := Sha2.Proofs.Wrapper.Dispatch.run ctx
  · exact Sha2.Proofs.Wrapper.finish ctx finalized.1 finalized.2
  · obtain ⟨t, buffered, rip⟩ := Sha2.Proofs.Wrapper.Absorb.absorb_all ctx loop
    exact Sha2.Proofs.Wrapper.finish ctx buffered rip

end Sha2.Statements
