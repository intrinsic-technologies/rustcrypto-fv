import Sha2.Spec
import Sha2.Proofs.Wrapper512.Correctness

namespace Sha2.Statements

open Sha2.Spec Sha2.Spec.Program Standards.NIST.SHA2 Prelude X86

theorem sha512_224_digest_slices_writes_sha512_224_of_message
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {inputs : Array Input}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall sha512_224DigestSlices initial inputs) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[outputRegion sha512_224DigestSlices initial,
          Stack.region initial sha512_224DigestSlices.minStackBytes] ∧
      readOutput sha512_224DigestSlices initial final =
        .ok (SHA512_224 (bytesToBits (message inputs))).bytes := by
  exact (Sha2.Proofs.Wrapper512.wrapper_contract .sha512_224).toExists
    (Sha2.Proofs.Wrapper512.Context.of_root .sha512_224 hBindings hMachine hCall)

theorem sha512_256_digest_slices_writes_sha512_256_of_message
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {inputs : Array Input}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall sha512_256DigestSlices initial inputs) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[outputRegion sha512_256DigestSlices initial,
          Stack.region initial sha512_256DigestSlices.minStackBytes] ∧
      readOutput sha512_256DigestSlices initial final =
        .ok (SHA512_256 (bytesToBits (message inputs))).bytes := by
  exact (Sha2.Proofs.Wrapper512.wrapper_contract .sha512_256).toExists
    (Sha2.Proofs.Wrapper512.Context.of_root .sha512_256 hBindings hMachine hCall)


end Sha2.Statements
