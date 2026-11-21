import Md5.Proofs.NewEntries.Reset

namespace Md5.Statements

open Md5.Spec Md5.Spec.Program Prelude X86 Standards.RFC

theorem md5_reset_slices_writes_second_message_digest
    {initial : Machine.RamState} {inputs : Array Slices.Input} {first : Nat}
    (bindings : Machine.Bindings)
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall :
      ResetThenDigest.ValidCall ResetThenDigest.resetSlices bindings initial inputs first) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution (bindings := bindings) initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[ResetThenDigest.outputRegion ResetThenDigest.resetSlices initial,
          Stack.region initial ResetThenDigest.resetSlices.minStackBytes] ∧
      ResetThenDigest.readOutput ResetThenDigest.resetSlices initial final =
        .ok (MD5.messageDigest (MD5.bitsOfBytes (Slices.secondMessage inputs first))) := by
  exact md5_update_reset_slices_writes_second_message_digest bindings hBindings hMachine hCall

end Md5.Statements
