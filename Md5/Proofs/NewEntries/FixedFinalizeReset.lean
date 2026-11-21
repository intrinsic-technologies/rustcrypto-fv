import Md5.Proofs.NewEntries.FinalizeReset

namespace Md5.Statements

open Md5.Spec Md5.Spec.Program Prelude X86 Standards.RFC

theorem md5_fixed_finalize_into_reset_slices_writes_both_message_digests
    {initial : Machine.RamState} {inputs : Array Slices.Input} {first : Nat}
    (bindings : Machine.Bindings)
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall :
      TwoMessages.ValidCall TwoMessages.fixedFinalizeIntoResetSlices bindings initial inputs
        first) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution (bindings := bindings) initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[TwoMessages.outputRegion TwoMessages.fixedFinalizeIntoResetSlices initial,
          Stack.region initial TwoMessages.fixedFinalizeIntoResetSlices.minStackBytes] ∧
      TwoMessages.readOutput TwoMessages.fixedFinalizeIntoResetSlices initial final =
        .ok (MD5.messageDigest (MD5.bitsOfBytes (Slices.firstMessage inputs first)) ++
            MD5.messageDigest (MD5.bitsOfBytes (Slices.secondMessage inputs first))) := by
  exact md5_finalize_into_reset_slices_writes_both_message_digests bindings hBindings hMachine hCall

end Md5.Statements
