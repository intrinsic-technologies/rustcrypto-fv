import Sha1.Spec
import Sha1.Proofs.Entry.Digest.Execution
import Sha1.Proofs.Entry.UpdateFinalize.Execution

namespace Sha1.Statements

open Sha1.Spec Sha1.Spec.Program Standards.NIST Prelude X86

theorem sha1_digest_writes_digest_of_input
    {initial : Machine.RamState} {input : ByteArray}
    (bindings : Machine.Bindings)
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : Digest.ValidCall bindings initial input) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution (bindings := bindings) initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[Digest.outputRegion initial, Stack.region initial Digest.minStackBytes] ∧
      Digest.readOutput initial final = .ok (SHA1.SHA1 (SHA2.bytesToBits input)).bytes := by
  exact Sha1.Proofs.Entry.Digest.digest_execution bindings hBindings hMachine hCall

theorem sha1_update_finalize_writes_digest_of_inputs
    {initial : Machine.RamState} {inputs : Array Slices.Input}
    (bindings : Machine.Bindings)
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : SliceHash.ValidCall SliceHash.updateFinalize bindings initial inputs) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution (bindings := bindings) initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[SliceHash.outputRegion SliceHash.updateFinalize initial,
          Stack.region initial SliceHash.updateFinalize.minStackBytes] ∧
      SliceHash.readOutput SliceHash.updateFinalize initial final =
        .ok (SHA1.SHA1 (SHA2.bytesToBits (Slices.message inputs))).bytes := by
  exact Sha1.Proofs.Entry.UpdateFinalize.update_finalize_execution bindings hBindings hMachine hCall

end Sha1.Statements
