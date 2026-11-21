import Sha2.Proofs.OneShot.Correctness
import Sha2.Spec

namespace Sha2.Statements

open Sha2.Spec Sha2.Spec.Program Standards.NIST.SHA2 Prelude X86

theorem sha256_digest_writes_sha256_of_data
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {data : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : OneShot.ValidCall sha256Digest initial data) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[OneShot.outputRegion sha256Digest initial,
          Stack.region initial sha256Digest.minStackBytes] ∧
      OneShot.readOutput sha256Digest initial final = .ok (SHA256 (bytesToBits data)).bytes := by
  exact Sha2.Proofs.OneShot.correct hBindings hMachine hCall

end Sha2.Statements
