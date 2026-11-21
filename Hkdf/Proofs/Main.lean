import Hkdf.Proofs.NewExpand.Extract
import Hkdf.Proofs.NewExpand.Expand
import Hkdf.Proofs.NewExpand.Wrapper

namespace Hkdf.Statements

open Hkdf.Spec Hkdf.Spec.Program Prelude X86

theorem hkdf_sha256_new_expand_writes_okm_or_rejects_length
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {salt : Option ByteArray} {ikm info : ByteArray}
    {okmLength : Nat}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall :
      ValidDeriveKeyCall Extracted.hkdfSha256NewExpandAddress
        hkdfSha256NewExpandMinStackBytes initial salt ikm info okmLength) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      hkdf_sha256_new_expand_writes_okm_or_rejects_length.match_1 (fun _ => Prop)
        (RFC5869.expandFromPrk .sha256 (RFC5869.extract .sha256 salt ikm) info okmLength)
        (fun okm =>
        SuccessfulStatus final ∧
        MemoryWriteFrame initial final
          #v[deriveKeyOutputRegion initial okmLength,
            Stack.region initial hkdfSha256NewExpandMinStackBytes] ∧
        readOutput (deriveKeyOutputRegion initial okmLength) final.external = .ok okm)
        (fun _ => False)
        (fun _ =>
        FailureStatus final invalidLengthStatus ∧
        MemoryWriteFrame initial final
          #v[Stack.region initial hkdfSha256NewExpandMinStackBytes]) := by
  exact Hkdf.Proofs.NewExpand.wrapper_correct Hkdf.Proofs.NewExpand.extract_correct
    Hkdf.Proofs.NewExpand.expand_correct hBindings hMachine hCall

end Hkdf.Statements
