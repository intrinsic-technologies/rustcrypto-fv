import K256.Spec

namespace K256.Proofs

open K256.Spec K256.Spec.Program Prelude X86

def SignatureSliceResult [bindings : Machine.Bindings] (initial : Machine.RamState)
    (bytes : ByteArray) : Prop :=
  ∃ (fuel : Nat) (final : Machine.RamState),
    UniqueExecution initial fuel final ∧
    SupportedIntegerMachineState bindings.processor final ∧
    MachineRamUnitStrideDecodable bindings final ∧
    CalleeSavedRegistersUnchanged initial final ∧
    DirectionFlagUnset final ∧
    match Ecdsa.signatureScalars bytes with
    | some (r, s) =>
      SuccessfulStatus final ∧
      MemoryWriteFrame initial final
        #v[outputRegion signatureFromSlice initial,
          Stack.region initial signatureFromSlice.minStackBytes] ∧
      readOutput signatureFromSlice initial final = .ok (Ecdsa.signatureBytes r s)
    | none =>
      FailureStatus final signatureErrorStatus ∧
      MemoryWriteFrame initial final
        #v[Stack.region initial signatureFromSlice.minStackBytes]

end K256.Proofs
