import Base16ct.Proofs.Base16ctLowerEncodeCorrect.Machine.Subroutine
import Base16ct.Proofs.Base16ctLowerEncodeCorrect.Machine.ABI.Run
import Base16ct.Proofs.Base16ctLowerEncodeCorrect.Boundary

namespace Base16ct.Proofs.LowerEncode

open Base16ct.Spec.Program Prelude X86 X86Proofs

theorem execution
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {input : List UInt8} {outputCapacity : Nat}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall base16ctLowerEncode initial input.toByteArray outputCapacity (2 * input.length)
      (2 * input.length ≤ outputCapacity)) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      Returns (returnBoundary initial) fuel initial final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      if 2 * input.length ≤ outputCapacity then
        SuccessfulStatus final ∧
        MemoryWriteFrame initial final
          #v[outputRegion initial (2 * input.length), lengthOutputRegion initial,
            Stack.region initial base16ctLowerEncode.minStackBytes] ∧
        readOutput initial final (2 * input.length) = .ok (encodedBytes input).toByteArray ∧
        readLengthOutput initial final = .ok (BitVec.ofNat 64 (2 * input.length))
      else
        FailureStatus final invalidLengthStatus ∧
        MemoryWriteFrame initial final
          #v[Stack.region initial base16ctLowerEncode.minStackBytes] := by
  have hInitial := MachineInvariant.initial
    (written := if 2 * input.length ≤ outputCapacity then 2 * input.length else 0)
    hBindings hMachine hCall
  have hBoundary := lowerEncode_returnBoundary_bounds hCall
  exact lower_abi_execute hBindings hInitial hCall hBoundary.1 hBoundary.2
    (fun _ hPre => subroutine hCall hBoundary.2 hPre)

end Base16ct.Proofs.LowerEncode
