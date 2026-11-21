import Base16ct.Proofs.EncodeStr.Lower.Machine.Execution
import Base16ct.Proofs.EncodeStr.Upper.Epilogue
import Base16ct.Proofs.EncodeStr.Upper.Prologue
import Base16ct.Proofs.EncodeStr.Upper.Callee
import Base16ct.Spec

namespace Base16ct.Proofs.EncodeStr

open Base16ct.Spec Base16ct.Spec.Program Prelude X86 X86Proofs

 theorem lower_correct
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {input : ByteArray} {outputCapacity : Nat}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall base16ctLowerEncodeStr initial input outputCapacity
      (2 * input.size) (2 * input.size ≤ outputCapacity)) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      if 2 * input.size ≤ outputCapacity then
        SuccessfulStatus final ∧
        MemoryWriteFrame initial final
          #v[outputRegion initial (2 * input.size), lengthOutputRegion initial,
            Stack.region initial base16ctLowerEncodeStr.minStackBytes] ∧
        readOutput initial final (2 * input.size) = .ok (Base16.lowerEncoder input) ∧
        readLengthOutput initial final = .ok (BitVec.ofNat 64 (2 * input.size))
      else
        FailureStatus final invalidLengthStatus ∧
        MemoryWriteFrame initial final
          #v[Stack.region initial base16ctLowerEncodeStr.minStackBytes] := by
  have hBytes : input.data.toList.toByteArray = input := by
    apply ByteArray.ext
    simp only [List.data_toByteArray, Array.toArray_toList]
  have hLength : input.data.toList.length = input.size := Array.length_toList
  have hCall' : ValidCall base16ctLowerEncodeStr initial input.data.toList.toByteArray
      outputCapacity (2 * input.data.toList.length) (2 * input.data.toList.length ≤ outputCapacity) := by
    simpa only [hBytes, hLength] using hCall
  obtain ⟨fuel, final, hReturn, hFinal⟩ := Lower.execution hBindings hMachine hCall'
  obtain ⟨least, hUnique⟩ := hReturn.unique_of_boundary
    (Lower.lowerEncode_returnBoundary hMachine hBindings hCall')
  refine ⟨least, final, hUnique, ?_⟩
  simpa only [hLength, ← Lower.encode_eq_encodedBytes] using hFinal

 theorem upper_correct
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {input : ByteArray} {outputCapacity : Nat}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall base16ctUpperEncodeStr initial input outputCapacity
      (2 * input.size) (2 * input.size ≤ outputCapacity)) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      if 2 * input.size ≤ outputCapacity then
        SuccessfulStatus final ∧
        MemoryWriteFrame initial final
          #v[outputRegion initial (2 * input.size), lengthOutputRegion initial,
            Stack.region initial base16ctUpperEncodeStr.minStackBytes] ∧
        readOutput initial final (2 * input.size) = .ok (Base16.upperEncoder input) ∧
        readLengthOutput initial final = .ok (BitVec.ofNat 64 (2 * input.size))
      else
        FailureStatus final invalidLengthStatus ∧
        MemoryWriteFrame initial final
          #v[Stack.region initial base16ctUpperEncodeStr.minStackBytes] := by
  have hinput : input.data.toList.toByteArray = input := by
    apply ByteArray.ext
    simp only [List.data_toByteArray, Array.toArray_toList]
  let c : Upper.CallContext := ⟨initial, input.data.toList, outputCapacity, by
    simpa only [hinput, Array.length_toList, ByteArray.size] using hCall⟩
  have hsize : c.input.length = input.size := by
    simp only [c, Array.length_toList]
    rfl
  have hencodedLength : c.encoded.length = 2 * input.size := by
    exact (Upper.encode_length c.input).trans (congrArg (fun n : Nat => 2 * n) hsize)
  have hencoded : c.encoded.toByteArray = Base16.upperEncoder input := by
    apply ByteArray.ext
    simp only [Upper.CallContext.encoded, c, hinput, List.data_toByteArray,
      Array.toArray_toList, Base16.upperEncoder]
  have hEntry := Upper.entryReady bindings hBindings hMachine hCall.programLoaded
  obtain ⟨s, hPrologue, hs, he⟩ := Upper.prologue_run c hEntry.ready hEntry.code
  obtain ⟨calleeFuel, t, hCallee, ht, htExit⟩ := Upper.callee_run c hs he
  obtain ⟨returnFuel, final, hReturn, hReady, hAgree, hRbx, hResult⟩ :=
    Upper.epilogue_run c ht htExit
  have hRun := hPrologue.returns (hCallee.returns hReturn)
  obtain ⟨fuel, hUnique⟩ := hRun.unique_of_boundary
    (Upper.nearReturn64Boundary_of_valid hEntry.ready hCall.stack)
  obtain ⟨hSupported, hDecodable, hSaved, hDirection⟩ :=
    Upper.encoder_final_state c hMachine hBindings hReady hAgree hRbx
  have hFrame := Upper.encoder_final_memoryWriteFrame c hAgree
  refine ⟨fuel, final, hUnique, hSupported, hDecodable, hSaved, hDirection, ?_⟩
  rw [hsize, show c.capacity = outputCapacity from rfl] at hFrame hResult
  by_cases hcap : 2 * input.size ≤ outputCapacity
  · simp only [ite_eq_left hcap] at hResult hFrame ⊢
    refine ⟨hResult.1, hFrame, ?_, hResult.2.2⟩
    simpa only [hencodedLength, hencoded] using hResult.2.1
  · simp only [ite_eq_right hcap] at hResult hFrame ⊢
    exact ⟨hResult, hFrame⟩

end Base16ct.Proofs.EncodeStr
