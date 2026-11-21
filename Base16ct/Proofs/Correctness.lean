import Base16ct.Proofs.Base16ctLowerEncodeCorrect.Boundary
import Base16ct.Proofs.Base16ctLowerEncodeCorrect.Machine.Execution
import Base16ct.Spec
import Base16ct.Proofs.Base16ctUpperEncodeCorrect.Prologue
import Base16ct.Proofs.Base16ctUpperEncodeCorrect.Callee
import Base16ct.Proofs.Base16ctUpperEncodeCorrect.Epilogue
import Base16ct.Proofs.Base16ctUpperDecodeCorrect.Control
import Base16ct.Proofs.Base16ctLowerDecodeCorrect.ModelBridge
import Base16ct.Proofs.Base16ctUpperDecodeCorrect.Decoding.ModelBridge
import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine

namespace Base16ct.Statements

open Base16ct.Spec Base16ct.Spec.Program Prelude X86
open Base16ct.Proofs.LowerEncode X86Proofs

theorem base16ct_lower_encode_writes_lowercase_hex_or_rejects_short_buffer
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {input : ByteArray} {outputCapacity : Nat}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall base16ctLowerEncode initial input outputCapacity
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
            Stack.region initial base16ctLowerEncode.minStackBytes] ∧
        readOutput initial final (2 * input.size) = .ok (Base16.lowerEncoder input) ∧
        readLengthOutput initial final = .ok (BitVec.ofNat 64 (2 * input.size))
      else
        FailureStatus final invalidLengthStatus ∧
        MemoryWriteFrame initial final
          #v[Stack.region initial base16ctLowerEncode.minStackBytes] := by
  have hBytes : input.data.toList.toByteArray = input := by
    apply ByteArray.ext
    simp only [List.data_toByteArray, Array.toArray_toList]
  have hLength : input.data.toList.length = input.size := Array.length_toList
  have hCall' : ValidCall base16ctLowerEncode initial input.data.toList.toByteArray
      outputCapacity (2 * input.data.toList.length) (2 * input.data.toList.length ≤ outputCapacity) := by
    simpa only [hBytes, hLength] using hCall
  obtain ⟨fuel, final, hReturn, hFinal⟩ := execution hBindings hMachine hCall'
  obtain ⟨least, hUnique⟩ := hReturn.unique_of_boundary
    (lowerEncode_returnBoundary hMachine hBindings hCall')
  refine ⟨least, final, hUnique, ?_⟩
  simpa only [hLength, ← encode_eq_encodedBytes] using hFinal

end Base16ct.Statements

namespace Base16ct.Statements
open Base16ct.Spec Base16ct.Spec.Program Prelude X86
open X86Proofs Base16ct.Proofs.Base16ctUpperEncodeCorrect

theorem base16ct_upper_encode_writes_uppercase_hex_or_rejects_short_buffer
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {input : ByteArray} {outputCapacity : Nat}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall base16ctUpperEncode initial input outputCapacity
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
            Stack.region initial base16ctUpperEncode.minStackBytes] ∧
        readOutput initial final (2 * input.size) = .ok (Base16.upperEncoder input) ∧
        readLengthOutput initial final = .ok (BitVec.ofNat 64 (2 * input.size))
      else
        FailureStatus final invalidLengthStatus ∧
        MemoryWriteFrame initial final
          #v[Stack.region initial base16ctUpperEncode.minStackBytes] := by
  have hinput : input.data.toList.toByteArray = input := by
    apply ByteArray.ext
    simp only [List.data_toByteArray, Array.toArray_toList]
  let c : CallContext := ⟨initial, input.data.toList, outputCapacity, by
    simpa only [hinput, Array.length_toList, ByteArray.size] using hCall⟩
  have hsize : c.input.length = input.size := by
    simp only [c, Array.length_toList]
    rfl
  have hencodedLength : c.encoded.length = 2 * input.size := by
    exact (encode_length c.input).trans (congrArg (fun n : Nat => 2 * n) hsize)
  have hencoded : c.encoded.toByteArray = Base16.upperEncoder input := by
    apply ByteArray.ext
    simp only [CallContext.encoded, c, hinput, List.data_toByteArray, Array.toArray_toList,
      Base16.upperEncoder]
  have hEntry := entryReady bindings hBindings hMachine hCall.programLoaded
  obtain ⟨s, hPrologue, hs, he⟩ := prologue_run c hEntry.ready hEntry.code
  obtain ⟨calleeFuel, t, hCallee, ht, htExit⟩ := callee_run c hs he
  obtain ⟨returnFuel, final, hReturn, hReady, hAgree, hRbx, hResult⟩ := epilogue_run c ht htExit
  have hRun := hPrologue.returns (hCallee.returns hReturn)
  obtain ⟨fuel, hUnique⟩ := hRun.unique_of_boundary
    (nearReturn64Boundary_of_valid hEntry.ready hCall.stack)
  obtain ⟨hSupported, hDecodable, hSaved, hDirection⟩ :=
    encoder_final_state c hMachine hBindings hReady hAgree hRbx
  have hFrame := encoder_final_memoryWriteFrame c hAgree
  refine ⟨fuel, final, hUnique, hSupported, hDecodable, hSaved, hDirection, ?_⟩
  rw [hsize, show c.capacity = outputCapacity from rfl] at hFrame hResult
  by_cases hcap : 2 * input.size ≤ outputCapacity
  · simp only [ite_eq_left hcap] at hResult hFrame ⊢
    refine ⟨hResult.1, hFrame, ?_, hResult.2.2⟩
    simpa only [hencodedLength, hencoded] using hResult.2.1
  · simp only [ite_eq_right hcap] at hResult hFrame ⊢
    exact ⟨hResult, hFrame⟩

end Base16ct.Statements

namespace Base16ct.Statements

open Base16ct.Spec Prelude X86
open Base16ct.Spec.Program
open Base16ct.Proofs.Base16ctUpperDecodeCorrect hiding ValidCall readOutput
open Base16ct.Proofs.Base16ctLowerDecodeCorrect

theorem base16ct_lower_decode_writes_decoded_bytes_or_rejects
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {input : ByteArray} {outputCapacity : Nat}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall base16ctLowerDecode initial input outputCapacity
      (input.size / 2)
      (∃ output, Base16.decodeInto Base16.lowerDecoder input outputCapacity = .ok output)) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      match Base16.decodeInto Base16.lowerDecoder input outputCapacity with
      | .ok output =>
        SuccessfulStatus final ∧
        MemoryWriteFrame initial final
          #v[outputRegion initial output.size, lengthOutputRegion initial,
            Stack.region initial base16ctLowerDecode.minStackBytes] ∧
        readOutput initial final output.size = .ok output ∧
        readLengthOutput initial final = .ok (BitVec.ofNat 64 output.size)
      | .error .invalidLength =>
        FailureStatus final invalidLengthStatus ∧
        MemoryWriteFrame initial final #v[Stack.region initial base16ctLowerDecode.minStackBytes]
      | .error .invalidEncoding =>
        FailureStatus final invalidEncodingStatus ∧
        MemoryWriteFrame initial final
          #v[outputRegion initial (input.size / 2),
            Stack.region initial base16ctLowerDecode.minStackBytes] := by
  let xs := input.data.toList
  have hin : xs.toByteArray = input := by
    apply ByteArray.ext
    simp only [xs, List.data_toByteArray, Array.toArray_toList]
  have hmodel := decodeInto_eq_pair Base16.lowerDecoder [.lower] xs outputCapacity
    (lowerDecoder_eq_model xs)
  rw [hin] at hmodel
  have hok : (∃ output, Base16.decodeInto Base16.lowerDecoder input outputCapacity = .ok output) ↔
      (∃ output, pairDecodeResult [.lower] xs outputCapacity = .ok output) := by
    rw [hmodel]
    cases pairDecodeResult [.lower] xs outputCapacity <;> simp [Except.map]
  have hsize : xs.length = input.size := Array.length_toList
  have hc : Base16ct.Proofs.Base16ctUpperDecodeCorrect.ValidCall (decodeRoutine .lower)
      initial xs outputCapacity
      (∃ output, pairDecodeResult [.lower] xs outputCapacity = .ok output) := by
    simpa only [Base16ct.Proofs.Base16ctUpperDecodeCorrect.ValidCall, hin, hsize, ← hok,
      decodeRoutine, decodeAddress, base16ctLowerDecode, Extracted.lower_decodeStackBytes, Option.get_some] using hCall
  obtain ⟨fuel, final, he, hs, hb, hsaved, hdf, hr⟩ :=
    decode_correct .lower hBindings hMachine hc
  refine ⟨fuel, final, he, hs, hb, hsaved, hdf, ?_⟩
  rw [hmodel]
  cases hresult : pairDecodeResult [.lower] xs outputCapacity with
  | ok output =>
    simpa only [hresult, Except.map, List.size_toByteArray, decodeRoutine, decodeAddress,
      base16ctLowerDecode, Extracted.lower_decodeStackBytes, Option.get_some] using hr
  | error error =>
    cases error <;>
      simpa only [hresult, Except.map, decodeRoutine, decodeAddress, base16ctLowerDecode, Extracted.lower_decodeStackBytes, Option.get_some,
        xs, Array.length_toList, ByteArray.size] using hr

end Base16ct.Statements

namespace Base16ct.Statements

open Base16ct.Spec Prelude X86
open Base16ct.Spec.Program
open Base16ct.Proofs.Base16ctUpperDecodeCorrect hiding ValidCall readOutput
open Base16ct.Proofs.Base16ctLowerDecodeCorrect

theorem base16ct_upper_decode_writes_decoded_bytes_or_rejects
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {input : ByteArray} {outputCapacity : Nat}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall base16ctUpperDecode initial input outputCapacity
      (input.size / 2)
      (∃ output, Base16.decodeInto Base16.upperDecoder input outputCapacity = .ok output)) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      match Base16.decodeInto Base16.upperDecoder input outputCapacity with
      | .ok output =>
        SuccessfulStatus final ∧
        MemoryWriteFrame initial final
          #v[outputRegion initial output.size, lengthOutputRegion initial,
            Stack.region initial base16ctUpperDecode.minStackBytes] ∧
        readOutput initial final output.size = .ok output ∧
        readLengthOutput initial final = .ok (BitVec.ofNat 64 output.size)
      | .error .invalidLength =>
        FailureStatus final invalidLengthStatus ∧
        MemoryWriteFrame initial final #v[Stack.region initial base16ctUpperDecode.minStackBytes]
      | .error .invalidEncoding =>
        FailureStatus final invalidEncodingStatus ∧
        MemoryWriteFrame initial final
          #v[outputRegion initial (input.size / 2),
            Stack.region initial base16ctUpperDecode.minStackBytes] := by
  let xs := input.data.toList
  have hin : xs.toByteArray = input := by
    apply ByteArray.ext
    simp only [xs, List.data_toByteArray, Array.toArray_toList]
  have hmodel := decodeInto_eq_pair Base16.upperDecoder [.upper] xs outputCapacity
    (upperDecoder_eq_model xs)
  rw [hin] at hmodel
  have hok : (∃ output, Base16.decodeInto Base16.upperDecoder input outputCapacity = .ok output) ↔
      (∃ output, pairDecodeResult [.upper] xs outputCapacity = .ok output) := by
    rw [hmodel]
    cases pairDecodeResult [.upper] xs outputCapacity <;> simp [Except.map]
  have hsize : xs.length = input.size := Array.length_toList
  have hc : Base16ct.Proofs.Base16ctUpperDecodeCorrect.ValidCall (decodeRoutine .upper)
      initial xs outputCapacity
      (∃ output, pairDecodeResult [.upper] xs outputCapacity = .ok output) := by
    simpa only [Base16ct.Proofs.Base16ctUpperDecodeCorrect.ValidCall, hin, hsize, ← hok,
      decodeRoutine, decodeAddress, base16ctUpperDecode, Extracted.upper_decodeStackBytes, Option.get_some] using hCall
  obtain ⟨fuel, final, he, hs, hb, hsaved, hdf, hr⟩ :=
    decode_correct .upper hBindings hMachine hc
  refine ⟨fuel, final, he, hs, hb, hsaved, hdf, ?_⟩
  rw [hmodel]
  cases hresult : pairDecodeResult [.upper] xs outputCapacity with
  | ok output =>
    simpa only [hresult, Except.map, List.size_toByteArray, decodeRoutine, decodeAddress,
      base16ctUpperDecode, Extracted.upper_decodeStackBytes, Option.get_some] using hr
  | error error =>
    cases error <;>
      simpa only [hresult, Except.map, decodeRoutine, decodeAddress, base16ctUpperDecode, Extracted.upper_decodeStackBytes, Option.get_some,
        xs, Array.length_toList, ByteArray.size] using hr

end Base16ct.Statements

namespace Base16ct.Statements

open Base16ct.Spec Base16ct.Spec.Program Prelude X86

theorem base16ct_mixed_decode_writes_decoded_bytes_or_rejects
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {input : ByteArray} {outputCapacity : Nat}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall base16ctMixedDecode initial input outputCapacity
      (input.size / 2)
      (∃ output, Base16.decodeInto Base16.mixedDecoder input outputCapacity = .ok output)) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      match Base16.decodeInto Base16.mixedDecoder input outputCapacity with
      | .ok output =>
        SuccessfulStatus final ∧
        MemoryWriteFrame initial final
          #v[outputRegion initial output.size, lengthOutputRegion initial,
            Stack.region initial base16ctMixedDecode.minStackBytes] ∧
        readOutput initial final output.size = .ok output ∧
        readLengthOutput initial final = .ok (BitVec.ofNat 64 output.size)
      | .error .invalidLength =>
        FailureStatus final invalidLengthStatus ∧
        MemoryWriteFrame initial final #v[Stack.region initial base16ctMixedDecode.minStackBytes]
      | .error .invalidEncoding =>
        FailureStatus final invalidEncodingStatus ∧
        MemoryWriteFrame initial final
          #v[outputRegion initial (input.size / 2),
            Stack.region initial base16ctMixedDecode.minStackBytes] := by
  exact Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.mixed_decode_correct
    hBindings hMachine hCall

end Base16ct.Statements
