import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Setup
import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Output
import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Decoder
import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.Positive
import Base16ct.Proofs.Common.Output

namespace Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine

open Base16ct.Spec Base16ct.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem mixed_decode_correct
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {input : ByteArray} {outputCapacity : Nat}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall base16ctMixedDecode initial input outputCapacity (input.size / 2)
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
  have hModel := mixedDecodeResult_byteArray input outputCapacity
  have hLength (hFit : input.data.toList.length / 2 ≤ outputCapacity)
      (hSome : ∃ output, mixedDecodeList input.data.toList = some output) :
      ∃ output, Base16.decodeInto Base16.mixedDecoder input outputCapacity = .ok output := by
    obtain ⟨output, ho⟩ := hSome
    have hEven := mixedDecodeList_even ho
    refine ⟨output.toByteArray, ?_⟩
    rw [hModel, ite_eq_right (by omega), ho]
  have hInternal := mixed_internal_call hCall hLength
  have hEntry := entryReady hBindings hMachine hCall.programLoaded
  obtain ⟨fuel, final, hRun, hRip, hRsp, hReady, hCode,
      hFrame, hRbx, hRbp, hR14, hResult⟩ :=
    mixed_internal_run hInternal hEntry.ready hEntry.code
  obtain ⟨least, hUnique, hSupported, hBindingsF, hSaved, hDirection⟩ :=
    finish_call hBindings hMachine hCall hRun hReady hFrame hRbx hRbp hR14
  refine ⟨least, final, hUnique, hSupported, hBindingsF, hSaved, hDirection, ?_⟩
  rw [hModel]
  by_cases hInvalid : input.data.toList.length % 2 ≠ 0 ∨
      outputCapacity < input.data.toList.length / 2
  · simp only [hInvalid, ↓reduceIte] at hFrame hResult ⊢
    refine ⟨?_, mixedCallChanges_frame hCall (Nat.zero_le _) (by simp)
      hFrame (by simp) (by simp) (by simp)⟩
    change (final.regValue .rax).setWidth 32 = invalidLengthStatus
    rw [hResult]
    rfl
  · simp only [hInvalid, ↓reduceIte] at hFrame hResult ⊢
    cases hd : mixedDecodeList input.data.toList with
    | none =>
      simp only [hd, Option.isSome_none] at hFrame hResult
      refine ⟨?_, ?_⟩
      · change (final.regValue .rax).setWidth 32 = invalidEncodingStatus
        rw [hResult]
        rfl
      · simpa only [Array.length_toList, ← ByteArray.size_data] using
          mixedCallChanges_frame hCall (written := input.data.toList.length / 2)
            (by omega) (by simp) hFrame
            (regions := #v[outputRegion initial (input.size / 2),
              Stack.region initial base16ctMixedDecode.minStackBytes])
            (by simp) (by simp) (by simp)
    | some output =>
      simp only [hd, Option.isSome_some] at hFrame hResult
      have hsize := mixedDecodeList_length_div_two hd
      have hs := hLength (by omega) ⟨output, hd⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · change (final.regValue .rax).setWidth 32 = 0
        rw [hResult.1]
        rfl
      · have hf := mixedCallChanges_frame hCall (written := input.data.toList.length / 2)
          (by omega) (fun _ ↦ hs) hFrame
          (regions := #v[outputRegion initial output.length, lengthOutputRegion initial,
            Stack.region initial base16ctMixedDecode.minStackBytes])
          (by simp [hsize]) (by simp) (by simp)
        simpa only [List.size_toByteArray] using hf
      · simpa only [List.size_toByteArray] using readOutput_eq_of_bytes hResult.2.2
      · apply Base16ct.Proofs.readLengthOutput_of_operand_read
        · have hw := hInternal.result (by omega) ⟨output, hd⟩
          exact ⟨hw.low, fun i hi ↦ hFrame.grow _ (hw.bytes i hi)⟩
        · simpa only [List.size_toByteArray] using hResult.2.1

end Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine
