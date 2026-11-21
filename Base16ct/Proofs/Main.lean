import Base16ct.Spec
import Base16ct.Proofs.EncodeStr
import Base16ct.Proofs.Common.EncodedLenSummary
import Base16ct.Proofs.Common.DecodedLenSummary
import Base16ct.Proofs.Common.DecodedLenExecution

namespace Base16ct.Statements

open Base16ct.Spec Base16ct.Spec.Program Prelude X86 X86.UserProcess X86Proofs
open Base16ct.Proofs.Common

theorem base16ct_lower_encode_str_writes_lowercase_hex_or_rejects_short_buffer
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
  exact Base16ct.Proofs.EncodeStr.lower_correct hBindings hMachine hCall

theorem base16ct_upper_encode_str_writes_uppercase_hex_or_rejects_short_buffer
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
  exact Base16ct.Proofs.EncodeStr.upper_correct hBindings hMachine hCall

theorem base16ct_decoded_len_writes_half_length_or_rejects_odd_length
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {byteLength : Nat}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidLengthCall base16ctDecodedLen initial byteLength (byteLength % 2 = 0)) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      match Base16.decodedLength byteLength with
      | some length =>
        SuccessfulStatus final ∧
        MemoryWriteFrame initial final
          #v[lengthOutputRegion initial, Stack.region initial base16ctDecodedLen.minStackBytes] ∧
        readLengthOutput initial final = .ok (BitVec.ofNat 64 length)
      | none =>
        FailureStatus final invalidLengthStatus ∧
        MemoryWriteFrame initial final
          #v[Stack.region initial base16ctDecodedLen.minStackBytes] := by
  by_cases hEven : byteLength % 2 = 0
  · obtain ⟨phase, hAdvances, hReady, hCode, hRip, hAgree, hFrame, hCallee, hDirection,
        hStatus, hValue⟩ := decoded_len_even_trace hBindings hMachine hCall hEven
    have hStackPtr : stackPtr phase = stackPtr initial := by
      change phase.regValue .rsp = initial.regValue .rsp
      exact hAgree.read (r := 4) (n := 64) (by simp)
    have hReturnBytes : ∀ i < 8,
        phase.external[stackPtr initial + BitVec.ofNat 64 i]? =
          initial.external[stackPtr initial + BitVec.ofNat 64 i]? := by
      intro i hi
      rw [hAgree.memory]
      intro c hc hcov
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · simp [Component.Covers] at hcov
      · simp [Component.Covers] at hcov
      · simp [Component.Covers] at hcov
      · obtain ⟨j, hj, heq⟩ := hcov
        have hLen0 := hCall.lengthOutputInMemoryIfLengthWritten hEven
        have hLen := Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.region_offset_contains
          hLen0.1 (i := j) hj
        obtain ⟨hs, he⟩ := Base16ct.Proofs.Copied.Md5.Proofs.Block.stack_subrange_bounds
          hCall.stack (used := 0) (by omega)
        have hStack := Base16ct.Proofs.Base16ctUpperEncodeCorrect.contains_offset_of_subrange
          hCall.stack.1 hs he i hi
        have hStack' : (Stack.region initial base16ctDecodedLen.minStackBytes).Contains
            (stackPtr initial + BitVec.ofNat 64 i).toNat := by
          simpa only [BitVec.sub_zero] using hStack
        have hLen' : (lengthOutputRegion initial).Contains
            (initial.regValue .rdx + BitVec.ofNat 64 j).toNat := by
          simpa [lengthOutputRegion, registerRegion] using hLen
        rw [heq] at hStack'
        exact (hCall.separation.2 hEven).1 _ hLen' hStack'
      · simp [Component.Covers] at hcov
    obtain ⟨least, final, hUnique, hSupported, hBindingsFinal, hCalleeFinal, hDirectionFinal,
        hFrameFinal, hAgreeFinal⟩ :=
      decoded_len_ret_finish hBindings hMachine hCall hAdvances hReady hCode hRip hAgree
        hStackPtr hReturnBytes hFrame hCallee hDirection
    have hReadableInitial : MemReadable initial (initial.regValue .rdx) 8 := by
      have hOut := hCall.lengthOutputInMemoryIfLengthWritten hEven
      apply Base16ct.Proofs.Base16ctUpperDecodeCorrect.regionReadable hOut.1 hOut.2
      · simp [lengthOutputRegion, registerRegion]
      · simp [lengthOutputRegion, registerRegion]
    have hReadableFinal : MemReadable final (initial.regValue .rdx) 8 := by
      refine ⟨hReadableInitial.low, ?_⟩
      intro i hi
      exact hAgreeFinal.grow _ (hAgree.grow _ (hReadableInitial.mem i hi))
    have hReadFinal :
        (Operand.mem (initial.regValue .rdx) : Operand 64).read final =
          (Operand.mem (initial.regValue .rdx) : Operand 64).read phase := by
      apply memLoad_congr
      intro i hi
      change (final.external[initial.regValue .rdx + BitVec.ofNat 64 i]?).getD 0 =
        (phase.external[initial.regValue .rdx + BitVec.ofNat 64 i]?).getD 0
      have hNoMem : ∀ (c : Component), c ∈ [.reg 4, .rip] →
          ¬ c.Covers (initial.regValue .rdx + BitVec.ofNat 64 i) := by
        intro c hc hcov
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl <;> simp [Component.Covers] at hcov
      rw [hAgreeFinal.byte hNoMem]
    have hLength := Base16ct.Proofs.readLengthOutput_of_operand_read hReadableFinal
      (hReadFinal.trans hValue)
    have hStatusFinal : final.regValue .rax = 0 := by
      exact hAgreeFinal.read (r := 0) (n := 64) (by simp) |>.trans hStatus
    have hSuccessful : SuccessfulStatus final := by
      simpa [SuccessfulStatus, AddrMode.reg64, State.regValue, Operand.read, gprIndex,
        Syntax.Reg.fin] using congrArg (fun x : BitVec 64 => x.setWidth 32) hStatusFinal
    have hDecoded : Base16.decodedLength byteLength = some (byteLength / 2) := by
      simp [Base16.decodedLength, hEven]
    rw [hDecoded]
    exact ⟨least, final, hUnique, hSupported, hBindingsFinal, hCalleeFinal, hDirectionFinal,
      hSuccessful, hFrameFinal, hLength⟩
  · have hOdd : byteLength % 2 ≠ 0 := hEven
    obtain ⟨phase, hAdvances, hReady, hCode, hRip, hAgree, hFrame, hCallee, hDirection,
        hStatus⟩ := decoded_len_odd_trace hBindings hMachine hCall hOdd
    have hStackPtr : stackPtr phase = stackPtr initial := by
      change phase.regValue .rsp = initial.regValue .rsp
      exact hAgree.read (r := 4) (n := 64) (by simp)
    have hReturnBytes : ∀ i < 8,
        phase.external[stackPtr initial + BitVec.ofNat 64 i]? =
          initial.external[stackPtr initial + BitVec.ofNat 64 i]? := by
      intro i hi
      rw [hAgree.memory]
      intro c hc hcov
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      all_goals simp [Component.Covers] at hcov
    have hFrameStack : MemoryWriteFrame initial phase
        #v[Stack.region initial base16ctDecodedLen.minStackBytes] := by
      apply hAgree.memoryWriteFrame
      intro c hc x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      all_goals exact False.elim (by simp [Component.Covers] at hx)
    obtain ⟨least, final, hUnique, hSupported, hBindingsFinal, hCalleeFinal, hDirectionFinal,
        hFrameFinal, hAgreeFinal⟩ :=
      decoded_len_ret_finish hBindings hMachine hCall hAdvances hReady hCode hRip hAgree
        hStackPtr hReturnBytes hFrameStack hCallee hDirection
    have hStatusFinal : final.regValue .rax = BitVec.setWidth 64 invalidLengthStatus := by
      exact hAgreeFinal.read (r := 0) (n := 64) (by simp) |>.trans hStatus
    have hFailure : FailureStatus final invalidLengthStatus := by
      simpa [FailureStatus, invalidLengthStatus, AddrMode.reg64, State.regValue,
        Operand.read, gprIndex, Syntax.Reg.fin] using
        congrArg (fun x : BitVec 64 => x.setWidth 32) hStatusFinal
    have hDecoded : Base16.decodedLength byteLength = none := by
      simp [Base16.decodedLength, hOdd]
    rw [hDecoded]
    refine ⟨least, final, hUnique, hSupported, hBindingsFinal, hCalleeFinal, hDirectionFinal, hFailure, ?_⟩
    exact hFrameFinal

theorem base16ct_encoded_len_writes_twice_length
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {byteLength : Nat}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidLengthCall base16ctEncodedLen initial byteLength True) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[lengthOutputRegion initial, Stack.region initial base16ctEncodedLen.minStackBytes] ∧
      readLengthOutput initial final = .ok (BitVec.ofNat 64 (2 * byteLength)) := by
  obtain ⟨s, u, hSummary⟩ := encoded_len_routine_summary hBindings hMachine hCall
  have hCode : CodeIn (codeRange (0x100026 : BitVec 64) [0xc3]) u := by
    have h := Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.program_text_slice
      hSummary.code.phase 0x26 1 (by decide +kernel)
    have hb : Extracted.textBytes.toListFrom 0x26 1 = [0xc3] := by
      decide +kernel
    simpa only [hb,
      show Extracted.textAddress + BitVec.ofNat 64 0x26 = (0x100026 : BitVec 64) by
        decide +kernel] using h
  have hPre : RetPre 0x100026 u := by
    refine ⟨⟨hSummary.code.phaseRip, hSummary.continuation.returnSlot⟩, ?_⟩
    rw [hSummary.continuation.returnTop]
    simpa [userAddressLimit] using hSummary.continuation.returnAddress.1
  obtain ⟨final, hReturn, hReadyFinal, hAgreeFinal⟩ :=
    encoded_len_ret_step hSummary.continuation.ready hCode hPre
      hSummary.continuation.returnTop hSummary.continuation.stackPointer
  have hRun : Returns (returnBoundary initial) (2 + 1) initial final :=
    hSummary.advances.returns hReturn
  have hEntry := Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.entryReady
    hBindings hMachine hCall.programLoaded
  have hNear := nearReturn64Boundary_eq initial hEntry.ready.dataReady hEntry.ready.cpu.ss
    (Base16ct.Proofs.Copied.Md5.Proofs.stack_return_readable hCall.stack)
  obtain ⟨fuel, hUnique⟩ := hRun.unique_of_boundary hNear
  have hSseU : SupportedSSE bindings.processor u :=
    SupportedSSE.of_agreesExcept hSummary.agrees hMachine.sse
  have hSupported : SupportedIntegerMachineState bindings.processor final :=
    Base16ct.Proofs.Base16ctUpperEncodeCorrect.supportedIntegerMachineState_of_ready
      hReadyFinal hAgreeFinal hSseU
  have hControls : SameControls initial final :=
    SameControls.of_fixedPart (hAgreeFinal.rest.trans hSummary.agrees.rest)
  have hBindingsFinal : MachineRamUnitStrideDecodable bindings final := by
    refine ⟨smrrUnblocked_of_sameControls hControls hBindings.smrr,
      writeBackMemoryType_of_sameControls hControls hBindings.memoryType,
      hBindings.stringStride, ?_⟩
    obtain ⟨enabled, henabled⟩ := hBindings.leadingZeroCount
    exact ⟨enabled, reportsCPUFeature_of_sameControls hControls henabled⟩
  have hCalleeRet : CalleeSavedRegistersUnchanged u final := by
    intro register hreg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hreg
    rcases hreg with rfl | rfl | rfl | rfl | rfl | rfl
    · change final.GPR[gprIndex (3 : BitVec 5)] = u.GPR[gprIndex (3 : BitVec 5)]
      simpa only [Component.Agrees] using hAgreeFinal.agree (.reg 3) (by simp) rfl
    · change final.GPR[gprIndex (5 : BitVec 5)] = u.GPR[gprIndex (5 : BitVec 5)]
      simpa only [Component.Agrees] using hAgreeFinal.agree (.reg 5) (by simp) rfl
    · change final.GPR[gprIndex (12 : BitVec 5)] = u.GPR[gprIndex (12 : BitVec 5)]
      simpa only [Component.Agrees] using hAgreeFinal.agree (.reg 12) (by simp) rfl
    · change final.GPR[gprIndex (13 : BitVec 5)] = u.GPR[gprIndex (13 : BitVec 5)]
      simpa only [Component.Agrees] using hAgreeFinal.agree (.reg 13) (by simp) rfl
    · change final.GPR[gprIndex (14 : BitVec 5)] = u.GPR[gprIndex (14 : BitVec 5)]
      simpa only [Component.Agrees] using hAgreeFinal.agree (.reg 14) (by simp) rfl
    · change final.GPR[gprIndex (15 : BitVec 5)] = u.GPR[gprIndex (15 : BitVec 5)]
      simpa only [Component.Agrees] using hAgreeFinal.agree (.reg 15) (by simp) rfl
  have hCallee : CalleeSavedRegistersUnchanged initial final := by
    intro register hreg
    exact (hCalleeRet register hreg).trans (hSummary.calleeSaved register hreg)
  have hDirection : DirectionFlagUnset final :=
    hAgreeFinal.directionFlagClear (by simp) hSummary.direction
  have hFrameRet : MemoryWriteFrame u final
      #v[lengthOutputRegion initial, Stack.region initial base16ctEncodedLen.minStackBytes] := by
    apply hAgreeFinal.memoryWriteFrame
    intro c hc x hcov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact False.elim (by simp [Component.Covers] at hcov)
    · exact False.elim (by simp [Component.Covers] at hcov)
  have hFrame := memoryWriteFrame_trans hSummary.writes hFrameRet
  have hReadableInitial : MemReadable initial (initial.regValue .rdx) 8 := by
    have hOut := hCall.lengthOutputInMemoryIfLengthWritten (by trivial)
    apply Base16ct.Proofs.Base16ctUpperDecodeCorrect.regionReadable hOut.1 hOut.2
    · simp [lengthOutputRegion, registerRegion]
    · simp [lengthOutputRegion, registerRegion]
  have hReadableFinal : MemReadable final (initial.regValue .rdx) 8 := by
    refine ⟨hReadableInitial.low, ?_⟩
    intro i hi
    exact hAgreeFinal.grow _ (hSummary.agrees.grow _ (hReadableInitial.mem i hi))
  have hReadFinal :
      (Operand.mem (initial.regValue .rdx) : Operand 64).read final =
        (Operand.mem (initial.regValue .rdx) : Operand 64).read u := by
    apply memLoad_congr
    intro i hi
    change (final.external[initial.regValue .rdx + BitVec.ofNat 64 i]?).getD 0 =
      (u.external[initial.regValue .rdx + BitVec.ofNat 64 i]?).getD 0
    have hNoMem : ∀ (c : Component), c ∈ [.reg 4, .rip] →
        ¬ c.Covers (initial.regValue .rdx + BitVec.ofNat 64 i) := by
      intro c hc hcov
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> simp [Component.Covers] at hcov
    rw [hAgreeFinal.byte hNoMem]
  have hLength := Base16ct.Proofs.readLengthOutput_of_operand_read hReadableFinal
    (hReadFinal.trans hSummary.value)
  refine ⟨fuel, final, hUnique, hSupported, hBindingsFinal, hCallee, hDirection, hFrame, hLength⟩

end Base16ct.Statements
