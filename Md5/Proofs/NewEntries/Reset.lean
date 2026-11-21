import Md5.Proofs.NewEntries.Reset.SecondPass
import Md5.Proofs.NewEntries.Reset.Finish
import Md5.Proofs.Streaming.ResetCounter
import Md5.Proofs.Buffered.Update.ResetFirst
import Md5.Proofs.Buffered.Update.ResetSecond
import Md5.Proofs.Buffered.Finalize.Streams.ResetSecond

namespace Md5.Statements

open Standards.RFC Md5.Spec Md5.Spec.Program Md5.Proofs Md5.Proofs.Streaming Prelude X86 X86Proofs

theorem md5_update_reset_slices_writes_second_message_digest
    {initial : Machine.RamState} {inputs : Array Slices.Input} {first : Nat}
    (bindings : Machine.Bindings)
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall :
      ResetThenDigest.ValidCall ResetThenDigest.updateResetSlices bindings initial inputs first) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution (bindings := bindings) initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[ResetThenDigest.outputRegion ResetThenDigest.updateResetSlices initial,
          Stack.region initial ResetThenDigest.updateResetSlices.minStackBytes] ∧
      ResetThenDigest.readOutput ResetThenDigest.updateResetSlices initial final =
        .ok (MD5.messageDigest (MD5.bitsOfBytes (Slices.secondMessage inputs first))) := by
  let := bindings
  have hEntry := entryReady bindings hBindings hMachine hCall.programLoaded
  have hBoundary := nearReturn64Boundary_eq initial hEntry.ready.dataReady
    hMachine.integer.ss (stack_return_readable hCall.stackAvailable)
  obtain ⟨boundary, hReturn, _, hOutside⟩ := hCall.returnAddress
  have hEq : boundary = returnBoundary initial := Except.ok.inj (hReturn.symm.trans hBoundary)
  subst boundary
  have firstOperations : LoopOperations .resetDiscardFirst (returnBoundary initial) := {
    update := fun _ _ _ hp ↦ Buffered.update_resetDiscardFirst hp
    counter := fun _ _ _ hr hc hp hi hn hlt hb _ ↦
      register_loop_counter .resetDiscardFirst (by decide) hOutside hr hc hp hi hn hlt hb
  }
  have secondOperations : LoopOperations .resetDiscardSecond (returnBoundary initial) := {
    update := fun _ _ _ hp ↦ Buffered.update_resetDiscardSecond hp
    counter := fun _ _ _ hr hc hp hi hn hlt hb hRead ↦
      stack_loop_counter .resetDiscardSecond (by simp) hOutside hr hc hp hi hn hlt hb hRead
  }
  obtain ⟨n, s, hFirstRun, hFirst⟩ := NewEntries.Reset.first_pass firstOperations
    hEntry.ready hEntry.code hMachine.sse hBindings.stringStride hCall hOutside
  obtain ⟨m, t, hSecondRun, hSecond, hRip⟩ := NewEntries.Reset.second_pass secondOperations
    hFirst hCall hBindings.stringStride hOutside
  obtain ⟨fuel, final, hReturns, hReady, hSse, hFrame, hBytes, hCallee, hDf⟩ :=
    NewEntries.Reset.finish (hFirstRun.trans hSecondRun) hSecond hRip
      (fun _ _ hp ↦ Buffered.Finalize.resetDiscardSecond_finalize hp)
      hEntry.ready hBindings.stringStride hCall hOutside
  obtain ⟨least, hUnique⟩ := hReturns.unique_of_boundary hBoundary
  refine ⟨least, final, hUnique, ⟨hReady.cpu, hSse, hReady.memory, hReady.ready⟩,
    machineRamUnitStrideDecodable_of_ready hReady hBindings.stringStride,
    hCallee, hDf, hFrame, ?_⟩
  exact readVector_of_hasBytes hBytes

end Md5.Statements
