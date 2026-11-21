import Md5.Proofs.Streaming.ResetRun
import Md5.Proofs.Streaming.ResetCounter
import Md5.Proofs.Buffered.Update.ResetFirst
import Md5.Proofs.Buffered.Update.ResetSecond
import Md5.Proofs.Buffered.Finalize
import Md5.Proofs.Buffered.FinalizeReset

namespace Md5.Statements

open Standards.RFC Md5.Spec Md5.Spec.Program Md5.Proofs Md5.Proofs.Streaming Prelude X86 X86Proofs

theorem md5_digest_slices_reset_writes_both_message_digests
    {initial : Machine.RamState} {inputs : Array Slices.Input} {first : Nat}
    (bindings : Machine.Bindings)
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : TwoMessages.ValidCall TwoMessages.digestSlicesReset bindings initial inputs first) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution (bindings := bindings) initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[TwoMessages.outputRegion TwoMessages.digestSlicesReset initial,
          Stack.region initial TwoMessages.digestSlicesReset.minStackBytes] ∧
      TwoMessages.readOutput TwoMessages.digestSlicesReset initial final =
        .ok (MD5.messageDigest (MD5.bitsOfBytes (Slices.firstMessage inputs first)) ++
            MD5.messageDigest (MD5.bitsOfBytes (Slices.secondMessage inputs first))) := by
  letI := bindings
  have hEntry := entryReady bindings hBindings hMachine hCall.programLoaded
  have hBoundary := nearReturn64Boundary_eq initial hEntry.ready.dataReady
    hMachine.integer.ss (stack_return_readable hCall.stackAvailable)
  obtain ⟨boundary, hReturn, _, hOutside⟩ := hCall.returnAddress
  have hEq : boundary = returnBoundary initial := Except.ok.inj (hReturn.symm.trans hBoundary)
  subst boundary
  have firstOperations : LoopOperations .resetFirst (returnBoundary initial) := {
    update := fun _ _ _ hp ↦ Buffered.update_resetFirst hp
    counter := fun _ _ _ hr hc hp hi hn hlt hb _ ↦
      register_loop_counter .resetFirst (by decide) hOutside hr hc hp hi hn hlt hb
  }
  have secondOperations : LoopOperations .resetSecond (returnBoundary initial) := {
    update := fun _ _ _ hp ↦ Buffered.update_resetSecond hp
    counter := fun _ _ _ hr hc hp hi hn hlt hb hread ↦
      resetSecond_loop_counter hOutside hr hc hp hi hn hlt hb hread
  }
  obtain ⟨fuel, final, hReturns, hReady, hSse, hFrame, hBytes, hCallee, hDf⟩ :=
    reset_run firstOperations secondOperations
      (fun _ _ hp ↦ Buffered.FinalizeReset.run hp)
      (fun _ _ hp ↦ Buffered.Finalize.resetSecond_finalize hp)
      hEntry.ready hEntry.code hMachine.sse hBindings.stringStride hCall hOutside
  obtain ⟨least, hUnique⟩ := hReturns.unique_of_boundary hBoundary
  refine ⟨least, final, hUnique, ⟨hReady.cpu, hSse, hReady.memory, hReady.ready⟩,
    machineRamUnitStrideDecodable_of_ready hReady hBindings.stringStride,
    hCallee, hDf, hFrame, ?_⟩
  exact readVector_of_hasBytes hBytes

end Md5.Statements
