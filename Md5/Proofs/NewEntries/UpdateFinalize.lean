import Md5.Proofs.NewEntries.UpdateFinalize.Run
import Md5.Proofs.Buffered.Update.Slices
import Md5.Proofs.Buffered.Finalize

namespace Md5.Statements

open Standards.RFC Md5.Spec Md5.Spec.Program Md5.Proofs Md5.Proofs.Streaming Prelude X86 X86Proofs

theorem md5_update_finalize_into_writes_message_digest
    {initial : Machine.RamState} {inputs : Array Slices.Input}
    (bindings : Machine.Bindings)
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : OneMessage.ValidCall OneMessage.updateFinalizeInto bindings initial inputs) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution (bindings := bindings) initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[OneMessage.outputRegion OneMessage.updateFinalizeInto initial,
          Stack.region initial OneMessage.updateFinalizeInto.minStackBytes] ∧
      OneMessage.readOutput OneMessage.updateFinalizeInto initial final =
        .ok (MD5.messageDigest (MD5.bitsOfBytes (Slices.message inputs))) := by
  let := bindings
  have hEntry := entryReady bindings hBindings hMachine hCall.programLoaded
  have hBoundary := nearReturn64Boundary_eq initial hEntry.ready.dataReady
    hMachine.integer.ss (stack_return_readable hCall.stackAvailable)
  obtain ⟨boundary, hReturn, _, hOutside⟩ := hCall.returnAddress
  have hEq : boundary = returnBoundary initial := Except.ok.inj (hReturn.symm.trans hBoundary)
  subst boundary
  have operations : LoopOperations .updateFinalizeInto (returnBoundary initial) := {
    update := fun _ _ _ hp ↦ Buffered.update_finalizeInto hp
    counter := fun _ _ _ hr hc hp hi hn hlt hb _ ↦
      register_loop_counter .updateFinalizeInto (by decide) hOutside hr hc hp hi hn hlt hb
  }
  obtain ⟨fuel, final, hReturns, hReady, hSse, hFrame, hBytes, hCallee, hDf⟩ :=
    NewEntries.UpdateFinalize.slices_run operations (fun _ _ hp ↦ Buffered.Finalize.updateFinalizeInto_finalize hp)
      hEntry.ready hEntry.code hMachine.sse hBindings.stringStride hCall hOutside
  obtain ⟨least, hUnique⟩ := hReturns.unique_of_boundary hBoundary
  refine ⟨least, final, hUnique, ⟨hReady.cpu, hSse, hReady.memory, hReady.ready⟩,
    machineRamUnitStrideDecodable_of_ready hReady hBindings.stringStride,
    hCallee, hDf, hFrame, ?_⟩
  exact readVector_of_hasBytes hBytes

end Md5.Statements
