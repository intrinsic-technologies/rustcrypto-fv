import Md5.Proofs.Buffered.DigestPrepare
import Md5.Proofs.Buffered.DigestFinish
import Md5.Proofs.Buffered.Finalize

namespace Md5.Statements

open Md5.Spec Md5.Spec.Program Md5.Proofs Md5.Proofs.Buffered Prelude X86 X86Proofs

theorem md5_digest_writes_message_digest
    {initial : Machine.RamState} {input : ByteArray}
    (bindings : Machine.Bindings)
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : Digest.ValidCall bindings initial input) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution (bindings := bindings) initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[Digest.outputRegion initial, Stack.region initial Digest.minStackBytes] ∧
      Digest.readOutput initial final =
        .ok (Standards.RFC.MD5.messageDigest (Standards.RFC.MD5.bitsOfBytes input)) := by
  letI := bindings
  have hEntry := entryReady bindings hBindings hMachine hCall.programLoaded
  have hReadable := stack_return_readable hCall.stackAvailable
  have hBoundary := nearReturn64Boundary_eq initial hEntry.ready.dataReady
    hMachine.integer.ss hReadable
  obtain ⟨boundary, hBoundary', hLow, _⟩ := hCall.returnAddress
  have hEq : boundary = returnBoundary initial := Except.ok.inj (hBoundary'.symm.trans hBoundary)
  subst boundary
  obtain ⟨_, prepared, hPrepare, hp⟩ :=
    digest_prepare hEntry.ready hEntry.code hBindings.stringStride hCall
  obtain ⟨finalized, hq⟩ := Finalize.digest_finalize hp.pre
  obtain ⟨_, final, cs, hReturn, hReady, hAgrees, hFrame, hOutput, hCallee, hDf⟩ :=
    digest_finish hCall hp hq rfl hLow
  obtain ⟨least, hUnique⟩ := (hPrepare.returns hReturn).unique_of_boundary hBoundary
  exact ⟨least, final, hUnique,
    supportedIntegerMachineState_of_ready hReady hAgrees hMachine.sse,
    machineRamUnitStrideDecodable_of_ready hReady hBindings.stringStride,
    hCallee, hDf, hFrame, hOutput⟩

end Md5.Statements
