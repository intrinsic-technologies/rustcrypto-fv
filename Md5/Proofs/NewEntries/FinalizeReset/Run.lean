import Md5.Proofs.NewEntries.FinalizeReset.Absorb
import Md5.Proofs.NewEntries.FinalizeReset.Finish

namespace Md5.Proofs.NewEntries.FinalizeReset

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Buffered Streaming

theorem reset_run [bindings : Bindings] {initial : RamState}
    {inputs : Array Slices.Input} {first : Nat}
    (firstOperations : LoopOperations .finalizeResetFirst (returnBoundary initial))
    (secondOperations : LoopOperations .finalizeResetSecond (returnBoundary initial))
    (firstFinalize : ∀ message s, Buffered.FinalizeReset.Pre (returnBoundary initial) message s (variant := .direct) →
      ∃ t, Buffered.FinalizeReset.Post (returnBoundary initial) message s t (variant := .direct))
    (secondFinalize : ∀ message s, Finalize.Pre .finalizeResetSecond (returnBoundary initial) message s →
      ∃ t, Finalize.Post .finalizeResetSecond (returnBoundary initial) message s t)
    (hReady : ReadyToStep initial) (hCode : CodeIn Extracted.programImage initial)
    (hSse : SupportedSSE bindings.processor initial) (hStride : UnitStringStride bindings)
    (hCall : (TwoMessages.ValidCall TwoMessages.finalizeIntoResetSlices) bindings initial inputs first)
    (hOutside : ¬ InProgram (returnBoundary initial).rip) :
    ∃ fuel final, Returns (returnBoundary initial) fuel initial final ∧
      ReadyToStep final ∧ SupportedSSE bindings.processor final ∧
      MemoryWriteFrame initial final
        #v[(TwoMessages.outputRegion TwoMessages.finalizeIntoResetSlices) initial,
          Stack.region initial TwoMessages.finalizeIntoResetSlices.minStackBytes] ∧
      ((TwoMessages.outputRegion TwoMessages.finalizeIntoResetSlices) initial).HasBytes final.external
        ⟨(Standards.RFC.MD5.messageDigest
            (Standards.RFC.MD5.bitsOfBytes (Slices.message (inputs.extract 0 first))) ++
          Standards.RFC.MD5.messageDigest
            (Standards.RFC.MD5.bitsOfBytes (Slices.message (inputs.extract first inputs.size)))).toArray⟩ ∧
      CalleeSavedRegistersUnchanged initial final ∧ DirectionFlagUnset final := by
  obtain ⟨n, s, hRun, hs, hRip, hFirst⟩ := reset_absorb firstOperations secondOperations
    firstFinalize hReady hCode hSse hStride hCall hOutside
  obtain ⟨m, final, hReturn, hFinalReady, hFinalSse, hFrame, hOutput, hCallee, hDF⟩ :=
    reset_second_finish secondFinalize hReady hCall hs hStride hOutside hRip
      (by have := validInputs_message_extract_size_lt hCall.inputsInMemory first inputs.size; omega)
      hFirst
  exact ⟨n + m, final, hRun.returns hReturn, hFinalReady, hFinalSse, hFrame, hOutput, hCallee, hDF⟩

end Md5.Proofs.NewEntries.FinalizeReset
