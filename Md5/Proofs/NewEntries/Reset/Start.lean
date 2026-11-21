import Md5.Proofs.Streaming.Loop
import Md5.Proofs.NewEntries.Reset.Prologue

namespace Md5.Proofs.NewEntries.Reset

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Md5.Proofs Md5.Proofs.Streaming

theorem prologue_streaming_state [bindings : Bindings] {initial s : RamState}
    {inputs : Array Slices.Input} {first : Nat} (h : ResetProloguePost initial inputs first s)
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hSse : SupportedSSE bindings.processor initial)
    (hDf : Prelude.RFLAGS.DirectionFlagClear initial.RFLAGS) :
    StreamingState .resetDiscardFirst initial ByteArray.empty s := by
  exact ⟨h.toPrologueStorage, hReady, hCode, SupportedSSE.of_agreesExcept h.agrees hSse,
    h.agrees.directionFlagClear (by simp [resetPrologueChanges]) hDf,
    h.absorbed, h.agrees.grow, h.memoryFrame⟩

theorem first_loop_initial [bindings : Bindings] {initial s : RamState}
    {inputs : Array Slices.Input} {first : Nat} (h : ResetProloguePost initial inputs first s)
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hSse : SupportedSSE bindings.processor initial)
    (hDf : Prelude.RFLAGS.DirectionFlagClear initial.RFLAGS) (hne : min first inputs.size ≠ 0) :
    LoopInvariant .resetDiscardFirst initial inputs 0 (min first inputs.size) 0 s := by
  refine {
    toStreamingState := ?_
    rip := ?_
    indexValue := h.index hne
    countValue := h.count
    resetTotal := by intro hk; rcases hk with hk | hk <;> cases hk
    secondRegisters := by intro hk; rcases hk with hk | hk <;> cases hk
    discardSecondMemcpy := by intro hk; cases hk
    discardTotal := fun _ ↦ h.total
  }
  · simpa [message_empty] using prologue_streaming_state h hReady hCode hSse hDf
  · simpa only [ite_eq_right hne, ite_eq_left (show 0 < min first inputs.size by omega),
      LoopKind.entry] using h.rip

end Md5.Proofs.NewEntries.Reset
