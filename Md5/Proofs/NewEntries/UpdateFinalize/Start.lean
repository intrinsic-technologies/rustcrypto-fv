import Md5.Proofs.Streaming.Loop
import Md5.Proofs.NewEntries.UpdateFinalize.Prologue

namespace Md5.Proofs.NewEntries.UpdateFinalize

open Md5.Proofs.Streaming Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem slices_prologue_state [bindings : Bindings] {initial s : RamState}
    {inputs : Array Slices.Input} (h : SlicesProloguePost initial inputs s)
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hSse : SupportedSSE bindings.processor initial)
    (hDf : Prelude.RFLAGS.DirectionFlagClear initial.RFLAGS) :
    StreamingState .updateFinalizeInto initial ByteArray.empty s := by
  refine ⟨h.toPrologueStorage, hReady, hCode, SupportedSSE.of_agreesExcept h.agrees hSse,
    h.agrees.directionFlagClear (by simp [prologueChanges]) hDf, h.absorbed, h.agrees.grow, ?_⟩
  intro a ha
  apply h.memoryFrame a
  intro r hr
  simp only [Vector.mem_mk, Array.mem_singleton] at hr
  subst r
  exact ha _ (LoopKind.stack_mem_writable _ initial)

theorem slices_loop_initial [bindings : Bindings] {initial s : RamState}
    {inputs : Array Slices.Input} (h : SlicesProloguePost initial inputs s)
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hSse : SupportedSSE bindings.processor initial)
    (hDf : Prelude.RFLAGS.DirectionFlagClear initial.RFLAGS) (hne : inputs.size ≠ 0) :
    LoopInvariant .updateFinalizeInto initial inputs 0 inputs.size 0 s := by
  refine {
    toStreamingState := ?_
    rip := ?_
    indexValue := h.index hne
    countValue := h.count hne
    secondRegisters := fun hk ↦ by rcases hk with hk | hk <;> cases hk
    resetTotal := fun hk ↦ by rcases hk with hk | hk <;> cases hk
    discardSecondMemcpy := fun hk ↦ by cases hk
    discardTotal := fun hk ↦ by cases hk
  }
  · simpa [message_empty] using slices_prologue_state h hReady hCode hSse hDf
  · simpa only [ite_eq_right hne, ite_eq_left (show 0 < inputs.size by omega), LoopKind.entry] using h.rip

theorem slices_absorb [bindings : Bindings] {boundary : ReturnBoundary}
    (operations : LoopOperations .updateFinalizeInto boundary) {initial : RamState}
    {inputs : Array Slices.Input} (hReady : ReadyToStep initial)
    (hCode : CodeIn Extracted.programImage initial)
    (hSse : SupportedSSE bindings.processor initial) (hStride : UnitStringStride bindings)
    (hCall : (OneMessage.ValidCall OneMessage.updateFinalizeInto) bindings initial inputs)
    (hOutside : ¬ InProgram boundary.rip) :
    ∃ fuel s, Advances boundary fuel initial s ∧
      StreamingState .updateFinalizeInto initial (Slices.message inputs) s ∧ s.RIP = 0x1019db := by
  obtain ⟨n, s, hRun, hReady', hCode', hp⟩ :=
    slices_prologue_of_ready boundary hReady hCode hCall hOutside
  by_cases hz : inputs.size = 0
  · have he : inputs = #[] := Array.eq_empty_of_size_eq_zero hz
    subst inputs
    exact ⟨n, s, hRun, slices_prologue_state hp hReady' hCode' hSse hCall.directionFlagUnset,
      by simpa using hp.rip⟩
  · have hi := slices_loop_initial hp hReady' hCode' hSse hCall.directionFlagUnset hz
    obtain ⟨m, t, hLoop, ht, _⟩ := loop_complete operations hi hCall.inputsInMemory
      hCall.stackAvailable hCall.stackSeparation hStride hOutside (Nat.zero_le _) (Nat.le_refl _)
    refine ⟨n + m, t, hRun.trans hLoop, ?_, ?_⟩
    · simpa using ht.toStreamingState
    · simpa [LoopKind.finalPC] using ht.rip

end Md5.Proofs.NewEntries.UpdateFinalize
