import Md5.Proofs.Streaming.Start
import Md5.Proofs.Streaming.ResetFinalize
import Md5.Proofs.Buffered.FinalizeReset.Normalize

namespace Md5.Proofs.Streaming

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure FirstPassPost [Bindings] (initial : RamState) (inputs : Array Slices.Input)
    (first : Nat) (s : RamState) : Prop extends
    StreamingState .resetFirst initial (Slices.message (inputs.extract 0 first)) s where
  rip : s.RIP = 0x1007a6
  position : (Operand.reg 0 : Operand 64).read s =
    BitVec.ofNat 64 ((Slices.message (inputs.extract 0 first)).size % 64)
  bitBlocks : (Operand.reg 14 : Operand 64).read s =
    BitVec.ofNat 64 ((Slices.message (inputs.extract 0 first)).size / 64) <<< 9
  bound : (Operand.reg 5 : Operand 64).read s = BitVec.ofNat 64 (min first inputs.size)
  count : (Operand.reg 12 : Operand 64).read s = BitVec.ofNat 64 inputs.size
  total : stackWord s 192 = BitVec.ofNat 64 inputs.size

theorem FirstPassPost.finalizePre [bindings : Bindings] {initial s : RamState}
    {inputs : Array Slices.Input} {first : Nat} {boundary : ReturnBoundary}
    (h : FirstPassPost initial inputs first s)
    (hCall : (TwoMessages.ValidCall TwoMessages.digestSlicesReset) bindings initial inputs first)
    (hStride : UnitStringStride bindings) (hOutside : ¬ InProgram boundary.rip) :
    Buffered.FinalizeReset.Pre boundary (Slices.message (inputs.extract 0 first)) s := by
  refine ⟨streaming_finalizeReset_storage h.toStreamingState hCall, h.ready, h.code,
    hStride, h.df, hOutside, h.rip, h.absorbed, h.position, h.bitBlocks, ?_⟩
  exact Nat.lt_trans (validInputs_message_extract_size_lt hCall.inputsInMemory 0 first)
    (by decide +kernel)

theorem first_normalize [bindings : Bindings] {initial s : RamState}
    {inputs : Array Slices.Input} {first : Nat} {boundary : ReturnBoundary}
    (h : LoopInvariant .resetFirst initial inputs 0 (min first inputs.size)
      (min first inputs.size) s)
    (hStorage : Buffered.FinalizeReset.Storage s) (hOutside : ¬ InProgram boundary.rip) :
    ∃ fuel t, Advances boundary fuel s t ∧ FirstPassPost initial inputs first t := by
  have hState : StreamingState .resetFirst initial
      (Slices.message (inputs.extract 0 first)) s := by
    simpa only [message_prefix_clamp] using h.toStreamingState
  have hRip : s.RIP = 0x100790 := by
    simpa only [Nat.lt_irrefl, ite_false, LoopKind.finalPC] using h.rip
  obtain ⟨fuel, t, hRun, ht, hCode, hRipT, hPosition, hBitBlocks, hCount, hRsp, hAgrees⟩ :=
    Buffered.FinalizeReset.normalize h.ready h.code hStorage hOutside hRip hState.absorbed
  have hMemory := hAgrees.external (by simp [Component.Covers])
  have hStateT : StreamingState .resetFirst initial
      (Slices.message (inputs.extract 0 first)) t := by
    refine ⟨h.storage.of_external_eq hRsp hMemory, ht, hCode,
      SupportedSSE.of_agreesExcept hAgrees h.sse, hAgrees.directionFlagClear (by simp) h.df,
      ?_, ?_, ?_⟩
    · have hContext : Buffered.UpdateKind.context .resetFirst t =
          Buffered.UpdateKind.context .resetFirst s := by
        simp only [Buffered.UpdateKind.context, hRsp]
      rw [hContext]
      exact absorbed_of_external_eq hState.absorbed hMemory
    · exact fun address ha ↦ hAgrees.grow address (h.grows address ha)
    · intro address ha
      rw [hMemory]
      exact h.memoryFrame address ha
  refine ⟨fuel, t, hRun, hStateT, hRipT, hPosition, hBitBlocks, ?_, ?_, ?_⟩
  · exact (hAgrees.read (n := 64) (r := 5) (by simp)).trans h.countValue
  · exact hCount.trans (h.resetTotal (Or.inl rfl))
  · simpa only [stackWord, hRsp, Operand.read, hMemory] using h.resetTotal (Or.inl rfl)

theorem first_pass [bindings : Bindings] {boundary : ReturnBoundary}
    (operations : LoopOperations .resetFirst boundary) {initial : RamState}
    {inputs : Array Slices.Input} {first : Nat} (hReady : ReadyToStep initial)
    (hCode : CodeIn Extracted.programImage initial)
    (hSse : SupportedSSE bindings.processor initial) (hStride : UnitStringStride bindings)
    (hCall : (TwoMessages.ValidCall TwoMessages.digestSlicesReset) bindings initial inputs first)
    (hOutside : ¬ InProgram boundary.rip) :
    ∃ fuel s, Advances boundary fuel initial s ∧ FirstPassPost initial inputs first s := by
  obtain ⟨n, s, hPrologue, hs, hCodeS, hp⟩ :=
    reset_prologue_of_ready boundary hReady hCode hCall hOutside
  by_cases hEmpty : min first inputs.size = 0
  · have hMessage : Slices.message (inputs.extract 0 first) = ByteArray.empty := by
      rw [← message_prefix_clamp, hEmpty, Array.extract_eq_empty_of_le (Nat.zero_le _),
        message_empty]
    refine ⟨n, s, hPrologue, ?_⟩
    refine {
      toStreamingState := ?_
      rip := ?_
      position := ?_
      bitBlocks := ?_
      bound := hp.bound
      count := hp.count
      total := hp.total
    }
    · rw [hMessage]
      exact reset_prologue_state hp hs hCodeS hSse hCall.directionFlagUnset
    · simpa only [hEmpty, ite_true] using hp.rip
    · simpa [hMessage] using (hp.empty hEmpty).1
    · simpa [hMessage] using (hp.empty hEmpty).2
  · have hi := reset_loop_initial hp hs hCodeS hSse hCall.directionFlagUnset hEmpty
    obtain ⟨m, t, hLoop, ht, _⟩ := loop_complete operations hi hCall.inputsInMemory
      hCall.stackAvailable hCall.separation hStride hOutside (Nat.zero_le _)
      (Nat.min_le_right _ _)
    have hState : StreamingState .resetFirst initial
        (Slices.message (inputs.extract 0 first)) t := by
      simpa only [message_prefix_clamp] using ht.toStreamingState
    obtain ⟨k, u, hNormalize, hu⟩ :=
      first_normalize ht (streaming_finalizeReset_storage hState hCall) hOutside
    exact ⟨n + m + k, u, (hPrologue.trans hLoop).trans hNormalize, hu⟩

end Md5.Proofs.Streaming
