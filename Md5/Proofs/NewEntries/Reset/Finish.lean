import Md5.Proofs.Streaming.Finalize
import Md5.Proofs.Streaming.Finish

namespace Md5.Proofs.NewEntries.Reset

open Md5.Proofs.Streaming Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Buffered

theorem finish [bindings : Bindings] {initial s : RamState} {inputs : Array Slices.Input} {first n : Nat}
    (hRun : Advances (returnBoundary initial) n initial s)
    (hs : StreamingState .resetDiscardSecond initial
      (Slices.message (inputs.extract first inputs.size)) s)
    (hRip : s.RIP = 0x1015fd)
    (finalize : ∀ message s, Finalize.Pre .resetDiscardSecond (returnBoundary initial) message s →
      ∃ t, Finalize.Post .resetDiscardSecond (returnBoundary initial) message s t)
    (hReady : ReadyToStep initial) (hStride : UnitStringStride bindings)
    (hCall : (ResetThenDigest.ValidCall ResetThenDigest.updateResetSlices) bindings initial inputs first)
    (hOutside : ¬ InProgram (returnBoundary initial).rip) :
    ∃ fuel final, Returns (returnBoundary initial) fuel initial final ∧
      ReadyToStep final ∧ SupportedSSE bindings.processor final ∧
      MemoryWriteFrame initial final
        #v[(ResetThenDigest.outputRegion ResetThenDigest.updateResetSlices) initial, Stack.region initial ResetThenDigest.updateResetSlices.minStackBytes] ∧
      ((ResetThenDigest.outputRegion ResetThenDigest.updateResetSlices) initial).HasBytes final.external
        ⟨(Standards.RFC.MD5.messageDigest (Standards.RFC.MD5.bitsOfBytes (Slices.message (inputs.extract first inputs.size)))).toArray⟩ ∧
      CalleeSavedRegistersUnchanged initial final ∧ DirectionFlagUnset final := by
  have hPre := streaming_finalize_pre hs (by decide) hCall.stackAvailable
    (hCall.stackSeparation.2 (Stack.region initial ResetThenDigest.updateResetSlices.minStackBytes) (by simp)).2
    hStride hOutside hRip (by have := validInputs_message_extract_size_lt hCall.inputsInMemory first inputs.size; omega)
  obtain ⟨t, ht⟩ := finalize _ s hPre
  have hStored := finalize_storage hs.storage hCall.stackAvailable ht
  have hDF := ht.agrees.directionFlagClear
    (by simp [Finalize.Kind.changes, Finalize.Kind.workRegisters, Finalize.Kind.localChanges]) hs.df
  have hGrow : ∀ address : BitVec 64, (initial.external[address]?).isSome →
      (t.external[address]?).isSome := fun a ha ↦ ht.agrees.grow a (hs.grows a ha)
  have hDigest : (⟨(stackPtr t).toNat + 120, 16⟩ : MemoryRegion).HasBytes t.external
      ⟨(Standards.RFC.MD5.messageDigest (Standards.RFC.MD5.bitsOfBytes (Slices.message (inputs.extract first inputs.size)))).toArray⟩ := by
    simpa only [Finalize.Kind.resultRegion, Finalize.Kind.resultOffset, Nat.add_zero, ht.rsp]
      using ht.digest
  have hEpilogue := resetDiscardSecond_epiloguePre hCall hReady hStored ht.ready ht.code hDF hGrow ht.rip hDigest
  obtain ⟨final, hf⟩ := epilogue_correct hEpilogue
  obtain ⟨m, hFinalize⟩ := ht.advances
  obtain ⟨k, hReturn⟩ := hf.returns
  have hFrame₁ := memoryWriteFrame_trans hs.memoryFrame
    (finalize_loop_frame hs.storage hCall.stackAvailable hPre ht)
  have hFrame₂ := hf.memoryFrame_stack hCall.stackAvailable (by decide +kernel)
    (by simpa only [Nat.add_comm, LoopKind.frame, EpilogueKind.frame] using hStored.rsp)
  refine ⟨n + (m + k), final, hRun.returns (hFinalize.returns hReturn), hf.ready,
    hf.sse (SupportedSSE.of_agreesExcept ht.agrees hs.sse),
    memoryWriteFrame_trans (fun a ha ↦ hFrame₁ a (by
      intro r hr
      change r ∈ #v[Stack.region initial ResetThenDigest.updateResetSlices.minStackBytes] at hr
      simp only [Vector.mem_mk, Array.mem_singleton] at hr
      subst r
      exact ha _ (Vector.getElem_mem (i := 1) (by decide)))) hFrame₂, hf.digestBytes, hf.calleeSaved, hf.df⟩

end Md5.Proofs.NewEntries.Reset
