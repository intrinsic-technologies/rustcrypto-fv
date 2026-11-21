import Md5.Proofs.Streaming.Start
import Md5.Proofs.Streaming.Finalize
import Md5.Proofs.Streaming.Finish

namespace Md5.Proofs.Streaming

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Buffered

theorem slices_run [bindings : Bindings] {initial : RamState} {inputs : Array Slices.Input}
    (operations : LoopOperations .slices (returnBoundary initial))
    (finalize : ∀ message s, Finalize.Pre .slices (returnBoundary initial) message s →
      ∃ t, Finalize.Post .slices (returnBoundary initial) message s t)
    (hReady : ReadyToStep initial) (hCode : CodeIn Extracted.programImage initial)
    (hSse : SupportedSSE bindings.processor initial) (hStride : UnitStringStride bindings)
    (hCall : (OneMessage.ValidCall OneMessage.digestSlices) bindings initial inputs)
    (hOutside : ¬ InProgram (returnBoundary initial).rip) :
    ∃ fuel final, Returns (returnBoundary initial) fuel initial final ∧
      ReadyToStep final ∧ SupportedSSE bindings.processor final ∧
      MemoryWriteFrame initial final
        #v[(OneMessage.outputRegion OneMessage.digestSlices) initial, Stack.region initial OneMessage.digestSlices.minStackBytes] ∧
      ((OneMessage.outputRegion OneMessage.digestSlices) initial).HasBytes final.external
        ⟨(Standards.RFC.MD5.messageDigest (Standards.RFC.MD5.bitsOfBytes (Slices.message inputs))).toArray⟩ ∧
      CalleeSavedRegistersUnchanged initial final ∧ DirectionFlagUnset final := by
  obtain ⟨n, s, hRun, hs, hRip⟩ :=
    slices_absorb operations hReady hCode hSse hStride hCall hOutside
  have hPre := streaming_finalize_pre hs (by decide) hCall.stackAvailable
    (hCall.stackSeparation.2 (Stack.region initial OneMessage.digestSlices.minStackBytes) (by simp)).2
    hStride hOutside hRip (by have := validInputs_message_size_lt hCall.inputsInMemory; omega)
  obtain ⟨t, ht⟩ := finalize _ s hPre
  have hStored := finalize_storage hs.storage hCall.stackAvailable ht
  have hDF := ht.agrees.directionFlagClear
    (by simp [Finalize.Kind.changes, Finalize.Kind.workRegisters, Finalize.Kind.localChanges]) hs.df
  have hGrow : ∀ address : BitVec 64, (initial.external[address]?).isSome →
      (t.external[address]?).isSome := fun a ha ↦ ht.agrees.grow a (hs.grows a ha)
  have hDigest : (⟨(stackPtr t).toNat, 16⟩ : MemoryRegion).HasBytes t.external
      ⟨(Standards.RFC.MD5.messageDigest (Standards.RFC.MD5.bitsOfBytes (Slices.message inputs))).toArray⟩ := by
    simpa only [Finalize.Kind.resultRegion, Finalize.Kind.resultOffset, Nat.add_zero, ht.rsp]
      using ht.digest
  have hEpilogue := slices_epiloguePre hCall hReady hStored ht.ready ht.code hDF hGrow ht.rip hDigest
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
      change r ∈ #v[Stack.region initial OneMessage.digestSlices.minStackBytes] at hr
      simp only [Vector.mem_mk, Array.mem_singleton] at hr
      subst r
      exact ha _ (Vector.getElem_mem (i := 1) (by decide)))) hFrame₂, hf.digestBytes, hf.calleeSaved, hf.df⟩

end Md5.Proofs.Streaming
