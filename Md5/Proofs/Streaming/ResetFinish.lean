import Md5.Proofs.Streaming.Finalize
import Md5.Proofs.Streaming.Finish
import Md5.Proofs.Buffered.Update.Memory

namespace Md5.Proofs.Streaming

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Buffered

theorem reset_second_finish [bindings : Bindings] {initial s : RamState}
    {inputs : Array Slices.Input} {first : Nat} {suffix : ByteArray}
    {firstDigest : Vector UInt8 16}
    (finalize : ∀ message s, Finalize.Pre .resetSecond (returnBoundary initial) message s →
      ∃ t, Finalize.Post .resetSecond (returnBoundary initial) message s t)
    (hReady : ReadyToStep initial)
    (hCall : (TwoMessages.ValidCall TwoMessages.digestSlicesReset) bindings initial inputs first)
    (hs : StreamingState .resetSecond initial suffix s)
    (hStride : UnitStringStride bindings) (hOutside : ¬ InProgram (returnBoundary initial).rip)
    (hRip : s.RIP = 0x100a90) (hSize : suffix.size < 2^64)
    (hFirst : (⟨(initial.regValue .r8).toNat, 16⟩ : MemoryRegion).HasBytes s.external
      ⟨firstDigest.toArray⟩) :
    ∃ fuel final, Returns (returnBoundary initial) fuel s final ∧
      ReadyToStep final ∧ SupportedSSE bindings.processor final ∧
      MemoryWriteFrame initial final
        #v[(TwoMessages.outputRegion TwoMessages.digestSlicesReset) initial,
          Stack.region initial TwoMessages.digestSlicesReset.minStackBytes] ∧
      ((TwoMessages.outputRegion TwoMessages.digestSlicesReset) initial).HasBytes final.external
        ⟨(firstDigest ++ Standards.RFC.MD5.messageDigest (Standards.RFC.MD5.bitsOfBytes suffix)).toArray⟩ ∧
      CalleeSavedRegistersUnchanged initial final ∧ DirectionFlagUnset final := by
  have hPre := streaming_finalize_pre hs (by decide) hCall.stackAvailable
    (hCall.separation.2 (Stack.region initial TwoMessages.digestSlicesReset.minStackBytes) (by simp)).2
    hStride hOutside hRip hSize
  obtain ⟨t, ht⟩ := finalize _ s hPre
  have hStackFrame := finalize_stack_frame hs.storage hCall.stackAvailable hPre ht
  have hOutputBound : (initial.regValue .r8).toNat + 32 < 2^32 := hCall.outputInMemory.2.1
  have hFirstBound : (⟨(initial.regValue .r8).toNat, 16⟩ : MemoryRegion).Bounded := by
    change (initial.regValue .r8).toNat + 16 < 2^32
    omega
  have hFirstStack : (⟨(initial.regValue .r8).toNat, 16⟩ : MemoryRegion).Disjoint
      (Stack.region initial TwoMessages.digestSlicesReset.minStackBytes) := by
    intro a ha haStack
    apply hCall.separation.1 (0 : Fin 2) (1 : Fin 2) (by decide +kernel) a ?_ haStack
    change (initial.regValue .r8).toNat ≤ a ∧ a < (initial.regValue .r8).toNat + 32
    change (initial.regValue .r8).toNat ≤ a ∧ a < (initial.regValue .r8).toNat + 16 at ha
    omega
  have hFirstFinalized := hasBytes_of_memoryWriteFrame hStackFrame hFirst hFirstBound (by
    intro r hr
    simp only [Vector.mem_mk, Array.mem_singleton] at hr
    subst r
    exact hFirstStack)
  have hStored := finalize_storage hs.storage hCall.stackAvailable ht
  have hDF := ht.agrees.directionFlagClear
    (by simp [Finalize.Kind.changes, Finalize.Kind.workRegisters, Finalize.Kind.localChanges]) hs.df
  have hGrow : ∀ address : BitVec 64, (initial.external[address]?).isSome →
      (t.external[address]?).isSome := fun a ha ↦ ht.agrees.grow a (hs.grows a ha)
  have hDigest : (⟨(stackPtr t).toNat + 216, 16⟩ : MemoryRegion).HasBytes t.external
      ⟨(Standards.RFC.MD5.messageDigest (Standards.RFC.MD5.bitsOfBytes suffix)).toArray⟩ := by
    simpa only [Finalize.Kind.resultRegion, Finalize.Kind.resultOffset, ht.rsp] using ht.digest
  have hEpilogue := resetSecond_epiloguePre hCall hReady hStored ht.ready ht.code hDF hGrow
    ht.rip hDigest
  obtain ⟨final, hf⟩ := epilogue_correct hEpilogue
  have hSecondFrame := hf.memoryFrame_stack hCall.stackAvailable (by decide +kernel)
    (by simpa only [Nat.add_comm, LoopKind.frame, EpilogueKind.frame] using hStored.rsp)
  have hOutputNext : (initial.regValue .r8 + 16).toNat = (initial.regValue .r8).toNat + 16 := by
    exact toNat_add_ofNat _ 16 (by omega)
  have hFirstSecond : (⟨(initial.regValue .r8).toNat, 16⟩ : MemoryRegion).Disjoint
      ⟨(initial.regValue .r8 + 16).toNat, 16⟩ := by
    intro a ha hb
    change (initial.regValue .r8).toNat ≤ a ∧ a < (initial.regValue .r8).toNat + 16 at ha
    change (initial.regValue .r8 + 16).toNat ≤ a ∧
      a < (initial.regValue .r8 + 16).toNat + 16 at hb
    rw [hOutputNext] at hb
    omega
  have hFirstFinal := hasBytes_of_memoryWriteFrame hSecondFrame hFirstFinalized hFirstBound (by
    intro r hr
    simp only [Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hFirstSecond
    · exact hFirstStack)
  have hSecondBytes : (⟨(initial.regValue .r8).toNat + 16, 16⟩ : MemoryRegion).HasBytes
      final.external ⟨(Standards.RFC.MD5.messageDigest (Standards.RFC.MD5.bitsOfBytes suffix)).toArray⟩ := by
    simpa only [hOutputNext] using hf.digestBytes
  have hCombined := hasBytes_append
    (a := ⟨firstDigest.toArray⟩)
    (b := ⟨(Standards.RFC.MD5.messageDigest (Standards.RFC.MD5.bitsOfBytes suffix)).toArray⟩)
    (by simpa only [ByteArray.size, Vector.size_toArray] using hFirstFinal)
    (by simpa only [ByteArray.size, Vector.size_toArray] using hSecondBytes)
  have hFinalFrame : MemoryWriteFrame t final
      #v[(TwoMessages.outputRegion TwoMessages.digestSlicesReset) initial,
        Stack.region initial TwoMessages.digestSlicesReset.minStackBytes] := by
    intro address ha
    apply hSecondFrame address
    intro r hr hin
    simp only [Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · apply ha ((TwoMessages.outputRegion TwoMessages.digestSlicesReset) initial) (by simp)
      change (initial.regValue .r8 + 16).toNat ≤ address.toNat ∧
        address.toNat < (initial.regValue .r8 + 16).toNat + 16 at hin
      rw [hOutputNext] at hin
      change (initial.regValue .r8).toNat ≤ address.toNat ∧
        address.toNat < (initial.regValue .r8).toNat + 32
      omega
    · exact ha _ (by simp) hin
  obtain ⟨m, hFinalize⟩ := ht.advances
  obtain ⟨k, hReturn⟩ := hf.returns
  have hFrame := memoryWriteFrame_trans hs.memoryFrame
    (finalize_loop_frame hs.storage hCall.stackAvailable hPre ht)
  refine ⟨m + k, final, hFinalize.returns hReturn, hf.ready,
    hf.sse (SupportedSSE.of_agreesExcept ht.agrees hs.sse),
    memoryWriteFrame_trans hFrame hFinalFrame, ?_, hf.calleeSaved, hf.df⟩
  have hJoin :
      (⟨firstDigest.toArray⟩ ++
        ⟨(Standards.RFC.MD5.messageDigest (Standards.RFC.MD5.bitsOfBytes suffix)).toArray⟩ : ByteArray) =
      ⟨(firstDigest ++ Standards.RFC.MD5.messageDigest (Standards.RFC.MD5.bitsOfBytes suffix)).toArray⟩ := by
    apply ByteArray.ext
    simp only [ByteArray.data_append, Vector.toArray_append]
  rw [hJoin] at hCombined
  simpa only [ByteArray.size, Vector.size_toArray, Nat.reduceAdd,
    TwoMessages.outputRegion, TwoMessages.digestSlicesReset, registerRegion] using hCombined

end Md5.Proofs.Streaming
