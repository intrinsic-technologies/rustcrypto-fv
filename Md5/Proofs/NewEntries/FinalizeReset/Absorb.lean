import Md5.Proofs.NewEntries.FinalizeReset.FirstPass
import Md5.Proofs.NewEntries.FinalizeReset.SecondPass
import Md5.Proofs.Streaming.ResetFinalize

namespace Md5.Proofs.NewEntries.FinalizeReset

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Buffered Streaming

theorem reset_absorb [bindings : Bindings] {boundary : ReturnBoundary}
    (firstOperations : LoopOperations .finalizeResetFirst boundary)
    (secondOperations : LoopOperations .finalizeResetSecond boundary)
    (finalize : ∀ message s, Buffered.FinalizeReset.Pre boundary message s (variant := .direct) →
      ∃ t, Buffered.FinalizeReset.Post boundary message s t (variant := .direct))
    {initial : RamState} {inputs : Array Slices.Input} {first : Nat}
    (hReady : ReadyToStep initial) (hCode : CodeIn Extracted.programImage initial)
    (hSse : SupportedSSE bindings.processor initial) (hStride : UnitStringStride bindings)
    (hCall : (TwoMessages.ValidCall TwoMessages.finalizeIntoResetSlices) bindings initial inputs first)
    (hOutside : ¬ InProgram boundary.rip) :
    ∃ fuel s, Advances boundary fuel initial s ∧
      StreamingState .finalizeResetSecond initial (Slices.message (inputs.extract first inputs.size)) s ∧
      s.RIP = 0x101120 ∧
      (⟨(initial.regValue .r8).toNat, 16⟩ : MemoryRegion).HasBytes s.external
        ⟨(Standards.RFC.MD5.messageDigest
          (Standards.RFC.MD5.bitsOfBytes (Slices.message (inputs.extract 0 first)))).toArray⟩ := by
  obtain ⟨n, s, hFirst, hs⟩ :=
    first_pass firstOperations hReady hCode hSse hStride hCall hOutside
  have hp := hs.finalizePre hCall hStride hOutside
  obtain ⟨t, ht⟩ := finalize _ s hp
  have htState := finalizeReset_state_variant (variant := .direct) hs.toStreamingState hCall ht
  have htDigest := finalizeReset_digest_variant (variant := .direct) hs.storage ht
  have htTotal := (finalizeReset_total_variant (variant := .direct) hp.toStorage ht).trans hs.total
  obtain ⟨m, u, hSecond, hu, hRip, hFrame⟩ := reset_second_absorb secondOperations htState
    hCall hStride hOutside ht.rip (ht.rbp.trans hs.bound) (ht.r12.trans hs.count) htTotal
  have hOutput : (⟨(initial.regValue .r8).toNat, 16⟩ : MemoryRegion).Bounded := by
    have hb := hCall.outputInMemory.2.1
    change (initial.regValue .r8).toNat + 32 < userAddressLimit at hb
    change (initial.regValue .r8).toNat + 16 < userAddressLimit
    omega
  have hSep : (⟨(initial.regValue .r8).toNat, 16⟩ : MemoryRegion).Disjoint
      (Stack.region initial TwoMessages.finalizeIntoResetSlices.minStackBytes) := by
    intro address ha
    apply hCall.separation.1 (0 : Fin 2) (1 : Fin 2) (by decide +kernel) address
    change (initial.regValue .r8).toNat ≤ address ∧ address < (initial.regValue .r8).toNat + 32
    change (initial.regValue .r8).toNat ≤ address ∧ address < (initial.regValue .r8).toNat + 16 at ha
    omega
  have hDigest := hasBytes_of_memoryWriteFrame hFrame htDigest hOutput (by
    intro region hr
    simp only [Vector.mem_mk, Array.mem_singleton] at hr
    subst region
    exact hSep)
  obtain ⟨k, hFinalize⟩ := ht.advances
  exact ⟨n + k + m, u, (hFirst.trans hFinalize).trans hSecond, hu, hRip, hDigest⟩

end Md5.Proofs.NewEntries.FinalizeReset
