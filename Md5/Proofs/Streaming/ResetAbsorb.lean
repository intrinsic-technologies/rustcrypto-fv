import Md5.Proofs.Streaming.FirstPass
import Md5.Proofs.Streaming.SecondPass
import Md5.Proofs.Streaming.ResetFinalize

namespace Md5.Proofs.Streaming

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Buffered

theorem reset_absorb [bindings : Bindings] {boundary : ReturnBoundary}
    (firstOperations : LoopOperations .resetFirst boundary)
    (secondOperations : LoopOperations .resetSecond boundary)
    (finalize : ∀ message s, FinalizeReset.Pre boundary message s →
      ∃ t, FinalizeReset.Post boundary message s t)
    {initial : RamState} {inputs : Array Slices.Input} {first : Nat}
    (hReady : ReadyToStep initial) (hCode : CodeIn Extracted.programImage initial)
    (hSse : SupportedSSE bindings.processor initial) (hStride : UnitStringStride bindings)
    (hCall : (TwoMessages.ValidCall TwoMessages.digestSlicesReset) bindings initial inputs first)
    (hOutside : ¬ InProgram boundary.rip) :
    ∃ fuel s, Advances boundary fuel initial s ∧
      StreamingState .resetSecond initial (Slices.message (inputs.extract first inputs.size)) s ∧
      s.RIP = 0x100a90 ∧
      (⟨(initial.regValue .r8).toNat, 16⟩ : MemoryRegion).HasBytes s.external
        ⟨(Standards.RFC.MD5.messageDigest
          (Standards.RFC.MD5.bitsOfBytes (Slices.message (inputs.extract 0 first)))).toArray⟩ := by
  obtain ⟨n, s, hFirst, hs⟩ :=
    first_pass firstOperations hReady hCode hSse hStride hCall hOutside
  have hp := hs.finalizePre hCall hStride hOutside
  obtain ⟨t, ht⟩ := finalize _ s hp
  have htState := finalizeReset_state hs.toStreamingState hCall ht
  have htDigest := finalizeReset_digest hs.storage ht
  have htTotal := (finalizeReset_total hp.toStorage ht).trans hs.total
  obtain ⟨m, u, hSecond, hu, hRip, hFrame⟩ := reset_second_absorb secondOperations htState
    hCall hStride hOutside ht.rip (ht.rbp.trans hs.bound) (ht.r12.trans hs.count) htTotal
  have hOutput : (⟨(initial.regValue .r8).toNat, 16⟩ : MemoryRegion).Bounded := by
    have hb := hCall.outputInMemory.2.1
    change (initial.regValue .r8).toNat + 32 < userAddressLimit at hb
    change (initial.regValue .r8).toNat + 16 < userAddressLimit
    omega
  have hSep : (⟨(initial.regValue .r8).toNat, 16⟩ : MemoryRegion).Disjoint
      (Stack.region initial TwoMessages.digestSlicesReset.minStackBytes) := by
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

end Md5.Proofs.Streaming
