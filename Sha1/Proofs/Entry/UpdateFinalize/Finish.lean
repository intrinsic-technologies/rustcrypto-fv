import Sha1.Proofs.Entry.UpdateFinalize.Epilogue
import Sha1.Proofs.Entry.UpdateFinalize.FinishFrame
import Sha1.Proofs.Common.Output
import Sha1.Proofs.Buffered.Finalize.Family

namespace Sha1.Proofs.Entry.UpdateFinalize

open Sha1.Spec Sha1.Spec.Program Standards.NIST Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha1.Proofs.Buffered Sha1.Proofs.Streaming.UpdateFinalize

theorem finish [bindings : Bindings] {initial : RamState} {inputs : Array Slices.Input}
    {s : RamState} (hCall : SliceHash.ValidCall SliceHash.updateFinalize bindings initial inputs)
    (hStride : UnitStringStride bindings) (hOutside : ¬ InProgram (returnBoundary initial).rip)
    (hLow : (returnBoundary initial).rip.toNat < userAddressLimit)
    (h : Header initial inputs inputs.size s) :
    ∃ fuel final, Returns (returnBoundary initial) fuel s final ∧ ReadyToStep final ∧
      CodeIn Extracted.programImage final ∧ CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧ MemoryWriteFrame initial final
        #v[SliceHash.outputRegion SliceHash.updateFinalize initial,
          Stack.region initial SliceHash.updateFinalize.minStackBytes] ∧
      fixedPart final = fixedPart initial ∧
      SliceHash.readOutput SliceHash.updateFinalize initial final =
        .ok (SHA1.SHA1 (SHA2.bytesToBits (Slices.message inputs))).bytes := by
  have hpre : Finalize.Pre .updateFinalizeCopy (returnBoundary initial) (Slices.message inputs) s := by
    refine ⟨h.toFrame.finalize_storage hCall, h.ready, h.code, hStride, h.df, ?_, hOutside, ?_, ?_⟩
    · simpa only [Nat.lt_irrefl, ite_false, Finalize.Kind.entry] using h.rip
    · change Absorbed (stackPtr s + 0xd8) (Slices.message inputs) s
      simpa only [Array.extract_eq_self_of_le (Nat.le_refl _)] using h.absorbed
    · have := Streaming.validInputs_message_size_lt hCall.inputInMemory
      omega
  have hresult := h.toFrame.finalize_output
  obtain ⟨t, hp⟩ := Finalize.finalize_family hpre (hresult ▸ hCall.outputInMemory.2.1)
    (by
      rw [hresult]
      intro a ha
      exact Option.isSome_iff_exists.mp (h.grows a (Option.isSome_iff_exists.mpr
        (hCall.outputInMemory.2.2 a ha))))
    (by
      rw [hresult]
      exact fun a ho hs ↦ hCall.separation.1 a ho (h.toFrame.finalize_stack_subset hCall.stackAvailable hs))
    (by rw [hresult]; exact (hCall.separation.2 _ (Vector.getElem_mem (i := 0) (by decide))).2)
  have hkeep := finalize_saved_word h.toFrame hCall hp
  have hsp : stackPtr t + 368 = (returnBoundary initial).rsp := by
    rw [hp.rsp, h.stack]
    change stackPtr initial - 360 + 368 = stackPtr initial + 8
    bv_omega
  obtain ⟨n, final, hret, hr, hag, hv⟩ := epilogue hp.ready hp.code hp.rip
    (finalize_stack_readable h.toFrame hCall hp) hOutside
    ((hkeep 360 (by decide) (by decide)).trans h.returnSlot) hsp hLow
  obtain ⟨m, ha⟩ := hp.advances
  have hmem := hag.external (by simp [Component.Covers])
  refine ⟨m + n, final, ha.returns hret, hr, CodeIn.of_external_eq hmem hp.code, ?_, ?_, ?_,
    hag.rest.trans (hp.agrees.rest.trans h.fixed), ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hv 0).trans ((hkeep 312 (by decide) (by decide)).trans h.savedRbx)
    · exact (hv 5).trans ((hkeep 352 (by decide) (by decide)).trans h.savedRbp)
    · exact (hv 1).trans ((hkeep 320 (by decide) (by decide)).trans h.savedR12)
    · exact (hv 2).trans ((hkeep 328 (by decide) (by decide)).trans h.savedR13)
    · exact (hv 3).trans ((hkeep 336 (by decide) (by decide)).trans h.savedR14)
    · exact (hv 4).trans ((hkeep 344 (by decide) (by decide)).trans h.savedR15)
  · apply hag.directionFlagClear (by decide)
    exact hp.agrees.directionFlagClear (by
      simp [Finalize.Kind.changes, Finalize.Kind.workRegisters, Finalize.Kind.localChanges]) h.df
  · intro a hout
    rw [hmem]
    exact finalize_write_frame h.toFrame hCall hp a hout
  · have hd := hp.digest
    rw [hresult] at hd
    unfold SliceHash.readOutput
    rw [hmem]
    exact Common.readBytes_of_hasBytes (initial := initial) hd

end Sha1.Proofs.Entry.UpdateFinalize
