import Md5.Proofs.Buffered.Update.ResetFirst.FillIncrement
import Md5.Proofs.Buffered.Update.ResetFirst.Calls
import Md5.Proofs.Buffered.Update.Compression
import Md5.Proofs.Buffered.Update.Preservation

namespace Md5.Proofs.Buffered.ResetFirst

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Block

section
variable [Bindings] {kind : UpdateKind} (hk : KindSupported kind) {boundary : ReturnBoundary} {message input : ByteArray} {s v : RamState}
  (h : UpdatePre kind boundary message input s)

include hk h in
theorem fill_compress_of_kind {changes : List Component} (ha : AgreesExcept changes s v)
    (hsp : stackPtr v = stackPtr s) (hr : ReadyToStep v)
    (hc : CodeIn Extracted.programImage v) (hip : v.RIP = (pc kind 0x704))
    (hfull : 64 - message.size % 64 ≤ input.size)
    (hblock : (⟨(kind.context s).toNat, 64⟩ : MemoryRegion).HasBytes
      v.external (updateBlock message input))
    (hbuffer : (⟨(kind.context s).toNat + 64, 16⟩ : MemoryRegion).HasBytes
      v.external ⟨(absorbedBuffer message).toBytes.toArray⟩) :
    ∃ fuel w t, Advances boundary fuel v w ∧ (incrementPrepareEffect_of_kind kind v).Holds v w ∧
      FinalizeReset.CompressCall.Post boundary (pc kind 0x71d)
        (absorbedBuffer message) (updateBlock message input) w t := by
  have hw : MemoryRoutines.WritableRange v (stackPtr v + stackOffset kind 88) 8 := by
    rw [hsp]
    have hw := h.contextWritable_of_agrees ha 80 8 (by decide)
    rcases hk with rfl | rfl | rfl <;> simpa [stackOffset, UpdateKind.contextOffset] using hw
  obtain ⟨fuel, w, haw, hrw, hcw, he⟩ := increment_prepare_of_kind hk boundary h.boundaryOutside hr hc hip hw
  have hspw : stackPtr w = stackPtr s :=
    (he.agrees.read (n := 64) (r := 4)
      (by simp [incrementPrepareEffect_of_kind, Effect.components])).trans hsp
  have hdi : w.regValue .rdi = kind.context s + 64 := by
    change (.reg 7 : Operand 64).read w = _
    rw [he.writes.2.2.1, hsp]
    rcases hk with rfl | rfl | rfl <;> simp [stackOffset, UpdateKind.context, UpdateKind.contextOffset, BitVec.add_assoc]
  have hsi : w.regValue .rsi = kind.context s := by
    change (.reg 6 : Operand 64).read w = _
    rw [he.writes.2.2.2, hsp]
    rcases hk with rfl | rfl | rfl <;> rfl
  have hdx : w.regValue .rdx = 1 := he.writes.2.1
  have hm : ∀ c ∈ (incrementPrepareEffect_of_kind kind v).components, ∀ address, c.Covers address →
      (Component.mem (kind.context s + 80) 8).Covers address := by
    intro c hcm address hcover
    simp only [incrementPrepareEffect_of_kind, Effect.components, List.map_cons, List.map_nil,
      Write.component_reg, Write.component_mem, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hcm
    rcases hcm with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hcover.elim
    have heq : stackPtr v + stackOffset kind 88 = kind.context s + 80 := by
      rw [hsp]
      rcases hk with rfl | rfl | rfl <;> simp [stackOffset, UpdateKind.context, UpdateKind.contextOffset, BitVec.add_assoc]
    simpa only [heq] using hcover
  have hbw : (⟨(kind.context s).toNat, 64⟩ : MemoryRegion).HasBytes
      w.external (updateBlock message input) := by
    have hs := size_updateBlock message input hfull
    have hb' : (⟨(kind.context s).toNat + 0,
        (updateBlock message input).size⟩ : MemoryRegion).HasBytes v.external
        (updateBlock message input) := by simpa only [Nat.add_zero, hs] using hblock
    have hp := h.bytes_before_counter_of_agrees he.agrees hm (offset := 0)
      (by rw [hs]; decide) hb'
    simpa only [Nat.add_zero, hs] using hp
  have hbufferw : (⟨(kind.context s).toNat + 64, 16⟩ : MemoryRegion).HasBytes
      w.external ⟨(absorbedBuffer message).toBytes.toArray⟩ := by
    have hs : (⟨(absorbedBuffer message).toBytes.toArray⟩ : ByteArray).size = 16 := by
      simp only [ByteArray.size, Vector.size_toArray]
    have hp := h.bytes_before_counter_of_agrees he.agrees hm (offset := 64)
      (bytes := ⟨(absorbedBuffer message).toBytes.toArray⟩) (by rw [hs]; decide)
      (by simpa only [hs] using hbuffer)
    simpa only [hs] using hp
  have hp := h.compressionPre_context (ha.trans he.agrees) hspw hdi hsi hdx
    (size_updateBlock message input hfull) hbw hbufferw
  obtain ⟨t, ht⟩ := compress_call_of_kind hk (Or.inl rfl) h.boundaryOutside hrw hcw he.rip hp
  refine ⟨fuel, w, t, haw, he, ?_⟩
  have hpc : pc kind 0x718 + 5 = pc kind 0x71d := by
    rcases hk with rfl | rfl | rfl <;> decide
  simpa only [hpc] using ht


end

section
variable [Bindings] {boundary : ReturnBoundary} {message input : ByteArray} {s v : RamState}
  (h : UpdatePre .resetFirst boundary message input s)

include h in
theorem fill_compress {changes : List Component} (ha : AgreesExcept changes s v)
    (hsp : stackPtr v = stackPtr s) (hr : ReadyToStep v)
    (hc : CodeIn Extracted.programImage v) (hip : v.RIP = 0x100704)
    (hfull : 64 - message.size % 64 ≤ input.size)
    (hblock : (⟨(UpdateKind.resetFirst.context s).toNat, 64⟩ : MemoryRegion).HasBytes
      v.external (updateBlock message input))
    (hbuffer : (⟨(UpdateKind.resetFirst.context s).toNat + 64, 16⟩ : MemoryRegion).HasBytes
      v.external ⟨(absorbedBuffer message).toBytes.toArray⟩) :
    ∃ fuel w t, Advances boundary fuel v w ∧ (incrementPrepareEffect v).Holds v w ∧
      FinalizeReset.CompressCall.Post boundary 0x10071d
        (absorbedBuffer message) (updateBlock message input) w t := by
  exact fill_compress_of_kind (kind := .resetFirst) (Or.inl rfl) h ha hsp hr hc hip hfull hblock hbuffer

end

end Md5.Proofs.Buffered.ResetFirst
