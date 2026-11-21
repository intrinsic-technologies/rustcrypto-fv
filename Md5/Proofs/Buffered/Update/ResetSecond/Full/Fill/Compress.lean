import Md5.Proofs.Buffered.Update.ResetSecond.Counter
import Md5.Proofs.Buffered.Update.ResetSecond.Calls
import Md5.Proofs.Buffered.Update.Compression
import Md5.Proofs.Buffered.Update.Preservation

namespace Md5.Proofs.Buffered.ResetSecond

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Block

variable [Bindings] {kind : UpdateKind}
  (hkind : kind = .resetSecond ∨ kind = .finalizeResetSecond ∨ kind = .resetDiscardSecond) {boundary : ReturnBoundary} {message input : ByteArray} {s v : RamState}
  (h : UpdatePre kind boundary message input s)

include hkind h in
theorem fill_compress {changes : List Component} (ha : AgreesExcept changes s v)
    (hsp : stackPtr v = stackPtr s)
    (hrbx : kind ≠ .resetDiscardSecond → (.reg 3 : Operand 64).read v = kind.context s)
    (hr : ReadyToStep v)
    (hc : CodeIn Extracted.programImage v) (hip : v.RIP = (pc kind 0x100a0d))
    (hfull : 64 - message.size % 64 ≤ input.size)
    (hblock : (⟨(kind.context s).toNat, 64⟩ : MemoryRegion).HasBytes
      v.external (updateBlock message input))
    (hbuffer : (⟨(kind.context s).toNat + 64, 16⟩ : MemoryRegion).HasBytes
      v.external ⟨(absorbedBuffer message).toBytes.toArray⟩) :
    ∃ fuel w t, Advances boundary fuel v w ∧ (incrementPrepareEffect kind v).Holds v w ∧
      FinalizeReset.CompressCall.Post boundary (pc kind 0x100a24)
        (absorbedBuffer message) (updateBlock message input) w t := by
  have hw : MemoryRoutines.WritableRange v (kind.context v + 80) 8 := by
    simpa [UpdateKind.context, UpdateKind.contextOffset, BitVec.add_assoc, ← BitVec.ofNat_add, hsp] using
      h.contextWritable_of_agrees ha 80 8 (by decide)
  have hb : CodeIn (codeRange (pc kind 0x100a0d) (incrementPrepareBytes kind)) v :=
    by
      rcases hkind with rfl | rfl | rfl
      · exact program_text_slice hc 0xa0d 18 (by decide +kernel)
      · exact program_text_slice hc 0x109d 18 (by decide +kernel)
      · exact program_text_slice hc 0x1579 20 (by decide +kernel)
  have hap : RangeApart (kind.context v + 80) 8 (pc kind 0x100a0d) (if kind = .resetDiscardSecond then 20 else 18) := by
    intro i hi j hj heq
    apply hw.code i hi
    rw [heq]
    rcases hkind with rfl | rfl | rfl
    · have ht := text_address_in_program (0xa0d + j) (by
        have hn : 0xa0d + 18 ≤ Extracted.textBytes.size := by decide +kernel
        simp only [reduceCtorEq, ite_false] at hj
        omega)
      rw [BitVec.ofNat_add, ← BitVec.add_assoc] at ht
      simpa only [show Extracted.textAddress + BitVec.ofNat 64 0xa0d = pc .resetSecond 0x100a0d by decide +kernel] using ht
    · have ht := text_address_in_program (0x109d + j) (by
        have hn : 0x109d + 18 ≤ Extracted.textBytes.size := by decide +kernel
        simp only [reduceCtorEq, ite_false] at hj
        omega)
      rw [BitVec.ofNat_add, ← BitVec.add_assoc] at ht
      simpa only [show Extracted.textAddress + BitVec.ofNat 64 0x109d = pc .finalizeResetSecond 0x100a0d by decide +kernel] using ht
    · have ht := text_address_in_program (0x1579 + j) (by
        have hn : 0x1579 + 20 ≤ Extracted.textBytes.size := by decide +kernel
        simp only [ite_true] at hj
        omega)
      rw [BitVec.ofNat_add, ← BitVec.add_assoc] at ht
      simpa only [show Extracted.textAddress + BitVec.ofNat 64 0x1579 = pc .resetDiscardSecond 0x100a0d by decide +kernel] using ht
  obtain ⟨fuel, w, haw, hrw, _, he⟩ := increment_prepare hkind boundary h.boundaryOutside
    v hr hb ⟨hip, ⟨hw.readable.low, hw.readable.mem, hw.tables⟩, hap⟩
  have hcw : CodeIn Extracted.programImage w := by
    apply CodeIn.of_agreesExcept he.agrees _ hc
    intro x hx c hm hcover
    simp only [incrementPrepareEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component_reg, Write.component_mem, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hcover.elim
    obtain ⟨i, hi, heq⟩ := hcover
    exact hw.code i hi (heq ▸ ⟨x.2, hx⟩)
  have hspw : stackPtr w = stackPtr s :=
    (he.agrees.read (n := 64) (r := 4)
      (by simp [incrementPrepareEffect, Effect.components])).trans hsp
  have hdi : w.regValue .rdi = kind.context s + 64 := by
    change (.reg 7 : Operand 64).read w = _
    rw [he.writes.2.2.1]
    simp only [UpdateKind.context, hsp]
  have hsi : w.regValue .rsi = kind.context s := by
    change (.reg 6 : Operand 64).read w = _
    rw [he.writes.2.2.2]
    by_cases hd : kind = .resetDiscardSecond
    · simp only [hd, ite_true, UpdateKind.context, hsp]
    · simpa only [hd, ite_false] using hrbx hd
  have hdx : w.regValue .rdx = 1 := he.writes.2.1
  have hm : ∀ c ∈ (incrementPrepareEffect kind v).components, ∀ address, c.Covers address →
      (Component.mem (kind.context s + 80) 8).Covers address := by
    intro c hcm address hcover
    simp only [incrementPrepareEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component_reg, Write.component_mem, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hcm
    rcases hcm with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hcover.elim
    have heq : kind.context v + 80 = kind.context s + 80 := by
      simp only [UpdateKind.context, hsp]
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
  obtain ⟨t, ht⟩ := compress_call (p := pc kind 0x100a1f) (by rcases hkind with rfl | rfl | rfl <;> decide +kernel) h.boundaryOutside hrw hcw he.rip hp
  refine ⟨fuel, w, t, haw, he, ?_⟩
  simpa only [show pc kind 0x100a1f + 5 = pc kind 0x100a24 by
    rcases hkind with rfl | rfl | rfl <;> decide +kernel] using ht

end Md5.Proofs.Buffered.ResetSecond
