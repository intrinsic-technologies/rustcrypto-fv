import Md5.Proofs.Buffered.Update.Slices.Short.Finish
import Md5.Proofs.Buffered.Update.Slices.Short.Suffix

namespace Md5.Proofs.Buffered.Update.Slices

open Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs Block

theorem update_short [Bindings] {variant : Bool} {boundary : ReturnBoundary} {message input : ByteArray}
    {s : RamState} (h : UpdatePre (kind variant) boundary message input s)
    (hshort : message.size % 64 + input.size < 64) :
    ∃ t, UpdatePost (kind variant) boundary message input s t := by
  obtain ⟨p, hp⟩ := prepare h
  obtain ⟨fu, u, hau, hru, hcu, he⟩ := short_ready h hp (by omega)
  obtain ⟨v, hc⟩ := short_copy h he hru hcu (by omega)
  have hsp : stackPtr u = stackPtr s := he.agrees.read (n := 64) (r := 4)
    (by simp [shortReadyEffect, Effect.components])
  have hvsp : stackPtr v = stackPtr s := hc.rsp.trans hsp
  have hw : MemoryRoutines.WritableRange v (stackPtr v + 255) 1 := by
    rw [hvsp]
    cases variant <;> simpa [kind, UpdateKind.contextOffset, BitVec.add_assoc] using
      h.contextWritable_of_agrees (he.agrees.trans hc.agrees) 63 1 (by decide)
  have hbytes : CodeIn (codeRange (pc variant 0x100327) shortSuffixBytes) v := by
    cases variant with
    | false => exact program_text_slice hc.code 0x327 10 (by decide +kernel)
    | true => exact program_text_slice hc.code 0x18d7 10 (by decide +kernel)
  have hap : RangeApart (stackPtr v + 255) 1 (pc variant 0x100327) 10 := by
    intro i hi j hj heq
    apply hw.code i hi
    rw [heq]
    cases variant with
    | false =>
      have ht := text_address_in_program (0x327 + j) (by
        have hs : 0x331 ≤ Extracted.textBytes.size := by decide +kernel
        omega)
      simpa [pc, Extracted.textAddress, BitVec.ofNat_add, ← BitVec.add_assoc] using ht
    | true =>
      have ht := text_address_in_program (0x18d7 + j) (by
        have hs : 0x18e1 ≤ Extracted.textBytes.size := by decide +kernel
        omega)
      simpa [pc, Extracted.textAddress, BitVec.ofNat_add, ← BitVec.add_assoc] using ht
  obtain ⟨ft, t, hat, hrt, _, hf⟩ := short_suffix (variant := variant) boundary h.boundaryOutside
    v hc.ready hbytes ⟨hc.rip, ⟨hw.readable.low, hw.readable.mem, hw.tables⟩, hap⟩
  have hct : CodeIn Extracted.programImage t := by
    apply CodeIn.of_agreesExcept hf.agrees _ hc.code
    intro x hx c hm hcover
    simp only [shortSuffixEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component_reg, Write.component_mem, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl
    all_goals try exact hcover.elim
    obtain ⟨i, hi, heq⟩ := hcover
    exact hw.code i hi (heq ▸ ⟨x.2, hx⟩)
  refine ⟨t, short_result h hshort he ⟨fu, hau⟩ hc ⟨ft, hat⟩ hrt hct hf.rip ?_ hf.writes.2⟩
  apply hf.agrees.mono
  intro c hm
  simpa [shortSuffixEffect, Effect.components, or_assoc, or_left_comm, or_comm] using hm

end Md5.Proofs.Buffered.Update.Slices
