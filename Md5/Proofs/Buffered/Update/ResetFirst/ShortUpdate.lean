import Md5.Proofs.Buffered.Update.ResetFirst.ShortResult

namespace Md5.Proofs.Buffered.ResetFirst
open Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs Block

theorem update_short_of_kind [Bindings] {kind : UpdateKind} (hk : KindSupported kind) {boundary : ReturnBoundary} {message input : ByteArray}
    {s : RamState} (h : UpdatePre kind boundary message input s)
    (hshort : message.size % 64 + input.size < 64) :
    ∃ t, UpdatePost kind boundary message input s t := by
  obtain ⟨fu, u, hau, hru, hcu, he⟩ := short_ready_of_kind hk h hshort
  obtain ⟨v, hc⟩ := short_copy_of_kind hk h he hru hcu (by omega)
  have hsp : stackPtr u = stackPtr s := he.agrees.read (n := 64) (r := 4)
    (by rcases hk with rfl | rfl | rfl <;> simp [shortReadyEffect_of_kind, Effect.components, reg, UpdateKind.inputRegister, UpdateKind.sizeRegister])
  have hvsp : stackPtr v = stackPtr s := hc.rsp.trans hsp
  have hw : MemoryRoutines.WritableRange v (stackPtr v + stackOffset kind 71) 1 := by
    rw [hvsp]
    have hw := h.contextWritable_of_agrees (he.agrees.trans hc.agrees) 63 1 (by decide)
    rcases hk with rfl | rfl | rfl <;> simpa [stackOffset, UpdateKind.contextOffset] using hw
  have hbytes : CodeIn (codeRange (pc kind 0x6a4) (shortFinishBytes_of_kind kind)) v :=
    by
      rcases hk with rfl | rfl | rfl
      · exact program_text_slice hc.code 0x6a4 8 (by decide +kernel)
      · exact program_text_slice hc.code 0xd54 8 (by decide +kernel)
      · exact program_text_slice hc.code 0x13e4 8 (by decide +kernel)
  have hap : RangeApart (stackPtr v + stackOffset kind 71) 1 (pc kind 0x6a4) 8 := by
    intro i hi j hj heq
    apply hw.code i hi
    rw [heq]
    rcases hk with rfl | rfl | rfl
    · have ht := text_address_in_program (0x6a4 + j) (by
        have hs : 0x6ac ≤ Extracted.textBytes.size := by decide +kernel
        omega)
      rw [BitVec.ofNat_add, ← BitVec.add_assoc] at ht
      exact ht
    · have ht := text_address_in_program (0xd54 + j) (by
        have hs : 0xd5c ≤ Extracted.textBytes.size := by decide +kernel
        omega)
      rw [BitVec.ofNat_add, ← BitVec.add_assoc] at ht
      exact ht
    · have ht := text_address_in_program (0x13e4 + j) (by
        have hs : 0x13ec ≤ Extracted.textBytes.size := by decide +kernel
        omega)
      rw [BitVec.ofNat_add, ← BitVec.add_assoc] at ht
      exact ht
  obtain ⟨ft, t, hat, hrt, _, hf⟩ := short_finish_of_kind hk boundary h.boundaryOutside
    v hc.ready hbytes ⟨hc.rip, ⟨hw.readable.low, hw.readable.mem, hw.tables⟩, hap⟩
  have hct : CodeIn Extracted.programImage t := by
    apply CodeIn.of_agreesExcept hf.agrees _ hc.code
    intro x hx c hm hcover
    simp only [shortFinishEffect_of_kind, Effect.components, List.map_cons, List.map_nil,
      Write.component_reg, Write.component_mem, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl
    all_goals try exact hcover.elim
    obtain ⟨i, hi, heq⟩ := hcover
    exact hw.code i hi (heq ▸ ⟨x.2, hx⟩)
  exact ⟨t, short_result_of_kind hk h hshort he ⟨fu, hau⟩ hc ⟨ft, hat⟩ hrt hct hf⟩


theorem update_short [Bindings] {boundary : ReturnBoundary} {message input : ByteArray}
    {s : RamState} (h : UpdatePre .resetFirst boundary message input s)
    (hshort : message.size % 64 + input.size < 64) :
    ∃ t, UpdatePost .resetFirst boundary message input s t := by
  exact update_short_of_kind (kind := .resetFirst) (Or.inl rfl) h hshort

end Md5.Proofs.Buffered.ResetFirst
