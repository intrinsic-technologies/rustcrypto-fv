import Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Copy.Execution
import Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Copy.Composition

namespace Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Copy

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Block

theorem part_run {variant : Variant} [Bindings] {boundary : ReturnBoundary} {kind : Kind} {part : Part}
    {s : RamState} (hOutside : ¬ InProgram boundary.rip) (hr : ReadyToStep s)
    (hc : CodeIn Extracted.programImage s) (hp : PartPre kind part s variant) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ (partEffect kind part s variant).Holds s t := by
  have hb : CodeIn (codeRange (kind.partEntry part variant) (kind.partBytes part variant)) s := by
    cases variant <;> cases kind <;> cases part
    · exact program_text_slice hc 0xaf9 64 (by decide +kernel)
    · exact program_text_slice hc 0xb39 52 (by decide +kernel)
    · exact program_text_slice hc 0xb6d 21 (by decide +kernel)
    · exact program_text_slice hc 0xbea 48 (by decide +kernel)
    · exact program_text_slice hc 0xc1a 52 (by decide +kernel)
    · exact program_text_slice hc 0xc4e 21 (by decide +kernel)
    · exact program_text_slice hc 0x1189 64 (by decide +kernel)
    · exact program_text_slice hc 0x11c9 52 (by decide +kernel)
    · exact program_text_slice hc 0x11fd 21 (by decide +kernel)
    · exact program_text_slice hc 0x127a 48 (by decide +kernel)
    · exact program_text_slice hc 0x12aa 52 (by decide +kernel)
    · exact program_text_slice hc 0x12de 21 (by decide +kernel)
    · exact program_text_slice hc 0x166c 64 (by decide +kernel)
    · exact program_text_slice hc 0x16ac 64 (by decide +kernel)
    · exact program_text_slice hc 0x16ec 18 (by decide +kernel)
    · exact program_text_slice hc 0x1772 48 (by decide +kernel)
    · exact program_text_slice hc 0x17a2 64 (by decide +kernel)
    · exact program_text_slice hc 0x17e2 18 (by decide +kernel)
  obtain ⟨fuel, t, ha, ht, _, he⟩ := part_execution (variant := variant) kind part boundary hOutside s hr hb hp
  exact ⟨fuel, t, ha, ht, he.codeIn (part_avoids hp.toStorage) hc, he⟩

theorem run {variant : Variant} [Bindings] {boundary : ReturnBoundary} {kind : Kind} {s : RamState}
    (hOutside : ¬ InProgram boundary.rip) (hr : ReadyToStep s)
    (hc : CodeIn Extracted.programImage s) (hp : RunPre kind s variant) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ (effect kind s variant).Holds s t := by
  have hh : PartPre kind .high s variant := ⟨hp.toStorage, by
    simpa [Kind.partEntry, Kind.partOffset] using hp.rip⟩
  obtain ⟨n, u, hn, hu, hcu, he⟩ := part_run hOutside hr hc hh
  have hl : PartPre kind .low u variant := ⟨hp.toStorage.of_agrees he.agrees (part_rsp he), by
    have hip := he.rip
    cases variant <;> cases kind <;> simpa [partEffect, Kind.partEntry, Kind.entry, Kind.partOffset,
      Kind.partLength] using hip⟩
  obtain ⟨m, v, hm, hv, hcv, hf⟩ := part_run hOutside hu hcu hl
  have hx : PartPre kind .arguments v variant := ⟨hl.toStorage.of_agrees hf.agrees (part_rsp hf), by
    have hip := hf.rip
    cases variant <;> cases kind <;> simpa [partEffect, Kind.partEntry, Kind.entry, Kind.partOffset,
      Kind.partLength] using hip⟩
  obtain ⟨k, t, hk, ht, hct, hg⟩ := part_run hOutside hv hcv hx
  exact ⟨n + m + k, t, (hn.trans hm).trans hk, ht, hct, effect_combine he hf hg⟩

theorem transition_agrees {variant : Variant} {kind : Kind} {s t : RamState}
    (h : (effect kind s variant).Holds s t) :
    AgreesExcept (variant.toKind.changes s) s t := by
  apply (effect_agrees h).widen
  · intro c hc hm
    simp only [changes, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals cases variant <;> simp_all [Component.isMem, Variant.toKind,
      Finalize.Kind.changes, Finalize.Kind.workRegisters, Finalize.Kind.localChanges]
  · intro address c hc ha
    simp only [changes, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    obtain ⟨i, hi, he⟩ := ha
    refine ⟨.mem (stackPtr s + BitVec.ofNat 64 variant.resultOffset)
      (if variant = .discard then 168 else 80), ?_,
      variant.blockOffset - variant.resultOffset + i, ?_, ?_⟩
    · cases variant <;> simp [Variant.toKind, Variant.resultOffset,
        Finalize.Kind.changes, Finalize.Kind.localChanges]
    · have := words_le kind
      change i < 8 * kind.words at hi
      cases variant <;> simp [Variant.blockOffset, Variant.resultOffset] <;> omega
    · rw [he]
      cases variant <;> simp [Variant.blockOffset, Variant.resultOffset,
        BitVec.ofNat_add, BitVec.add_assoc] <;> rw [← BitVec.add_assoc] <;> rfl

theorem buffer_bytes {variant : Variant} {kind : Kind} {s t : RamState}
    {buffer : Standards.RFC.MD5.Buffer} (he : (effect kind s variant).Holds s t)
    (hb : (⟨(stackPtr s).toNat + variant.resultOffset, 16⟩ : MemoryRegion).HasBytes s.external
      ⟨buffer.toBytes.toArray⟩) :
    (⟨(stackPtr t).toNat + variant.resultOffset, 16⟩ : MemoryRegion).HasBytes t.external
      ⟨buffer.toBytes.toArray⟩ := by
  rw [effect_rsp he]
  refine ⟨hb.1, ?_⟩
  intro i
  have hi : i.val < 16 := by simpa only [ByteArray.size, Vector.size_toArray] using i.isLt
  have hs := hb.2 i
  change t.external[BitVec.ofNat 64 ((stackPtr s).toNat + variant.resultOffset + i.val)]? = _
  change s.external[BitVec.ofNat 64 ((stackPtr s).toNat + variant.resultOffset + i.val)]? = _ at hs
  simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hs ⊢
  refine Eq.trans ((effect_agrees he).byte ?_) hs
  intro c hc ha
  simp only [changes, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  obtain ⟨j, hj, heq⟩ := ha
  have hj64 : j < 64 := by have := words_le kind; change j < 8 * kind.words at hj; omega
  have hApart : OffsetsApart variant.blockOffset 64 variant.resultOffset 16 := by
    cases variant <;> unfold OffsetsApart <;> decide
  cases variant <;> exact hApart.ne (stackPtr s) hj64 hi (by decide) heq.symm

end Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Copy
