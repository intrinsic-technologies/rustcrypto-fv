import Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Padding.Clear.Execution
import Md5.Proofs.Buffered.FinalizeReset.Export.Geometry

namespace Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Padding.Clear

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

theorem effect_word {variant : Variant} {s t : RamState} (h : (effect s variant).Holds s t) (j : Nat) (hj : j < 7) :
    (Operand.mem (stackPtr s + BitVec.ofNat 64 (variant.tailOffset + 8 * j)) : Operand 64).read t = 0 := by
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h.writes.1
  · exact h.writes.2.1
  · exact h.writes.2.2.1
  · exact h.writes.2.2.2.1
  · exact h.writes.2.2.2.2.1
  · exact h.writes.2.2.2.2.2.1
  · exact h.writes.2.2.2.2.2.2

theorem effect_bytes {variant : Variant} {s t : RamState} (hs : Storage variant.toKind s) (h : (effect s variant).Holds s t) :
    Bytes t.external (stackPtr s + BitVec.ofNat 64 variant.tailOffset) 56 (fun _ ↦ 0) := by
  intro i hi
  have hReadable := Stores.readable_of_agrees
    (hs.stackWritable (variant.tailOffset + 8 * (i / 8)) 8 (by
      cases variant <;> simp only [Variant.tailOffset, Variant.toKind, Kind.stackBytes] <;> omega)).readable h.agrees
  have hBytes := Stores.bytes_of_read_eq hReadable (effect_word h (i / 8) (by omega))
  have hByte := hBytes (i % 8) (by omega)
  have he : stackPtr s + BitVec.ofNat 64 (variant.tailOffset + 8 * (i / 8)) + BitVec.ofNat 64 (i % 8) =
      stackPtr s + BitVec.ofNat 64 variant.tailOffset + BitVec.ofNat 64 i := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    have hn : variant.tailOffset + 8 * (i / 8) + i % 8 = variant.tailOffset + i := by omega
    rw [hn, BitVec.ofNat_add, ← BitVec.add_assoc]
  simpa [he, storedByte] using hByte

theorem effect_avoids {variant : Variant} {s : RamState} (h : Storage variant.toKind s) :
    (effect s variant).Avoids Extracted.programImage := by
  cases variant with
  | original =>
    intro x hx c hc ha
    simp only [effect, Effect.components, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, Write.component, Operand.component,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    all_goals apply h.stackAvoids x.1 _ (.inl ⟨x.2, hx⟩)
    · exact h.stackCover (by decide : 96 + 8 ≤ Kind.resetSecond.stackBytes) ha
    · exact h.stackCover (by decide : 104 + 8 ≤ Kind.resetSecond.stackBytes) ha
    · exact h.stackCover (by decide : 112 + 8 ≤ Kind.resetSecond.stackBytes) ha
    · exact h.stackCover (by decide : 120 + 8 ≤ Kind.resetSecond.stackBytes) ha
    · exact h.stackCover (by decide : 128 + 8 ≤ Kind.resetSecond.stackBytes) ha
    · exact h.stackCover (by decide : 136 + 8 ≤ Kind.resetSecond.stackBytes) ha
    · exact h.stackCover (by decide : 144 + 8 ≤ Kind.resetSecond.stackBytes) ha
  | finalize =>
    intro x hx c hc ha
    simp only [effect, Effect.components, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, Write.component, Operand.component,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    all_goals apply h.stackAvoids x.1 _ (.inl ⟨x.2, hx⟩)
    · exact h.stackCover (by decide : 96 + 8 ≤ Kind.finalizeResetSecond.stackBytes) ha
    · exact h.stackCover (by decide : 104 + 8 ≤ Kind.finalizeResetSecond.stackBytes) ha
    · exact h.stackCover (by decide : 112 + 8 ≤ Kind.finalizeResetSecond.stackBytes) ha
    · exact h.stackCover (by decide : 120 + 8 ≤ Kind.finalizeResetSecond.stackBytes) ha
    · exact h.stackCover (by decide : 128 + 8 ≤ Kind.finalizeResetSecond.stackBytes) ha
    · exact h.stackCover (by decide : 136 + 8 ≤ Kind.finalizeResetSecond.stackBytes) ha
    · exact h.stackCover (by decide : 144 + 8 ≤ Kind.finalizeResetSecond.stackBytes) ha
  | discard =>
    intro x hx c hc ha
    simp only [effect, Effect.components, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, Write.component, Operand.component,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    all_goals apply h.stackAvoids x.1 _ (.inl ⟨x.2, hx⟩)
    · exact h.stackCover (by decide : 136 + 8 ≤ Kind.resetDiscardSecond.stackBytes) ha
    · exact h.stackCover (by decide : 144 + 8 ≤ Kind.resetDiscardSecond.stackBytes) ha
    · exact h.stackCover (by decide : 152 + 8 ≤ Kind.resetDiscardSecond.stackBytes) ha
    · exact h.stackCover (by decide : 160 + 8 ≤ Kind.resetDiscardSecond.stackBytes) ha
    · exact h.stackCover (by decide : 168 + 8 ≤ Kind.resetDiscardSecond.stackBytes) ha
    · exact h.stackCover (by decide : 176 + 8 ≤ Kind.resetDiscardSecond.stackBytes) ha
    · exact h.stackCover (by decide : 184 + 8 ≤ Kind.resetDiscardSecond.stackBytes) ha

theorem effect_frame {variant : Variant} {s t : RamState} (h : (effect s variant).Holds s t) :
    AgreesExcept [.rip, .mem (stackPtr s + BitVec.ofNat 64 variant.tailOffset) 56] s t := by
  cases variant with
  | original =>
    apply h.agrees.widen
    · intro c hc hm
      simp only [effect, Effect.components, List.map_cons, List.map_nil,
        List.cons_append, List.nil_append, Write.component, Operand.component,
        List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp_all [Component.isMem]
    · intro address c hc ha
      simp only [effect, Effect.components, List.map_cons, List.map_nil,
        List.cons_append, List.nil_append, Write.component, Operand.component,
        List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals try exact ha.elim
      all_goals refine ⟨.mem (stackPtr s + 96) 56, by simp [Variant.tailOffset], ?_⟩
      · exact FinalizeReset.Export.covers_shift (offset := 0) (by simpa [Variant.tailOffset] using ha) (by decide)
      · exact FinalizeReset.Export.covers_shift (offset := 8)
          (by simpa [BitVec.add_assoc, Variant.tailOffset] using ha) (by decide)
      · exact FinalizeReset.Export.covers_shift (offset := 16)
          (by simpa [BitVec.add_assoc, Variant.tailOffset] using ha) (by decide)
      · exact FinalizeReset.Export.covers_shift (offset := 24)
          (by simpa [BitVec.add_assoc, Variant.tailOffset] using ha) (by decide)
      · exact FinalizeReset.Export.covers_shift (offset := 32)
          (by simpa [BitVec.add_assoc, Variant.tailOffset] using ha) (by decide)
      · exact FinalizeReset.Export.covers_shift (offset := 40)
          (by simpa [BitVec.add_assoc, Variant.tailOffset] using ha) (by decide)
      · exact FinalizeReset.Export.covers_shift (offset := 48)
          (by simpa [BitVec.add_assoc, Variant.tailOffset] using ha) (by decide)
  | finalize =>
    apply h.agrees.widen
    · intro c hc hm
      simp only [effect, Effect.components, List.map_cons, List.map_nil,
        List.cons_append, List.nil_append, Write.component, Operand.component,
        List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp_all [Component.isMem]
    · intro address c hc ha
      simp only [effect, Effect.components, List.map_cons, List.map_nil,
        List.cons_append, List.nil_append, Write.component, Operand.component,
        List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals try exact ha.elim
      all_goals refine ⟨.mem (stackPtr s + 96) 56, by simp [Variant.tailOffset], ?_⟩
      · exact FinalizeReset.Export.covers_shift (offset := 0) (by simpa [Variant.tailOffset] using ha) (by decide)
      · exact FinalizeReset.Export.covers_shift (offset := 8)
          (by simpa [BitVec.add_assoc, Variant.tailOffset] using ha) (by decide)
      · exact FinalizeReset.Export.covers_shift (offset := 16)
          (by simpa [BitVec.add_assoc, Variant.tailOffset] using ha) (by decide)
      · exact FinalizeReset.Export.covers_shift (offset := 24)
          (by simpa [BitVec.add_assoc, Variant.tailOffset] using ha) (by decide)
      · exact FinalizeReset.Export.covers_shift (offset := 32)
          (by simpa [BitVec.add_assoc, Variant.tailOffset] using ha) (by decide)
      · exact FinalizeReset.Export.covers_shift (offset := 40)
          (by simpa [BitVec.add_assoc, Variant.tailOffset] using ha) (by decide)
      · exact FinalizeReset.Export.covers_shift (offset := 48)
          (by simpa [BitVec.add_assoc, Variant.tailOffset] using ha) (by decide)
  | discard =>
    apply h.agrees.widen
    · intro c hc hm
      simp only [effect, Effect.components, List.map_cons, List.map_nil,
        List.cons_append, List.nil_append, Write.component, Operand.component,
        List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp_all [Component.isMem]
    · intro address c hc ha
      simp only [effect, Effect.components, List.map_cons, List.map_nil,
        List.cons_append, List.nil_append, Write.component, Operand.component,
        List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals try exact ha.elim
      all_goals refine ⟨.mem (stackPtr s + 136) 56, by simp [Variant.tailOffset], ?_⟩
      · exact FinalizeReset.Export.covers_shift (offset := 0) (by simpa [Variant.tailOffset] using ha) (by decide)
      · exact FinalizeReset.Export.covers_shift (offset := 8)
          (by simpa [BitVec.add_assoc, Variant.tailOffset] using ha) (by decide)
      · exact FinalizeReset.Export.covers_shift (offset := 16)
          (by simpa [BitVec.add_assoc, Variant.tailOffset] using ha) (by decide)
      · exact FinalizeReset.Export.covers_shift (offset := 24)
          (by simpa [BitVec.add_assoc, Variant.tailOffset] using ha) (by decide)
      · exact FinalizeReset.Export.covers_shift (offset := 32)
          (by simpa [BitVec.add_assoc, Variant.tailOffset] using ha) (by decide)
      · exact FinalizeReset.Export.covers_shift (offset := 40)
          (by simpa [BitVec.add_assoc, Variant.tailOffset] using ha) (by decide)
      · exact FinalizeReset.Export.covers_shift (offset := 48)
          (by simpa [BitVec.add_assoc, Variant.tailOffset] using ha) (by decide)

theorem effect_agrees {variant : Variant} {s t : RamState} (h : (effect s variant).Holds s t) :
    AgreesExcept (variant.toKind.changes s) s t := by
  cases variant with
  | original =>
    apply (effect_frame h).widen
    · intro c hc hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · simp [Kind.changes, Kind.localChanges, Variant.toKind]
      · cases hm
    · intro address c hc ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact ha.elim
      · refine ⟨.mem (stackPtr s + 96) 88, by simp [Kind.changes, Kind.localChanges, Variant.toKind], ?_⟩
        obtain ⟨i, hi, he⟩ := ha
        exact ⟨i, by omega, he⟩
  | finalize =>
    apply (effect_frame h).widen
    · intro c hc hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · simp [Kind.changes, Kind.localChanges, Variant.toKind]
      · cases hm
    · intro address c hc ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact ha.elim
      · refine ⟨.mem (stackPtr s + 96) 88, by simp [Kind.changes, Kind.localChanges, Variant.toKind], ?_⟩
        obtain ⟨i, hi, he⟩ := ha
        exact ⟨i, by omega, he⟩
  | discard =>
    apply (effect_frame h).widen
    · intro c hc hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · simp [Kind.changes, Kind.localChanges, Variant.toKind]
      · cases hm
    · intro address c hc ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact ha.elim
      · refine ⟨.mem (stackPtr s + 120) 168, by simp [Kind.changes, Kind.localChanges, Variant.toKind], ?_⟩
        obtain ⟨i, hi, he⟩ := ha
        refine ⟨16 + i, by omega, ?_⟩
        rw [he]
        simp only [BitVec.ofNat_add, Variant.tailOffset, BitVec.add_assoc]
        exact congrArg (fun x : BitVec 64 ↦ stackPtr s + x)
          (BitVec.add_assoc (120 : BitVec 64) 16 (BitVec.ofNat 64 i))

theorem run {variant : Variant} [Bindings] {boundary : ReturnBoundary} {s : RamState}
    (hOutside : ¬ InProgram boundary.rip) (hr : ReadyToStep s)
    (hc : CodeIn Extracted.programImage s) (hp : Storage variant.toKind s)
    (hip : s.RIP = entry variant) :
    ∃ t, Transition boundary s t variant ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = variant.paddedRip ∧ AgreesExcept [.rip, .mem (stackPtr s + BitVec.ofNat 64 variant.tailOffset) 56] s t ∧
      Bytes t.external (stackPtr t + BitVec.ofNat 64 variant.tailOffset) 56 (fun _ ↦ 0) := by
  have hBytes : CodeIn (codeRange (entry variant) (bytes variant)) s := by
    cases variant with
    | original => exact program_text_slice hc 0xb87 72 (by decide +kernel)
    | finalize => exact program_text_slice hc 0x1217 72 (by decide +kernel)
    | discard => exact program_text_slice hc 0x1703 84 (by decide +kernel)
  obtain ⟨fuel, t, hRun, hReady, _, hEffect⟩ :=
    execution (variant := variant) boundary hOutside s hr hBytes ⟨hp, hip⟩
  have hsp : stackPtr t = stackPtr s :=
    (effect_frame hEffect).read (n := 64) (r := 4) (by simp)
  refine ⟨t, ⟨⟨fuel, hRun⟩, effect_agrees hEffect⟩, hReady,
    hEffect.codeIn (effect_avoids hp) hc, hEffect.rip, effect_frame hEffect, ?_⟩
  rw [hsp]
  exact effect_bytes hp hEffect

end Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Padding.Clear
