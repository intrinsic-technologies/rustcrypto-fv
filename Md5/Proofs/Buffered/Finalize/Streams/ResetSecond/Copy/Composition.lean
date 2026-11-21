import Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Copy.Parts
import Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Copy.Properties

namespace Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Copy

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Block

theorem part_memory_index {variant : Variant} {kind : Kind} {part : Part} {s : RamState} {c : Component}
    (hc : c ∈ (partEffect kind part s variant).components) {address : BitVec 64}
    (ha : c.Covers address) :
    ∃ j < 8, (part = .high → 4 ≤ j) ∧ (part = .low → j < 4) ∧
      Component.Covers (.mem (stackPtr s + BitVec.ofNat 64 ((variant.blockOffset) + 8 * j)) 8) address := by
  cases kind <;> cases part <;>
    simp only [partEffect, wordWrite, Effect.components, List.map_cons, List.map_nil,
      List.append_nil, List.cons_append, List.nil_append, Write.component, Operand.component,
      List.mem_cons, List.not_mem_nil, or_false] at hc
  · rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    · exact ⟨4, by decide, by decide, by decide, ha⟩
    · exact ⟨5, by decide, by decide, by decide, ha⟩
    · exact ⟨6, by decide, by decide, by decide, ha⟩
    · exact ⟨7, by decide, by decide, by decide, ha⟩
  · rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    · exact ⟨0, by decide, by decide, by decide, ha⟩
    · exact ⟨1, by decide, by decide, by decide, ha⟩
    · exact ⟨2, by decide, by decide, by decide, ha⟩
    · exact ⟨3, by decide, by decide, by decide, ha⟩
  · rcases hc with rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
  · rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    · exact ⟨4, by decide, by decide, by decide, ha⟩
    · exact ⟨5, by decide, by decide, by decide, ha⟩
    · exact ⟨6, by decide, by decide, by decide, ha⟩
  · rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    · exact ⟨0, by decide, by decide, by decide, ha⟩
    · exact ⟨1, by decide, by decide, by decide, ha⟩
    · exact ⟨2, by decide, by decide, by decide, ha⟩
    · exact ⟨3, by decide, by decide, by decide, ha⟩
  · rcases hc with rfl | rfl | rfl | rfl
    all_goals try exact ha.elim

theorem source_read {variant : Variant} {kind : Kind} {part : Part} {s t : RamState}
    (h : (partEffect kind part s variant).Holds s t) {offset : Nat} (ho : offset + 8 ≤ (variant.blockOffset)) :
    (Operand.mem (stackPtr s + BitVec.ofNat 64 offset) : Operand 64).read t =
      (Operand.mem (stackPtr s + BitVec.ofNat 64 offset) : Operand 64).read s := by
  have hLayout : variant.blockOffset ≤ 232 ∧ variant.tailOffset + 64 ≤ variant.blockOffset ∧
      variant.blockOffset + 64 ≤ variant.toKind.stackBytes := by cases variant <;> decide
  apply memLoad_congr
  intro i hi
  change (t.external[_]?).getD 0 = (s.external[_]?).getD 0
  rw [h.agrees.byte (fun c hc ha ↦ ?_)]
  obtain ⟨j, hj, _, _, k, hk, he⟩ := part_memory_index hc ha
  exact RangeApart.offsets (stackPtr s) (by omega) (by omega)
    (Or.inl (by omega)) i hi k hk he

theorem high_read_low {variant : Variant} {kind : Kind} {s t : RamState}
    (h : (partEffect kind .low s variant).Holds s t) {word : Nat} (hlo : 4 ≤ word) (hhi : word < 8) :
    (Operand.mem (stackPtr s + BitVec.ofNat 64 ((variant.blockOffset) + 8 * word)) : Operand 64).read t =
      (Operand.mem (stackPtr s + BitVec.ofNat 64 ((variant.blockOffset) + 8 * word)) : Operand 64).read s := by
  have hLayout : variant.blockOffset ≤ 232 ∧ variant.tailOffset + 64 ≤ variant.blockOffset ∧
      variant.blockOffset + 64 ≤ variant.toKind.stackBytes := by cases variant <;> decide
  apply memLoad_congr
  intro i hi
  change (t.external[_]?).getD 0 = (s.external[_]?).getD 0
  rw [h.agrees.byte (fun c hc ha ↦ ?_)]
  obtain ⟨j, _, _, hj, k, hk, he⟩ := part_memory_index hc ha
  have hj4 := hj rfl
  exact RangeApart.offsets (stackPtr s) (by omega) (by omega)
    (Or.inr (by omega)) i hi k hk he

theorem part_word_high {variant : Variant} {kind : Kind} {s t : RamState}
    (h : (partEffect kind .high s variant).Holds s t) {word : Nat}
    (hlo : 4 ≤ word) (hhi : word < kind.words) :
    (Operand.mem (stackPtr s + BitVec.ofNat 64 ((variant.blockOffset) + 8 * word)) : Operand 64).read t =
      (Operand.mem (stackPtr s + BitVec.ofNat 64 ((variant.tailOffset) + 8 * word)) : Operand 64).read s := by
  apply Write.allHold_iff.mp h.writes (wordWrite s word variant)
  cases kind
  · have hw : word = 4 ∨ word = 5 ∨ word = 6 ∨ word = 7 := by
      change word < 8 at hhi
      omega
    rcases hw with rfl | rfl | rfl | rfl <;> simp [partEffect]
  · have hw : word = 4 ∨ word = 5 ∨ word = 6 := by change word < 7 at hhi; omega
    rcases hw with rfl | rfl | rfl <;> simp [partEffect]

theorem part_word_low {variant : Variant} {kind : Kind} {s t : RamState}
    (h : (partEffect kind .low s variant).Holds s t) {word : Nat} (hhi : word < 4) :
    (Operand.mem (stackPtr s + BitVec.ofNat 64 ((variant.blockOffset) + 8 * word)) : Operand 64).read t =
      (Operand.mem (stackPtr s + BitVec.ofNat 64 ((variant.tailOffset) + 8 * word)) : Operand 64).read s := by
  apply Write.allHold_iff.mp h.writes (wordWrite s word variant)
  have hw : word = 0 ∨ word = 1 ∨ word = 2 ∨ word = 3 := by omega
  rcases hw with rfl | rfl | rfl | rfl <;> simp [partEffect]

theorem effect_combine {variant : Variant} {kind : Kind} {s u v t : RamState}
    (hHigh : (partEffect kind .high s variant).Holds s u)
    (hLow : (partEffect kind .low u variant).Holds u v)
    (hArguments : (partEffect kind .arguments v variant).Holds v t) :
    (effect kind s variant).Holds s t := by
  have hLayout : variant.blockOffset ≤ 232 ∧ variant.tailOffset + 64 ≤ variant.blockOffset ∧
      variant.blockOffset + 64 ≤ variant.toKind.stackBytes := by cases variant <;> decide
  have hsu := part_rsp hHigh
  have hsv := (part_rsp hLow).trans hsu
  have hmem : t.external = v.external := hArguments.agrees.external (by
    intro c hc a ha
    simp only [partEffect, Effect.components, List.map_cons, List.map_nil, List.append_nil,
      List.cons_append, List.nil_append, Write.component, Operand.component,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl <;> exact ha.elim)
  refine ⟨?_, ?_, trivial, ?_⟩
  · have hip := hArguments.rip
    cases variant <;> cases kind <;> simpa [Variant.toKind, Variant.tailOffset, Variant.blockOffset, Variant.resultOffset, partEffect, Kind.partEntry, Kind.entry, Kind.partOffset,
      Kind.partLength, effect, Kind.exit] using hip
  · apply Write.allHold_iff.mpr
    intro w hw
    simp only [effect, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_map] at hw
    rcases hw with (rfl | rfl | rfl | rfl | rfl) | ⟨word, hw, rfl⟩
    · change (Operand.reg 0 : Operand 64).read t = _
      rw [hArguments.agrees.read (r := 0) (by simp [partEffect, Effect.components]),
        hLow.writes.1, hsu]
      exact source_read hHigh (by cases variant <;> decide : (variant.tailOffset) + 8 ≤ (variant.blockOffset))
    · change (Operand.reg 1 : Operand 64).read t = _
      rw [hArguments.agrees.read (r := 1) (by simp [partEffect, Effect.components]),
        hLow.writes.2.1, hsu]
      exact source_read hHigh (by cases variant <;> decide : ((variant.tailOffset + 8)) + 8 ≤ (variant.blockOffset))
    · simpa only [hsv] using hArguments.writes.1
    · simpa only [hsv] using hArguments.writes.2.1
    · exact hArguments.writes.2.2
    · have hword : word < kind.words := List.mem_range.mp hw
      have hword8 : word < 8 := Nat.lt_of_lt_of_le hword (words_le kind)
      change memLoad t.external _ 64 = _
      rw [hmem]
      change (Operand.mem (stackPtr s + BitVec.ofNat 64 ((variant.blockOffset) + 8 * word)) : Operand 64).read v = _
      by_cases hlo : word < 4
      · have hh := part_word_low hLow hlo
        rw [hsu] at hh
        exact hh.trans (source_read hHigh (by omega))
      · have hh := high_read_low hLow (by omega : 4 ≤ word) hword8
        rw [hsu] at hh
        exact hh.trans (part_word_high hHigh (by omega) hword)
  · have ha := (hHigh.agrees.trans hLow.agrees).trans hArguments.agrees
    apply ha.mono
    intro c hc
    cases kind <;>
      simp only [partEffect, effect, Kind.words, List.range_succ, List.range_zero,
        wordWrite, Effect.components, List.map_cons, List.map_nil,
        List.append_nil, List.cons_append, List.nil_append, Write.component, Operand.component,
        List.mem_cons, List.not_mem_nil, or_false, hsu, hsv] at hc ⊢
    all_goals grind only

end Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Copy
