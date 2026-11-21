import Md5.Proofs.Buffered.Finalize.Streams.Slices.Blocks.Copy.Parts
import Md5.Proofs.Buffered.Finalize.Streams.Slices.Blocks.Copy.Properties

namespace Md5.Proofs.Buffered.Finalize.Streams.Slices.Blocks.Copy

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Block

theorem part_memory_index {update : Bool} {kind : Kind} {part : Part} {s : RamState} {c : Component}
    (hc : c ∈ (partEffect (update := update) kind part s).components) {address : BitVec 64}
    (ha : c.Covers address) :
    ∃ j < 8, (part = .high → 4 ≤ j) ∧ (part = .low → j < 4) ∧
      Component.Covers (.mem (stackPtr s + BitVec.ofNat 64 (104 + 8 * j)) 8) address := by
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

theorem source_read {update : Bool} {kind : Kind} {part : Part} {s t : RamState}
    (h : (partEffect (update := update) kind part s).Holds s t) {offset : Nat} (ho : offset + 8 ≤ 104) :
    (Operand.mem (stackPtr s + BitVec.ofNat 64 offset) : Operand 64).read t =
      (Operand.mem (stackPtr s + BitVec.ofNat 64 offset) : Operand 64).read s := by
  apply memLoad_congr
  intro i hi
  change (t.external[_]?).getD 0 = (s.external[_]?).getD 0
  rw [h.agrees.byte (fun c hc ha ↦ ?_)]
  obtain ⟨j, hj, _, _, k, hk, he⟩ := part_memory_index (update := update) hc ha
  exact RangeApart.offsets (stackPtr s) (by omega) (by omega)
    (Or.inl (by omega)) i hi k hk he

theorem high_read_low {update : Bool} {kind : Kind} {s t : RamState}
    (h : (partEffect (update := update) kind .low s).Holds s t) {word : Nat} (hlo : 4 ≤ word) (hhi : word < 8) :
    (Operand.mem (stackPtr s + BitVec.ofNat 64 (104 + 8 * word)) : Operand 64).read t =
      (Operand.mem (stackPtr s + BitVec.ofNat 64 (104 + 8 * word)) : Operand 64).read s := by
  apply memLoad_congr
  intro i hi
  change (t.external[_]?).getD 0 = (s.external[_]?).getD 0
  rw [h.agrees.byte (fun c hc ha ↦ ?_)]
  obtain ⟨j, _, _, hj, k, hk, he⟩ := part_memory_index (update := update) hc ha
  have hj4 := hj rfl
  exact RangeApart.offsets (stackPtr s) (by omega) (by omega)
    (Or.inr (by omega)) i hi k hk he

theorem part_word_high {update : Bool} {kind : Kind} {s t : RamState}
    (h : (partEffect (update := update) kind .high s).Holds s t) {word : Nat}
    (hlo : 4 ≤ word) (hhi : word < kind.words) :
    (Operand.mem (stackPtr s + BitVec.ofNat 64 (104 + 8 * word)) : Operand 64).read t =
      (Operand.mem (stackPtr s + BitVec.ofNat 64 (16 + 8 * word)) : Operand 64).read s := by
  apply Write.allHold_iff.mp h.writes (wordWrite s word)
  cases kind
  · have hw : word = 4 ∨ word = 5 ∨ word = 6 ∨ word = 7 := by
      change word < 8 at hhi
      omega
    rcases hw with rfl | rfl | rfl | rfl <;> simp [partEffect]
  · have hw : word = 4 ∨ word = 5 ∨ word = 6 := by change word < 7 at hhi; omega
    rcases hw with rfl | rfl | rfl <;> simp [partEffect]

theorem part_word_low {update : Bool} {kind : Kind} {s t : RamState}
    (h : (partEffect (update := update) kind .low s).Holds s t) {word : Nat} (hhi : word < 4) :
    (Operand.mem (stackPtr s + BitVec.ofNat 64 (104 + 8 * word)) : Operand 64).read t =
      (Operand.mem (stackPtr s + BitVec.ofNat 64 (16 + 8 * word)) : Operand 64).read s := by
  apply Write.allHold_iff.mp h.writes (wordWrite s word)
  have hw : word = 0 ∨ word = 1 ∨ word = 2 ∨ word = 3 := by omega
  rcases hw with rfl | rfl | rfl | rfl <;> simp [partEffect]

theorem effect_combine {update : Bool} {kind : Kind} {s u v t : RamState}
    (hHigh : (partEffect (update := update) kind .high s).Holds s u)
    (hLow : (partEffect (update := update) kind .low u).Holds u v)
    (hArguments : (partEffect (update := update) kind .arguments v).Holds v t) :
    (effect (update := update) kind s).Holds s t := by
  have hsu := part_rsp (update := update) hHigh
  have hsv := (part_rsp (update := update) hLow).trans hsu
  have hmem : t.external = v.external := hArguments.agrees.external (by
    intro c hc a ha
    simp only [partEffect, Effect.components, List.map_cons, List.map_nil, List.append_nil,
      List.cons_append, List.nil_append, Write.component, Operand.component,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl <;> exact ha.elim)
  refine ⟨?_, ?_, trivial, ?_⟩
  · have hip := hArguments.rip
    cases update <;> cases kind <;> simpa [relocated, partEffect, Kind.partEntry, Kind.entry, Kind.partOffset,
      Kind.partLength, effect, Kind.exit] using hip
  · apply Write.allHold_iff.mpr
    intro w hw
    simp only [effect, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_map] at hw
    rcases hw with (rfl | rfl | rfl | rfl | rfl) | ⟨word, hw, rfl⟩
    · change (Operand.reg 0 : Operand 64).read t = _
      rw [hArguments.agrees.read (r := 0) (by simp [partEffect, Effect.components]),
        hLow.writes.1, hsu]
      exact source_read (update := update) hHigh (by decide : 16 + 8 ≤ 104)
    · change (Operand.reg 1 : Operand 64).read t = _
      rw [hArguments.agrees.read (r := 1) (by simp [partEffect, Effect.components]),
        hLow.writes.2.1, hsu]
      exact source_read (update := update) hHigh (by decide : 24 + 8 ≤ 104)
    · simpa only [hsv] using hArguments.writes.1
    · simpa only [hsv] using hArguments.writes.2.1
    · exact hArguments.writes.2.2
    · have hword : word < kind.words := List.mem_range.mp hw
      have hword8 : word < 8 := Nat.lt_of_lt_of_le hword (words_le kind)
      change memLoad t.external _ 64 = _
      rw [hmem]
      change (Operand.mem (stackPtr s + BitVec.ofNat 64 (104 + 8 * word)) : Operand 64).read v = _
      by_cases hlo : word < 4
      · have hh := part_word_low (update := update) hLow hlo
        rw [hsu] at hh
        exact hh.trans (source_read (update := update) hHigh (by omega))
      · have hh := high_read_low (update := update) hLow (by omega : 4 ≤ word) hword8
        rw [hsu] at hh
        exact hh.trans (part_word_high (update := update) hHigh (by omega) hword)
  · have ha := (hHigh.agrees.trans hLow.agrees).trans hArguments.agrees
    apply ha.mono
    intro c hc
    cases kind <;>
      simp only [partEffect, effect, Kind.words, List.range_succ, List.range_zero,
        wordWrite, Effect.components, List.map_cons, List.map_nil,
        List.append_nil, List.cons_append, List.nil_append, Write.component, Operand.component,
        List.mem_cons, List.not_mem_nil, or_false, hsu, hsv] at hc ⊢
    all_goals grind only

end Md5.Proofs.Buffered.Finalize.Streams.Slices.Blocks.Copy
