import Md5.Proofs.Buffered.Finalize.Digest.Long.Copy.Parts
import Md5.Proofs.Buffered.Finalize.Digest.Long.Copy.Properties

namespace Md5.Proofs.Buffered.Finalize.Digest.Long.Copy

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Block

theorem part_memory_index {part : Part} {s : RamState} {c : Component}
    (hc : c ∈ (partEffect part s).components) {address : BitVec 64}
    (ha : c.Covers address) :
    ∃ j < 8, (part = .high → 4 ≤ j) ∧ (part = .low → j < 4) ∧
      Component.Covers (.mem (stackPtr s + BitVec.ofNat 64 (112 + 8 * j)) 8) address := by
  cases part <;>
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

theorem source_read {part : Part} {s t : RamState}
    (h : (partEffect part s).Holds s t) {offset : Nat} (ho : offset + 8 ≤ 112) :
    (Operand.mem (stackPtr s + BitVec.ofNat 64 offset) : Operand 64).read t =
      (Operand.mem (stackPtr s + BitVec.ofNat 64 offset) : Operand 64).read s := by
  apply memLoad_congr
  intro i hi
  change (t.external[_]?).getD 0 = (s.external[_]?).getD 0
  rw [h.agrees.byte (fun c hc ha ↦ ?_)]
  obtain ⟨j, hj, _, _, k, hk, he⟩ := part_memory_index hc ha
  exact RangeApart.offsets (stackPtr s) (by omega) (by omega)
    (Or.inl (by omega)) i hi k hk he

theorem high_read_low {s t : RamState}
    (h : (partEffect .low s).Holds s t) {word : Nat} (hlo : 4 ≤ word) (hhi : word < 8) :
    (Operand.mem (stackPtr s + BitVec.ofNat 64 (112 + 8 * word)) : Operand 64).read t =
      (Operand.mem (stackPtr s + BitVec.ofNat 64 (112 + 8 * word)) : Operand 64).read s := by
  apply memLoad_congr
  intro i hi
  change (t.external[_]?).getD 0 = (s.external[_]?).getD 0
  rw [h.agrees.byte (fun c hc ha ↦ ?_)]
  obtain ⟨j, _, _, hj, k, hk, he⟩ := part_memory_index hc ha
  have hj4 := hj rfl
  exact RangeApart.offsets (stackPtr s) (by omega) (by omega)
    (Or.inr (by omega)) i hi k hk he

theorem part_word_high {s t : RamState}
    (h : (partEffect .high s).Holds s t) {word : Nat}
    (hlo : 4 ≤ word) (hhi : word < 8) :
    (Operand.mem (stackPtr s + BitVec.ofNat 64 (112 + 8 * word)) : Operand 64).read t =
      (Operand.mem (stackPtr s + BitVec.ofNat 64 (24 + 8 * word)) : Operand 64).read s := by
  apply Write.allHold_iff.mp h.writes (wordWrite s word)
  have hw : word = 4 ∨ word = 5 ∨ word = 6 ∨ word = 7 := by omega
  rcases hw with rfl | rfl | rfl | rfl <;> simp [partEffect]

theorem part_word_low {s t : RamState}
    (h : (partEffect .low s).Holds s t) {word : Nat} (hhi : word < 4) :
    (Operand.mem (stackPtr s + BitVec.ofNat 64 (112 + 8 * word)) : Operand 64).read t =
      (Operand.mem (stackPtr s + BitVec.ofNat 64 (24 + 8 * word)) : Operand 64).read s := by
  apply Write.allHold_iff.mp h.writes (wordWrite s word)
  have hw : word = 0 ∨ word = 1 ∨ word = 2 ∨ word = 3 := by omega
  rcases hw with rfl | rfl | rfl | rfl <;> simp [partEffect]

theorem effect_combine {s u v t : RamState}
    (hHigh : (partEffect .high s).Holds s u)
    (hLow : (partEffect .low u).Holds u v)
    (hArguments : (partEffect .arguments v).Holds v t) :
    (effect s).Holds s t := by
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
    simpa [partEffect, Part.entry, Part.offset, Part.length, effect] using hip
  · apply Write.allHold_iff.mpr
    intro w hw
    simp only [effect, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_map] at hw
    rcases hw with (rfl | rfl | rfl | rfl | rfl) | ⟨word, hw, rfl⟩
    · change (Operand.reg 0 : Operand 64).read t = _
      rw [hArguments.agrees.read (r := 0) (by simp [partEffect, Effect.components]),
        hLow.writes.1, hsu]
      exact source_read hHigh (by decide : 24 + 8 ≤ 112)
    · change (Operand.reg 1 : Operand 64).read t = _
      rw [hArguments.agrees.read (r := 1) (by simp [partEffect, Effect.components]),
        hLow.writes.2.1, hsu]
      exact source_read hHigh (by decide : 32 + 8 ≤ 112)
    · simpa only [hsv] using hArguments.writes.1
    · simpa only [hsv] using hArguments.writes.2.1
    · exact hArguments.writes.2.2
    · have hword : word < 8 := List.mem_range.mp hw
      have hword8 : word < 8 := hword
      change memLoad t.external _ 64 = _
      rw [hmem]
      change (Operand.mem (stackPtr s + BitVec.ofNat 64 (112 + 8 * word)) : Operand 64).read v = _
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
    simp only [partEffect, effect, List.range_succ, List.range_zero,
        wordWrite, Effect.components, List.map_cons, List.map_nil,
        List.append_nil, List.cons_append, List.nil_append, Write.component, Operand.component,
        List.mem_cons, List.not_mem_nil, or_false, hsu, hsv] at hc ⊢
    all_goals grind only

end Md5.Proofs.Buffered.Finalize.Digest.Long.Copy
