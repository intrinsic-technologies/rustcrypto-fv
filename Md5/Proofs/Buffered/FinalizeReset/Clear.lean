import Md5.Proofs.Buffered.FinalizeReset.Clear.Execution

namespace Md5.Proofs.Buffered.FinalizeReset.Clear

open X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block Md5.Spec.Program

theorem effect_word {variant : Variant} {s t : RamState} (h : (effect s variant).Holds s t) (j : Nat) (hj : j < 7) :
    (Operand.mem (stackPtr s + BitVec.ofNat 64 (8 + 8 * j)) : Operand 64).read t = 0 := by
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h.writes.1
  · exact h.writes.2.1
  · exact h.writes.2.2.1
  · exact h.writes.2.2.2.1
  · exact h.writes.2.2.2.2.1
  · exact h.writes.2.2.2.2.2.1
  · exact h.writes.2.2.2.2.2.2

theorem effect_bytes {variant : Variant} {s t : RamState} (hs : Storage s variant) (h : (effect s variant).Holds s t) :
    Bytes t.external (stackPtr s + 8) 56 (fun _ ↦ 0) := by
  intro i hi
  have hReadable := Stores.readable_of_agrees
    (Export.stackWritable hs (8 + 8 * (i / 8)) 8 (by have := variant.stackBytes_bounds; omega)).readable h.agrees
  have hBytes := Stores.bytes_of_read_eq hReadable (effect_word h (i / 8) (by have := variant.stackBytes_bounds; omega))
  have hByte := hBytes (i % 8) (by have := variant.stackBytes_bounds; omega)
  have he : stackPtr s + BitVec.ofNat 64 (8 + 8 * (i / 8)) + BitVec.ofNat 64 (i % 8) =
      stackPtr s + 8 + BitVec.ofNat 64 i := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    have hn : 8 + 8 * (i / 8) + i % 8 = 8 + i := by omega
    rw [hn, BitVec.ofNat_add, ← BitVec.add_assoc]
    rfl
  simpa [he, storedByte] using hByte

theorem effect_avoids {variant : Variant} {s : RamState} (h : Storage s variant) :
    (effect s variant).Avoids Extracted.programImage := by
  intro x hx c hc ha
  simp only [effect, Effect.components, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, Write.component, Operand.component,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  all_goals apply h.stackAvoids x.1 _ (.inl ⟨x.2, hx⟩)
  · exact Export.stack_cover h (by cases variant <;> decide : 8 + 8 ≤ variant.stackBytes) ha
  · exact Export.stack_cover h (by cases variant <;> decide : 16 + 8 ≤ variant.stackBytes) ha
  · exact Export.stack_cover h (by cases variant <;> decide : 24 + 8 ≤ variant.stackBytes) ha
  · exact Export.stack_cover h (by cases variant <;> decide : 32 + 8 ≤ variant.stackBytes) ha
  · exact Export.stack_cover h (by cases variant <;> decide : 40 + 8 ≤ variant.stackBytes) ha
  · exact Export.stack_cover h (by cases variant <;> decide : 48 + 8 ≤ variant.stackBytes) ha
  · exact Export.stack_cover h (by cases variant <;> decide : 56 + 8 ≤ variant.stackBytes) ha

theorem run {variant : Variant} [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hStorage : Storage s variant) (hOutside : ¬ InProgram boundary.rip)
    (hRip : s.RIP = (variant.address 0x100863)) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ (effect s variant).Holds s t := by
  have hBytes : CodeIn (codeRange (variant.address 0x100863) bytes) s :=
    by have haddr := program_text_slice hCode (0x863 + (if variant = .saved then 0 else 0x6b0)) 63 (by cases variant <;> decide +kernel); cases variant <;> exact haddr
  obtain ⟨fuel, t, hRun, hReady', _, hEffect⟩ :=
    execution boundary hOutside s hReady hBytes ⟨hStorage, hRip⟩
  exact ⟨fuel, t, hRun, hReady', hEffect.codeIn (effect_avoids hStorage) hCode, hEffect⟩

end Md5.Proofs.Buffered.FinalizeReset.Clear
