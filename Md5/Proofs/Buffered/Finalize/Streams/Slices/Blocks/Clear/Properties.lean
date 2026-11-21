import Md5.Proofs.Buffered.Finalize.Streams.Slices.Layout
import Md5.Proofs.Buffered.Finalize.Streams.Slices.Blocks.Clear

namespace Md5.Proofs.Buffered.Finalize.Streams.Slices.Blocks.Clear

open X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block Md5.Spec.Program

theorem effect_word {update : Bool} {s t : RamState} (h : (effect (update := update) s).Holds s t) (j : Nat) (hj : j < 7) :
    (Operand.mem (stackPtr s + BitVec.ofNat 64 (16 + 8 * j)) : Operand 64).read t = 0 := by
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h.writes.1
  · exact h.writes.2.1
  · exact h.writes.2.2.1
  · exact h.writes.2.2.2.1
  · exact h.writes.2.2.2.2.1
  · exact h.writes.2.2.2.2.2.1
  · exact h.writes.2.2.2.2.2.2

theorem effect_bytes {update : Bool} {s t : RamState} (hs : Storage (streamKind update) s) (h : (effect (update := update) s).Holds s t) :
    Bytes t.external (stackPtr s + 16) 56 (fun _ ↦ 0) := by
  cases update with
  | false =>
    intro i hi
    have hReadable := Stores.readable_of_agrees
      (hs.stackWritable (16 + 8 * (i / 8)) 8
        (by change 16 + 8 * (i / 8) + 8 ≤ 280; omega)).readable h.agrees
    have hBytes := Stores.bytes_of_read_eq hReadable (effect_word h (i / 8) (by omega))
    have hByte := hBytes (i % 8) (by omega)
    have he : stackPtr s + BitVec.ofNat 64 (16 + 8 * (i / 8)) + BitVec.ofNat 64 (i % 8) =
        stackPtr s + 16 + BitVec.ofNat 64 i := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      have hn : 16 + 8 * (i / 8) + i % 8 = 16 + i := by omega
      rw [hn, BitVec.ofNat_add, ← BitVec.add_assoc]
      rfl
    simpa [he, storedByte] using hByte
  | true =>
    intro i hi
    have hReadable := Stores.readable_of_agrees
      (hs.stackWritable (16 + 8 * (i / 8)) 8
        (by change 16 + 8 * (i / 8) + 8 ≤ 280; omega)).readable h.agrees
    have hBytes := Stores.bytes_of_read_eq hReadable (effect_word h (i / 8) (by omega))
    have hByte := hBytes (i % 8) (by omega)
    have he : stackPtr s + BitVec.ofNat 64 (16 + 8 * (i / 8)) + BitVec.ofNat 64 (i % 8) =
        stackPtr s + 16 + BitVec.ofNat 64 i := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      have hn : 16 + 8 * (i / 8) + i % 8 = 16 + i := by omega
      rw [hn, BitVec.ofNat_add, ← BitVec.add_assoc]
      rfl
    simpa [he, storedByte] using hByte
theorem effect_avoids {update : Bool} {s : RamState} (h : Storage (streamKind update) s) :
    (effect (update := update) s).Avoids Extracted.programImage := by
  cases update with
  | false =>
    intro x hx c hc ha
    simp only [effect, Effect.components, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, Write.component, Operand.component,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    all_goals apply h.stackAvoids x.1 _ (.inl ⟨x.2, hx⟩)
    · exact h.stackCover (by decide : 16 + 8 ≤ (streamKind false).stackBytes) ha
    · exact h.stackCover (by decide : 24 + 8 ≤ (streamKind false).stackBytes) ha
    · exact h.stackCover (by decide : 32 + 8 ≤ (streamKind false).stackBytes) ha
    · exact h.stackCover (by decide : 40 + 8 ≤ (streamKind false).stackBytes) ha
    · exact h.stackCover (by decide : 48 + 8 ≤ (streamKind false).stackBytes) ha
    · exact h.stackCover (by decide : 56 + 8 ≤ (streamKind false).stackBytes) ha
    · exact h.stackCover (by decide : 64 + 8 ≤ (streamKind false).stackBytes) ha
  | true =>
    intro x hx c hc ha
    simp only [effect, Effect.components, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, Write.component, Operand.component,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    all_goals apply h.stackAvoids x.1 _ (.inl ⟨x.2, hx⟩)
    · exact h.stackCover (by decide : 16 + 8 ≤ (streamKind true).stackBytes) ha
    · exact h.stackCover (by decide : 24 + 8 ≤ (streamKind true).stackBytes) ha
    · exact h.stackCover (by decide : 32 + 8 ≤ (streamKind true).stackBytes) ha
    · exact h.stackCover (by decide : 40 + 8 ≤ (streamKind true).stackBytes) ha
    · exact h.stackCover (by decide : 48 + 8 ≤ (streamKind true).stackBytes) ha
    · exact h.stackCover (by decide : 56 + 8 ≤ (streamKind true).stackBytes) ha
    · exact h.stackCover (by decide : 64 + 8 ≤ (streamKind true).stackBytes) ha
theorem run {update : Bool} [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hStorage : Storage (streamKind update) s) (hOutside : ¬ InProgram boundary.rip)
    (hRip : s.RIP = (BitVec.ofNat 64 (relocated update 0x1004fe))) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ (effect (update := update) s).Holds s t := by
  cases update with
  | false =>
    have hBytes : CodeIn (codeRange 0x1004fe bytes) s :=
      program_text_slice hCode 0x4fe 63 (by decide +kernel)
    obtain ⟨fuel, t, hRun, hReady', _, hEffect⟩ :=
      execution (update := false) boundary hOutside s hReady hBytes ⟨hStorage, hRip⟩
    exact ⟨fuel, t, hRun, hReady', hEffect.codeIn (effect_avoids hStorage) hCode, hEffect⟩
  | true =>
    have hBytes : CodeIn (codeRange 0x101aae bytes) s :=
      program_text_slice hCode 0x1aae 63 (by decide +kernel)
    obtain ⟨fuel, t, hRun, hReady', _, hEffect⟩ :=
      execution (update := true) boundary hOutside s hReady hBytes ⟨hStorage, hRip⟩
    exact ⟨fuel, t, hRun, hReady', hEffect.codeIn (effect_avoids hStorage) hCode, hEffect⟩

def changes (s : RamState) : List Component := [.rip, .mem (stackPtr s + 16) 56]

theorem effect_agrees {update : Bool} {s t : RamState} (h : (effect (update := update) s).Holds s t) :
    AgreesExcept (changes s) s t := by
  apply h.agrees.widen
  · intro c hc hm
    cases c <;> simp_all [effect, Effect.components, Write.component, Operand.component,
      changes, Component.isMem]
  · intro a c hc ha
    simp only [effect, Effect.components, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, Write.component, Operand.component,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    all_goals refine ⟨.mem (stackPtr s + 16) 56, by simp [changes], ?_⟩
    all_goals obtain ⟨i, hi, rfl⟩ := ha
    · exact ⟨i, by omega, rfl⟩
    · refine ⟨8 + i, by omega, ?_⟩
      simp only [BitVec.ofNat_add, ← BitVec.add_assoc]
      congr 1
      rw [BitVec.add_assoc]
      rfl
    · refine ⟨16 + i, by omega, ?_⟩
      simp only [BitVec.ofNat_add, ← BitVec.add_assoc]
      congr 1
      rw [BitVec.add_assoc]
      rfl
    · refine ⟨24 + i, by omega, ?_⟩
      simp only [BitVec.ofNat_add, ← BitVec.add_assoc]
      congr 1
      rw [BitVec.add_assoc]
      rfl
    · refine ⟨32 + i, by omega, ?_⟩
      simp only [BitVec.ofNat_add, ← BitVec.add_assoc]
      congr 1
      rw [BitVec.add_assoc]
      rfl
    · refine ⟨40 + i, by omega, ?_⟩
      simp only [BitVec.ofNat_add, ← BitVec.add_assoc]
      congr 1
      rw [BitVec.add_assoc]
      rfl
    · refine ⟨48 + i, by omega, ?_⟩
      simp only [BitVec.ofNat_add, ← BitVec.add_assoc]
      congr 1
      rw [BitVec.add_assoc]
      rfl

theorem effect_rsp {update : Bool} {s t : RamState} (h : (effect (update := update) s).Holds s t) :
    stackPtr t = stackPtr s := (effect_agrees h).read (n := 64) (r := 4) (by simp [changes])

end Md5.Proofs.Buffered.Finalize.Streams.Slices.Blocks.Clear
