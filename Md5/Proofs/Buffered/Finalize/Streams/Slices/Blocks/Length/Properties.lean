import Md5.Proofs.Buffered.Finalize.Streams.Slices.Layout
import Md5.Proofs.Buffered.Finalize.Streams.Slices.Blocks.Length
import Md5.Proofs.Buffered.FinalizeReset.Length

namespace Md5.Proofs.Buffered.Finalize.Streams.Slices.Blocks.Length

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Block

theorem value_eq {s : RamState} {message : ByteArray}
    (hp : (Operand.reg 15 : Operand 64).read s = BitVec.ofNat 64 (message.size % 64))
    (hb : (Operand.reg 14 : Operand 64).read s = BitVec.ofNat 64 (message.size / 64)) :
    value s = BitVec.ofNat 64 (message.size * 8) := by
  have hp32 : (Operand.reg 15 : Operand 32).read s = BitVec.ofNat 32 (message.size % 64) := by
    change ((Operand.reg 15 : Operand 64).read s).setWidth 32 = _
    rw [hp, BitVec.setWidth_ofNat_of_le (by decide)]
  rw [value, positionValue, hp32, hb,
    FinalizeReset.Length.shift_position _ (by omega)]
  exact FinalizeReset.bitLength message.size

theorem effect_cover {update : Bool} {s : RamState} {c : Component}
    (hc : c ∈ (effect (update := update) s).components) {address : BitVec 64} (ha : c.Covers address) :
    Component.Covers (.mem (stackPtr s + 72) 8) address ∨
    Component.Covers (.mem (stackPtr s + 160) 8) address := by
  simp only [effect, Effect.components, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, Write.component, Operand.component, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  · exact Or.inl ha
  · exact Or.inr ha

theorem effect_avoids {update : Bool} {s : RamState} (h : Storage (streamKind update) s) :
    (effect (update := update) s).Avoids Extracted.programImage := by
  cases update with
  | false =>
    intro x hx c hc ha
    rcases effect_cover hc ha with ha | ha
    · exact h.stackAvoids x.1 (h.stackCover (by decide : 72 + 8 ≤ 280) ha) (.inl ⟨x.2, hx⟩)
    · exact h.stackAvoids x.1 (h.stackCover (by decide : 160 + 8 ≤ 280) ha) (.inl ⟨x.2, hx⟩)
  | true =>
    intro x hx c hc ha
    rcases effect_cover hc ha with ha | ha
    · exact h.stackAvoids x.1 (h.stackCover (by decide : 72 + 8 ≤ 280) ha) (.inl ⟨x.2, hx⟩)
    · exact h.stackAvoids x.1 (h.stackCover (by decide : 160 + 8 ≤ 280) ha) (.inl ⟨x.2, hx⟩)
theorem effect_rsp {update : Bool} {s t : RamState} (h : (effect (update := update) s).Holds s t) :
    stackPtr t = stackPtr s :=
  h.agrees.read (n := 64) (r := 4) (by simp [effect, Effect.components])

theorem effect_byte {update : Bool} {s t : RamState} (h : (effect (update := update) s).Holds s t) {offset len : Nat}
    (h72 : OffsetsApart 72 8 (BitVec.ofNat 64 offset) len)
    (h160 : OffsetsApart 160 8 (BitVec.ofNat 64 offset) len)
    (hbound : len + 8 < 2^64) {i : Nat} (hi : i < len) :
    t.external[stackPtr s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      s.external[stackPtr s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  apply h.agrees.byte
  intro c hc ha
  rcases effect_cover hc ha with ⟨j, hj, he⟩ | ⟨j, hj, he⟩
  · exact h72.ne (stackPtr s) hj hi (by omega) he.symm
  · exact h160.ne (stackPtr s) hj hi (by omega) he.symm

theorem run {update : Bool} [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hStorage : Storage (streamKind update) s) (hOutside : ¬ InProgram boundary.rip)
    (hRip : s.RIP = (BitVec.ofNat 64 (relocated update 0x10053d))) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ (effect (update := update) s).Holds s t := by
  cases update with
  | false =>
    have hBytes : CodeIn (codeRange 0x10053d bytes) s :=
      program_text_slice hCode 0x53d 24 (by decide +kernel)
    obtain ⟨fuel, t, hRun, hReady, _, hEffect⟩ :=
      execution (update := false) boundary hOutside s hReady hBytes ⟨hStorage, hRip⟩
    exact ⟨fuel, t, hRun, hReady, hEffect.codeIn (effect_avoids hStorage) hCode, hEffect⟩
  | true =>
    have hBytes : CodeIn (codeRange 0x101aed bytes) s :=
      program_text_slice hCode 0x1aed 24 (by decide +kernel)
    obtain ⟨fuel, t, hRun, hReady, _, hEffect⟩ :=
      execution (update := true) boundary hOutside s hReady hBytes ⟨hStorage, hRip⟩
    exact ⟨fuel, t, hRun, hReady, hEffect.codeIn (effect_avoids hStorage) hCode, hEffect⟩
theorem transition_agrees {update : Bool} {s t : RamState} (h : (effect (update := update) s).Holds s t) :
    AgreesExcept ((streamKind update).changes s) s t := by
  cases update with
  | false =>
    apply h.agrees.widen
    · intro c hc hm
      simp only [effect, Effect.components, List.map_cons, List.map_nil, List.cons_append,
        List.nil_append, Write.component, Operand.component, List.mem_cons,
        List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp_all [streamKind, Kind.changes, Kind.workRegisters, Kind.localChanges, Component.isMem]
    · intro address c hc ha
      rcases effect_cover hc ha with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
      · refine ⟨.mem (stackPtr s) 168, by simp [streamKind, Kind.changes, Kind.localChanges],
          72 + i, by omega, ?_⟩
        simp only [BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat]
      · refine ⟨.mem (stackPtr s) 168, by simp [streamKind, Kind.changes, Kind.localChanges],
          160 + i, by omega, ?_⟩
        simp only [BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat]
  | true =>
    apply h.agrees.widen
    · intro c hc hm
      simp only [effect, Effect.components, List.map_cons, List.map_nil, List.cons_append,
        List.nil_append, Write.component, Operand.component, List.mem_cons,
        List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp_all [streamKind, Kind.changes, Kind.workRegisters, Kind.localChanges, Component.isMem]
    · intro address c hc ha
      rcases effect_cover hc ha with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
      · refine ⟨.mem (stackPtr s) 168, by simp [streamKind, Kind.changes, Kind.localChanges],
          72 + i, by omega, ?_⟩
        simp only [BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat]
      · refine ⟨.mem (stackPtr s) 168, by simp [streamKind, Kind.changes, Kind.localChanges],
          160 + i, by omega, ?_⟩
        simp only [BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat]

end Md5.Proofs.Buffered.Finalize.Streams.Slices.Blocks.Length
