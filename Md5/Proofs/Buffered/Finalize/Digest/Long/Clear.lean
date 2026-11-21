import Md5.Proofs.Buffered.Finalize.Digest.Long.Clear.Execution

namespace Md5.Proofs.Buffered.Finalize.Digest.Long.Clear

open X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block Md5.Spec.Program

theorem effect_word {s t : RamState} (h : (effect s).Holds s t) (j : Nat) (hj : j < 7) :
    (Operand.mem (stackPtr s + BitVec.ofNat 64 (24 + 8 * j)) : Operand 64).read t = 0 := by
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h.writes.1
  · exact h.writes.2.1
  · exact h.writes.2.2.1
  · exact h.writes.2.2.2.1
  · exact h.writes.2.2.2.2.1
  · exact h.writes.2.2.2.2.2.1
  · exact h.writes.2.2.2.2.2.2

theorem effect_bytes {s t : RamState} (hs : Storage .digest s) (h : (effect s).Holds s t) :
    Bytes t.external (stackPtr s + 24) 56 (fun _ ↦ 0) := by
  intro i hi
  have hReadable := Stores.readable_of_agrees
    (hs.stackWritable (24 + 8 * (i / 8)) 8 (by change 24 + 8 * (i / 8) + 8 ≤ 264; omega)).readable h.agrees
  have hBytes := Stores.bytes_of_read_eq hReadable (effect_word h (i / 8) (by omega))
  have hByte := hBytes (i % 8) (by omega)
  have he : stackPtr s + BitVec.ofNat 64 (24 + 8 * (i / 8)) + BitVec.ofNat 64 (i % 8) =
      stackPtr s + 24 + BitVec.ofNat 64 i := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    have hn : 24 + 8 * (i / 8) + i % 8 = 24 + i := by omega
    rw [hn, BitVec.ofNat_add, ← BitVec.add_assoc]
    rfl
  simpa [he, storedByte] using hByte

theorem effect_avoids {s : RamState} (h : Storage .digest s) :
    (effect s).Avoids Extracted.programImage := by
  intro x hx c hc ha
  simp only [effect, Effect.components, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, Write.component, Operand.component,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  all_goals apply h.stackAvoids x.1 _ (.inl ⟨x.2, hx⟩)
  · exact h.stackCover (by decide : 24 + 8 ≤ Kind.digest.stackBytes) ha
  · exact h.stackCover (by decide : 32 + 8 ≤ Kind.digest.stackBytes) ha
  · exact h.stackCover (by decide : 40 + 8 ≤ Kind.digest.stackBytes) ha
  · exact h.stackCover (by decide : 48 + 8 ≤ Kind.digest.stackBytes) ha
  · exact h.stackCover (by decide : 56 + 8 ≤ Kind.digest.stackBytes) ha
  · exact h.stackCover (by decide : 64 + 8 ≤ Kind.digest.stackBytes) ha
  · exact h.stackCover (by decide : 72 + 8 ≤ Kind.digest.stackBytes) ha

theorem run [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hStorage : Storage .digest s) (hOutside : ¬ InProgram boundary.rip)
    (hRip : s.RIP = 0x1001a0) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ (effect s).Holds s t := by
  have hBytes : CodeIn (codeRange 0x1001a0 bytes) s :=
    program_text_slice hCode 0x1a0 63 (by decide +kernel)
  obtain ⟨fuel, t, hRun, hReady', _, hEffect⟩ :=
    execution boundary hOutside s hReady hBytes ⟨hStorage, hRip⟩
  exact ⟨fuel, t, hRun, hReady', hEffect.codeIn (effect_avoids hStorage) hCode, hEffect⟩

def changes (s : RamState) : List Component := [.rip, .mem (stackPtr s + 24) 56]

theorem effect_agrees {s t : RamState} (h : (effect s).Holds s t) :
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
    all_goals refine ⟨.mem (stackPtr s + 24) 56, by simp [changes], ?_⟩
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

theorem effect_rsp {s t : RamState} (h : (effect s).Holds s t) :
    stackPtr t = stackPtr s := (effect_agrees h).read (n := 64) (r := 4) (by simp [changes])

theorem effect_buffer {s t : RamState} {buffer : Standards.RFC.MD5.Buffer}
    (h : (effect s).Holds s t)
    (hb : (⟨(stackPtr s + 8).toNat, 16⟩ : Prelude.MemoryRegion).HasBytes
      s.external ⟨buffer.toBytes.toArray⟩) :
    (⟨(stackPtr t + 8).toNat, 16⟩ : Prelude.MemoryRegion).HasBytes
      t.external ⟨buffer.toBytes.toArray⟩ := by
  rw [effect_rsp h]
  refine ⟨hb.1, ?_⟩
  intro i
  have hi : i.val < 16 := by simpa only [ByteArray.size, Vector.size_toArray] using i.isLt
  have he : t.external[stackPtr s + 8 + BitVec.ofNat 64 i.val]? =
      s.external[stackPtr s + 8 + BitVec.ofNat 64 i.val]? := by
    apply (effect_agrees h).byte
    intro c hc ha
    simp only [changes, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ha.elim
    · obtain ⟨j, hj, he⟩ := ha
      exact (OffsetsApart.ne (by unfold OffsetsApart; decide : OffsetsApart 8 16 24 56)
        (stackPtr s) hi hj (by decide)) he
  have hb' := hb.2 i
  simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hb' ⊢
  exact he.trans hb'

end Md5.Proofs.Buffered.Finalize.Digest.Long.Clear
