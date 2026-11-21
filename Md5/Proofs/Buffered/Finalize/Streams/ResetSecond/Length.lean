import Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Length.Execution

import Md5.Proofs.Buffered.FinalizeReset.Length

namespace Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Length

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Block

theorem value_eq [Bindings] {variant : Variant} {s : RamState} {message : ByteArray} (h : Padded message s variant) :
    value s = BitVec.ofNat 64 (message.size * 8) := by
  have hp32 : (Operand.reg 15 : Operand 32).read s = BitVec.ofNat 32 (message.size % 64) := by
    change ((Operand.reg 15 : Operand 64).read s).setWidth 32 = _
    rw [h.position, BitVec.setWidth_ofNat_of_le (by decide)]
  rw [value, positionValue, hp32, h.blocks,
    FinalizeReset.Length.shift_position _ (by omega)]
  exact FinalizeReset.bitLength message.size

theorem effect_cover {variant : Variant} {s : RamState} {c : Component}
    (hc : c ∈ (effect s variant).components) {address : BitVec 64} (ha : c.Covers address) :
    Component.Covers (.mem (stackPtr s + BitVec.ofNat 64 (variant.tailOffset + 56)) 8) address ∨
    Component.Covers (.mem (stackPtr s + BitVec.ofNat 64 (variant.blockOffset + 56)) 8) address := by
  simp only [effect, Effect.components, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, Write.component, Operand.component, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  · exact Or.inl ha
  · exact Or.inr ha

theorem effect_avoids {variant : Variant} {s : RamState} (h : Storage variant.toKind s) :
    (effect s variant).Avoids Extracted.programImage := by
  intro x hx c hc ha
  rcases effect_cover hc ha with ha | ha
  · exact h.stackAvoids x.1 (h.stackCover (by cases variant <;> decide : variant.tailOffset + 56 + 8 ≤ variant.toKind.stackBytes) ha) (.inl ⟨x.2, hx⟩)
  · exact h.stackAvoids x.1 (h.stackCover (by cases variant <;> decide : variant.blockOffset + 56 + 8 ≤ variant.toKind.stackBytes) ha) (.inl ⟨x.2, hx⟩)

theorem effect_rsp {variant : Variant} {s t : RamState} (h : (effect s variant).Holds s t) :
    stackPtr t = stackPtr s :=
  h.agrees.read (n := 64) (r := 4) (by simp [effect, Effect.components])

theorem effect_agrees {variant : Variant} {s t : RamState} (h : (effect s variant).Holds s t) :
    AgreesExcept (variant.toKind.changes s) s t := by
  apply h.agrees.widen
  · intro c hc hm
    simp only [effect, Effect.components, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, Write.component, Operand.component, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals cases variant <;> simp_all [Variant.toKind, Component.isMem, Kind.changes, Kind.workRegisters, Kind.localChanges]
  · intro address c hc ha
    rcases effect_cover hc ha with ⟨i, hi, he⟩ | ⟨i, hi, he⟩
    · cases variant
      · refine ⟨.mem (stackPtr s + 96) 88, by
          simp [Variant.toKind, Kind.changes, Kind.localChanges], 56 + i, by omega, ?_⟩
        rw [he]
        simp only [Variant.tailOffset, BitVec.ofNat_add, BitVec.add_assoc] <;>
          congr 1 <;> simp only [← BitVec.add_assoc] <;> rfl
      · refine ⟨.mem (stackPtr s + 96) 88, by
          simp [Variant.toKind, Kind.changes, Kind.localChanges], 56 + i, by omega, ?_⟩
        rw [he]
        simp only [Variant.tailOffset, BitVec.ofNat_add, BitVec.add_assoc] <;>
          congr 1 <;> simp only [← BitVec.add_assoc] <;> rfl
      · refine ⟨.mem (stackPtr s + 120) 168, by
          simp [Variant.toKind, Kind.changes, Kind.localChanges], 72 + i, by omega, ?_⟩
        rw [he]
        simp only [Variant.tailOffset, BitVec.ofNat_add, BitVec.add_assoc] <;>
          congr 1 <;> simp only [← BitVec.add_assoc] <;> rfl
    · cases variant
      · refine ⟨.mem (stackPtr s + 216) 80, by
          simp [Variant.toKind, Kind.changes, Kind.localChanges], 72 + i, by omega, ?_⟩
        rw [he]
        simp only [Variant.blockOffset, BitVec.ofNat_add, BitVec.add_assoc] <;>
          congr 1 <;> simp only [← BitVec.add_assoc] <;> rfl
      · refine ⟨.mem (stackPtr s + 216) 80, by
          simp [Variant.toKind, Kind.changes, Kind.localChanges], 72 + i, by omega, ?_⟩
        rw [he]
        simp only [Variant.blockOffset, BitVec.ofNat_add, BitVec.add_assoc] <;>
          congr 1 <;> simp only [← BitVec.add_assoc] <;> rfl
      · refine ⟨.mem (stackPtr s + 120) 168, by
          simp [Variant.toKind, Kind.changes, Kind.localChanges], 160 + i, by omega, ?_⟩
        rw [he]
        simp only [Variant.blockOffset, BitVec.ofNat_add, BitVec.add_assoc] <;>
          congr 1 <;> simp only [← BitVec.add_assoc] <;> rfl

theorem effect_byte {variant : Variant} {s t : RamState} (h : (effect s variant).Holds s t) {offset len : Nat}
    (h152 : OffsetsApart (BitVec.ofNat 64 (variant.tailOffset + 56)) 8 (BitVec.ofNat 64 offset) len)
    (h288 : OffsetsApart (BitVec.ofNat 64 (variant.blockOffset + 56)) 8 (BitVec.ofNat 64 offset) len)
    (hbound : len + 8 < 2^64) {i : Nat} (hi : i < len) :
    t.external[stackPtr s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      s.external[stackPtr s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  apply h.agrees.byte
  intro c hc ha
  rcases effect_cover hc ha with ⟨j, hj, he⟩ | ⟨j, hj, he⟩
  · exact h152.ne (stackPtr s) hj hi (by omega) he.symm
  · exact h288.ne (stackPtr s) hj hi (by omega) he.symm

theorem prefix_bytes [Bindings] {variant : Variant} {message : ByteArray} {s t : RamState} (h : Padded message s variant)
    (he : (effect s variant).Holds s t) :
    Bytes t.external (stackPtr t + BitVec.ofNat 64 (variant.tailOffset)) 56
      (fun i ↦ if message.size % 64 < 56 then (firstBlock message)[i]! else 0) := by
  rw [effect_rsp he]
  intro i hi
  exact (effect_byte he (offset := variant.tailOffset) (by cases variant <;> (unfold OffsetsApart; decide))
    (by cases variant <;> (unfold OffsetsApart; decide)) (by decide) hi).trans
    (h.prefixBytes i hi)

theorem buffer_bytes [Bindings] {variant : Variant} {message : ByteArray} {s t : RamState} (h : Padded message s variant)
    (he : (effect s variant).Holds s t) :
    (⟨(stackPtr t).toNat + (variant.resultOffset), 16⟩ : MemoryRegion).HasBytes t.external
      ⟨(paddedBuffer message).toBytes.toArray⟩ := by
  rw [effect_rsp he]
  refine ⟨h.buffer.1, ?_⟩
  intro i
  have hi : i.val < 16 := by simpa only [ByteArray.size, Vector.size_toArray] using i.isLt
  have hb := h.buffer.2 i
  change t.external[BitVec.ofNat 64 ((stackPtr s).toNat + (variant.resultOffset) + i.val)]? = _
  change s.external[BitVec.ofNat 64 ((stackPtr s).toNat + (variant.resultOffset) + i.val)]? = _ at hb
  simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hb ⊢
  rw [effect_byte he (by cases variant <;> (unfold OffsetsApart; decide) : OffsetsApart (BitVec.ofNat 64 (variant.tailOffset + 56)) 8 (BitVec.ofNat 64 variant.resultOffset) 16)
    (by cases variant <;> (unfold OffsetsApart; decide) : OffsetsApart (BitVec.ofNat 64 (variant.blockOffset + 56)) 8 (BitVec.ofNat 64 variant.resultOffset) 16) (by decide) hi]
  exact hb

theorem length_bytes [Bindings] {variant : Variant} {message : ByteArray} {s t : RamState} (h : Padded message s variant)
    (he : (effect s variant).Holds s t) :
    Bytes t.external (stackPtr t + BitVec.ofNat 64 (variant.blockOffset + 56)) 8
      (storedByte (BitVec.ofNat 64 (message.size * 8))) := by
  rw [effect_rsp he]
  apply Stores.bytes_of_read_eq
    (Stores.readable_of_agrees (h.toStorage.stackWritable (variant.blockOffset + 56) 8 (by cases variant <;> decide)).readable he.agrees)
  exact he.writes.2.2.2.trans (value_eq h)

theorem run [Bindings] {variant : Variant} {s : RamState} {boundary : ReturnBoundary} {message : ByteArray}
    (hOutside : ¬ InProgram boundary.rip) (h : Padded message s variant) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ (effect s variant).Holds s t := by
  have hBytes : CodeIn (codeRange variant.paddedRip (bytes variant)) s := by
    cases variant
    · exact program_text_slice h.code 0xbcf 27 (by decide +kernel)
    · exact program_text_slice h.code 0x125f 27 (by decide +kernel)
    · exact program_text_slice h.code 0x1757 27 (by decide +kernel)
  obtain ⟨fuel, t, hRun, hReady, _, hEffect⟩ :=
    execution boundary hOutside s h.ready hBytes ⟨h.toStorage, h.rip⟩
  exact ⟨fuel, t, hRun, hReady, hEffect.codeIn (effect_avoids h.toStorage) h.code, hEffect⟩

end Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Length
