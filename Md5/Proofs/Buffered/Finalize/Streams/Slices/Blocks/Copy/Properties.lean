import Md5.Proofs.Buffered.Finalize.Streams.Slices.Blocks.Copy.Model
import Md5.Proofs.Buffered.Stores.Program

namespace Md5.Proofs.Buffered.Finalize.Streams.Slices.Blocks.Copy

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

theorem words_le (kind : Kind) : kind.words ≤ 8 := by cases kind <;> decide

theorem effect_word {update : Bool} {kind : Kind} {s t : RamState} (h : (effect (update := update) kind s).Holds s t)
    (word : Nat) (hw : word < kind.words) :
    (Operand.mem (stackPtr s + BitVec.ofNat 64 (104 + 8 * word)) : Operand 64).read t =
      (Operand.mem (stackPtr s + BitVec.ofNat 64 (16 + 8 * word)) : Operand 64).read s := by
  apply Write.allHold_iff.mp h.writes (wordWrite s word)
  change wordWrite s word ∈ _ ++ _
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨word, List.mem_range.mpr hw, rfl⟩

theorem effect_cover {update : Bool} {kind : Kind} {s : RamState} {c : Component}
    (hc : c ∈ (effect (update := update) kind s).components) {address : BitVec 64} (ha : c.Covers address) :
    Component.Covers (.mem (stackPtr s + 104) kind.length) address := by
  rcases Effect.mem_components.mp hc with ⟨w, hw, rfl⟩ | ⟨hf, rfl⟩ | rfl
  · simp only [effect, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_map] at hw
    rcases hw with (rfl | rfl | rfl | rfl | rfl) | ⟨word, hw, rfl⟩
    all_goals try exact ha.elim
    have hword : word < kind.words := List.mem_range.mp hw
    simp only [wordWrite, Write.component, Operand.component, Nat.reduceDiv] at ha
    obtain ⟨i, hi, rfl⟩ := ha
    refine ⟨8 * word + i, ?_, ?_⟩
    · unfold Kind.length
      omega
    · simp only [BitVec.ofNat_eq_ofNat]
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.add_assoc, ← BitVec.ofNat_add]
      congr 2
      omega
  · cases hf
  · exact ha.elim

theorem effect_agrees {update : Bool} {kind : Kind} {s t : RamState} (h : (effect (update := update) kind s).Holds s t) :
    AgreesExcept (changes kind s) s t := by
  apply h.agrees.widen
  · intro c hc hm
    cases c <;> simp_all [effect, Effect.components, wordWrite, Write.component,
      Operand.component, changes, Component.isMem, List.map_map]
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp
  · intro address c hc ha
    exact ⟨.mem (stackPtr s + 104) kind.length, by simp [changes], effect_cover (update := update) hc ha⟩

theorem effect_avoids {update : Bool} {kind : Kind} {s : RamState} (hs : Storage (streamKind update) s) :
    (effect (update := update) kind s).Avoids Extracted.programImage := by
  intro x hx c hc ha
  have hCover := effect_cover (update := update) hc ha
  have hEnd : 104 + kind.length ≤ 280 := by
    have := words_le kind
    unfold Kind.length
    omega
  exact hs.stackAvoids _ (hs.stackCover (kind := streamKind update) (by cases update <;> exact hEnd) hCover) (.inl ⟨x.2, hx⟩)

theorem effect_rsp {update : Bool} {kind : Kind} {s t : RamState} (h : (effect (update := update) kind s).Holds s t) :
    stackPtr t = stackPtr s :=
  (effect_agrees (update := update) h).read (n := 64) (r := 4) (by simp [changes])

theorem effect_arguments {update : Bool} {kind : Kind} {s t : RamState} (h : (effect (update := update) kind s).Holds s t) :
    (Operand.reg 7 : Operand 64).read t = stackPtr s ∧
    (Operand.reg 6 : Operand 64).read t = stackPtr s + 104 ∧
    (Operand.reg 2 : Operand 64).read t = 1 := by
  have hw := Write.allHold_iff.mp h.writes
  exact ⟨hw ⟨(.reg 7 : Operand 64), stackPtr s⟩ (by simp [effect]),
    hw ⟨(.reg 6 : Operand 64), stackPtr s + 104⟩ (by simp [effect]),
    hw ⟨(.reg 2 : Operand 64), 1⟩ (by simp [effect])⟩

theorem effect_copy {update : Bool} {kind : Kind} {s t : RamState}
    (hs : Storage (streamKind update) s) (h : (effect (update := update) kind s).Holds s t) (i : Nat) (hi : i < kind.length) :
    t.external[stackPtr s + 104 + BitVec.ofNat 64 i]? =
      s.external[stackPtr s + 16 + BitVec.ofNat 64 i]? := by
  have hw : i / 8 < kind.words := by
    unfold Kind.length at hi
    omega
  have hEnd : 104 + 8 * (i / 8) + 8 ≤ 280 := by have := words_le kind; omega
  have hr := hs.stackWritable (104 + 8 * (i / 8)) 8 (by cases update <;> exact hEnd)
  have ht : MemReadable t (stackPtr s + BitVec.ofNat 64 (104 + 8 * (i / 8))) 8 :=
    ⟨hr.low, fun j hj ↦ h.agrees.grow _ (hr.bytes j hj)⟩
  have hb := Stores.bytes_of_read_eq ht (effect_word (update := update) h (i / 8) hw) (i % 8) (by omega)
  have hAddress (offset : Nat) :
      stackPtr s + BitVec.ofNat 64 (offset + 8 * (i / 8)) + BitVec.ofNat 64 (i % 8) =
      stackPtr s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
    omega
  rw [hAddress 104] at hb
  change t.external[_]? = some (storedByte (memLoad s.external _ 64) (i % 8)) at hb
  rw [storedByte_memLoad _ _ _ (by omega : i % 8 < 64 / 8), hAddress 16] at hb
  have hsRead := (hs.stackWritable 16 kind.length
    (by have := words_le kind; cases update <;> change 16 + kind.length ≤ 280 <;> unfold Kind.length <;> omega)).readable
  have hSource := hsRead.mem i hi
  simp only [BitVec.ofNat_eq_ofNat] at hb hSource ⊢
  change t.external[_]? = some ((s.external[_]?).getD 0) at hb
  cases he : s.external[stackPtr s + BitVec.ofNat 64 16 + BitVec.ofNat 64 i]? with
  | none => simp only [he, Option.isSome_none] at hSource; contradiction
  | some byte => simpa only [he, Option.getD_some] using hb

theorem effect_bytes {update : Bool} {kind : Kind} {s t : RamState} {bytes : ByteArray}
    (hs : Storage (streamKind update) s) (h : (effect (update := update) kind s).Holds s t) (hSize : bytes.size = kind.length)
    (hBytes : (⟨(stackPtr s + 16).toNat, bytes.size⟩ : MemoryRegion).HasBytes
      s.external bytes) :
    (⟨(stackPtr s + 104).toNat, bytes.size⟩ : MemoryRegion).HasBytes t.external bytes := by
  refine ⟨by rfl, ?_⟩
  intro i
  have hi : i.val < kind.length := by simpa only [hSize] using i.isLt
  have hb := effect_copy (update := update) hs h i.val hi
  have hsByte := hBytes.2 i
  change s.external[BitVec.ofNat 64 ((stackPtr s + 16).toNat + i.val)]? = some bytes[i.val]
    at hsByte
  change t.external[BitVec.ofNat 64 ((stackPtr s + 104).toNat + i.val)]? = some bytes[i.val]
  simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hsByte ⊢
  exact hb.trans hsByte

theorem finalBlock_length {update : Bool} {s t : RamState} (h : (effect (update := update) .finalBlock s).Holds s t)
    (i : Nat) (hi : i < 8) :
    t.external[stackPtr s + 160 + BitVec.ofNat 64 i]? =
      s.external[stackPtr s + 160 + BitVec.ofNat 64 i]? := by
  apply (effect_agrees (update := update) h).byte
  intro c hc ha
  simp only [changes, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  obtain ⟨j, hj, he⟩ := ha
  have hj' : j < 56 := hj
  have hApart : OffsetsApart 104 56 160 8 := by unfold OffsetsApart; decide
  exact hApart.ne (stackPtr s) hj' hi (by decide) he.symm


theorem transition_agrees {update : Bool} {kind : Kind} {s t : RamState}
    (h : (effect (update := update) kind s).Holds s t) : AgreesExcept ((streamKind update).changes s) s t := by
  apply (effect_agrees (update := update) h).widen
  · intro c hc hm
    simp only [changes, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals cases update <;> simp_all [Finalize.Kind.changes, Finalize.Kind.workRegisters,
      Finalize.Kind.localChanges, streamKind, Component.isMem]
  · intro address c hc ha
    simp only [changes, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    refine ⟨.mem (stackPtr s) 168, by
      cases update <;> simp [Finalize.Kind.changes, Finalize.Kind.localChanges, streamKind], ?_⟩
    obtain ⟨i, hi, rfl⟩ := ha
    refine ⟨104 + i, ?_, ?_⟩
    · have := words_le kind
      change i < 8 * kind.words at hi
      omega
    · simp only [BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat]

theorem buffer_bytes {update : Bool} {kind : Kind} {s t : RamState} {buffer : Standards.RFC.MD5.Buffer}
    (h : (effect (update := update) kind s).Holds s t)
    (hb : (⟨(stackPtr s).toNat, 16⟩ : MemoryRegion).HasBytes
      s.external ⟨buffer.toBytes.toArray⟩) :
    (⟨(stackPtr t).toNat, 16⟩ : MemoryRegion).HasBytes
      t.external ⟨buffer.toBytes.toArray⟩ := by
  rw [effect_rsp (update := update) h]
  refine ⟨hb.1, ?_⟩
  intro i
  have hi : i.val < 16 := by simpa only [ByteArray.size, Vector.size_toArray] using i.isLt
  have ha : RangeApart (stackPtr s + 104) kind.length (stackPtr s) 16 := by
    simpa only [BitVec.add_zero, BitVec.ofNat_eq_ofNat] using
      (RangeApart.offsets (stackPtr s) (a := 104) (b := 0) (len := kind.length) (count := 16)
        (by have := words_le kind; unfold Kind.length; omega)
        (by decide) (Or.inr (by decide)))
  have he : t.external[stackPtr s + BitVec.ofNat 64 i.val]? =
      s.external[stackPtr s + BitVec.ofNat 64 i.val]? := by
    apply h.agrees.byte
    intro c hc hcov
    obtain ⟨j, hj, he⟩ := effect_cover (update := update) hc hcov
    exact ha j hj i.val hi he.symm
  have hb' := hb.2 i
  simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hb' ⊢
  exact he.trans hb'

end Md5.Proofs.Buffered.Finalize.Streams.Slices.Blocks.Copy
