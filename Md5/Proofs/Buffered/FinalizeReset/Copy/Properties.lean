import Md5.Proofs.Buffered.FinalizeReset.Copy.Model
import Md5.Proofs.Buffered.FinalizeReset.Export.Geometry
import Md5.Proofs.Buffered.Stores.Program

namespace Md5.Proofs.Buffered.FinalizeReset.Copy

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

theorem words_le (kind : Kind) : kind.words ≤ 8 := by cases kind <;> decide

theorem effect_word {variant : Variant} {kind : Kind} {s t : RamState} (h : (effect kind s variant).Holds s t)
    (word : Nat) (hw : word < kind.words) :
    (Operand.mem (stackPtr s + BitVec.ofNat 64 (96 + 8 * word)) : Operand 64).read t =
      (Operand.mem (stackPtr s + BitVec.ofNat 64 (8 + 8 * word)) : Operand 64).read s := by
  apply Write.allHold_iff.mp h.writes (wordWrite s word)
  change wordWrite s word ∈ _ ++ _
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨word, List.mem_range.mpr hw, rfl⟩

theorem effect_cover {variant : Variant} {kind : Kind} {s : RamState} {c : Component}
    (hc : c ∈ (effect kind s variant).components) {address : BitVec 64} (ha : c.Covers address) :
    Component.Covers (.mem (stackPtr s + 96) kind.length) address := by
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

theorem effect_agrees {variant : Variant} {kind : Kind} {s t : RamState} (h : (effect kind s variant).Holds s t) :
    AgreesExcept (changes kind s) s t := by
  apply h.agrees.widen
  · intro c hc hm
    cases c <;> simp_all [effect, Effect.components, wordWrite, Write.component,
      Operand.component, changes, Component.isMem, List.map_map]
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp
  · intro address c hc ha
    exact ⟨.mem (stackPtr s + 96) kind.length, by simp [changes], effect_cover hc ha⟩

theorem effect_avoids {variant : Variant} {kind : Kind} {s : RamState} (hs : Storage s variant) :
    (effect kind s variant).Avoids Extracted.programImage := by
  intro x hx c hc ha
  have hCover := effect_cover hc ha
  have hEnd : 96 + kind.length ≤ variant.stackBytes := by
    have := words_le kind
    unfold Kind.length
    cases variant <;> simp only [Variant.stackBytes] <;> omega
  exact hs.stackAvoids _ (Export.stack_cover hs hEnd hCover) (.inl ⟨x.2, hx⟩)

theorem effect_rsp {variant : Variant} {kind : Kind} {s t : RamState} (h : (effect kind s variant).Holds s t) :
    stackPtr t = stackPtr s :=
  (effect_agrees h).read (n := 64) (r := 4) (by simp [changes])

theorem effect_arguments {variant : Variant} {kind : Kind} {s t : RamState} (h : (effect kind s variant).Holds s t) :
    (Operand.reg 7 : Operand 64).read t = stackPtr s + 0xe8 ∧
    (Operand.reg 6 : Operand 64).read t = stackPtr s + 0x60 ∧
    (Operand.reg 2 : Operand 64).read t = 1 := by
  have hw := Write.allHold_iff.mp h.writes
  exact ⟨hw ⟨(.reg 7 : Operand 64), stackPtr s + 0xe8⟩ (by simp [effect]),
    hw ⟨(.reg 6 : Operand 64), stackPtr s + 0x60⟩ (by simp [effect]),
    hw ⟨(.reg 2 : Operand 64), 1⟩ (by simp [effect])⟩

theorem effect_copy {variant : Variant} {kind : Kind} {s t : RamState}
    (hs : Storage s variant) (h : (effect kind s variant).Holds s t) (i : Nat) (hi : i < kind.length) :
    t.external[stackPtr s + 96 + BitVec.ofNat 64 i]? =
      s.external[stackPtr s + 8 + BitVec.ofNat 64 i]? := by
  have hw : i / 8 < kind.words := by
    unfold Kind.length at hi
    omega
  have hEnd : 96 + 8 * (i / 8) + 8 ≤ variant.stackBytes := by have := words_le kind; cases variant <;> simp only [Variant.stackBytes] <;> omega
  have hr := Export.stackWritable hs (96 + 8 * (i / 8)) 8 hEnd
  have ht : MemReadable t (stackPtr s + BitVec.ofNat 64 (96 + 8 * (i / 8))) 8 :=
    ⟨hr.low, fun j hj ↦ h.agrees.grow _ (hr.bytes j hj)⟩
  have hb := Stores.bytes_of_read_eq ht (effect_word h (i / 8) hw) (i % 8) (by omega)
  have hAddress (offset : Nat) :
      stackPtr s + BitVec.ofNat 64 (offset + 8 * (i / 8)) + BitVec.ofNat 64 (i % 8) =
      stackPtr s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
    omega
  rw [hAddress 96] at hb
  change t.external[_]? = some (storedByte (memLoad s.external _ 64) (i % 8)) at hb
  rw [storedByte_memLoad _ _ _ (by omega : i % 8 < 64 / 8), hAddress 8] at hb
  have hsRead := (Export.stackWritable hs 8 kind.length
    (by have := words_le kind; unfold Kind.length; cases variant <;> simp only [Variant.stackBytes] <;> omega)).readable
  have hSource := hsRead.mem i hi
  simp only [BitVec.ofNat_eq_ofNat] at hb hSource ⊢
  change t.external[_]? = some ((s.external[_]?).getD 0) at hb
  cases he : s.external[stackPtr s + BitVec.ofNat 64 8 + BitVec.ofNat 64 i]? with
  | none => simp only [he, Option.isSome_none] at hSource; contradiction
  | some byte => simpa only [he, Option.getD_some] using hb

theorem effect_bytes {variant : Variant} {kind : Kind} {s t : RamState} {bytes : ByteArray}
    (hs : Storage s variant) (h : (effect kind s variant).Holds s t) (hSize : bytes.size = kind.length)
    (hBytes : (⟨(stackPtr s + 8).toNat, bytes.size⟩ : MemoryRegion).HasBytes
      s.external bytes) :
    (⟨(stackPtr s + 96).toNat, bytes.size⟩ : MemoryRegion).HasBytes t.external bytes := by
  refine ⟨by rfl, ?_⟩
  intro i
  have hi : i.val < kind.length := by simpa only [hSize] using i.isLt
  have hb := effect_copy hs h i.val hi
  have hsByte := hBytes.2 i
  change s.external[BitVec.ofNat 64 ((stackPtr s + 8).toNat + i.val)]? = some bytes[i.val]
    at hsByte
  change t.external[BitVec.ofNat 64 ((stackPtr s + 96).toNat + i.val)]? = some bytes[i.val]
  simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hsByte ⊢
  exact hb.trans hsByte

theorem finalBlock_length {variant : Variant} {s t : RamState} (h : (effect .finalBlock s variant).Holds s t)
    (i : Nat) (hi : i < 8) :
    t.external[stackPtr s + 152 + BitVec.ofNat 64 i]? =
      s.external[stackPtr s + 152 + BitVec.ofNat 64 i]? := by
  apply (effect_agrees h).byte
  intro c hc ha
  simp only [changes, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  obtain ⟨j, hj, he⟩ := ha
  have hj' : j < 56 := hj
  have hApart : OffsetsApart 96 56 152 8 := by unfold OffsetsApart; decide
  exact hApart.ne (stackPtr s) hj' hi (by decide) he.symm

end Md5.Proofs.Buffered.FinalizeReset.Copy
