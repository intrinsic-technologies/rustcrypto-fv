import Md5.Proofs.Buffered.Finalize.Digest.Long.Copy.Model
import Md5.Proofs.Buffered.Stores.Program

namespace Md5.Proofs.Buffered.Finalize.Digest.Long.Copy

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

theorem effect_word {s t : RamState} (h : (effect s).Holds s t)
    (word : Nat) (hw : word < 8) :
    (Operand.mem (stackPtr s + BitVec.ofNat 64 (112 + 8 * word)) : Operand 64).read t =
      (Operand.mem (stackPtr s + BitVec.ofNat 64 (24 + 8 * word)) : Operand 64).read s := by
  apply Write.allHold_iff.mp h.writes (wordWrite s word)
  change wordWrite s word ∈ _ ++ _
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨word, List.mem_range.mpr hw, rfl⟩

theorem effect_cover {s : RamState} {c : Component}
    (hc : c ∈ (effect s).components) {address : BitVec 64} (ha : c.Covers address) :
    Component.Covers (.mem (stackPtr s + 112) 64) address := by
  rcases Effect.mem_components.mp hc with ⟨w, hw, rfl⟩ | ⟨hf, rfl⟩ | rfl
  · simp only [effect, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_map] at hw
    rcases hw with (rfl | rfl | rfl | rfl | rfl) | ⟨word, hw, rfl⟩
    all_goals try exact ha.elim
    have hword : word < 8 := List.mem_range.mp hw
    simp only [wordWrite, Write.component, Operand.component, Nat.reduceDiv] at ha
    obtain ⟨i, hi, rfl⟩ := ha
    refine ⟨8 * word + i, ?_, ?_⟩
    · omega
    · simp only [BitVec.ofNat_eq_ofNat]
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.add_assoc, ← BitVec.ofNat_add]
      congr 2
      omega
  · cases hf
  · exact ha.elim

theorem effect_agrees {s t : RamState} (h : (effect s).Holds s t) :
    AgreesExcept (changes s) s t := by
  apply h.agrees.widen
  · intro c hc hm
    cases c <;> simp_all [effect, Effect.components, wordWrite, Write.component,
      Operand.component, changes, Component.isMem, List.map_map]
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp
  · intro address c hc ha
    exact ⟨.mem (stackPtr s + 112) 64, by simp [changes], effect_cover hc ha⟩

theorem effect_avoids {s : RamState} (hs : Storage .digest s) :
    (effect s).Avoids Extracted.programImage := by
  intro x hx c hc ha
  have hCover := effect_cover hc ha
  have hEnd : 112 + 64 ≤ 264 := by
    decide
  exact hs.stackAvoids _ (hs.stackCover hEnd hCover) (.inl ⟨x.2, hx⟩)

theorem effect_rsp {s t : RamState} (h : (effect s).Holds s t) :
    stackPtr t = stackPtr s :=
  (effect_agrees h).read (n := 64) (r := 4) (by simp [changes])

theorem effect_arguments {s t : RamState} (h : (effect s).Holds s t) :
    (Operand.reg 7 : Operand 64).read t = stackPtr s + 8 ∧
    (Operand.reg 6 : Operand 64).read t = stackPtr s + 112 ∧
    (Operand.reg 2 : Operand 64).read t = 1 := by
  have hw := Write.allHold_iff.mp h.writes
  exact ⟨hw ⟨(.reg 7 : Operand 64), stackPtr s + 8⟩ (by simp [effect]),
    hw ⟨(.reg 6 : Operand 64), stackPtr s + 112⟩ (by simp [effect]),
    hw ⟨(.reg 2 : Operand 64), 1⟩ (by simp [effect])⟩

theorem effect_copy {s t : RamState}
    (hs : Storage .digest s) (h : (effect s).Holds s t) (i : Nat) (hi : i < 64) :
    t.external[stackPtr s + 112 + BitVec.ofNat 64 i]? =
      s.external[stackPtr s + 24 + BitVec.ofNat 64 i]? := by
  have hw : i / 8 < 8 := by
    omega
  have hEnd : 112 + 8 * (i / 8) + 8 ≤ 264 := by change 112 + 8 * (i / 8) + 8 ≤ 264; omega
  have hr := hs.stackWritable (112 + 8 * (i / 8)) 8 hEnd
  have ht : MemReadable t (stackPtr s + BitVec.ofNat 64 (112 + 8 * (i / 8))) 8 :=
    ⟨hr.low, fun j hj ↦ h.agrees.grow _ (hr.bytes j hj)⟩
  have hb := Stores.bytes_of_read_eq ht (effect_word h (i / 8) hw) (i % 8) (by omega)
  have hAddress (offset : Nat) :
      stackPtr s + BitVec.ofNat 64 (offset + 8 * (i / 8)) + BitVec.ofNat 64 (i % 8) =
      stackPtr s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
    omega
  rw [hAddress 112] at hb
  change t.external[_]? = some (storedByte (memLoad s.external _ 64) (i % 8)) at hb
  rw [storedByte_memLoad _ _ _ (by omega : i % 8 < 64 / 8), hAddress 24] at hb
  have hsRead := (hs.stackWritable 24 64 (by decide)).readable
  have hSource := hsRead.mem i hi
  simp only [BitVec.ofNat_eq_ofNat] at hb hSource ⊢
  change t.external[_]? = some ((s.external[_]?).getD 0) at hb
  cases he : s.external[stackPtr s + BitVec.ofNat 64 24 + BitVec.ofNat 64 i]? with
  | none => simp only [he, Option.isSome_none] at hSource; contradiction
  | some byte => simpa only [he, Option.getD_some] using hb

theorem effect_bytes {s t : RamState} {bytes : ByteArray}
    (hs : Storage .digest s) (h : (effect s).Holds s t) (hSize : bytes.size = 64)
    (hBytes : (⟨(stackPtr s + 24).toNat, bytes.size⟩ : MemoryRegion).HasBytes
      s.external bytes) :
    (⟨(stackPtr s + 112).toNat, bytes.size⟩ : MemoryRegion).HasBytes t.external bytes := by
  refine ⟨by rfl, ?_⟩
  intro i
  have hi : i.val < 64 := by simpa only [hSize] using i.isLt
  have hb := effect_copy hs h i.val hi
  have hsByte := hBytes.2 i
  change s.external[BitVec.ofNat 64 ((stackPtr s + 24).toNat + i.val)]? = some bytes[i.val]
    at hsByte
  change t.external[BitVec.ofNat 64 ((stackPtr s + 112).toNat + i.val)]? = some bytes[i.val]
  simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hsByte ⊢
  exact hb.trans hsByte

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
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    obtain ⟨j, hj, he⟩ := ha
    exact (OffsetsApart.ne (by unfold OffsetsApart; decide : OffsetsApart 8 16 112 64)
        (stackPtr s) hi hj (by decide)) he
  have hb' := hb.2 i
  simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hb' ⊢
  exact he.trans hb'

end Md5.Proofs.Buffered.Finalize.Digest.Long.Copy
