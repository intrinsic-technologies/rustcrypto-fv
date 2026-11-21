import Md5.Proofs.Buffered.FinalizeReset.Export.Model
import Md5.Proofs.Memory.Basic

namespace Md5.Proofs.Buffered.FinalizeReset.Export

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

theorem stackAddress_toNat {variant : Variant} {s : RamState} (h : Storage s variant) (offset : Nat)
    (ho : offset ≤ variant.stackBytes) :
    (stackPtr s + BitVec.ofNat 64 offset).toNat = (stackPtr s).toNat + offset := by
  have hh := h.stackHigh
  unfold userAddressLimit at hh
  rw [BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : offset < 2^64), Nat.mod_eq_of_lt (by omega)]

theorem stackBounded {variant : Variant} {s : RamState} (h : Storage s variant) : (stackRegion s variant).Bounded := by
  have := h.stackHigh
  have := h.stackLow
  change (stackPtr s).toNat - 320 + (320 + variant.stackBytes) < userAddressLimit
  omega

theorem stackContains {variant : Variant} {s : RamState} (h : Storage s variant) (offset : Nat)
    (ho : offset < variant.stackBytes) :
    (stackRegion s variant).Contains (stackPtr s + BitVec.ofNat 64 offset).toNat := by
  rw [stackAddress_toNat h offset (by omega)]
  have := h.stackLow
  change (stackPtr s).toNat - 320 ≤ _ ∧ _ < (stackPtr s).toNat - 320 + (320 + variant.stackBytes)
  omega

theorem stackWritable {variant : Variant} {s : RamState} (h : Storage s variant) (offset len : Nat)
    (he : offset + len ≤ variant.stackBytes) :
    Md5.Proofs.Memory.MemWritable s (stackPtr s + BitVec.ofNat 64 offset) len := by
  apply Md5.Proofs.Memory.MemWritable.of_region (stackBounded h) h.stackAllocated
    (fun a ha hp ↦ h.stackAvoids a ha (.inr hp))
  · rw [stackAddress_toNat h offset (by omega)]
    change (stackPtr s).toNat - 320 ≤ _
    omega
  · rw [stackAddress_toNat h offset (by omega)]
    have := h.stackLow
    change _ ≤ (stackPtr s).toNat - 320 + (320 + variant.stackBytes)
    omega

theorem outputAddress_toNat {variant : Variant} {s : RamState} (h : Storage s variant) (offset : Nat)
    (ho : offset ≤ 16) :
    (outputAddress s + BitVec.ofNat 64 offset).toNat = (outputAddress s).toNat + offset := by
  have hh := h.outputBounded
  change (outputAddress s).toNat + 16 < 2^32 at hh
  rw [BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : offset < 2^64), Nat.mod_eq_of_lt (by omega)]

theorem outputWritable {variant : Variant} {s : RamState} (h : Storage s variant) (offset len : Nat)
    (he : offset + len ≤ 16) :
    Md5.Proofs.Memory.MemWritable s (outputAddress s + BitVec.ofNat 64 offset) len := by
  apply Md5.Proofs.Memory.MemWritable.of_region h.outputBounded h.outputAllocated
    (fun a ha hp ↦ h.outputAvoids a ha (.inr hp))
  · rw [outputAddress_toNat h offset (by omega)]
    change (outputAddress s).toNat ≤ _
    omega
  · rw [outputAddress_toNat h offset (by omega)]
    change _ ≤ (outputAddress s).toNat + 16
    omega

theorem covers_shift {base address : BitVec 64} {offset len total : Nat}
    (h : Component.Covers (.mem (base + BitVec.ofNat 64 offset) len) address)
    (he : offset + len ≤ total) : Component.Covers (.mem base total) address := by
  obtain ⟨i, hi, rfl⟩ := h
  exact ⟨offset + i, by omega, by rw [BitVec.add_assoc, ← BitVec.ofNat_add]⟩

theorem stack_cover {variant : Variant} {s : RamState} (h : Storage s variant) {offset len : Nat}
    (he : offset + len ≤ variant.stackBytes) {address : BitVec 64}
    (hc : Component.Covers (.mem (stackPtr s + BitVec.ofNat 64 offset) len) address) :
    (stackRegion s variant).Contains address.toNat := by
  obtain ⟨i, hi, rfl⟩ := hc
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact stackContains h _ (by omega)

theorem output_cover {variant : Variant} {s : RamState} (h : Storage s variant) {offset len : Nat}
    (he : offset + len ≤ 16) {address : BitVec 64}
    (hc : Component.Covers (.mem (outputAddress s + BitVec.ofNat 64 offset) len) address) :
    (outputRegion s).Contains address.toNat := by
  obtain ⟨i, hi, rfl⟩ := hc
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, outputAddress_toNat h _ (by omega)]
  change (outputAddress s).toNat ≤ _ ∧ _ < (outputAddress s).toNat + 16
  omega

theorem effect_covered {variant : Variant} {s : RamState} (h : Storage s variant) {c : Component}
    (hc : c ∈ (effect s variant).components) {address : BitVec 64} (ha : c.Covers address) :
    (stackRegion s variant).Contains address.toNat ∨ (outputRegion s).Contains address.toNat := by
  cases variant with
  | saved =>
      simp only [effect, Effect.components, List.map_cons, List.map_nil, List.append_nil,
        List.cons_append, List.nil_append, Write.component, Operand.component,
        List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals try exact False.elim ha
      · exact .inl (stack_cover h (offset := 296) (len := 8) (by decide) ha)
      · exact .inl (stack_cover h (offset := 304) (len := 8) (by decide) ha)
      · exact .inl (stack_cover h (offset := 80) (len := 8) (by decide) ha)
      · exact .inl (stack_cover h (offset := 72) (len := 8) (by decide) ha)
      · exact .inl (stack_cover h (offset := 88) (len := 8) (by decide) ha)
      · exact .inl (stack_cover h (offset := 71) (len := 1) (by decide) ha)
      · exact .inr (output_cover h (offset := 8) (len := 8) (by decide) ha)
      · exact .inr (output_cover h (offset := 0) (len := 8) (by decide) (by simpa using ha))

  | direct =>
      simp only [effect, Effect.components, List.map_cons, List.map_nil, List.append_nil,
        List.cons_append, List.nil_append, Write.component, Operand.component,
        List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals try exact False.elim ha
      · exact .inl (stack_cover h (offset := 80) (len := 8) (by decide) ha)
      · exact .inl (stack_cover h (offset := 72) (len := 8) (by decide) ha)
      · exact .inl (stack_cover h (offset := 88) (len := 8) (by decide) ha)
      · exact .inl (stack_cover h (offset := 71) (len := 1) (by decide) ha)
      · exact .inr (output_cover h (offset := 8) (len := 8) (by decide) ha)
      · exact .inr (output_cover h (offset := 0) (len := 8) (by decide) (by simpa using ha))

theorem effect_avoids {variant : Variant} {s : RamState} (h : Storage s variant) :
    (effect s variant).Avoids Extracted.programImage := by
  intro x hx c hc ha
  rcases effect_covered h hc ha with hs | ho
  · exact h.stackAvoids x.1 hs (.inl ⟨x.2, hx⟩)
  · exact h.outputAvoids x.1 ho (.inl ⟨x.2, hx⟩)

theorem effect_agrees {variant : Variant} {s t : RamState} (h : (effect s variant).Holds s t) :
    AgreesExcept (changes s) s t := by
  cases variant with
  | saved =>
      apply h.agrees.widen
      · intro c hc hm
        simp only [effect, Effect.components, List.map_cons, List.map_nil, List.append_nil,
          List.cons_append, List.nil_append, Write.component, Operand.component,
          List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals simp_all [Component.isMem, changes]
      · intro x c hc ha
        simp only [effect, Effect.components, List.map_cons, List.map_nil, List.append_nil,
          List.cons_append, List.nil_append, Write.component, Operand.component,
          List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals try exact False.elim ha
        · exact ⟨.mem (stackPtr s + 0x128) 16, by simp [changes],
            covers_shift (offset := 0) (by simpa using ha) (by decide)⟩
        · exact ⟨.mem (stackPtr s + 0x128) 16, by simp [changes],
            covers_shift (offset := 8) (by simpa [BitVec.add_assoc] using ha) (by decide)⟩
        · exact ⟨.mem (stackPtr s + 8) 152, by simp [changes],
            covers_shift (offset := 72) (by simpa [BitVec.add_assoc] using ha) (by decide)⟩
        · exact ⟨.mem (stackPtr s + 8) 152, by simp [changes],
            covers_shift (offset := 64) (by simpa [BitVec.add_assoc] using ha) (by decide)⟩
        · exact ⟨.mem (stackPtr s + 8) 152, by simp [changes],
            covers_shift (offset := 80) (by simpa [BitVec.add_assoc] using ha) (by decide)⟩
        · exact ⟨.mem (stackPtr s + 8) 152, by simp [changes],
            covers_shift (offset := 63) (by simpa [BitVec.add_assoc] using ha) (by decide)⟩
        · exact ⟨.mem (outputAddress s) 16, by simp [changes], covers_shift ha (by decide)⟩
        · exact ⟨.mem (outputAddress s) 16, by simp [changes],
            covers_shift (offset := 0) (by simpa using ha) (by decide)⟩

  | direct =>
      apply h.agrees.widen
      · intro c hc hm
        simp only [effect, Effect.components, List.map_cons, List.map_nil, List.append_nil,
          List.cons_append, List.nil_append, Write.component, Operand.component,
          List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals simp_all [Component.isMem, changes]
      · intro x c hc ha
        simp only [effect, Effect.components, List.map_cons, List.map_nil, List.append_nil,
          List.cons_append, List.nil_append, Write.component, Operand.component,
          List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals try exact False.elim ha
        · exact ⟨.mem (stackPtr s + 8) 152, by simp [changes],
            covers_shift (offset := 72) (by simpa [BitVec.add_assoc] using ha) (by decide)⟩
        · exact ⟨.mem (stackPtr s + 8) 152, by simp [changes],
            covers_shift (offset := 64) (by simpa [BitVec.add_assoc] using ha) (by decide)⟩
        · exact ⟨.mem (stackPtr s + 8) 152, by simp [changes],
            covers_shift (offset := 80) (by simpa [BitVec.add_assoc] using ha) (by decide)⟩
        · exact ⟨.mem (stackPtr s + 8) 152, by simp [changes],
            covers_shift (offset := 63) (by simpa [BitVec.add_assoc] using ha) (by decide)⟩
        · exact ⟨.mem (outputAddress s) 16, by simp [changes], covers_shift ha (by decide)⟩
        · exact ⟨.mem (outputAddress s) 16, by simp [changes],
            covers_shift (offset := 0) (by simpa using ha) (by decide)⟩


theorem stackTextApart {variant : Variant} {s : RamState} (h : Storage s variant) (offset len codeOffset codeLen : Nat)
    (hs : offset + len ≤ variant.stackBytes) (hc : codeOffset + codeLen ≤ Extracted.textBytes.size) :
    RangeApart (stackPtr s + BitVec.ofNat 64 offset) len
      (Extracted.textAddress + BitVec.ofNat 64 codeOffset) codeLen := by
  intro i hi j hj he
  apply h.stackAvoids _ (stack_cover h hs ⟨i, hi, rfl⟩)
  left
  rw [he, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact text_address_in_program _ (by omega)

theorem outputTextApart {variant : Variant} {s : RamState} (h : Storage s variant) (offset len codeOffset codeLen : Nat)
    (ho : offset + len ≤ 16) (hc : codeOffset + codeLen ≤ Extracted.textBytes.size) :
    RangeApart (outputAddress s + BitVec.ofNat 64 offset) len
      (Extracted.textAddress + BitVec.ofNat 64 codeOffset) codeLen := by
  intro i hi j hj he
  apply h.outputAvoids _ (output_cover h ho ⟨i, hi, rfl⟩)
  left
  rw [he, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact text_address_in_program _ (by omega)

theorem outputStackApart {variant : Variant} {s : RamState} (h : Storage s variant)
    (outOffset outLen stackOffset stackLen : Nat)
    (ho : outOffset + outLen ≤ 16) (hs : stackOffset + stackLen ≤ variant.stackBytes) :
    RangeApart (outputAddress s + BitVec.ofNat 64 outOffset) outLen
      (stackPtr s + BitVec.ofNat 64 stackOffset) stackLen := by
  intro i hi j hj he
  exact h.outputStack _ (output_cover h ho ⟨i, hi, rfl⟩)
    (he ▸ stack_cover h hs ⟨j, hj, rfl⟩)

theorem memLoad_memStore_rangeApart {m : Ram} {src dst : BitVec 64} {n k : Nat}
    {value : BitVec n} (h : RangeApart dst (n / 8) src (k / 8)) :
    memLoad (memStore m dst value) src k = memLoad m src k := by
  apply memLoad_congr
  intro j hj
  change ((memStore m dst value)[src + BitVec.ofNat 64 j]?).getD 0 = _
  rw [memStore_getElem?_of_ne _ _ _ _ (fun i hi he ↦ h i hi j hj he)]
  rfl


end Md5.Proofs.Buffered.FinalizeReset.Export
