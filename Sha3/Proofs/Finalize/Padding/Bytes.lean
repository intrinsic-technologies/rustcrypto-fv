import X86Proofs.Program.ReadWrite.Bytes
import X86Proofs.Program.Effect

namespace Sha3.Proofs.Finalize.Padding

open X86 X86.Machine X86.UserProcess X86Proofs

theorem shifted_padding_bytes (remaining : Fin 200) (j : Fin 8) (suffix : UInt8 := 6) :
    storedByte (suffix.toBitVec.setWidth 64 <<< (8 * (remaining.val % 8))) j.val =
      if j.val = remaining.val % 8 then suffix else 0 := by
  have h : ∀ b : Fin 256, ∀ i : Fin 8, ∀ j : Fin 8,
      storedByte ((BitVec.ofNat 64 b.val) <<< (8 * i.val)) j.val =
        if j.val = i.val then UInt8.ofNat b.val else 0 := by decide +kernel
  have he : BitVec.ofNat 64 suffix.toNat = suffix.toBitVec.setWidth 64 := by
    apply BitVec.eq_of_toNat_eq
    simp
  simpa only [Fin.val_mk, UInt8.ofNat_toNat, he] using
    h ⟨suffix.toNat, suffix.toNat_lt⟩ ⟨remaining.val % 8, by omega⟩ j

theorem xor_padding_lane {m : Ram} {base : BitVec 64} {len remaining : Nat}
    {bytes : Nat → UInt8} (h : Bytes m base len bytes) (hlen : len ≤ 2 ^ 64)
    (hr : remaining < 200) (hspan : remaining / 8 * 8 + 8 ≤ len) (suffix : UInt8 := 6) :
    Bytes (memStore m (base + BitVec.ofNat 64 (remaining / 8 * 8))
      (memLoad m (base + BitVec.ofNat 64 (remaining / 8 * 8)) 64 ^^^
        (suffix.toBitVec.setWidth 64 <<< (8 * (remaining % 8))))) base len
      (fun i ↦ bytes i ^^^ (if i = remaining then suffix else 0)) := by
  apply (h.store hlen (remaining / 8 * 8) _ (by decide) hspan).congr
  intro i hi
  by_cases hin : remaining / 8 * 8 ≤ i ∧ i < remaining / 8 * 8 + 64 / 8
  · simp only [hin, storedByte_xor]
    rw [storedByte_memLoad _ _ _ (by omega)]
    have hb := h i hi
    have he : base + BitVec.ofNat 64 (remaining / 8 * 8) +
        BitVec.ofNat 64 (i - remaining / 8 * 8) = base + BitVec.ofNat 64 i := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' hin.1]
    rw [he]
    change (m[base + BitVec.ofNat 64 i]?).getD 0 ^^^ _ = _
    rw [hb]
    simp only [Option.getD_some]
    rw [shifted_padding_bytes ⟨remaining, hr⟩ ⟨i - remaining / 8 * 8, by omega⟩ suffix]
    have heq : i - remaining / 8 * 8 = remaining % 8 ↔ i = remaining := by omega
    simp only [heq]
  · have hne : i ≠ remaining := by omega
    simp only [hin, ↓reduceIte, hne, UInt8.xor_zero]

theorem xor_padding_final {m : Ram} {base : BitVec 64} {len rate : Nat}
    {bytes : Nat → UInt8} (h : Bytes m base len bytes) (hlen : len ≤ 2 ^ 64)
    (hr : 0 < rate) (hspan : rate ≤ len) :
    Bytes (memStore m (base + BitVec.ofNat 64 (rate - 1))
      (memLoad m (base + BitVec.ofNat 64 (rate - 1)) 8 ^^^ (0x80 : BitVec 8))) base len
      (fun i ↦ bytes i ^^^ (if i + 1 = rate then 0x80 else 0)) := by
  rw [h.loadByte (rate - 1) (by omega)]
  change Bytes (memStore m (base + BitVec.ofNat 64 (rate - 1))
    ((bytes (rate - 1) ^^^ 0x80).toBitVec)) base len _
  apply (h.writeByte hlen (rate - 1) (by omega) (bytes (rate - 1) ^^^ 0x80)).congr
  intro i _
  by_cases hi : i = rate - 1
  · have hi' : i + 1 = rate := by omega
    simp only [hi, ↓reduceIte, show rate - 1 + 1 = rate by omega]
  · have hi' : i + 1 ≠ rate := by omega
    simp only [hi, hi', ↓reduceIte, UInt8.xor_zero]


theorem single_store_external {s t : RamState} {n : Nat} {address : BitVec 64}
    {value : BitVec n} {rip : BitVec 64} {flags : Option StatusFlagsOutcome}
    (hn : n ≤ 128)
    (hallocated : ∀ i < n / 8, (s.external[address + BitVec.ofNat 64 i]?).isSome)
    (h : ({ rip := rip
            writes := [⟨(Operand.mem address : Operand n), value⟩]
            flags := flags } : Effect).Holds s t) :
    t.external = memStore s.external address value := by
  apply Std.ExtHashMap.ext_getElem?
  intro x
  by_cases hx : ∃ i < n / 8, x = address + BitVec.ofNat 64 i
  · obtain ⟨i, hi, rfl⟩ := hx
    rw [memStore_getElem?_self _ _ _ hn i hi]
    have hb := Bytes.of_memLoad (fun j hj ↦ h.agrees.grow _ (hallocated j hj)) i hi
    have hv : memLoad t.external address n = value := h.writes
    rwa [hv] at hb
  · rw [memStore_getElem?_of_ne _ _ _ _ (fun i hi he ↦ hx ⟨i, hi, he.symm⟩)]
    apply h.agrees.memory
    intro c hc hcx
    have hc' : c = .mem address (n / 8) ∨ c = .flags ∨ c = .rip := by
      cases flags with
      | none =>
        have hc' : c = .mem address (n / 8) ∨ c = .rip := by
          simpa [Effect.components, Write.component, Operand.component] using hc
        exact hc'.imp_right Or.inr
      | some flags => simpa [Effect.components, Write.component, Operand.component] using hc
    rcases hc' with rfl | rfl | rfl
    · exact hx hcx
    · exact hcx
    · exact hcx

end Sha3.Proofs.Finalize.Padding
