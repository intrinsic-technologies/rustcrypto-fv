import Md5.Proofs.Buffered.Finalize.Contracts
import Md5.Proofs.Buffered.Stores.Program
import Md5.Proofs.MemoryRoutines.Ranges

namespace Md5.Proofs.Buffered.Finalize

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable {kind : Kind} {boundary : ReturnBoundary} {message : ByteArray}
  {s t : RamState}

theorem Storage.stackBounded (h : Storage kind s) : (kind.stackRegion s).Bounded := by
  change (stackPtr s).toNat - 320 + (320 + kind.stackBytes) < userAddressLimit
  have := h.stackLow
  have := h.stackHigh
  omega

theorem Storage.stackAddress (h : Storage kind s) {offset : Nat}
    (ho : offset ≤ kind.stackBytes) :
    (stackPtr s + BitVec.ofNat 64 offset).toNat = (stackPtr s).toNat + offset := by
  have hh : (stackPtr s).toNat + kind.stackBytes < 2^32 := h.stackHigh
  rw [BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show offset < 2^64 by omega),
    Nat.mod_eq_of_lt (show (stackPtr s).toNat + offset < 2^64 by omega)]

theorem Storage.stackCover (h : Storage kind s) {offset len : Nat}
    (ho : offset + len ≤ kind.stackBytes) {address : BitVec 64}
    (hc : Component.Covers (.mem (stackPtr s + BitVec.ofNat 64 offset) len) address) :
    (kind.stackRegion s).Contains address.toNat := by
  obtain ⟨i, hi, rfl⟩ := hc
  rw [add_ofNat_add_ofNat, h.stackAddress (by omega)]
  change (stackPtr s).toNat - 320 ≤ (stackPtr s).toNat + (offset + i) ∧
    (stackPtr s).toNat + (offset + i) < (stackPtr s).toNat - 320 + (320 + kind.stackBytes)
  have := h.stackLow
  omega

theorem Storage.stackWritable (h : Storage kind s) (offset len : Nat)
    (ho : offset + len ≤ kind.stackBytes) :
    Memory.MemWritable s (stackPtr s + BitVec.ofNat 64 offset) len := by
  apply Memory.MemWritable.of_region h.stackBounded h.stackAllocated
    (fun a ha hp ↦ h.stackAvoids a ha (.inr hp))
  · rw [h.stackAddress (by omega)]
    change (stackPtr s).toNat - 320 ≤ _
    omega
  · rw [h.stackAddress (by omega)]
    change _ ≤ (stackPtr s).toNat - 320 + (320 + kind.stackBytes)
    have := h.stackLow
    omega

theorem Storage.stackRange (h : Storage kind s) (offset len : Nat)
    (ho : offset + len ≤ kind.stackBytes) :
    MemoryRoutines.WritableRange s (stackPtr s + BitVec.ofNat 64 offset) len := by
  have hw := h.stackWritable offset len ho
  refine ⟨hw.readable, hw.tables, ?_⟩
  intro i hi hp
  exact h.stackAvoids _ (h.stackCover ho ⟨i, hi, rfl⟩) (.inl hp)

theorem Storage.stackApart (h : Storage kind s) {offset len codeOffset codeLen : Nat}
    (he : offset + len ≤ kind.stackBytes) (hc : codeOffset + codeLen ≤ Extracted.textBytes.size) :
    RangeApart (stackPtr s + BitVec.ofNat 64 offset) len
      (Extracted.textAddress + BitVec.ofNat 64 codeOffset) codeLen := by
  apply Stores.rangeApart_text _ hc
  exact (h.stackRange offset len he).code

theorem Storage.belowAddress (h : Storage kind s) :
    (stackPtr s - 320).toNat = (stackPtr s).toNat - 320 := by
  rw [BitVec.toNat_sub_of_le]
  · rfl
  · exact h.stackLow

theorem Storage.belowCover (h : Storage kind s) {address : BitVec 64}
    (hc : Component.Covers (.mem (stackPtr s - 320) 320) address) :
    (kind.stackRegion s).Contains address.toNat := by
  obtain ⟨i, hi, rfl⟩ := hc
  have hh : (stackPtr s).toNat + kind.stackBytes < 2^32 := h.stackHigh
  rw [BitVec.toNat_add, h.belowAddress, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show i < 2^64 by omega),
    Nat.mod_eq_of_lt (show (stackPtr s).toNat - 320 + i < 2^64 by omega)]
  change (stackPtr s).toNat - 320 ≤ (stackPtr s).toNat - 320 + i ∧
    (stackPtr s).toNat - 320 + i < (stackPtr s).toNat - 320 + (320 + kind.stackBytes)
  omega

theorem Storage.belowRange (h : Storage kind s) :
    MemoryRoutines.WritableRange s (stackPtr s - 320) 320 := by
  have hw : Memory.MemWritable s (stackPtr s - 320) 320 := by
    apply Memory.MemWritable.of_region h.stackBounded h.stackAllocated
      (fun a ha hp ↦ h.stackAvoids a ha (.inr hp))
    · rw [h.belowAddress]
      exact Nat.le_refl _
    · rw [h.belowAddress]
      change _ ≤ (stackPtr s).toNat - 320 + (320 + kind.stackBytes)
      omega
  refine ⟨hw.readable, hw.tables, ?_⟩
  intro i hi hp
  exact h.stackAvoids _ (h.belowCover ⟨i, hi, rfl⟩) (.inl hp)

theorem Post.frame [Bindings] (h : Post kind boundary message s t) (hp : Storage kind s) :
    MemoryWriteFrame s t #v[kind.stackRegion s] := by
  apply h.agrees.memoryWriteFrame
  intro c hc address hcover
  refine ⟨kind.stackRegion s, by simp, ?_⟩
  simp only [Kind.changes, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with (hc | hc) | hc
  · rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hcover.elim
    exact hp.belowCover hcover
  · obtain ⟨r, _, rfl⟩ := List.mem_map.mp hc
    exact hcover.elim
  · cases kind <;> simp only [Kind.localChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
    · subst c
      exact hp.stackCover (offset := 8) (len := 168) (by decide) hcover
    · subst c
      exact hp.stackCover (offset := 0) (len := 168) (by decide) (by simpa using hcover)
    · rcases hc with rfl | rfl
      · exact hp.stackCover (offset := 96) (len := 88) (by decide) hcover
      · exact hp.stackCover (offset := 216) (len := 80) (by decide) hcover
    · rcases hc with rfl | rfl
      · exact hp.stackCover (offset := 96) (len := 88) (by decide) hcover
      · exact hp.stackCover (offset := 216) (len := 80) (by decide) hcover
    · subst c
      exact hp.stackCover (offset := 120) (len := 168) (by decide) hcover
    · subst c
      exact hp.stackCover (offset := 0) (len := 168) (by decide) (by simpa using hcover)

end Md5.Proofs.Buffered.Finalize
