import P256.Proofs.Program.Input
import P256.Proofs.Program.Stack
import P256.Proofs.Common.Instructions.CrossPageStore.Range

set_option autoImplicit false

namespace P256.Proofs.Program

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions.CrossPageStore

theorem statics_writable {s : RamState}
    (hallocator : allocatorStateRegion.Allocated s.external)
    (hrandom : randomSourceRegion.Allocated s.external) : Writable s 0x300000 40 := by
  refine ⟨⟨by decide, ?_⟩, PageTableEntriesApart.of_frames (.inr (by decide))⟩
  intro i hi
  have ha : ((0x300000 : BitVec 64) + BitVec.ofNat 64 i).toNat = 3145728 + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    change (3145728 + i % 2^64) % 2^64 = _
    omega
  apply Option.isSome_iff_exists.mpr
  by_cases h : i < 24
  · apply hallocator
    change 3145728 ≤ _ ∧ _ < 3145728 + 24
    rw [ha]
    omega
  · apply hrandom
    change 3145752 ≤ _ ∧ _ < 3145752 + 16
    rw [ha]
    omega

theorem call_statics_writable [Bindings] {routine : Routine} {s t : RamState}
    {inputs : List ByteArray} {slices : Array Input}
    (h : ValidCallWithSlices routine s inputs slices)
    (hgrow : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome)
    {offset : Nat} (hoffset : offset + 8 ≤ 40) :
    Writable t (0x300000 + BitVec.ofNat 64 offset) 8 := by
  have hw := statics_writable h.allocatorStateInMemory h.randomSourceInMemory
  have ht : Writable t 0x300000 40 := ⟨readable_of_grow hw.toMemReadable hgrow, hw.tables⟩
  exact ht.add offset hoffset

theorem heap_length_memReadable [Bindings] {routine : Routine} {s t : RamState}
    {inputs : List ByteArray} {slices : Array Input}
    (h : ValidCallWithSlices routine s inputs slices)
    (hgrow : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome) :
    MemReadable t (stackPtr s + 8) 8 := by
  have hs := h.stackAvailable.2
  change (stackPtr s).toNat - routine.minStackBytes +
    ((stackPtr s).toNat + 16 - ((stackPtr s).toNat - routine.minStackBytes)) < 2^32 at hs
  have hl : (stackPtr s).toNat + 16 < 2^32 := by omega
  have ha : (stackPtr s + 8).toNat = (stackPtr s).toNat + 8 := by
    rw [BitVec.toNat_add]
    change ((stackPtr s).toNat + 8) % 2^64 = _
    omega
  obtain ⟨length, hword, _⟩ := h.heapInMemory
  have hw : (MemoryRegion.mk (stackPtr s + 8).toNat 8).Word64At s.external length := by
    rw [ha]
    exact hword
  apply readable_of_grow (word64_memReadable ?_ hw) hgrow
  change (stackPtr s + 8).toNat + 8 < 2^32
  rw [ha]
  omega

end P256.Proofs.Program
