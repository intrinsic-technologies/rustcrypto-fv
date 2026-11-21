import K256.Proofs.Common.Image
import K256.Proofs.Common.Refine.Lemma.SysVEntry

namespace K256.Proofs.Generate

open K256.Spec.Program Prelude X86 X86.Machine X86Proofs K256.Proofs.Refine

variable {initial : RamState} {random : ByteArray}

theorem stackOffset (call : ValidCall signingKeyGenerateFromRng initial [random]) {off : Nat}
    (depth : off ≤ 10584) :
    (stackPtr initial - BitVec.ofNat 64 off).toNat = (stackPtr initial).toNat - off := by
  have room : 10584 ≤ (stackPtr initial).toNat := call.stackAvailable.2.2.1
  have index : (BitVec.ofNat 64 off).toNat = off := Nat.mod_eq_of_lt (by omega)
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, index]; omega), index]

theorem stackRange (call : ValidCall signingKeyGenerateFromRng initial [random]) {off len : Nat}
    (depth : off ≤ 10584) (fits : len ≤ off + 8) :
    InRegion (Stack.region initial signingKeyGenerateFromRng.minStackBytes)
      (stackPtr initial - BitVec.ofNat 64 off) len := by
  have room : 10584 ≤ (stackPtr initial).toNat := call.stackAvailable.2.2.1
  have low := call.stackAvailable.1
  change (stackPtr initial).toNat - 10584 + ((stackPtr initial).toNat + 8 -
    ((stackPtr initial).toNat - 10584)) < 2^32 at low
  unfold InRegion
  rw [stackOffset call depth]
  change _ ∧ _ ≤ (stackPtr initial).toNat - 10584 +
    ((stackPtr initial).toNat + 8 - ((stackPtr initial).toNat - 10584)) ∧ _
  change (stackPtr initial).toNat - 10584 ≤ _ ∧ _ ∧ _
  omega

private theorem writable {r : MemoryRegion} {p : BitVec 64} {len : Nat}
    (call : ValidCall signingKeyGenerateFromRng initial [random])
    (written : r ∈ writtenRegions signingKeyGenerateFromRng initial)
    (low : r.Bounded) (allocated : r.Allocated initial.external)
    (inside : InRegion r p len) (pos : 0 < len) :
    Writable Extracted.programImage initial.external p len := by
  apply Writable.of_avoids low allocated (call.separation.2 r written).1 _ _ inside.1 inside.2.1 pos
  · exact fun x hx => Or.inl ⟨x.2, Common.programSections_fetchByte_of_mem hx⟩
  · intro b hb
    have h := not_pageTableEntriesApart_frames hb
    exact Or.inr (contains_iff.mpr (by simp only [pageTables]; omega))

theorem stackWritable (call : ValidCall signingKeyGenerateFromRng initial [random]) {off len : Nat}
    (depth : off ≤ 10584) (fits : len ≤ off + 8) (pos : 0 < len) :
    Writable Extracted.programImage initial.external (stackPtr initial - BitVec.ofNat 64 off) len :=
  writable call (by simp [writtenRegions]) call.stackAvailable.1 call.stackAvailable.2.1
    (stackRange call depth fits) pos

theorem outputWritable (call : ValidCall signingKeyGenerateFromRng initial [random]) :
    Writable Extracted.programImage initial.external (initial.regValue .rdi) 97 := by
  have h := call.outputInMemory rfl
  have low : (initial.regValue .rdi).toNat + 97 < 2^32 := h.2.1
  apply writable call (r := outputRegion signingKeyGenerateFromRng initial) _ h.2.1 h.2.2 _ (by decide)
  · exact List.mem_cons_self
  · exact ⟨Nat.le_refl _, Nat.le_refl _, by omega⟩

end K256.Proofs.Generate
