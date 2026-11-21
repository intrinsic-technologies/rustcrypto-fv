import K256.Proofs.Common.Image
import K256.Proofs.Common.Machine
import K256.Proofs.Common.Refine.Lemma.SysVEntry

namespace K256.Proofs.Common

open K256.Spec.Program Prelude X86 X86.Machine X86Proofs K256.Proofs.Refine

variable {routine : Routine} {s : RamState} {inputs : List ByteArray} {args : List Nat}

theorem stackOffset {budget off : Nat} (stack : Stack.Valid s budget)
    (depth : off ≤ budget) :
    (stackPtr s - BitVec.ofNat 64 off).toNat = (stackPtr s).toNat - off := by
  have room := stack.2.2.1
  change budget ≤ (stackPtr s).toNat at room
  have limit := (stackPtr s).isLt
  have index : (BitVec.ofNat 64 off).toNat = off := Nat.mod_eq_of_lt (by omega)
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, index]; omega), index]

theorem stackRange {budget : Nat} (stack : Stack.Valid s budget) {off len : Nat}
    (depth : off ≤ budget) (fits : len ≤ off + 8) :
    InRegion (Stack.region s budget) (stackPtr s - BitVec.ofNat 64 off) len := by
  have room : budget ≤ (stackPtr s).toNat := stack.2.2.1
  have low := stack.1
  change (stackPtr s).toNat - budget + ((stackPtr s).toNat + 8 -
    ((stackPtr s).toNat - budget)) < 2^32 at low
  unfold InRegion
  rw [stackOffset stack depth]
  change (stackPtr s).toNat - budget ≤ _ ∧
    _ ≤ (stackPtr s).toNat - budget +
      ((stackPtr s).toNat + 8 - ((stackPtr s).toNat - budget)) ∧ _
  omega

theorem writable_of_validCall {r : MemoryRegion} {p : BitVec 64} {len : Nat}
    (call : ValidCall routine s inputs args) (written : r ∈ writtenRegions routine s)
    (low : r.Bounded) (allocated : r.Allocated s.external)
    (inside : InRegion r p len) (pos : 0 < len) :
    Writable Extracted.programImage s.external p len := by
  apply Writable.of_avoids low allocated (call.separation.2 r written).1 _ _ inside.1 inside.2.1 pos
  · exact fun x hx => Or.inl ⟨x.2, programSections_fetchByte_of_mem hx⟩
  · intro b hb
    have h := not_pageTableEntriesApart_frames hb
    exact Or.inr (contains_iff.mpr (by simp only [pageTables]; omega))

theorem stackWritable (call : ValidCall routine s inputs args) {off len : Nat}
    (depth : off ≤ routine.minStackBytes) (fits : len ≤ off + 8) (pos : 0 < len) :
    Writable Extracted.programImage s.external (stackPtr s - BitVec.ofNat 64 off) len :=
  writable_of_validCall call (by simp [writtenRegions]) call.stackAvailable.1 call.stackAvailable.2.1
    (stackRange call.stackAvailable depth fits) pos

theorem outputWritable (call : ValidCall routine s inputs args) (writes : routine.writesOutput = true)
    (pos : 0 < routine.outputBytes) :
    Writable Extracted.programImage s.external (s.regValue .rdi) routine.outputBytes := by
  have valid := call.outputInMemory writes
  have low : (s.regValue .rdi).toNat + routine.outputBytes < 2^32 := valid.2.1
  apply writable_of_validCall call (r := outputRegion routine s) _ valid.2.1 valid.2.2 _ pos
  · simp [writtenRegions, writes]
  · exact ⟨Nat.le_refl _, Nat.le_refl _, by omega⟩

end K256.Proofs.Common
