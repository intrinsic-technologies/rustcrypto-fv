import P256.Proofs.Verifying.Combination.Naf.Serialize.Reverse.Words
import P256.Proofs.Verifying.Combination.Naf.Serialize.Reverse.ResultCommon

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Serialize.Reverse

open P256.Proofs.Common.Curve.LinearCombination.NafReverse

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem words_result {s t : RamState} (pre : Pre s 0x10b1cf)
    (h : (wordsEffect s).Holds s t) : SegmentPost s t 0x10b223 0 6 := by
  have components : (wordsEffect s).components = [.reg 0, .reg 1, .reg 2, .mem (stackPtr s+8) 2, .mem (stackPtr s+38) 2, .mem (stackPtr s+10) 2, .mem (stackPtr s+36) 2, .mem (stackPtr s+12) 2, .mem (stackPtr s+34) 2, .flags, .rip] := by
    simp [wordsEffect, Effect.components, Write.component, Operand.component, Operand.read, stackPtr]
  refine ⟨h.rip, ?_, ?_⟩
  · apply frame_of_effect h
    · intro c hc hm
      rw [components] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [Component.isMem, footprint]
    · intro c hc a cover
      rw [components] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cover.elim
      · exact cover.elim
      · exact cover.elim
      · exact slot_cover s 8 2 (by decide) (by decide) cover
      · exact slot_cover s 38 2 (by decide) (by decide) cover
      · exact slot_cover s 10 2 (by decide) (by decide) cover
      · exact slot_cover s 36 2 (by decide) (by decide) cover
      · exact slot_cover s 12 2 (by decide) (by decide) cover
      · exact slot_cover s 34 2 (by decide) (by decide) cover
      · exact cover.elim
      · exact cover.elim
  · apply (Bytes.of_isSome (fun i hi => h.agrees.grow _ (pre.writable.mem i hi))).congr
    intro i bound
    by_cases changed : (0 ≤ i ∧ i < 6) ∨ (32-6 ≤ i ∧ i < 32-0)
    · have choices : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 := by omega
      obtain ⟨r0, r1, r2, w8, w38, w10, w36, w12, w34⟩ := h.writes
      rcases choices with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simpa [segmentIndex, BitVec.add_assoc, stackPtr] using rotated_load_byte w8 0 (by decide)
      · simpa [segmentIndex, BitVec.add_assoc, stackPtr] using rotated_load_byte w8 1 (by decide)
      · simpa [segmentIndex, BitVec.add_assoc, stackPtr] using rotated_load_byte w10 0 (by decide)
      · simpa [segmentIndex, BitVec.add_assoc, stackPtr] using rotated_load_byte w10 1 (by decide)
      · simpa [segmentIndex, BitVec.add_assoc, stackPtr] using rotated_load_byte w12 0 (by decide)
      · simpa [segmentIndex, BitVec.add_assoc, stackPtr] using rotated_load_byte w12 1 (by decide)
      · simpa [segmentIndex, BitVec.add_assoc, stackPtr] using rotated_load_byte w34 0 (by decide)
      · simpa [segmentIndex, BitVec.add_assoc, stackPtr] using rotated_load_byte w34 1 (by decide)
      · simpa [segmentIndex, BitVec.add_assoc, stackPtr] using rotated_load_byte w36 0 (by decide)
      · simpa [segmentIndex, BitVec.add_assoc, stackPtr] using rotated_load_byte w36 1 (by decide)
      · simpa [segmentIndex, BitVec.add_assoc, stackPtr] using rotated_load_byte w38 0 (by decide)
      · simpa [segmentIndex, BitVec.add_assoc, stackPtr] using rotated_load_byte w38 1 (by decide)
    · simp only [segmentIndex, ite_eq_right changed]
      apply unchanged_byte h.agrees
      intro c hc cover
      rw [components] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cover.elim
      · exact cover.elim
      · exact cover.elim
      · have ix := covered_slot_index s 8 2 (by decide) bound cover
        omega
      · have ix := covered_slot_index s 38 2 (by decide) bound cover
        omega
      · have ix := covered_slot_index s 10 2 (by decide) bound cover
        omega
      · have ix := covered_slot_index s 36 2 (by decide) bound cover
        omega
      · have ix := covered_slot_index s 12 2 (by decide) bound cover
        omega
      · have ix := covered_slot_index s 34 2 (by decide) bound cover
        omega
      · exact cover.elim
      · exact cover.elim

end P256.Proofs.Verifying.Combination.Naf.Serialize.Reverse
