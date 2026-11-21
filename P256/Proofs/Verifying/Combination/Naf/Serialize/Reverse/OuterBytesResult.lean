import P256.Proofs.Verifying.Combination.Naf.Serialize.Reverse.OuterBytes
import P256.Proofs.Verifying.Combination.Naf.Serialize.Reverse.ResultCommon

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Serialize.Reverse

open P256.Proofs.Common.Curve.LinearCombination.NafReverse

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem outerBytes_result {s t : RamState} (pre : Pre s 0x10b223)
    (h : (outerBytesEffect s).Holds s t) : SegmentPost s t 0x10b27d 6 11 := by
  have components : (outerBytesEffect s).components = [.reg 0, .reg 1, .mem (stackPtr s+14) 1, .mem (stackPtr s+33) 1, .mem (stackPtr s+15) 1, .mem (stackPtr s+32) 1, .mem (stackPtr s+16) 1, .mem (stackPtr s+31) 1, .mem (stackPtr s+17) 1, .mem (stackPtr s+30) 1, .mem (stackPtr s+18) 1, .mem (stackPtr s+29) 1, .flags, .rip] := by
    simp [outerBytesEffect, Effect.components, Write.component, Operand.component, Operand.read, stackPtr]
  refine ⟨h.rip, ?_, ?_⟩
  · apply frame_of_effect h
    · intro c hc hm
      rw [components] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [Component.isMem, footprint]
    · intro c hc a cover
      rw [components] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cover.elim
      · exact cover.elim
      · exact slot_cover s 14 1 (by decide) (by decide) cover
      · exact slot_cover s 33 1 (by decide) (by decide) cover
      · exact slot_cover s 15 1 (by decide) (by decide) cover
      · exact slot_cover s 32 1 (by decide) (by decide) cover
      · exact slot_cover s 16 1 (by decide) (by decide) cover
      · exact slot_cover s 31 1 (by decide) (by decide) cover
      · exact slot_cover s 17 1 (by decide) (by decide) cover
      · exact slot_cover s 30 1 (by decide) (by decide) cover
      · exact slot_cover s 18 1 (by decide) (by decide) cover
      · exact slot_cover s 29 1 (by decide) (by decide) cover
      · exact cover.elim
      · exact cover.elim
  · apply (Bytes.of_isSome (fun i hi => h.agrees.grow _ (pre.writable.mem i hi))).congr
    intro i bound
    by_cases changed : (6 ≤ i ∧ i < 11) ∨ (32-11 ≤ i ∧ i < 32-6)
    · have choices : i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 := by omega
      obtain ⟨r0, r1, w14, w33, w15, w32, w16, w31, w17, w30, w18, w29⟩ := h.writes
      rcases choices with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simpa [segmentIndex, BitVec.add_assoc, stackPtr] using memByte_of_memLoad_eq (n := 8) w14 0 (by decide)
      · simpa [segmentIndex, BitVec.add_assoc, stackPtr] using memByte_of_memLoad_eq (n := 8) w15 0 (by decide)
      · simpa [segmentIndex, BitVec.add_assoc, stackPtr] using memByte_of_memLoad_eq (n := 8) w16 0 (by decide)
      · simpa [segmentIndex, BitVec.add_assoc, stackPtr] using memByte_of_memLoad_eq (n := 8) w17 0 (by decide)
      · simpa [segmentIndex, BitVec.add_assoc, stackPtr] using memByte_of_memLoad_eq (n := 8) w18 0 (by decide)
      · simpa [segmentIndex, BitVec.add_assoc, stackPtr] using memByte_of_memLoad_eq (n := 8) w29 0 (by decide)
      · simpa [segmentIndex, BitVec.add_assoc, stackPtr] using memByte_of_memLoad_eq (n := 8) w30 0 (by decide)
      · simpa [segmentIndex, BitVec.add_assoc, stackPtr] using memByte_of_memLoad_eq (n := 8) w31 0 (by decide)
      · simpa [segmentIndex, BitVec.add_assoc, stackPtr] using memByte_of_memLoad_eq (n := 8) w32 0 (by decide)
      · simpa [segmentIndex, BitVec.add_assoc, stackPtr] using memByte_of_memLoad_eq (n := 8) w33 0 (by decide)
    · simp only [segmentIndex, ite_eq_right changed]
      apply unchanged_byte h.agrees
      intro c hc cover
      rw [components] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cover.elim
      · exact cover.elim
      · have ix := covered_slot_index s 14 1 (by decide) bound cover
        omega
      · have ix := covered_slot_index s 33 1 (by decide) bound cover
        omega
      · have ix := covered_slot_index s 15 1 (by decide) bound cover
        omega
      · have ix := covered_slot_index s 32 1 (by decide) bound cover
        omega
      · have ix := covered_slot_index s 16 1 (by decide) bound cover
        omega
      · have ix := covered_slot_index s 31 1 (by decide) bound cover
        omega
      · have ix := covered_slot_index s 17 1 (by decide) bound cover
        omega
      · have ix := covered_slot_index s 30 1 (by decide) bound cover
        omega
      · have ix := covered_slot_index s 18 1 (by decide) bound cover
        omega
      · have ix := covered_slot_index s 29 1 (by decide) bound cover
        omega
      · exact cover.elim
      · exact cover.elim

end P256.Proofs.Verifying.Combination.Naf.Serialize.Reverse
