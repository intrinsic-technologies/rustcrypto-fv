import P256.Proofs.Verifying.Combination.Naf.Serialize.Reverse.InnerBytes
import P256.Proofs.Verifying.Combination.Naf.Serialize.Reverse.ResultCommon

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Serialize.Reverse

open P256.Proofs.Common.Curve.LinearCombination.NafReverse

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem innerBytes_result {s t : RamState} (pre : Pre s 0x10b27d)
    (h : (innerBytesEffect s).Holds s t) : SegmentPost s t 0x10b2d7 11 16 := by
  have components : (innerBytesEffect s).components = [.reg 0, .reg 1, .mem (stackPtr s+19) 1, .mem (stackPtr s+28) 1, .mem (stackPtr s+20) 1, .mem (stackPtr s+27) 1, .mem (stackPtr s+21) 1, .mem (stackPtr s+26) 1, .mem (stackPtr s+22) 1, .mem (stackPtr s+25) 1, .mem (stackPtr s+23) 1, .mem (stackPtr s+24) 1, .flags, .rip] := by
    simp [innerBytesEffect, Effect.components, Write.component, Operand.component, Operand.read, stackPtr]
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
      · exact slot_cover s 19 1 (by decide) (by decide) cover
      · exact slot_cover s 28 1 (by decide) (by decide) cover
      · exact slot_cover s 20 1 (by decide) (by decide) cover
      · exact slot_cover s 27 1 (by decide) (by decide) cover
      · exact slot_cover s 21 1 (by decide) (by decide) cover
      · exact slot_cover s 26 1 (by decide) (by decide) cover
      · exact slot_cover s 22 1 (by decide) (by decide) cover
      · exact slot_cover s 25 1 (by decide) (by decide) cover
      · exact slot_cover s 23 1 (by decide) (by decide) cover
      · exact slot_cover s 24 1 (by decide) (by decide) cover
      · exact cover.elim
      · exact cover.elim
  · apply (Bytes.of_isSome (fun i hi => h.agrees.grow _ (pre.writable.mem i hi))).congr
    intro i bound
    by_cases changed : (11 ≤ i ∧ i < 16) ∨ (32-16 ≤ i ∧ i < 32-11)
    · have choices : i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 := by omega
      obtain ⟨r0, r1, w19, w28, w20, w27, w21, w26, w22, w25, w23, w24⟩ := h.writes
      rcases choices with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simpa [segmentIndex, BitVec.add_assoc, stackPtr] using memByte_of_memLoad_eq (n := 8) w19 0 (by decide)
      · simpa [segmentIndex, BitVec.add_assoc, stackPtr] using memByte_of_memLoad_eq (n := 8) w20 0 (by decide)
      · simpa [segmentIndex, BitVec.add_assoc, stackPtr] using memByte_of_memLoad_eq (n := 8) w21 0 (by decide)
      · simpa [segmentIndex, BitVec.add_assoc, stackPtr] using memByte_of_memLoad_eq (n := 8) w22 0 (by decide)
      · simpa [segmentIndex, BitVec.add_assoc, stackPtr] using memByte_of_memLoad_eq (n := 8) w23 0 (by decide)
      · simpa [segmentIndex, BitVec.add_assoc, stackPtr] using memByte_of_memLoad_eq (n := 8) w24 0 (by decide)
      · simpa [segmentIndex, BitVec.add_assoc, stackPtr] using memByte_of_memLoad_eq (n := 8) w25 0 (by decide)
      · simpa [segmentIndex, BitVec.add_assoc, stackPtr] using memByte_of_memLoad_eq (n := 8) w26 0 (by decide)
      · simpa [segmentIndex, BitVec.add_assoc, stackPtr] using memByte_of_memLoad_eq (n := 8) w27 0 (by decide)
      · simpa [segmentIndex, BitVec.add_assoc, stackPtr] using memByte_of_memLoad_eq (n := 8) w28 0 (by decide)
    · simp only [segmentIndex, ite_eq_right changed]
      apply unchanged_byte h.agrees
      intro c hc cover
      rw [components] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cover.elim
      · exact cover.elim
      · have ix := covered_slot_index s 19 1 (by decide) bound cover
        omega
      · have ix := covered_slot_index s 28 1 (by decide) bound cover
        omega
      · have ix := covered_slot_index s 20 1 (by decide) bound cover
        omega
      · have ix := covered_slot_index s 27 1 (by decide) bound cover
        omega
      · have ix := covered_slot_index s 21 1 (by decide) bound cover
        omega
      · have ix := covered_slot_index s 26 1 (by decide) bound cover
        omega
      · have ix := covered_slot_index s 22 1 (by decide) bound cover
        omega
      · have ix := covered_slot_index s 25 1 (by decide) bound cover
        omega
      · have ix := covered_slot_index s 23 1 (by decide) bound cover
        omega
      · have ix := covered_slot_index s 24 1 (by decide) bound cover
        omega
      · exact cover.elim
      · exact cover.elim

end P256.Proofs.Verifying.Combination.Naf.Serialize.Reverse
