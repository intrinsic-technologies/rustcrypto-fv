import P256.Proofs.Generate.Zero.Frame

set_option autoImplicit false

namespace P256.Proofs.Generate.Zero

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

variable [Bindings] {s t : RamState} {boundary : ReturnBoundary} {entry : BitVec 64}

theorem writes (pre : CalleePre s boundary entry 32 32 32) :
    WritesWithin (clobbers s) #v[Stack.region s 32] := by
  intro c hc address cover
  rcases List.mem_append.mp hc with hc | hc
  · exact prefix_writes pre c hc address cover
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact cover.elim
    · exact ⟨Stack.region s 32, by simp,
        ScalarFrame.stack_contains pre (offset := 1) (by decide) (by decide) cover⟩

theorem loaded (pre : CalleePre s boundary entry 32 32 32)
    (agrees : AgreesExcept (clobbers s) s t) : ProgramLoaded t := by
  have memory := agrees.memoryWriteFrame (writes pre)
  intro a b fetch
  rw [memory a]
  · exact pre.loaded a b fetch
  · intro region hr ha
    have eq : region = Stack.region s 32 := by simpa using hr
    subst region
    exact pre.avoids _ (by simp) a ha (.inl ⟨b, fetch⟩)

omit [Bindings] in
theorem return_address (agrees : AgreesExcept (clobbers s) s t) :
    memLoad t.external (stackPtr s) 64 = memLoad s.external (stackPtr s) 64 := by
  apply memLoad_congr
  intro i hi
  change (t.external[_]?).getD 0 = (s.external[_]?).getD 0
  congr 1
  apply agrees.byte
  intro c hc cover
  simp only [clobbers, prefixClobbers, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl)
  all_goals try exact cover.elim
  all_goals obtain ⟨j, hj, eq⟩ := cover
  · apply OffsetsApart.ne (c₁ := -8) (c₂ := 0#64) (len₁ := 8) (len₂ := 8)
      (by unfold OffsetsApart; decide +kernel) (stackPtr s) hj hi (by decide)
    simpa only [BitVec.sub_eq_add_neg, BitVec.add_zero] using eq.symm
  · apply OffsetsApart.ne (c₁ := -16) (c₂ := 0#64) (len₁ := 8) (len₂ := 8)
      (by unfold OffsetsApart; decide +kernel) (stackPtr s) hj hi (by decide)
    simpa only [BitVec.sub_eq_add_neg, BitVec.add_zero] using eq.symm
  · apply OffsetsApart.ne (c₁ := -1) (c₂ := 0#64) (len₁ := 1) (len₂ := 8)
      (by unfold OffsetsApart; decide +kernel) (stackPtr s) hj hi (by decide)
    simpa only [BitVec.sub_eq_add_neg, BitVec.add_zero] using eq.symm

end P256.Proofs.Generate.Zero
