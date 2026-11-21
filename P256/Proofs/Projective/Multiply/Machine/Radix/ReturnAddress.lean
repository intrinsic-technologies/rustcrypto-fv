import P256.Proofs.Projective.Multiply.Machine.Radix.State

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Radix

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs Program

theorem State.returnAddress [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {offset : BitVec 64} (pre : CalleePre s boundary 0x10b720 32 65 136)
    (state : State s t offset) :
    memLoad t.external (stackPtr s) 64 = memLoad s.external (stackPtr s) 64 := by
  have apart : RangeApart (stackPtr s-136) 136 (stackPtr s) 8 := by
    simpa only [BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd,
      BitVec.add_zero] using RangeApart.offsets (stackPtr s-136) (a := 0) (b := 136)
        (len := 136) (count := 8) (by decide) (by decide) (.inl (by decide))
  apply memLoad_congr
  intro i hi
  apply congrArg (fun b : Option UInt8 => b.getD 0)
  apply state.agrees.byte
  intro c hc ha
  simp only [components,registers,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl)|rfl|rfl
  all_goals try exact ha.elim
  · obtain ⟨j,hj,eq⟩ := ha
    apply pre.separation 1 2 (by decide) _
      (memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) hj)
    rw [←eq]
    apply memoryRegion_contains_add pre.stack.1 (len := 8) (Nat.sub_le _ _) _ hi
    rw [stack_region_end]
    exact Nat.le_refl _
  · obtain ⟨j,hj,eq⟩ := ha
    exact apart j hj i hi eq.symm

end P256.Proofs.Projective.Multiply.Machine.Radix
