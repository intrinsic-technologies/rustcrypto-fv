import P256.Proofs.Projective.Multiply.Machine.Lookup.Select.Finish.Copy
import P256.Proofs.Projective.Multiply.Machine.Lookup.Select.Memory

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)

open P256.Proofs.Program (inProgram_of_textOffset memoryRegion_contains_add)

namespace P256.Proofs.Projective.Multiply.Machine.Lookup.Select

open P256.Proofs.Field P256.Proofs.Program P256.Spec.Program.Routines
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [Bindings] {s t u : RamState} {boundary : ReturnBoundary}

theorem finish_output_contains (pre : BinaryFieldPre s boundary 0x114380 128)
    {i : Nat} (hi : i < 32) :
    (registerRegion s .rdi 32).Contains (s.regValue .rdi + BitVec.ofNat 64 i).toNat :=
  memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) hi

theorem finish_output_readable (pre : BinaryFieldPre s boundary 0x114380 128)
    (state : SavedState s t) {off len : Nat} (hn : off + len ≤ 32) :
    MemReadable t (s.regValue .rdi + BitVec.ofNat 64 off) len := by
  have hb : (s.regValue .rdi).toNat + 32 < 2^32 := pre.outputBounded
  refine ⟨?_, ?_⟩
  · rw [toNat_add_ofNat _ _ (by omega)]; omega
  · intro i hi
    rw [add_ofNat_add_ofNat]
    exact state.allocated _ (Option.isSome_iff_exists.mpr (pre.outputAllocated _
      (finish_output_contains pre (by omega))))

theorem finish_output_writable (pre : BinaryFieldPre s boundary 0x114380 128)
    (state : SavedState s t) {off : Nat} (hn : off + 8 ≤ 32) :
    P256.Proofs.Common.Instructions.CrossPageStore.Writable t (s.regValue .rdi + BitVec.ofNat 64 off) 8 := by
  refine ⟨finish_output_readable pre state hn,
    tables_of_not_reserved (by decide) (finish_output_readable pre state hn).low ?_⟩
  intro i hi hin
  apply pre.avoids (registerRegion s .rdi 32) (by simp) _ _ (.inr hin)
  rw [add_ofNat_add_ofNat]
  exact finish_output_contains pre (by omega)

theorem finish_output_code (pre : BinaryFieldPre s boundary 0x114380 128)
    {off len pc n : Nat} (hn : off + len ≤ 32) (hp : pc + n ≤ 118431) :
    RangeApart (s.regValue .rdi + BitVec.ofNat 64 off) len
      (Extracted.textAddress + BitVec.ofNat 64 pc) n := by
  intro i hi j hj he
  apply pre.avoids (registerRegion s .rdi 32) (by simp)
    (s.regValue .rdi + BitVec.ofNat 64 off + BitVec.ofNat 64 i) _ (.inl ?_)
  · rw [add_ofNat_add_ofNat]; exact finish_output_contains pre (by omega)
  · rw [he, add_ofNat_add_ofNat]
    exact inProgram_of_textOffset (pc+j) (by omega)

theorem finish_output_stack_apart (pre : BinaryFieldPre s boundary 0x114380 128)
    {off len stackOff stackLen : Nat} (hn : off + len ≤ 32)
    (hs : stackOff ≤ 128) (hl : stackLen ≤ stackOff + 8) :
    RangeApart (s.regValue .rdi + BitVec.ofNat 64 off) len
      (stackPtr s - BitVec.ofNat 64 stackOff) stackLen := by
  intro i hi j hj he
  have hd := pre.separation (1 : Fin 3) (2 : Fin 3) (by decide)
  apply hd _ _ (stack_contains pre hs hl hj)
  rw [← he, add_ofNat_add_ofNat]
  exact finish_output_contains pre (by omega)

theorem finish_copy_pre {select : Bool} (pre : BinaryFieldPre s boundary 0x114380 128)
    (state : ReturnedState s t select) : FinishCopyPre t := by
  refine ⟨state.rip, ?_, ?_, ?_, ?_⟩
  · intro i hi
    change MemReadable t (stackPtr t + i) 8
    rw [state.rsp]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · simpa only [scratch, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using state.toSavedState.stack_readable pre (offset := 40) (len := 8) (by decide) (by decide)
    · simpa only [scratch, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using state.toSavedState.stack_readable pre (offset := 32) (len := 8) (by decide) (by decide)
    · simpa only [scratch, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using state.toSavedState.stack_readable pre (offset := 24) (len := 8) (by decide) (by decide)
    · simpa only [scratch, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using state.toSavedState.stack_readable pre (offset := 16) (len := 8) (by decide) (by decide)
  · intro i hi
    change P256.Proofs.Common.Instructions.CrossPageStore.Writable t (t.regValue .rbx + i) 8
    rw [state.rbx]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact finish_output_writable pre state.toSavedState (off := 0) (by decide)
    · exact finish_output_writable pre state.toSavedState (off := 8) (by decide)
    · exact finish_output_writable pre state.toSavedState (off := 16) (by decide)
    · exact finish_output_writable pre state.toSavedState (off := 24) (by decide)
  · intro i hi pc n hn
    change RangeApart (t.regValue .rbx + i) 8 _ n
    rw [state.rbx]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact finish_output_code pre (off := 0) (by decide) hn
    · exact finish_output_code pre (off := 8) (by decide) hn
    · exact finish_output_code pre (off := 16) (by decide) hn
    · exact finish_output_code pre (off := 24) (by decide) hn
  · intro i hi j hj
    change RangeApart (t.regValue .rbx + i) 8 (stackPtr t + j) 8
    rw [state.rbx, state.rsp]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi hj
    rcases hi with rfl | rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl | rfl
    · simpa only [scratch, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using finish_output_stack_apart pre (off := 0) (len := 8) (stackOff := 40) (stackLen := 8) (by decide) (by decide) (by decide)
    · simpa only [scratch, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using finish_output_stack_apart pre (off := 0) (len := 8) (stackOff := 32) (stackLen := 8) (by decide) (by decide) (by decide)
    · simpa only [scratch, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using finish_output_stack_apart pre (off := 0) (len := 8) (stackOff := 24) (stackLen := 8) (by decide) (by decide) (by decide)
    · simpa only [scratch, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using finish_output_stack_apart pre (off := 0) (len := 8) (stackOff := 16) (stackLen := 8) (by decide) (by decide) (by decide)
    · simpa only [scratch, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using finish_output_stack_apart pre (off := 8) (len := 8) (stackOff := 40) (stackLen := 8) (by decide) (by decide) (by decide)
    · simpa only [scratch, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using finish_output_stack_apart pre (off := 8) (len := 8) (stackOff := 32) (stackLen := 8) (by decide) (by decide) (by decide)
    · simpa only [scratch, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using finish_output_stack_apart pre (off := 8) (len := 8) (stackOff := 24) (stackLen := 8) (by decide) (by decide) (by decide)
    · simpa only [scratch, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using finish_output_stack_apart pre (off := 8) (len := 8) (stackOff := 16) (stackLen := 8) (by decide) (by decide) (by decide)
    · simpa only [scratch, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using finish_output_stack_apart pre (off := 16) (len := 8) (stackOff := 40) (stackLen := 8) (by decide) (by decide) (by decide)
    · simpa only [scratch, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using finish_output_stack_apart pre (off := 16) (len := 8) (stackOff := 32) (stackLen := 8) (by decide) (by decide) (by decide)
    · simpa only [scratch, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using finish_output_stack_apart pre (off := 16) (len := 8) (stackOff := 24) (stackLen := 8) (by decide) (by decide) (by decide)
    · simpa only [scratch, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using finish_output_stack_apart pre (off := 16) (len := 8) (stackOff := 16) (stackLen := 8) (by decide) (by decide) (by decide)
    · simpa only [scratch, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using finish_output_stack_apart pre (off := 24) (len := 8) (stackOff := 40) (stackLen := 8) (by decide) (by decide) (by decide)
    · simpa only [scratch, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using finish_output_stack_apart pre (off := 24) (len := 8) (stackOff := 32) (stackLen := 8) (by decide) (by decide) (by decide)
    · simpa only [scratch, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using finish_output_stack_apart pre (off := 24) (len := 8) (stackOff := 24) (stackLen := 8) (by decide) (by decide) (by decide)
    · simpa only [scratch, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using finish_output_stack_apart pre (off := 24) (len := 8) (stackOff := 16) (stackLen := 8) (by decide) (by decide) (by decide)

omit [Bindings] in
theorem finish_copy_memory_component {c : Component} {a : BitVec 64}
    (hc : c ∈ (finishCopyEffect t).components) (ha : c.Covers a) :
    ∃ off ∈ ([0, 8, 16, 24] : List Nat), ∃ i < 8,
      a = t.regValue .rbx + BitVec.ofNat 64 off + BitVec.ofNat 64 i := by
  simp only [finishCopyEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component_reg, Write.component_mem, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  all_goals obtain ⟨i, hi, rfl⟩ := ha
  · exact ⟨0, by simp, i, hi, rfl⟩
  · exact ⟨8, by simp, i, hi, rfl⟩
  · exact ⟨16, by simp, i, hi, rfl⟩
  · exact ⟨24, by simp, i, hi, rfl⟩

theorem finish_copy_frame (pre : BinaryFieldPre s boundary 0x114380 128)
    (state : SavedState s t) (effect : (finishCopyEffect t).Holds t u) :
    MemoryWriteFrame t u #v[registerRegion s .rdi 32] := by
  apply effect.agrees.memoryWriteFrame
  intro c hc a ha
  obtain ⟨off, ho, i, hi, rfl⟩ := finish_copy_memory_component hc ha
  refine ⟨registerRegion s .rdi 32, by simp, ?_⟩
  rw [state.rbx, add_ofNat_add_ofNat]
  apply finish_output_contains pre
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl <;> omega

theorem finish_stack_word (pre : BinaryFieldPre s boundary 0x114380 128)
    (frame : MemoryWriteFrame t u #v[registerRegion s .rdi 32])
    {off : Nat} (ho : off ≤ 128) :
    (Operand.mem (stackPtr s - BitVec.ofNat 64 off) : Operand 64).read u =
      (Operand.mem (stackPtr s - BitVec.ofNat 64 off) : Operand 64).read t := by
  apply memLoad_congr
  intro i hi
  apply memByte_congr
  apply frame
  intro r hr hin
  have he : r = registerRegion s .rdi 32 := by simpa using hr
  subst r
  exact pre.separation (1 : Fin 3) (2 : Fin 3) (by decide) _ hin
    (stack_contains pre ho (by omega) hi)

theorem finish_copy_bytes {select : Bool} (pre : BinaryFieldPre s boundary 0x114380 128)
    (state : ReturnedState s t select) (effect : (finishCopyEffect t).Holds t u) :
    ∀ i < 32, u.external[s.regValue .rdi + BitVec.ofNat 64 i]? = outputBytes s select i := by
  have hw := effect.writes
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ at hw
  rcases hw with ⟨_, _, h0, h8, h16, h24⟩
  change (Operand.mem (t.regValue .rbx + 0) : Operand 64).read u =
    (Operand.mem (stackPtr t + 0) : Operand 64).read t at h0
  change (Operand.mem (t.regValue .rbx + 8) : Operand 64).read u =
    (Operand.mem (stackPtr t + 8) : Operand 64).read t at h8
  change (Operand.mem (t.regValue .rbx + 16) : Operand 64).read u =
    (Operand.mem (stackPtr t + 16) : Operand 64).read t at h16
  change (Operand.mem (t.regValue .rbx + 24) : Operand 64).read u =
    (Operand.mem (stackPtr t + 24) : Operand 64).read t at h24
  intro i hi
  have hread : memLoad u.external (t.regValue .rbx + BitVec.ofNat 64 (i / 8 * 8)) 64 =
      memLoad t.external (stackPtr t + BitVec.ofNat 64 (i / 8 * 8)) 64 := by
    have hdiv : i / 8 = 0 ∨ i / 8 = 1 ∨ i / 8 = 2 ∨ i / 8 = 3 := by omega
    rcases hdiv with h | h | h | h
    · simpa only [h, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero, memLoad_external] using h0
    · simpa only [h, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero, memLoad_external] using h8
    · simpa only [h, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero, memLoad_external] using h16
    · simpa only [h, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero, memLoad_external] using h24
  have hb := memByte_of_memLoad_eq hread (i % 8) (by omega)
  have hidx : i / 8 * 8 + i % 8 = i := by omega
  simp only [BitVec.add_assoc, ← BitVec.ofNat_add, hidx, state.rbx, state.rsp] at hb
  have hd := effect.agrees.grow _ ((finish_output_readable pre state.toSavedState
    (off := 0) (len := 32) (by decide)).mem i hi)
  have hs := (state.toSavedState.stack_readable pre (offset := 40) (len := 32)
    (by decide) (by decide)).mem i hi
  change (u.external[s.regValue .rdi + 0 + BitVec.ofNat 64 i]?).isSome at hd
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at hd
  obtain ⟨b, hdb⟩ := Option.isSome_iff_exists.mp hd
  obtain ⟨a, hsa⟩ := Option.isSome_iff_exists.mp hs
  change t.external[scratch s + BitVec.ofNat 64 i]? = some a at hsa
  have he : b = a := by
    simpa only [memByte, PhysicalMemory.read, hdb, hsa, Option.getD_some] using hb
  exact (hdb.trans (congrArg some he)).trans (hsa.symm.trans (state.selected i hi))

end P256.Proofs.Projective.Multiply.Machine.Lookup.Select
