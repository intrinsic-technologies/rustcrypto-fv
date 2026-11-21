import P256.Proofs.Field.Inverse.Tail.OutputCopy
import P256.Proofs.Field.Inverse.Tail.Support

set_option autoImplicit false

open P256.Proofs.Program (CalleePre inProgram_of_textOffset memoryRegion_contains_add)

namespace P256.Proofs.Field.Inverse

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)

variable [Bindings] {s t u : RamState} {boundary : ReturnBoundary}

theorem output_contains (pre : Pre s boundary)
    {i : Nat} (hi : i<40) : (registerRegion s .rdi 40).Contains
      (s.regValue .rdi+BitVec.ofNat 64 i).toNat :=
  memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) hi

theorem output_readable (pre : Pre s boundary)
    (state : SavedState s t) {off len : Nat} (hn : off+len≤40) :
    MemReadable t (s.regValue .rdi+BitVec.ofNat 64 off) len := by
  have hb : (s.regValue .rdi).toNat+40<2^32 := pre.outputBounded
  refine ⟨?_,?_⟩
  · rw [toNat_add_ofNat _ _ (by omega)]; omega
  · intro i hi
    rw [add_ofNat_add_ofNat]
    exact state.allocated _ (Option.isSome_iff_exists.mpr (pre.outputAllocated _ (output_contains pre (by omega))))

theorem output_writable (pre : Pre s boundary)
    (state : SavedState s t) {off len : Nat} (hn : off+len≤40) (hl : 0<len) :
    P256.Proofs.Common.Instructions.CrossPageStore.Writable t (s.regValue .rdi+BitVec.ofNat 64 off) len := by
  refine ⟨output_readable pre state hn,tables_of_not_reserved hl (output_readable pre state hn).low ?_⟩
  intro i hi hin
  apply pre.avoids (registerRegion s .rdi 40) (by simp) _ _ (.inr hin)
  rw [add_ofNat_add_ofNat]
  exact output_contains pre (by omega)

theorem output_code_apart (pre : Pre s boundary)
    {off len pc n : Nat} (hn : off+len≤40) (hp : pc+n≤118431) :
    RangeApart (s.regValue .rdi+BitVec.ofNat 64 off) len
      (Extracted.textAddress+BitVec.ofNat 64 pc) n := by
  intro i hi j hj he
  apply pre.avoids (registerRegion s .rdi 40) (by simp)
    (s.regValue .rdi+BitVec.ofNat 64 off+BitVec.ofNat 64 i) _ (.inl ?_)
  · rw [add_ofNat_add_ofNat]; exact output_contains pre (by omega)
  · rw [he,add_ofNat_add_ofNat]
    exact inProgram_of_textOffset (pc+j) (by omega)

theorem output_stack_apart (pre : Pre s boundary)
    {off len stackOff stackLen : Nat} (hn : off+len≤40)
    (hs : stackOff≤880) (hl : stackLen≤stackOff+8) :
    RangeApart (s.regValue .rdi+BitVec.ofNat 64 off) len
      (stackPtr s-BitVec.ofNat 64 stackOff) stackLen := by
  intro i hi j hj he
  apply pre.separation (1 : Fin 3) (2 : Fin 3) (by decide) _ _ (ScalarFrame.stack_contains pre hs hl ⟨j, hj, rfl⟩)
  rw [←he,add_ofNat_add_ofNat]
  exact output_contains pre (by omega)

theorem outputCopyPre_of_frame (pre : Pre s boundary)
    (state : FrameState s t) (rip : t.RIP=0x114204) : OutputCopyPre t := by
  refine ⟨rip,?_,?_,?_,?_,?_,?_⟩
  · intro i hi
    rw [state.stack_address]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    all_goals simp only [BitVec.reduceSub]
    all_goals exact P256.Proofs.Program.readable_of_grow (P256.Proofs.Program.stack_sub_readable pre.stack (by decide) (by decide)) state.allocated
  · intro i hi
    change P256.Proofs.Common.Instructions.CrossPageStore.Writable t (t.regValue .rbx+i) 8
    rw [state.rbx]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    all_goals exact output_writable pre state.toSavedState (by decide) (by decide)
  · intro i hi pc n hn
    change RangeApart (t.regValue .rbx+i) 8 _ n
    rw [state.rbx]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    all_goals exact output_code_apart pre (by decide) hn
  · change MemWritable t (t.regValue .rbx+32) 1
    rw [state.rbx]
    have hr := output_readable pre state.toSavedState (off := 32) (len := 1) (by decide)
    apply MemWritable.of_not_reserved (by decide) hr.low hr.mem
    intro i hi hres
    apply pre.avoids (registerRegion s .rdi 40) (by simp) _ _ (.inr hres)
    have hi0 : i=0 := by omega
    subst i
    simp only [BitVec.add_zero]
    exact output_contains pre (i := 32) (by decide)
  · intro pc n hn
    change RangeApart (t.regValue .rbx+32) 1 _ n
    rw [state.rbx]
    exact output_code_apart pre (off := 32) (by decide) hn
  · intro i hi j hj
    change RangeApart (t.regValue .rbx+i) 8 ((Operand.reg 4 : Operand 64).read t+j) 8
    rw [state.rbx,state.stack_address]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi hj
    rcases hi with rfl | rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl | rfl
    all_goals simp only [BitVec.reduceSub]
    all_goals exact output_stack_apart pre (by decide) (by decide) (by decide)

end P256.Proofs.Field.Inverse
