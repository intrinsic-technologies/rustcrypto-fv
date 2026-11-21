import P256.Proofs.Field.Inverse.Tail.Support
import P256.Proofs.SecretKeyFromBytes.Choice

set_option autoImplicit false

open P256.Proofs.SecretKeyFromBytes (ChoicePre choice_code_loaded choice_correct)
open P256.Proofs.Program (CalleePre boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice)

namespace P256.Proofs.Field.Inverse

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)

theorem choice_stage [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (state : FrameState s t)
    (rip : t.RIP = 0x11414f) :
    ∃ u, Advances boundary 6 t u ∧ FrameState s u ∧ u.RIP = 0x114154 ∧
      (Operand.reg 0 : Operand 64).read u = ((Operand.reg 7 : Operand 8).read t).setWidth 64 ∧
      (∀ {offset len : Nat}, offset ≤ 168 → len ≤ offset+8 → ∀ i < len,
        u.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
          t.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?) := by
  have push : pushAddr t = stackPtr s - 176 := by
    simp only [pushAddr, state.rsp, BitVec.sub_sub, BitVec.reduceAdd]; rfl
  have hpush : PushPre 0x11414f 5 t := by
    refine ⟨rip, ?_, ?_⟩
    · rw [push]
      exact P256.Proofs.Program.writable_of_grow (P256.Proofs.Program.stack_sub_writable8 pre.stack (fun a ha ht ↦ pre.avoids _ (by simp) a ha (.inr ht))
        (offset := 176) (by decide) (by decide)) state.allocated
    · rw [push]
      exact stack_code_apart pre (codeOffset := 0x1414f) (by decide) (by decide) (by decide)
  obtain ⟨t1,run1,ready1,effect1⟩ :=
    (call_rel32_effect_step 0x11414f 0x4f1c (by decide)).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0x1414f
        [0xe8,0x1c,0x4f,0x0,0x0] (by decide) (by decide +kernel)) hpush
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x19070 (by decide)))
  have sp1 : stackPtr t1 = stackPtr s - 176 := effect1.writes.1.trans push
  have frame1 : MemoryWriteFrame t t1 #v[registerRegion s .rdi 40, workRegion s] := by
    apply effect1.agrees.memoryWriteFrame
    intro c hc a hcov
    simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> try exact hcov.elim
    obtain ⟨i,hi,rfl⟩ := hcov
    rw [push]
    exact ⟨workRegion s, by simp, ScalarFrame.Work.contains pre (by decide) (by decide) ⟨i, hi, rfl⟩⟩
  have state1 := state.toSavedState.after_agrees pre ready1 effect1.agrees frame1 (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp)
  have scratch : stackPtr t1 - 1 = stackPtr s - 177 := by
    rw [sp1, BitVec.sub_sub]; rfl
  have return1 : stackTop t1 = 0x114154 := (callEffect_stack effect1).1
  have choicePre : ChoicePre t1 := by
    refine ⟨effect1.rip, ?_, ?_, ?_, ?_⟩
    · rw [scratch]
      apply P256.Proofs.Program.writable_of_grow (P256.Proofs.Program.stack_sub_writable pre.stack (fun a ha ht ↦ pre.avoids _ (by simp) a ha (.inr ht))
        (offset := 177) (len := 1) (by decide) (by decide) (by decide) (by omega)) state1.allocated
    · rw [sp1]
      exact P256.Proofs.Program.readable_of_grow (P256.Proofs.Program.stack_sub_readable pre.stack (by decide) (by decide)) state1.allocated
    · rw [return1]; decide
    · rw [scratch]
      exact stack_code_apart pre (codeOffset := 0x19070) (by decide) (by decide) (by decide)
  obtain ⟨t2,run2,ready2,result⟩ := choice_correct ready1 (choice_code_loaded state1.loaded) choicePre (by
    intro ip hip
    simp only [return1, List.mem_cons, List.not_mem_nil, or_false] at hip
    rcases hip with rfl | rfl | rfl | rfl | rfl
    all_goals apply boundary_ne_program pre.outerBoundary
    · exact inProgram_of_textOffset 0x19074 (by decide)
    · exact inProgram_of_textOffset 0x19078 (by decide)
    · exact inProgram_of_textOffset 0x1907c (by decide)
    · exact inProgram_of_textOffset 0x19080 (by decide)
    · exact inProgram_of_textOffset 0x14154 (by decide))
  have frame2 : MemoryWriteFrame t1 t2 #v[registerRegion s .rdi 40, workRegion s] := by
    apply result.agrees.memoryWriteFrame
    intro c hc a hcov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> try exact hcov.elim
    obtain ⟨i,hi,rfl⟩ := hcov
    rw [scratch]
    exact ⟨workRegion s, by simp, ScalarFrame.Work.contains pre (by decide) (by decide) ⟨i, hi, rfl⟩⟩
  have state2 := state1.after_agrees pre ready2 result.agrees frame2 (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp)
  refine ⟨t2,run1.trans run2,⟨state2,?_⟩,result.rip.trans return1,?_,?_⟩
  · change stackPtr t2 = _
    rw [result.rsp]
    change stackPtr t1 + 8 = _
    rw [sp1]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  · rw [result.rax, effect1.agrees.read (r := 7) (n := 8) (by simp)]
  · intro offset len ho hl i hi
    apply Eq.trans (result.agrees.byte ?_) (effect1.agrees.byte ?_)
    · intro c hc hcov
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl <;> try exact hcov.elim
      obtain ⟨j,hj,he⟩ := hcov
      rw [scratch] at he
      exact stack_sub_apart pre.stack (a := 177) (b := offset) (by decide) (by omega)
        (by decide) hl (.inl (by omega)) j hj i hi he.symm
    · intro c hc hcov
      simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;> try exact hcov.elim
      obtain ⟨j,hj,he⟩ := hcov
      rw [push] at he
      exact stack_sub_apart pre.stack (a := 176) (b := offset) (by decide) (by omega)
        (by decide) hl (.inl (by omega)) j hj i hi he.symm

end P256.Proofs.Field.Inverse
