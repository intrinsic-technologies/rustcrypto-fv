import P256.Proofs.Sec1.SquareRoot.Middle.CandidateCopy
import P256.Proofs.Program.WrapperMemory
set_option autoImplicit false

open P256.Proofs.Program

namespace P256.Proofs.Sec1.SquareRoot.Middle

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem candidate_copy_frame [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (state : FrameState s t)
    (effect : (candidateCopyEffect t).Holds t u) :
    MemoryWriteFrame t u #v[registerRegion s .rdi 40, workRegion s] := by
  apply effect.agrees.memoryWriteFrame
  intro c hc a hcov
  simp only [candidateCopyEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component_reg, Write.component_mem, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try exact hcov.elim
  all_goals
    obtain ⟨i, hi, rfl⟩ := hcov
    rw [state.stack_address]
    simp only [BitVec.reduceSub]
    exact ⟨workRegion s, by simp, ScalarFrame.Work.contains pre (by decide) (by decide) ⟨i, hi, rfl⟩⟩

theorem candidate_copy_bytes [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (state : FrameState s t)
    (effect : (candidateCopyEffect t).Holds t u)
    {offset len : Nat} (ho : offset ≤ 544) (hl : len ≤ offset + 8) :
    ∀ i < len, u.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      t.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  intro i hi
  apply effect.agrees.byte
  intro c hc hcov
  simp only [candidateCopyEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component_reg, Write.component_mem, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try exact hcov.elim
  all_goals
    obtain ⟨j,hj,he⟩ := hcov
    rw [state.stack_address] at he
    simp only [BitVec.reduceSub] at he
  · exact stack_sub_apart pre.stack (a := 576) (b := offset) (by decide) (by omega)
      (by decide) hl (.inl (by omega)) j hj i hi he.symm
  · exact stack_sub_apart pre.stack (a := 568) (b := offset) (by decide) (by omega)
      (by decide) hl (.inl (by omega)) j hj i hi he.symm
  · exact stack_sub_apart pre.stack (a := 560) (b := offset) (by decide) (by omega)
      (by decide) hl (.inl (by omega)) j hj i hi he.symm
  · exact stack_sub_apart pre.stack (a := 552) (b := offset) (by decide) (by omega)
      (by decide) hl (.inl (by omega)) j hj i hi he.symm

theorem candidate_copy_state [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (state : FrameState s t)
    (ready : ReadyToStep u) (effect : (candidateCopyEffect t).Holds t u) : FrameState s u := by
  refine ⟨state.toSavedState.after_agrees pre ready effect.agrees
    (candidate_copy_frame pre state effect) ?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp [candidateCopyEffect, Effect.components]
  · exact (effect.agrees.read (r := 4) (n := 64) (by simp [candidateCopyEffect, Effect.components])).trans state.rsp

end P256.Proofs.Sec1.SquareRoot.Middle
