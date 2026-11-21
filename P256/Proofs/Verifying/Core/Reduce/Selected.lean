import P256.Proofs.Verifying.Core.Reduce.ChoiceFlag
import P256.Proofs.Verifying.Core.Reduce.Select

set_option autoImplicit false

open P256.Proofs.SecretKeyFromBytes.Scalar (Limbs)
open P256.Proofs.Program (CalleePre programLoaded_codeIn programText_slice readyToStep)

namespace P256.Proofs.Verifying.Core.Reduce

open P256.Proofs.Program
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem selection_pre [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x113120 32 32 104) (state : FrameState s t)
    (rip : t.RIP = 0x113204) : SelectionPre t := by
  refine ⟨rip, ?_, ?_, ?_⟩
  · change MemWritable t (stackPtr t + BitVec.ofNat 64 7) 1
    rw [scalar_stack_address state.rsp (by decide)]
    exact writable_of_grow
      (stack_sub_writable pre.stack (fun a ha hpt => pre.avoids _ (by simp) a ha (.inr hpt)) (offset := 81) (len := 1)
        (by decide) (by decide) (by decide) (by omega)) state.allocated
  · intro offset ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl
    all_goals exact stack_readable pre state (by decide)
  · intro offset len bound
    exact stack_code pre state (offset := 7) (len := 1) (by decide) bound

theorem selection_writes [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x113120 32 32 104) (state : FrameState s t) :
    WritesWithin (selectionEffect t).components #v[registerRegion s .rdi 32, workRegion s] := by
  intro c hc a ha
  simp only [selectionEffect, Effect.components, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false, Write.component_reg, Write.component_mem] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  refine ⟨workRegion s, by simp, ?_⟩
  change (Component.mem (stackPtr t + BitVec.ofNat 64 7) 1).Covers a at ha
  rw [scalar_stack_address state.rsp (by decide)] at ha
  exact work_contains pre (by decide) (by decide) ha

theorem select_body [Bindings] {s t : RamState} {boundary : ReturnBoundary} {a : Limbs}
    (pre : CalleePre s boundary 0x113120 32 32 104) (state : Subtracted s t a) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u ∧ u.RIP = 0x113239 ∧
      u.regValue .rax = s.regValue .rdi ∧
      (Limbs.mk (u.regValue .rcx) (u.regValue .r12) (u.regValue .rbp) (u.regValue .rbx)) = reduceOrder a := by
  obtain ⟨v,hv,sv,pv,av,fv⟩ := choices pre state
  obtain ⟨fuel,u,hu,ready,_,effect⟩ := selection_correct boundary pre.outerBoundary v
    (readyToStep sv.machine sv.bindingsSupported)
    (programText_slice (programLoaded_codeIn sv.loaded) 0x13204 selectionBytes
      (by decide +kernel) (by decide +kernel)) (selection_pre pre sv pv)
  have final := sv.after_effect pre (by decide) ready effect.agrees (selection_writes pre sv)
    (by simp [selectionEffect, Effect.components])
  have sp : stackPtr v = stackPtr t := sv.rsp.trans state.rsp.symm
  have x0 : (Operand.mem (stackPtr v+24) : Operand 64).read v = a.l0 := by
    rw [sp]
    exact (choice_slot fv (offset := 24) (by simp)).trans state.original0
  have d0 : (Operand.mem (stackPtr v+16) : Operand 64).read v = (subtractOrder a).l0 := by
    rw [sp]
    exact (choice_slot fv (offset := 16) (by simp)).trans state.difference0
  have ptr : (Operand.mem (stackPtr v+32) : Operand 64).read v = s.regValue .rdi := by
    rw [sp]
    exact (choice_slot fv (offset := 32) (by simp)).trans state.outputPointer
  have x1 : v.regValue .r12 = a.l1 :=
    (fv.read (n := 64) (r := 12) (by simp [choiceFrame])).trans state.original1
  have x2 : v.regValue .rbp = a.l2 :=
    (fv.read (n := 64) (r := 5) (by simp [choiceFrame])).trans state.original2
  have x3 : v.regValue .rbx = a.l3 :=
    (fv.read (n := 64) (r := 3) (by simp [choiceFrame])).trans state.original3
  have d1 : v.regValue .r13 = (subtractOrder a).l1 :=
    (fv.read (n := 64) (r := 13) (by simp [choiceFrame])).trans state.difference1
  have d2 : v.regValue .r15 = (subtractOrder a).l2 :=
    (fv.read (n := 64) (r := 15) (by simp [choiceFrame])).trans state.difference2
  have d3 : v.regValue .r14 = (subtractOrder a).l3 :=
    (fv.read (n := 64) (r := 14) (by simp [choiceFrame])).trans state.difference3
  have al : (Operand.reg 0 : Operand 8).read v =
      if SecretKeyFromBytes.Scalar.orderBorrow a = 0 then 1 else 0 := by
    change (v.regValue .rax).setWidth 8 = _
    rw [av]
    split <;> rfl
  refine ⟨15+fuel,u,hv.trans hu,final,effect.rip,effect.writes.2.1.trans ptr,?_⟩
  have y0 : u.regValue .rcx = if (Operand.reg 0 : Operand 8).read v = 0 then
      (Operand.mem (stackPtr v+24) : Operand 64).read v else
      (Operand.mem (stackPtr v+16) : Operand 64).read v := effect.writes.2.2.1
  have y1 : u.regValue .r12 = if (Operand.reg 0 : Operand 8).read v = 0 then
      v.regValue .r12 else v.regValue .r13 := effect.writes.2.2.2.2.1
  have y2 : u.regValue .rbp = if (Operand.reg 0 : Operand 8).read v = 0 then
      v.regValue .rbp else v.regValue .r15 := effect.writes.2.2.2.2.2.1
  have y3 : u.regValue .rbx = if (Operand.reg 0 : Operand 8).read v = 0 then
      v.regValue .rbx else v.regValue .r14 := effect.writes.2.2.2.2.2.2
  rw [y0,y1,y2,y3,al,x0,x1,x2,x3,d0,d1,d2,d3]
  by_cases h : SecretKeyFromBytes.Scalar.orderBorrow a = 0
  · simp only [h, ↓reduceIte, reduceOrder]
    rfl
  · simp only [h, ↓reduceIte]
    change a = reduceOrder a
    unfold reduceOrder
    split
    · contradiction
    · rfl

end P256.Proofs.Verifying.Core.Reduce
