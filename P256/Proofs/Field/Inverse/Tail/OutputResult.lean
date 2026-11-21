import P256.Proofs.Field.Inverse.Tail.OutputMemory

set_option autoImplicit false

open P256.Proofs.Program (CalleePre)

namespace P256.Proofs.Field.Inverse

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)

theorem output_copy_state [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (state : FrameState s t)
    (ready : ReadyToStep u) (effect : (outputCopyEffect t).Holds t u) : FrameState s u := by
  refine ⟨state.toSavedState.after_agrees pre ready effect.agrees ?_ ?_, ?_⟩
  · apply effect.agrees.memoryWriteFrame
    intro c hc a hcov
    simp only [outputCopyEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component_reg, Write.component_mem, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try exact hcov.elim
    all_goals
      obtain ⟨i,hi,rfl⟩ := hcov
      change ∃ r∈#v[registerRegion s .rdi 40,workRegion s],
        r.Contains (t.regValue .rbx + _ + BitVec.ofNat 64 i).toNat
      rw [state.rbx]
      refine ⟨registerRegion s .rdi 40,by simp,?_⟩
      simp only [BitVec.ofNat_eq_ofNat]
      rw [add_ofNat_add_ofNat]
      exact output_contains pre (by omega)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [outputCopyEffect, Effect.components]
  · exact (effect.agrees.read (r := 4) (n := 64) (by simp [outputCopyEffect, Effect.components])).trans state.rsp

theorem output_stage [Bindings] {s t : RamState} {boundary : ReturnBoundary} {value : Nat} {select : Bool}
    (pre : Pre s boundary) (state : FrameState s t)
    (rip : t.RIP=0x114204) (rbp : t.regValue .rbp=if select then 1 else 0)
    (input : Nat256At t (stackPtr s-168) value) :
    ∃ n u, Advances boundary n t u ∧ FrameState s u ∧ u.RIP=0x11422d ∧
      Nat256At u (s.regValue .rdi) value ∧
      u.external[s.regValue .rdi+32]?=some (if select then 1 else 0) := by
  obtain ⟨n,u,run,ready,_,effect⟩ := output_copy boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported) (output_copy_code state.loaded)
    (outputCopyPre_of_frame pre state rip)
  have state1 := output_copy_state pre state ready effect
  have bx : (Operand.reg 3 : Operand 64).read t=s.regValue .rdi := state.rbx
  have sp : (Operand.reg 4 : Operand 64).read t=stackPtr s-168 := state.rsp
  have hw := effect.writes
  change _ ∧ _ ∧
    (Operand.mem ((Operand.reg 3 : Operand 64).read t+0) : Operand 64).read u = _ ∧
    (Operand.mem ((Operand.reg 3 : Operand 64).read t+8) : Operand 64).read u = _ ∧
    (Operand.mem ((Operand.reg 3 : Operand 64).read t+16) : Operand 64).read u = _ ∧
    (Operand.mem ((Operand.reg 3 : Operand 64).read t+24) : Operand 64).read u = _ ∧
    (Operand.mem ((Operand.reg 3 : Operand 64).read t+32) : Operand 8).read u =
      (Operand.reg 5 : Operand 8).read t at hw
  rw [bx,sp] at hw
  have allocated (i : Nat) (hi : i<40) : (u.external[s.regValue .rdi+BitVec.ofNat 64 i]?).isSome :=
    state1.allocated _ (Option.isSome_iff_exists.mpr (pre.outputAllocated _ (output_contains pre hi)))
  refine ⟨n,u,run,state1,effect.rip,?_,?_⟩
  · apply nat256At_copy_limbs input (fun i hi => allocated i (by omega))
    intro j hj
    have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
    rcases hc with rfl | rfl | rfl | rfl
    all_goals change (Operand.mem _ : Operand 64).read u = (Operand.mem _ : Operand 64).read t
    · simpa (config := {decide := true}) only [x86_compose, BitVec.sub_eq_add_neg, BitVec.add_assoc] using hw.2.2.1
    · simpa (config := {decide := true}) only [x86_compose, BitVec.sub_eq_add_neg, BitVec.add_assoc] using hw.2.2.2.1
    · simpa (config := {decide := true}) only [x86_compose, BitVec.sub_eq_add_neg, BitVec.add_assoc] using hw.2.2.2.2.1
    · simpa (config := {decide := true}) only [x86_compose, BitVec.sub_eq_add_neg, BitVec.add_assoc] using hw.2.2.2.2.2.1
  · have tag := hw.2.2.2.2.2.2
    change memLoad u.external (s.regValue .rdi+32) 8 = (t.regValue .rbp).setWidth 8 at tag
    rw [rbp] at tag
    have bytes : Bytes u.external (s.regValue .rdi+32) 1
        (storedByte (memLoad u.external (s.regValue .rdi+32) 8)) := by
      apply Bytes.of_memLoad (n := 8)
      intro i hi
      have hi0 : i=0 := by omega
      subst i
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using allocated 32 (by decide)
    rw [tag] at bytes
    have h := bytes 0 (by decide)
    cases select <;> simpa [storedByte] using h

end P256.Proofs.Field.Inverse
