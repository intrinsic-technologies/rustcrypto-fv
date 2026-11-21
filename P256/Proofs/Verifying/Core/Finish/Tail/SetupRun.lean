import P256.Proofs.Verifying.Core.Finish.Tail.Setup

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Finish.Tail

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame
open SecretKeyFromBytes.Scalar

theorem setup [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (hp : Core.Pre s boundary) (state : Frame s t) (rip : t.RIP = 0x10e098) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧
      (Setup.setupEffect t).Holds t u ∧
      (∀ i : Nat, 384 ≤ i → (i < 576 ∨ 580 ≤ i) → i < 1128 →
        u.external[frameBase s+BitVec.ofNat 64 i]? = t.external[frameBase s+BitVec.ofNat 64 i]?) := by
  have pre : Setup.SetupPre t := by
    refine ⟨rip,?_,?_,?_,?_,?_,?_⟩
    · have addr : stackPtr t+128 = stackPtr s-1048 := by
        rw [state.rsp]
        simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
        rfl
      change MemWritable t (stackPtr t+128) 1
      rw [addr]
      exact writable_of_grow (stack_sub_writable hp.stack
        (fun a ha h => hp.avoids _ (by simp) a ha (.inr h))
        (by decide) (by decide) (by decide) (by omega)) state.allocated
    · exact stack_writable (frameOffset := 1176) hp.toCalleePre state (by decide) (by decide) (by decide)
    · intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl
      all_goals exact local_writable8 hp state (by decide) (by decide)
    · intro off len hl
      exact stack_code (frameOffset := 1176) hp.toCalleePre state (by decide) (by decide) hl
    · intro off len hl
      exact stack_code (frameOffset := 1176) hp.toCalleePre state (by decide) (by decide) hl
    · intro i hi off len hl
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl
      all_goals exact stack_code (frameOffset := 1176) hp.toCalleePre state (by decide) (by decide) hl
  obtain ⟨n,u,run,ready,_,effect⟩ := Setup.setup_block boundary hp.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xe098 Setup.setupBytes
      (by decide) (by decide +kernel)) pre
  have writes : WritesWithin (Setup.setupEffect t).components
      #v[registerRegion s .rdi 24,workRegion s 9992] := by
    intro c hc a ha
    simp only [Setup.setupEffect,Effect.components,List.map_cons,List.map_nil,
      Write.component_reg,Write.component_mem,List.cons_append,List.nil_append,
      List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals try exact ha.elim
    all_goals exact ⟨_,by simp,local_work_contains hp state (by decide) ha⟩
  refine ⟨n,u,run,state.after_effect hp.toCalleePre (by decide) ready effect.agrees writes
    (by simp [Setup.setupEffect,Effect.components]),effect,?_⟩
  intro i lo apart hi
  apply effect.agrees.byte
  intro c hc ha
  simp only [Setup.setupEffect,Effect.components,List.map_cons,List.map_nil,
    Write.component_reg,Write.component_mem,List.cons_append,List.nil_append,
    List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals try exact ha.elim
  all_goals obtain ⟨j,hj,eq⟩ := ha
  all_goals change _ = stackPtr t+_+_ at eq
  all_goals rw [state.rsp] at eq
  all_goals change _ = frameBase s+_+_ at eq
  all_goals bv_omega

end P256.Proofs.Verifying.Core.Finish.Tail
