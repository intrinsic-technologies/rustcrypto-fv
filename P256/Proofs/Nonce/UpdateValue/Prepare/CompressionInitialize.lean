import P256.Proofs.Nonce.UpdateValue.Prepare.CompressionPayload
import P256.Proofs.Nonce.UpdateValue.Prepare.Memory

set_option autoImplicit false

namespace P256.Proofs.Nonce.UpdateValue.Prepare

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem CompressionSetup.pre [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {state : State} (pre : DrbgCalleePre initial boundary 0x10a900 1168 state)
    (input : InnerPadded initial s state) : Pre s := by
  refine ⟨input.rip, ?_, ?_⟩
  · intro slot member
    have avoids : (Stack.region initial 1168).Avoids InPageTables :=
      fun a ha hp => pre.avoids _ (by simp) a ha (.inr hp)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals change MemWritable s (stackPtr s + _) _
    all_goals rw [ScalarFrame.scalar_stack_address input.rsp (by decide) (by decide)]
    all_goals apply writable_of_grow _ input.allocated
    all_goals first
      | exact stack_sub_writable8 pre.stack avoids (by decide) (by decide)
      | exact stack_sub_writable pre.stack avoids (by decide) (by decide) (by decide)
          (by have h := Nat.mod_lt (stackPtr initial - 321).toNat (by decide : 0 < 4096); omega)
  · intro slot member offset len bound
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact ScalarFrame.stack_code pre.callee input.toFrameState (by decide) (by decide) (by omega)

theorem CompressionSetup.context [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
    {state : State} (pre : DrbgCalleePre initial boundary 0x10a900 1168 state)
    (input : Context initial s state) (ready : ReadyToStep t) (h : (effect s).Holds s t) :
    Context initial t state := by
  apply input.after_agrees pre ready h.agrees
  · intro r member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    all_goals simp [effect, Effect.components, Write.component, Operand.component]
  · intro c member a covered
    simp only [effect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at member
    rcases member with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    all_goals try exact covered.elim
    all_goals change (Component.mem (stackPtr s + _) _).Covers a at covered
    all_goals rw [show stackPtr s = scratch initial from input.rsp] at covered
    all_goals exact work_contains_scratch pre (by decide) covered

theorem CompressionSetup.key_bytes {s t : RamState} (h : (effect s).Holds s t) :
    ∀ i < 64, t.external[rspOf s + 8 + BitVec.ofNat 64 i]? =
      s.external[rspOf s + 8 + BitVec.ofNat 64 i]? := by
  intro i hi
  apply h.agrees.byte
  intro c member covered
  simp only [effect, Effect.components, List.map_cons, List.map_nil,
    Write.component, Operand.component, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
  all_goals try exact covered
  all_goals obtain ⟨j, hj, eq⟩ := covered
  all_goals exact OffsetsApart.ne (len₂ := 64) (by unfold OffsetsApart; decide +kernel) (rspOf s) hj hi (by decide) eq.symm

theorem initialize_compression [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {state : State} (pre : DrbgCalleePre initial boundary 0x10a900 1168 state)
    (input : InnerPadded initial s state) :
    ∃ fuel t, Advances boundary fuel s t ∧ CompressionInput initial t state := by
  obtain ⟨fuel, t, run, ready, _, effect⟩ := CompressionSetup.run boundary pre.outerBoundary s
    (readyToStep input.machine input.bindingsSupported) (CompressionSetup.code input.loaded)
    (CompressionSetup.pre pre input)
  have context := CompressionSetup.context pre input.toContext ready effect
  have rsp : rspOf s = scratch initial := input.rsp
  have readable (offset len : Nat) (_bound : offset ≤ 488) (span : offset + len ≤ 488) :
      MemReadable t (rspOf s + BitVec.ofNat 64 offset) len := by
    rw [rsp, ← show stackPtr t = scratch initial from context.rsp]
    exact ScalarFrame.stack_readable pre.callee context.toFrameState (by decide) span
  have writes := effect.writes
  simp only [CompressionSetup.effect, Write.AllHold] at writes
  refine ⟨fuel, t, run, context, effect.rip, ?_, ?_, writes.2.2.2.2.2.2.2.2.2.1,
    ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [rsp] using (show t.regValue .rdi = rspOf s + 168 from writes.2.2.2.2.2.2.2.2.2.2)
  · simpa only [rsp] using (show t.regValue .rsi = rspOf s + 8 from writes.2.2.2.2.2.2.2.2.1)
  · simpa only [rsp] using (show t.regValue .r14 = rspOf s + 168 from writes.1)
  · apply hasBytes_copy input.key
    simpa only [rsp] using CompressionSetup.key_bytes effect
  · simpa only [rsp] using CompressionSetup.hash_words effect (readable 168 32 (by decide) (by decide))
  · simpa only [rsp] using CompressionSetup.position effect (readable 167 1 (by decide) (by decide))
  · simpa only [rsp] using CompressionSetup.blocks effect (readable 200 8 (by decide) (by decide))

end P256.Proofs.Nonce.UpdateValue.Prepare
