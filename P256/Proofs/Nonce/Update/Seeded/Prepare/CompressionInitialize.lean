import P256.Proofs.Nonce.Update.Seeded.Prepare.CompressionPayload
import P256.Proofs.Nonce.Update.Seeded.Prepare.Memory

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Seeded.Prepare

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem CompressionSetup.pre [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {original state : State} (pre : DrbgCalleePre initial boundary 0x109f30 1856 original)
    (input : InnerPadded initial s state) : Pre s := by
  refine ⟨input.rip, ?_, ?_⟩
  · intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals change MemWritable s (stackPtr s + _) _
    all_goals first
      | exact stack_writable8 input.toFrameState pre (by decide) (by decide) (by decide)
      | skip
    rw [stack_address input.toFrameState (by decide : 319 ≤ 680)]
    apply writable_of_grow _ input.allocated
    exact stack_sub_writable pre.stack (fun a ha hp => pre.avoids _ (by simp) a ha (.inr hp)) (by decide) (by decide) (by decide) (by omega)
  · intro slot member offset len bound
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact stack_codeApart input.toFrameState pre (by decide) (by decide) (by decide) bound

theorem CompressionSetup.context [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
    {original state : State} (pre : DrbgCalleePre initial boundary 0x109f30 1856 original)
    (input : Context initial s state) (ready : ReadyToStep t) (h : (effect s).Holds s t) :
    Context initial t state := by
  apply input.after_agrees pre ready h.agrees
  · intro r member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    all_goals simp [effect, Effect.components, Write.component, Operand.component]
  · intro c member a covered
    simp only [effect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at member
    rcases member with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    all_goals try exact covered.elim
    all_goals change (Component.mem (stackPtr s + _) _).Covers a at covered
    all_goals rw [show stackPtr s = scratch initial from input.rsp] at covered
    all_goals exact Update.Prepare.work_contains_scratch pre (by decide) covered
  · intro i hi
    apply h.agrees.byte
    intro c member covered
    simp only [effect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at member
    rcases member with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    all_goals try exact covered.elim
    all_goals obtain ⟨j, hj, equal⟩ := covered
    all_goals rw [show rspOf s = scratch initial from input.rsp] at equal
    all_goals exact OffsetsApart.ne (len₁ := 24) (by unfold OffsetsApart; decide +kernel) (scratch initial) hi hj (by decide) equal

theorem CompressionSetup.key_bytes {s t : RamState} (h : (effect s).Holds s t) :
    ∀ i < 64, t.external[rspOf s + 0#64 + BitVec.ofNat 64 i]? =
      s.external[rspOf s + 0#64 + BitVec.ofNat 64 i]? := by
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
    {original state : State} (pre : DrbgCalleePre initial boundary 0x109f30 1856 original)
    (input : InnerPadded initial s state) :
    ∃ fuel t, Advances boundary fuel s t ∧ CompressionInput initial t state := by
  obtain ⟨fuel, t, run, ready, _, effect⟩ := CompressionSetup.run boundary pre.outerBoundary s
    (readyToStep input.machine input.bindingsSupported) (CompressionSetup.code input.loaded)
    (CompressionSetup.pre pre input)
  have context := CompressionSetup.context pre input.toContext ready effect
  have rsp : rspOf s = scratch initial := input.rsp
  have readable (offset len : Nat) (bound : offset ≤ 680) (span : offset + len ≤ 688) :
      MemReadable t (rspOf s + BitVec.ofNat 64 offset) len := by
    rw [rsp, ← show stackPtr t = scratch initial from context.rsp]
    exact stack_readable context.toFrameState pre (by decide) bound span
  have writes := effect.writes
  simp only [CompressionSetup.effect, Write.AllHold] at writes
  refine ⟨fuel, t, run, context, effect.rip, ?_, ?_, ?_, writes.2.2.2.2.2.2.2.2.2.1,
    ?_, ?_, ?_, ?_⟩
  · simpa only [rsp] using (show t.regValue .r12 = rspOf s + 320 from writes.1)
  · simpa only [rsp] using (show t.regValue .rdi = rspOf s + 320 from writes.2.2.2.2.2.2.2.2.2.2)
  · simpa only [rsp] using (show t.regValue .rsi = rspOf s from writes.2.2.2.2.2.2.2.2.1)
  · apply hasBytes_copy input.key
    simpa only [rsp, BitVec.add_zero] using CompressionSetup.key_bytes effect
  · simpa only [rsp] using CompressionSetup.hash_words effect (readable 320 32 (by decide) (by decide))
  · simpa only [rsp] using CompressionSetup.position effect (readable 319 1 (by decide) (by decide))
  · simpa only [rsp] using CompressionSetup.blocks effect (readable 352 8 (by decide) (by decide))

end P256.Proofs.Nonce.Update.Seeded.Prepare
