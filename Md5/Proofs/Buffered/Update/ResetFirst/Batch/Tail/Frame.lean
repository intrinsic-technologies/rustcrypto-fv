import Md5.Proofs.Buffered.Update.ResetFirst.Batch.Tail.Ready
import Md5.Proofs.Buffered.Update.Calls

namespace Md5.Proofs.Buffered.ResetFirst

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem tailReadyEffect.update_agrees_of_kind {kind : UpdateKind} (hk : KindSupported kind) {s u v : RamState}
    (hsp : stackPtr u = stackPtr s) (he : (tailReadyEffect_of_kind kind u).Holds u v) :
    AgreesExcept (kind.changes s) u v := by
  apply he.agrees.widen
  · intro c hc hn
    simp only [tailReadyEffect_of_kind, Effect.components, List.map_cons, List.map_nil,
      Write.component_reg, Write.component_mem, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals rcases hk with rfl | rfl | rfl <;> simp [reg, UpdateKind.inputRegister, UpdateKind.changes, UpdateKind.workRegisters, Component.isMem] at hn ⊢
  · intro address c hc hcover
    simp only [tailReadyEffect_of_kind, Effect.components, List.map_cons, List.map_nil,
      Write.component_reg, Write.component_mem, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hcover.elim
    obtain ⟨i, hi, rfl⟩ := hcover
    have : i = 0 := by omega
    subst i
    refine ⟨.mem (kind.context s) 88, by simp [UpdateKind.changes], 63, by decide, ?_⟩
    rcases hk with rfl | rfl | rfl <;> simp [stackOffset, UpdateKind.context, UpdateKind.contextOffset, hsp, BitVec.add_assoc]

theorem tailReadyEffect.frame_of_kind [Bindings] {kind : UpdateKind} (hk : KindSupported kind) {boundary : ReturnBoundary}
    {message input : ByteArray} {s u v : RamState}
    (h : UpdatePre kind boundary message input s)
    (hsp : stackPtr u = stackPtr s) (he : (tailReadyEffect_of_kind kind u).Holds u v) :
    MemoryWriteFrame u v #v[UpdateKind.scratchRegion s,
      ⟨(kind.context s).toNat, 64⟩] := by
  apply he.agrees.memoryWriteFrame
  intro c hc address hcover
  simp only [tailReadyEffect_of_kind, Effect.components, List.map_cons, List.map_nil,
    Write.component_reg, Write.component_mem, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hcover.elim
  obtain ⟨i, hi, rfl⟩ := hcover
  have : i = 0 := by omega
  subst i
  have haddr : stackPtr u + stackOffset kind 71 = kind.context s + 63 := by
    rw [hsp]
    rcases hk with rfl | rfl | rfl <;> simp [stackOffset, UpdateKind.context, UpdateKind.contextOffset, BitVec.add_assoc]
  have hctx : (kind.context s).toNat + 88 < 2^32 := h.contextBounded
  refine ⟨⟨(kind.context s).toNat, 64⟩, by simp, ?_⟩
  change (kind.context s).toNat ≤ _ ∧
    _ < (kind.context s).toNat + 64
  have hn : (kind.context s + 63).toNat =
      (kind.context s).toNat + 63 := toNat_add_ofNat _ 63 (by omega)
  rw [BitVec.add_zero, haddr, hn]
  omega

theorem tailReadyEffect.update_agrees {s u v : RamState}
    (hsp : stackPtr u = stackPtr s) (he : (tailReadyEffect u).Holds u v) :
    AgreesExcept (UpdateKind.resetFirst.changes s) u v := by
  exact tailReadyEffect.update_agrees_of_kind (kind := .resetFirst) (Or.inl rfl) hsp he

theorem tailReadyEffect.frame [Bindings] {boundary : ReturnBoundary}
    {message input : ByteArray} {s u v : RamState}
    (h : UpdatePre .resetFirst boundary message input s)
    (hsp : stackPtr u = stackPtr s) (he : (tailReadyEffect u).Holds u v) :
    MemoryWriteFrame u v #v[UpdateKind.scratchRegion s,
      ⟨(UpdateKind.resetFirst.context s).toNat, 64⟩] := by
  exact tailReadyEffect.frame_of_kind (kind := .resetFirst) (Or.inl rfl) h hsp he

end Md5.Proofs.Buffered.ResetFirst
