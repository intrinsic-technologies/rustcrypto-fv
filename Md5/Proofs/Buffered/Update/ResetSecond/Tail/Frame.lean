import Md5.Proofs.Buffered.Update.ResetSecond.Tail.Ready
import Md5.Proofs.Buffered.Update.Calls

namespace Md5.Proofs.Buffered.ResetSecond

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem tailReadyEffect.update_agrees {kind : UpdateKind} {s u v : RamState}
    (hkind : kind = .resetSecond ∨ kind = .finalizeResetSecond ∨ kind = .resetDiscardSecond)
    (hsp : stackPtr u = stackPtr s) (he : (tailReadyEffect kind u).Holds u v) :
    AgreesExcept (kind.changes s) u v := by
  apply he.agrees.widen
  · intro c hc hn
    by_cases hk : kind = .resetDiscardSecond
    all_goals simp only [tailReadyEffect, hk, ite_true, ite_false, List.append_nil, Effect.components, List.map_cons, List.map_nil,
      Write.component_reg, Write.component_mem, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    all_goals first
      | (rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      | (rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals rcases hkind with rfl | rfl | rfl <;> simp [UpdateKind.changes, UpdateKind.workRegisters, UpdateKind.inputRegister, Component.isMem] at hk hn ⊢
  · intro address c hc hcover
    by_cases hk : kind = .resetDiscardSecond
    all_goals simp only [tailReadyEffect, hk, ite_true, ite_false, List.append_nil, Effect.components, List.map_cons, List.map_nil,
      Write.component_reg, Write.component_mem, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    all_goals first
      | (rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      | (rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals try exact hcover.elim
    all_goals
      obtain ⟨i, hi, rfl⟩ := hcover
      have : i = 0 := by omega
      subst i
      refine ⟨.mem (kind.context s) 88, by simp [UpdateKind.changes], 63, by decide, ?_⟩
      try rw [← hk]
      simp only [UpdateKind.context, UpdateKind.contextOffset, hsp, BitVec.add_zero,
        BitVec.add_assoc]
      rfl

theorem tailReadyEffect.frame [Bindings] {kind : UpdateKind} {boundary : ReturnBoundary}
    {message input : ByteArray} {s u v : RamState}
    (h : UpdatePre kind boundary message input s)
    (hsp : stackPtr u = stackPtr s) (he : (tailReadyEffect kind u).Holds u v) :
    MemoryWriteFrame u v #v[UpdateKind.scratchRegion s,
      ⟨(kind.context s).toNat, 64⟩] := by
  apply he.agrees.memoryWriteFrame
  intro c hc address hcover
  by_cases hk : kind = .resetDiscardSecond
  all_goals simp only [tailReadyEffect, hk, ite_true, ite_false, List.append_nil, Effect.components, List.map_cons, List.map_nil,
    Write.component_reg, Write.component_mem, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  all_goals first
    | (rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    | (rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals try exact hcover.elim
  all_goals
    obtain ⟨i, hi, rfl⟩ := hcover
    have : i = 0 := by omega
    subst i
    have haddr : kind.context u + 63 = kind.context s + 63 := by
      simp only [UpdateKind.context, hsp]
    have hctx : (kind.context s).toNat + 88 < 2^32 := h.contextBounded
    refine ⟨⟨(kind.context s).toNat, 64⟩, by simp, ?_⟩
    change (kind.context s).toNat ≤ _ ∧
      _ < (kind.context s).toNat + 64
    have hn : (kind.context s + 63).toNat =
        (kind.context s).toNat + 63 := toNat_add_ofNat _ 63 (by omega)
    try rw [← hk]
    rw [BitVec.add_zero, haddr, hn]
    omega

end Md5.Proofs.Buffered.ResetSecond
