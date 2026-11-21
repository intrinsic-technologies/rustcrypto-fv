import Md5.Proofs.Buffered.Update.Slices.Tail.Ready
import Md5.Proofs.Buffered.Update.Calls.Frame

namespace Md5.Proofs.Buffered.Update.Slices

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem tailReadyEffect.update_agrees {variant : Bool} {s u v : RamState}
    (hsp : stackPtr u = stackPtr s) (he : (tailReadyEffect variant u).Holds u v) :
    AgreesExcept ((kind variant).changes s) u v := by
  apply he.agrees.widen
  · intro c hc hn
    simp only [tailReadyEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component_reg, Write.component_mem, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals cases variant <;> simp [UpdateKind.changes, UpdateKind.workRegisters, kind, Component.isMem] at hn ⊢
  · intro address c hc hcover
    simp only [tailReadyEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component_reg, Write.component_mem, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hcover.elim
    obtain ⟨i, hi, rfl⟩ := hcover
    have : i = 0 := by omega
    subst i
    refine ⟨.mem ((kind variant).context s) 88, by simp [UpdateKind.changes], 63, by decide, ?_⟩
    simp only [kind_context, hsp, BitVec.add_zero,
      BitVec.add_assoc]
    rfl

theorem tailReadyEffect.frame {variant : Bool} [Bindings] {boundary : ReturnBoundary}
    {message input : ByteArray} {s u v : RamState}
    (h : UpdatePre (kind variant) boundary message input s)
    (hsp : stackPtr u = stackPtr s) (he : (tailReadyEffect variant u).Holds u v) :
    MemoryWriteFrame u v #v[UpdateKind.scratchRegion s,
      ⟨((kind variant).context s).toNat, 64⟩] := by
  apply he.agrees.memoryWriteFrame
  intro c hc address hcover
  simp only [tailReadyEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component_reg, Write.component_mem, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hcover.elim
  obtain ⟨i, hi, rfl⟩ := hcover
  have : i = 0 := by omega
  subst i
  have haddr : stackPtr u + 255 = (kind variant).context s + 63 := by
    rw [hsp]
    rw [kind_context]
    change stackPtr s + 255 = stackPtr s + 192 + 63
    rw [BitVec.add_assoc]
    rfl
  have hctx : ((kind variant).context s).toNat + 88 < 2^32 := h.contextBounded
  refine ⟨⟨((kind variant).context s).toNat, 64⟩, by simp, ?_⟩
  change ((kind variant).context s).toNat ≤ _ ∧
    _ < ((kind variant).context s).toNat + 64
  have hn : ((kind variant).context s + 63).toNat =
      ((kind variant).context s).toNat + 63 := toNat_add_ofNat _ 63 (by omega)
  rw [BitVec.add_zero, haddr, hn]
  omega

end Md5.Proofs.Buffered.Update.Slices
