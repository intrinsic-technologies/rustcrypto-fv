import Md5.Proofs.Buffered.Update.ResetSecond.Full.Fill.Ready
import Md5.Proofs.Buffered.Update.ResetSecond.Counter
import Md5.Proofs.Buffered.Update.ResetSecond.Full.Fill.Count
import Md5.Proofs.Buffered.Update.Preservation

namespace Md5.Proofs.Buffered.ResetSecond

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem fillReadyEffect_agrees {kind : UpdateKind}
    (hkind : kind = .resetSecond ∨ kind = .finalizeResetSecond ∨ kind = .resetDiscardSecond) {s t : RamState} (he : (fillReadyEffect kind s).Holds s t) :
    AgreesExcept (kind.changes s) s t := by
  apply he.agrees.mono
  intro c hm
  simp only [fillReadyEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component_reg, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rcases hkind with rfl | rfl | rfl <;> simp [UpdateKind.changes, UpdateKind.workRegisters, positionRegister, savedInputRegister]

theorem incrementPrepareEffect_agrees {kind : UpdateKind}
    (hkind : kind = .resetSecond ∨ kind = .finalizeResetSecond ∨ kind = .resetDiscardSecond) {initial s t : RamState} (hsp : stackPtr s = stackPtr initial)
    (he : (incrementPrepareEffect kind s).Holds s t) :
    AgreesExcept (kind.changes initial) s t := by
  apply he.agrees.widen
  · intro c hm hn
    simp only [incrementPrepareEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component_reg, Write.component_mem, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Bool.noConfusion hn
    all_goals rcases hkind with rfl | rfl | rfl <;> simp [UpdateKind.changes, UpdateKind.workRegisters]
  · intro address c hm hcover
    simp only [incrementPrepareEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component_reg, Write.component_mem, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hcover.elim
    refine ⟨.mem (kind.context initial) 88,
      by simp [UpdateKind.changes], ?_⟩
    obtain ⟨i, hi, rfl⟩ := hcover
    refine ⟨80 + i, by omega, ?_⟩
    simp [UpdateKind.context, hsp, BitVec.ofNat_add, BitVec.add_assoc]

theorem fillCountEffect_agrees {kind : UpdateKind}
    (hkind : kind = .resetSecond ∨ kind = .finalizeResetSecond ∨ kind = .resetDiscardSecond) {initial s t : RamState} (hsp : stackPtr s = stackPtr initial)
    (he : (fillCountEffect kind s).Holds s t) :
    AgreesExcept (kind.changes initial) s t := by
  apply he.agrees.widen
  · intro c hm hn
    simp only [fillCountEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component_reg, Write.component_mem, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl
    · exact Bool.noConfusion hn
    all_goals rcases hkind with rfl | rfl | rfl <;> simp [UpdateKind.changes, UpdateKind.workRegisters, UpdateKind.inputRegister]
  · intro address c hm hcover
    simp only [fillCountEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component_reg, Write.component_mem, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl
    all_goals try exact hcover.elim
    refine ⟨.mem (kind.context initial) 88,
      by simp [UpdateKind.changes], ?_⟩
    obtain ⟨i, hi, rfl⟩ := hcover
    refine ⟨63 + i, by omega, ?_⟩
    simp [UpdateKind.context, hsp, BitVec.ofNat_add, BitVec.add_assoc]

theorem fillCountEffect_frame [Bindings] {kind : UpdateKind}
    (_hkind : kind = .resetSecond ∨ kind = .finalizeResetSecond ∨ kind = .resetDiscardSecond) {boundary : ReturnBoundary}
    {message input : ByteArray} {initial s t : RamState}
    (h : UpdatePre kind boundary message input initial)
    (hsp : stackPtr s = stackPtr initial) (he : (fillCountEffect kind s).Holds s t) :
    MemoryWriteFrame s t
      #v[UpdateKind.scratchRegion initial, ⟨(kind.context initial).toNat, 64⟩] := by
  apply he.agrees.memoryWriteFrame
  intro c hm address hcover
  simp only [fillCountEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component_reg, Write.component_mem, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl
  all_goals try exact hcover.elim
  refine ⟨⟨(kind.context initial).toNat, 64⟩, by simp, ?_⟩
  have hb : (⟨(kind.context initial).toNat, 64⟩ : MemoryRegion).Bounded := by
    have hh : (kind.context initial).toNat + 88 < 2^32 := h.contextBounded
    change (kind.context initial).toNat + 64 < 2^32
    omega
  apply Block.contains_of_mem_covers hb
  obtain ⟨i, hi, rfl⟩ := hcover
  refine ⟨63 + i, by change 63 + i < 64; omega, ?_⟩
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  simp [UpdateKind.context, hsp, BitVec.ofNat_add, BitVec.add_assoc]

end Md5.Proofs.Buffered.ResetSecond
