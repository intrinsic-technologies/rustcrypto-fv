import Md5.Proofs.Buffered.Update.ResetFirst.FillReady
import Md5.Proofs.Buffered.Update.ResetFirst.FillIncrement
import Md5.Proofs.Buffered.Update.ResetFirst.FillCount
import Md5.Proofs.Buffered.Update.Preservation

namespace Md5.Proofs.Buffered.ResetFirst

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem fillReadyEffect_agrees_of_kind {kind : UpdateKind} (hk : KindSupported kind) {s t : RamState} (he : (fillReadyEffect_of_kind kind s).Holds s t) :
    AgreesExcept (kind.changes s) s t := by
  apply he.agrees.mono
  intro c hm
  simp only [fillReadyEffect_of_kind, Effect.components, List.map_cons, List.map_nil,
    Write.component_reg, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rcases hk with rfl | rfl | rfl <;> simp [UpdateKind.changes, UpdateKind.workRegisters, reg, UpdateKind.sizeRegister]

theorem incrementPrepareEffect_agrees_of_kind {kind : UpdateKind} (hk : KindSupported kind) {initial s t : RamState} (hsp : stackPtr s = stackPtr initial)
    (he : (incrementPrepareEffect_of_kind kind s).Holds s t) :
    AgreesExcept (kind.changes initial) s t := by
  apply he.agrees.widen
  · intro c hm hn
    simp only [incrementPrepareEffect_of_kind, Effect.components, List.map_cons, List.map_nil,
      Write.component_reg, Write.component_mem, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Bool.noConfusion hn
    all_goals rcases hk with rfl | rfl | rfl <;> simp [UpdateKind.changes, UpdateKind.workRegisters]
  · intro address c hm hcover
    simp only [incrementPrepareEffect_of_kind, Effect.components, List.map_cons, List.map_nil,
      Write.component_reg, Write.component_mem, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hcover.elim
    refine ⟨.mem (kind.context initial) 88,
      by simp [UpdateKind.changes], ?_⟩
    obtain ⟨i, hi, rfl⟩ := hcover
    refine ⟨80 + i, by omega, ?_⟩
    rw [hsp, BitVec.ofNat_add]
    rcases hk with rfl | rfl | rfl <;>
      simp [stackOffset, UpdateKind.context, UpdateKind.contextOffset, BitVec.add_assoc] <;>
      rw [← BitVec.add_assoc] <;> rfl

theorem fillCountEffect_agrees_of_kind {kind : UpdateKind} (hk : KindSupported kind) {initial s t : RamState} (hsp : stackPtr s = stackPtr initial)
    (he : (fillCountEffect_of_kind kind s).Holds s t) :
    AgreesExcept (kind.changes initial) s t := by
  apply he.agrees.widen
  · intro c hm hn
    simp only [fillCountEffect_of_kind, Effect.components, List.map_cons, List.map_nil,
      Write.component_reg, Write.component_mem, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl
    · exact Bool.noConfusion hn
    all_goals rcases hk with rfl | rfl | rfl <;> simp [UpdateKind.changes, UpdateKind.workRegisters, UpdateKind.inputRegister]
  · intro address c hm hcover
    simp only [fillCountEffect_of_kind, Effect.components, List.map_cons, List.map_nil,
      Write.component_reg, Write.component_mem, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl
    all_goals try exact hcover.elim
    refine ⟨.mem (kind.context initial) 88,
      by simp [UpdateKind.changes], ?_⟩
    obtain ⟨i, hi, rfl⟩ := hcover
    refine ⟨63 + i, by omega, ?_⟩
    rw [hsp, BitVec.ofNat_add]
    rcases hk with rfl | rfl | rfl <;>
      simp [stackOffset, UpdateKind.context, UpdateKind.contextOffset, BitVec.add_assoc] <;>
      rw [← BitVec.add_assoc] <;> rfl

theorem fillCountEffect_frame_of_kind {kind : UpdateKind} (hk : KindSupported kind) [Bindings] {boundary : ReturnBoundary}
    {message input : ByteArray} {initial s t : RamState}
    (h : UpdatePre kind boundary message input initial)
    (hsp : stackPtr s = stackPtr initial) (he : (fillCountEffect_of_kind kind s).Holds s t) :
    MemoryWriteFrame s t
      #v[UpdateKind.scratchRegion initial, ⟨(kind.context initial).toNat, 64⟩] := by
  apply he.agrees.memoryWriteFrame
  intro c hm address hcover
  simp only [fillCountEffect_of_kind, Effect.components, List.map_cons, List.map_nil,
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
  rw [hsp, BitVec.ofNat_add]
  rcases hk with rfl | rfl | rfl <;>
    simp [stackOffset, UpdateKind.context, UpdateKind.contextOffset, BitVec.add_assoc] <;>
      rw [← BitVec.add_assoc] <;> rfl


theorem fillReadyEffect_agrees {s t : RamState} (he : (fillReadyEffect s).Holds s t) :
    AgreesExcept (UpdateKind.resetFirst.changes s) s t := by
  exact fillReadyEffect_agrees_of_kind (kind := .resetFirst) (Or.inl rfl) he

theorem incrementPrepareEffect_agrees {initial s t : RamState} (hsp : stackPtr s = stackPtr initial)
    (he : (incrementPrepareEffect s).Holds s t) :
    AgreesExcept (UpdateKind.resetFirst.changes initial) s t := by
  exact incrementPrepareEffect_agrees_of_kind (kind := .resetFirst) (Or.inl rfl) hsp he

theorem fillCountEffect_agrees {initial s t : RamState} (hsp : stackPtr s = stackPtr initial)
    (he : (fillCountEffect s).Holds s t) :
    AgreesExcept (UpdateKind.resetFirst.changes initial) s t := by
  exact fillCountEffect_agrees_of_kind (kind := .resetFirst) (Or.inl rfl) hsp he

theorem fillCountEffect_frame [Bindings] {boundary : ReturnBoundary}
    {message input : ByteArray} {initial s t : RamState}
    (h : UpdatePre .resetFirst boundary message input initial)
    (hsp : stackPtr s = stackPtr initial) (he : (fillCountEffect s).Holds s t) :
    MemoryWriteFrame s t
      #v[UpdateKind.scratchRegion initial, ⟨(UpdateKind.resetFirst.context initial).toNat, 64⟩] := by
  exact fillCountEffect_frame_of_kind (kind := .resetFirst) (Or.inl rfl) h hsp he

end Md5.Proofs.Buffered.ResetFirst
