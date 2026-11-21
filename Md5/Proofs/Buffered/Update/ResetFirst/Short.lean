import Md5.Proofs.Buffered.Update.ResetFirst.Entry
import Md5.Proofs.Buffered.Update.ResetFirst.Preparation


namespace Md5.Proofs.Buffered.ResetFirst

open Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs Block

attribute [local x86_compose] shortCopyEffect_of_kind entryEffect_of_kind prefixEffect_of_kind

theorem shortCopyEffect_local_of_kind (kind : UpdateKind) : Effect.Local (shortCopyEffect_of_kind kind) := by
  refine ⟨fun _ _ _ ↦ rfl, fun s t h ↦ ?_, fun _ _ _ ↦ rfl,
    fun _ _ _ i _ ↦ ?_, fun _ ↦ ?_⟩
  · simp [shortCopyEffect_of_kind, stackPtr, h.read_reg, h.gpr]
  · cases i <;> simp [shortCopyEffect_of_kind, Effect.flag]
  · simp [shortCopyEffect_of_kind, Write.Full, Operand.Full]

def shortReadyEffect_of_kind (kind : UpdateKind) (s : RamState) : Effect :=
  { rip := (pc kind 0x69e)
    writes := [⟨(.reg (reg kind 13) : Operand 64), position_of_kind kind s⟩,
      ⟨(.reg (reg kind 3) : Operand 64), (.reg kind.sizeRegister : Operand 64).read s - (64 - position_of_kind kind s)⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + position_of_kind kind s + stackOffset kind 8⟩,
      ⟨(.reg 6 : Operand 64), (.reg kind.inputRegister : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64), (.reg kind.sizeRegister : Operand 64).read s⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem short_ready_of_kind [Bindings] {kind : UpdateKind} (hk : KindSupported kind) {boundary : ReturnBoundary} {message input : ByteArray}
    {s : RamState} (h : UpdatePre kind boundary message input s)
    (hshort : message.size % 64 + input.size < 64) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ (shortReadyEffect_of_kind kind s).Holds s t := by
  obtain ⟨n, u, ha, hu, hcu, he, _⟩ := entry_of_pre_of_kind hk h
  have hrip : u.RIP = (pc kind 0x690) := by
    rw [he.rip, entryEffect_of_kind, ite_eq_left ((short_condition_iff_of_kind h).mpr hshort)]
  obtain ⟨m, t, hb, ht, _, heb⟩ := short_copy_prepare_of_kind hk boundary h.boundaryOutside
    u hu hcu hrip
  refine ⟨n + m, t, ha.trans hb, ht,
    heb.agrees.codeIn (by simp [shortCopyEffect_of_kind, Effect.components, Component.Covers]) hcu, ?_⟩
  have hall : ∀ w ∈ (entryEffect_of_kind kind s).writes, w.Full := by
    simp [entryEffect_of_kind, prefixEffect_of_kind, Write.Full, Operand.Full]
  have hsp : stackPtr ((entryEffect_of_kind kind s).after s true) = stackPtr s :=
    ((he.obsAfter hall true).read (.reg 4 : Operand 64) trivial).trans
      (he.agrees.read (n := 64) (r := 4) (by
        rcases hk with rfl | rfl | rfl <;> simp [entryEffect_of_kind, prefixEffect_of_kind, Effect.components, reg, UpdateKind.sizeRegister]))
  have hseq := he.seq (shortCopyEffect_local_of_kind kind) hall heb
  apply hseq.weaken
  · rcases hk with rfl | rfl | rfl <;> x86_norm [shortReadyEffect_of_kind, reg, UpdateKind.sizeRegister, UpdateKind.inputRegister, stackOffset, UpdateKind.contextOffset]
  · rcases hk with rfl | rfl | rfl <;> x86_norm [shortReadyEffect_of_kind, reg, UpdateKind.sizeRegister, UpdateKind.inputRegister, stackOffset, UpdateKind.contextOffset]
  · rcases hk with rfl | rfl | rfl <;> intro i <;> cases i <;> x86_norm [shortReadyEffect_of_kind, reg, UpdateKind.sizeRegister, UpdateKind.inputRegister, stackOffset, UpdateKind.contextOffset]
  · rcases hk with rfl | rfl | rfl <;> x86_norm [shortReadyEffect_of_kind, reg, UpdateKind.sizeRegister, UpdateKind.inputRegister, stackOffset, UpdateKind.contextOffset]


def shortReadyEffect (s : RamState) : Effect :=
  { rip := 0x10069e
    writes := [⟨(.reg 13 : Operand 64), position s⟩,
      ⟨(.reg 3 : Operand 64), (.reg 14 : Operand 64).read s - (64 - position s)⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + position s + 8⟩,
      ⟨(.reg 6 : Operand 64), (.reg 12 : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64), (.reg 14 : Operand 64).read s⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }


theorem shortCopyEffect_local : Effect.Local shortCopyEffect := by
  exact shortCopyEffect_local_of_kind .resetFirst

theorem short_ready [Bindings] {boundary : ReturnBoundary} {message input : ByteArray}
    {s : RamState} (h : UpdatePre .resetFirst boundary message input s)
    (hshort : message.size % 64 + input.size < 64) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ (shortReadyEffect s).Holds s t := by
  exact short_ready_of_kind (kind := .resetFirst) (Or.inl rfl) h hshort

end Md5.Proofs.Buffered.ResetFirst
