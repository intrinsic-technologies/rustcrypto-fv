import Md5.Proofs.Buffered.Update.ResetFirst.FullEntry
import Md5.Proofs.Buffered.Update.ResetFirst.Preparation

namespace Md5.Proofs.Buffered.ResetFirst

open Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs Block

attribute [local x86_compose] fullEntryEffect_of_kind prefixEffect_of_kind fillCopyEffect_of_kind

theorem fillCopyEffect_local_of_kind (kind : UpdateKind) : Effect.Local (fillCopyEffect_of_kind kind) := by
  refine ⟨fun _ _ _ ↦ rfl, fun s t h ↦ ?_, fun _ _ _ ↦ rfl,
    fun _ _ _ i _ ↦ ?_, fun _ ↦ ?_⟩
  · simp [fillCopyEffect_of_kind, stackPtr, h.read_reg, h.gpr]
  · cases i <;> simp [fillCopyEffect_of_kind, Effect.flag]
  · simp [fillCopyEffect_of_kind, Write.Full, Operand.Full]

def fillReadyEffect_of_kind (kind : UpdateKind) (s : RamState) : Effect :=
  { rip := (pc kind 0x6fe)
    writes := [⟨(.reg (reg kind 13) : Operand 64), position_of_kind kind s⟩,
      ⟨(.reg 2 : Operand 64), 64 - position_of_kind kind s⟩,
      ⟨(.reg (reg kind 3) : Operand 64), (.reg kind.sizeRegister : Operand 64).read s - (64 - position_of_kind kind s)⟩,
      ⟨(.reg kind.sizeRegister : Operand 64), (.reg kind.inputRegister : Operand 64).read s + (64 - position_of_kind kind s)⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + position_of_kind kind s + stackOffset kind 8⟩,
      ⟨(.reg 6 : Operand 64), (.reg kind.inputRegister : Operand 64).read s⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem fill_ready_of_kind [Bindings] {kind : UpdateKind} (hk : KindSupported kind) {boundary : ReturnBoundary} {message input : ByteArray}
    {s : RamState} (h : UpdatePre kind boundary message input s)
    (hfull : 64 ≤ message.size % 64 + input.size) (hpos : message.size % 64 ≠ 0) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ (fillReadyEffect_of_kind kind s).Holds s t := by
  obtain ⟨fu, u, hau, hru, hcu, he⟩ := full_entry_of_kind hk h hfull
  have hp : position_of_kind kind s ≠ 0 := by
    intro hn
    have ht := congrArg BitVec.toNat hn
    rw [position_of_pre_of_kind h, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show message.size % 64 < 2^64 by omega)] at ht
    exact hpos ht
  have hip : u.RIP = (pc kind 0x6ef) := by
    rw [he.rip, fullEntryEffect_of_kind, ite_eq_right hp]
  obtain ⟨ft, t, hat, hrt, _, hf⟩ :=
    fill_copy_prepare_of_kind hk boundary h.boundaryOutside u hru hcu hip
  refine ⟨fu + ft, t, hau.trans hat, hrt,
    hf.agrees.codeIn (by simp [fillCopyEffect_of_kind, Effect.components, Component.Covers]) hcu, ?_⟩
  have hall : ∀ w ∈ (fullEntryEffect_of_kind kind s).writes, w.Full := by
    simp [fullEntryEffect_of_kind, prefixEffect_of_kind, Write.Full, Operand.Full]
  have hsp : stackPtr ((fullEntryEffect_of_kind kind s).after s true) = stackPtr s :=
    ((he.obsAfter hall true).read (.reg 4 : Operand 64) trivial).trans
      (he.agrees.read (n := 64) (r := 4) (by
        rcases hk with rfl | rfl | rfl <;> simp [fullEntryEffect_of_kind, prefixEffect_of_kind, Effect.components, reg, UpdateKind.sizeRegister]))
  have hseq := he.seq (fillCopyEffect_local_of_kind kind) hall hf
  apply hseq.weaken
  · rcases hk with rfl | rfl | rfl <;> x86_norm [fillReadyEffect_of_kind, reg, UpdateKind.sizeRegister, UpdateKind.inputRegister, stackOffset, UpdateKind.contextOffset]
  · rcases hk with rfl | rfl | rfl <;> x86_norm [fillReadyEffect_of_kind, reg, UpdateKind.sizeRegister, UpdateKind.inputRegister, stackOffset, UpdateKind.contextOffset]
  · rcases hk with rfl | rfl | rfl <;> intro i <;> cases i <;> x86_norm [fillReadyEffect_of_kind, reg, UpdateKind.sizeRegister, UpdateKind.inputRegister, stackOffset, UpdateKind.contextOffset]
  · rcases hk with rfl | rfl | rfl <;> x86_norm [fillReadyEffect_of_kind, reg, UpdateKind.sizeRegister, UpdateKind.inputRegister, stackOffset, UpdateKind.contextOffset]


def fillReadyEffect (s : RamState) : Effect :=
  { rip := 0x1006fe
    writes := [⟨(.reg 13 : Operand 64), position s⟩,
      ⟨(.reg 2 : Operand 64), 64 - position s⟩,
      ⟨(.reg 3 : Operand 64), (.reg 14 : Operand 64).read s - (64 - position s)⟩,
      ⟨(.reg 14 : Operand 64), (.reg 12 : Operand 64).read s + (64 - position s)⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + position s + 8⟩,
      ⟨(.reg 6 : Operand 64), (.reg 12 : Operand 64).read s⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }


theorem fillCopyEffect_local : Effect.Local fillCopyEffect := by
  exact fillCopyEffect_local_of_kind .resetFirst

theorem fill_ready [Bindings] {boundary : ReturnBoundary} {message input : ByteArray}
    {s : RamState} (h : UpdatePre .resetFirst boundary message input s)
    (hfull : 64 ≤ message.size % 64 + input.size) (hpos : message.size % 64 ≠ 0) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ (fillReadyEffect s).Holds s t := by
  exact fill_ready_of_kind (kind := .resetFirst) (Or.inl rfl) h hfull hpos

end Md5.Proofs.Buffered.ResetFirst
