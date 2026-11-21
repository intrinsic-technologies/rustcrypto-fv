import Md5.Proofs.Buffered.Update.ResetFirst.KindMachine
import Md5.Proofs.Buffered.Update.Memory

namespace Md5.Proofs.Buffered.ResetFirst

open Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs Block

theorem position_of_pre_of_kind [Bindings] {kind : UpdateKind} {boundary : ReturnBoundary}
    {message input : ByteArray} {s : RamState}
    (h : UpdatePre kind boundary message input s) :
    position_of_kind kind s = BitVec.ofNat 64 (message.size % 64) := by
  have hp := h.absorbed.position
  change (Operand.mem (stackPtr s + BitVec.ofNat 64 kind.contextOffset + BitVec.ofNat 64 63) :
    Operand 8).read s = _ at hp
  rw [BitVec.add_assoc, ← BitVec.ofNat_add] at hp
  rw [position_of_kind, hp]
  apply BitVec.setWidth_ofNat_of_le_of_lt (by decide)
  omega

theorem capacity_of_pre_of_kind [Bindings] {kind : UpdateKind} {boundary : ReturnBoundary}
    {message input : ByteArray} {s : RamState}
    (h : UpdatePre kind boundary message input s) :
    64 - position_of_kind kind s = BitVec.ofNat 64 (64 - message.size % 64) := by
  rw [position_of_pre_of_kind h]
  exact BitVec.ofNat_sub_ofNat_of_le 64 (message.size % 64) (by omega) (by omega)

theorem short_condition_iff_of_kind [Bindings] {kind : UpdateKind}
    {boundary : ReturnBoundary} {message input : ByteArray} {s : RamState}
    (h : UpdatePre kind boundary message input s) :
    ((.reg kind.sizeRegister : Operand 64).read s).toNat <
      (64 - position_of_kind kind s).toNat ↔
      message.size % 64 + input.size < 64 := by
  rw [h.inputSize, capacity_of_pre_of_kind h]
  simp only [BitVec.toNat_ofNat]
  have ht := h.totalSize
  rw [Nat.mod_eq_of_lt (show input.size < 2^64 by omega),
    Nat.mod_eq_of_lt (show 64 - message.size % 64 < 2^64 by omega)]
  omega

theorem entry_of_pre_of_kind [Bindings] {kind : UpdateKind} (hk : KindSupported kind) {boundary : ReturnBoundary}
    {message input : ByteArray} {s : RamState}
    (h : UpdatePre kind boundary message input s) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ (entryEffect_of_kind kind s).Holds s t ∧
      Absorbed (kind.context s) message t := by
  have hp : LoadPre kind.entry (fun s ↦ stackPtr s + BitVec.ofNat 64 (kind.contextOffset + 63)) 1 s :=
    ⟨h.rip, by
      simpa only [UpdateKind.context, BitVec.add_assoc, BitVec.ofNat_add] using
        h.contextReadable 63 1 (by decide)⟩
  obtain ⟨fuel, t, ha, ht, hc, he⟩ :=
    entry_branch_of_kind hk boundary h.boundaryOutside s h.ready h.code hp
  have hm : t.external = s.external := he.agrees.external (by
    simp [entryEffect_of_kind, prefixEffect_of_kind, Effect.components, Component.Covers])
  refine ⟨fuel, t, ha, ht, hc, he, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hm]
    exact h.absorbed.buffer
  · rw [hm]
    exact h.absorbed.tail
  · simpa only [Operand.read, hm] using h.absorbed.position
  · simpa only [Operand.read, hm] using h.absorbed.blocks


theorem position_of_pre [Bindings] {boundary : ReturnBoundary}
    {message input : ByteArray} {s : RamState}
    (h : UpdatePre .resetFirst boundary message input s) :
    position s = BitVec.ofNat 64 (message.size % 64) := by
  exact position_of_pre_of_kind (kind := .resetFirst) h

theorem capacity_of_pre [Bindings] {boundary : ReturnBoundary}
    {message input : ByteArray} {s : RamState}
    (h : UpdatePre .resetFirst boundary message input s) :
    64 - position s = BitVec.ofNat 64 (64 - message.size % 64) := by
  exact capacity_of_pre_of_kind (kind := .resetFirst) h

theorem short_condition_iff [Bindings] {boundary : ReturnBoundary}
    {message input : ByteArray} {s : RamState}
    (h : UpdatePre .resetFirst boundary message input s) :
    ((.reg 14 : Operand 64).read s).toNat < (64 - position s).toNat ↔
      message.size % 64 + input.size < 64 := by
  exact short_condition_iff_of_kind (kind := .resetFirst) h

theorem entry_of_pre [Bindings] {boundary : ReturnBoundary}
    {message input : ByteArray} {s : RamState}
    (h : UpdatePre .resetFirst boundary message input s) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ (entryEffect s).Holds s t ∧
      Absorbed (UpdateKind.resetFirst.context s) message t := by
  exact entry_of_pre_of_kind (kind := .resetFirst) (Or.inl rfl) h

end Md5.Proofs.Buffered.ResetFirst
