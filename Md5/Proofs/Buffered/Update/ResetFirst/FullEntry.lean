import Md5.Proofs.Buffered.Update.ResetFirst.Entry


namespace Md5.Proofs.Buffered.ResetFirst

open Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs Block

def fullEntryEffect_of_kind (kind : UpdateKind) (s : RamState) : Effect :=
  { prefixEffect_of_kind kind s with
    rip := if position_of_kind kind s = 0 then (pc kind 0x779) else (pc kind 0x6ef)
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem full_entry_of_kind [Bindings] {kind : UpdateKind} (hk : KindSupported kind) {boundary : ReturnBoundary} {message input : ByteArray}
    {s : RamState} (h : UpdatePre kind boundary message input s)
    (hfull : 64 ≤ message.size % 64 + input.size) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ (fullEntryEffect_of_kind kind s).Holds s t := by
  obtain ⟨fu, u, hau, hru, hcu, he, _⟩ := entry_of_pre_of_kind hk h
  have hip : u.RIP = (pc kind 0x6e6) := by
    rw [he.rip, entryEffect_of_kind, ite_eq_right]
    exact fun hn ↦ (show ¬ message.size % 64 + input.size < 64 by omega)
      ((short_condition_iff_of_kind h).mp hn)
  obtain ⟨ft, t, hat, hrt, hct, hf⟩ :=
    partial_branch_of_kind hk boundary h.boundaryOutside u hru hcu hip
  refine ⟨fu + ft, t, hau.trans hat, hrt, hct, ?_⟩
  refine ⟨?_, ?_, by trivial, ?_⟩
  · rw [hf.rip]
    change (if (.reg (reg kind 13) : Operand 64).read u = 0 then (pc kind 0x779) else (pc kind 0x6ef)) = _
    rw [he.writes.1]
    rfl
  · change (.reg (reg kind 13) : Operand 64).read t = _ ∧ (.reg 2 : Operand 64).read t = _ ∧
      (.reg (reg kind 3) : Operand 64).read t = _
    exact ⟨(hf.agrees.read (by simp [partialEffect_of_kind, Effect.components])).trans he.writes.1,
      (hf.agrees.read (by simp [partialEffect_of_kind, Effect.components])).trans he.writes.2.1,
      (hf.agrees.read (by simp [partialEffect_of_kind, Effect.components])).trans he.writes.2.2⟩
  · apply (he.agrees.trans hf.agrees).mono
    simp [entryEffect_of_kind, partialEffect_of_kind, fullEntryEffect_of_kind, prefixEffect_of_kind, Effect.components]


def fullEntryEffect (s : RamState) : Effect :=
  { prefixEffect s with
    rip := if position s = 0 then 0x100779 else 0x1006ef
    flags := some ⟨none, none, none, none, none, none⟩ }


theorem full_entry [Bindings] {boundary : ReturnBoundary} {message input : ByteArray}
    {s : RamState} (h : UpdatePre .resetFirst boundary message input s)
    (hfull : 64 ≤ message.size % 64 + input.size) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ (fullEntryEffect s).Holds s t := by
  exact full_entry_of_kind (kind := .resetFirst) (Or.inl rfl) h hfull

end Md5.Proofs.Buffered.ResetFirst
