import Md5.Proofs.Buffered.Update.ResetSecond.Entry

namespace Md5.Proofs.Buffered.ResetSecond

open Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs Block

def fullEntryEffect (kind : UpdateKind) (s : RamState) : Effect :=
  { prefixEffect kind s with
    rip := if position kind s = 0 then (pc kind 0x100a82) else (pc kind 0x1009fe)
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem full_entry [Bindings] {kind : UpdateKind} {boundary : ReturnBoundary} {message input : ByteArray}
    {s : RamState} (hkind : kind = .resetSecond ∨ kind = .finalizeResetSecond ∨ kind = .resetDiscardSecond)
    (h : UpdatePre kind boundary message input s)
    (hfull : 64 ≤ message.size % 64 + input.size) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ (fullEntryEffect kind s).Holds s t := by
  obtain ⟨fu, u, hau, hru, hcu, he⟩ :=
    entry_branch hkind boundary h.boundaryOutside s h.ready h.code
      ⟨by rcases hkind with rfl | rfl | rfl <;> exact h.rip,
        by simpa [UpdateKind.context, BitVec.ofNat_add, BitVec.add_assoc] using
          h.contextReadable 63 1 (by decide)⟩
  have hip : u.RIP = (pc kind 0x1009f5) := by
    rw [he.rip, entryEffect, ite_eq_right]
    exact fun hn ↦ (show ¬ message.size % 64 + input.size < 64 by omega)
      ((short_condition_iff h).mp hn)
  obtain ⟨ft, t, hat, hrt, hct, hf⟩ :=
    partial_branch hkind boundary h.boundaryOutside u hru hcu hip
  refine ⟨fu + ft, t, hau.trans hat, hrt, hct, ?_⟩
  refine ⟨?_, ?_, by trivial, ?_⟩
  · rw [hf.rip]
    change (if (.reg (positionRegister kind) : Operand 64).read u = 0 then (pc kind 0x100a82) else (pc kind 0x1009fe)) = _
    rw [he.writes.1]
    rfl
  · change (.reg (positionRegister kind) : Operand 64).read t = _ ∧ (.reg 2 : Operand 64).read t = _ ∧
      (.reg 14 : Operand 64).read t = _
    exact ⟨(hf.agrees.read (by rcases hkind with rfl | rfl | rfl <;> simp [partialEffect, Effect.components, positionRegister])).trans he.writes.1,
      (hf.agrees.read (by rcases hkind with rfl | rfl | rfl <;> simp [partialEffect, Effect.components, positionRegister])).trans he.writes.2.1,
      (hf.agrees.read (by rcases hkind with rfl | rfl | rfl <;> simp [partialEffect, Effect.components, positionRegister])).trans he.writes.2.2⟩
  · apply (he.agrees.trans hf.agrees).mono
    simp [entryEffect, partialEffect, fullEntryEffect, prefixEffect, Effect.components]

end Md5.Proofs.Buffered.ResetSecond
