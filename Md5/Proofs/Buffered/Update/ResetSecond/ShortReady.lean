import Md5.Proofs.Buffered.Update.ResetSecond.Entry
import Md5.Proofs.Buffered.Update.ResetSecond.Preparation

namespace Md5.Proofs.Buffered.ResetSecond

open Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs Block

attribute [local x86_compose] shortCopyEffect entryEffect prefixEffect

theorem shortCopyEffect_local (kind : UpdateKind) : Effect.Local (shortCopyEffect kind) := by
  cases kind
  all_goals refine ⟨fun _ _ _ ↦ rfl, fun s t h ↦ ?_, fun _ _ _ ↦ rfl,
    fun _ _ _ i _ ↦ ?_, fun _ ↦ ?_⟩
  all_goals first
    | solve | simp [shortCopyEffect, stackPtr, h.read_reg, h.gpr]
    | solve | cases i <;> simp [shortCopyEffect, Effect.flag]
    | solve | simp [shortCopyEffect, Write.Full, Operand.Full]

def shortReadyEffect (kind : UpdateKind) (s : RamState) : Effect :=
  { rip := (pc kind 0x1009ab)
    writes := [⟨(.reg (positionRegister kind) : Operand 64), position kind s⟩,
      ⟨(.reg 14 : Operand 64), (.reg kind.sizeRegister : Operand 64).read s - (64 - position kind s)⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + position kind s + BitVec.ofNat 64 kind.contextOffset⟩,
      ⟨(.reg 2 : Operand 64), (.reg kind.sizeRegister : Operand 64).read s⟩] ++
      (if kind = .resetDiscardSecond then [⟨(.reg 6 : Operand 64), (.reg 3 : Operand 64).read s⟩] else [])
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem short_ready [Bindings] {kind : UpdateKind} {boundary : ReturnBoundary} {message input : ByteArray}
    {s : RamState} (hkind : kind = .resetSecond ∨ kind = .finalizeResetSecond ∨ kind = .resetDiscardSecond)
    (h : UpdatePre kind boundary message input s)
    (hshort : message.size % 64 + input.size < 64) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ (shortReadyEffect kind s).Holds s t := by
  obtain ⟨n, u, ha, hu, hcu, he⟩ := entry_branch hkind boundary h.boundaryOutside s h.ready h.code
    ⟨by rcases hkind with rfl | rfl | rfl <;> exact h.rip,
        by simpa [UpdateKind.context, ← BitVec.ofNat_add, BitVec.add_assoc] using
          h.contextReadable 63 1 (by decide)⟩
  have hrip : u.RIP = (pc kind 0x1009a0) := by
    rw [he.rip, entryEffect, ite_eq_left ((short_condition_iff h).mpr hshort)]
  have hbytes : CodeIn (codeRange (pc kind 0x1009a0) (shortCopyBytes kind)) u := by
    rcases hkind with rfl | rfl | rfl
    · exact program_text_slice hcu 0x9a0 11 (by decide +kernel)
    · exact program_text_slice hcu 0x1030 11 (by decide +kernel)
    · exact program_text_slice hcu 0x1510 14 (by decide +kernel)
  obtain ⟨m, t, hb, ht, _, heb⟩ := short_copy_prepare hkind boundary h.boundaryOutside
    u hu hbytes hrip
  refine ⟨n + m, t, ha.trans hb, ht,
    heb.agrees.codeIn (by cases kind <;> simp [shortCopyEffect, Effect.components, Component.Covers]) hcu, ?_⟩
  have hall : ∀ w ∈ (entryEffect kind s).writes, w.Full := by
    rcases hkind with rfl | rfl | rfl <;> simp [entryEffect, prefixEffect, Write.Full, Operand.Full]
  have hseq := he.seq (shortCopyEffect_local kind) hall heb
  rcases hkind with rfl | rfl | rfl
  all_goals apply hseq.weaken
  all_goals first
    | x86_norm [shortReadyEffect, pc, positionRegister, UpdateKind.sizeRegister, UpdateKind.contextOffset, savedInputRegister]
    | intro i; cases i <;> x86_norm [shortReadyEffect, pc, positionRegister, UpdateKind.sizeRegister, UpdateKind.contextOffset, savedInputRegister]

end Md5.Proofs.Buffered.ResetSecond
