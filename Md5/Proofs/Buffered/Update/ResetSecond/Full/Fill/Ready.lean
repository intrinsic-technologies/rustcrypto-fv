import Md5.Proofs.Buffered.Update.ResetSecond.FullEntry
import Md5.Proofs.Buffered.Update.ResetSecond.Preparation

namespace Md5.Proofs.Buffered.ResetSecond

open Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs Block

attribute [local x86_compose] fullEntryEffect prefixEffect fillCopyEffect

theorem fillCopyEffect_local (kind : UpdateKind) : Effect.Local (fillCopyEffect kind) := by
  refine ⟨fun _ _ _ ↦ rfl, fun s t h ↦ ?_, fun _ _ _ ↦ rfl,
    fun _ _ _ i _ ↦ ?_, fun _ ↦ ?_⟩
  · simp [fillCopyEffect, stackPtr, h.read_reg, h.gpr]
  · cases i <;> simp [fillCopyEffect, Effect.flag]
  · cases kind <;> simp [fillCopyEffect, Write.Full, Operand.Full]

def fillReadyEffect (kind : UpdateKind) (s : RamState) : Effect :=
  { rip := (pc kind 0x100a0a)
    writes := [⟨(.reg (positionRegister kind) : Operand 64), position kind s⟩,
      ⟨(.reg 2 : Operand 64), 64 - position kind s⟩,
      ⟨(.reg 14 : Operand 64), (.reg kind.sizeRegister : Operand 64).read s - (64 - position kind s)⟩,
      ⟨(.reg (savedInputRegister kind) : Operand 64), (.reg kind.inputRegister : Operand 64).read s + (64 - position kind s)⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + position kind s + BitVec.ofNat 64 kind.contextOffset⟩,
      ⟨(.reg 6 : Operand 64), (.reg kind.inputRegister : Operand 64).read s⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem fill_ready [Bindings] {kind : UpdateKind} {boundary : ReturnBoundary} {message input : ByteArray}
    {s : RamState}
    (hkind : kind = .resetSecond ∨ kind = .finalizeResetSecond ∨ kind = .resetDiscardSecond)
    (h : UpdatePre kind boundary message input s)
    (hfull : 64 ≤ message.size % 64 + input.size) (hpos : message.size % 64 ≠ 0) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ (fillReadyEffect kind s).Holds s t := by
  obtain ⟨fu, u, hau, hru, hcu, he⟩ := full_entry hkind h hfull
  have hp : position kind s ≠ 0 := by
    intro hn
    have ht := congrArg BitVec.toNat hn
    rw [position_of_pre h, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show message.size % 64 < 2^64 by omega)] at ht
    exact hpos ht
  have hip : u.RIP = pc kind 0x1009fe := by
    rw [he.rip, fullEntryEffect, ite_eq_right hp]
  have hbytes : CodeIn (codeRange (pc kind 0x1009fe) (fillCopyBytes kind)) u :=
    by
      rcases hkind with rfl | rfl | rfl
      · exact program_text_slice hcu 0x9fe 12 (by decide +kernel)
      · exact program_text_slice hcu 0x108e 12 (by decide +kernel)
      · exact program_text_slice hcu 0x1567 15 (by decide +kernel)
  obtain ⟨ft, t, hat, hrt, _, hf⟩ :=
    fill_copy_prepare hkind boundary h.boundaryOutside u hru hbytes hip
  refine ⟨fu + ft, t, hau.trans hat, hrt,
    hf.agrees.codeIn (by rcases hkind with rfl | rfl | rfl <;> simp [fillCopyEffect, Effect.components, Component.Covers]) hcu, ?_⟩
  have hall : ∀ w ∈ (fullEntryEffect kind s).writes, w.Full := by
    simp [fullEntryEffect, prefixEffect, Write.Full, Operand.Full]
  have hsp : stackPtr ((fullEntryEffect kind s).after s true) = stackPtr s :=
    ((he.obsAfter hall true).read (.reg 4 : Operand 64) trivial).trans
      (he.agrees.read (n := 64) (r := 4) (by
        rcases hkind with rfl | rfl | rfl <;> simp [fullEntryEffect, prefixEffect, Effect.components, positionRegister]))
  have hseq := he.seq (fillCopyEffect_local kind) hall hf
  rcases hkind with rfl | rfl | rfl
  all_goals
    have hw := hseq.writes
    have hr := hseq.rip
    have ha := hseq.agrees
    refine ⟨?_, ?_, by trivial, ?_⟩
    · simpa only [Effect.seq, fillCopyEffect, fillReadyEffect] using hr
    · x86_norm [fillReadyEffect, positionRegister, savedInputRegister, UpdateKind.contextOffset, UpdateKind.inputRegister, UpdateKind.sizeRegister, Write.AllHold] at hw ⊢
      first
      | grind only
      | have hsix := ha.read (n := 64) (r := 6) (by x86_norm)
        exact ⟨hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2, hsix⟩
    · apply ha.mono
      x86_norm [fillReadyEffect, positionRegister, savedInputRegister, UpdateKind.contextOffset, UpdateKind.inputRegister, UpdateKind.sizeRegister]

end Md5.Proofs.Buffered.ResetSecond
