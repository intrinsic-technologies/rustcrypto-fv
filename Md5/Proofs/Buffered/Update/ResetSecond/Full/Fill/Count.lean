import Md5.Proofs.Buffered.Update.ResetSecond.Control
import Md5.Proofs.Buffered.Update.ResetSecond.Counter
import Md5.Proofs.Buffered.Stores.Effect
import Md5.Proofs.MemoryRoutines.Contracts

namespace Md5.Proofs.Buffered.ResetSecond

open Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs Block

attribute [local x86_compose] remainderBranchEffect remainderCountEffect positionClearEffect

theorem remainderBranchEffect_local (kind : UpdateKind) : Effect.Local (remainderBranchEffect kind) := by
  refine ⟨fun s t h ↦ ?_, fun s t h ↦ ?_, fun _ _ _ ↦ rfl,
    fun _ _ _ i _ ↦ ?_, fun _ ↦ ?_⟩
  · simp [remainderBranchEffect, h.read_reg]
  · simp [remainderBranchEffect, remainderCountEffect, h.read_reg]
  · cases i <;> simp [remainderBranchEffect, Effect.flag]
  · simp [remainderBranchEffect, remainderCountEffect, Write.Full, Operand.Full]

def fillCountEffect (kind : UpdateKind) (s : RamState) : Effect :=
  { rip := if (.reg 14 : Operand 64).read s >>> 6 = 0 then pc kind 0x100a4a else pc kind 0x100a35
    writes := [⟨(.mem (kind.context s + 63) : Operand 8), 0⟩,
      ⟨(.reg kind.inputRegister : Operand 64), (.reg (savedInputRegister kind) : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64), (.reg 14 : Operand 64).read s >>> 6⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem fill_count [Bindings] {kind : UpdateKind}
    (hkind : kind = .resetSecond ∨ kind = .finalizeResetSecond ∨ kind = .resetDiscardSecond) (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) {s : RamState}
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s) (hip : s.RIP = pc kind 0x100a24)
    (hw : MemoryRoutines.WritableRange s (kind.context s + 63) 1) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      (fillCountEffect kind s).Holds s t := by
  have hb : CodeIn (codeRange (pc kind 0x100a24) (positionClearBytes kind)) s := by
    rcases hkind with rfl | rfl | rfl
    · exact program_text_slice hc 0xa24 5 (by decide +kernel)
    · exact program_text_slice hc 0x10b4 5 (by decide +kernel)
    · exact program_text_slice hc 0x1592 5 (by decide +kernel)
  have hap : RangeApart (kind.context s + 63) 1 (pc kind 0x100a24) 5 := by
    intro i hi j hj heq
    apply hw.code i hi
    rw [heq]
    rcases hkind with rfl | rfl | rfl
    · have ht := text_address_in_program (0xa24 + j) (by
        have hn : 0xa29 ≤ Extracted.textBytes.size := by decide +kernel
        omega)
      rw [BitVec.ofNat_add, ← BitVec.add_assoc] at ht
      exact ht
    · have ht := text_address_in_program (0x10b4 + j) (by
        have hn : 0x10b9 ≤ Extracted.textBytes.size := by decide +kernel
        omega)
      rw [BitVec.ofNat_add, ← BitVec.add_assoc] at ht
      exact ht
    · have ht := text_address_in_program (0x1592 + j) (by
        have hn : 0x1597 ≤ Extracted.textBytes.size := by decide +kernel
        omega)
      rw [BitVec.ofNat_add, ← BitVec.add_assoc] at ht
      exact ht
  obtain ⟨fu, u, hau, hru, _, he⟩ := position_clear hkind boundary hOutside s hr hb
    ⟨hip, ⟨hw.readable.low, hw.readable.mem, hw.tables⟩, hap⟩
  have hcu : CodeIn Extracted.programImage u := by
    apply CodeIn.of_agreesExcept he.agrees _ hc
    intro x hx c hm hcover
    have hec : (positionClearEffect kind s).components =
        [.mem (kind.context s + 63) 1, .rip] := by
      simp [positionClearEffect, Effect.components]
    rw [hec] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · obtain ⟨i, hi, heq⟩ := hcover
      exact hw.code i hi (heq ▸ ⟨x.2, hx⟩)
    · exact hcover
  obtain ⟨ft, t, hat, hrt, hct, hf⟩ :=
    remainder_count_branch hkind boundary hOutside u hru hcu he.rip
  refine ⟨fu + ft, t, hau.trans hat, hrt, hct, ?_⟩
  have hseq := he.seq (remainderBranchEffect_local kind)
    (by simp [positionClearEffect, Write.Full, Operand.Full]) hf
  rcases hkind with rfl | rfl | rfl
  all_goals apply hseq.weaken
  all_goals first
    | (intro i; cases i <;> x86_norm [fillCountEffect, UpdateKind.context, UpdateKind.contextOffset, UpdateKind.inputRegister, savedInputRegister, stackPtr])
    | x86_norm [fillCountEffect, UpdateKind.context, UpdateKind.contextOffset, UpdateKind.inputRegister, savedInputRegister, stackPtr]

  all_goals first
    | exact fun h ↦ h
    | exact fun h ↦ Or.inl h
    | exact fun h₁ h₂ ↦ ⟨h₁, h₂⟩

end Md5.Proofs.Buffered.ResetSecond
