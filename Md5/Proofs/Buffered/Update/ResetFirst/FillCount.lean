import Md5.Proofs.Buffered.Update.ResetFirst.KindMachine
import Md5.Proofs.Buffered.Stores.Effect
import Md5.Proofs.MemoryRoutines.Contracts

namespace Md5.Proofs.Buffered.ResetFirst

open Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs Block

attribute [local x86_compose] remainderBranchEffect_of_kind remainderCountEffect_of_kind movM8Imm8Effect

theorem remainderBranchEffect_local_of_kind (kind : UpdateKind) : Effect.Local (remainderBranchEffect_of_kind kind) := by
  refine ⟨fun s t h ↦ ?_, fun s t h ↦ ?_, fun _ _ _ ↦ rfl,
    fun _ _ _ i _ ↦ ?_, fun _ ↦ ?_⟩
  · simp [remainderBranchEffect_of_kind, h.read_reg]
  · simp [remainderBranchEffect_of_kind, remainderCountEffect_of_kind, h.read_reg]
  · cases i <;> simp [remainderBranchEffect_of_kind, Effect.flag]
  · simp [remainderBranchEffect_of_kind, remainderCountEffect_of_kind, Write.Full, Operand.Full]

def fillCountEffect_of_kind (kind : UpdateKind) (s : RamState) : Effect :=
  { rip := if (.reg (reg kind 3) : Operand 64).read s >>> 6 = 0 then (pc kind 0x740) else (pc kind 0x72e)
    writes := [⟨(.mem (stackPtr s + stackOffset kind 71) : Operand 8), 0⟩,
      ⟨(.reg kind.inputRegister : Operand 64), (.reg kind.sizeRegister : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64), (.reg (reg kind 3) : Operand 64).read s >>> 6⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem fill_count_of_kind [Bindings] {kind : UpdateKind} (hk : KindSupported kind) (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) {s : RamState}
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s) (hip : s.RIP = (pc kind 0x71d))
    (hw : MemoryRoutines.WritableRange s (stackPtr s + stackOffset kind 71) 1) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      (fillCountEffect_of_kind kind s).Holds s t := by
  have hs := Stores.mov_m8_imm8_effect_step (pc kind 0x71d) (.sib 4 none 0 (.d8 (BitVec.ofNat 8 (kind.contextOffset + 63))))
    (by rcases hk with rfl | rfl | rfl <;> decide) (by rcases hk with rfl | rfl | rfl <;> decide) (by rcases hk with rfl | rfl | rfl <;> decide) 0
  have hb : CodeIn (codeRange (pc kind 0x71d)
      [0xc6, 0x44, 0x24, UInt8.ofNat (kind.contextOffset + 63), 0x00]) s := by
    rcases hk with rfl | rfl | rfl
    · exact program_text_slice hc 0x71d 5 (by decide +kernel)
    · exact program_text_slice hc 0xdcd 5 (by decide +kernel)
    · exact program_text_slice hc 0x1456 5 (by decide +kernel)
  have hp : Memory.StorePre (pc kind 0x71d) 5
      (storeAddrAt (pc kind 0x71d) (.sib 4 none 0 (.d8 (BitVec.ofNat 8 (kind.contextOffset + 63)))) 5) 1 s := by
    refine ⟨hip, ?_, ?_⟩
    · rcases hk with rfl | rfl | rfl <;> x86_norm [stackOffset, UpdateKind.contextOffset] at *
      all_goals exact ⟨hw.readable.low, hw.readable.mem, hw.tables⟩
    · rcases hk with rfl | rfl | rfl <;> x86_norm [stackOffset, UpdateKind.contextOffset]
      all_goals
        intro i hi j hj heq
        apply hw.code i hi
        simp only [Operand.read_reg64] at heq
        x86_norm [stackPtr, stackOffset, UpdateKind.contextOffset] at heq ⊢
        rw [heq]
      · have ht := text_address_in_program (0x71d + j) (by
          have hn : 0x722 ≤ Extracted.textBytes.size := by decide +kernel
          omega)
        rw [BitVec.ofNat_add, ← BitVec.add_assoc] at ht
        exact ht
      · have ht := text_address_in_program (0xdcd + j) (by
          have hn : 0xdd2 ≤ Extracted.textBytes.size := by decide +kernel
          omega)
        rw [BitVec.ofNat_add, ← BitVec.add_assoc] at ht
        exact ht
      · have ht := text_address_in_program (0x1456 + j) (by
          have hn : 0x145b ≤ Extracted.textBytes.size := by decide +kernel
          omega)
        rw [BitVec.ofNat_add, ← BitVec.add_assoc] at ht
        exact ht
  obtain ⟨u, hau, hru, he⟩ := hs.advances hr (by rcases hk with rfl | rfl | rfl <;> exact hb) hp
    (by
      rcases hk with rfl | rfl | rfl
      · exact text_address_ne_return hOutside 0x722 (by decide +kernel)
      · exact text_address_ne_return hOutside 0xdd2 (by decide +kernel)
      · exact text_address_ne_return hOutside 0x145b (by decide +kernel))
  have hcu : CodeIn Extracted.programImage u := by
    apply CodeIn.of_agreesExcept he.agrees _ hc
    intro x hx c hm hcover
    have hec : (movM8Imm8Effect (pc kind 0x71d) (.sib 4 none 0 (.d8 (BitVec.ofNat 8 (kind.contextOffset + 63)))) 0 s).components =
        [.mem (stackPtr s + stackOffset kind 71) 1, .rip] := by
      rcases hk with rfl | rfl | rfl <;> x86_norm [stackPtr, stackOffset, UpdateKind.contextOffset]
      all_goals rfl
    rw [hec] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · obtain ⟨i, hi, heq⟩ := hcover
      exact hw.code i hi (heq ▸ ⟨x.2, hx⟩)
    · exact hcover
  obtain ⟨ft, t, hat, hrt, hct, hf⟩ :=
    remainder_count_branch_of_kind hk boundary hOutside u hru hcu (by
      change u.RIP = pc kind 0x722
      rw [he.rip]
      rcases hk with rfl | rfl | rfl <;> rfl)
  refine ⟨1 + ft, t, hau.trans hat, hrt, hct, ?_⟩
  have hseq := he.seq (remainderBranchEffect_local_of_kind kind)
    (by simp [movM8Imm8Effect, storeEffect, Write.Full, Operand.Full]) hf
  apply hseq.weaken
  · rcases hk with rfl | rfl | rfl <;> x86_norm [fillCountEffect_of_kind, pc, reg, UpdateKind.inputRegister, UpdateKind.sizeRegister]
  · rcases hk with rfl | rfl | rfl <;> x86_norm [fillCountEffect_of_kind, stackPtr, stackOffset, reg, UpdateKind.contextOffset, UpdateKind.inputRegister, UpdateKind.sizeRegister]
    all_goals exact Or.inl rfl
  · rcases hk with rfl | rfl | rfl <;> intro i <;> cases i <;> x86_norm [fillCountEffect_of_kind]
  · rcases hk with rfl | rfl | rfl <;> x86_norm [fillCountEffect_of_kind, stackPtr, stackOffset, reg, UpdateKind.contextOffset, UpdateKind.inputRegister, UpdateKind.sizeRegister]
    all_goals rfl


def fillCountEffect (s : RamState) : Effect :=
  { rip := if (.reg 3 : Operand 64).read s >>> 6 = 0 then 0x100740 else 0x10072e
    writes := [⟨(.mem (stackPtr s + 71) : Operand 8), 0⟩,
      ⟨(.reg 12 : Operand 64), (.reg 14 : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64), (.reg 3 : Operand 64).read s >>> 6⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }


theorem remainderBranchEffect_local : Effect.Local remainderBranchEffect := by
  exact remainderBranchEffect_local_of_kind .resetFirst

theorem fill_count [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) {s : RamState}
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s) (hip : s.RIP = 0x10071d)
    (hw : MemoryRoutines.WritableRange s (stackPtr s + 71) 1) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      (fillCountEffect s).Holds s t := by
  exact fill_count_of_kind (kind := .resetFirst) (Or.inl rfl) boundary hOutside hr hc hip hw

end Md5.Proofs.Buffered.ResetFirst
