import Md5.Proofs.Buffered.Update.Slices.Control
import X86Proofs.Instructions.Add.Generated.Imm32.Triple

namespace Md5.Proofs.Buffered.Update.Slices

open Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs Block

attribute [local x86_compose] addR64Imm32Effect

@[local x86_local] theorem addR64Imm32Effect_local (p : BitVec 64) (dst : BitVec 5)
    (imm : BitVec 32) : Effect.Local (addR64Imm32Effect p dst imm) := by
  refine ⟨fun _ _ _ ↦ rfl, fun s t h ↦ ?_, fun _ _ _ ↦ rfl,
    fun s t h i _ ↦ ?_, fun _ ↦ ?_⟩
  · simp only [addR64Imm32Effect, h.read_reg]
  · cases i <;> simp [addR64Imm32Effect, Effect.flag, h.read_reg]
  · simp [addR64Imm32Effect, Write.Full, Operand.Full]

def shortPrepareBytes : List UInt8 :=
  [0x4a, 0x8d, 0x3c, 0x2c, 0x48, 0x81, 0xc7, 0xc0, 0x00, 0x00, 0x00,
    0x4c, 0x89, 0xf6, 0x48, 0x89, 0xda]

def shortPrepareEffect (variant : Bool) (s : RamState) : Effect where
  rip := (pc variant 0x100321)
  writes := [⟨(.reg 7 : Operand 64),
    stackPtr s + (Operand.reg 13 : Operand 64).read s + 192⟩,
    ⟨(.reg 6 : Operand 64), (Operand.reg 14 : Operand 64).read s⟩,
    ⟨(.reg 2 : Operand 64), (Operand.reg 3 : Operand 64).read s⟩]
  flags := some ⟨none, none, none, none, none, none⟩

theorem short_prepare [Bindings] {variant : Bool} (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = (pc variant 0x100310))
      (codeRange (pc variant 0x100310) shortPrepareBytes) (shortPrepareEffect variant) := by
  cases variant
  case false =>
    simp only [pc]
    unfold shortPrepareBytes
    md5_run_begin lea_r64_effect_step 0x100310 0x4a (by unfold RexWPrefix; decide)
      7 (.sib 4 (some 13) 0 .none) (by decide) (by decide) (by decide)
    case boundary =>
      intro _ _
      exact text_address_ne_return hOutside 0x314 (by decide +kernel)
    md5_run_then add_r64_imm32_effect_step 0x100314 0x48 0xc7 192
      (by unfold RexWPrefix; decide) (by decide) (by decide)
    case sub => apply codeRange_mem_of_drop (p := 0x100310) 4; decide +kernel
    case boundary =>
      intro _ _
      exact text_address_ne_return hOutside 0x31b (by decide +kernel)
    md5_run_then mov_r64_r64_effect_step 0x10031b 0x4c 0xf6
      (by unfold RexWPrefix; decide) (by decide)
    case sub => apply codeRange_mem_of_drop (p := 0x100310) 11; decide +kernel
    case boundary =>
      intro _ _
      exact text_address_ne_return hOutside 0x31e (by decide +kernel)
    md5_run_then mov_r64_r64_effect_step 0x10031e 0x48 0xda
      (by unfold RexWPrefix; decide) (by decide)
    case sub => apply codeRange_mem_of_drop (p := 0x100310) 14; decide +kernel
    case boundary =>
      intro _ _
      exact text_address_ne_return hOutside 0x321 (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ he
    apply he.weaken
    · x86_norm [shortPrepareEffect, pc]
    · x86_norm [shortPrepareEffect, pc, stackPtr]
      simp only [BitVec.shiftLeft_zero]
      exact ⟨rfl, rfl, rfl⟩
    · intro i; cases i <;> x86_norm [shortPrepareEffect, pc]
    · x86_norm [shortPrepareEffect, pc]

  case true =>
    simp only [pc]
    unfold shortPrepareBytes
    md5_run_begin lea_r64_effect_step 0x1018c0 0x4a (by unfold RexWPrefix; decide)
      7 (.sib 4 (some 13) 0 .none) (by decide) (by decide) (by decide)
    case boundary =>
      intro _ _
      exact text_address_ne_return hOutside 0x18c4 (by decide +kernel)
    md5_run_then add_r64_imm32_effect_step 0x1018c4 0x48 0xc7 192
      (by unfold RexWPrefix; decide) (by decide) (by decide)
    case sub => apply codeRange_mem_of_drop (p := 0x1018c0) 4; decide +kernel
    case boundary =>
      intro _ _
      exact text_address_ne_return hOutside 0x18cb (by decide +kernel)
    md5_run_then mov_r64_r64_effect_step 0x1018cb 0x4c 0xf6
      (by unfold RexWPrefix; decide) (by decide)
    case sub => apply codeRange_mem_of_drop (p := 0x1018c0) 11; decide +kernel
    case boundary =>
      intro _ _
      exact text_address_ne_return hOutside 0x18ce (by decide +kernel)
    md5_run_then mov_r64_r64_effect_step 0x1018ce 0x48 0xda
      (by unfold RexWPrefix; decide) (by decide)
    case sub => apply codeRange_mem_of_drop (p := 0x1018c0) 14; decide +kernel
    case boundary =>
      intro _ _
      exact text_address_ne_return hOutside 0x18d1 (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ he
    apply he.weaken
    · x86_norm [shortPrepareEffect, pc]
    · x86_norm [shortPrepareEffect, pc, stackPtr]
      simp only [BitVec.shiftLeft_zero]
      exact ⟨rfl, rfl, rfl⟩
    · intro i; cases i <;> x86_norm [shortPrepareEffect, pc]
    · x86_norm [shortPrepareEffect, pc]


def shortReadyEffect (variant : Bool) (s : RamState) : Effect where
  rip := (pc variant 0x100321)
  writes := [⟨(.reg 13 : Operand 64), position s⟩,
    ⟨(.reg 5 : Operand 64), (Operand.reg 3 : Operand 64).read s - (64 - position s)⟩,
    ⟨(.reg 7 : Operand 64), stackPtr s + position s + 192⟩,
    ⟨(.reg 6 : Operand 64), (Operand.reg 14 : Operand 64).read s⟩,
    ⟨(.reg 2 : Operand 64), (Operand.reg 3 : Operand 64).read s⟩]
  flags := some ⟨none, none, none, none, none, none⟩

theorem short_ready [Bindings] {variant : Bool} {boundary : ReturnBoundary} {message input : ByteArray}
    {s u : RamState} (h : UpdatePre (kind variant) boundary message input s)
    (hp : Prepared variant boundary s u) (hshort : input.size < 64 - message.size % 64) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ ((shortReadyEffect variant) s).Holds s t := by
  obtain ⟨v, hav, hrv, hcv, hpcv, hagv⟩ := branch h hp
  rw [ite_eq_left hshort] at hpcv
  have hbytes : CodeIn (codeRange (pc variant 0x100310) shortPrepareBytes) v := by
    cases variant with
    | false => exact program_text_slice hcv 0x310 17 (by decide +kernel)
    | true => exact program_text_slice hcv 0x18c0 17 (by decide +kernel)
  obtain ⟨fuel, t, hat, hrt, _, het⟩ := short_prepare (variant := variant) boundary h.boundaryOutside
    v hrv hbytes hpcv
  have hct : CodeIn Extracted.programImage t := het.codeIn (by
    apply Effect.Avoids.of_noMem
    simp [shortPrepareEffect, Effect.components, Component.Covers]) hcv
  have hu3 : (Operand.reg 3 : Operand 64).read u = (Operand.reg 3 : Operand 64).read s :=
    hp.effect.agrees.read (by simp [entryEffect, Effect.components])
  have hu14 : (Operand.reg 14 : Operand 64).read u = (Operand.reg 14 : Operand 64).read s :=
    hp.effect.agrees.read (by simp [entryEffect, Effect.components])
  have husp : stackPtr u = stackPtr s :=
    hp.effect.agrees.read (n := 64) (r := 4) (by simp [entryEffect, Effect.components])
  have hv13 : (Operand.reg 13 : Operand 64).read v = position s :=
    (hagv.read (by simp)).trans hp.effect.writes.1
  have hv5 : (Operand.reg 5 : Operand 64).read v =
      (Operand.reg 3 : Operand 64).read s - (64 - position s) :=
    (hagv.read (by simp)).trans hp.effect.writes.2.2
  have hv3 : (Operand.reg 3 : Operand 64).read v = (Operand.reg 3 : Operand 64).read s :=
    (hagv.read (by simp)).trans hu3
  have hv14 : (Operand.reg 14 : Operand 64).read v = (Operand.reg 14 : Operand 64).read s :=
    (hagv.read (by simp)).trans hu14
  have hvsp : stackPtr v = stackPtr s :=
    (hagv.read (n := 64) (r := 4) (by simp)).trans husp
  obtain ⟨oldFuel, ha⟩ := hp.advances
  refine ⟨oldFuel + 1 + fuel, t, (ha.trans hav).trans hat, hrt, hct, ?_⟩
  refine ⟨het.rip, ?_, ?_, ?_⟩
  · change _ ∧ _ ∧ _ ∧ _ ∧ _
    refine ⟨(het.agrees.read (by simp [shortPrepareEffect, Effect.components])).trans hv13,
      (het.agrees.read (by simp [shortPrepareEffect, Effect.components])).trans hv5, ?_, ?_, ?_⟩
    · exact het.writes.1.trans (by rw [hvsp, hv13])
    · exact het.writes.2.1.trans hv14
    · exact het.writes.2.2.trans hv3
  · exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  · apply ((hp.effect.agrees.trans hagv).trans het.agrees).mono
    intro c hc
    simp only [entryEffect, shortPrepareEffect, shortReadyEffect, Effect.components,
      List.map_cons, List.map_nil, Write.component_reg, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp

end Md5.Proofs.Buffered.Update.Slices
