import Md5.Proofs.Buffered.Update.ResetSecond.Layout
import Md5.Proofs.Buffered.Update.ResetFirst.Prefix

namespace Md5.Proofs.Buffered.ResetSecond

open Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

def prefixBytes (kind : UpdateKind) : List UInt8 :=
  if kind = .resetDiscardSecond then [0x0f, 0xb6, 0x6c, 0x24, 0x5f, 0xba, 0x40, 0, 0, 0, 0x48, 0x29, 0xea, 0x4d, 0x89, 0xee, 0x49, 0x29, 0xd6] else
  [0x44, 0x0f, 0xb6, 0x6c, 0x24, 0x47, 0xba, 0x40, 0x00, 0x00, 0x00,
    0x4c, 0x29, 0xea, 0x4d, 0x89, 0xe6, 0x49, 0x29, 0xd6]


def prefixEffect (kind : UpdateKind) (s : RamState) : Effect :=
  let capacity := 64 - position kind s
  { rip := (pc kind 0x1009f3)
    writes := [⟨(.reg (positionRegister kind) : Operand 64), position kind s⟩,
      ⟨(.reg 2 : Operand 64), capacity⟩,
      ⟨(.reg 14 : Operand 64), (.reg kind.sizeRegister : Operand 64).read s - capacity⟩]
    flags := some (.ofStatusFlags (subSpec ((.reg kind.sizeRegister : Operand 64).read s) capacity).2) }

set_option maxHeartbeats 800000 in
theorem entry_prepare [Bindings] {kind : UpdateKind}
    (hkind : kind = .resetSecond ∨ kind = .finalizeResetSecond ∨ kind = .resetDiscardSecond) (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary (LoadPre (pc kind 0x1009df) (fun s ↦ kind.context s + 63) 1)
      (codeRange (pc kind 0x1009df) (prefixBytes kind)) (prefixEffect kind) := by
  rcases hkind with rfl | rfl | rfl
  ·
    unfold prefixBytes
    md5_run_begin (movzx_r_m8_rex_effect_step 0x1009df 0x44
      (by unfold RexPrefix; decide) 32 (.inr rfl)
      (fun seg ↦ (show RexNoWPrefix (0x44 : UInt8).toBitVec by
        unfold RexNoWPrefix; decide).operand_size seg)
      5 (.sib 4 none 0 (.d8 71)) (by decide) (by decide) (by decide))
    case pre =>
      intro s hP
      refine ⟨hP.rip, ?_⟩
      have hread := hP.read
      x86_norm [UpdateKind.context, UpdateKind.contextOffset, stackPtr] at hread ⊢
      exact hread
    case boundary =>
      intro _ _
      exact text_address_ne_return hOutside 0x9e5 (by decide +kernel)
    md5_run_then mov_r32_imm32_effect_step 0x1009e5 0xba (by decide) 64
    case sub => exact codeRange_mem_of_drop (p := 0x1009df) 6 (by decide +kernel)
    case boundary =>
      intro _ _
      exact text_address_ne_return hOutside 0x9ea (by decide +kernel)
    md5_run_then sub_r64_r64_effect_step 0x1009ea 0x4c 0xea
      (by unfold RexWPrefix; decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x1009df) 11 (by decide +kernel)
    case boundary =>
      intro _ _
      exact text_address_ne_return hOutside 0x9ed (by decide +kernel)
    md5_run_then mov_r64_r64_effect_step 0x1009ed 0x4d 0xe6
      (by unfold RexWPrefix; decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x1009df) 14 (by decide +kernel)
    case boundary =>
      intro _ _
      exact text_address_ne_return hOutside 0x9f0 (by decide +kernel)
    md5_run_then sub_r64_r64_effect_step 0x1009f0 0x49 0xd6
      (by unfold RexWPrefix; decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x1009df) 17 (by decide +kernel)
    case boundary =>
      intro _ _
      exact text_address_ne_return hOutside 0x9f3 (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [prefixEffect, pc, UpdateKind.sizeRegister, positionRegister, savedInputRegister, UpdateKind.inputRegister]
    · x86_norm [prefixEffect, position, UpdateKind.context, UpdateKind.contextOffset, pc, positionRegister, UpdateKind.sizeRegister, savedInputRegister, UpdateKind.inputRegister, stackPtr]
      simp [Operand.read, gprNumber, rexR, modrmReg]
    · intro i; cases i <;> x86_norm [prefixEffect, position, UpdateKind.context, UpdateKind.contextOffset, pc, positionRegister, UpdateKind.sizeRegister, savedInputRegister, UpdateKind.inputRegister, stackPtr]
      all_goals simp [Operand.read, gprNumber, rexR, modrmReg]
    · x86_norm [prefixEffect, pc, UpdateKind.sizeRegister, positionRegister, savedInputRegister, UpdateKind.inputRegister]

  ·
    unfold prefixBytes
    md5_run_begin (movzx_r_m8_rex_effect_step 0x10106f 0x44
      (by unfold RexPrefix; decide) 32 (.inr rfl)
      (fun seg ↦ (show RexNoWPrefix (0x44 : UInt8).toBitVec by
        unfold RexNoWPrefix; decide).operand_size seg)
      5 (.sib 4 none 0 (.d8 71)) (by decide) (by decide) (by decide))
    case pre =>
      intro s hP
      refine ⟨hP.rip, ?_⟩
      have hread := hP.read
      x86_norm [UpdateKind.context, UpdateKind.contextOffset, stackPtr] at hread ⊢
      exact hread
    case boundary =>
      intro _ _
      exact text_address_ne_return hOutside 0x1075 (by decide +kernel)
    md5_run_then mov_r32_imm32_effect_step 0x101075 0xba (by decide) 64
    case sub => exact codeRange_mem_of_drop (p := 0x10106f) 6 (by decide +kernel)
    case boundary =>
      intro _ _
      exact text_address_ne_return hOutside 0x107a (by decide +kernel)
    md5_run_then sub_r64_r64_effect_step 0x10107a 0x4c 0xea
      (by unfold RexWPrefix; decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x10106f) 11 (by decide +kernel)
    case boundary =>
      intro _ _
      exact text_address_ne_return hOutside 0x107d (by decide +kernel)
    md5_run_then mov_r64_r64_effect_step 0x10107d 0x4d 0xe6
      (by unfold RexWPrefix; decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x10106f) 14 (by decide +kernel)
    case boundary =>
      intro _ _
      exact text_address_ne_return hOutside 0x1080 (by decide +kernel)
    md5_run_then sub_r64_r64_effect_step 0x101080 0x49 0xd6
      (by unfold RexWPrefix; decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x10106f) 17 (by decide +kernel)
    case boundary =>
      intro _ _
      exact text_address_ne_return hOutside 0x1083 (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [prefixEffect, pc, UpdateKind.sizeRegister, positionRegister, savedInputRegister, UpdateKind.inputRegister]
    · x86_norm [prefixEffect, position, UpdateKind.context, UpdateKind.contextOffset, pc, positionRegister, UpdateKind.sizeRegister, savedInputRegister, UpdateKind.inputRegister, stackPtr]
      simp [Operand.read, gprNumber, rexR, modrmReg]
    · intro i; cases i <;> x86_norm [prefixEffect, position, UpdateKind.context, UpdateKind.contextOffset, pc, positionRegister, UpdateKind.sizeRegister, savedInputRegister, UpdateKind.inputRegister, stackPtr]
      all_goals simp [Operand.read, gprNumber, rexR, modrmReg]
    · x86_norm [prefixEffect, pc, UpdateKind.sizeRegister, positionRegister, savedInputRegister, UpdateKind.inputRegister]

  ·
    unfold prefixBytes
    md5_run_begin movzx_r32_m8_effect_step 0x101549 5 (.sib 4 none 0 (.d8 95)) (by decide) (by decide) (by decide)
    case pre =>
      intro s hP
      refine ⟨hP.rip, ?_⟩
      have hread := hP.read
      x86_norm [UpdateKind.context, UpdateKind.contextOffset, stackPtr] at hread ⊢
      exact hread
    case boundary =>
      intro _ _
      exact text_address_ne_return hOutside 0x154e (by decide +kernel)
    md5_run_then mov_r32_imm32_effect_step 0x10154e 0xba (by decide) 64
    case sub => exact codeRange_mem_of_drop (p := 0x101549) 5 (by decide +kernel)
    case boundary =>
      intro _ _
      exact text_address_ne_return hOutside 0x1553 (by decide +kernel)
    md5_run_then sub_r64_r64_effect_step 0x101553 0x48 0xea
      (by unfold RexWPrefix; decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x101549) 10 (by decide +kernel)
    case boundary =>
      intro _ _
      exact text_address_ne_return hOutside 0x1556 (by decide +kernel)
    md5_run_then mov_r64_r64_effect_step 0x101556 0x4d 0xee
      (by unfold RexWPrefix; decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x101549) 13 (by decide +kernel)
    case boundary =>
      intro _ _
      exact text_address_ne_return hOutside 0x1559 (by decide +kernel)
    md5_run_then sub_r64_r64_effect_step 0x101559 0x49 0xd6
      (by unfold RexWPrefix; decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x101549) 16 (by decide +kernel)
    case boundary =>
      intro _ _
      exact text_address_ne_return hOutside 0x155c (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [prefixEffect, pc, UpdateKind.sizeRegister, positionRegister, savedInputRegister, UpdateKind.inputRegister]
    · x86_norm [prefixEffect, position, UpdateKind.context, UpdateKind.contextOffset, pc, positionRegister, UpdateKind.sizeRegister, savedInputRegister, UpdateKind.inputRegister, stackPtr]
      simp [Operand.read, gprNumber, rexR, modrmReg]
    · intro i; cases i <;> x86_norm [prefixEffect, position, UpdateKind.context, UpdateKind.contextOffset, pc, positionRegister, UpdateKind.sizeRegister, savedInputRegister, UpdateKind.inputRegister, stackPtr]
      all_goals simp [Operand.read, gprNumber, rexR, modrmReg]
    · x86_norm [prefixEffect, pc, UpdateKind.sizeRegister, positionRegister, savedInputRegister, UpdateKind.inputRegister]

def entryEffect (kind : UpdateKind) (s : RamState) : Effect :=
  { (prefixEffect kind) s with
    rip := if ((.reg kind.sizeRegister : Operand 64).read s).toNat < (64 - position kind s).toNat then
      (pc kind 0x1009a0) else (pc kind 0x1009f5)
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem entry_branch [Bindings] {kind : UpdateKind}
    (hkind : kind = .resetSecond ∨ kind = .finalizeResetSecond ∨ kind = .resetDiscardSecond) (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (LoadPre (pc kind 0x1009df) (fun s ↦ kind.context s + 63) 1)
      Extracted.programImage (entryEffect kind) := by
  rcases hkind with rfl | rfl | rfl
  ·
    intro s hs hc hp
    have hbytes : CodeIn (codeRange 0x1009df (prefixBytes UpdateKind.resetSecond)) s :=
      program_text_slice hc 0x9df 20 (by decide +kernel)
    obtain ⟨fuel, u, ha, hu, _, he⟩ := entry_prepare (kind := .resetSecond) (by exact Or.inl rfl) boundary hOutside s hs hbytes hp
    have hcu := he.agrees.codeIn (by
      simp [prefixEffect, Effect.components, Component.Covers]) hc
    have hcf : condHolds 2 (StatusFlags.ofRFLAGS u.RFLAGS) =
        decide (((.reg UpdateKind.resetSecond.sizeRegister : Operand 64).read s).toNat < (64 - position UpdateKind.resetSecond s).toNat) :=
      he.flags.1
    have hnext : (jccEffect 0x1009f3 2 2 ((0xab#8).signExtend 64) u).rip =
        ((entryEffect UpdateKind.resetSecond) s).rip := by
      simp only [jccEffect, hcf, branchEffect, entryEffect, decide_eq_true_eq]
      split <;> rfl
    have hne : ((entryEffect UpdateKind.resetSecond) s).rip ≠ boundary.rip := by
      unfold entryEffect
      split
      · exact text_address_ne_return hOutside 0x9a0 (by decide +kernel)
      · exact text_address_ne_return hOutside 0x9f5 (by decide +kernel)
    have hbranch : CodeIn (codeRange 0x1009f3 [0x72, 0xab]) u :=
      program_text_slice hcu 0x9f3 2 (by decide +kernel)
    obtain ⟨t, hb, ht, heb⟩ := (jcc_rel8_effect_step 0x1009f3 2 0xab).advances
      hu hbranch ⟨he.rip, fun _ ↦ by decide +kernel⟩ (hnext ▸ hne)
    have hag : AgreesExcept [.rip] u t := heb.agrees
    refine ⟨fuel + 1, t, ha.trans hb, ht,
      hag.codeIn (by simp [Component.Covers]) hcu, heb.rip.trans hnext, ?_, by trivial, ?_⟩
    · change (.reg (positionRegister UpdateKind.resetSecond) : Operand 64).read t = _ ∧ (.reg 2 : Operand 64).read t = _ ∧
        (.reg 14 : Operand 64).read t = _
      exact ⟨(hag.read (by simp)).trans he.writes.1,
        (hag.read (by simp)).trans he.writes.2.1,
        (hag.read (by simp)).trans he.writes.2.2⟩
    · apply (he.agrees.trans hag).mono
      simp [prefixEffect, entryEffect, Effect.components]

  ·
    intro s hs hc hp
    have hbytes : CodeIn (codeRange 0x10106f (prefixBytes UpdateKind.finalizeResetSecond)) s :=
      program_text_slice hc 0x106f 20 (by decide +kernel)
    obtain ⟨fuel, u, ha, hu, _, he⟩ := entry_prepare (kind := .finalizeResetSecond) (by exact Or.inr (Or.inl rfl)) boundary hOutside s hs hbytes hp
    have hcu := he.agrees.codeIn (by
      simp [prefixEffect, Effect.components, Component.Covers]) hc
    have hcf : condHolds 2 (StatusFlags.ofRFLAGS u.RFLAGS) =
        decide (((.reg UpdateKind.finalizeResetSecond.sizeRegister : Operand 64).read s).toNat < (64 - position UpdateKind.finalizeResetSecond s).toNat) :=
      he.flags.1
    have hnext : (jccEffect 0x101083 2 2 ((0xab#8).signExtend 64) u).rip =
        ((entryEffect UpdateKind.finalizeResetSecond) s).rip := by
      simp only [jccEffect, hcf, branchEffect, entryEffect, decide_eq_true_eq]
      split <;> rfl
    have hne : ((entryEffect UpdateKind.finalizeResetSecond) s).rip ≠ boundary.rip := by
      unfold entryEffect
      split
      · exact text_address_ne_return hOutside 0x1030 (by decide +kernel)
      · exact text_address_ne_return hOutside 0x1085 (by decide +kernel)
    have hbranch : CodeIn (codeRange 0x101083 [0x72, 0xab]) u :=
      program_text_slice hcu 0x1083 2 (by decide +kernel)
    obtain ⟨t, hb, ht, heb⟩ := (jcc_rel8_effect_step 0x101083 2 0xab).advances
      hu hbranch ⟨he.rip, fun _ ↦ by decide +kernel⟩ (hnext ▸ hne)
    have hag : AgreesExcept [.rip] u t := heb.agrees
    refine ⟨fuel + 1, t, ha.trans hb, ht,
      hag.codeIn (by simp [Component.Covers]) hcu, heb.rip.trans hnext, ?_, by trivial, ?_⟩
    · change (.reg (positionRegister UpdateKind.finalizeResetSecond) : Operand 64).read t = _ ∧ (.reg 2 : Operand 64).read t = _ ∧
        (.reg 14 : Operand 64).read t = _
      exact ⟨(hag.read (by simp)).trans he.writes.1,
        (hag.read (by simp)).trans he.writes.2.1,
        (hag.read (by simp)).trans he.writes.2.2⟩
    · apply (he.agrees.trans hag).mono
      simp [prefixEffect, entryEffect, Effect.components]

  ·
    intro s hs hc hp
    have hbytes : CodeIn (codeRange 0x101549 (prefixBytes UpdateKind.resetDiscardSecond)) s :=
      program_text_slice hc 0x1549 19 (by decide +kernel)
    obtain ⟨fuel, u, ha, hu, _, he⟩ := entry_prepare (kind := .resetDiscardSecond) (by exact Or.inr (Or.inr rfl)) boundary hOutside s hs hbytes hp
    have hcu := he.agrees.codeIn (by
      simp [prefixEffect, Effect.components, Component.Covers]) hc
    have hcf : condHolds 2 (StatusFlags.ofRFLAGS u.RFLAGS) =
        decide (((.reg UpdateKind.resetDiscardSecond.sizeRegister : Operand 64).read s).toNat < (64 - position UpdateKind.resetDiscardSecond s).toNat) :=
      he.flags.1
    have hnext : (jccEffect 0x10155c 2 2 ((0xb2#8).signExtend 64) u).rip =
        ((entryEffect UpdateKind.resetDiscardSecond) s).rip := by
      simp only [jccEffect, hcf, branchEffect, entryEffect, decide_eq_true_eq]
      split <;> rfl
    have hne : ((entryEffect UpdateKind.resetDiscardSecond) s).rip ≠ boundary.rip := by
      unfold entryEffect
      split
      · exact text_address_ne_return hOutside 0x1510 (by decide +kernel)
      · exact text_address_ne_return hOutside 0x155e (by decide +kernel)
    have hbranch : CodeIn (codeRange 0x10155c [0x72, 0xb2]) u :=
      program_text_slice hcu 0x155c 2 (by decide +kernel)
    obtain ⟨t, hb, ht, heb⟩ := (jcc_rel8_effect_step 0x10155c 2 0xb2).advances
      hu hbranch ⟨he.rip, fun _ ↦ by decide +kernel⟩ (hnext ▸ hne)
    have hag : AgreesExcept [.rip] u t := heb.agrees
    refine ⟨fuel + 1, t, ha.trans hb, ht,
      hag.codeIn (by simp [Component.Covers]) hcu, heb.rip.trans hnext, ?_, by trivial, ?_⟩
    · change (.reg (positionRegister UpdateKind.resetDiscardSecond) : Operand 64).read t = _ ∧ (.reg 2 : Operand 64).read t = _ ∧
        (.reg 14 : Operand 64).read t = _
      exact ⟨(hag.read (by simp)).trans he.writes.1,
        (hag.read (by simp)).trans he.writes.2.1,
        (hag.read (by simp)).trans he.writes.2.2⟩
    · apply (he.agrees.trans hag).mono
      simp [prefixEffect, entryEffect, Effect.components]

def partialEffect (kind : UpdateKind) (s : RamState) : Effect :=
  { rip := if (.reg (positionRegister kind) : Operand 64).read s = 0 then (pc kind 0x100a82) else (pc kind 0x1009fe)
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem partial_branch [Bindings] {kind : UpdateKind}
    (hkind : kind = .resetSecond ∨ kind = .finalizeResetSecond ∨ kind = .resetDiscardSecond) (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = (pc kind 0x1009f5))
      Extracted.programImage (partialEffect kind) := by
  rcases hkind with rfl | rfl | rfl
  ·
    intro s hs hc hp
    have hbytes : CodeIn (codeRange 0x1009f5 [0x4d, 0x85, 0xed]) s :=
      program_text_slice hc 0x9f5 3 (by decide +kernel)
    have htest : StepEffect (fun s ↦ s.RIP = 0x1009f5)
        (codeRange 0x1009f5 [0x4d, 0x85, 0xed]) (testR64R64Effect 0x1009f5 13 13) :=
      test_r64_r64_effect_step _ _ _ (by unfold RexWPrefix; decide) (by decide)
    obtain ⟨u, ha, hu, he⟩ := htest.advances hs hbytes hp
      (text_address_ne_return hOutside 0x9f8 (by decide +kernel))
    have hcu := he.codeIn (testR64R64Effect_avoids _ _ _ _ _) hc
    have hzf : condHolds 4 (StatusFlags.ofRFLAGS u.RFLAGS) =
        ((.reg (positionRegister UpdateKind.resetSecond) : Operand 64).read s == 0) := by
      have hz := he.flags.2.2.2.1
      change (StatusFlags.ofRFLAGS u.RFLAGS).ZF =
        (((.reg (positionRegister UpdateKind.resetSecond) : Operand 64).read s &&& (.reg (positionRegister UpdateKind.resetSecond) : Operand 64).read s) == 0) at hz
      rw [BitVec.and_self] at hz
      exact hz
    have hnext : (jccEffect 0x1009f8 6 4 ((0x84#32).signExtend 64) u).rip =
        ((partialEffect UpdateKind.resetSecond) s).rip := by
      simp only [jccEffect, hzf, branchEffect, partialEffect, beq_iff_eq]
      split <;> rfl
    have hne : ((partialEffect UpdateKind.resetSecond) s).rip ≠ boundary.rip := by
      unfold partialEffect
      split
      · exact text_address_ne_return hOutside 0xa82 (by decide +kernel)
      · exact text_address_ne_return hOutside 0x9fe (by decide +kernel)
    have hbranch : CodeIn (codeRange 0x1009f8 [0x0f, 0x84, 0x84, 0x00, 0x00, 0x00]) u :=
      program_text_slice hcu 0x9f8 6 (by decide +kernel)
    obtain ⟨t, hb, ht, heb⟩ := (jcc_rel32_effect_step 0x1009f8 4 0x84).advances
      hu hbranch ⟨he.rip, fun _ ↦ by decide +kernel⟩ (hnext ▸ hne)
    have hag : AgreesExcept [.rip] u t := heb.agrees
    refine ⟨2, t, ha.trans hb, ht, hag.codeIn (by simp [Component.Covers]) hcu,
      heb.rip.trans hnext, by trivial, by trivial, ?_⟩
    apply (he.agrees.trans hag).mono
    simp [partialEffect, testR64R64Effect, Effect.components]

  ·
    intro s hs hc hp
    have hbytes : CodeIn (codeRange 0x101085 [0x4d, 0x85, 0xed]) s :=
      program_text_slice hc 0x1085 3 (by decide +kernel)
    have htest : StepEffect (fun s ↦ s.RIP = 0x101085)
        (codeRange 0x101085 [0x4d, 0x85, 0xed]) (testR64R64Effect 0x101085 13 13) :=
      test_r64_r64_effect_step _ _ _ (by unfold RexWPrefix; decide) (by decide)
    obtain ⟨u, ha, hu, he⟩ := htest.advances hs hbytes hp
      (text_address_ne_return hOutside 0x1088 (by decide +kernel))
    have hcu := he.codeIn (testR64R64Effect_avoids _ _ _ _ _) hc
    have hzf : condHolds 4 (StatusFlags.ofRFLAGS u.RFLAGS) =
        ((.reg (positionRegister UpdateKind.finalizeResetSecond) : Operand 64).read s == 0) := by
      have hz := he.flags.2.2.2.1
      change (StatusFlags.ofRFLAGS u.RFLAGS).ZF =
        (((.reg (positionRegister UpdateKind.finalizeResetSecond) : Operand 64).read s &&& (.reg (positionRegister UpdateKind.finalizeResetSecond) : Operand 64).read s) == 0) at hz
      rw [BitVec.and_self] at hz
      exact hz
    have hnext : (jccEffect 0x101088 6 4 ((0x84#32).signExtend 64) u).rip =
        ((partialEffect UpdateKind.finalizeResetSecond) s).rip := by
      simp only [jccEffect, hzf, branchEffect, partialEffect, beq_iff_eq]
      split <;> rfl
    have hne : ((partialEffect UpdateKind.finalizeResetSecond) s).rip ≠ boundary.rip := by
      unfold partialEffect
      split
      · exact text_address_ne_return hOutside 0x1112 (by decide +kernel)
      · exact text_address_ne_return hOutside 0x108e (by decide +kernel)
    have hbranch : CodeIn (codeRange 0x101088 [0x0f, 0x84, 0x84, 0x00, 0x00, 0x00]) u :=
      program_text_slice hcu 0x1088 6 (by decide +kernel)
    obtain ⟨t, hb, ht, heb⟩ := (jcc_rel32_effect_step 0x101088 4 0x84).advances
      hu hbranch ⟨he.rip, fun _ ↦ by decide +kernel⟩ (hnext ▸ hne)
    have hag : AgreesExcept [.rip] u t := heb.agrees
    refine ⟨2, t, ha.trans hb, ht, hag.codeIn (by simp [Component.Covers]) hcu,
      heb.rip.trans hnext, by trivial, by trivial, ?_⟩
    apply (he.agrees.trans hag).mono
    simp [partialEffect, testR64R64Effect, Effect.components]

  ·
    intro s hs hc hp
    have hbytes : CodeIn (codeRange 0x10155e [0x48, 0x85, 0xed]) s :=
      program_text_slice hc 0x155e 3 (by decide +kernel)
    have htest : StepEffect (fun s ↦ s.RIP = 0x10155e)
        (codeRange 0x10155e [0x48, 0x85, 0xed]) (testR64R64Effect 0x10155e 5 5) :=
      test_r64_r64_effect_step _ _ _ (by unfold RexWPrefix; decide) (by decide)
    obtain ⟨u, ha, hu, he⟩ := htest.advances hs hbytes hp
      (text_address_ne_return hOutside 0x1561 (by decide +kernel))
    have hcu := he.codeIn (testR64R64Effect_avoids _ _ _ _ _) hc
    have hzf : condHolds 4 (StatusFlags.ofRFLAGS u.RFLAGS) =
        ((.reg (positionRegister UpdateKind.resetDiscardSecond) : Operand 64).read s == 0) := by
      have hz := he.flags.2.2.2.1
      change (StatusFlags.ofRFLAGS u.RFLAGS).ZF =
        (((.reg (positionRegister UpdateKind.resetDiscardSecond) : Operand 64).read s &&& (.reg (positionRegister UpdateKind.resetDiscardSecond) : Operand 64).read s) == 0) at hz
      rw [BitVec.and_self] at hz
      exact hz
    have hnext : (jccEffect 0x101561 6 4 ((0x88#32).signExtend 64) u).rip =
        ((partialEffect UpdateKind.resetDiscardSecond) s).rip := by
      simp only [jccEffect, hzf, branchEffect, partialEffect, beq_iff_eq]
      split <;> rfl
    have hne : ((partialEffect UpdateKind.resetDiscardSecond) s).rip ≠ boundary.rip := by
      unfold partialEffect
      split
      · exact text_address_ne_return hOutside 0x15ef (by decide +kernel)
      · exact text_address_ne_return hOutside 0x1567 (by decide +kernel)
    have hbranch : CodeIn (codeRange 0x101561 [0x0f, 0x84, 0x88, 0x00, 0x00, 0x00]) u :=
      program_text_slice hcu 0x1561 6 (by decide +kernel)
    obtain ⟨t, hb, ht, heb⟩ := (jcc_rel32_effect_step 0x101561 4 0x88).advances
      hu hbranch ⟨he.rip, fun _ ↦ by decide +kernel⟩ (hnext ▸ hne)
    have hag : AgreesExcept [.rip] u t := heb.agrees
    refine ⟨2, t, ha.trans hb, ht, hag.codeIn (by simp [Component.Covers]) hcu,
      heb.rip.trans hnext, by trivial, by trivial, ?_⟩
    apply (he.agrees.trans hag).mono
    simp [partialEffect, testR64R64Effect, Effect.components]

def remainderCountBytes (kind : UpdateKind) : List UInt8 :=
  [0x4c, 0x89, (if kind = .resetDiscardSecond then 0xeb else 0xe6), 0x4c, 0x89, 0xf2, 0x48, 0xc1, 0xea, 0x06]

def remainderCountEffect (kind : UpdateKind) (s : RamState) : Effect :=
  { rip := (pc kind 0x100a33)
    writes := [⟨(.reg kind.inputRegister : Operand 64), (.reg (savedInputRegister kind) : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64), (.reg 14 : Operand 64).read s >>> 6⟩]
    flags := some (shrFlags (StatusFlags.ofRFLAGS s.RFLAGS) 6 ((.reg 14 : Operand 64).read s)) }

theorem remainder_count_prepare [Bindings] {kind : UpdateKind}
    (hkind : kind = .resetSecond ∨ kind = .finalizeResetSecond ∨ kind = .resetDiscardSecond) (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = (pc kind 0x100a29))
      (codeRange (pc kind 0x100a29) (remainderCountBytes kind)) (remainderCountEffect kind) := by
  rcases hkind with rfl | rfl | rfl
  ·
    unfold remainderCountBytes
    md5_run_begin mov_r64_r64_effect_step 0x100a29 0x4c 0xe6
      (by unfold RexWPrefix; decide) (by decide)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0xa2c (by decide +kernel)
    md5_run_then mov_r64_r64_effect_step 0x100a2c 0x4c 0xf2
      (by unfold RexWPrefix; decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x100a29) 3 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0xa2f (by decide +kernel)
    md5_run_then shr_r64_imm8_effect_step 0x100a2f 0x48 0xea 6
      (by unfold RexWPrefix; decide) (by decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x100a29) 6 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0xa33 (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [remainderCountEffect, shiftCount, pc, UpdateKind.sizeRegister, savedInputRegister, UpdateKind.inputRegister]
    · x86_norm [remainderCountEffect, shiftCount, pc, UpdateKind.sizeRegister, savedInputRegister, UpdateKind.inputRegister]
      simp [Operand.read, gprNumber, rexR, modrmReg]
    · intro i; cases i <;> x86_norm [remainderCountEffect, shiftCount, pc, UpdateKind.sizeRegister, savedInputRegister, UpdateKind.inputRegister]
      all_goals simp [Operand.read, gprNumber, rexR, modrmReg]
    · x86_norm [remainderCountEffect, shiftCount, pc, UpdateKind.sizeRegister, savedInputRegister, UpdateKind.inputRegister]

  ·
    unfold remainderCountBytes
    md5_run_begin mov_r64_r64_effect_step 0x1010b9 0x4c 0xe6
      (by unfold RexWPrefix; decide) (by decide)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x10bc (by decide +kernel)
    md5_run_then mov_r64_r64_effect_step 0x1010bc 0x4c 0xf2
      (by unfold RexWPrefix; decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x1010b9) 3 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x10bf (by decide +kernel)
    md5_run_then shr_r64_imm8_effect_step 0x1010bf 0x48 0xea 6
      (by unfold RexWPrefix; decide) (by decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x1010b9) 6 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x10c3 (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [remainderCountEffect, shiftCount, pc, UpdateKind.sizeRegister, savedInputRegister, UpdateKind.inputRegister]
    · x86_norm [remainderCountEffect, shiftCount, pc, UpdateKind.sizeRegister, savedInputRegister, UpdateKind.inputRegister]
      simp [Operand.read, gprNumber, rexR, modrmReg]
    · intro i; cases i <;> x86_norm [remainderCountEffect, shiftCount, pc, UpdateKind.sizeRegister, savedInputRegister, UpdateKind.inputRegister]
      all_goals simp [Operand.read, gprNumber, rexR, modrmReg]
    · x86_norm [remainderCountEffect, shiftCount, pc, UpdateKind.sizeRegister, savedInputRegister, UpdateKind.inputRegister]

  ·
    unfold remainderCountBytes
    md5_run_begin mov_r64_r64_effect_step 0x101597 0x4c 0xeb
      (by unfold RexWPrefix; decide) (by decide)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x159a (by decide +kernel)
    md5_run_then mov_r64_r64_effect_step 0x10159a 0x4c 0xf2
      (by unfold RexWPrefix; decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x101597) 3 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x159d (by decide +kernel)
    md5_run_then shr_r64_imm8_effect_step 0x10159d 0x48 0xea 6
      (by unfold RexWPrefix; decide) (by decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x101597) 6 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x15a1 (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [remainderCountEffect, shiftCount, pc, UpdateKind.sizeRegister, savedInputRegister, UpdateKind.inputRegister]
    · x86_norm [remainderCountEffect, shiftCount, pc, UpdateKind.sizeRegister, savedInputRegister, UpdateKind.inputRegister]
      simp [Operand.read, gprNumber, rexR, modrmReg]
    · intro i; cases i <;> x86_norm [remainderCountEffect, shiftCount, pc, UpdateKind.sizeRegister, savedInputRegister, UpdateKind.inputRegister]
      all_goals simp [Operand.read, gprNumber, rexR, modrmReg]
    · x86_norm [remainderCountEffect, shiftCount, pc, UpdateKind.sizeRegister, savedInputRegister, UpdateKind.inputRegister]

def alignedCountBytes (kind : UpdateKind) : List UInt8 :=
  [0x4d, 0x89, (if kind = .resetDiscardSecond then 0xee else 0xe6), 0x4c, 0x89, 0xf2, 0x48, 0xc1, 0xea, 0x06]

def alignedCountEffect (kind : UpdateKind) (s : RamState) : Effect :=
  { rip := (pc kind 0x100a8c)
    writes := [⟨(.reg 14 : Operand 64), (.reg kind.sizeRegister : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64), (.reg kind.sizeRegister : Operand 64).read s >>> 6⟩]
    flags := some (shrFlags (StatusFlags.ofRFLAGS s.RFLAGS) 6 ((.reg kind.sizeRegister : Operand 64).read s)) }

theorem aligned_count_prepare [Bindings] {kind : UpdateKind}
    (hkind : kind = .resetSecond ∨ kind = .finalizeResetSecond ∨ kind = .resetDiscardSecond) (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = (pc kind 0x100a82))
      (codeRange (pc kind 0x100a82) (alignedCountBytes kind)) (alignedCountEffect kind) := by
  rcases hkind with rfl | rfl | rfl
  ·
    unfold alignedCountBytes
    md5_run_begin mov_r64_r64_effect_step 0x100a82 0x4d 0xe6
      (by unfold RexWPrefix; decide) (by decide)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0xa85 (by decide +kernel)
    md5_run_then mov_r64_r64_effect_step 0x100a85 0x4c 0xf2
      (by unfold RexWPrefix; decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x100a82) 3 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0xa88 (by decide +kernel)
    md5_run_then shr_r64_imm8_effect_step 0x100a88 0x48 0xea 6
      (by unfold RexWPrefix; decide) (by decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x100a82) 6 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0xa8c (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [alignedCountEffect, shiftCount, pc, UpdateKind.sizeRegister, savedInputRegister, UpdateKind.inputRegister]
    · x86_norm [alignedCountEffect, shiftCount, pc, UpdateKind.sizeRegister, savedInputRegister, UpdateKind.inputRegister]
      simp [Operand.read, gprNumber, rexR, modrmReg]
    · intro i; cases i <;> x86_norm [alignedCountEffect, shiftCount, pc, UpdateKind.sizeRegister, savedInputRegister, UpdateKind.inputRegister]
      all_goals simp [Operand.read, gprNumber, rexR, modrmReg]
    · x86_norm [alignedCountEffect, shiftCount, pc, UpdateKind.sizeRegister, savedInputRegister, UpdateKind.inputRegister]

  ·
    unfold alignedCountBytes
    md5_run_begin mov_r64_r64_effect_step 0x101112 0x4d 0xe6
      (by unfold RexWPrefix; decide) (by decide)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x1115 (by decide +kernel)
    md5_run_then mov_r64_r64_effect_step 0x101115 0x4c 0xf2
      (by unfold RexWPrefix; decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x101112) 3 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x1118 (by decide +kernel)
    md5_run_then shr_r64_imm8_effect_step 0x101118 0x48 0xea 6
      (by unfold RexWPrefix; decide) (by decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x101112) 6 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x111c (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [alignedCountEffect, shiftCount, pc, UpdateKind.sizeRegister, savedInputRegister, UpdateKind.inputRegister]
    · x86_norm [alignedCountEffect, shiftCount, pc, UpdateKind.sizeRegister, savedInputRegister, UpdateKind.inputRegister]
      simp [Operand.read, gprNumber, rexR, modrmReg]
    · intro i; cases i <;> x86_norm [alignedCountEffect, shiftCount, pc, UpdateKind.sizeRegister, savedInputRegister, UpdateKind.inputRegister]
      all_goals simp [Operand.read, gprNumber, rexR, modrmReg]
    · x86_norm [alignedCountEffect, shiftCount, pc, UpdateKind.sizeRegister, savedInputRegister, UpdateKind.inputRegister]

  ·
    unfold alignedCountBytes
    md5_run_begin mov_r64_r64_effect_step 0x1015ef 0x4d 0xee
      (by unfold RexWPrefix; decide) (by decide)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x15f2 (by decide +kernel)
    md5_run_then mov_r64_r64_effect_step 0x1015f2 0x4c 0xf2
      (by unfold RexWPrefix; decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x1015ef) 3 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x15f5 (by decide +kernel)
    md5_run_then shr_r64_imm8_effect_step 0x1015f5 0x48 0xea 6
      (by unfold RexWPrefix; decide) (by decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := 0x1015ef) 6 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x15f9 (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [alignedCountEffect, shiftCount, pc, UpdateKind.sizeRegister, savedInputRegister, UpdateKind.inputRegister]
    · x86_norm [alignedCountEffect, shiftCount, pc, UpdateKind.sizeRegister, savedInputRegister, UpdateKind.inputRegister]
      simp [Operand.read, gprNumber, rexR, modrmReg]
    · intro i; cases i <;> x86_norm [alignedCountEffect, shiftCount, pc, UpdateKind.sizeRegister, savedInputRegister, UpdateKind.inputRegister]
      all_goals simp [Operand.read, gprNumber, rexR, modrmReg]
    · x86_norm [alignedCountEffect, shiftCount, pc, UpdateKind.sizeRegister, savedInputRegister, UpdateKind.inputRegister]

def remainderBranchEffect (kind : UpdateKind) (s : RamState) : Effect :=
  { (remainderCountEffect kind) s with
    rip := if (.reg 14 : Operand 64).read s >>> 6 = 0 then (pc kind 0x100a4a) else (pc kind 0x100a35)
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem remainder_count_branch [Bindings] {kind : UpdateKind}
    (hkind : kind = .resetSecond ∨ kind = .finalizeResetSecond ∨ kind = .resetDiscardSecond) (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = (pc kind 0x100a29))
      Extracted.programImage (remainderBranchEffect kind) := by
  rcases hkind with rfl | rfl | rfl
  ·
    intro s hs hc hp
    have hbytes : CodeIn (codeRange 0x100a29 (remainderCountBytes UpdateKind.resetSecond)) s :=
      program_text_slice hc 0xa29 10 (by decide +kernel)
    obtain ⟨fuel, u, ha, hu, _, he⟩ := remainder_count_prepare (kind := .resetSecond) (by exact Or.inl rfl) boundary hOutside s hs hbytes hp
    have hcu := he.agrees.codeIn (by
      simp [remainderCountEffect, Effect.components, Component.Covers]) hc
    have hz : condHolds 4 (StatusFlags.ofRFLAGS u.RFLAGS) =
        ((.reg 14 : Operand 64).read s >>> 6 == 0) := he.flags.2.2.2.1
    have hnext : (jccEffect 0x100a33 2 4 ((0x15#8).signExtend 64) u).rip =
        ((remainderBranchEffect UpdateKind.resetSecond) s).rip := by
      simp only [jccEffect, hz, branchEffect, remainderBranchEffect, beq_iff_eq]
      split <;> rfl
    have hne : ((remainderBranchEffect UpdateKind.resetSecond) s).rip ≠ boundary.rip := by
      unfold remainderBranchEffect
      split
      · exact text_address_ne_return hOutside 0xa4a (by decide +kernel)
      · exact text_address_ne_return hOutside 0xa35 (by decide +kernel)
    have hbranch : CodeIn (codeRange 0x100a33 [0x74, 0x15]) u :=
      program_text_slice hcu 0xa33 2 (by decide +kernel)
    obtain ⟨t, hb, ht, heb⟩ := (jcc_rel8_effect_step 0x100a33 4 0x15).advances
      hu hbranch ⟨he.rip, fun _ ↦ by decide +kernel⟩ (hnext ▸ hne)
    have hag : AgreesExcept [.rip] u t := heb.agrees
    refine ⟨fuel + 1, t, ha.trans hb, ht,
      hag.codeIn (by simp [Component.Covers]) hcu, heb.rip.trans hnext, ?_, by trivial, ?_⟩
    · exact ⟨(hag.read (by simp)).trans he.writes.1,
        (hag.read (by simp)).trans he.writes.2⟩
    · apply (he.agrees.trans hag).mono
      simp [remainderCountEffect, remainderBranchEffect, Effect.components]

  ·
    intro s hs hc hp
    have hbytes : CodeIn (codeRange 0x1010b9 (remainderCountBytes UpdateKind.finalizeResetSecond)) s :=
      program_text_slice hc 0x10b9 10 (by decide +kernel)
    obtain ⟨fuel, u, ha, hu, _, he⟩ := remainder_count_prepare (kind := .finalizeResetSecond) (by exact Or.inr (Or.inl rfl)) boundary hOutside s hs hbytes hp
    have hcu := he.agrees.codeIn (by
      simp [remainderCountEffect, Effect.components, Component.Covers]) hc
    have hz : condHolds 4 (StatusFlags.ofRFLAGS u.RFLAGS) =
        ((.reg 14 : Operand 64).read s >>> 6 == 0) := he.flags.2.2.2.1
    have hnext : (jccEffect 0x1010c3 2 4 ((0x15#8).signExtend 64) u).rip =
        ((remainderBranchEffect UpdateKind.finalizeResetSecond) s).rip := by
      simp only [jccEffect, hz, branchEffect, remainderBranchEffect, beq_iff_eq]
      split <;> rfl
    have hne : ((remainderBranchEffect UpdateKind.finalizeResetSecond) s).rip ≠ boundary.rip := by
      unfold remainderBranchEffect
      split
      · exact text_address_ne_return hOutside 0x10da (by decide +kernel)
      · exact text_address_ne_return hOutside 0x10c5 (by decide +kernel)
    have hbranch : CodeIn (codeRange 0x1010c3 [0x74, 0x15]) u :=
      program_text_slice hcu 0x10c3 2 (by decide +kernel)
    obtain ⟨t, hb, ht, heb⟩ := (jcc_rel8_effect_step 0x1010c3 4 0x15).advances
      hu hbranch ⟨he.rip, fun _ ↦ by decide +kernel⟩ (hnext ▸ hne)
    have hag : AgreesExcept [.rip] u t := heb.agrees
    refine ⟨fuel + 1, t, ha.trans hb, ht,
      hag.codeIn (by simp [Component.Covers]) hcu, heb.rip.trans hnext, ?_, by trivial, ?_⟩
    · exact ⟨(hag.read (by simp)).trans he.writes.1,
        (hag.read (by simp)).trans he.writes.2⟩
    · apply (he.agrees.trans hag).mono
      simp [remainderCountEffect, remainderBranchEffect, Effect.components]

  ·
    intro s hs hc hp
    have hbytes : CodeIn (codeRange 0x101597 (remainderCountBytes UpdateKind.resetDiscardSecond)) s :=
      program_text_slice hc 0x1597 10 (by decide +kernel)
    obtain ⟨fuel, u, ha, hu, _, he⟩ := remainder_count_prepare (kind := .resetDiscardSecond) (by exact Or.inr (Or.inr rfl)) boundary hOutside s hs hbytes hp
    have hcu := he.agrees.codeIn (by
      simp [remainderCountEffect, Effect.components, Component.Covers]) hc
    have hz : condHolds 4 (StatusFlags.ofRFLAGS u.RFLAGS) =
        ((.reg 14 : Operand 64).read s >>> 6 == 0) := he.flags.2.2.2.1
    have hnext : (jccEffect 0x1015a1 2 4 ((0x12#8).signExtend 64) u).rip =
        ((remainderBranchEffect UpdateKind.resetDiscardSecond) s).rip := by
      simp only [jccEffect, hz, branchEffect, remainderBranchEffect, beq_iff_eq]
      split <;> rfl
    have hne : ((remainderBranchEffect UpdateKind.resetDiscardSecond) s).rip ≠ boundary.rip := by
      unfold remainderBranchEffect
      split
      · exact text_address_ne_return hOutside 0x15b5 (by decide +kernel)
      · exact text_address_ne_return hOutside 0x15a3 (by decide +kernel)
    have hbranch : CodeIn (codeRange 0x1015a1 [0x74, 0x12]) u :=
      program_text_slice hcu 0x15a1 2 (by decide +kernel)
    obtain ⟨t, hb, ht, heb⟩ := (jcc_rel8_effect_step 0x1015a1 4 0x12).advances
      hu hbranch ⟨he.rip, fun _ ↦ by decide +kernel⟩ (hnext ▸ hne)
    have hag : AgreesExcept [.rip] u t := heb.agrees
    refine ⟨fuel + 1, t, ha.trans hb, ht,
      hag.codeIn (by simp [Component.Covers]) hcu, heb.rip.trans hnext, ?_, by trivial, ?_⟩
    · exact ⟨(hag.read (by simp)).trans he.writes.1,
        (hag.read (by simp)).trans he.writes.2⟩
    · apply (he.agrees.trans hag).mono
      simp [remainderCountEffect, remainderBranchEffect, Effect.components]

def alignedBranchEffect (kind : UpdateKind) (s : RamState) : Effect :=
  { (alignedCountEffect kind) s with
    rip := if (.reg kind.sizeRegister : Operand 64).read s >>> 6 = 0 then (pc kind 0x100a4a) else (pc kind 0x100a35)
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem aligned_count_branch [Bindings] {kind : UpdateKind}
    (hkind : kind = .resetSecond ∨ kind = .finalizeResetSecond ∨ kind = .resetDiscardSecond) (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = (pc kind 0x100a82))
      Extracted.programImage (alignedBranchEffect kind) := by
  rcases hkind with rfl | rfl | rfl
  ·
    intro s hs hc hp
    have hbytes : CodeIn (codeRange 0x100a82 (alignedCountBytes UpdateKind.resetSecond)) s :=
      program_text_slice hc 0xa82 10 (by decide +kernel)
    obtain ⟨fuel, u, ha, hu, _, he⟩ := aligned_count_prepare (kind := .resetSecond) (by exact Or.inl rfl) boundary hOutside s hs hbytes hp
    have hcu := he.agrees.codeIn (by
      simp [alignedCountEffect, Effect.components, Component.Covers]) hc
    have hz : (StatusFlags.ofRFLAGS u.RFLAGS).ZF =
        ((.reg UpdateKind.resetSecond.sizeRegister : Operand 64).read s >>> 6 == 0) := he.flags.2.2.2.1
    have hcond : condHolds 5 (StatusFlags.ofRFLAGS u.RFLAGS) =
        !((.reg UpdateKind.resetSecond.sizeRegister : Operand 64).read s >>> 6 == 0) := congrArg Bool.not hz
    have hnext : (jccEffect 0x100a8c 2 5 ((0xa7#8).signExtend 64) u).rip =
        if (.reg UpdateKind.resetSecond.sizeRegister : Operand 64).read s >>> 6 = 0 then 0x100a8e else 0x100a35 := by
      simp only [jccEffect, hcond, branchEffect]
      simp [branchTarget]
    have hne : (jccEffect 0x100a8c 2 5 ((0xa7#8).signExtend 64) u).rip ≠
        boundary.rip := by
      rw [hnext]
      split
      · exact text_address_ne_return hOutside 0xa8e (by decide +kernel)
      · exact text_address_ne_return hOutside 0xa35 (by decide +kernel)
    have hbranch : CodeIn (codeRange 0x100a8c [0x75, 0xa7]) u :=
      program_text_slice hcu 0xa8c 2 (by decide +kernel)
    obtain ⟨v, hb, hv, heb⟩ := (jcc_rel8_effect_step 0x100a8c 5 0xa7).advances
      hu hbranch ⟨he.rip, fun _ ↦ by decide +kernel⟩ hne
    have hag : AgreesExcept [.rip] u v := heb.agrees
    have hcv := hag.codeIn (by simp [Component.Covers]) hcu
    by_cases hzero : (.reg UpdateKind.resetSecond.sizeRegister : Operand 64).read s >>> 6 = 0
    · have hvpc : v.RIP = 0x100a8e := by
        simpa only [hzero, ite_true] using heb.rip.trans hnext
      have hjump : CodeIn (codeRange 0x100a8e [0xeb, 0xba]) v :=
        program_text_slice hcv 0xa8e 2 (by decide +kernel)
      obtain ⟨t, hj, ht, hej⟩ :=
        (jmp_rel8_effect_step 0x100a8e 0xba (by decide +kernel)).advances hv hjump hvpc
          (text_address_ne_return hOutside 0xa4a (by decide +kernel))
      have hagj : AgreesExcept [.rip] v t := hej.agrees
      refine ⟨fuel + 1 + 1, t, (ha.trans hb).trans hj, ht,
        hagj.codeIn (by simp [Component.Covers]) hcv, ?_, ?_, by trivial, ?_⟩
      · simp only [alignedBranchEffect, hzero, ite_true]
        exact hej.rip
      · exact ⟨(hagj.read (by simp)).trans ((hag.read (by simp)).trans he.writes.1),
          (hagj.read (by simp)).trans ((hag.read (by simp)).trans he.writes.2)⟩
      · apply ((he.agrees.trans hag).trans hagj).mono
        simp [alignedCountEffect, alignedBranchEffect, Effect.components]
    · refine ⟨fuel + 1, v, ha.trans hb, hv, hcv, ?_, ?_, by trivial, ?_⟩
      · simpa only [alignedBranchEffect, ite_eq_right hzero,
          show pc .resetSecond 0x100a35 = 0x100a35 by decide +kernel] using heb.rip.trans hnext
      · exact ⟨(hag.read (by simp)).trans he.writes.1,
          (hag.read (by simp)).trans he.writes.2⟩
      · apply (he.agrees.trans hag).mono
        simp [alignedCountEffect, alignedBranchEffect, Effect.components]
  ·
    intro s hs hc hp
    have hbytes : CodeIn (codeRange 0x101112 (alignedCountBytes UpdateKind.finalizeResetSecond)) s :=
      program_text_slice hc 0x1112 10 (by decide +kernel)
    obtain ⟨fuel, u, ha, hu, _, he⟩ := aligned_count_prepare (kind := .finalizeResetSecond) (by exact Or.inr (Or.inl rfl)) boundary hOutside s hs hbytes hp
    have hcu := he.agrees.codeIn (by
      simp [alignedCountEffect, Effect.components, Component.Covers]) hc
    have hz : (StatusFlags.ofRFLAGS u.RFLAGS).ZF =
        ((.reg UpdateKind.finalizeResetSecond.sizeRegister : Operand 64).read s >>> 6 == 0) := he.flags.2.2.2.1
    have hcond : condHolds 5 (StatusFlags.ofRFLAGS u.RFLAGS) =
        !((.reg UpdateKind.finalizeResetSecond.sizeRegister : Operand 64).read s >>> 6 == 0) := congrArg Bool.not hz
    have hnext : (jccEffect 0x10111c 2 5 ((0xa7#8).signExtend 64) u).rip =
        if (.reg UpdateKind.finalizeResetSecond.sizeRegister : Operand 64).read s >>> 6 = 0 then 0x10111e else 0x1010c5 := by
      simp only [jccEffect, hcond, branchEffect]
      simp [branchTarget]
    have hne : (jccEffect 0x10111c 2 5 ((0xa7#8).signExtend 64) u).rip ≠
        boundary.rip := by
      rw [hnext]
      split
      · exact text_address_ne_return hOutside 0x111e (by decide +kernel)
      · exact text_address_ne_return hOutside 0x10c5 (by decide +kernel)
    have hbranch : CodeIn (codeRange 0x10111c [0x75, 0xa7]) u :=
      program_text_slice hcu 0x111c 2 (by decide +kernel)
    obtain ⟨v, hb, hv, heb⟩ := (jcc_rel8_effect_step 0x10111c 5 0xa7).advances
      hu hbranch ⟨he.rip, fun _ ↦ by decide +kernel⟩ hne
    have hag : AgreesExcept [.rip] u v := heb.agrees
    have hcv := hag.codeIn (by simp [Component.Covers]) hcu
    by_cases hzero : (.reg UpdateKind.finalizeResetSecond.sizeRegister : Operand 64).read s >>> 6 = 0
    · have hvpc : v.RIP = 0x10111e := by
        simpa only [hzero, ite_true] using heb.rip.trans hnext
      have hjump : CodeIn (codeRange 0x10111e [0xeb, 0xba]) v :=
        program_text_slice hcv 0x111e 2 (by decide +kernel)
      obtain ⟨t, hj, ht, hej⟩ :=
        (jmp_rel8_effect_step 0x10111e 0xba (by decide +kernel)).advances hv hjump hvpc
          (text_address_ne_return hOutside 0x10da (by decide +kernel))
      have hagj : AgreesExcept [.rip] v t := hej.agrees
      refine ⟨fuel + 1 + 1, t, (ha.trans hb).trans hj, ht,
        hagj.codeIn (by simp [Component.Covers]) hcv, ?_, ?_, by trivial, ?_⟩
      · simp only [alignedBranchEffect, hzero, ite_true]
        exact hej.rip
      · exact ⟨(hagj.read (by simp)).trans ((hag.read (by simp)).trans he.writes.1),
          (hagj.read (by simp)).trans ((hag.read (by simp)).trans he.writes.2)⟩
      · apply ((he.agrees.trans hag).trans hagj).mono
        simp [alignedCountEffect, alignedBranchEffect, Effect.components]
    · refine ⟨fuel + 1, v, ha.trans hb, hv, hcv, ?_, ?_, by trivial, ?_⟩
      · simpa only [alignedBranchEffect, ite_eq_right hzero,
          show pc .finalizeResetSecond 0x100a35 = 0x1010c5 by decide +kernel] using heb.rip.trans hnext
      · exact ⟨(hag.read (by simp)).trans he.writes.1,
          (hag.read (by simp)).trans he.writes.2⟩
      · apply (he.agrees.trans hag).mono
        simp [alignedCountEffect, alignedBranchEffect, Effect.components]
  ·
    intro s hs hc hp
    have hbytes : CodeIn (codeRange 0x1015ef (alignedCountBytes UpdateKind.resetDiscardSecond)) s :=
      program_text_slice hc 0x15ef 10 (by decide +kernel)
    obtain ⟨fuel, u, ha, hu, _, he⟩ := aligned_count_prepare (kind := .resetDiscardSecond) (by exact Or.inr (Or.inr rfl)) boundary hOutside s hs hbytes hp
    have hcu := he.agrees.codeIn (by
      simp [alignedCountEffect, Effect.components, Component.Covers]) hc
    have hz : (StatusFlags.ofRFLAGS u.RFLAGS).ZF =
        ((.reg UpdateKind.resetDiscardSecond.sizeRegister : Operand 64).read s >>> 6 == 0) := he.flags.2.2.2.1
    have hcond : condHolds 5 (StatusFlags.ofRFLAGS u.RFLAGS) =
        !((.reg UpdateKind.resetDiscardSecond.sizeRegister : Operand 64).read s >>> 6 == 0) := congrArg Bool.not hz
    have hnext : (jccEffect 0x1015f9 2 5 ((0xa8#8).signExtend 64) u).rip =
        if (.reg UpdateKind.resetDiscardSecond.sizeRegister : Operand 64).read s >>> 6 = 0 then 0x1015fb else 0x1015a3 := by
      simp only [jccEffect, hcond, branchEffect]
      simp [branchTarget]
    have hne : (jccEffect 0x1015f9 2 5 ((0xa8#8).signExtend 64) u).rip ≠
        boundary.rip := by
      rw [hnext]
      split
      · exact text_address_ne_return hOutside 0x15fb (by decide +kernel)
      · exact text_address_ne_return hOutside 0x15a3 (by decide +kernel)
    have hbranch : CodeIn (codeRange 0x1015f9 [0x75, 0xa8]) u :=
      program_text_slice hcu 0x15f9 2 (by decide +kernel)
    obtain ⟨v, hb, hv, heb⟩ := (jcc_rel8_effect_step 0x1015f9 5 0xa8).advances
      hu hbranch ⟨he.rip, fun _ ↦ by decide +kernel⟩ hne
    have hag : AgreesExcept [.rip] u v := heb.agrees
    have hcv := hag.codeIn (by simp [Component.Covers]) hcu
    by_cases hzero : (.reg UpdateKind.resetDiscardSecond.sizeRegister : Operand 64).read s >>> 6 = 0
    · have hvpc : v.RIP = 0x1015fb := by
        simpa only [hzero, ite_true] using heb.rip.trans hnext
      have hjump : CodeIn (codeRange 0x1015fb [0xeb, 0xb8]) v :=
        program_text_slice hcv 0x15fb 2 (by decide +kernel)
      obtain ⟨t, hj, ht, hej⟩ :=
        (jmp_rel8_effect_step 0x1015fb 0xb8 (by decide +kernel)).advances hv hjump hvpc
          (text_address_ne_return hOutside 0x15b5 (by decide +kernel))
      have hagj : AgreesExcept [.rip] v t := hej.agrees
      refine ⟨fuel + 1 + 1, t, (ha.trans hb).trans hj, ht,
        hagj.codeIn (by simp [Component.Covers]) hcv, ?_, ?_, by trivial, ?_⟩
      · simp only [alignedBranchEffect, hzero, ite_true]
        exact hej.rip
      · exact ⟨(hagj.read (by simp)).trans ((hag.read (by simp)).trans he.writes.1),
          (hagj.read (by simp)).trans ((hag.read (by simp)).trans he.writes.2)⟩
      · apply ((he.agrees.trans hag).trans hagj).mono
        simp [alignedCountEffect, alignedBranchEffect, Effect.components]
    · refine ⟨fuel + 1, v, ha.trans hb, hv, hcv, ?_, ?_, by trivial, ?_⟩
      · simpa only [alignedBranchEffect, ite_eq_right hzero,
          show pc .resetDiscardSecond 0x100a35 = 0x1015a3 by decide +kernel] using heb.rip.trans hnext
      · exact ⟨(hag.read (by simp)).trans he.writes.1,
          (hag.read (by simp)).trans he.writes.2⟩
      · apply (he.agrees.trans hag).mono
        simp [alignedCountEffect, alignedBranchEffect, Effect.components]

end Md5.Proofs.Buffered.ResetSecond
